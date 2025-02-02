// Author: Alexander M. Pellegrino
// Date: November 2, 2024
// License: CC BY-NC 4.0

use std::io::{stdin, stdout, BufRead, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::ops::RangeInclusive;
use std::process::exit;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::channel;
use std::thread;
use std::time::Duration;
use aes_gcm::{Aes256Gcm, KeyInit, Nonce};
use aes_gcm::aead::Aead;
use aes_gcm::aead::generic_array::GenericArray;
use aes_gcm::aead::rand_core::Error;
use dialoguer::{Confirm, Select};
use fips203::{ml_kem_1024, SharedSecretKey};
use fips203::traits::{Decaps, Encaps, KeyGen};
use fips203::traits::SerDes as SerDesKyber;
use fips204::ml_dsa_87;
use fips204::traits::Signer;
use fips204::traits::SerDes as SerDesDilithium;
use hkdf::Hkdf;
use hkdf::hmac::{Hmac, Mac};
use igd_next::{PortMappingProtocol, SearchOptions};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use rand_chacha::rand_core::{RngCore, TryRngCore};
use secrecy::{ExposeSecret, ExposeSecretMut, SecretBox, SecretSlice, SecretString};
use sha2::{Digest, Sha512};
use subtle_encoding::hex;

// Standard delimiters.
const TRANSMISSION_DELIMITER: &str = ":::";
const NONCE_DELIMITER: &str = "~-~";

// The signature context. All signatures from this application should have it.
const SIGNATURE_CONTEXT: &[u8] = b"\xCE\xB1";

// The messages peers and the server should transmit.
const AUTHENTICATION_REQUEST: &str = "Friend requesting access.";
const SESSION_REQUEST: &str = "もうすぐ私に会えますよ"; // 山村貞子、『リング』 - Sadako Yamamura/Samara Morgan, The Ring (Remake, 2002)
const ISSUED_CHALLENGE: &str = "Welcome Anon. Here's your challenge:";
const VERIFIED_PEER: &str = "You're in.";
const PEER_KEYS_RECEIVED: &str = "I see you have constructed a new lightsaber."; // Darth Vader, Star Wars (Return of the Jedi, 1983)
const PEER_CONNECTION_REQUEST: &str = "We Shall Sail Together."; // Sea of Thieves (Rare Games, 2018)
const HEARTBEAT_PROMPT: &str = "Are you still there?"; // Turret, Portal (Valve, 2007)
const HEARTBEAT_RESPONSE: &str = "There you are."; // Turret, Portal (Valve, 2007)
const PEER_AUTHENTICATION: &str = "Hello there."; // Obi-Wan Kenobi, Star Wars (Revenge of the Sith, 2005)
const PEER_AUTH_RESPONSE: &str = "General Kenobi."; // Qymaen jai Sheelal "General Grievous", Star Wars (Revenge of the Sith, 2005)
const SHARED_SECRET_TEST_MESSAGE: &str = "Wake Up, Neo..."; // Morpheus, The Matrix (Original Film, 1999)
const DISCONNECT_MESSAGE: &str = "END OF LINE"; // Master Control Program "MCP", Tron (Original Film, 1982)

// The standard range of valid UPnP ports.
const PORT_RANGE: RangeInclusive<u16> = 1024..=49151;

// Bindings to allow ChaCha20 Use with FIPS203/FIPS204 Crates
struct FipsChaCha20(ChaCha20Rng);

// fips203 and fips204 share this trait
impl fips203::RngCore for FipsChaCha20 {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        // try_fill_bytes is marked as Infallible for ChaCha20
        // It can't error out the same way OsRng can, making this safe.
        self.0.try_fill_bytes(dest).map_err(|_| unreachable!())
    }
}

impl fips203::CryptoRng for FipsChaCha20 {}

fn main() {

    // Generate client keypair. This needs to be done on its own thread
    // due to the massive key sizes being handled here - doing so on the
    // main thread can cause Stack Overflow on Windows Systems which have
    // a default Stack Size of 1MB compared to Mac/Linux's 8MB default.
    let (dilithium_public, dilithium_private) = generate_dilithium_keys();

    // Serialize the key for transmission
    let serialized_pubkey = hex::encode(dilithium_public.expose_secret().clone().into_bytes());

    // Allow user to enter target exchange server address.
    println!("Enter target exchange server address and port:");
    stdout().flush().unwrap();
    
    let mut target_address = String::new();
    stdin().read_line(&mut target_address).expect("Error reading input.");
    target_address = target_address.trim().to_string();

    // Attempt to connect to exchange server.
    let mut server = TcpStream::connect(target_address).expect("Unable to connect to server.");
    write_to_server(&mut server, vec![AUTHENTICATION_REQUEST]);

    // Await the server's response. Should contain a greeting and a nonce.
    let response = read_message(&mut server);

    // Connection denied
    if response.expose_secret().to_lowercase().contains("invalid") {
        eprintln!("The server has rejected this connection.");
        exit(0);
    }

    // Connection accepted, challenge received
    else if response.expose_secret().contains(ISSUED_CHALLENGE) {

        // Sometimes the hex transmitted introduces invisible formatting characters.
        let nonce_hex = response.expose_secret().split('\n').last().expect("Error receiving nonce.");

        let nonce = SecretSlice::from(hex::decode(nonce_hex).expect("Unable to decode nonce."));

        // Sign the nonce
        let nonce_signature = serialize_dilithium_signature(&dilithium_private, nonce);

        // Transmit the signature to the server. Consists of:

        /*
         *   Our public Dilithium key.
         *   The nonce the server sent us.
         *   The nonce signed using our private key.
         */
        write_to_server(&mut server,
                        vec![
                            String::from_utf8(serialized_pubkey).expect("Error serializing public key.").as_str(),
                            nonce_hex,
                            nonce_signature.expose_secret()
                        ]
        );

        // Check authentication.
        let authentication_status = read_message(&mut server);

        println!("{}", authentication_status.expose_secret());

        // Authentication successful.
        if authentication_status.expose_secret() == VERIFIED_PEER {

            // Generate our Kyber keys. Similar to Dilithium, this
            // needs to be offloaded to reduce the Stack Pressure.
            let (kyber_public, kyber_private) = generate_kyber_keys();

            // Link our public Kyber key with our public Dilithium key for the server. Format:

            /*
             *   Our public Dilithium key.
             *   Our public Kyber key.
             *   Our Kyber key signed using the Dilithium key.
             *
             *   The server will ensure our Dilithium key is consistent
             *   with the last transmission from this address and use
             *   the priorly established key to authenticate the signature.
             */
            write_to_server(&mut server,
                            vec![
                                serialize_dilithium_key(&dilithium_public).expose_secret(),
                                serialize_kyber_key(&kyber_public).expose_secret(),
                                serialize_dilithium_signature(&dilithium_private, SecretSlice::from(kyber_public.expose_secret().clone().into_bytes().to_vec())).expose_secret(),
                            ]
            );

            // Confirm the server has linked our keys and added us to the pool.
            let verification_status = read_message(&mut server);

            if verification_status.expose_secret() == PEER_KEYS_RECEIVED {
                // Prepare for connection.
                connection_mode(server, &dilithium_private, &kyber_public, &kyber_private);
            }

        }

        // We failed authentication. This could be a server issue or packet issue.
        else {
            exit(0);
        }
    }
    
}

// Function to handle the peer to peer handoff. The keys are
// massive here - they must be transferred to the Heap Memory
// in order to safely take ownership without blowing up the Stack.
fn connection_mode(
    mut server: TcpStream,
    dilithium_private: &SecretBox<ml_dsa_87::PrivateKey>,
    kyber_public: &SecretBox<ml_kem_1024::EncapsKey>,
    kyber_private: &SecretBox<ml_kem_1024::DecapsKey>
                  )
{
    // Clear all prior console input.
    clearscreen::clear().unwrap();

    // Display the user's public key.
    println!("This is your public ID. Copy it down to share with your peer.");
    println!("WARNING: You will not see it again!");
    println!("\n{}", serialize_kyber_key(kyber_public).expose_secret());

    // Wait for the user to continue.
    println!("\nPress Enter to continue...");
    stdout().flush().unwrap();

    let mut tmp = String::new();
    stdin().read_line(&mut tmp).unwrap();
    drop(tmp);

    clearscreen::clear().unwrap();

    let tx_mode = Select::new()
        .with_prompt("Would you like to send a request, or wait for one?")
        .items(&["Send", "Await"])
        .default(0)
        .interact()
        .unwrap();

    // Send a connection request
    if tx_mode == 0 {

        println!("You must open a listening port to receive the incoming connection.");
        let listening_port = get_open_port();

        // Allow user to enter ID of target peer to connect with.
        println!("Enter Target Peer ID:");
        stdout().flush().unwrap();

        // Read user input.
        let mut peer_id = String::new();
        stdin().read_line(&mut peer_id).expect("Error reading input.");

        // Attempt to decode our peer's public key from the input.
        let peer_kyber_key = SecretBox::from(Box::from(ml_kem_1024::EncapsKey::try_from_bytes(
            <[u8; 1568]>::try_from(
                hex::decode(
                    peer_id.trim()
                ).expect("Invalid hex detected.")
            ).unwrap()
        ).expect("Invalid peer key.")));

        // Establish a shared secret with the target Peer ID and our local one.
        let (shared_secret, ciphertext) = peer_kyber_key.expose_secret().try_encaps().unwrap();

        clearscreen::clear().unwrap();

        println!("Sending session request. There is no guarantee of a response.");
        println!("You will not be informed if the recipient exists in the pool or not.");

        // Transmit the connection request to the server. Consists of:

        /*
         *   Session Request Header
         *   Public Kyber Key
         *   Peer ID to Connect With
         *   Peer ID to Connect With, Signed Using our Private Key
         *   Our listening port, encrypted with the target Peer's public key.
         */

        // We need to send this over a new stream, hence the double authentication.
        // This is because the server consumes the prior stream in case we're in
        // listening mode - the server has no knowledge of our internal state.
        let mut flag_signal = TcpStream::connect(server.peer_addr().unwrap()).expect("Unable to initiate flag connection to server.");

        write_to_server(&mut flag_signal,
                        vec![
                            SESSION_REQUEST,
                            serialize_kyber_key(kyber_public).expose_secret(),
                            serialize_kyber_key(&peer_kyber_key).expose_secret(),
                            serialize_dilithium_signature(dilithium_private, SecretBox::from(hex::decode(peer_id.trim()).unwrap())).expose_secret(),
                            encrypt_message(&derive_symmetric_key(&shared_secret), &listening_port.to_string()).expose_secret(),
                            serialize_ciphertext(&ciphertext).expose_secret(),
                        ]
        );

        // We should be done talking with the server now. All future communication should
        // come from our peer assuming that they received and accepted our request.

        // Open a listener on our selected port - port should now be open via forwarding or UPnP.
        let listener = TcpListener::bind(format!("0.0.0.0:{}", listening_port))
            .expect("Unable to bind to port.");

        for stream in listener.incoming() {
            match stream {
                Ok(stream) => { host_message_mode(stream); break; },
                Err(e) => eprintln!("Connection failed: {}", e)
            }
        }
    }

    // Listen for an incoming connection request. Format:

    /*
     *   Connection request header.
     *   The sender's public Kyber key.
     *   The sender's listening port, encrypted using our public key.
     */
    else {
        let mut connection_attempt = false;

        clearscreen::clear().unwrap();

        while !connection_attempt {
            println!("The quieter you become, the more you can hear. Listening...");
            let mut request_components: Vec<String>;

            loop {
                let incoming_request = read_message(&mut server);

                request_components = incoming_request.expose_secret().split(TRANSMISSION_DELIMITER).map(String::from).collect();

                if incoming_request.expose_secret().contains(PEER_CONNECTION_REQUEST) && request_components.len() == 5 {
                    break;
                }

                if incoming_request.expose_secret().contains(HEARTBEAT_PROMPT) {
                    write_to_server(&mut server, vec![HEARTBEAT_RESPONSE]);
                }
            }

            let incoming_key = request_components[1].clone();
            let peer_address = request_components[2].clone();
            let encrypted_port = request_components[3].clone();
            let ciphertext = request_components[4].clone();

            let shared_secret = kyber_private.expose_secret().try_decaps(deserialize_ciphertext(&ciphertext).expose_secret()).expect("Shared secret could not be established.");

            let peer_port = decrypt_message(&derive_symmetric_key(&shared_secret), &encrypted_port);

            clearscreen::clear().unwrap();

            // 30 Seconds to Accept Connection before automated timeout.
            // This is to prevent crashes caused by DDOS attempts with valid requests.
            let (prompter, receiver) = channel();

            thread::spawn(move || {
                let start_session = Confirm::new()
                    .with_prompt(format!("Incoming Request From Peer:\n{}\n\nInitiate Session?", incoming_key))
                    .interact()
                    .unwrap_or(false);
                let _ = prompter.send(start_session);
            });

            match receiver.recv_timeout(Duration::from_secs(30)) {
                Ok(true) => {
                        connection_attempt = true;
                        listener_message_mode(TcpStream::connect(
                            format!("{}:{}", peer_address, peer_port.expose_secret())
                        ).expect("Failed to connect to peer.")
                    );
                },

                Ok(false) => {
                    println!("Connection declined.");
                    println!("{}", DISCONNECT_MESSAGE);
                },

                _ => {
                    println!("Connection failed or timed out.");
                    println!("{}", DISCONNECT_MESSAGE);
                }
            }
        }
    }
}

// The function for the sender to enter message mode.
// The listener authenticated the server relay, so the
// host will authenticate the communication channel.
fn host_message_mode(mut peer_stream: TcpStream) {
    clearscreen::clear().unwrap();

    let handshake = read_message(&mut peer_stream);

    if handshake.expose_secret() == PEER_AUTHENTICATION {
        write_message(&mut peer_stream, PEER_AUTH_RESPONSE.as_bytes()).unwrap();
    }

    // Flip the message order - we want to be the ones doing decapsulation.
    let _ = read_message(&mut peer_stream);

    // We did key exchange one way over the server. We'll do it
    // the other way around with new keys in the private tunnel.
    let (morpheus_public, morpheus_private) = generate_kyber_keys();

    write_message(&mut peer_stream, serialize_kyber_key(&morpheus_public).expose_secret().as_bytes()).unwrap();

    let ciphertext = deserialize_ciphertext(read_message(&mut peer_stream).expose_secret());

    let shared_secret = SecretBox::from(Box::from(morpheus_private.expose_secret().try_decaps(ciphertext.expose_secret()).unwrap()));
    let symmetric_key = derive_symmetric_key(shared_secret.expose_secret());

    let test_message = encrypt_message(&symmetric_key, SHARED_SECRET_TEST_MESSAGE);

    write_message(&mut peer_stream, test_message.expose_secret().as_bytes()).unwrap();

    chatroom(peer_stream, symmetric_key);
}

// The function for the recipient to enter message mode.
fn listener_message_mode(mut peer_stream: TcpStream) {
    clearscreen::clear().unwrap();

    write_message(&mut peer_stream, PEER_AUTHENTICATION.as_bytes()).unwrap();

    let handshake_response = read_message(&mut peer_stream);

    if handshake_response.expose_secret() == PEER_AUTH_RESPONSE {

        // Flip the message order - we want to be the ones doing encapsulation.
        write_message(&mut peer_stream, b"Ready").unwrap();

        // We did key exchange one way over the server. We'll do it
        // the other way around with new keys in the private tunnel.
        let morpheus_public = deserialize_kyber_key(read_message(&mut peer_stream).expose_secret());

        let (shared_secret, ciphertext) = morpheus_public.expose_secret().try_encaps().map(|(shared_secret, ciphertext)| {
            (SecretBox::from(Box::from(shared_secret)), SecretBox::from(Box::from(ciphertext)))
        }).unwrap();

        write_message(&mut peer_stream, serialize_ciphertext(ciphertext.expose_secret()).expose_secret().as_bytes()).unwrap();

        let symmetric_key = derive_symmetric_key(shared_secret.expose_secret());

        let test_response = decrypt_message(&symmetric_key, read_message(&mut peer_stream).expose_secret());

        if test_response.expose_secret() == SHARED_SECRET_TEST_MESSAGE {
            chatroom(peer_stream, symmetric_key);
        }
    }
}

fn chatroom(mut transmitter: TcpStream, symmetric_key: SecretSlice<u8>) {
    let mut receiver = transmitter.try_clone().unwrap();

    let mut transmitter_key = symmetric_key.clone();
    let mut receiver_key = symmetric_key.clone();
    
    let message_counter = Arc::new(AtomicU64::new(0));
    
    let transmitter_counter = Arc::clone(&message_counter);
    let receiver_counter = Arc::clone(&message_counter);

    let initial_symmetric_key_hash: [u8; 64] = Sha512::digest(symmetric_key.expose_secret()).into();
    let shared_secret_string = hex::encode(&initial_symmetric_key_hash[0..16]);
    
    println!("Welcome friend.");
    println!("Your initial shared secret string is: {}", String::from_utf8(shared_secret_string).unwrap());
    println!("Please confirm through a third-party channel that this matches with your peer's.");
    println!("This is an important step to prevent man-in-the-middle attacks.\n");

    // Transmission thread.
    let tx = thread::spawn(move || {
        
        for line in stdin().lock().lines() {
            match line {
                Ok(message) => {
                    if message.starts_with('>') {
                        if message.to_lowercase().contains("exit") {
                            exit(0);
                        }

                        else if message.to_lowercase().contains("help") {
                            println!("Current Commands:");
                            println!("\thelp - Lists Commands");
                            println!("\texit - Exits The Program");
                        }

                        else {
                            println!("Unknown command.");
                        }
                    }

                    else if !message.is_empty() {
                        transmitter_counter.fetch_add(1, Ordering::SeqCst);
                        let encrypted = encrypt_message(&transmitter_key, message.as_str());
                        if let Err(e) = write_message(&mut transmitter, encrypted.expose_secret().as_bytes()) {
                            eprintln!("Error writing to peer: {}", e);
                            transmitter_counter.fetch_sub(1, Ordering::SeqCst);
                            break;
                        }
                        transmitter_key = cycle_symmetric_key(transmitter_key, &transmitter_counter);
                    }

                }
                Err(_) => {
                    eprintln!("Error reading from console.");
                    break;
                }
            }
        }
    });

    // Reception thread.
    let rx = thread::spawn(move || {

        loop {
            match read_message(&mut receiver) {
                message if !message.expose_secret().is_empty() => {
                    println!("Peer: {}", decrypt_message(&receiver_key, message.expose_secret()).expose_secret());
                    receiver_counter.fetch_add(1, Ordering::SeqCst);
                    receiver_key = cycle_symmetric_key(receiver_key, &receiver_counter);
                    stdout().flush().unwrap();

                }
                
                _ => {
                    println!("Connection closed by peer.");
                    exit(0);
                }
            }
        }
    });

    // Prevent Main Thread from terminating while Transmitter and Receiver are running.
    tx.join().unwrap();
    rx.join().unwrap();
}

fn get_open_port() -> u16 {
    // The port to listen for incoming connections on.
    let mut listening_port = 0;

    // Decide how to open client port.
    let connection_method = Select::new()
        .with_prompt("Would you like to attempt to auto-open a port with UPnP, or enter an open port on your router?")
        .items(&["Auto-map with UPnP", "Specify a Port Manually"])
        .default(0)
        .interact()
        .expect("Error processing connection method.");

    // Attempt to automatically open a port with UPnP.
    if connection_method == 0 {

        println!("Attempting to open a port with UPnP, please wait...");

        if let Ok(local_address) = local_ip_address::local_ip() {

            let search_options = SearchOptions {
                bind_addr: SocketAddr::new(local_address, 0),
                broadcast_address: "239.255.255.250:1900".parse().unwrap(),
                timeout: Some(Duration::from_secs(3600)),
                single_search_timeout: Some(Duration::from_secs(60)),
            };

            match igd_next::search_gateway(search_options) {
                Ok(gateway) => {
                    // Pick a port to attempt to open.
                    let random_port: u16 = rand::random_range(PORT_RANGE);

                    let socket_address = SocketAddr::new(local_address, random_port);

                    if gateway.add_any_port(PortMappingProtocol::TCP,
                                            socket_address,
                                            3600,
                                            "Peer Messaging")
                        .is_ok() {
                        println!("Port successfully opened.");
                        listening_port = random_port;
                    }

                    else {
                        println!("UPnP blocked. Please specify an open port manually.")
                    }
                },

                Err(e) => {
                    println!("UPnP unable to access gateway. Please specify an open port manually.");
                    println!("{}", e);
                }
            }

        }

        else {
            println!("Error determining local IP address. Please specify an open port manually.");
        }
    }

    // User chose manual entry or UPnP failed.
    if listening_port == 0 {
        println!("Enter Open Port Number: ");
        stdout().flush().unwrap();

        let mut input_port = String::new();

        // Ensure we get a valid port to listen on.
        loop {
            stdin().read_line(&mut input_port).expect("Error reading from console.");

            match input_port.trim().parse::<u16>() {
                Ok(p) => {
                    if PORT_RANGE.contains(&p) {
                        listening_port = p;
                        break;
                    }

                    else {
                        println!("Ports must fall within range 1024-49151");
                    }
                }

                Err(_) => println!("Invalid input.")
            }
        }
    }

    listening_port
}

// Function to transmit data with length prefixed.
fn write_message(stream: &mut TcpStream, data: &[u8]) -> std::io::Result<()> {
    let len = data.len() as u32;
    stream.write_all(&len.to_be_bytes())?;
    stream.write_all(data)?;
    Ok(())
}

// Function to safely read incoming transmissions.
fn read_message(stream: &mut TcpStream) -> SecretString {

    let mut len_bytes = [0u8; 4];

    match stream.read_exact(&mut len_bytes) {
        Ok(_) => {
            let len = u32::from_be_bytes(len_bytes) as usize;
            let mut buffer = vec![0; len];

            match stream.read_exact(&mut buffer) {
                Ok(_) => {
                    let result = String::from_utf8(buffer);

                    if let Ok(safe_result) = result {
                        SecretString::from(safe_result)
                    }

                    else {
                        SecretString::from("Invalid Response")
                    }
                },
                Err(_) => {
                    eprintln!("{}", DISCONNECT_MESSAGE);
                    exit(0);
                }
            }
        },
        Err(_) => {
            eprintln!("{}", DISCONNECT_MESSAGE);
            exit(0);
        }
    }
}

// Function to safely write data fragments to the server.
// They will be automatically delimited with the standard separator.
fn write_to_server(server: &mut TcpStream, data_fragments: Vec<&str>) {

    // If statement avoids an empty transmission to the server.
    if !data_fragments.is_empty() {
        if let Err(e) = write_message(server, data_fragments.join(TRANSMISSION_DELIMITER).as_bytes()) {
            eprintln!("Error writing to server: {}", e);
        };
    }
}

// Serializes a Dilithium public key to hex for transmission.
// Will not and should not work with private keys - these should never be shared over the network!
fn serialize_dilithium_key(key: &SecretBox<ml_dsa_87::PublicKey>) -> SecretString {
    let key_bytes = SerDesDilithium::into_bytes(key.expose_secret().clone());
    SecretString::from(String::from_utf8(hex::encode(key_bytes)).unwrap())
}

// Serializes a signature generated with a Dilithium Private Key for transmission.
fn serialize_dilithium_signature(key: &SecretBox<ml_dsa_87::PrivateKey>, message: SecretSlice<u8>) -> SecretString {
    SecretString::from(String::from_utf8(hex::encode(key.expose_secret().try_sign(message.expose_secret(), SIGNATURE_CONTEXT)
        .expect("Unable to encode signature."))).unwrap())
}

// Generate a set of Dilithium keys on their own private thread to avoid blowing up the stack.
fn generate_dilithium_keys() -> (SecretBox<ml_dsa_87::PublicKey>, SecretBox<ml_dsa_87::PrivateKey>) {
    let dilithium_builder = thread::Builder::new()
        .stack_size(8 * 1024 * 1024) // In Bytes - 8MB
        .spawn(|| {
            let cha_cha = ChaCha20Rng::from_os_rng();
            ml_dsa_87::try_keygen_with_rng(&mut FipsChaCha20(cha_cha)).map(|(public_key, private_key)| {
                (SecretBox::new(Box::new(public_key)), SecretBox::new(Box::new(private_key)))
            })
        })
        .unwrap();

    dilithium_builder.join().unwrap().expect("Unable to generate Dilithium keys.")
}

// Generate a set of Kyber keys on their own private thread to avoid blowing up the stack.
fn generate_kyber_keys() -> (SecretBox<ml_kem_1024::EncapsKey>, SecretBox<ml_kem_1024::DecapsKey>) {
    // Generate our Kyber keys. Similar to Dilithium, this
    // needs to be offloaded to reduce the Stack Pressure.
    let kyber_builder = thread::Builder::new()
        .stack_size(8 * 1024 * 1024) // In Bytes - 8MB
        .spawn(|| {
            let cha_cha = ChaCha20Rng::from_os_rng();
            ml_kem_1024::KG::try_keygen_with_rng(&mut FipsChaCha20(cha_cha)).map(|(public_key, private_key)| {
                (SecretBox::new(Box::new(public_key)), SecretBox::new(Box::new(private_key)))
            })
        })
        .unwrap();

    kyber_builder.join().unwrap().expect("Unable to generate Kyber keys.")
}

// Serializes a Kyber public key to hex for transmission.
// Will not and should not work with private keys - these should never be shared over the network!
fn serialize_kyber_key(key: &SecretBox<ml_kem_1024::EncapsKey>) -> SecretString {
    let key_bytes = SerDesKyber::into_bytes(key.expose_secret().clone());
    SecretString::from(String::from_utf8(hex::encode(key_bytes)).unwrap())
}

// Reads a hex-encoded Kyber public key. Will not
// and should not work for private keys - these should
// never be going out over the network, or we have issues.
fn deserialize_kyber_key(serial_key: &str) -> SecretBox<ml_kem_1024::EncapsKey> {
    SecretBox::from(
        Box::from(
            ml_kem_1024::EncapsKey::try_from_bytes(
                <[u8; 1568]>::try_from(
                    hex::decode(serial_key).
                        expect("Unable to decode public key.")
                ).expect("Unable to extract public key bytes.")
            ).expect("Invalid public key.")
        )
    )
}

// Serializes ciphertext for transmission.
fn serialize_ciphertext(ciphertext: &ml_kem_1024::CipherText) -> SecretString {
    SecretString::from(String::from_utf8(hex::encode(ciphertext.clone().into_bytes())).unwrap())
}

// Deserializes received ciphertext.
fn deserialize_ciphertext(serial_ciphertext: &str) -> SecretBox<ml_kem_1024::CipherText> {
    SecretBox::from(
        Box::from(
            ml_kem_1024::CipherText::try_from_bytes(
                hex::decode(serial_ciphertext)
                    .expect("Unable to decode ciphertext hex.")
                    .try_into()
                    .expect("Invalid ciphertext.")
            ).expect("Invalid ciphertext.")
        )
    )
}

// Derive a symmetric key from a shared secret.
fn derive_symmetric_key(shared_secret: &SharedSecretKey) -> SecretSlice<u8> {
    // Use HKDF with SHA512 to derive a 512-bit key (64 bytes) from the shared secret
    let hk = Hkdf::<Sha512>::new(None, shared_secret.clone().into_bytes().as_slice());
    let mut okm = SecretSlice::from(vec![0u8; 32]); // Output key material (32 bytes for AES-256)
    hk.expand(b"encryption key", okm.expose_secret_mut()).unwrap();
    okm
}

// Derive a new symmetric key based on an atomic counter.
fn cycle_symmetric_key(current_key: SecretSlice<u8>, tracker: &AtomicU64) -> SecretSlice<u8> {
    let hkdf = Hkdf::<Sha512>::new(None, current_key.expose_secret());
    let mut new_key = SecretSlice::from(vec![0u8; 32]);
    hkdf.expand(tracker.load(Ordering::Relaxed).to_be_bytes().as_slice(), new_key.expose_secret_mut()).unwrap();
    new_key
}

// Encrypt a message using a symmetric key.
fn encrypt_message(symmetric_key: &SecretSlice<u8>, plaintext: &str) -> SecretString {

    // Derive separate keys for encryption and HMAC.
    let hkdf = Hkdf::<Sha512>::new(None, symmetric_key.expose_secret());
    let mut encryption_key = SecretSlice::from(vec![0u8; 32]);
    let mut hmac_key = SecretSlice::from(vec![0u8; 32]);
    hkdf.expand(b"encryption", encryption_key.expose_secret_mut()).unwrap();
    hkdf.expand(b"hmac", hmac_key.expose_secret_mut()).unwrap();

    // AES-GCM requires a random nonce (12 bytes)
    let mut cha_cha = ChaCha20Rng::from_os_rng();
    let nonce = SecretSlice::from(Vec::from(&mut cha_cha.random::<[u8; 12]>()));
    let cipher = Aes256Gcm::new(GenericArray::from_slice(encryption_key.expose_secret()));

    // Pad plaintext to obscure message length.
    let plaintext_bytes = SecretSlice::from(Vec::from(plaintext.as_bytes()));

    // All messages are padded to a multiple of 2KB.
    let padding_byte_length = SecretBox::new(Box::new(2048u16 - (plaintext_bytes.expose_secret().len() % 2048) as u16));
    let mut padding_bytes = SecretSlice::from(vec![0u8; *padding_byte_length.expose_secret() as usize]);
    
    ChaCha20Rng::from_os_rng().try_fill_bytes(padding_bytes.expose_secret_mut()).expect("Unable to securely pad message.");
    
    // The last two bytes we pad will tell us how many padding bytes we need to strip during
    // decryption. This value will be encrypted along with the plaintext, so leaks no information.
    
    // Plaintext bytes + padding bytes + padding byte length encoded in big-endian.
    let unciphered_data = SecretSlice::from([plaintext_bytes.expose_secret(), padding_bytes.expose_secret(), padding_byte_length.expose_secret().to_be_bytes().as_slice()].concat());

    // Perform encryption.
    let ciphertext = SecretSlice::from(cipher.encrypt(Nonce::from_slice(nonce.expose_secret()), unciphered_data.expose_secret()).unwrap());

    // Calculate HMAC of nonce + ciphertext.
    let mut mac = <Hmac<Sha512> as Mac>::new_from_slice(hmac_key.expose_secret()).unwrap();
    mac.update(nonce.expose_secret());
    mac.update(ciphertext.expose_secret());
    let mac_result = mac.finalize().into_bytes();

    SecretString::from(
        format!("{}{}{}{}{}",
                             String::from_utf8(hex::encode(nonce.expose_secret())).unwrap(),
                             NONCE_DELIMITER,
                             String::from_utf8(hex::encode(ciphertext.expose_secret())).unwrap(),
                             NONCE_DELIMITER,
                             String::from_utf8(hex::encode(mac_result)).unwrap()
        )
    )
}

// Decrypt a message using a symmetric key.
fn decrypt_message(symmetric_key: &SecretSlice<u8>, raw_cipher: &str) -> SecretString {
    // Derive separate keys for encryption and HMAC
    let hkdf = Hkdf::<Sha512>::new(None, symmetric_key.expose_secret());
    let mut encryption_key = SecretSlice::from(vec![0u8; 32]);
    let mut hmac_key = SecretSlice::from(vec![0u8; 32]);
    hkdf.expand(b"encryption", encryption_key.expose_secret_mut()).unwrap();
    hkdf.expand(b"hmac", hmac_key.expose_secret_mut()).unwrap();

    let components: Vec<&str> = raw_cipher.split(NONCE_DELIMITER).collect();

    if components.len() != 3 {
        return SecretString::default();
    }

    let nonce = SecretSlice::from(hex::decode(components[0].trim()).unwrap());
    let ciphertext = SecretSlice::from(hex::decode(components[1].trim()).unwrap());
    let received_mac = SecretSlice::from(hex::decode(components[2].trim()).unwrap());

    // Verify HMAC
    let mut mac = <Hmac<Sha512> as Mac>::new_from_slice(hmac_key.expose_secret()).unwrap();
    mac.update(nonce.expose_secret());
    mac.update(ciphertext.expose_secret());
    if mac.verify_slice(received_mac.expose_secret()).is_err() {
        return SecretString::default();
    }

    // Perform decryption.
    let cipher = Aes256Gcm::new(GenericArray::from_slice(encryption_key.expose_secret()));
    let plaintext_bytes = SecretSlice::from(cipher.decrypt(
        Nonce::from_slice(nonce.expose_secret()),
        ciphertext.expose_secret()
    ).unwrap_or_else(|_| Vec::from(b"Decryption error.")));

    // Strip message padding for display.
    let padding_length = u16::from_be_bytes(plaintext_bytes.expose_secret()[plaintext_bytes.expose_secret().len() - 2..].try_into().unwrap());
    
    // Don't forget to truncate two additional bytes to remove the padding length marker.
    SecretString::from(String::from_utf8(plaintext_bytes.expose_secret()[..plaintext_bytes.expose_secret().len() - (padding_length as usize + 2)].to_vec()).unwrap())
}