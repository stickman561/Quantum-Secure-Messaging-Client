// Author: Alexander M. Pellegrino
// Date: November 2, 2024
// License: CC BY-NC 4.0

use std::io::{stdin, stdout, BufRead, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::ops::RangeInclusive;
use std::process::exit;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::Duration;
use aes_gcm::{Aes256Gcm, KeyInit, Nonce};
use aes_gcm::aead::Aead;
use aes_gcm::aead::generic_array::GenericArray;
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
use rand::{random, Rng, RngCore};
use rand::rngs::OsRng;
use sha2::{Digest, Sha256};
use zeroize::Zeroize;

// Standard delimiters.
const TRANSMISSION_DELIMITER: &str = ":::";
const NONCE_DELIMITER: &str = "~-~";

// The signature context. All signatures from this application should have it.
const SIGNATURE_CONTEXT: &[u8] = b"\xCE\xB1";

// The messages peers and the server should transmit.
const AUTHENTICATION_REQUEST: &str = "Friend requesting access.";
const SESSION_REQUEST: &str = "もうすぐ私に会えますよ";
const ISSUED_CHALLENGE: &str = "Welcome Anon. Here's your challenge:";
const VERIFIED_PEER: &str = "You're in.";
const PEER_KEYS_RECEIVED: &str = "I see you have constructed a new lightsaber.";
const PEER_CONNECTION_REQUEST: &str = "We Shall Sail Together.";
const PEER_AUTHENTICATION: &str = "Hello there.";
const PEER_AUTH_RESPONSE: &str = "General Kenobi.";
const SHARED_SECRET_TEST_MESSAGE: &str = "Wake Up, Neo.";
const DISCONNECT_MESSAGE: &str = "END OF LINE";

// The standard range of valid ports.
const PORT_RANGE: RangeInclusive<u16> = 1024..=49151;

fn main() {

    // Generate client keypair. This needs to be done on its own thread
    // due to the massive key sizes being handled here - doing so on the
    // main thread can cause Stack Overflow on Windows Systems which have
    // a default Stack Size of 1MB compared to Mac/Linux's 8MB default.
    let (dilithium_public, dilithium_private) = generate_dilithium_keys();

    // Serialize the key for transmission
    let serialized_pubkey = hex::encode(dilithium_public.clone().into_bytes());

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
    if response.to_lowercase().contains("invalid") {
        eprintln!("The server has rejected this connection.");
        exit(0);
    }

    // Connection accepted, challenge received
    else if response.contains(ISSUED_CHALLENGE) {

        // Sometimes the hex transmitted introduces invisible formatting characters.
        let nonce_hex = response.split('\n').last().expect("Error receiving nonce.");

        let nonce = hex::decode(nonce_hex).expect("Unable to decode nonce.");

        // Sign the nonce
        let nonce_signature = serialize_dilithium_signature(&dilithium_private, &nonce);

        // Transmit the signature to the server. Consists of:

        /*
         *   Our public Dilithium key.
         *   The nonce the server sent us.
         *   The nonce signed using our private key.
         */
        write_to_server(&mut server,
                        vec![
                            serialized_pubkey.as_str(),
                            nonce_hex,
                            nonce_signature.as_str()
                        ]
        );

        // Check authentication.
        let authentication_status = read_message(&mut server);

        println!("{}", authentication_status);

        // Authentication successful.
        if authentication_status == VERIFIED_PEER {

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
                                serialize_dilithium_key(&dilithium_public).as_str(),
                                serialize_kyber_key(&kyber_public).as_str(),
                                serialize_dilithium_signature(&dilithium_private, &kyber_public.clone().into_bytes()).as_str()
                            ]
            );

            // Confirm the server has linked our keys and added us to the pool.
            let verification_status = read_message(&mut server);

            if verification_status == PEER_KEYS_RECEIVED {
                // Prepare for connection.
                connection_mode(server, Box::from(dilithium_private), Box::from(kyber_public), Box::from(kyber_private));
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
    mut dilithium_private: Box<ml_dsa_87::PrivateKey>,
    kyber_public: Box<ml_kem_1024::EncapsKey>,
    mut kyber_private: Box<ml_kem_1024::DecapsKey>
                  )
{
    // Clear all prior console input.
    clearscreen::clear().unwrap();

    // Display the user's public key.
    println!("This is your public ID. Copy it down to share with your peer.");
    println!("WARNING: You will not see it again!");
    println!("\n{}", serialize_kyber_key(&kyber_public));

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
        let peer_kyber_key = ml_kem_1024::EncapsKey::try_from_bytes(
            <[u8; 1568]>::try_from(
                hex::decode(
                    peer_id.trim()
                ).expect("Invalid hex detected.")
            ).unwrap()
        ).expect("Invalid peer key.");

        // Establish a shared secret with the target Peer ID and our local one.
        let (shared_secret, ciphertext) = peer_kyber_key.try_encaps().unwrap();

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
                            serialize_kyber_key(&kyber_public).as_str(),
                            serialize_kyber_key(&peer_kyber_key).as_str(),
                            serialize_dilithium_signature(&dilithium_private, &hex::decode(peer_id.trim()).unwrap()).as_str(),
                            encrypt_message(&derive_symmetric_key(&shared_secret), &listening_port.to_string()).as_str(),
                            serialize_ciphertext(&ciphertext).as_str()
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
                Err(e) => eprintln!("Connection failed: {}", e),
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

        clearscreen::clear().unwrap();

        println!("The quieter you become, the more you can hear. Listening...");

        let mut incoming_request;
        let mut request_components: Vec<&str>;

        loop {
            incoming_request = read_message(&mut server);

            request_components = incoming_request.split(TRANSMISSION_DELIMITER).collect();

            if incoming_request.contains(PEER_CONNECTION_REQUEST) && request_components.len() == 5 {
                break;
            }
        }

        let incoming_key = request_components[1];
        let peer_address = request_components[2];
        let encrypted_port = request_components[3];
        let ciphertext = request_components[4];

        let mut shared_secret = kyber_private.try_decaps(&deserialize_ciphertext(ciphertext)).expect("Shared secret could not be established.");

        let mut peer_port = decrypt_message(derive_symmetric_key(&shared_secret).as_slice(), encrypted_port);

        clearscreen::clear().unwrap();

        let start_session = Confirm::new()
            .with_prompt(format!("Incoming Request From Peer:\n{}\n\nInitiate Session?", incoming_key))
            .interact()
            .unwrap();

        if start_session {
            listener_message_mode(TcpStream::connect(
                                format!("{}:{}", peer_address, peer_port)
                            ).expect("Failed to connect to peer.")
            );
        }

        else {
            println!("Connection declined.");
            println!("{}", DISCONNECT_MESSAGE);
            exit(0);
        }

        // Securely Zero sensitive values in memory before drop.
        shared_secret.zeroize();
        peer_port.zeroize();
    }

    // Securely Zero sensitive values in memory before drop.
    dilithium_private.zeroize();
    kyber_private.zeroize();
}

// The function for the sender to enter message mode.
// The listener authenticated the server relay, so the
// host will authenticate the communication channel.
fn host_message_mode(mut peer_stream: TcpStream) {
    clearscreen::clear().unwrap();

    let handshake = read_message(&mut peer_stream);

    if handshake == PEER_AUTHENTICATION {
        write_message(&mut peer_stream, PEER_AUTH_RESPONSE.as_bytes()).unwrap();
    }

    // Flip the message order - we want to be the ones doing decapsulation.
    let _ = read_message(&mut peer_stream);

    // We did key exchange one way over the server. We'll do it
    // the other way around with new keys in the private tunnel.
    let (morpheus_public, mut morpheus_private) = generate_kyber_keys();

    write_message(&mut peer_stream, serialize_kyber_key(&morpheus_public).as_bytes()).unwrap();

    let mut ciphertext = deserialize_ciphertext(read_message(&mut peer_stream).as_str());

    let mut shared_secret = morpheus_private.try_decaps(&ciphertext).unwrap();
    let symmetric_key = derive_symmetric_key(&shared_secret);

    let test_message = encrypt_message(&symmetric_key, SHARED_SECRET_TEST_MESSAGE);

    write_message(&mut peer_stream, test_message.as_bytes()).unwrap();

    chatroom(peer_stream, symmetric_key);

    // Securely Zero sensitive values in memory before drop.
    morpheus_private.zeroize();
    shared_secret.zeroize();
    ciphertext.zeroize();
}

// The function for the recipient to enter message mode.
fn listener_message_mode(mut peer_stream: TcpStream) {
    clearscreen::clear().unwrap();

    write_message(&mut peer_stream, PEER_AUTHENTICATION.as_bytes()).unwrap();

    let handshake_response = read_message(&mut peer_stream);

    if handshake_response == PEER_AUTH_RESPONSE {

        // Flip the message order - we want to be the ones doing encapsulation.
        write_message(&mut peer_stream, b"Ready").unwrap();

        // We did key exchange one way over the server. We'll do it
        // the other way around with new keys in the private tunnel.
        let morpheus_public = deserialize_kyber_key(read_message(&mut peer_stream).as_str());

        let (mut shared_secret, mut ciphertext) = morpheus_public.try_encaps().unwrap();

        write_message(&mut peer_stream, serialize_ciphertext(&ciphertext).as_bytes()).unwrap();

        let symmetric_key = derive_symmetric_key(&shared_secret);

        let test_response = decrypt_message(&symmetric_key, read_message(&mut peer_stream).as_str());

        if test_response == SHARED_SECRET_TEST_MESSAGE {
            chatroom(peer_stream, symmetric_key);
        }

        // Securely Zero sensitive values in memory before drop.
        shared_secret.zeroize();
        ciphertext.zeroize();
    }
}

fn chatroom(mut transmitter: TcpStream, mut symmetric_key: Vec<u8>) {
    let mut receiver = transmitter.try_clone().unwrap();

    let mut transmitter_key = symmetric_key.clone();
    let mut receiver_key = symmetric_key.clone();
    
    let message_counter = Arc::new(AtomicU64::new(0));
    
    let transmitter_counter = Arc::clone(&message_counter);
    let receiver_counter = Arc::clone(&message_counter);

    let initial_symmetric_key_hash: [u8; 32] = Sha256::digest(symmetric_key.as_slice()).into();
    let shared_secret_string = hex::encode(&initial_symmetric_key_hash[0..8]);
    
    println!("Welcome friend.");
    println!("Your initial shared secret string is: {}", shared_secret_string);
    println!("Please confirm through a third-party channel that this matches with your peer's.");
    println!("This is an important step to prevent man-in-the-middle attacks.\n");

    // Transmission thread.
    let tx = thread::spawn(move || {
        
        for line in stdin().lock().lines() {
            match line {
                Ok(message) => {
                    if message.starts_with('>') {
                        if message.to_lowercase().contains("exit") {

                            // Securely Zero the Final Key (Prior keys Zeroed during cycle.)
                            transmitter_key.zeroize();
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
                        if let Err(e) = write_message(&mut transmitter, encrypted.as_bytes()) {
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
                message if !message.is_empty() => {
                    println!("Peer: {}", decrypt_message(receiver_key.as_slice(), &message));
                    receiver_counter.fetch_add(1, Ordering::SeqCst);
                    receiver_key = cycle_symmetric_key(receiver_key, &receiver_counter);
                    stdout().flush().unwrap();

                }
                
                _ => {
                    println!("Connection closed by peer.");

                    // Securely Zero the Final Key (Prior keys Zeroed during cycle.)
                    receiver_key.zeroize();
                    exit(0);
                }
            }
        }
    });

    // Securely Zero the symmetric key used.
    symmetric_key.zeroize();

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
                timeout: Some(Duration::from_secs(3600))
            };

            match igd_next::search_gateway(search_options) {
                Ok(gateway) => {
                    // Pick a port to attempt to open.
                    let random_port: u16 = OsRng.gen_range(PORT_RANGE);

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
fn read_message(stream: &mut TcpStream) -> String {
    let mut len_bytes = [0u8; 4];

    match stream.read_exact(&mut len_bytes) {
        Ok(_) => {
            let len = u32::from_be_bytes(len_bytes) as usize;
            let mut buffer = vec![0; len];

            match stream.read_exact(&mut buffer) {
                Ok(_) => {
                    let result = String::from_utf8(buffer);

                    if let Ok(safe_result) = result {
                        safe_result
                    } else {
                        String::from("Invalid Response")
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
fn serialize_dilithium_key(key: &ml_dsa_87::PublicKey) -> String {
    let key_bytes = SerDesDilithium::into_bytes(key.clone());
    hex::encode(key_bytes)
}

// Serializes a signature generated with a Dilithium Private Key for transmission.
fn serialize_dilithium_signature(key: &ml_dsa_87::PrivateKey, message: &[u8]) -> String {
    hex::encode(key.try_sign(message, SIGNATURE_CONTEXT)
        .expect("Unable to encode signature."))
}

// Generate a set of Dilithium keys on their own private thread to avoid blowing up the stack.
fn generate_dilithium_keys() -> (ml_dsa_87::PublicKey, ml_dsa_87::PrivateKey) {
    let dilithium_builder = thread::Builder::new()
        .stack_size(8 * 1024 * 1024) // In Bytes - 8MB
        .spawn(|| {
            ml_dsa_87::try_keygen_with_rng(&mut OsRng)
        })
        .unwrap();

    dilithium_builder.join().unwrap().expect("Unable to generate Dilithium keys.")
}

// Generate a set of Kyber keys on their own private thread to avoid blowing up the stack.
fn generate_kyber_keys() -> (ml_kem_1024::EncapsKey, ml_kem_1024::DecapsKey) {
    // Generate our Kyber keys. Similar to Dilithium, this
    // needs to be offloaded to reduce the Stack Pressure.
    let kyber_builder = thread::Builder::new()
        .stack_size(8 * 1024 * 1024) // In Bytes - 8MB
        .spawn(|| {
            ml_kem_1024::KG::try_keygen_with_rng(&mut OsRng)
        })
        .unwrap();

    kyber_builder.join().unwrap().expect("Unable to generate Kyber keys.")
}

// Serializes a Kyber public key to hex for transmission.
// Will not and should not work with private keys - these should never be shared over the network!
fn serialize_kyber_key(key: &ml_kem_1024::EncapsKey) -> String {
    let key_bytes = SerDesKyber::into_bytes(key.clone());
    hex::encode(key_bytes)
}

// Reads a hex-encoded Kyber public key. Will not
// and should not work for private keys - these should
// never be going out over the network, or we have issues.
fn deserialize_kyber_key(serial_key: &str) -> ml_kem_1024::EncapsKey {
    ml_kem_1024::EncapsKey::try_from_bytes(
        <[u8; 1568]>::try_from(
            hex::decode(serial_key).
                expect("Unable to decode public key.")
        ).expect("Unable to extract public key bytes.")
    ).expect("Invalid public key.")
}

// Serializes ciphertext for transmission.
fn serialize_ciphertext(ciphertext: &ml_kem_1024::CipherText) -> String {
    hex::encode(ciphertext.clone().into_bytes())
}

// Deserializes received ciphertext.
fn deserialize_ciphertext(serial_ciphertext: &str) -> ml_kem_1024::CipherText {
    ml_kem_1024::CipherText::try_from_bytes(
        hex::decode(serial_ciphertext)
            .expect("Unable to decode ciphertext hex.")
            .try_into()
            .expect("Invalid ciphertext.")
    ).expect("Invalid ciphertext.")
}

// Derive a symmetric key from a shared secret.
fn derive_symmetric_key(shared_secret: &SharedSecretKey) -> Vec<u8> {
    // Use HKDF with SHA256 to derive a 256-bit key (32 bytes) from the shared secret
    let hk = Hkdf::<Sha256>::new(None, shared_secret.clone().into_bytes().as_slice());
    let mut okm = [0u8; 32]; // Output key material (32 bytes for AES-256)
    hk.expand(b"encryption key", &mut okm).unwrap();
    let result = okm.to_vec();
    okm.zeroize();
    result
}

// Derive a new symmetric key based on an atomic counter.
fn cycle_symmetric_key(mut current_key: Vec<u8>, tracker: &AtomicU64) -> Vec<u8> {
    let hkdf = Hkdf::<Sha256>::new(None, &current_key);
    let mut new_key = vec![0u8; 32];
    hkdf.expand(tracker.load(Ordering::Relaxed).to_be_bytes().as_slice(), &mut new_key).unwrap();

    // Securely Zero old key from memory before drop.
    current_key.zeroize();
    new_key
}

// Encrypt a message using a symmetric key.
fn encrypt_message(symmetric_key: &[u8], plaintext: &str) -> String {

    // Derive separate keys for encryption and HMAC.
    let hkdf = Hkdf::<Sha256>::new(None, symmetric_key);
    let mut encryption_key = [0u8; 32];
    let mut hmac_key = [0u8; 32];
    hkdf.expand(b"encryption", &mut encryption_key).unwrap();
    hkdf.expand(b"hmac", &mut hmac_key).unwrap();

    // AES-GCM requires a random nonce (12 bytes)
    let mut nonce = random::<[u8; 12]>();
    let cipher = Aes256Gcm::new(GenericArray::from_slice(&encryption_key));

    // Pad plaintext to obscure message length.
    let mut plaintext_bytes = Vec::from(plaintext.as_bytes());

    // All messages are padded to a multiple of 2KB.
    let padding_byte_length: [u8; 2] = (2048u16 - (plaintext_bytes.len() % 2048) as u16).to_be_bytes();
    let mut padding_bytes = vec![0u8; u16::from_be_bytes(padding_byte_length) as usize];
    
    OsRng.try_fill_bytes(&mut padding_bytes).expect("Unable to securely pad message.");
    
    // The last two bytes we pad will tell us how many padding bytes we need to strip during
    // decryption. This value will be encrypted along with the plaintext, so leaks no information.
    padding_bytes.extend(padding_byte_length);
    
    // Add the padding to the plaintext.
    plaintext_bytes.extend(padding_bytes);

    // Perform encryption.
    let mut ciphertext = cipher.encrypt(Nonce::from_slice(&nonce), plaintext_bytes.as_slice()).unwrap();

    // Calculate HMAC of nonce + ciphertext.
    let mut mac = <Hmac<Sha256> as Mac>::new_from_slice(&hmac_key).unwrap();
    mac.update(&nonce);
    mac.update(&ciphertext);
    let mac_result = mac.finalize().into_bytes();

    let result = format!("{}{}{}{}{}",
                         hex::encode(nonce),
                         NONCE_DELIMITER,
                         hex::encode(&ciphertext),
                         NONCE_DELIMITER,
                         hex::encode(mac_result)
    );

    // Securely Zero sensitive values in memory before drop.
    encryption_key.zeroize();
    hmac_key.zeroize();
    nonce.zeroize();
    plaintext_bytes.zeroize();
    ciphertext.zeroize();

    result
}

// Decrypt a message using a symmetric key.
fn decrypt_message(symmetric_key: &[u8], raw_cipher: &str) -> String {
    // Derive separate keys for encryption and HMAC
    let hkdf = Hkdf::<Sha256>::new(None, symmetric_key);
    let mut encryption_key = [0u8; 32];
    let mut hmac_key = [0u8; 32];
    hkdf.expand(b"encryption", &mut encryption_key).unwrap();
    hkdf.expand(b"hmac", &mut hmac_key).unwrap();

    let components: Vec<&str> = raw_cipher.split(NONCE_DELIMITER).collect();

    if components.len() != 3 {
        return String::new();
    }

    let mut nonce = hex::decode(components[0].trim()).unwrap();
    let mut ciphertext = hex::decode(components[1].trim()).unwrap();
    let received_mac = hex::decode(components[2].trim()).unwrap();

    // Verify HMAC
    let mut mac = <Hmac<Sha256> as Mac>::new_from_slice(&hmac_key).unwrap();
    mac.update(&nonce);
    mac.update(&ciphertext);
    if mac.verify_slice(&received_mac).is_err() {
        return String::new();
    }

    // Perform decryption.
    let cipher = Aes256Gcm::new(GenericArray::from_slice(&encryption_key));
    let mut plaintext_bytes = cipher.decrypt(
        Nonce::from_slice(nonce.as_slice()),
        ciphertext.as_slice()
    ).unwrap_or_else(|_| Vec::from(b"Decryption error."));

    // Strip message padding for display.
    let padding_length = u16::from_be_bytes(plaintext_bytes[plaintext_bytes.len() - 2..].try_into().unwrap());
    
    // Don't forget to truncate two additional bytes to remove the padding length marker.
    plaintext_bytes.truncate(plaintext_bytes.len() - (padding_length as usize + 2));

    // Securely Zero sensitive values in memory before drop.
    encryption_key.zeroize();
    hmac_key.zeroize();
    nonce.zeroize();
    ciphertext.zeroize();

    String::from_utf8(plaintext_bytes).unwrap()
}