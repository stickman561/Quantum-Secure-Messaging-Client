# Client Application

Just throwing together a quick README for now, will likely improve later. This repository contains the source code for a peer-to-peer messaging client, 
based on a custom relay server application (which can be found at https://github.com/stickman561/Quantum-Secure-Messaging-Server). It's built entirely in safe Rust
and uses Quantum-Secure signing, key encapsulation, and encryption in order to provide a hopefully future-safe messaging experience. Because this is a
peer to peer application, one client does need an open port to listen on, however, by default it will try to open this port automatically if the router
has UPnP enabled. As a fallback or if you prefer a port can be manually specified instead. You'll need to connect to an instance of the Server application,
which requires a port of its own, in order to act as a relay for the peer to peer handoff. Public keys are to be exchanged out-of-band. (On another platform.)
