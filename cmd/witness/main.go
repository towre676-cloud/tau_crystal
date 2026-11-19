// Moth Witness v1: a source-device signer intended to run ON the acquisition Pi.
package main

import (
	"crypto/ed25519"
	"encoding/json"
	"flag"
	"fmt"
	"mothcompanion/internal/witness"
	"os"
	"path/filepath"
)

func main() {
	mode := flag.String("mode", "sign", "sign, verify or fingerprint")
	file := flag.String("file", "", "physical capture file to hash or verify")
	node := flag.String("node", "moth-pi-01", "device name")
	keypath := flag.String("key", "", "private key path (local to acquisition device)")
	out := flag.String("out", "", "output envelope path for sign or input manifest path for verify")
	method := flag.String("method", "direct-on-device", "description of physical acquisition path")
	source := flag.String("source", "pi-capture", "source context; not an independent truth guarantee")
	previous := flag.String("previous", "", "SHA256 of preceding envelope for continuity")
	flag.Parse()
	if *mode != "fingerprint" && *out == "" {
		fmt.Fprintln(os.Stderr, "-out manifest.json is required")
		os.Exit(2)
	}
	if *mode == "verify" {
		e, err := witness.Read(*out)
		if err != nil {
			die(err)
		}
		r := witness.Check(e, *file)
		b, _ := json.MarshalIndent(r, "", "  ")
		fmt.Println(string(b))
		if !r.Valid {
			os.Exit(1)
		}
		return
	}
	if *mode != "sign" && *mode != "fingerprint" {
		fmt.Fprintln(os.Stderr, "invalid mode")
		os.Exit(2)
	}
	if *mode == "sign" && *file == "" {
		fmt.Fprintln(os.Stderr, "usage: moth-witness -file capture.wav -out capture.moth.json [-node moth-pi-01]")
		os.Exit(2)
	}
	p := *keypath
	if p == "" {
		home, err := os.UserHomeDir()
		if err != nil {
			die(err)
		}
		p = filepath.Join(home, ".moth-witness", "device.ed25519")
	}
	priv, err := witness.Key(p)
	if err != nil {
		die(err)
	}
	if *mode == "fingerprint" {
		fmt.Printf("Device public-key fingerprint: %s\nIMPORTANT: compare this directly on your Pi with the Windows companion before trusting any receipt.\n", witness.Fingerprint(priv.Public().(ed25519.PublicKey)))
		return
	}
	e, err := witness.Make(*file, *node, *method, *source, *previous, priv)
	if err != nil {
		die(err)
	}
	if err := witness.Save(*out, e); err != nil {
		die(err)
	}
	fmt.Printf("Created %s\nCapture SHA256: %s\nKey fingerprint: %s\nEnvelope SHA256: %s\nIMPORTANT: sensor origin depends on physical custody, secure capture path, firmware integrity and key storage.\n", *out, e.Statement.SHA256, witness.Check(e, "").Fingerprint, witness.EnvelopeDigest(e))
}
func die(err error) { fmt.Fprintln(os.Stderr, err); os.Exit(1) }
