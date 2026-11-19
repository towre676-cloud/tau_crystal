// Package witness defines the interoperable Moth Witness v1 signed capture envelope.
// A valid signature authenticates the signing key and exact hashed bytes. It DOES NOT
// by itself demonstrate that the bytes were acquired directly from a physical sensor.
package witness

import (
	"crypto/ed25519"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"time"
)

const Version = "moth-witness/v1"

type Statement struct {
	Version       string `json:"version"`
	NodeID        string `json:"node_id"`
	Source        string `json:"source"`
	CaptureMethod string `json:"capture_method"`
	FileName      string `json:"file_name"`
	Bytes         int64  `json:"bytes"`
	SHA256        string `json:"sha256"`
	Previous      string `json:"previous_envelope_sha256,omitempty"`
	UTC           string `json:"utc"`
	Nonce         string `json:"nonce"`
}
type Envelope struct {
	Statement Statement `json:"statement"`
	PublicKey string    `json:"public_key_ed25519"`
	Signature string    `json:"signature_ed25519"`
}
type Result struct {
	Valid          bool   `json:"valid"`
	SignatureValid bool   `json:"signature_valid"`
	FileValid      *bool  `json:"file_valid,omitempty"`
	NodeID         string `json:"node_id"`
	Fingerprint    string `json:"fingerprint"`
	ContentSHA256  string `json:"content_sha256"`
	Source         string `json:"source"`
	CaptureMethod  string `json:"capture_method"`
	Claim          string `json:"claim"`
	Message        string `json:"message"`
}

func (e Envelope) SignedBytes() ([]byte, error) { return json.Marshal(e.Statement) }
func FileHash(path string) (string, int64, error) {
	f, err := os.Open(path)
	if err != nil {
		return "", 0, err
	}
	defer f.Close()
	h := sha256.New()
	n, err := io.Copy(h, f)
	if err != nil {
		return "", 0, err
	}
	return hex.EncodeToString(h.Sum(nil)), n, nil
}
func Key(path string) (ed25519.PrivateKey, error) {
	if b, err := os.ReadFile(path); err == nil {
		if len(b) != ed25519.PrivateKeySize {
			return nil, errors.New("invalid Ed25519 private key length")
		}
		return ed25519.PrivateKey(b), nil
	} else if !os.IsNotExist(err) {
		return nil, err
	}
	if err := os.MkdirAll(filepath.Dir(path), 0700); err != nil {
		return nil, err
	}
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return nil, err
	}
	f, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0600)
	if err != nil {
		return nil, err
	}
	if _, err = f.Write(priv); err != nil {
		f.Close()
		return nil, err
	}
	if err = f.Close(); err != nil {
		return nil, err
	}
	return priv, nil
}
func Make(path, node, method, source, previous string, priv ed25519.PrivateKey) (Envelope, error) {
	hash, n, err := FileHash(path)
	if err != nil {
		return Envelope{}, err
	}
	if strings.TrimSpace(node) == "" {
		return Envelope{}, errors.New("node ID required")
	}
	if len(previous) > 0 {
		if len(previous) != 64 {
			return Envelope{}, errors.New("previous hash must be SHA-256 hex")
		}
		if _, err := hex.DecodeString(previous); err != nil {
			return Envelope{}, err
		}
	}
	nonce := make([]byte, 16)
	if _, err = rand.Read(nonce); err != nil {
		return Envelope{}, err
	}
	if method == "" {
		method = "file-import"
	}
	if source == "" {
		source = "file-on-device"
	}
	e := Envelope{Statement: Statement{Version: Version, NodeID: node, Source: source, CaptureMethod: method, FileName: filepath.Base(path), Bytes: n, SHA256: hash, Previous: previous, UTC: time.Now().UTC().Format(time.RFC3339Nano), Nonce: hex.EncodeToString(nonce)}, PublicKey: base64.StdEncoding.EncodeToString(priv.Public().(ed25519.PublicKey))}
	b, _ := e.SignedBytes()
	e.Signature = base64.StdEncoding.EncodeToString(ed25519.Sign(priv, b))
	return e, nil
}
func Fingerprint(pub ed25519.PublicKey) string {
	h := sha256.Sum256(pub)
	return hex.EncodeToString(h[:])[:24]
}
func Check(e Envelope, filePath string) Result {
	s := e.Statement
	r := Result{NodeID: s.NodeID, ContentSHA256: s.SHA256, Source: s.Source, CaptureMethod: s.CaptureMethod, Claim: "A signature authenticates a key's statement about a file, not the truthfulness or sensor origin of that file."}
	if s.Version != Version {
		r.Message = "unsupported witness version"
		return r
	}
	if s.NodeID == "" || s.Source == "" || s.CaptureMethod == "" || len(s.SHA256) != 64 || s.Bytes < 0 {
		r.Message = "incomplete capture statement"
		return r
	}
	if _, err := hex.DecodeString(s.SHA256); err != nil {
		r.Message = "invalid SHA-256 hex"
		return r
	}
	pub, err := base64.StdEncoding.DecodeString(e.PublicKey)
	if err != nil || len(pub) != ed25519.PublicKeySize {
		r.Message = "invalid public key"
		return r
	}
	sig, err := base64.StdEncoding.DecodeString(e.Signature)
	if err != nil || len(sig) != ed25519.SignatureSize {
		r.Message = "invalid signature encoding"
		return r
	}
	r.Fingerprint = Fingerprint(ed25519.PublicKey(pub))
	data, err := e.SignedBytes()
	if err != nil {
		r.Message = "invalid statement"
		return r
	}
	r.SignatureValid = ed25519.Verify(ed25519.PublicKey(pub), data, sig)
	if !r.SignatureValid {
		r.Message = "signature verification FAILED"
		return r
	}
	if filePath != "" {
		h, n, err := FileHash(filePath)
		okay := err == nil && h == s.SHA256 && n == s.Bytes
		r.FileValid = &okay
		if !okay {
			r.Message = "file digest/length does not match signed statement"
			return r
		}
	}
	r.Valid = true
	r.Message = "signature valid"
	if filePath != "" {
		r.Message = "signature and file hash valid"
	}
	return r
}
func EnvelopeDigest(e Envelope) string {
	b, _ := json.Marshal(e)
	h := sha256.Sum256(b)
	return hex.EncodeToString(h[:])
}
func Save(path string, e Envelope) error {
	b, err := json.MarshalIndent(e, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(path, append(b, '\n'), 0600)
}
func Read(path string) (Envelope, error) {
	var e Envelope
	b, err := os.ReadFile(path)
	if err != nil {
		return e, err
	}
	if err = json.Unmarshal(b, &e); err != nil {
		return e, fmt.Errorf("invalid envelope: %w", err)
	}
	return e, nil
}
