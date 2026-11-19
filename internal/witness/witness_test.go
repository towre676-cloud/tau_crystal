package witness

import (
	"crypto/ed25519"
	"crypto/rand"
	"os"
	"path/filepath"
	"testing"
)

func TestWitnessAuthenticityAndTamper(t *testing.T) {
	d := t.TempDir()
	f := filepath.Join(d, "sensor.raw")
	os.WriteFile(f, []byte("original sensor bytes"), 0600)
	_, priv, _ := ed25519.GenerateKey(rand.Reader)
	e, err := Make(f, "pi-01", "direct-on-device", "pi-capture", "", priv)
	if err != nil {
		t.Fatal(err)
	}
	if r := Check(e, f); !r.Valid || r.FileValid == nil || !*r.FileValid {
		t.Fatalf("valid envelope failed: %+v", r)
	}
	os.WriteFile(f, []byte("altered stream"), 0600)
	if r := Check(e, f); r.Valid {
		t.Fatal("tampered stream accepted")
	}
	e.Statement.NodeID = "imposter"
	if r := Check(e, ""); r.Valid {
		t.Fatal("changed statement accepted")
	}
}
