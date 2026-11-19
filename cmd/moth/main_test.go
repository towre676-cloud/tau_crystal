package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/rand"
	"encoding/json"
	"mothcompanion/internal/witness"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func req(t *testing.T, h http.Handler, method, url string, body interface{}, local bool) *httptest.ResponseRecorder {
	t.Helper()
	var b []byte
	if body != nil {
		b, _ = json.Marshal(body)
	}
	r := httptest.NewRequest(method, url, bytes.NewReader(b))
	if local {
		r.Header.Set("X-Moth-Local", "1")
	}
	w := httptest.NewRecorder()
	h.ServeHTTP(w, r)
	return w
}
func TestCompanionEndToEnd(t *testing.T) {
	dir := t.TempDir()
	a, err := newApp(dir)
	if err != nil {
		t.Fatal(err)
	}
	h := a.handler()
	if w := req(t, h, "GET", "/", nil, false); w.Code != 200 || !strings.Contains(w.Body.String(), "Memory garden") {
		t.Fatalf("web app unavailable: %d", w.Code)
	}
	if w := req(t, h, "POST", "/api/memory", map[string]string{"text": "I love pine forests"}, false); w.Code != 403 {
		t.Fatalf("Cross-site request accepted: %d", w.Code)
	}
	if w := req(t, h, "POST", "/api/memory", map[string]string{"text": "I love pine forests"}, true); w.Code != 200 {
		t.Fatalf("Memory add failed: %d %s", w.Code, w.Body.String())
	}
	if w := req(t, h, "POST", "/api/chat", map[string]string{"message": "What do you remember about me?"}, true); w.Code != 200 || !strings.Contains(w.Body.String(), "pine forests") {
		t.Fatalf("Recall failed: %d %s", w.Code, w.Body.String())
	}
	if w := req(t, h, "GET", "/api/ledger/verify", nil, false); !strings.Contains(w.Body.String(), "\"valid\":true") {
		t.Fatalf("Journal verification failed: %s", w.Body.String())
	}
	again, err := newApp(dir)
	if err != nil {
		t.Fatal(err)
	}
	if len(again.state.Memories) != 1 || len(again.state.Turns) != 2 {
		t.Fatalf("State did not persist: %+v", again.state)
	}
	f := filepath.Join(dir, "events.signed.jsonl")
	b, _ := os.ReadFile(f)
	b = bytes.Replace(b, []byte("memory-added"), []byte("memory-wrong"), 1)
	os.WriteFile(f, b, 0600)
	if w := req(t, again.handler(), "GET", "/api/ledger/verify", nil, false); !strings.Contains(w.Body.String(), "\"valid\":false") {
		t.Fatalf("Tampered journal accepted: %s", w.Body.String())
	}
}
func TestWitnessImportRequiresSignatureAndTrust(t *testing.T) {
	dir := t.TempDir()
	a, _ := newApp(dir)
	h := a.handler()
	f := filepath.Join(dir, "video.dat")
	os.WriteFile(f, []byte("sensor acquisition"), 0600)
	_, priv, _ := ed25519.GenerateKey(rand.Reader)
	e, _ := witness.Make(f, "pi-01", "sensor-pipeline", "pi-direct", "", priv)
	w := req(t, h, "POST", "/api/witness/import", e, true)
	if w.Code != 200 || !strings.Contains(w.Body.String(), "\"trusted\":false") {
		t.Fatalf("New signing key should not be trusted: %s", w.Body.String())
	}
	fp := witness.Check(e, "").Fingerprint
	w = req(t, h, "POST", "/api/witness/trust", map[string]string{"fingerprint": fp, "node": "pi-01"}, true)
	if w.Code != 200 {
		t.Fatalf("Trust failed: %s", w.Body.String())
	}
	w = req(t, h, "POST", "/api/witness/import", e, true)
	if w.Code != 200 || !strings.Contains(w.Body.String(), "\"trusted\":true") {
		t.Fatalf("Previously trusted key rejected: %s", w.Body.String())
	}
	e.Statement.SHA256 = strings.Repeat("a", 64)
	w = req(t, h, "POST", "/api/witness/import", e, true)
	if w.Code != 422 {
		t.Fatalf("Tampered manifest accepted: %d", w.Code)
	}
}

func TestRejectsReboundHost(t *testing.T) {
	a, err := newApp(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	a.url = "http://127.0.0.1:44112"
	r := httptest.NewRequest("GET", "http://attacker.example:44112/api/state", nil)
	w := httptest.NewRecorder()
	a.handler().ServeHTTP(w, r)
	if w.Code != http.StatusForbidden {
		t.Fatalf("foreign Host accepted: %d", w.Code)
	}
	r = httptest.NewRequest("GET", "http://127.0.0.1:44112/api/state", nil)
	w = httptest.NewRecorder()
	a.handler().ServeHTTP(w, r)
	if w.Code != http.StatusOK {
		t.Fatalf("local Host rejected: %d", w.Code)
	}
}

// A signed manifest is NOT enough to claim the media bytes were verified.
// This regression test proves that an actual file mismatch is rejected and
// that a correct file updates the distinct media_verified flag.
func TestMediaVerificationRequiresOriginalBytes(t *testing.T) {
	a, err := newApp(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	h := a.handler()
	original := []byte("raw sensor acquisition payload — not just a signature")
	f := filepath.Join(t.TempDir(), "original.bin")
	if err := os.WriteFile(f, original, 0600); err != nil {
		t.Fatal(err)
	}
	_, priv, _ := ed25519.GenerateKey(rand.Reader)
	receipt, err := witness.Make(f, "moth-pi-02", "pi-microphone-direct", "physical-pi-microphone", "", priv)
	if err != nil {
		t.Fatal(err)
	}
	w := req(t, h, "POST", "/api/witness/import", receipt, true)
	if w.Code != 200 {
		t.Fatalf("receipt rejected: %d %s", w.Code, w.Body.String())
	}
	var imported struct {
		Capture Capture `json:"capture"`
	}
	if err := json.Unmarshal(w.Body.Bytes(), &imported); err != nil {
		t.Fatal(err)
	}
	if imported.Capture.MediaVerified {
		t.Fatal("manifest alone marked media as verified")
	}
	endpoint := "/api/witness/media?id=" + imported.Capture.ID
	bad := httptest.NewRequest("POST", endpoint, bytes.NewReader([]byte("replacement bytes")))
	bad.Header.Set("X-Moth-Local", "1")
	bw := httptest.NewRecorder()
	h.ServeHTTP(bw, bad)
	if bw.Code != 422 {
		t.Fatalf("altered media accepted: %d %s", bw.Code, bw.Body.String())
	}
	good := httptest.NewRequest("POST", endpoint, bytes.NewReader(original))
	good.Header.Set("X-Moth-Local", "1")
	gw := httptest.NewRecorder()
	h.ServeHTTP(gw, good)
	if gw.Code != 200 {
		t.Fatalf("correct media rejected: %d %s", gw.Code, gw.Body.String())
	}
	var report struct {
		Matched bool `json:"matched"`
	}
	if err := json.Unmarshal(gw.Body.Bytes(), &report); err != nil || !report.Matched {
		t.Fatalf("no verification proof: %s", gw.Body.String())
	}
	again, err := newApp(a.dir)
	if err != nil {
		t.Fatal(err)
	}
	if len(again.state.Captures) != 1 || !again.state.Captures[0].MediaVerified {
		t.Fatalf("media verification not persisted: %+v", again.state.Captures)
	}
	restricted := httptest.NewRequest("POST", endpoint, bytes.NewReader(original))
	restricted.Header.Set("X-Moth-Local", "1")
	restricted.Header.Set("Origin", "https://evil.example")
	rw := httptest.NewRecorder()
	h.ServeHTTP(rw, restricted)
	if rw.Code != 403 {
		t.Fatalf("cross-origin upload permitted: %d", rw.Code)
	}
}

func TestCompanionWindowHeartbeat(t *testing.T) {
	a, err := newApp(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	w := req(t, a.handler(), "POST", "/api/heartbeat", map[string]any{}, true)
	if w.Code != 200 {
		t.Fatalf("heartbeat failed: %d", w.Code)
	}
	a.mu.Lock()
	defer a.mu.Unlock()
	if !a.heartbeatSeen || time.Since(a.lastHeartbeat) > time.Second {
		t.Fatal("window heartbeat not retained")
	}
}
