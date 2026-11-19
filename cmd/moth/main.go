// Moth Companion: a real local-first Windows application with a responsive
// desktop window powered by the installed Edge/Chrome browser engine.
// Its HTTP server only binds the IPv4 loopback interface on a random port.
package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/sha256"
	"embed"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"log"
	"mothcompanion/internal/witness"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"time"
)

//go:embed ui/*
var webUI embed.FS

const Version = "0.1.1"

type Memory struct {
	ID      string `json:"id"`
	Text    string `json:"text"`
	Created string `json:"created"`
	Kind    string `json:"kind"`
}
type Turn struct {
	Role   string `json:"role"`
	Text   string `json:"text"`
	At     string `json:"at"`
	Engine string `json:"engine,omitempty"`
}
type Event struct {
	ID   string `json:"id"`
	At   string `json:"at"`
	Kind string `json:"kind"`
	Text string `json:"text"`
}
type Task struct {
	ID        string `json:"id"`
	Text      string `json:"text"`
	Due       string `json:"due,omitempty"`
	Done      bool   `json:"done"`
	Created   string `json:"created"`
	Completed string `json:"completed,omitempty"`
}
type Capture struct {
	ID            string `json:"id"`
	When          string `json:"when"`
	Node          string `json:"node"`
	Fingerprint   string `json:"fingerprint"`
	ContentHash   string `json:"content_hash"`
	ContentBytes  int64  `json:"content_bytes"`
	Verified      bool   `json:"verified"`
	MediaVerified bool   `json:"media_verified"`
	Trusted       bool   `json:"trusted"`
	Method        string `json:"method"`
}
type Settings struct {
	Voice     bool   `json:"voice"`
	Ollama    bool   `json:"ollama"`
	Model     string `json:"model"`
	LowMotion bool   `json:"low_motion"`
}
type State struct {
	Version       string            `json:"version"`
	CompanionName string            `json:"companion_name"`
	CompanionKind string            `json:"companion_kind"`
	UserName      string            `json:"user_name"`
	Personality   string            `json:"personality"`
	Bond          int               `json:"bond"`
	Energy        int               `json:"energy"`
	Mood          string            `json:"mood"`
	FirstMet      string            `json:"first_met"`
	LastSeen      string            `json:"last_seen"`
	Memories      []Memory          `json:"memories"`
	Turns         []Turn            `json:"turns"`
	Events        []Event           `json:"events"`
	Tasks         []Task            `json:"tasks"`
	Captures      []Capture         `json:"captures"`
	TrustedKeys   map[string]string `json:"trusted_keys"`
	Settings      Settings          `json:"settings"`
}
type Ledger struct {
	Seq         int    `json:"seq"`
	UTC         string `json:"utc"`
	Kind        string `json:"kind"`
	PayloadHash string `json:"payload_hash"`
	Previous    string `json:"previous"`
	Digest      string `json:"digest"`
	Signature   string `json:"signature"`
}
type App struct {
	mu            sync.Mutex
	state         State
	dir           string
	private       ed25519.PrivateKey
	ledgerFile    string
	server        *http.Server
	url           string
	lastHeartbeat time.Time
	heartbeatSeen bool
}

func utc() string            { return time.Now().UTC().Format(time.RFC3339Nano) }
func digest(b []byte) string { h := sha256.Sum256(b); return hex.EncodeToString(h[:]) }
func clamp(v, lo, hi int) int {
	if v < lo {
		return lo
	}
	if v > hi {
		return hi
	}
	return v
}
func newApp(dir string) (*App, error) {
	if err := os.MkdirAll(dir, 0700); err != nil {
		return nil, err
	}
	priv, err := witness.Key(filepath.Join(dir, "identity.ed25519"))
	if err != nil {
		return nil, err
	}
	a := &App{dir: dir, private: priv, ledgerFile: filepath.Join(dir, "events.signed.jsonl")}
	path := filepath.Join(dir, "nest.json")
	if b, err := os.ReadFile(path); err == nil {
		if err = json.Unmarshal(b, &a.state); err != nil {
			return nil, fmt.Errorf("could not read local nest: %w", err)
		}
	} else if os.IsNotExist(err) {
		a.state = State{Version: Version, CompanionName: "Moth", CompanionKind: "moth", Personality: "curious", Bond: 6, Energy: 82, Mood: "curious", FirstMet: utc(), Settings: Settings{Model: "llama3.2"}, TrustedKeys: map[string]string{}, Memories: []Memory{}, Turns: []Turn{}, Events: []Event{}, Tasks: []Task{}, Captures: []Capture{}}
	} else {
		return nil, err
	}
	if a.state.TrustedKeys == nil {
		a.state.TrustedKeys = map[string]string{}
	}
	if a.state.CompanionName == "" {
		a.state.CompanionName = "Moth"
	}
	if a.state.Settings.Model == "" {
		a.state.Settings.Model = "llama3.2"
	}
	a.state.Version = Version
	a.state.LastSeen = utc()
	if err := a.saveLocked(); err != nil {
		return nil, err
	}
	return a, nil
}
func (a *App) saveLocked() error {
	b, err := json.MarshalIndent(a.state, "", "  ")
	if err != nil {
		return err
	}
	tmp, err := os.CreateTemp(a.dir, "nest-*.tmp")
	if err != nil {
		return err
	}
	n := tmp.Name()
	defer os.Remove(n)
	if err := tmp.Chmod(0600); err != nil {
		tmp.Close()
		return err
	}
	if _, err = tmp.Write(append(b, '\n')); err != nil {
		tmp.Close()
		return err
	}
	if err = tmp.Sync(); err != nil {
		tmp.Close()
		return err
	}
	if err = tmp.Close(); err != nil {
		return err
	}
	return os.Rename(n, filepath.Join(a.dir, "nest.json"))
}
func (a *App) recordLocked(kind string, payload []byte) error {
	entries, err := readLedger(a.ledgerFile)
	if err != nil {
		return err
	}
	prev := ""
	if len(entries) > 0 {
		prev = entries[len(entries)-1].Digest
	}
	e := Ledger{Seq: len(entries) + 1, UTC: utc(), Kind: kind, PayloadHash: digest(payload), Previous: prev}
	e.Digest = ledgerDigest(e)
	e.Signature = hex.EncodeToString(ed25519.Sign(a.private, []byte(e.Digest)))
	f, err := os.OpenFile(a.ledgerFile, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0600)
	if err != nil {
		return err
	}
	b, _ := json.Marshal(e)
	if _, err = f.Write(append(b, '\n')); err != nil {
		f.Close()
		return err
	}
	return f.Close()
}
func ledgerDigest(e Ledger) string {
	return digest([]byte(fmt.Sprintf("moth-ledger/v1\n%d\n%s\n%s\n%s\n%s", e.Seq, e.UTC, e.Kind, e.PayloadHash, e.Previous)))
}
func readLedger(path string) ([]Ledger, error) {
	var es []Ledger
	b, err := os.ReadFile(path)
	if os.IsNotExist(err) {
		return es, nil
	}
	if err != nil {
		return nil, err
	}
	for i, line := range bytes.Split(bytes.TrimSpace(b), []byte("\n")) {
		if len(line) == 0 {
			continue
		}
		var e Ledger
		if err := json.Unmarshal(line, &e); err != nil {
			return nil, fmt.Errorf("ledger line %d: %w", i+1, err)
		}
		es = append(es, e)
	}
	return es, nil
}
func (a *App) verifyLedger() map[string]interface{} {
	a.mu.Lock()
	defer a.mu.Unlock()
	es, err := readLedger(a.ledgerFile)
	if err != nil {
		return map[string]interface{}{"valid": false, "message": err.Error()}
	}
	prev := ""
	pub := a.private.Public().(ed25519.PublicKey)
	for i, e := range es {
		sig, err := hex.DecodeString(e.Signature)
		if err != nil || e.Seq != i+1 || e.Previous != prev || e.Digest != ledgerDigest(e) || !ed25519.Verify(pub, []byte(e.Digest), sig) {
			return map[string]interface{}{"valid": false, "count": len(es), "failure_at": i + 1, "message": "signature, ordering, or hash-chain failed"}
		}
		prev = e.Digest
	}
	return map[string]interface{}{"valid": true, "count": len(es), "head": prev, "fingerprint": witness.Fingerprint(pub), "message": "local event-signature chain verifies; this is not independent sensor attestation"}
}
func (a *App) addEventLocked(kind, text string) {
	a.state.Events = append(a.state.Events, Event{ID: fmt.Sprintf("e%d", time.Now().UnixNano()), At: utc(), Kind: kind, Text: text})
	if len(a.state.Events) > 180 {
		a.state.Events = a.state.Events[len(a.state.Events)-180:]
	}
}
func (a *App) addMemoryLocked(s, kind string) (Memory, error) {
	s = strings.TrimSpace(s)
	if len([]rune(s)) > 500 {
		return Memory{}, errors.New("memory must be 500 characters or fewer")
	}
	if s == "" {
		return Memory{}, errors.New("memory is blank")
	}
	m := Memory{ID: fmt.Sprintf("m%d", time.Now().UnixNano()), Text: s, Kind: kind, Created: utc()}
	a.state.Memories = append(a.state.Memories, m)
	a.addEventLocked("memory", "A new detail was remembered")
	a.state.Bond = clamp(a.state.Bond+2, 0, 100)
	if err := a.recordLocked("memory-added", []byte(s)); err != nil {
		return Memory{}, err
	}
	return m, a.saveLocked()
}
func writeJSON(w http.ResponseWriter, code int, x interface{}) {
	w.Header().Set("Content-Type", "application/json; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	w.WriteHeader(code)
	_ = json.NewEncoder(w).Encode(x)
}
func decodeJSON(w http.ResponseWriter, r *http.Request, dst interface{}) bool {
	r.Body = http.MaxBytesReader(w, r.Body, 64<<10)
	if err := json.NewDecoder(r.Body).Decode(dst); err != nil {
		writeJSON(w, 400, map[string]string{"error": "Invalid request: " + err.Error()})
		return false
	}
	return true
}
func (a *App) mutate(fn func(http.ResponseWriter, *http.Request)) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != "POST" && r.Method != "DELETE" {
			http.Error(w, "method not allowed", 405)
			return
		}
		if r.Header.Get("X-Moth-Local") != "1" {
			http.Error(w, "local application header required", 403)
			return
		}
		if origin := r.Header.Get("Origin"); origin != "" && origin != "http://"+r.Host {
			http.Error(w, "foreign origin forbidden", 403)
			return
		}
		fn(w, r)
	}
}
func (a *App) handler() http.Handler {
	mux := http.NewServeMux()
	root, _ := fs.Sub(webUI, "ui")
	mux.Handle("/", http.FileServer(http.FS(root)))
	mux.HandleFunc("/api/state", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != "GET" {
			http.Error(w, "method", 405)
			return
		}
		a.mu.Lock()
		defer a.mu.Unlock()
		writeJSON(w, 200, a.state)
	})
	mux.HandleFunc("/api/status", func(w http.ResponseWriter, r *http.Request) {
		a.mu.Lock()
		defer a.mu.Unlock()
		writeJSON(w, 200, map[string]interface{}{"version": Version, "port": a.url, "fingerprint": witness.Fingerprint(a.private.Public().(ed25519.PublicKey)), "store": "local-only", "model": a.state.Settings.Model, "ollama_enabled": a.state.Settings.Ollama})
	})
	mux.HandleFunc("/api/ledger/verify", func(w http.ResponseWriter, r *http.Request) { writeJSON(w, 200, a.verifyLedger()) })
	mux.HandleFunc("/api/pet", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		var p struct {
			Action string `json:"action"`
		}
		if !decodeJSON(w, r, &p) {
			return
		}
		a.mu.Lock()
		defer a.mu.Unlock()
		switch p.Action {
		case "pet":
			a.state.Bond = clamp(a.state.Bond+1, 0, 100)
			a.state.Mood = "content"
			a.state.Energy = clamp(a.state.Energy-1, 0, 100)
		case "play":
			a.state.Energy = clamp(a.state.Energy-6, 0, 100)
			a.state.Bond = clamp(a.state.Bond+2, 0, 100)
			a.state.Mood = "bright"
		case "rest":
			a.state.Energy = clamp(a.state.Energy+14, 0, 100)
			a.state.Mood = "peaceful"
		case "explore":
			a.state.Mood = "curious"
		default:
			writeJSON(w, 400, map[string]string{"error": "unknown action"})
			return
		}
		a.addEventLocked("interaction", p.Action)
		_ = a.recordLocked("interaction", []byte(p.Action))
		_ = a.saveLocked()
		writeJSON(w, 200, map[string]interface{}{"bond": a.state.Bond, "energy": a.state.Energy, "mood": a.state.Mood})
	}))
	mux.HandleFunc("/api/settings", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		var p struct {
			Name        string `json:"name"`
			UserName    string `json:"user_name"`
			Personality string `json:"personality"`
			Model       string `json:"model"`
			Ollama      bool   `json:"ollama"`
			Voice       bool   `json:"voice"`
			LowMotion   bool   `json:"low_motion"`
		}
		if !decodeJSON(w, r, &p) {
			return
		}
		a.mu.Lock()
		defer a.mu.Unlock()
		if n := strings.TrimSpace(p.Name); n != "" && len([]rune(n)) <= 30 {
			a.state.CompanionName = n
		}
		if len([]rune(p.UserName)) <= 50 {
			a.state.UserName = strings.TrimSpace(p.UserName)
		}
		if p.Personality == "curious" || p.Personality == "gentle" || p.Personality == "mischievous" {
			a.state.Personality = p.Personality
		}
		if n := strings.TrimSpace(p.Model); len(n) > 0 && len(n) <= 80 {
			a.state.Settings.Model = n
		}
		a.state.Settings.Ollama = p.Ollama
		a.state.Settings.Voice = p.Voice
		a.state.Settings.LowMotion = p.LowMotion
		_ = a.saveLocked()
		writeJSON(w, 200, map[string]interface{}{"ok": true})
	}))
	mux.HandleFunc("/api/memory", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		if r.Method == "DELETE" {
			id := r.URL.Query().Get("id")
			a.mu.Lock()
			defer a.mu.Unlock()
			found := false
			for i, m := range a.state.Memories {
				if m.ID == id {
					a.state.Memories = append(a.state.Memories[:i], a.state.Memories[i+1:]...)
					found = true
					break
				}
			}
			if !found {
				writeJSON(w, 404, map[string]string{"error": "not found"})
				return
			}
			_ = a.recordLocked("memory-deleted", []byte(id))
			_ = a.saveLocked()
			writeJSON(w, 200, map[string]bool{"ok": true})
			return
		}
		var p struct {
			Text string `json:"text"`
		}
		if !decodeJSON(w, r, &p) {
			return
		}
		a.mu.Lock()
		defer a.mu.Unlock()
		m, err := a.addMemoryLocked(p.Text, "explicit")
		if err != nil {
			writeJSON(w, 400, map[string]string{"error": err.Error()})
			return
		}
		writeJSON(w, 200, m)
	}))
	mux.HandleFunc("/api/chat", a.mutate(a.handleChat))
	mux.HandleFunc("/api/heartbeat", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		a.mu.Lock()
		a.lastHeartbeat = time.Now()
		a.heartbeatSeen = true
		a.mu.Unlock()
		writeJSON(w, 200, map[string]bool{"ok": true})
	}))
	mux.HandleFunc("/api/witness/import", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		var e witness.Envelope
		if !decodeJSON(w, r, &e) {
			return
		}
		res := witness.Check(e, "")
		if !res.Valid {
			writeJSON(w, 422, res)
			return
		}
		a.mu.Lock()
		defer a.mu.Unlock()
		_, trusted := a.state.TrustedKeys[res.Fingerprint]
		c := Capture{ID: fmt.Sprintf("c%d", time.Now().UnixNano()), When: utc(), Node: res.NodeID, Fingerprint: res.Fingerprint, ContentHash: res.ContentSHA256, ContentBytes: e.Statement.Bytes, Verified: true, Trusted: trusted, Method: res.CaptureMethod}
		a.state.Captures = append(a.state.Captures, c)
		if len(a.state.Captures) > 100 {
			a.state.Captures = a.state.Captures[len(a.state.Captures)-100:]
		}
		a.addEventLocked("witness", "Signed capture received from "+res.NodeID)
		_ = a.recordLocked("capture-attached", []byte(res.ContentSHA256))
		_ = a.saveLocked()
		writeJSON(w, 200, map[string]interface{}{"verification": res, "trusted": trusted, "capture": c})
	}))
	mux.HandleFunc("/api/witness/media", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "POST required", http.StatusMethodNotAllowed)
			return
		}
		id := r.URL.Query().Get("id")
		a.mu.Lock()
		var expectedHash string
		var expectedBytes int64
		for _, c := range a.state.Captures {
			if c.ID == id {
				expectedHash, expectedBytes = c.ContentHash, c.ContentBytes
				break
			}
		}
		a.mu.Unlock()
		if expectedHash == "" {
			writeJSON(w, 404, map[string]string{"error": "Import the signed receipt before verifying media"})
			return
		}
		const maxMediaBytes int64 = 512 << 20
		if expectedBytes < 0 || expectedBytes > maxMediaBytes || r.ContentLength > maxMediaBytes {
			writeJSON(w, http.StatusRequestEntityTooLarge, map[string]string{"error": "Capture file exceeds the local 512 MiB verification limit"})
			return
		}
		hasher := sha256.New()
		length, err := io.Copy(hasher, io.LimitReader(r.Body, maxMediaBytes+1))
		if err != nil {
			writeJSON(w, 400, map[string]string{"error": "Media read failed: " + err.Error()})
			return
		}
		actual := hex.EncodeToString(hasher.Sum(nil))
		if length > maxMediaBytes || length != expectedBytes || actual != expectedHash {
			writeJSON(w, http.StatusUnprocessableEntity, map[string]interface{}{"matched": false, "bytes": length, "sha256": actual, "error": "Media file length or SHA-256 differs from the signed receipt"})
			return
		}
		a.mu.Lock()
		for i := range a.state.Captures {
			if a.state.Captures[i].ID == id {
				a.state.Captures[i].MediaVerified = true
				break
			}
		}
		a.addEventLocked("witness", "File bytes independently checked against signed receipt")
		if err := a.recordLocked("media-verified", []byte(expectedHash)); err != nil {
			a.mu.Unlock()
			writeJSON(w, 500, map[string]string{"error": err.Error()})
			return
		}
		if err := a.saveLocked(); err != nil {
			a.mu.Unlock()
			writeJSON(w, 500, map[string]string{"error": err.Error()})
			return
		}
		a.mu.Unlock()
		writeJSON(w, 200, map[string]interface{}{"matched": true, "bytes": length, "sha256": actual, "note": "Media bytes match signed metadata. This does not prove sensor firmware or physical custody."})
	}))
	mux.HandleFunc("/api/witness/trust", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		var p struct {
			Fingerprint string `json:"fingerprint"`
			Node        string `json:"node"`
		}
		if !decodeJSON(w, r, &p) {
			return
		}
		if len(p.Fingerprint) != 24 || len(p.Node) == 0 || len(p.Node) > 80 {
			writeJSON(w, 400, map[string]string{"error": "fingerprint and device name required"})
			return
		}
		a.mu.Lock()
		defer a.mu.Unlock()
		found := false
		for _, c := range a.state.Captures {
			if c.Fingerprint == p.Fingerprint {
				found = true
				break
			}
		}
		if !found {
			writeJSON(w, 400, map[string]string{"error": "import a signed capture from this key first"})
			return
		}
		a.state.TrustedKeys[p.Fingerprint] = p.Node
		_ = a.recordLocked("trust-granted", []byte(p.Fingerprint))
		_ = a.saveLocked()
		writeJSON(w, 200, map[string]bool{"ok": true})
	}))
	mux.HandleFunc("/api/task", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		var p struct {
			Action string `json:"action"`
			ID     string `json:"id"`
			Text   string `json:"text"`
			Due    string `json:"due"`
		}
		if !decodeJSON(w, r, &p) {
			return
		}
		a.mu.Lock()
		defer a.mu.Unlock()
		switch p.Action {
		case "add":
			p.Text = strings.TrimSpace(p.Text)
			if len([]rune(p.Text)) == 0 || len([]rune(p.Text)) > 240 || len(a.state.Tasks) > 2500 {
				writeJSON(w, 400, map[string]string{"error": "Task must be 1–240 characters; maximum 2,500 tasks"})
				return
			}
			if p.Due != "" {
				if _, err := time.Parse("2006-01-02", p.Due); err != nil {
					writeJSON(w, 400, map[string]string{"error": "Expected due date YYYY-MM-DD"})
					return
				}
			}
			t := Task{ID: fmt.Sprintf("t%d", time.Now().UnixNano()), Text: p.Text, Due: p.Due, Created: utc()}
			a.state.Tasks = append(a.state.Tasks, t)
			a.addEventLocked("task", "Created a plan")
			_ = a.recordLocked("task-added", []byte(p.Text))
		case "toggle", "delete":
			found := -1
			for i, t := range a.state.Tasks {
				if t.ID == p.ID {
					found = i
					break
				}
			}
			if found < 0 {
				writeJSON(w, 404, map[string]string{"error": "Task not found"})
				return
			}
			if p.Action == "delete" {
				a.state.Tasks = append(a.state.Tasks[:found], a.state.Tasks[found+1:]...)
			} else {
				t := &a.state.Tasks[found]
				t.Done = !t.Done
				if t.Done {
					t.Completed = utc()
					a.state.Bond = clamp(a.state.Bond+1, 0, 100)
				} else {
					t.Completed = ""
				}
			}
			_ = a.recordLocked("task-"+p.Action, []byte(p.ID))
		default:
			writeJSON(w, 400, map[string]string{"error": "Unknown task action"})
			return
		}
		if err := a.saveLocked(); err != nil {
			writeJSON(w, 500, map[string]string{"error": err.Error()})
			return
		}
		writeJSON(w, 200, map[string]interface{}{"ok": true, "tasks": a.state.Tasks})
	}))
	mux.HandleFunc("/api/focus", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		var p struct {
			Minutes int `json:"minutes"`
		}
		if !decodeJSON(w, r, &p) {
			return
		}
		if p.Minutes < 1 || p.Minutes > 180 {
			writeJSON(w, 400, map[string]string{"error": "Invalid focus duration"})
			return
		}
		a.mu.Lock()
		defer a.mu.Unlock()
		a.addEventLocked("focus", fmt.Sprintf("Shared %d focused minutes", p.Minutes))
		a.state.Bond = clamp(a.state.Bond+1, 0, 100)
		_ = a.recordLocked("focus-finished", []byte(fmt.Sprint(p.Minutes)))
		_ = a.saveLocked()
		writeJSON(w, 200, map[string]bool{"ok": true})
	}))
	mux.HandleFunc("/api/export", func(w http.ResponseWriter, r *http.Request) {
		a.mu.Lock()
		defer a.mu.Unlock()
		w.Header().Set("Content-Disposition", "attachment; filename=Moth-Nest-Backup.json")
		writeJSON(w, 200, a.state)
	})
	mux.HandleFunc("/api/import", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		var s State
		if !decodeJSON(w, r, &s) {
			return
		}
		if len(s.Memories) > 10000 || len(s.Turns) > 50000 || len(s.CompanionName) > 100 || len(s.Events) > 2000 || len(s.Tasks) > 2500 {
			writeJSON(w, 400, map[string]string{"error": "import exceeds safety limits"})
			return
		}
		if s.CompanionName == "" {
			writeJSON(w, 400, map[string]string{"error": "not a nest backup"})
			return
		}
		a.mu.Lock()
		defer a.mu.Unlock()
		a.state = s
		if a.state.TrustedKeys == nil {
			a.state.TrustedKeys = map[string]string{}
		}
		a.state.Version = Version
		_ = a.recordLocked("nest-imported", []byte(fmt.Sprint(len(s.Memories), len(s.Turns))))
		_ = a.saveLocked()
		writeJSON(w, 200, map[string]bool{"ok": true})
	}))
	mux.HandleFunc("/api/quit", a.mutate(func(w http.ResponseWriter, r *http.Request) {
		writeJSON(w, 200, map[string]bool{"ok": true})
		go func() { time.Sleep(250 * time.Millisecond); _ = a.server.Close() }()
	}))
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Reject DNS-rebinding and alternate-host attempts against this loopback service.
		if a.url != "" && r.Host != strings.TrimPrefix(a.url, "http://") {
			http.Error(w, "invalid local host", http.StatusForbidden)
			return
		}
		w.Header().Set("X-Content-Type-Options", "nosniff")
		w.Header().Set("Referrer-Policy", "no-referrer")
		w.Header().Set("X-Frame-Options", "DENY")
		w.Header().Set("Content-Security-Policy", "default-src 'self'; connect-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; font-src 'self' data:; object-src 'none'; frame-ancestors 'none'; base-uri 'none'; form-action 'self'")
		mux.ServeHTTP(w, r)
	})
}
func (a *App) handleChat(w http.ResponseWriter, r *http.Request) {
	var p struct {
		Message string `json:"message"`
	}
	if !decodeJSON(w, r, &p) {
		return
	}
	msg := strings.TrimSpace(p.Message)
	if msg == "" || len([]rune(msg)) > 1600 {
		writeJSON(w, 400, map[string]string{"error": "message must be 1–1600 characters"})
		return
	}
	a.mu.Lock()
	s := a.state
	a.mu.Unlock()
	reply := ""
	engine := "offline"
	lower := strings.ToLower(msg)
	if strings.HasPrefix(lower, "remember that ") {
		text := strings.TrimSpace(msg[len("remember that "):])
		a.mu.Lock()
		m, err := a.addMemoryLocked(text, "explicit")
		a.mu.Unlock()
		if err != nil {
			writeJSON(w, 400, map[string]string{"error": err.Error()})
			return
		}
		reply = "I saved that to our nest: “" + m.Text + "”. You can edit what I remember by deleting it from the Memory garden."
	} else if s.Settings.Ollama {
		ctx, done := makeTimeoutContext(r, 38*time.Second)
		defer done()
		ans, err := askOllama(ctx, msg, s)
		if err == nil && strings.TrimSpace(ans) != "" {
			reply = ans
			engine = "ollama"
		} else {
			reply = "I couldn't reach your local model, so I'm answering in my simple offline mode. " + offlineReply(msg, s)
			engine = "offline-fallback"
		}
	} else {
		reply = offlineReply(msg, s)
	}
	a.mu.Lock()
	a.state.Turns = append(a.state.Turns, Turn{Role: "user", Text: msg, At: utc()}, Turn{Role: "assistant", Text: reply, At: utc(), Engine: engine})
	if len(a.state.Turns) > 500 {
		a.state.Turns = a.state.Turns[len(a.state.Turns)-500:]
	}
	a.state.Energy = clamp(a.state.Energy-1, 0, 100)
	a.state.Bond = clamp(a.state.Bond+1, 0, 100)
	a.state.Mood = "attentive"
	a.addEventLocked("conversation", "You talked together")
	_ = a.recordLocked("conversation", []byte(msg+"\n"+reply))
	_ = a.saveLocked()
	a.mu.Unlock()
	writeJSON(w, 200, map[string]interface{}{"reply": reply, "engine": engine})
}

// Context alias defined in ai.go to keep model transport separate.
func offlineReply(msg string, s State) string {
	lower := strings.ToLower(msg)
	name := s.CompanionName
	if name == "" {
		name = "Moth"
	}
	if strings.Contains(lower, "what do you remember") || strings.Contains(lower, "remember about me") {
		if len(s.Memories) == 0 {
			return "Our memory garden is empty so far. Say ‘remember that ...’ and I'll keep the detail on this computer. You can review and erase it whenever you like."
		}
		parts := []string{}
		for i := len(s.Memories) - 1; i >= 0 && len(parts) < 3; i-- {
			parts = append(parts, "“"+s.Memories[i].Text+"”")
		}
		return "Here are a few things I keep for us: " + strings.Join(parts, "; ") + ". Nothing leaves this computer unless you export it."
	}
	if strings.Contains(lower, "what can you do") || strings.Contains(lower, "help") {
		return "I keep our conversations and deliberate memories, speak aloud if you enable it, help with focus rituals, and connect to physical motion hardware through USB. With a local Ollama model I can hold open-ended conversations. Signed Pi witness receipts can be checked separately—without pretending a signature proves sensor authenticity."
	}
	if strings.Contains(lower, "how are you") || strings.Contains(lower, "how do you feel") {
		return "A little " + s.Mood + " today. My energy is at " + fmt.Sprint(s.Energy) + ". These are companion behavior signals, not claims of human feelings. Want to explore something, or just have a quiet moment together?"
	}
	if strings.Contains(lower, "good morning") || strings.Contains(lower, "morning") {
		return "Good morning. What's one small thing you want to make easier today? I'll stay beside the work, not on top of it."
	}
	if strings.Contains(lower, "good night") || strings.Contains(lower, "goodnight") {
		return "A good place to end. Your memories are saved locally; we'll pick up where we left off."
	}
	if strings.Contains(lower, "sad") || strings.Contains(lower, "lonely") || strings.Contains(lower, "anxious") {
		return "I'm here to listen. Would it help to name what's weighing on you, or would you prefer a simple grounding rhythm? You don't have to turn it into a task."
	}
	if strings.Contains(lower, "project") || strings.Contains(lower, "building") || strings.Contains(lower, "make a") {
		return "Tell me what the next concrete milestone is. I can keep it as a memory, and a local language model can help us plan it in detail. I won't pretend I've completed actions I haven't taken."
	}
	if strings.Contains(lower, "favorite") || strings.Contains(lower, "my name") {
		return "I can keep that. Say ‘remember that ...’ and I'll store your exact words in the memory garden."
	}
	if strings.Contains(lower, "hardware") || strings.Contains(lower, "furby") || strings.Contains(lower, "servo") {
		return "The USB workshop can send bounded motion commands to an RP2040/Arduino controller. That means actual actuator movement when a correctly wired device is attached. The physical swarm and calibration goals are separate engineering tests—not an animation masquerading as hardware."
	}
	if strings.Contains(lower, "hello") || strings.Contains(lower, "hi ") || lower == "hi" {
		if s.UserName != "" {
			return "Hello, " + s.UserName + ". I've got our local nest ready. What's interesting today?"
		}
		return "Hey. I'm " + name + ". What should we get curious about?"
	}
	if strings.Contains(lower, "thank") {
		return "You're welcome. I like when the useful parts work quietly. What should we do next?"
	}
	replies := []string{"That sounds worth looking at. Tell me a little more about the part that matters most.", "I can hold on to that thought if you'd like. Say ‘remember that ...’ to keep it across restarts.", "I'm listening. Would you like to explore it together or turn it into a small next step?", "There's more than one way into that. What would a good result actually look like?", "I don't want to guess what you mean. What's the part you're thinking about right now?"}
	sum := sha256.Sum256([]byte(msg))
	idx := int(sum[0]) % len(replies)
	return replies[idx]
}
func openWindow(url string) error {
	if runtime.GOOS == "windows" {
		paths := []string{filepath.Join(os.Getenv("ProgramFiles(x86)"), "Microsoft", "Edge", "Application", "msedge.exe"), filepath.Join(os.Getenv("ProgramFiles"), "Microsoft", "Edge", "Application", "msedge.exe")}
		for _, p := range paths {
			if _, err := os.Stat(p); err == nil {
				return exec.Command(p, "--app="+url, "--window-size=1280,900").Start()
			}
		}
		return exec.Command("rundll32.exe", "url.dll,FileProtocolHandler", url).Start()
	}
	if runtime.GOOS == "darwin" {
		return exec.Command("open", url).Start()
	}
	return exec.Command("xdg-open", url).Start()
}

// The desktop executable owns a local server. If its window vanishes and
// periodic local heartbeats stop, release the port and exit instead of
// stranding a hidden background executable on Windows.
func (a *App) startWindowWatchdog() {
	go func() {
		ticker := time.NewTicker(15 * time.Second)
		defer ticker.Stop()
		for range ticker.C {
			a.mu.Lock()
			closed := a.heartbeatSeen && time.Since(a.lastHeartbeat) > 135*time.Second
			a.mu.Unlock()
			if closed {
				log.Print("Companion window heartbeat expired; shutting down")
				_ = a.server.Close()
				return
			}
		}
	}()
}

func main() {
	noBrowser := flag.Bool("no-browser", false, "do not open the desktop window")
	data := flag.String("data-dir", "", "override the local data directory (for development/testing)")
	port := flag.Int("port", 0, "loopback port; zero selects a free random port")
	flag.Parse()
	dir := *data
	if dir == "" {
		base, err := os.UserConfigDir()
		if err != nil {
			log.Fatal(err)
		}
		dir = filepath.Join(base, "MothCompanion")
	}
	a, err := newApp(dir)
	if err != nil {
		log.Fatal(err)
	}
	logFile, err := os.OpenFile(filepath.Join(dir, "companion.log"), os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0600)
	if err == nil {
		defer logFile.Close()
		log.SetOutput(logFile)
	}
	listener, err := net.Listen("tcp", fmt.Sprintf("127.0.0.1:%d", *port))
	if err != nil {
		log.Fatal(err)
	}
	a.url = "http://" + listener.Addr().String()
	a.server = &http.Server{Handler: a.handler(), ReadHeaderTimeout: 6 * time.Second, ReadTimeout: 45 * time.Second, WriteTimeout: 50 * time.Second, IdleTimeout: 60 * time.Second}
	fmt.Println("Moth Companion running at", a.url)
	if !*noBrowser {
		a.startWindowWatchdog()
		if err := openWindow(a.url); err != nil {
			log.Println("Could not launch window:", err)
		}
	}
	if err := a.server.Serve(listener); err != nil && err != http.ErrServerClosed {
		log.Fatal(err)
	}
}
