package main

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"io"
	"net/http"
	"strings"
	"time"
)

func makeTimeoutContext(r *http.Request, t time.Duration) (context.Context, context.CancelFunc) {
	return context.WithTimeout(r.Context(), t)
}
func askOllama(ctx context.Context, msg string, s State) (string, error) {
	system := "You are " + s.CompanionName + ", an embodied desktop companion called Moth. Personality: " + s.Personality + ". Conversational, warm, clever, concise, practical, sometimes whimsical. You are not conscious, do not claim feelings or real-world senses. Be a useful collaborator and remember the user's explicit facts without inventing them. Don't claim any real device has moved, recording originated at sensor, or a task was done unless verified. Don't encourage emotional dependency. Data stays on this Windows computer by default. Your remembered facts: "
	for _, m := range s.Memories {
		system += "\n- " + m.Text
	}
	msgs := []map[string]string{{"role": "system", "content": system}}
	last := s.Turns
	if len(last) > 18 {
		last = last[len(last)-18:]
	}
	for _, t := range last {
		msgs = append(msgs, map[string]string{"role": t.Role, "content": t.Text})
	}
	msgs = append(msgs, map[string]string{"role": "user", "content": msg})
	body := map[string]interface{}{"model": s.Settings.Model, "stream": false, "messages": msgs, "options": map[string]interface{}{"temperature": 0.75}}
	b, _ := json.Marshal(body)
	req, err := http.NewRequestWithContext(ctx, "POST", "http://127.0.0.1:11434/api/chat", bytes.NewReader(b))
	if err != nil {
		return "", err
	}
	req.Header.Set("Content-Type", "application/json")
	client := &http.Client{Timeout: 36 * time.Second}
	res, err := client.Do(req)
	if err != nil {
		return "", err
	}
	defer res.Body.Close()
	if res.StatusCode != 200 {
		return "", errors.New("local model returned non-200")
	}
	limited := io.LimitReader(res.Body, 256<<10)
	var data struct {
		Message struct {
			Content string `json:"content"`
		} `json:"message"`
	}
	if err := json.NewDecoder(limited).Decode(&data); err != nil {
		return "", err
	}
	return strings.TrimSpace(data.Message.Content), nil
}
