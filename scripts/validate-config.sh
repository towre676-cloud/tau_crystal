#!/bin/bash
if ! [ -f config/sidecar.yaml ]; then
  echo "Error: config/sidecar.yaml not found"
  exit 1
fi
if ! command -v yq >/dev/null; then
  echo "Error: yq required (install via 'snap install yq' or similar)"
  exit 1
fi
yq e '.sidecar.transcript.required | contains(["id", "timestamp", "event_type"])' config/sidecar.yaml || {
  echo "Error: sidecar.yaml missing required transcript fields"
  exit 1
}
echo "Config valid"
exit 0
