#!/bin/bash
# Double-click to try the app on this Mac: starts a small local web server and opens the app in Firefox
# (or your default browser). Leave this Terminal window open while you use the app; close it to stop.
cd "$(dirname "$0")" || exit 1
PORT=8000
while lsof -iTCP:$PORT -sTCP:LISTEN >/dev/null 2>&1; do PORT=$((PORT + 1)); done
URL="http://localhost:$PORT/"
PY=$(command -v python3 || true)
if [ -z "$PY" ]; then
  echo "python3 was not found. Install it from python.org, then double-click this file again."
  read -n 1 -s -r -p "Press any key to close this window."
  exit 1
fi
echo "Serving the app at $URL  (press Ctrl+C or close this window to stop)"
( sleep 1; open -a Firefox "$URL" 2>/dev/null || open "$URL" ) &
exec "$PY" -m http.server "$PORT" --bind 127.0.0.1
