from flask import Flask
from threading import Thread
import os

app = Flask(__name__)

# Bot logic copied inline — replace this with import if bot.py is long
def bot_logic():
    token = os.getenv("TOKEN")
    username = os.getenv("USERNAME")
    room = os.getenv("ROOM")

    if not all([token, username, room]):
        print("❌ Missing environment variables!")
        return

    print("✅ All environment variables found")
    print(f"🟢 Logging in as {username} to room: {room}")

    # Example WebSocket connection logic
    import websocket
    import time

    def on_open(ws):
        print("🟢 Connected to WebSocket")
        ws.send(f"{username} joined the room: {room}")

    def on_message(ws, message):
        print(f"📩 Message from server: {message}")

    def on_error(ws, error):
        print(f"❌ WebSocket error: {error}")

    def on_close(ws, close_status_code, close_msg):
        print("🔴 WebSocket closed")

    ws = websocket.WebSocketApp(
        "wss://echo.websocket.events/",  # <-- replace with your actual WebSocket URL
        on_open=on_open,
        on_message=on_message,
        on_error=on_error,
        on_close=on_close
    )

    ws.run_forever()


@app.route("/")
def home():
    return "✅ CLI bot is idle. Use `/run` to launch."


@app.route("/run")
def run_bot():
    thread = Thread(target=bot_logic)
    thread.start()
    return "🚀 CLI bot started in background!"


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=10000)