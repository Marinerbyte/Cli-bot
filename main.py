from flask import Flask
import subprocess

app = Flask(__name__)

@app.route('/')
def home():
    return '✅ CLI bot web app is live on Render!'

@app.route('/run')
def run_bot():
    try:
        # Yeh teri CLI bot file ko background me start karega
        subprocess.Popen(["python3", "bot.py"])
        return '🚀 CLI bot started!'
    except Exception as e:
        return f'❌ Error: {str(e)}'

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=10000)
