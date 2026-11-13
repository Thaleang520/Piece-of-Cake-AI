# Piece-of-Cake-AI

A local Flask web app for turning Chinese-language videos into Khmer-dubbed videos. It uses faster-whisper for speech recognition, online translation and text-to-speech services, and FFmpeg for video/audio processing.

## Run locally

You need Python 3.10 or newer and an internet connection. From the repository directory, run:

```bash
python -m venv .venv
```

Activate the virtual environment:

- **Windows (Command Prompt):** `.venv\\Scripts\\activate`
- **macOS/Linux:** `source .venv/bin/activate`

Then install the dependencies and start the app:

```bash
python -m pip install --upgrade pip
python -m pip install Flask faster-whisper edge-tts deep-translator imageio-ffmpeg numpy
python app.py
```

Open <http://127.0.0.1:5000> in your browser. Keep the terminal and app running while you use it. On first use, faster-whisper downloads its speech model; that can take time and requires disk space. Processing speed depends on your computer and the video length. The app can also install missing dependencies through its **Install now** prompt, but installing them before launch is generally more reliable.

Upload a video with clear Chinese speech. Translation and Khmer voice generation need an internet connection. The app uses `imageio-ffmpeg` to obtain FFmpeg if a system FFmpeg executable is not available.

## Hosting note

This is a **Python/Flask backend**, not a static website. GitHub Pages cannot run `app.py`, accept/process uploaded videos, or provide the `/api/...` endpoints the interface needs. A Pages build can succeed while the application still does not work. Run it locally as above, or deploy the Flask app to a Python-capable host that supports long-running processes, file uploads, sufficient storage, and the required CPU/memory. Do not point the Pages URL at this app and expect the backend to run there.

## Troubleshooting

- **The page loads but buttons do nothing / API errors:** Make sure you opened `http://127.0.0.1:5000` from the running Flask app, not the GitHub Pages URL. Check the terminal for server errors.
- **Missing package or FFmpeg warning:** Use **Install now**, or rerun the `pip install` command above in the same Python environment used to launch the app, then restart it.
- **Speech model download or processing seems stuck:** The first model download can be large. Keep the terminal open, confirm internet access, and allow time for processing.
- **Translation or voice generation fails:** Confirm internet access and retry; those features use external services.
