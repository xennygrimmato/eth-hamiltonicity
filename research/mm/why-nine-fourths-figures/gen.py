#!/usr/bin/env python3
"""gen.py <prompt.txt> <out.png> [ref.png ...]  -- Gemini image generation."""
import sys, os, json, base64, urllib.request, time
MODEL = os.environ.get("GEMINI_MODEL", "gemini-3-pro-image")
KEY = os.environ["GEMINI_API_KEY"]
STYLE = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "prompts", "_style.txt")).read()
prompt_path, out = sys.argv[1], sys.argv[2]
refs = sys.argv[3:]
parts = []
for r in refs:
    parts.append({"inlineData": {"mimeType": "image/png", "data": base64.b64encode(open(r, "rb").read()).decode()}})
text = STYLE + "\n\n" + open(prompt_path).read()
if refs:
    text = ("The attached image is an earlier page of the same zine. Match its drawing style, lettering, "
            "line weight, colours and stick-figure character exactly, but draw the NEW page described below "
            "(do not copy its content).\n\n") + text
parts.append({"text": text})
body = {"contents": [{"parts": parts}],
        "generationConfig": {"responseModalities": ["TEXT", "IMAGE"],
                             "imageConfig": {"aspectRatio": os.environ.get("ASPECT", "4:5"), "imageSize": "2K"}}}
url = f"https://generativelanguage.googleapis.com/v1beta/models/{MODEL}:generateContent"
for attempt in range(4):
    try:
        req = urllib.request.Request(url, data=json.dumps(body).encode(),
                                     headers={"x-goog-api-key": KEY, "Content-Type": "application/json"})
        d = json.load(urllib.request.urlopen(req, timeout=300))
        for p in d["candidates"][0]["content"]["parts"]:
            if "inlineData" in p:
                open(out, "wb").write(base64.b64decode(p["inlineData"]["data"]))
                print("wrote", out, p["inlineData"]["mimeType"]); sys.exit(0)
        print("no image:", json.dumps(d)[:600])
    except Exception as e:
        msg = e.read().decode()[:600] if hasattr(e, "read") else repr(e)
        print("attempt", attempt, "failed:", msg)
    time.sleep(5 * (attempt + 1))
sys.exit(1)
