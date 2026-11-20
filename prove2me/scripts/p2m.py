"""Minimal Prove2Me API client (https://prove2.me/skill.md, metadata.version 0.13.10).

The API key is read from the environment variable PROVE2ME_API_KEY and is only ever sent to
https://prove2.me/api/v1/agent/refresh. Access tokens live in memory and are refreshed before
they expire. Nothing secret is written to disk or printed.
"""
import json
import mimetypes
import os
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid

BASE = "https://prove2.me/api/v1"
SKILL_VERSION = "0.13.10"
UA = "prove2me-uploader/0.1"


class ApiError(Exception):
    def __init__(self, status, body, method, path):
        super().__init__(f"{method} {path} -> {status}: {body[:800]}")
        self.status, self.body = status, body


class Client:
    def __init__(self):
        key = os.environ.get("PROVE2ME_API_KEY", "")
        if not key.startswith("p2m_"):
            raise SystemExit("PROVE2ME_API_KEY is not set (or does not look like a Prove2Me key)")
        self._key = key
        self._token = None
        self._exp = 0
        self.version = None

    def _refresh(self):
        data = self._raw("POST", "/agent/refresh", {"api_key": self._key}, auth=False)
        self._token = data["access_token"]
        self._exp = int(data.get("expires_at", time.time() + 3000))
        self.version = data.get("version")

    def _auth(self):
        if self._token is None or time.time() > self._exp - 300:
            self._refresh()
        return {"Authorization": f"Bearer {self._token}"}

    def _raw(self, method, path, body=None, auth=True, query=None, multipart=None, retries=4):
        url = BASE + path
        if query:
            url += "?" + urllib.parse.urlencode(query, doseq=True)
        headers = {"User-Agent": UA, "Accept": "application/json"}
        data = None
        if multipart is not None:
            boundary = uuid.uuid4().hex
            chunks = []
            for name, value in multipart.items():
                if isinstance(value, tuple):  # (filename, bytes)
                    fname, content = value
                    ctype = mimetypes.guess_type(fname)[0] or "application/octet-stream"
                    chunks.append(
                        f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"; '
                        f'filename="{fname}"\r\nContent-Type: {ctype}\r\n\r\n'.encode() + content + b"\r\n")
                else:
                    chunks.append(
                        f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n'
                        .encode() + str(value).encode() + b"\r\n")
            chunks.append(f"--{boundary}--\r\n".encode())
            data = b"".join(chunks)
            headers["Content-Type"] = f"multipart/form-data; boundary={boundary}"
        elif body is not None:
            data = json.dumps(body).encode()
            headers["Content-Type"] = "application/json"
        for attempt in range(retries):
            h = dict(headers)
            if auth:
                h.update(self._auth())
            req = urllib.request.Request(url, data=data, headers=h, method=method)
            try:
                with urllib.request.urlopen(req, timeout=120) as r:
                    txt = r.read().decode()
                    return json.loads(txt) if txt.strip() else {}
            except urllib.error.HTTPError as e:
                txt = e.read().decode(errors="replace")
                if e.code == 401 and auth and attempt == 0:
                    self._token = None
                    continue
                if e.code in (429, 502, 503, 504) and attempt + 1 < retries:
                    time.sleep(10 * (attempt + 1))
                    continue
                raise ApiError(e.code, txt, method, path)
            except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
                if attempt + 1 < retries:
                    time.sleep(10 * (attempt + 1))
                    continue
                raise ApiError(-1, str(e), method, path)

    def get(self, path, **query):
        return self._raw("GET", path, query=query or None)

    def post(self, path, body):
        return self._raw("POST", path, body)

    def patch(self, path, body):
        return self._raw("PATCH", path, body)

    def verify(self, theorem_id, content, explanation=None):
        form = {"theorem_id": theorem_id, "file": ("solution.lean", content.encode())}
        if explanation:
            form["explanation"] = explanation
        return self._raw("POST", "/verify", multipart=form)
