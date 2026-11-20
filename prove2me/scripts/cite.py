#!/usr/bin/env python3
"""Bring the `source` citation of every published item up to date.

  python3 cite.py            # dry run: show what would change
  python3 cite.py --apply    # PATCH /theorems/<id> {"source": ...} and update out/meta/batch_*.json

Only `source` is touched (the Lean statements are immutable, the natural-language statements are
left alone). Each rule below is applied once per item and is idempotent; a change can be reverted
by patching the old string back.
Needs PROVE2ME_API_KEY.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import p2m  # noqa: E402

OUT = os.path.join(os.path.dirname(HERE), "out")
RULES = [
    # 2026-11-15: cite the public ePrint version next to the submission number.
    ("(STOC 2027 submission #847)",
     "(STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634)"),
    # 2026-11-16: author order as on the paper and the ePrint page.
    ("G. Weissenberg, G. Fenzi, ", "G. Fenzi, G. Weissenberg, "),
]


def cited(src, name):
    for old, new in RULES:
        if new in src:
            continue
        if src.count(old) != 1:
            sys.exit(f"{name}: expected {old!r} exactly once in the source, got: {src!r}")
        src = src.replace(old, new)
    return src


def main():
    apply = "--apply" in sys.argv[1:]
    up = json.load(open(os.path.join(OUT, "upload_state.json")))
    items = [(k, n, rec["id"]) for k in ("definitions", "theorems") for n, rec in up[k].items()]
    c = p2m.Client()
    changed = same = 0
    for kind, name, tid in items:
        cur = c.get(f"/theorems/{tid}").get("source") or ""
        new = cited(cur, name)
        if new == cur:
            same += 1
            continue
        if apply:
            got = c.patch(f"/theorems/{tid}", {"source": new}).get("source")
            if got != new:
                sys.exit(f"{name}: server returned a different source: {got!r}")
        changed += 1
        print(("patched: " if apply else "would patch: ") + name)
    print(f"{len(items)} items: {changed} {'patched' if apply else 'to patch'}, {same} already up to date")
    if not apply:
        return
    # Keep the local metadata in step, editing the text in place so nothing else is reformatted.
    for f in sorted(os.listdir(os.path.join(OUT, "meta"))):
        if not (f.startswith("batch_") and f.endswith(".json")) or f.endswith("_items.json"):
            continue
        path = os.path.join(OUT, "meta", f)
        text = open(path).read()
        n = 0
        for o in json.loads(text):
            src = o["source"]
            new = cited(src, f)
            if new == src:
                continue
            for enc in (False, True):
                a = '"source": ' + json.dumps(src, ensure_ascii=enc)
                if text.count(a) == 1:
                    text = text.replace(a, '"source": ' + json.dumps(new, ensure_ascii=enc))
                    n += 1
                    break
            else:
                sys.exit(f"{f}: could not locate the source string of an entry")
        json.loads(text)
        open(path, "w").write(text)
        print(f"{f}: {n} sources updated")


if __name__ == "__main__":
    main()
