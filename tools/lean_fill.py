"""Fill a `sorry` in a Lean declaration with a local LLM (ollama), checked by the Lean compiler.

    python tools/lean_fill.py FILE NAME [--model M] [--rounds N] [--write] [--hint TEXT]

The declaration `NAME` in FILE must have proof `by sorry` (on one or several lines). The model
sees the file up to the declaration and the declaration itself, proposes a tactic proof, and
gets back the compiler errors in the declaration's line range, for up to N rounds. Other
`sorry`s in the file are ignored. On success the proof is printed, and with --write spliced
into FILE. Nothing is written on failure.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def ask(model, messages, think):
    body = json.dumps({"model": model, "messages": messages, "stream": False, "think": think,
                       "options": {"num_ctx": 32768, "temperature": 0.3}}).encode()
    req = urllib.request.Request("http://localhost:11434/api/chat", body,
                                 {"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=3600) as r:
        return json.loads(r.read())["message"]["content"]


def find_decl(text, name):
    m = re.search(rf"^(theorem|lemma) {re.escape(name)}\b", text, re.M)
    if not m:
        sys.exit(f"declaration {name} not found")
    start = m.start()
    # include a preceding docstring
    doc = text.rfind("/--", 0, start)
    if doc != -1 and text[doc:start].count("-/") == 1 and text[text.index("-/", doc) + 2:start].strip() == "":
        start = doc
    s = re.search(r":= by\s*\n?\s*sorry\b", text[m.start():])
    if not s:
        sys.exit(f"{name} does not have a `by sorry` proof")
    return start, m.start() + s.start(), m.start() + s.end()


def extract_proof(reply):
    reply = re.sub(r"<think>.*?</think>", "", reply, flags=re.S)
    blocks = re.findall(r"```(?:lean4?|)\n(.*?)```", reply, re.S)
    code = blocks[-1] if blocks else reply
    code = code.strip("\n")
    # accept either a bare tactic block or a full declaration
    m = re.search(r":= by\s*\n", code)
    if m and re.match(r"\s*(theorem|lemma)\b", code):
        code = code[m.end():]
    lines = code.split("\n")
    ind = min((len(l) - len(l.lstrip()) for l in lines if l.strip()), default=0)
    return "\n".join("  " + l[ind:] for l in lines)


def compile_lean(text, path):
    fd, tmp = tempfile.mkstemp(suffix=".lean", dir=os.path.dirname(path))
    with os.fdopen(fd, "w") as f:
        f.write(text)
    try:
        out = subprocess.run(["lake", "env", "lean", tmp], cwd=ROOT, capture_output=True, text=True,
                             timeout=1800).stdout
    finally:
        os.unlink(tmp)
    return out.replace(tmp, "FILE")


def errors_in(out, lo, hi):
    errs, cur = [], None
    for line in out.split("\n"):
        m = re.match(r"FILE:(\d+):(\d+): (error|warning)", line)
        if m:
            cur = None
            if m.group(3) == "error" and lo <= int(m.group(1)) <= hi:
                cur = [line]
                errs.append(cur)
        elif cur is not None:
            cur.append(line)
    return ["\n".join(e)[:2500] for e in errs]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file"); ap.add_argument("name")
    ap.add_argument("--model", default="qwen3.6-coder-64k")
    ap.add_argument("--rounds", type=int, default=6)
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--think", action="store_true")
    ap.add_argument("--hint", default="")
    ap.add_argument("--context-lines", type=int, default=400)
    a = ap.parse_args()
    path = os.path.abspath(a.file)
    text = open(path).read()
    dstart, sorry_start, sorry_end = find_decl(text, a.name)
    head = text[:dstart].split("\n")
    context = "\n".join(head[:40] + ["-- ..."] + head[-a.context_lines:]) if len(head) > a.context_lines + 40 \
        else "\n".join(head)
    decl = text[dstart:sorry_start] + ":= by"
    system = ("You are an expert in Lean 4 and Mathlib. You write tactic proofs that compile. "
              "Reply with a single ```lean code block containing only the tactic proof (the lines "
              "after `:= by`), no explanation. Use only lemmas that exist in Mathlib or in the "
              "given file.")
    user = (f"File context (Lean 4, Mathlib):\n```lean\n{context}\n```\n\nProve:\n```lean\n{decl}\n"
            f"  sorry\n```\n" + (f"\nHint: {a.hint}\n" if a.hint else ""))
    msgs = [{"role": "system", "content": system}, {"role": "user", "content": user}]
    lo = text[:dstart].count("\n") + 1
    for rnd in range(1, a.rounds + 1):
        t0 = time.time()
        reply = ask(a.model, msgs, a.think)
        proof = extract_proof(reply)
        new = text[:sorry_start] + ":= by\n" + proof + text[sorry_end:]
        hi = lo + new[dstart:].count("\n", 0, len(text[dstart:sorry_start]) + len(proof) + 10) + 1
        errs = errors_in(compile_lean(new, path), lo, hi)
        print(f"[round {rnd}] {len(errs)} error(s) ({time.time() - t0:.0f}s)", file=sys.stderr, flush=True)
        if not errs:
            print(proof)
            if a.write:  # splice into the current file, which may have changed meanwhile
                cur = open(path).read()
                _, cs, ce = find_decl(cur, a.name)
                open(path, "w").write(cur[:cs] + ":= by\n" + proof + cur[ce:])
                print(f"wrote {a.name} into {a.file}", file=sys.stderr)
            return 0
        msgs += [{"role": "assistant", "content": f"```lean\n{proof}\n```"},
                 {"role": "user", "content": "Lean reports:\n" + "\n\n".join(errs[:4]) +
                  "\n\nFix the proof. Reply with the full corrected tactic proof only."}]
    print(f"FAILED after {a.rounds} rounds; last attempt:\n{proof}\n\nlast errors:\n" + "\n\n".join(errs[:2]))
    return 1


if __name__ == "__main__":
    sys.exit(main())
