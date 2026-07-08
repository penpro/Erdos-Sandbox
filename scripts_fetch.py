"""Fetch an erdosproblems.com problem page and extract visible text to a file.
Usage: python scripts_fetch.py 129 460 467 ...
Writes scratch_problem_<n>.txt (UTF-8).
"""
import re, html, sys, subprocess

def fetch(n):
    url = f"https://www.erdosproblems.com/{n}"
    raw = subprocess.run(["curl","-s","-A","Mozilla/5.0",url],
                         capture_output=True).stdout.decode("utf-8","replace")
    t = re.sub(r"<script.*?</script>", "", raw, flags=re.S)
    t = re.sub(r"<style.*?</style>", "", t, flags=re.S)
    t = re.sub(r"<[^>]+>", " ", t)
    t = html.unescape(t)
    t = re.sub(r"[ \t]+", " ", t)
    t = re.sub(r"\n\s*\n+", "\n", t)
    out = f"scratch_problem_{n}.txt"
    open(out, "w", encoding="utf-8").write(t.strip())
    print(f"wrote {out} ({len(t)} chars)")

if __name__ == "__main__":
    for n in sys.argv[1:]:
        fetch(n)
