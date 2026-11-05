#!/usr/bin/env bash
# Build the PDF and the GitHub Markdown version of each write-up in docs/.
# Requires tectonic and pandoc (brew install tectonic pandoc).
# Usage: ./build.sh [name ...]   (default: every *.tex in docs/)
set -euo pipefail
cd "$(dirname "$0")"

names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for f in *.tex; do names+=("${f%.tex}"); done
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

for name in "${names[@]}"; do
  echo "== $name"
  tectonic --chatter minimal "$name.tex"
  # Pandoc merges thebibliography entries into one paragraph; give it a list instead.
  python3 - "$name.tex" "$tmp/$name.tex" <<'EOF'
import re, sys
src = open(sys.argv[1]).read()
def bib(m):
    items = re.split(r'\\bibitem\{[^}]*\}', m.group(1))[1:]
    body = "\n".join(r"\item " + it.strip() for it in items)
    return "\\section*{References}\n\\begin{itemize}\n" + body + "\n\\end{itemize}"
# Lean names use \\detokenize, which pandoc drops; give it verbatim text instead.
src = re.sub(r'\\newcommand\{\\lean(ref)?\}.*\n', '', src)
src = re.sub(r'\\leanref\{([^}]*)\}', lambda m: "\n\n\\emph{Lean:} \\verb|" + m.group(1) + "|\n\n", src)
src = re.sub(r'\\lean\{([^}]*)\}', lambda m: "\\verb|" + m.group(1) + "|", src)
src = re.sub(r'\\begin\{thebibliography\}\{[^}]*\}(.*?)\\end\{thebibliography\}', bib, src, flags=re.S)
open(sys.argv[2], "w").write(src)
EOF
  pandoc "$tmp/$name.tex" -f latex -t gfm --wrap=none --lua-filter=tools/gfm.lua -o "$name.md"
done

# With no arguments, also collect the chapter PDFs into one (combined/all-notes.tex -> all-notes.pdf).
if [ $# -eq 0 ]; then
  echo "== all-notes"
  (cd combined && tectonic --chatter minimal --outdir .. all-notes.tex)
fi
