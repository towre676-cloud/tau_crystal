#!/usr/bin/env bash
set +H
umask 022
TEX="docs/monographs/ramanujan_face_run1.tex"
PDF="docs/monographs/ramanujan_face_run1.pdf"
[ ! -f "$TEX" ] && { echo "missing $TEX" >&2; exit 2; }
if command -v latexmk >/dev/null 2>&1; then latexmk -pdf -interaction=nonstopmode -halt-on-error "$TEX" && echo "built $PDF";
elif command -v xelatex >/dev/null 2>&1; then xelatex -interaction=nonstopmode "$TEX" >/dev/null && echo "built $PDF";
else echo "TeX toolchain not found. Install TinyTeX or MikTeX to build locally."; fi
