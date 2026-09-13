#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

echo "======================================"
echo " Updating LinearAlgebraCourse"
echo "======================================"

for cmd in git lake; do
    if ! command -v "$cmd" >/dev/null 2>&1; then
        echo "ERROR: '$cmd' was not found."
        echo "Please make sure Git and Lean are installed."
        exit 1
    fi
done

if [ -n "$(git status --porcelain)" ]; then
    echo
    echo "ERROR: You have uncommitted changes."
    git status --short
    echo
    echo "Please commit or stash your work before updating."
    echo "For example:"
    echo
    echo '    git add .'
    echo '    git commit -m "Save my work"'
    echo
    echo "Then run this script again."
    exit 1
fi

echo
echo "[1/4] Updating course files..."
git pull --ff-only

echo
echo "[2/4] Updating Lean/mathlib dependencies..."
lake update

echo
echo "[3/4] Downloading precompiled mathlib cache..."
lake exe cache get

echo
echo "[4/4] Checking that the project builds..."
lake build

echo
echo "======================================"
echo " Update completed successfully!"
echo "======================================"
