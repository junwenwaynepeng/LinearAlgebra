#!/bin/bash

set -euo pipefail

cd "$(dirname "$0")"

MYWORK_DIR="MyWork"

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

# Make sure MyWork exists.
mkdir -p "$MYWORK_DIR"

# Make sure the current branch has an upstream branch.
UPSTREAM=$(git rev-parse --abbrev-ref --symbolic-full-name '@{u}' 2>/dev/null || true)

if [ -z "$UPSTREAM" ]; then
    echo
    echo "ERROR: This branch does not have an upstream branch."
    exit 1
fi

# Remember the previous course version.
OLD_UPSTREAM=$(git rev-parse "$UPSTREAM")

echo
echo "[1/2] Checking for course updates..."

# Fetch first, but do not modify any student's files yet.
git fetch

NEW_UPSTREAM=$(git rev-parse "$UPSTREAM")

# ------------------------------------------------------------
# Find changes outside MyWork.
# This includes:
#   - unstaged changes
#   - staged changes
#   - untracked files
#   - locally committed changes
# ------------------------------------------------------------

CHANGES_FILE=$(mktemp)
BACKUP_DIR=$(mktemp -d)

cleanup() {
    rm -f "$CHANGES_FILE"
    rm -rf "$BACKUP_DIR"
}
trap cleanup EXIT

{
    git diff --name-only
    git diff --cached --name-only
    git ls-files --others --exclude-standard
    git log --format= --name-only "$UPSTREAM"..HEAD
} |
    sed '/^$/d' |
    sort -u |
    while IFS= read -r file; do
        case "$file" in
            "$MYWORK_DIR"|"$MYWORK_DIR"/*)
                # Student files are allowed.
                ;;
            *)
                echo "$file"
                ;;
        esac
    done > "$CHANGES_FILE"

# ------------------------------------------------------------
# Warn if students changed course files.
# ------------------------------------------------------------

if [ -s "$CHANGES_FILE" ]; then
    echo
    echo "WARNING: You have made changes to course files."
    echo
    echo "The following files are outside $MYWORK_DIR/:"
    echo

    sed 's/^/    /' "$CHANGES_FILE"

    echo
    echo "These changes will be removed when the course is updated."
    echo
    echo "If you want to keep any of them:"
    echo
    echo "  1. Cancel this update."
    echo "  2. Copy or move your work into $MYWORK_DIR/."
    echo "  3. Run this updater again."
    echo
    echo "If you do NOT need these changes, type FORCE to"
    echo "restore the course files to the instructor's version."
    echo
    read -r -p "Type FORCE to continue, or anything else to cancel: " answer

    if [ "$answer" != "FORCE" ]; then
        echo
        echo "Update cancelled."
        echo "Your files have not been changed."
        exit 0
    fi
fi

# ------------------------------------------------------------
# Preserve MyWork before resetting the repository.
# This also protects against the unusual case where a student
# accidentally committed files inside MyWork.
# ------------------------------------------------------------

if [ -d "$MYWORK_DIR" ]; then
    mkdir -p "$BACKUP_DIR/$MYWORK_DIR"
    cp -R "$MYWORK_DIR"/. "$BACKUP_DIR/$MYWORK_DIR"/ 2>/dev/null || true
fi

echo
echo "Updating course files..."

# Make the course repository exactly match the instructor's version.
git reset --hard "$UPSTREAM"

# Remove untracked course files.
# Ignored files such as MyWork are not removed.
git clean -fd

# Restore student's MyWork.
if [ -d "$BACKUP_DIR/$MYWORK_DIR" ]; then
    mkdir -p "$MYWORK_DIR"
    cp -R "$BACKUP_DIR/$MYWORK_DIR"/. "$MYWORK_DIR"/
fi

# ------------------------------------------------------------
# Download mathlib cache only if dependencies changed.
# ------------------------------------------------------------

DEPENDENCIES_CHANGED=false

if [ "$OLD_UPSTREAM" != "$NEW_UPSTREAM" ]; then
    if ! git diff --quiet "$OLD_UPSTREAM" "$NEW_UPSTREAM" -- \
        lean-toolchain \
        lake-manifest.json \
        lakefile.toml \
        lakefile.lean; then
        DEPENDENCIES_CHANGED=true
    fi
fi

if [ "$DEPENDENCIES_CHANGED" = true ]; then
    echo
    echo "[2/2] Lean/mathlib dependencies changed."
    echo "Downloading the matching precompiled cache..."
    lake exe cache get
else
    echo
    echo "[2/2] Lean/mathlib dependencies have not changed."
    echo "No dependency update is needed."
fi

echo
echo "======================================"
echo " Update completed successfully!"
echo "======================================"