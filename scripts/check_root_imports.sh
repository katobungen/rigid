#!/usr/bin/env bash

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

fixture_dir="$(mktemp -d "${TMPDIR:-/tmp}/rigid-root-imports.XXXXXX")"
trap 'rm -rf "$fixture_dir"' EXIT

# Challenge and Development declare the same names and therefore cannot be imported together.
# Development belongs to the root module; the comparator check builds Challenge separately.
find Rigid -type f -name '*.lean' ! -path 'Rigid/Challenge.lean' -print \
  | sort \
  | sed -e 's#/#.#g' -e 's#\.lean$##' \
  >"$fixture_dir/expected"

sed -nE 's/^(public |private )?import (Rigid\.[^[:space:]]+).*$/\2/p' Rigid.lean \
  | sort -u \
  >"$fixture_dir/actual"

if ! diff -u "$fixture_dir/expected" "$fixture_dir/actual"; then
  echo >&2
  echo "Rigid.lean must directly import every project module except Rigid.Challenge." >&2
  echo "Rigid.Challenge cannot coexist with Rigid.Development and is built by the comparator check." >&2
  exit 1
fi

echo "Rigid.lean imports every compatible project module; Rigid.Challenge is checked separately."
