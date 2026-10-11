#!/usr/bin/env bash
set -euo pipefail
submission_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$submission_dir/proofs"
lake build Lax455465Proofs.RamOptimalDecode
checks_build=$(mktemp -d "${TMPDIR:-/tmp}/lr-ram-checks.XXXXXX")
trap 'rm -rf -- "$checks_build"' EXIT
mkdir -p -- "$checks_build/Checks"
export LEAN_PATH="$checks_build${LEAN_PATH:+:$LEAN_PATH}"
lake env lean --root="$submission_dir/checks" -o "$checks_build/Checks/Common.olean" "$submission_dir/checks/Checks/Common.lean"
lake env lean "$submission_dir/checks/CertificateDecode.lean"
printf 'PASS CertificateDecode\n'
