#!/usr/bin/env bash
set -euo pipefail
submission_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$submission_dir/proofs"
lake build Lax455465Proofs.RamOptimalDecode Lax455465Proofs.RamMinPlus Lax455465Proofs.RamFloydWarshall Lax455465Proofs.RamDualDistances Lax455465Proofs.RamTruncatedSubtract Lax455465Proofs.RamUnsignedSum Lax455465Proofs.RamEdgePortion Lax455465Proofs.RamRootDistances Lax455465Proofs.RamMetricCost Lax455465Proofs.RamBallMask Lax455465Proofs.RamMaskedSum Lax455465Proofs.RamFind Lax455465Proofs.RamProductVector
checks_build=$(mktemp -d "${TMPDIR:-/tmp}/lr-ram-checks.XXXXXX")
trap 'rm -rf -- "$checks_build"' EXIT
mkdir -p -- "$checks_build/Checks"
export LEAN_PATH="$checks_build${LEAN_PATH:+:$LEAN_PATH}"
lake env lean --root="$submission_dir/checks" -o "$checks_build/Checks/Common.olean" "$submission_dir/checks/Checks/Common.lean"
for suite in CertificateDecode MinPlus FloydWarshall DualDistances RegionArithmetic EdgePortion RootDistances MetricCost BallMass Find ProductVector; do
  lake env lean "$submission_dir/checks/$suite.lean"
  printf 'PASS %s\n' "$suite"
done
