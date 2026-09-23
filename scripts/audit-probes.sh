#!/usr/bin/env bash
# Negative controls for the audit suite.
#
# An audit that inspects nothing passes every commit. Each probe below plants a defect that a
# named audit must reject, and asserts both that the audit fails AND that its output names the
# planted thing -- an audit failing for an unrelated reason looks identical to a working one.
#
# Probes run against a scratch copy of the committed tree, never the working tree. Source-level
# probes are cheap; probes marked BUILD re-elaborate and are skipped under --fast.
#
# Usage:
#   scripts/audit-probes.sh            # all probes
#   scripts/audit-probes.sh --fast     # source-level probes only
#
# When you change an audit, add a probe here. An audit with no probe is not trusted.

set -euo pipefail

FAST=0
[[ "${1:-}" == "--fast" ]] && FAST=1

REPO_ROOT="$(git rev-parse --show-toplevel)"
PROJECT="$(sed -n 's/^name = "\(.*\)"/\1/p' "$REPO_ROOT/lakefile.toml" | head -1)"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

PASSED=0
FAILED=0

# Lay out the committed tree with its build artifacts, so a BUILD probe re-elaborates only what
# the planted defect actually invalidates.
#
# `.lake/packages` is several GB of Mathlib and is read-only here, so it is symlinked rather than
# copied -- copying it per probe dominated the runtime. `.lake/build` is project-only and small,
# and must be a real copy because probes dirty it.
setup_scratch() {
  rm -rf "$SCRATCH/tree"
  mkdir -p "$SCRATCH/tree/.lake"
  git -C "$REPO_ROOT" archive HEAD | tar -x -C "$SCRATCH/tree"
  if [[ -d "$REPO_ROOT/.lake/packages" ]]; then
    ln -s "$REPO_ROOT/.lake/packages" "$SCRATCH/tree/.lake/packages"
  fi
  for f in "$REPO_ROOT"/.lake/*; do
    [[ -e "$f" ]] || continue
    case "$(basename "$f")" in
      packages) ;;
      build) cp -R "$f" "$SCRATCH/tree/.lake/build" ;;
      *) cp -R "$f" "$SCRATCH/tree/.lake/" ;;
    esac
  done
}

# probe <name> <expected-substring-in-output> <command...>
#
# Asserts the command FAILS and that its combined output contains the expected substring.
probe() {
  local name="$1" expect="$2"
  shift 2
  local out status
  set +e
  out="$(cd "$SCRATCH/tree" && "$@" 2>&1)"
  status=$?
  set -e

  if [[ $status -eq 0 ]]; then
    echo "FAIL  $name: audit passed, but the probe planted a defect it must reject"
    FAILED=$((FAILED + 1))
    return
  fi
  if ! grep -qF -- "$expect" <<<"$out"; then
    echo "FAIL  $name: audit failed, but its output never mentions '$expect'."
    echo "      An audit that fails for an unrelated reason is indistinguishable from a working one."
    echo "      --- output ---"
    sed 's/^/      /' <<<"$out" | head -20
    FAILED=$((FAILED + 1))
    return
  fi
  echo "ok    $name"
  PASSED=$((PASSED + 1))
}

echo "audit-probes: project '$PROJECT', $( [[ $FAST == 1 ]] && echo 'source-level probes only' || echo 'all probes' )"
echo

# --- source-level probes -------------------------------------------------------------------

# The frozen Palomar statement must not drift. This is the cheapest and most important probe:
# a statement edited to match a proof that would not close is the defect this whole workspace
# is built to prevent.
setup_scratch
printf '\n-- planted drift\n' >> "$SCRATCH/tree/Challenge.lean"
probe "challenge-drift" "Challenge" ./scripts/check-palomar-challenge.sh .

# Mathlib's text-based linter does not run during elaboration, so line length is its own audit.
setup_scratch
STATEMENT_FILE="$(cd "$SCRATCH/tree" && find "$PROJECT/Standalone/Mathlib" -name '*.lean' ! -name '*Proof.lean' | head -1)"
if [[ -n "$STATEMENT_FILE" ]]; then
  printf -- '-- %s\n' "$(printf 'x%.0s' {1..120})" >> "$SCRATCH/tree/$STATEMENT_FILE"
  probe "style-line-length" "$STATEMENT_FILE" lake exe style
fi

if [[ $FAST == 1 ]]; then
  echo
  echo "audit-probes: $PASSED passed, $FAILED failed (source-level only)"
  [[ $FAILED -eq 0 ]] || exit 1
  exit 0
fi

# --- BUILD probes --------------------------------------------------------------------------

# `warningAsError = true` is what makes `sorry` a build failure rather than a warning. If this
# probe ever passes, that setting has been lost and every "green" tree since is suspect.
setup_scratch
mkdir -p "$SCRATCH/tree/$PROJECT/Standalone/Mathlib/Support"
cat > "$SCRATCH/tree/$PROJECT/Standalone/Mathlib/Support/Probe.lean" <<LEAN
module
public section
theorem probe_planted_sorry : True := by sorry
end
LEAN
probe "build-rejects-sorry" "Support/Probe.lean" lake build

# An axiom outside the permitted three must be rejected even though the tree compiles.
setup_scratch
mkdir -p "$SCRATCH/tree/$PROJECT/Standalone/Mathlib/Support"
cat > "$SCRATCH/tree/$PROJECT/Standalone/Mathlib/Support/Probe.lean" <<LEAN
module
public section
axiom probe_planted_axiom : True
theorem probe_uses_axiom : True := probe_planted_axiom
end
LEAN
probe "axioms-rejects-extra" "probe_planted_axiom" bash -c 'lake build 2>/dev/null; lake exe axioms'

# A claim with no satisfiability witness is the vacuity defect that axiom-cleanliness cannot see.
setup_scratch
mkdir -p "$SCRATCH/tree/$PROJECT/Standalone/Mathlib"
cat > "$SCRATCH/tree/$PROJECT/Standalone/Mathlib/Probe.lean" <<LEAN
module
public section
namespace $PROJECT.Standalone.Mathlib
def ProbeClaimWithoutWitness : Prop := ∀ n : Nat, n = n
end $PROJECT.Standalone.Mathlib
end
LEAN
probe "fidelity-requires-witness" "ProbeClaimWithoutWitness" \
  bash -c 'lake build 2>/dev/null; lake exe fidelity'

# `theorem C.witness : True` is the obvious way to satisfy the fidelity audit without doing the
# work. It must be rejected.
setup_scratch
mkdir -p "$SCRATCH/tree/$PROJECT/Standalone/Mathlib"
cat > "$SCRATCH/tree/$PROJECT/Standalone/Mathlib/Probe.lean" <<LEAN
module
public section
namespace $PROJECT.Standalone.Mathlib
def ProbeClaimTrivialWitness : Prop := ∀ n : Nat, n = n
def ProbeClaimTrivialWitness.witness : Prop := True
end $PROJECT.Standalone.Mathlib
end
LEAN
probe "fidelity-rejects-trivial-witness" "ProbeClaimTrivialWitness.witness" \
  bash -c 'lake build 2>/dev/null; lake exe fidelity'

# A drop companion whose body is not the negation of the claim with that hypothesis removed
# must be rejected by name. The hypothesis is anonymous, so the companion is `drop0`.
setup_scratch
mkdir -p "$SCRATCH/tree/$PROJECT/Standalone/Mathlib"
cat > "$SCRATCH/tree/$PROJECT/Standalone/Mathlib/Probe.lean" <<LEAN
module
public section
namespace $PROJECT.Standalone.Mathlib
def ProbeDropWrong : Prop := ∀ (_ : (0 : Nat) = 0), (1 : Nat) = 1
def ProbeDropWrong.witness : Prop := ProbeDropWrong ∨ True
def ProbeDropWrong.drop0 : Prop := True
end $PROJECT.Standalone.Mathlib
end
LEAN
probe "fidelity-rejects-wrong-drop" "ProbeDropWrong.drop0" \
  bash -c 'lake build 2>/dev/null; lake exe fidelity'

# A non-dependent hypothesis with no drop companion must be rejected by the hypothesis's tag.
setup_scratch
mkdir -p "$SCRATCH/tree/$PROJECT/Standalone/Mathlib"
cat > "$SCRATCH/tree/$PROJECT/Standalone/Mathlib/Probe.lean" <<LEAN
module
public section
namespace $PROJECT.Standalone.Mathlib
def ProbeDropMissing : Prop := ∀ (_ : (0 : Nat) = 0), (1 : Nat) = 1
def ProbeDropMissing.witness : Prop := ProbeDropMissing ∨ True
end $PROJECT.Standalone.Mathlib
end
LEAN
probe "fidelity-requires-drop" "hypothesis 0" \
  bash -c 'lake build 2>/dev/null; lake exe fidelity'

# A statement module that imports the development is no longer independently readable, and
# Palomar's isolation requirement is broken.
setup_scratch
mkdir -p "$SCRATCH/tree/$PROJECT/Standalone/Mathlib"
cat > "$SCRATCH/tree/$PROJECT/Standalone/Mathlib/Probe.lean" <<LEAN
module
public import $PROJECT.Standalone.Mathlib.Inline$PROJECT
public section
namespace $PROJECT.Standalone.Mathlib
def ProbeBadImport : Prop := True
end $PROJECT.Standalone.Mathlib
end
LEAN
probe "standalone-rejects-project-import" "Probe" \
  bash -c 'lake build 2>/dev/null; lake exe standalone-mathlib'

echo
echo "audit-probes: $PASSED passed, $FAILED failed"
[[ $FAILED -eq 0 ]] || exit 1
