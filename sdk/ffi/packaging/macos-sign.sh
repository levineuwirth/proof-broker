#!/usr/bin/env bash
#
# macOS code-signing for proof_broker_ffi.so (Phase 6 distribution).
#
# Two signing modes, auto-selected by which credentials are present in
# the environment. No mode requires editing this script.
#
#   Ad-hoc  (default; no secrets required):
#     `codesign --sign -` — a structurally valid but identity-less
#     signature. Enough to satisfy library-validation / hardened-
#     runtime loaders and to make the signing step real + verifiable
#     in CI on every run, including untrusted PRs and forks. Does NOT
#     satisfy Gatekeeper for a *downloaded* (quarantined) artifact.
#
#   Developer ID  (when MACOS_CERT_P12_BASE64 + MACOS_CERT_PASSWORD +
#                  MACOS_SIGN_IDENTITY are all set):
#     Imports the .p12 into an ephemeral keychain and signs with the
#     "Developer ID Application" identity, with the secure timestamp
#     and hardened runtime that notarization requires. This is the
#     signature Gatekeeper trusts once the artifact is also notarized.
#
# Notarization is deliberately NOT applied to the loose .so here:
# `xcrun stapler staple` cannot attach a ticket to a bare dylib — only
# to an app bundle, .dmg, or .pkg. Notarization belongs to the
# distribution *archive* the future prebuilt-bundle slice produces.
# `--notarize-archive` below is the credential-gated entry point that
# slice will call. For a loose dylib Gatekeeper checks the ticket
# online, so a notarized-archive ticket transitively covers the
# contained .so.
#
# Usage:
#   macos-sign.sh <path-to-.so>                 # sign + strict verify
#   macos-sign.sh --notarize-archive <archive>  # notarize .zip/.dmg/.pkg
#
# Safe to invoke unconditionally from a cross-platform matrix: on a
# non-Darwin host it exits 0 as a no-op.

set -euo pipefail

if [ "$(uname -s)" != "Darwin" ]; then
  echo "macos-sign: host is not Darwin — no-op"
  exit 0
fi

CLEANUP_KEYCHAIN=""
cleanup() {
  if [ -n "$CLEANUP_KEYCHAIN" ]; then
    security delete-keychain "$CLEANUP_KEYCHAIN" 2>/dev/null || true
  fi
}
trap cleanup EXIT

# Import the Developer ID .p12 into a throwaway keychain so codesign
# can find the identity, and prepend it to the user keychain search
# list. The keychain is deleted on exit by the trap above.
setup_keychain() {
  local kc_dir kc kc_pw p12
  kc_dir="$(mktemp -d)"
  kc="$kc_dir/sign.keychain-db"
  kc_pw="$(openssl rand -base64 24)"
  security create-keychain -p "$kc_pw" "$kc"
  security set-keychain-settings -lut 3600 "$kc"
  security unlock-keychain -p "$kc_pw" "$kc"
  p12="$kc_dir/cert.p12"
  echo "$MACOS_CERT_P12_BASE64" | base64 --decode > "$p12"
  security import "$p12" -k "$kc" -P "$MACOS_CERT_PASSWORD" \
    -T /usr/bin/codesign
  rm -f "$p12"
  # Allow codesign to use the imported key without an interactive
  # prompt (required for headless CI).
  security set-key-partition-list -S apple-tool:,apple: -s \
    -k "$kc_pw" "$kc" >/dev/null
  # Word-splitting of the existing search list is intentional here.
  # shellcheck disable=SC2046
  security list-keychains -d user -s "$kc" \
    $(security list-keychains -d user | sed 's/"//g')
  CLEANUP_KEYCHAIN="$kc"
}

sign() {
  local target="$1"
  if [ -n "${MACOS_SIGN_IDENTITY:-}" ] \
     && [ -n "${MACOS_CERT_P12_BASE64:-}" ] \
     && [ -n "${MACOS_CERT_PASSWORD:-}" ]; then
    echo "macos-sign: Developer ID mode (identity: $MACOS_SIGN_IDENTITY)"
    setup_keychain
    codesign --force --timestamp --options runtime \
      --sign "$MACOS_SIGN_IDENTITY" "$target"
  else
    echo "macos-sign: ad-hoc mode (no Developer ID credentials in env)"
    codesign --force --sign - "$target"
  fi
  # --strict makes codesign reject a signature it would otherwise
  # accept with warnings; a broken/absent signature fails the build.
  codesign --verify --strict --verbose=2 "$target"
  echo "macos-sign: signature verified for $target"
}

# Notarize a distribution archive (.zip/.dmg/.pkg). Credential-gated:
# skips cleanly (exit 0) when the App Store Connect API key secrets
# are absent so forks/PRs without secrets don't fail. Invoked by the
# future prebuilt-bundle publish slice, not by the per-platform build.
notarize_archive() {
  local archive="$1" key
  if [ -z "${MACOS_NOTARY_KEY_BASE64:-}" ] \
     || [ -z "${MACOS_NOTARY_KEY_ID:-}" ] \
     || [ -z "${MACOS_NOTARY_ISSUER_ID:-}" ]; then
    echo "macos-sign: notarization skipped — App Store Connect API" \
         "key secrets (MACOS_NOTARY_KEY_BASE64 / _KEY_ID /" \
         "_ISSUER_ID) not present in env" >&2
    return 0
  fi
  key="$(mktemp).p8"
  echo "$MACOS_NOTARY_KEY_BASE64" | base64 --decode > "$key"
  xcrun notarytool submit "$archive" \
    --key "$key" \
    --key-id "$MACOS_NOTARY_KEY_ID" \
    --issuer "$MACOS_NOTARY_ISSUER_ID" \
    --wait
  rm -f "$key"
  case "$archive" in
    *.dmg|*.pkg)
      xcrun stapler staple "$archive"
      echo "macos-sign: notarized + stapled $archive" ;;
    *)
      echo "macos-sign: notarized $archive (zip is not staple-able;" \
           "Gatekeeper resolves the ticket online for its contents)" ;;
  esac
}

case "${1:-}" in
  --notarize-archive)
    shift
    [ $# -eq 1 ] || { echo "usage: macos-sign.sh --notarize-archive <archive>" >&2; exit 2; }
    notarize_archive "$1" ;;
  "")
    echo "usage: macos-sign.sh <.so> | --notarize-archive <archive>" >&2
    exit 2 ;;
  *)
    [ -f "$1" ] || { echo "macos-sign: no such file: $1" >&2; exit 1; }
    sign "$1" ;;
esac
