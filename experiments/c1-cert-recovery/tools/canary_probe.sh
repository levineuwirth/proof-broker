#!/usr/bin/env bash
# Canary for tools/test_runner_preflight.sh: records that it was invoked, so
# the test can assert a failed preflight let NOTHING run. Never elaborates
# anything.
printf '%s %s\n' "$(date -Is)" "$*" >> "${CANARY_FILE:?CANARY_FILE unset}"
exit 0
