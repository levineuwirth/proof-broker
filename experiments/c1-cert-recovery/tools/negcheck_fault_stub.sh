#!/usr/bin/env bash
# Fault-injection stub for tools/run_negchecks.sh: always fails, writes no
# result. `NEGCHECK_BIN=tools/negcheck_fault_stub.sh tools/run_negchecks.sh`
# must exit nonzero — otherwise the gate is decorative.
exit 42
