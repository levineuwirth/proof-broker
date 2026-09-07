#!/usr/bin/env bash
# Fault-injection stub for the build preflight: always fails, builds nothing.
# `BUILD_DIAG=tools/build_fault_stub.sh <runner>` must exit nonzero AND must
# not reach a single probe or tracer invocation.
exit 42
