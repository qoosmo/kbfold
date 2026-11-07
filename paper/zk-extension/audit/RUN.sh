#!/usr/bin/env sh
set -eu
rustc --edition=2021 --test audit/kernel_algebra.rs -o /tmp/kbfold-zk-kernel-audit
/tmp/kbfold-zk-kernel-audit --nocapture
