#!/usr/bin/env sh
set -eu
rustc --edition=2021 --test audit/kernel_algebra.rs -o /tmp/kbfold-zk-kernel-audit
/tmp/kbfold-zk-kernel-audit --nocapture

rustc --edition=2021 --test audit/fold_masks.rs -o /tmp/kbfold-zk-fold-mask-audit
/tmp/kbfold-zk-fold-mask-audit --nocapture

rustc --edition=2021 --test audit/binary_kernel.rs -o /tmp/kbfold-zk-binary-audit
/tmp/kbfold-zk-binary-audit --nocapture
