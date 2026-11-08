#!/usr/bin/env sh
set -eu
rustc --edition=2021 --test audit/kernel_algebra.rs -o /tmp/kbfold-zk-kernel-audit
/tmp/kbfold-zk-kernel-audit --nocapture

rustc --edition=2021 --test audit/fold_masks.rs -o /tmp/kbfold-zk-fold-mask-audit
/tmp/kbfold-zk-fold-mask-audit --nocapture

rustc --edition=2021 --test audit/binary_kernel.rs -o /tmp/kbfold-zk-binary-audit
/tmp/kbfold-zk-binary-audit --nocapture

rustc --edition=2021 --test audit/affine_sigma.rs -o /tmp/kbfold-zk-affine-sigma-audit
/tmp/kbfold-zk-affine-sigma-audit --nocapture

rustc --edition=2021 --test audit/malicious_sigma.rs -o /tmp/kbfold-zk-malicious-sigma-audit
/tmp/kbfold-zk-malicious-sigma-audit --nocapture

rustc --edition=2021 --test audit/global_extraction.rs -o /tmp/kbfold-zk-global-extraction-audit
/tmp/kbfold-zk-global-extraction-audit --nocapture

rustc --edition=2021 --test audit/full_kbfold.rs -o /tmp/kbfold-zk-full-kbfold-audit
/tmp/kbfold-zk-full-kbfold-audit --nocapture

rustc --edition=2021 --test audit/final_security.rs -o /tmp/kbfold-zk-final-security-audit
/tmp/kbfold-zk-final-security-audit --nocapture
