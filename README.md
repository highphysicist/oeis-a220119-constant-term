# A220119 constant-term identity

Human contributor and submitter: Shreyas Samir Kolte.

This repository proves the constant-term identity attributed to F. Chapoton
(25 May 2026) in [OEIS A220119](https://oeis.org/A220119), for every n >= 0.
The sequence's separate (n+1)(n+2) divisibility conjecture is outside this result.

- [Written algebraic proof](paper/PROOF.md), with [LaTeX source](paper/PROOF.tex).
- [Exact original-statement audit](source/Audit.lean).
- [Universal Lean theorem](source/A220119/Main.lean).
- [Successful Colab build record](evidence/colab_status.json) and [axiom audit](evidence/colab_logs/axiom_audit.log).

## Verification

The six Lean modules in source/ are the actual files hashed in the successful Colab run.
All six modules compiled with Lean 4.19.0; the separate original-statement audit
passed. Only propext, Classical.choice, and Quot.sound are permitted by the audit.
This is ordinary Lean kernel verification, not a second independent kernel.
The concatenated standalone file is a convenience copy and was not separately checked.
Numerical checks are supporting evidence, separate from the universal theorem.

To reproduce in Colab, open notebooks/A220119_Lean_Colab.ipynb and upload the
complete assets/A220119_Lean_Colab.zip when the first cell asks. A High-RAM CPU
runtime gives headroom; no GPU is needed. The exact minimum RAM is unmeasured.

To reproduce locally or on the configured GitHub Actions runner:

    python3 ci_verify.py

That script fetches the recorded mathlib commit and Lean version. The Actions
result is separate from the saved Colab evidence; its success is not assumed.

## Provenance and scope

Substantial OpenAI ChatGPT/Codex assistance was used in proof discovery,
drafting, formalization, and debugging. The human contributor is responsible
for the submission. No independent human mathematical review is claimed here.
The defining double sum predates this work (Almkvist and Zudilin, 2004).
The conjectured Laurent polynomial is credited to Chapoton, not claimed as a
new discovery. A targeted prior-art search did not find an earlier proof;
first priority has not been established.

For OEIS submission, see OEIS_SUBMISSION_GUIDE.md. That file is a factual
checklist; write your own comment in accordance with OEIS's AI guidance.
