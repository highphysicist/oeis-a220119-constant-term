Historical search notes; build status in these notes predates formal verification.
See colab_status.json for the recorded successful build.

# Status and sources checked on 23 November 2026

## Precise claim

The theorem is the constant-term formula attributed to F. Chapoton on
25 May 2026 in OEIS A220119. The algebraic proof is self-contained.
The separate conjecture that (n+1)*(n+2) divides the sequence for positive n
is outside the result.

## Primary sources

1. https://oeis.org/A220119
2. https://oeis.org/A220119/internal
3. G. Almkvist and W. Zudilin, Differential equations, mirror maps and
   zeta values, arXiv:math/0402386v2 (2004), Section 4:
   https://arxiv.org/abs/math/0402386
   https://arxiv.org/html/math/0402386v2

The OEIS entry retrieved by the search service explicitly labels the
constant-term formula as a conjecture and gives the May 2026 attribution.
The 2004 paper supplies the older defining double sum and its zeta(4)
context. Its accessible text does not state the five-variable Laurent
identity proved here; a text search for "constant term" found no match.

## Search scope

Targeted web queries included:

- "A220119" conjecture proof
- "A220119" "constant" proof Chapoton
- "A220119" "Laurent"
- "A220119" "proof" "2026"
- "Chapoton" "220119"
- "A220119" site:github.com
- "a + c + d + e + 1" "binomial"
- "Chapoton" "Laurent" "zeta" "2026"

No earlier proof of this exact constant-term identity was located.
This is a bounded search, not an exhaustive priority certificate.
Some direct OEIS requests returned HTTP 403; the search service returned
the entry text, including both conjectures and their dates. The retrieved
internal-entry copy gives revision 72 dated 29 May 2026; a later uncrawled
change is possible.

## What has and has not been verified

- The all-n derivation uses only finite coefficient extraction, Vandermonde,
  and the explicitly displayed factorial identity.
- Direct five-variable expansion and the defining double sum agree through n=10.
- The auxiliary identities pass exact finite checks through n=45.
- The proof was reviewed within this conversation.
- No external peer review or Lean kernel verification has been performed.
- No publication or OEIS edit has been made.
- A standalone PDF was not produced because the available TeX installation
  lacked its format/bundle; the complete Markdown and LaTeX proofs are provided.
