# A220119: submission checklist after verification

This is a factual checklist, not text to paste as an OEIS comment.

1. Wait for a full successful build and the exact-statement/axiom audit.
   The GitHub publishing helper refuses to proceed without that result.
2. Recheck https://oeis.org/A220119 and its history for a newer proof or edit.
   The search performed here did not establish first priority.
3. Publish the written proof, the actual checked Lean modules, dependency
   information, and verification logs. The helper prints immutable commit URLs.
4. Log in to OEIS, open A220119, and choose **edit**. Propose an update to
   this existing sequence. Preserve Chapoton's conjecture and its attribution.
5. In your own words, write a short addition explaining exactly which
   constant-term identity was proved and pointing to the proof in Links.
   Distinguish Lean kernel checking from independent human mathematical review.
   Sign a new comment with ` - ~~~~`.
6. In Links, add the written proof and the reproducible formalization. The
   publishing helper supplies factual link metadata and immutable URLs.
7. State the substantial AI assistance honestly in the linked proof/repository.
   Supply a human contributor name, and be prepared to explain the argument
   and answer editorial questions yourself.
8. Save the edit and choose **These changes are ready for review by an OEIS
   Editor** when your contribution is ready.

## Facts to cover in your own comment

- Target: the constant-term formula attributed to F. Chapoton, May 25, 2026.
- Quantifier: every integer n >= 0.
- Proof method: eliminate e and b, evaluate a two-variable diagonal coefficient,
  and apply finite binomial identities/Vandermonde.
- Main theorem: `A220119.constantTerm_eq_doubleSum`.
- Original-formula audit: `IndependentAudit.original_statement`.
- Scope: the separate (n+1)(n+2) divisibility conjecture is not established here.
- Verification: report the actual successful build, toolchain, and audit;
  numerical checks alone do not establish the universal statement.

## Relevant OEIS guidance

The published AI guidance requires a human author responsible for correctness,
prohibits AI tools as authors/coauthors, prohibits AI-generated full comments,
and prohibits AI-generated replies to editorial Pink Box questions.
Do not paste an AI-written comment draft as your contribution.

- https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions
- https://oeis.org/wiki/Style_Sheet
- https://oeis.org/wiki/QandA_For_New_OEIS
- https://oeis.org/wiki/Overview_of_the_contribution_process

WG007 is an open working-group discussion, not an additional official rule.
It does not establish a mandatory journal-publication or registry requirement
for this small conjecture:
https://oeis.org/wiki/WG007_Handling_AI_proofs

Access note: direct wiki requests returned HTTP 403 during preparation;
indexed primary-source copies supplied the guidance. Recheck the live pages
before submission.
