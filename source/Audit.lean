import A220119.Main

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

/-! An independently written target, rather than a check of a theorem's name.
Variables are nested e[b[a[d[c]]]] and the original six factors are literal.
-/
namespace IndependentAudit

abbrev P := Polynomial (Polynomial (Polynomial (Polynomial (Polynomial ℕ))))

def originalNumerator : P :=
  let cv : P := Polynomial.C (Polynomial.C (Polynomial.C (Polynomial.C Polynomial.X)))
  let dv : P := Polynomial.C (Polynomial.C (Polynomial.C Polynomial.X))
  let av : P := Polynomial.C (Polynomial.C Polynomial.X)
  let bv : P := Polynomial.C Polynomial.X
  let ev : P := Polynomial.X
  (1+cv)*(1+cv+dv)*(1+av)*(1+av+cv+dv+ev)*
    (1+av+bv)*(1+av+bv+cv+dv+ev)

theorem original_statement (n : ℕ) :
    (((((originalNumerator^n).coeff n).coeff n).coeff n).coeff n).coeff n =
      ∑ j ∈ Finset.range (n+1), ∑ k ∈ Finset.range (n+1),
        ((n.choose j)^2*(n+j).choose n) *
          ((n.choose k)^2*(n+k).choose n) * (j+k).choose n := by
  exact A220119.constantTerm_eq_doubleSum n

end IndependentAudit

#print axioms A220119.constantTerm_eq_doubleSum
#print axioms A220119.full_conjecture
#print axioms IndependentAudit.original_statement
