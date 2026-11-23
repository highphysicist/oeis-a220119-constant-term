import A220119.Elimination

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 16

noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace A220119

private lemma numerator_rearrangement {R : Type*} [CommSemiring R]
    (av bv cv dv ev : R) :
    (1+cv)*(1+cv+dv)*(1+av)*(1+av+cv+dv+ev)*
        (1+av+bv)*(1+av+bv+cv+dv+ev) =
      ((1+cv)*(1+cv+dv))*(1+av)*(1+av+bv)*
        (ev+(1+av+(cv+dv)))*(ev+(1+av+(cv+dv)+bv)) := by
  have htail :
      (1+av+cv+dv+ev)*(1+av+bv)*(1+av+bv+cv+dv+ev) =
        (1+av+bv)*(ev+(1+av+(cv+dv)))*
          (ev+(1+av+(cv+dv)+bv)) := by ring
  simpa only [mul_assoc] using
    congrArg (fun z : R => ((1+cv)*(1+cv+dv)*(1+av))*z) htail

theorem constantTerm_eq_doubleSum (n : ℕ) : constantTerm n = doubleSum n := by
  classical
  let u : PADC := 1+X
  let v : PADC := 1+X+C (C X+X)
  have hnum :
      numerator =
        C (C (C ((1+C X)*(1+C X+X)))) *
          C (C u) * C (C u+X) *
          (X+C (C v)) * (X+C (C v+X)) := by
    dsimp [numerator, a, b, c, d, e, u, v]
    simp only [map_add, map_one, map_mul]
    simpa only [a, b, c, d, e, add_assoc, mul_assoc] using
      (numerator_rearrangement (R := PEBADC) a b c d e)
  have hform :
      numerator^n =
        C (C (C (Kpoly n))) * twoPoly (R := PADC) u v n := by
    rw [hnum]
    simp only [Kpoly, twoPoly, mul_pow, map_mul, map_pow, mul_assoc]
  have hEB :
      ((numerator^n).coeff n).coeff n =
        C (Kpoly n) *
          (∑ j ∈ range (n+1),
            (weight n j : Polynomial (Polynomial (Polynomial ℕ))) *
              u^(2*n-j)*v^j) := by
    rw [hform]
    simp only [Polynomial.coeff_C_mul]
    rw [twoPoly_coeff (R := PADC) u v n]
  unfold constantTerm
  rw [hEB, mul_sum, coeff_sum', coeff_sum', coeff_sum']
  calc
    _ = ∑ j ∈ range (n+1), weight n j*Rpoly n j := by
      apply sum_congr rfl
      intro j _
      have hp :
          C (Kpoly n) *
            ((weight n j : Polynomial (Polynomial (Polynomial ℕ))) *
              u^(2*n-j)*v^j) =
          (weight n j : Polynomial (Polynomial (Polynomial ℕ))) *
            (C (Kpoly n)*u^(2*n-j)*v^j) := by
        simp only [mul_assoc]
        exact mul_left_comm (C (Kpoly n) : PADC)
          (weight n j : PADC) (u^(2*n-j)*v^j)
      rw [hp]
      simp only [coeff_nat_mul', Nat.cast_id]
      rfl
    _ = ∑ j ∈ range (n+1), weight n j*expandedR n j := by
      apply sum_congr rfl
      intro j hj
      rw [Rpoly_expansion n j (by have := mem_range.mp hj; omega)]
    _ = _ := expanded_double_sum n

theorem full_conjecture : FullConjecture := constantTerm_eq_doubleSum

end A220119
