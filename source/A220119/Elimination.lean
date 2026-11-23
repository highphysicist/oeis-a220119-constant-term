import A220119.PolynomialTools

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace A220119

lemma binomial_product_coeff {R : Type*} [CommSemiring R]
    (u v : R) (n : ℕ) :
    (((X+C u)^n*(X+C v)^n : Polynomial R).coeff n) =
      ∑ i ∈ range (n+1), ((n.choose i)^2 : R)*u^(n-i)*v^i := by
  rw [coeff_mul_range]
  apply sum_congr rfl
  intro i hi
  have hin : i ≤ n := by have := mem_range.mp hi; omega
  rw [Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_add_C_pow]
  rw [Nat.choose_symm hin, show n-(n-i) = i by omega]
  push_cast
  ring

lemma mixed_binomial_coeff {R : Type*} [CommSemiring R]
    (u v : R) (n i : ℕ) :
    (((C u+X)^n*(C v+X)^i : Polynomial R).coeff n) =
      ∑ j ∈ range (n+1),
        (n.choose j*i.choose (n-j) : R)*u^(n-j)*v^(i-(n-j)) := by
  rw [show (C u+X : Polynomial R) = X+C u by ring,
    show (C v+X : Polynomial R) = X+C v by ring, coeff_mul_range]
  apply sum_congr rfl
  intro j _
  rw [Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_add_C_pow]
  push_cast
  ring

def twoPoly {R : Type*} [CommSemiring R] (u v : R) (n : ℕ) :
    Polynomial (Polynomial R) :=
  C (C (u^n)*(C u+X)^n) *
    (X+C (C v))^n * (X+C (C v+X))^n

lemma joint_term {R : Type*} [CommSemiring R]
    (u v : R) (n i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    ((n.choose i)^2 : R)*u^n*v^(n-i) *
      ((n.choose j*i.choose (n-j) : R)*u^(n-j)*v^(i-(n-j))) =
    ((n.choose i)^2*n.choose j*i.choose (n-j) : R)*
      u^(2*n-j)*v^j := by
  by_cases h : n-j ≤ i
  · have hu : n+(n-j) = 2*n-j := by omega
    have hv : n-i+(i-(n-j)) = j := by omega
    calc
      _ = ((n.choose i)^2*n.choose j*i.choose (n-j) : R) *
          (u^n*u^(n-j))*(v^(n-i)*v^(i-(n-j))) := by
        push_cast
        ring
      _ = _ := by rw [← pow_add, ← pow_add, hu, hv]
  · have hz : i.choose (n-j) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hz]

lemma twoPoly_coeff {R : Type*} [CommSemiring R]
    (u v : R) (n : ℕ) :
    (((twoPoly u v n).coeff n).coeff n) =
      ∑ j ∈ range (n+1), (weight n j : R)*u^(2*n-j)*v^j := by
  classical
  have hE :
      ((twoPoly u v n).coeff n) =
      (C (u^n)*(C u+X)^n) *
        ∑ i ∈ range (n+1),
          ((n.choose i)^2 : Polynomial R)*
            (C v)^(n-i)*(C v+X)^i := by
    unfold twoPoly
    rw [mul_assoc, Polynomial.coeff_C_mul, binomial_product_coeff]
  rw [hE, mul_sum, coeff_sum']
  have hterm (i : ℕ) :
      (((C (u^n)*(C u+X)^n) *
        (((n.choose i)^2 : Polynomial R)*
          (C v)^(n-i)*(C v+X)^i)).coeff n) =
      ((n.choose i)^2 : R)*u^n*v^(n-i) *
        ∑ j ∈ range (n+1),
          (n.choose j*i.choose (n-j) : R)*u^(n-j)*v^(i-(n-j)) := by
    have hp :
        (C (u^n)*(C u+X)^n) *
          (((n.choose i)^2 : Polynomial R)*(C v)^(n-i)*(C v+X)^i) =
        C (((n.choose i)^2 : R)*u^n*v^(n-i)) *
          ((C u+X)^n*(C v+X)^i) := by
      simp only [map_mul, map_pow, map_natCast]
      ring
    rw [hp, Polynomial.coeff_C_mul, mixed_binomial_coeff]
  simp_rw [hterm, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := mem_range.mp hj; omega
  have hw :
      (∑ i ∈ range (n+1), (n.choose i)^2*n.choose j*i.choose (n-j)) =
        weight n j := by
    calc
      _ = n.choose j *
          (∑ i ∈ range (n+1), (n.choose i)^2*i.choose (n-j)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := outer_weight n j hjn
  calc
    _ = ∑ i ∈ range (n+1),
        ((n.choose i)^2*n.choose j*i.choose (n-j) : R)*
          u^(2*n-j)*v^j := by
      apply sum_congr rfl
      intro i hi
      exact joint_term u v n i j
        (by have := mem_range.mp hi; omega) hjn
    _ = ((∑ i ∈ range (n+1),
        (n.choose i)^2*n.choose j*i.choose (n-j) : ℕ) : R)*
        u^(2*n-j)*v^j := by
      push_cast
      simp only [sum_mul]
    _ = _ := by rw [hw]

lemma coefficient_A {R : Type*} [CommSemiring R]
    (K s : R) (n j : ℕ) (hj : j ≤ n) :
    ((C K*(1+X)^(2*n-j)*(1+X+C s)^j : Polynomial R).coeff n) =
      ∑ l ∈ range (j+1),
        (j.choose l*(2*n-l).choose n : R) * (K*s^l) := by
  classical
  have he : (1+X+C s : Polynomial R) = C s+(1+X) := by ring
  rw [he, add_pow (C s : Polynomial R) (1+X) j, mul_sum, coeff_sum']
  apply sum_congr rfl
  intro l hl
  have hlj : l ≤ j := by have := mem_range.mp hl; omega
  have hp :
      (C K*(1+X)^(2*n-j) *
        ((C s)^l*(1+X)^(j-l)*(j.choose l : Polynomial R))) =
      C ((j.choose l : R)*(K*s^l))*(1+X)^(2*n-l) := by
    have hn : 2*n-j+(j-l) = 2*n-l := by omega
    rw [← hn, pow_add]
    simp only [map_mul, map_pow, map_natCast]
    ring
  rw [hp, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
  push_cast
  ring

def Kpoly (n : ℕ) : Polynomial (Polynomial ℕ) :=
  (1+C X)^n*(1+C X+X)^n

def Rpoly (n j : ℕ) : ℕ :=
  ((((C (Kpoly n) * (1+X)^(2*n-j) *
      (1+X+C (C X+X))^j :
        Polynomial (Polynomial (Polynomial ℕ))).coeff n).coeff n).coeff n)

lemma Rpoly_expansion (n j : ℕ) (hj : j ≤ n) :
    Rpoly n j = expandedR n j := by
  unfold Rpoly
  rw [coefficient_A (Kpoly n) (C X+X) n j hj, coeff_sum', coeff_sum']
  unfold expandedR
  apply sum_congr rfl
  intro l hl
  have hln : l ≤ n := by have := mem_range.mp hl; omega
  have hH :
      (((Kpoly n)*(C X+X)^l).coeff n).coeff n = H n l := by
    unfold Kpoly H
    simp only [map_add, map_one, map_pow]
  simp only [← Nat.cast_mul, coeff_nat_mul', Nat.cast_id]
  rw [hH, H_eq_expandedH n l hln]
  ring

end A220119
