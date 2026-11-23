import Mathlib

/-! Convenience concatenation of checked modules.
The authoritative verification is the recorded multi-module build. -/

/- A220119/Spec.lean -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-! The exact five-variable target. No theorem is assumed in this module. -/
noncomputable section
open scoped BigOperators
namespace A220119

abbrev PC := Polynomial ℕ
abbrev PDC := Polynomial PC
abbrev PADC := Polynomial PDC
abbrev PBADC := Polynomial PADC
abbrev PEBADC := Polynomial PBADC

-- Polynomial nesting is e[b[a[d[c]]]].
def c : PEBADC := Polynomial.C (Polynomial.C (Polynomial.C (Polynomial.C Polynomial.X)))
def d : PEBADC := Polynomial.C (Polynomial.C (Polynomial.C Polynomial.X))
def a : PEBADC := Polynomial.C (Polynomial.C Polynomial.X)
def b : PEBADC := Polynomial.C Polynomial.X
def e : PEBADC := Polynomial.X

def numerator : PEBADC :=
  (1 + c) * (1 + c + d) * (1 + a) *
  (1 + a + c + d + e) * (1 + a + b) *
  (1 + a + b + c + d + e)

-- This equals CT of (numerator / (a*b*c*d*e))^n, since every
-- exponent in the numerator is nonnegative.
def constantTerm (n : ℕ) : ℕ :=
  (((((numerator ^ n).coeff n).coeff n).coeff n).coeff n).coeff n

def weight (n k : ℕ) : ℕ := (n.choose k)^2 * (n+k).choose n

def doubleSum (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n+1), ∑ k ∈ Finset.range (n+1),
    weight n j * weight n k * (j+k).choose n

def FullConjecture : Prop := ∀ n : ℕ, constantTerm n = doubleSum n

end A220119

/- A220119/Arithmetic.lean -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators
open Finset

namespace A220119

/-! Universal binomial identities used in the written proof.
This module contains proof attempts, not assumed axioms.
-/

lemma range_sum_extend {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) {m n : ℕ} (hmn : m ≤ n)
    (hz : ∀ i, m < i → i ≤ n → f i = 0) :
    (∑ i ∈ range (n+1), f i) = ∑ i ∈ range (m+1), f i := by
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [mem_range] at hi ⊢
    omega
  · intro i hi hnot
    apply hz i
    · simp only [mem_range] at hnot
      omega
    · simp only [mem_range] at hi
      omega

lemma vandermonde_range (m n k : ℕ) :
    (∑ i ∈ range (k+1), m.choose i * n.choose (k-i)) =
      (m+n).choose k := by
  rw [Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma vandermonde_truncated (j k n : ℕ) (hj : j ≤ n) :
    (∑ i ∈ range (j+1), j.choose i * k.choose (n-i)) =
      (j+k).choose n := by
  rw [← vandermonde_range j k n]
  symm
  apply range_sum_extend _ hj
  intro i hi _
  simp [Nat.choose_eq_zero_of_lt hi]

lemma complementary_choices (n i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    n.choose i * i.choose (n-j) =
      n.choose j * j.choose (n-i) := by
  by_cases h : n-j ≤ i
  · have hji : n-i ≤ j := by omega
    have h1 : n-(n-j) = j := by omega
    have h2 : i-(n-j) = j-(n-i) := by omega
    have h3 := Nat.choose_mul (n := n) (k := i) (s := n-j) hi h
    simpa only [h1, h2, Nat.choose_symm hj, Nat.choose_symm hji] using h3
  · have h1 : i < n-j := by omega
    have h2 : j < n-i := by omega
    simp [Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2]

lemma outer_weight (n j : ℕ) (hj : j ≤ n) :
    n.choose j *
      (∑ i ∈ range (n+1), (n.choose i)^2 * i.choose (n-j)) =
      weight n j := by
  have hsum :
      (∑ i ∈ range (n+1), (n.choose i)^2 * i.choose (n-j)) =
      n.choose j * (n+j).choose n := by
    calc
      _ = ∑ i ∈ range (n+1),
          n.choose j * (n.choose i * j.choose (n-i)) := by
        apply sum_congr rfl
        intro i hi
        have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
        calc
          _ = n.choose i * (n.choose i * i.choose (n-j)) := by ring
          _ = n.choose i * (n.choose j * j.choose (n-i)) := by
            rw [complementary_choices n i j hin hj]
          _ = _ := by ring
      _ = n.choose j *
          (∑ i ∈ range (n+1), n.choose i * j.choose (n-i)) := by
        rw [mul_sum]
      _ = _ := by rw [vandermonde_range]
  rw [hsum, weight]
  ring

lemma choose_bridge (n l r : ℕ) (hr : r ≤ l) (hl : l ≤ n) :
    (2*n-l).choose n * (2*n-r).choose (l-r) =
      (2*n-r).choose n * (n-r).choose (n-l) := by
  have hnl : n ≤ 2*n-l := by omega
  have hs : l-r ≤ 2*n-r := by omega
  have h1 : (2*n-r) - (l-r) = 2*n-l := by omega
  have h2 : (2*n-r)-n = n-r := by omega
  have h3 : (2*n-l)-n = n-l := by omega
  have he : (2*n-r).choose (2*n-l) = (2*n-r).choose (l-r) := by
    simpa only [h1] using (Nat.choose_symm hs)
  have h := Nat.choose_mul
    (n := 2*n-r) (k := 2*n-l) (s := n) (by omega) hnl
  rw [he, h2, h3] at h
  simpa only [mul_comm] using h

def expandedH (n l : ℕ) : ℕ :=
  ∑ r ∈ range (l+1), (n.choose r)^2 * (2*n-r).choose (l-r)

lemma expandedH_auxiliary (n l : ℕ) (hl : l ≤ n) :
    (2*n-l).choose n * expandedH n l =
      ∑ k ∈ range (n+1), weight n k * k.choose (n-l) := by
  have hreflect :
      (∑ k ∈ range (n+1), weight n k * k.choose (n-l)) =
      ∑ r ∈ range (n+1),
        (n.choose r)^2 * (2*n-r).choose n * (n-r).choose (n-l) := by
    rw [← Finset.sum_range_reflect
      (fun k => weight n k * k.choose (n-l)) (n+1)]
    apply sum_congr rfl
    intro r hr
    have hrn : r ≤ n := by have := Finset.mem_range.mp hr; omega
    have h1 : n+1-1-r = n-r := by omega
    have h2 : n+(n-r) = 2*n-r := by omega
    simp only [h1, weight, Nat.choose_symm hrn, h2]
  rw [hreflect]
  have htruncate :
      (∑ r ∈ range (n+1),
        (n.choose r)^2 * (2*n-r).choose n * (n-r).choose (n-l)) =
      ∑ r ∈ range (l+1),
        (n.choose r)^2 * (2*n-r).choose n * (n-r).choose (n-l) := by
    apply range_sum_extend _ hl
    intro r hrl hrn
    have hz : n-r < n-l := by omega
    simp [Nat.choose_eq_zero_of_lt hz]
  rw [htruncate, expandedH, mul_sum]
  apply sum_congr rfl
  intro r hr
  have hrl : r ≤ l := by have := Finset.mem_range.mp hr; omega
  have h := choose_bridge n l r hrl hl
  calc
    _ = (n.choose r)^2 *
        ((2*n-l).choose n * (2*n-r).choose (l-r)) := by ring
    _ = _ := by rw [h]; ring

def expandedR (n j : ℕ) : ℕ :=
  ∑ l ∈ range (j+1),
    j.choose l * ((2*n-l).choose n * expandedH n l)

lemma expandedR_eq (n j : ℕ) (hj : j ≤ n) :
    expandedR n j =
      ∑ k ∈ range (n+1), weight n k * (j+k).choose n := by
  unfold expandedR
  calc
    _ = ∑ l ∈ range (j+1), j.choose l *
        (∑ k ∈ range (n+1), weight n k * k.choose (n-l)) := by
      apply sum_congr rfl
      intro l hl
      have hlj : l ≤ j := by have := Finset.mem_range.mp hl; omega
      rw [expandedH_auxiliary n l (by omega)]
    _ = ∑ l ∈ range (j+1), ∑ k ∈ range (n+1),
        j.choose l * (weight n k * k.choose (n-l)) := by
      simp only [mul_sum]
    _ = ∑ k ∈ range (n+1), ∑ l ∈ range (j+1),
        j.choose l * (weight n k * k.choose (n-l)) := by
      rw [sum_comm]
    _ = ∑ k ∈ range (n+1), weight n k *
        (∑ l ∈ range (j+1), j.choose l * k.choose (n-l)) := by
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
      apply sum_congr rfl
      intro l _
      ring
    _ = _ := by
      apply sum_congr rfl
      intro k _
      rw [vandermonde_truncated j k n hj]

theorem expanded_double_sum (n : ℕ) :
    (∑ j ∈ range (n+1), weight n j * expandedR n j) = doubleSum n := by
  unfold doubleSum
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [expandedR_eq n j hjn, mul_sum]
  apply sum_congr rfl
  intro k _
  ring

end A220119

/- A220119/PolynomialTools.lean -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace A220119

lemma coeff_nat_mul' {R : Type*} [Semiring R]
    (m : ℕ) (p : Polynomial R) (k : ℕ) :
    ((m : Polynomial R)*p).coeff k = (m : R)*p.coeff k := by
  have hc : (m : Polynomial R) = C (m : R) := by simp
  rw [hc, Polynomial.coeff_C_mul]

lemma coeff_sum' {R : Type*} [Semiring R] {ι : Type*}
    (s : Finset ι) (f : ι → Polynomial R) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

lemma coeff_mul_range {R : Type*} [Semiring R]
    (p q : Polynomial R) (k : ℕ) :
    (p*q).coeff k =
      ∑ i ∈ range (k+1), p.coeff i * q.coeff (k-i) := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma choose_pow {R : Type*} [CommSemiring R] (x : R) (n : ℕ) :
    (1+x)^n = ∑ i ∈ range (n+1), (n.choose i : R)*x^i := by
  rw [add_comm, add_pow]
  apply sum_congr rfl
  intro i _
  simp only [one_pow, mul_one]
  ring

lemma coeff_shifted_one_add (n r k : ℕ) :
    ((C ((n.choose r)^2) * X^r * (1+X)^(n-r) :
        Polynomial ℕ).coeff k) =
      if r ≤ k then (n.choose r)^2 * (n-r).choose (k-r) else 0 := by
  have he :
      (C ((n.choose r)^2) * X^r * (1+X)^(n-r) : Polynomial ℕ) =
      C ((n.choose r)^2) * ((1+X)^(n-r)*X^r) := by ring
  rw [he, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
  by_cases h : r ≤ k
  · simp [h, Polynomial.coeff_one_add_X_pow]
  · simp [h]

def L (n : ℕ) : Polynomial ℕ :=
  ∑ r ∈ range (n+1), monomial r (n.choose r * (n+r).choose n)

lemma coeff_L (n k : ℕ) :
    (L n).coeff k = n.choose k * (n+k).choose n := by
  classical
  unfold L
  rw [coeff_sum']
  by_cases hk : k ≤ n
  · simp [Polynomial.coeff_monomial, show k < n+1 by omega]
  · have hz : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [Polynomial.coeff_monomial, show ¬ k < n+1 by omega, hz]

lemma L_expansion (n : ℕ) :
    L n = ∑ r ∈ range (n+1),
      C ((n.choose r)^2)*X^r*(1+X)^(n-r) := by
  classical
  ext k
  rw [coeff_L, coeff_sum']
  simp_rw [coeff_shifted_one_add]
  by_cases hk : k ≤ n
  · have htrim :
        (∑ r ∈ range (n+1),
          if r ≤ k then (n.choose r)^2*(n-r).choose (k-r) else 0) =
        ∑ r ∈ range (k+1),
          if r ≤ k then (n.choose r)^2*(n-r).choose (k-r) else 0 := by
      apply range_sum_extend _ hk
      intro r hr _
      simp [show ¬ r ≤ k by omega]
    rw [htrim]
    have hsum :
        (∑ r ∈ range (k+1),
          if r ≤ k then (n.choose r)^2*(n-r).choose (k-r) else 0) =
        n.choose k * (n+k).choose n := by
      calc
        _ = ∑ r ∈ range (k+1), n.choose k * (n.choose r*k.choose r) := by
          apply sum_congr rfl
          intro r hr
          have hrk : r ≤ k := by have := mem_range.mp hr; omega
          have hc := Nat.choose_mul (n := n) (k := k) (s := r) hk hrk
          simp only [if_pos hrk]
          calc
            _ = n.choose r *
                (n.choose r*(n-r).choose (k-r)) := by ring
            _ = n.choose r*(n.choose k*k.choose r) := by rw [← hc]
            _ = _ := by ring
        _ = n.choose k *
            (∑ r ∈ range (k+1), n.choose r*k.choose (k-r)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro r hr
          have hrk : r ≤ k := by have := mem_range.mp hr; omega
          rw [Nat.choose_symm hrk]
        _ = n.choose k * (n+k).choose k := by rw [vandermonde_range]
        _ = _ := by
          congr 1
          have hs := Nat.choose_symm (n := n+k) (k := n) (by omega)
          simpa only [show n+k-n = k by omega] using hs
    exact hsum.symm
  · have hz : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz, zero_mul]
    symm
    apply sum_eq_zero
    intro r hr
    have hrn : r ≤ n := by have := mem_range.mp hr; omega
    have hrk : r ≤ k := by omega
    have hz' : (n-r).choose (k-r) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hrk, hz']

lemma L_product_coeff (n l : ℕ) (hl : l ≤ n) :
    (((1+X)^n * L n : Polynomial ℕ).coeff l) = expandedH n l := by
  rw [L_expansion, mul_sum, coeff_sum']
  have hterm (r : ℕ) (hr : r ≤ n) :
      (((1+X)^n *
        (C ((n.choose r)^2)*X^r*(1+X)^(n-r)) : Polynomial ℕ).coeff l) =
      if r ≤ l then (n.choose r)^2*(2*n-r).choose (l-r) else 0 := by
    have he :
        ((1+X)^n * (C ((n.choose r)^2)*X^r*(1+X)^(n-r)) :
          Polynomial ℕ) =
        C ((n.choose r)^2)*((1+X)^(2*n-r)*X^r) := by
      rw [show 2*n-r = n+(n-r) by omega, pow_add]
      ring
    rw [he, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    by_cases h : r ≤ l
    · simp [h, Polynomial.coeff_one_add_X_pow]
    · simp [h]
  calc
    _ = ∑ r ∈ range (n+1),
        if r ≤ l then (n.choose r)^2*(2*n-r).choose (l-r) else 0 := by
      apply sum_congr rfl
      intro r hr
      exact hterm r (by have := mem_range.mp hr; omega)
    _ = ∑ r ∈ range (l+1),
        if r ≤ l then (n.choose r)^2*(2*n-r).choose (l-r) else 0 := by
      apply range_sum_extend _ hl
      intro r hr _
      simp [show ¬ r ≤ l by omega]
    _ = expandedH n l := by
      unfold expandedH
      apply sum_congr rfl
      intro r hr
      simp [show r ≤ l by have := mem_range.mp hr; omega]

lemma L_product_coeff_first (n l : ℕ) :
    (((1+X)^n * L n : Polynomial ℕ).coeff l) =
      ∑ r ∈ range (l+1),
        n.choose r * n.choose (l-r) * (n+r).choose n := by
  rw [mul_comm, coeff_mul_range]
  apply sum_congr rfl
  intro r _
  rw [coeff_L, Polynomial.coeff_one_add_X_pow]
  simp only [Nat.cast_id]
  ring

def H (n l : ℕ) : ℕ :=
  (((C (1+X))^n * (1+C X+X)^n * (C X+X)^l :
    Polynomial (Polynomial ℕ)).coeff n).coeff n

lemma homogeneous_diagonal (n s m : ℕ) (hs : s ≤ n) :
    (((C (X^s) * (C X+X)^m : Polynomial (Polynomial ℕ)).coeff n).coeff n) =
      if s+m = 2*n then m.choose n else 0 := by
  have he : (C X+X : Polynomial (Polynomial ℕ)) = X+C X := by ring
  rw [he, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  have hp :
      (X^s * (X^(m-n) * (m.choose n : Polynomial ℕ)) : Polynomial ℕ) =
      (m.choose n : Polynomial ℕ)*X^(s+(m-n)) := by
    rw [pow_add]
    ring
  rw [hp]
  simp only [coeff_nat_mul', Polynomial.coeff_X_pow, Nat.cast_id]
  by_cases hm : n ≤ m
  · by_cases hsm : s+m = 2*n
    · simp only [if_pos hsm,
        if_pos (show n = s+(m-n) by omega),
        if_pos (show s+(m-n) = n by omega), mul_one]
    · simp only [if_neg hsm,
        if_neg (show ¬ n = s+(m-n) by omega),
        if_neg (show ¬ s+(m-n) = n by omega), mul_zero]
  · have hz : m.choose n = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hsm : ¬ s+m = 2*n := by omega
    simp [hz, hsm]

lemma H_expanded (n l : ℕ) :
    H n l =
      ∑ s ∈ range (n+1), ∑ t ∈ range (n+1),
        n.choose s * n.choose t *
          (if s+(t+l) = 2*n then (t+l).choose n else 0) := by
  classical
  let u : Polynomial (Polynomial ℕ) := C X+X
  have hp :
      ((C (1+X))^n : Polynomial (Polynomial ℕ)) =
        ∑ s ∈ range (n+1), C ((n.choose s : Polynomial ℕ)*X^s) := by
    rw [← map_pow, choose_pow, map_sum]
  have hq :
      ((1+C X+X)^n : Polynomial (Polynomial ℕ)) =
        ∑ t ∈ range (n+1), (n.choose t : Polynomial (Polynomial ℕ))*u^t := by
    have he : (1+C X+X : Polynomial (Polynomial ℕ)) = 1+u := by dsimp [u]; ring
    rw [he]
    exact A220119.choose_pow u n
  unfold H
  rw [hp, hq]
  simp only [sum_mul, mul_sum, coeff_sum']
  conv_lhs => rw [Finset.sum_comm]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro t _
  have hs' : s ≤ n := by have := mem_range.mp hs; omega
  have he :
      (C ((n.choose s : Polynomial ℕ)*X^s) *
        ((n.choose t : Polynomial (Polynomial ℕ))*u^t) * u^l) =
      (n.choose s*n.choose t : Polynomial (Polynomial ℕ)) *
        (C (X^s)*u^(t+l)) := by
    rw [map_mul, map_natCast, pow_add]
    push_cast
    ring
  change ((C ((n.choose s : Polynomial ℕ)*X^s) *
    ((n.choose t : Polynomial (Polynomial ℕ))*u^t) * u^l).coeff n).coeff n = _
  rw [he]
  simp only [← Nat.cast_mul, coeff_nat_mul', Nat.cast_id]
  exact congrArg (fun z : ℕ => n.choose s * n.choose t * z)
    (homogeneous_diagonal n s (t+l) hs')

lemma diagonal_degree_sum (n l s : ℕ) (hl : l ≤ n) (hs : s ≤ n) :
    (∑ t ∈ range (n+1), n.choose t *
      (if s+(t+l) = 2*n then (t+l).choose n else 0)) =
      if n-l ≤ s then n.choose (2*n-l-s)*(2*n-s).choose n else 0 := by
  classical
  by_cases h : n-l ≤ s
  · rw [if_pos h]
    let t0 := 2*n-l-s
    have ht0 : t0 < n+1 := by dsimp [t0]; omega
    have hsum : s+(t0+l) = 2*n := by dsimp [t0]; omega
    have he : t0+l = 2*n-s := by dsimp [t0]; omega
    have hsingle :
        (∑ t ∈ range (n+1), n.choose t *
          (if s+(t+l) = 2*n then (t+l).choose n else 0)) =
        n.choose t0 * (if s+(t0+l) = 2*n then (t0+l).choose n else 0) := by
      apply sum_eq_single t0
      · intro t _ hne
        have hx : ¬ s+(t+l) = 2*n := by dsimp [t0] at hne; omega
        simp [hx]
      · intro ht
        exact (ht (mem_range.mpr ht0)).elim
    rw [if_pos hsum, he] at hsingle
    exact hsingle
  · rw [if_neg h]
    apply sum_eq_zero
    intro t ht
    have htn : t ≤ n := by have := mem_range.mp ht; omega
    have hx : ¬ s+(t+l) = 2*n := by omega
    simp [hx]

lemma H_first (n l : ℕ) (hl : l ≤ n) :
    H n l =
      ∑ r ∈ range (l+1),
        n.choose r * n.choose (l-r) * (n+r).choose n := by
  rw [H_expanded]
  have h1 :
      (∑ s ∈ range (n+1), ∑ t ∈ range (n+1),
        n.choose s*n.choose t *
          (if s+(t+l) = 2*n then (t+l).choose n else 0)) =
      ∑ s ∈ range (n+1), n.choose s *
        (if n-l ≤ s then n.choose (2*n-l-s)*(2*n-s).choose n else 0) := by
    apply sum_congr rfl
    intro s hs
    have hsn : s ≤ n := by have := mem_range.mp hs; omega
    calc
      _ = n.choose s * (∑ t ∈ range (n+1), n.choose t *
          (if s+(t+l) = 2*n then (t+l).choose n else 0)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro t _
        ring
      _ = _ := by rw [diagonal_degree_sum n l s hl hsn]
  rw [h1, ← Finset.sum_range_reflect
    (fun s => n.choose s *
      (if n-l ≤ s then n.choose (2*n-l-s)*(2*n-s).choose n else 0)) (n+1)]
  have hterm (r : ℕ) (hr : r ≤ n) :
      n.choose (n+1-1-r) *
        (if n-l ≤ n+1-1-r then
          n.choose (2*n-l-(n+1-1-r)) *
            (2*n-(n+1-1-r)).choose n else 0) =
      if r ≤ l then
        n.choose r*n.choose (l-r)*(n+r).choose n else 0 := by
    have ha : n+1-1-r = n-r := by omega
    rw [ha, Nat.choose_symm hr]
    by_cases hrl : r ≤ l
    · have ha : n-l ≤ n-r := by omega
      have hb : 2*n-(n-r) = n+r := by omega
      have hc : 2*n-l-(n-r) = n-(l-r) := by omega
      simp only [if_pos hrl, if_pos ha, hb, hc,
        Nat.choose_symm (show l-r ≤ n by omega)]
      ring
    · have ha : ¬ n-l ≤ n-r := by omega
      simp [hrl, ha]
  calc
    _ = ∑ r ∈ range (n+1), if r ≤ l then
        n.choose r*n.choose (l-r)*(n+r).choose n else 0 := by
      apply sum_congr rfl
      intro r hr
      exact hterm r (by have := mem_range.mp hr; omega)
    _ = ∑ r ∈ range (l+1), if r ≤ l then
        n.choose r*n.choose (l-r)*(n+r).choose n else 0 := by
      apply range_sum_extend _ hl
      intro r hr _
      simp [show ¬ r ≤ l by omega]
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      simp [show r ≤ l by have := mem_range.mp hr; omega]

lemma H_eq_expandedH (n l : ℕ) (hl : l ≤ n) : H n l = expandedH n l := by
  rw [H_first n l hl, ← L_product_coeff_first, L_product_coeff n l hl]

end A220119

/- A220119/Elimination.lean -/

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

/- A220119/Main.lean -/

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

/- Audit.lean -/

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
