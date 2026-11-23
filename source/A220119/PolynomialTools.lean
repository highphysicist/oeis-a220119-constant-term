import A220119.Arithmetic

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
