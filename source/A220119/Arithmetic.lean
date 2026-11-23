import A220119.Spec

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
