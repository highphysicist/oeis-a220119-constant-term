import Mathlib

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
