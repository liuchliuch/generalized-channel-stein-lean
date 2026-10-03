import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity

/-!
# Scalar binomial bounds for fixed-block amplification

These are the scalar estimates in the proof of Lemma 4.5 of
arXiv:2609.27196. They do not assert a tensor-product identity or any fact
about quantum channels. In particular, passing from an operator-valued
truncation to these scalar sums remains a separate obligation.
-/

open Finset

namespace QuantumChannelStein

/-- The binomial sum in the order used for a residual term of degree `j`. -/
theorem binomial_sum (m : ℕ) (a b : ℝ) :
    (∑ j ∈ range (m + 1), (m.choose j : ℝ) * a ^ (m - j) * b ^ j) =
      (a + b) ^ m := by
  rw [add_comm a b, add_pow]
  apply sum_congr rfl
  intro j _
  ring

/-- A common scalar lower bound on the exponential weights controls any
selected subset of the binomial expansion. -/
theorem weighted_binomial_sum_le (m : ℕ) (s : Finset ℕ) (a b z q : ℝ)
    (hs : s ⊆ range (m + 1)) (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 0 ≤ z)
    (hq : ∀ j ∈ s, q ≤ z ^ j) :
    q * (∑ j ∈ s, (m.choose j : ℝ) * a ^ (m - j) * b ^ j) ≤
      (a + z * b) ^ m := by
  calc
    q * (∑ j ∈ s, (m.choose j : ℝ) * a ^ (m - j) * b ^ j) =
        ∑ j ∈ s, q * ((m.choose j : ℝ) * a ^ (m - j) * b ^ j) :=
      mul_sum ..
    _ ≤ ∑ j ∈ s, (m.choose j : ℝ) * a ^ (m - j) * (z * b) ^ j := by
      apply sum_le_sum
      intro j hj
      calc
        q * ((m.choose j : ℝ) * a ^ (m - j) * b ^ j) ≤
            z ^ j * ((m.choose j : ℝ) * a ^ (m - j) * b ^ j) :=
          mul_le_mul_of_nonneg_right (hq j hj) (by positivity)
        _ = (m.choose j : ℝ) * a ^ (m - j) * (z * b) ^ j := by
          rw [mul_pow]
          ring
    _ ≤ ∑ j ∈ range (m + 1), (m.choose j : ℝ) * a ^ (m - j) * (z * b) ^ j := by
      apply sum_le_sum_of_subset_of_nonneg hs
      intro j _ _
      positivity
    _ = (a + z * b) ^ m := binomial_sum m a (z * b)

/-- Terms beyond a natural-number cutoff in a binomial expansion. -/
def binomialTail (m t : ℕ) (a b : ℝ) : ℝ :=
  ∑ j ∈ (range (m + 1)).filter (t < ·),
    (m.choose j : ℝ) * a ^ (m - j) * b ^ j

/-- An elementary Chernoff bound with an integer cutoff. -/
theorem binomialTail_le (m t : ℕ) (a b z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 1 ≤ z) :
    binomialTail m t a b ≤ (z ^ t)⁻¹ * (a + z * b) ^ m := by
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have h := weighted_binomial_sum_le m ((range (m + 1)).filter (t < ·))
    a b z (z ^ t) (filter_subset _ _) ha hb hzpos.le (by
      intro j hj
      exact pow_le_pow_right₀ hz (le_of_lt (mem_filter.mp hj).2))
  change z ^ t * binomialTail m t a b ≤ (a + z * b) ^ m at h
  have hdiv : binomialTail m t a b ≤ (a + z * b) ^ m / z ^ t := by
    apply (le_div_iff₀ (pow_pos hzpos t)).2
    simpa only [mul_comm] using h
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- Terms beyond a real cutoff, as occur for `η * m` in Lemma 4.5. -/
noncomputable def realBinomialTail (m : ℕ) (u a b : ℝ) : ℝ :=
  ∑ j ∈ (range (m + 1)).filter (fun j : ℕ => u < (j : ℝ)),
    (m.choose j : ℝ) * a ^ (m - j) * b ^ j

/-- The same exponential-weight estimate for a real cutoff. -/
theorem realBinomialTail_le (m : ℕ) (u a b z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 1 ≤ z) :
    realBinomialTail m u a b ≤ z ^ (-u) * (a + z * b) ^ m := by
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have h := weighted_binomial_sum_le m
    ((range (m + 1)).filter (fun j : ℕ => u < (j : ℝ))) a b z (z ^ u)
    (filter_subset _ _) ha hb hzpos.le (by
      intro j hj
      have hju : u ≤ (j : ℝ) := le_of_lt (mem_filter.mp hj).2
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hz hju)
  change z ^ u * realBinomialTail m u a b ≤ (a + z * b) ^ m at h
  rw [Real.rpow_neg hzpos.le]
  have hdiv : realBinomialTail m u a b ≤ (a + z * b) ^ m / z ^ u := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hzpos u)).2
    simpa only [mul_comm] using h
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- The exponentially decaying scalar truncation bound used in Lemma 4.5.
The hypothesis on `z ^ η` is slightly weaker than the paper's choice
`z = 4 ^ (1 / η)`. -/
theorem realBinomialTail_le_half_pow (m : ℕ) (ε η z : ℝ)
    (hε : 0 ≤ ε) (hz : 1 ≤ z) (hzη : (4 : ℝ) ≤ z ^ η)
    (hsmall : ε ≤ 1 / (1 + z)) :
    realBinomialTail m (η * m) (1 + ε) ε ≤ (1 / 2 : ℝ) ^ m := by
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hden : 0 < 1 + z := by positivity
  have hsmall' : ε * (1 + z) ≤ 1 := (le_div_iff₀ hden).mp hsmall
  have hbase : 1 + ε + z * ε ≤ 2 := by nlinarith
  have hbase0 : 0 ≤ 1 + ε + z * ε := by positivity
  have hzηpos : 0 < z ^ η := Real.rpow_pos_of_pos hzpos η
  have hratio : (z ^ η)⁻¹ * (1 + ε + z * ε) ≤ 1 / 2 := by
    rw [mul_comm (z ^ η)⁻¹, ← div_eq_mul_inv]
    apply (div_le_iff₀ hzηpos).2
    nlinarith
  calc
    realBinomialTail m (η * m) (1 + ε) ε ≤
        z ^ (-(η * m)) * (1 + ε + z * ε) ^ m :=
      realBinomialTail_le m (η * m) (1 + ε) ε z (by positivity) hε hz
    _ = ((z ^ η)⁻¹ * (1 + ε + z * ε)) ^ m := by
      rw [Real.rpow_neg hzpos.le, Real.rpow_mul_natCast hzpos.le,
        mul_pow, inv_pow]
    _ ≤ (1 / 2 : ℝ) ^ m :=
      pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hzηpos.le) hbase0) hratio m

/-- The exact choice of the exponential weight made in Lemma 4.5. -/
theorem amplification_scalar_bound (m : ℕ) (ε η : ℝ)
    (hε : 0 ≤ ε) (hη : 0 < η)
    (hsmall : ε ≤ 1 / (1 + (4 : ℝ) ^ (1 / η))) :
    realBinomialTail m (η * m) (1 + ε) ε ≤ (1 / 2 : ℝ) ^ m := by
  apply realBinomialTail_le_half_pow m ε η ((4 : ℝ) ^ (1 / η)) hε
  · exact Real.one_le_rpow (by norm_num) (by positivity)
  · have hweight : ((4 : ℝ) ^ (1 / η)) ^ η = 4 := by
      simpa only [one_div] using Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 4) hη.ne'
    exact hweight.ge
  · exact hsmall

/-- Counting correction choices introduces precisely the scalar factor `3^m`. -/
theorem binomial_cost_sum (m : ℕ) :
    (∑ j ∈ range (m + 1), (m.choose j : ℝ) * 2 ^ j) = 3 ^ m := by
  simpa only [one_pow, mul_one, show (1 : ℝ) + 2 = 3 by norm_num] using
    binomial_sum m 1 2

/-- Every truncation has combinatorial cost at most `3^m`. -/
theorem binomial_cost_sum_le (m : ℕ) (s : Finset ℕ) (hs : s ⊆ range (m + 1)) :
    (∑ j ∈ s, (m.choose j : ℝ) * 2 ^ j) ≤ 3 ^ m := by
  calc
    (∑ j ∈ s, (m.choose j : ℝ) * 2 ^ j) ≤
        ∑ j ∈ range (m + 1), (m.choose j : ℝ) * 2 ^ j := by
      apply sum_le_sum_of_subset_of_nonneg hs
      intro j _ _
      positivity
    _ = 3 ^ m := binomial_cost_sum m

/-- A uniform scalar bound for each retained tensor term yields the cost
factor from the proof of Lemma 4.5. -/
theorem binomial_weighted_cost_sum_le (m : ℕ) (s : Finset ℕ) (c : ℕ → ℝ) (B : ℝ)
    (hs : s ⊆ range (m + 1)) (hB : 0 ≤ B) (hc : ∀ j ∈ s, c j ≤ B) :
    (∑ j ∈ s, (m.choose j : ℝ) * 2 ^ j * c j) ≤ 3 ^ m * B := by
  calc
    (∑ j ∈ s, (m.choose j : ℝ) * 2 ^ j * c j) ≤
        ∑ j ∈ s, (m.choose j : ℝ) * 2 ^ j * B := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hc j hj) (by positivity)
    _ = (∑ j ∈ s, (m.choose j : ℝ) * 2 ^ j) * B := (sum_mul ..).symm
    _ ≤ 3 ^ m * B := mul_le_mul_of_nonneg_right (binomial_cost_sum_le m s hs) hB

/-- The rate interpolation inequality for a retained term with `j ≤ η m`. -/
theorem truncated_rate_exponent_le (k m j : ℕ) (S L η : ℝ)
    (hj : j ≤ m) (hcut : (j : ℝ) ≤ η * m) (hSL : S ≤ L) :
    (k : ℝ) * (((m - j : ℕ) : ℝ) * S + j * L) / 2 ≤
      (k : ℝ) * m * (S + η * (L - S)) / 2 := by
  have hmix : ((m - j : ℕ) : ℝ) * S + j * L ≤ (m : ℝ) * (S + η * (L - S)) := by
    rw [Nat.cast_sub hj]
    nlinarith [mul_nonneg (sub_nonneg.mpr hcut) (sub_nonneg.mpr hSL)]
  have hscaled := mul_le_mul_of_nonneg_left hmix (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  exact div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hscaled) (by norm_num)

/-- The scalar cost estimate in Lemma 4.5, before rewriting its right side
using the increased rate `v`. -/
theorem truncated_binomial_rate_cost_le (k m : ℕ) (S L η : ℝ) (hSL : S ≤ L) :
    (∑ j ∈ (range (m + 1)).filter (fun j : ℕ => (j : ℝ) ≤ η * m),
      (m.choose j : ℝ) * 2 ^ j *
        (2 : ℝ) ^ ((k : ℝ) * (((m - j : ℕ) : ℝ) * S + j * L) / 2)) ≤
      3 ^ m * (2 : ℝ) ^ ((k : ℝ) * m * (S + η * (L - S)) / 2) := by
  apply binomial_weighted_cost_sum_le m _ _ _ (filter_subset _ _) (by positivity)
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hj).1)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (truncated_rate_exponent_le k m j S L η hjm (mem_filter.mp hj).2 hSL)

end QuantumChannelStein
