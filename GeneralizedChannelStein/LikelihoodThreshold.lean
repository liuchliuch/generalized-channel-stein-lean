import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Finite classical likelihood threshold estimate -/
noncomputable section
namespace GeneralizedChannelStein.LikelihoodThreshold
open scoped BigOperators

/-- A bounded finite random variable's upper tail carries the stated mass. -/
theorem expectation_le_threshold {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (L t : ℝ) (hz : ∀ i, 0 < p i → z i ≤ L) :
    ∑ i, p i * z i ≤ t + (L-t) * ∑ i, if t ≤ z i then p i else 0 := by
  classical
  calc
    ∑ i, p i * z i ≤ ∑ i, (t * p i + (L-t) * if t ≤ z i then p i else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : t ≤ z i
      · rw [if_pos hi]
        by_cases hpi : p i = 0
        · simp [hpi]
        · have hzi := hz i (lt_of_le_of_ne (hp i) (Ne.symm hpi))
          nlinarith [mul_le_mul_of_nonneg_left hzi (hp i)]
      · rw [if_neg hi]
        nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge hi) (hp i)]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, mul_one]

/-- Choosing the affine threshold makes its tail a feasible type-I test. -/
theorem tail_mass_lower {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (E L ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) (hEL : E < L)
    (hE : E ≤ ∑ i, p i * z i) (hz : ∀ i, 0 < p i → z i ≤ L) :
    1-ε ≤ ∑ i, if (E-(1-ε)*L)/ε ≤ z i then p i else 0 := by
  let t := (E-(1-ε)*L)/ε
  have ht : t < L := by dsimp [t]; apply (div_lt_iff₀ hε).mpr; nlinarith
  have hid : ε*t = E-(1-ε)*L := by dsimp [t]; field_simp
  have hbound := expectation_le_threshold p z hp hs L t hz
  have hdiff : 0 < L-t := sub_pos.mpr ht
  nlinarith

/-- Positive-mass likelihoods inherit a finite domination bound. -/
theorem logRatio_le (p q L : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (hdom : p ≤ (2 : ℝ)^L * q) : Real.logb 2 (p/q) ≤ L := by
  have hqpos : 0 < q := by
    by_contra h
    have : q = 0 := le_antisymm (le_of_not_gt h) hq
    simp [this] at hdom
    linarith
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (div_pos hp hqpos)).mpr
  exact (div_le_iff₀ hqpos).mpr hdom

/-- A likelihood threshold pays at most its inverse exponential under the alternative. -/
theorem likelihood_tail_cost {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hs : ∑ i, p i = 1) (t : ℝ) :
    (∑ i, if 0 < p i ∧ t ≤ Real.logb 2 (p i/q i) then q i else 0) ≤ (2 : ℝ)^(-t) := by
  classical
  have hpow : 0 < (2 : ℝ)^t := Real.rpow_pos_of_pos (by norm_num) _
  calc
    _ ≤ ∑ i, (2 : ℝ)^(-t) * p i := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · by_cases hqi : q i = 0
        · rw [hqi]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hp i)
        · have hqpos : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hqi)
          have hr := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ)<2)
            (div_pos hi.1 hqpos)).mp hi.2
          have hr' := (le_div_iff₀ hqpos).mp hr
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          exact (le_inv_mul_iff₀ hpow).mpr hr'
      · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hp i)
    _ = _ := by rw [← Finset.mul_sum, hs, mul_one]

/-- Excluding null target coordinates leaves the target tail probability unchanged. -/
theorem supported_tail_mass {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (t : ℝ) :
    (∑ i, if 0 < p i ∧ t ≤ z i then p i else 0) =
      ∑ i, if t ≤ z i then p i else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < p i
  · simp [hi]
  · have hpi : p i = 0 := le_antisymm (le_of_not_gt hi) (hp i)
    simp [hpi]

end GeneralizedChannelStein.LikelihoodThreshold
