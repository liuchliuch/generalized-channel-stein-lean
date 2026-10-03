import GeneralizedChannelStein.LocalExpansion
import GeneralizedChannelStein.ImageProjectorScalars

/-! Chebyshev product-image filters with literal local contraction expansions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.ImageProjector
open QuantumChannelStein Matrix LocalExpansion ImageProjectorScalars
open scoped BigOperators Matrix.Norms.L2Operator
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {k : ℕ}

def affineMatrix (Q : Matrix ι ι ℂ) (k : ℕ) : Block ι k :=
  (((k:ℝ)+1)/((k:ℝ)-1)) • (1 : Block ι k) +
    (-2/((k:ℝ)-1)) • ∑ i : Fin k, oneSite i Q

def affineExpansion (Q : Matrix ι ι ℂ) (hQ : ‖Q‖≤1) (k : ℕ) : Expansion ι k :=
  (Expansion.one.scale ((((k:ℝ)+1)/((k:ℝ)-1):ℝ):ℂ)).add
    ((Expansion.sum (fun i : Fin k => oneSiteExpansion i Q hQ)).scale ((-2/((k:ℝ)-1):ℝ):ℂ))

theorem affineExpansion_value (Q : Matrix ι ι ℂ) (hQ : ‖Q‖≤1) (k : ℕ) :
    (affineExpansion Q hQ k).value = affineMatrix Q k := by
  simp only [affineExpansion,affineMatrix,Expansion.value_add,Expansion.value_scale,Expansion.value_one,Expansion.value_sum,value_oneSiteExpansion]
  ext i j
  simp [Complex.real_smul]

theorem affineExpansion_size (Q : Matrix ι ι ℂ) (hQ : ‖Q‖≤1) (k : ℕ) :
    (affineExpansion Q hQ k).HasSize 1 := by
  apply Expansion.hasSize_add
  · exact Expansion.hasSize_scale _ (Expansion.hasSize_one 1) _
  · exact Expansion.hasSize_scale _ (Expansion.hasSize_sum _ (fun i => size_oneSiteExpansion i Q hQ)) _

theorem affineExpansion_cost (Q : Matrix ι ι ℂ) (hQ : ‖Q‖≤1) (hk : 2≤k) :
    (affineExpansion Q hQ k).cost ≤ 7 := by
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hden : 0 < (k:ℝ)-1 := by linarith
  have hnum : 0 ≤ ((k:ℝ)+1)/((k:ℝ)-1) := div_nonneg (by positivity) hden.le
  have hneg : -2/((k:ℝ)-1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hden.le
  simp only [affineExpansion,Expansion.cost_add,Expansion.cost_scale,Expansion.cost_one,
    Expansion.cost_sum,cost_oneSiteExpansion,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnum,abs_of_nonpos hneg]
  have heq : ((k:ℝ)+1)/((k:ℝ)-1) + -(-2/((k:ℝ)-1))*(k:ℝ) =
      (3*(k:ℝ)+1)/((k:ℝ)-1) := by ring
  rw [heq]
  apply (div_le_iff₀ hden).mpr
  linarith

/-- The actual filter, without any norm or error assumptions in its definition. -/
def filterMatrix (P : Matrix ι ι ℂ) (k : ℕ) (ξ : ℝ) : Block ι k :=
  (denominator k (filterDegree k ξ))⁻¹ •
    chebyshevMatrix (affineMatrix (1-P) k) (filterDegree k ξ)

def filterExpansion (P : Matrix ι ι ℂ) (hQ : ‖1-P‖≤1) (k : ℕ) (ξ : ℝ) : Expansion ι k :=
  ((affineExpansion (1-P) hQ k).chebyshev (filterDegree k ξ)).scale
    ((denominator k (filterDegree k ξ))⁻¹ : ℝ)

theorem filterExpansion_value (P : Matrix ι ι ℂ) (hQ : ‖1-P‖≤1) (k : ℕ) (ξ : ℝ) :
    (filterExpansion P hQ k ξ).value = filterMatrix P k ξ := by
  simp only [filterExpansion,filterMatrix,Expansion.value_scale,Expansion.value_chebyshev,affineExpansion_value]
  ext i j
  simp [Complex.real_smul]

theorem filterExpansion_size (P : Matrix ι ι ℂ) (hQ : ‖1-P‖≤1) (k : ℕ) (ξ : ℝ) :
    (filterExpansion P hQ k ξ).HasSize (min k (filterDegree k ξ)) := by
  apply Expansion.hasSize_min
  exact Expansion.hasSize_scale _
    (Expansion.size_chebyshev _ (affineExpansion_size _ _ _) _) _

theorem filterExpansion_cost (P : Matrix ι ι ℂ) (hQ : ‖1-P‖≤1) (hk : 2≤k) (ξ : ℝ) :
    (filterExpansion P hQ k ξ).cost ≤ (15:ℝ)^(filterDegree k ξ) := by
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hd := one_le_denominator hk' (filterDegree k ξ)
  have hdp : 0 < denominator k (filterDegree k ξ) := lt_of_lt_of_le zero_lt_one hd
  have hi : |(denominator k (filterDegree k ξ))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr hdp.le)]
    exact (inv_le_one₀ hdp).mpr hd
  rw [filterExpansion,Expansion.cost_scale]
  simp only [Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul hi (Expansion.cost_chebyshev _ (affineExpansion_cost _ _ hk) _)
    (Expansion.cost_nonneg _) zero_le_one).trans_eq (one_mul _)

end GeneralizedChannelStein.ImageProjector
