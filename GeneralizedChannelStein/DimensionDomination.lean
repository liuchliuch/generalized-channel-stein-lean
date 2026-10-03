import GeneralizedChannelStein.SumGram
import GeneralizedChannelStein.Families
import QuantumChannelStein.PseudoinverseDomination

/-! # Exact output-dimension domination and faithful replacer bounds -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.DimensionDomination
open QuantumChannelStein Matrix ChannelEntropy
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ} {κ : Type*} [Fintype κ]

def shiftedRows (S : Matrix (Fin a × Fin b) κ ℂ) (j k : Fin b) :
    Matrix (Fin a × Fin b) κ ℂ := fun u v => if u.2 = j then S (u.1,k) v else 0

omit [Fintype κ] in
theorem sum_shiftedRows_diagonal (S : Matrix (Fin a × Fin b) κ ℂ) :
    ∑ j : Fin b, shiftedRows S j j = S := by
  ext ⟨i,j⟩ v
  simp [shiftedRows, Matrix.sum_apply]

theorem shiftedRows_gram (S : Matrix (Fin a × Fin b) κ ℂ) (j k : Fin b)
    (u v : Fin a × Fin b) :
    (shiftedRows S j k * (shiftedRows S j k)ᴴ) u v =
      if u.2 = j ∧ v.2 = j then (S * Sᴴ) (u.1,k) (v.1,k) else 0 := by
  by_cases hu : u.2 = j <;> by_cases hv : v.2 = j <;>
    simp [shiftedRows, Matrix.mul_apply, Matrix.conjTranspose_apply, hu, hv]

/-- Pinching into the output-coordinate blocks is below marginal tensor identity. -/
theorem marginal_dominates_pinching (S : Matrix (Fin a × Fin b) κ ℂ) :
    (KrausChannel.traceOutput (S * Sᴴ) ⊗ₖ (1 : Operator b) -
      ∑ j : Fin b, shiftedRows S j j * (shiftedRows S j j)ᴴ).PosSemidef := by
  have hp : (∑ j : Fin b, ∑ k : Fin b,
      if k = j then 0 else shiftedRows S j k * (shiftedRows S j k)ᴴ).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro j hj
    apply Matrix.posSemidef_sum
    intro k hk
    split_ifs
    · exact Matrix.PosSemidef.zero
    · exact Matrix.posSemidef_self_mul_conjTranspose _
  convert hp using 1
  ext ⟨u,i⟩ ⟨v,j⟩
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, KrausChannel.traceOutput,
    Matrix.sum_apply, shiftedRows_gram, Matrix.zero_apply, Matrix.ite_apply]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply_eq, mul_one, and_self]
    have hc (x k : Fin b) :
        (if k = x then (0 : ℂ) else if i = x then (S*Sᴴ) (u,k) (v,k) else 0) =
        if i = x then (if k = i then 0 else (S*Sᴴ) (u,k) (v,k)) else 0 := by
      split_ifs <;> simp_all
    simp_rw [hc]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hs : (S*Sᴴ) (u,i) (v,i) = ∑ x : Fin b,
        if x = i then (S*Sᴴ) (u,x) (v,x) else 0 := by simp
    conv_lhs => rhs; rw [hs]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> simp
  · simp only [Matrix.one_apply, if_neg hij, mul_zero]
    have hz (x : Fin b) : ¬ (i = x ∧ j = x) := by rintro ⟨hi,hj⟩; exact hij (hi.trans hj.symm)
    simp [hz]

/-- Equation (9): every positive bipartite operator is bounded by output
dimension times its reference marginal tensored with identity. -/
theorem dimension_order (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hρ : ρ.PosSemidef) :
    ((b : ℝ) • (KrausChannel.traceOutput ρ ⊗ₖ (1 : Operator b)) - ρ).PosSemidef := by
  let S := CFC.sqrt ρ
  have hS : S * Sᴴ = ρ := by
    rw [(CFC.sqrt_nonneg ρ).posSemidef.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hgram := SpectralPinching.gram_sum_le_card (fun j : Fin b => shiftedRows S j j)
  rw [sum_shiftedRows_diagonal,hS,Fintype.card_fin] at hgram
  have hm := marginal_dominates_pinching S
  rw [hS] at hm
  have hh := (hm.smul (show (0 : ℝ) ≤ (b : ℝ) from Nat.cast_nonneg b)).add hgram
  convert hh using 1; module

/-- Every channel Choi matrix is bounded by output dimension times identity. -/
theorem choi_le_output_dimension (N : KrausChannel a b) :
    ((b : ℝ) • (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) - N.choi).PosSemidef := by
  have h := dimension_order N.choi N.choi_positive
  rw [N.traceOutput_choi] at h
  simpa only [Matrix.one_kronecker_one] using h

/-- The sharp single-use faithful-replacer domination constant b/w. -/
theorem cpLe_replacer_of_lower_bound (N : KrausChannel a b) (ω : State b)
    (w : ℝ) (hw : 0 < w) (hω : (ω.matrix - w • (1 : Operator b)).PosSemidef) :
    MatrixMap.CPLe N.toLinearMap ((((b : ℝ) / w : ℝ) : ℂ) • (ReplacerChannel.channel a ω).toLinearMap) := by
  rw [MatrixMap.cpLe_iff_choi_difference, MatrixMap.choi_smul,
    MatrixMap.choi_toLinearMap, MatrixMap.choi_toLinearMap, ReplacerChannel.channel_choi]
  have hp := (MatrixMap.posSemidef_kronecker (Matrix.PosSemidef.one (n := Fin a)) hω).smul
    (div_nonneg (Nat.cast_nonneg b) hw.le)
  have hq := choi_le_output_dimension N
  convert hp.add hq using 1
  ext ⟨i,u⟩ ⟨j,v⟩
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, Complex.real_smul, smul_eq_mul, Matrix.one_apply]
  push_cast
  split_ifs <;> simp_all <;> field_simp <;> ring

/-- A literal lower bound on all eigenvalues supplies the required PSD inequality. -/
theorem scalar_le_of_eigenvalue_lower (ω : State b) (w : ℝ)
    (h : ∀ i : Fin b, w ≤ ω.positive.isHermitian.eigenvalues i) :
    (ω.matrix - w • (1 : Operator b)).PosSemidef := by
  letI : CStarAlgebra (Operator b) := CStarAlgebra.mk
  have hh : cfc (fun _ : ℝ => w) ω.matrix ≤ cfc (fun x : ℝ => x) ω.matrix := by
    apply (cfc_le_iff (fun _ : ℝ => w) (fun x : ℝ => x) ω.matrix
      (ha := ω.positive.isHermitian.isSelfAdjoint)).mpr
    intro x hx
    rw [ω.positive.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i,rfl⟩ := hx
    exact h i
  rw [cfc_const w ω.matrix ω.positive.isHermitian.isSelfAdjoint,
    cfc_id' ℝ ω.matrix ω.positive.isHermitian.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one] at hh
  exact hh

/-- Paper constant C=log₂ b−log₂ w gives the exact per-use CP rate. -/
theorem cpLe_replacer_log_rate (N : KrausChannel a b) (ω : State b)
    (hb : 0 < b) (w : ℝ) (hw : 0 < w)
    (hω : ∀ i : Fin b, w ≤ ω.positive.isHermitian.eigenvalues i) :
    MatrixMap.CPLe N.toLinearMap
      ((((2 : ℝ) ^ (Real.logb 2 (b : ℝ) - Real.logb 2 w) : ℝ) : ℂ) •
        (ReplacerChannel.channel a ω).toLinearMap) := by
  have heq : (2 : ℝ) ^ (Real.logb 2 (b : ℝ) - Real.logb 2 w) = (b : ℝ) / w := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
      (Nat.cast_pos.mpr hb), Real.rpow_logb (by norm_num) (by norm_num) hw]
  rw [heq]
  exact cpLe_replacer_of_lower_bound N ω w hw (scalar_le_of_eigenvalue_lower ω w hω)

/-- The same fixed faithful replacer controls all tensor blocklengths at nC. -/
theorem cpLe_replacer_tensor_rate (N : KrausChannel a b) (ω : State b)
    (hb : 0 < b) (w : ℝ) (hw : 0 < w)
    (hω : ∀ i : Fin b, w ≤ ω.positive.isHermitian.eigenvalues i) (n : ℕ) :
    MatrixMap.CPLe (N.tensorPower n).toLinearMap
      (((((2 : ℝ) ^ ((n : ℝ) * (Real.logb 2 (b : ℝ) - Real.logb 2 w))) : ℝ) : ℂ) •
        ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap) := by
  have h := N.cpLe_tensorPower (ReplacerChannel.channel a ω)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    (cpLe_replacer_log_rate N ω hb w hw hω) n
  convert h using 1
  congr 2
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- The paper's w is literally the least eigenvalue of the witnessing state. -/
def minEigenvalue (ω : State b) (hb : 0 < b) : ℝ :=
  Finset.univ.inf' ⟨⟨0,hb⟩,Finset.mem_univ _⟩ ω.positive.isHermitian.eigenvalues

theorem minEigenvalue_le (ω : State b) (hb : 0 < b) (i : Fin b) :
    minEigenvalue ω hb ≤ ω.positive.isHermitian.eigenvalues i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem minEigenvalue_pos (ω : State b) (hb : 0 < b) (hω : ω.matrix.PosDef) :
    0 < minEigenvalue ω hb := by
  apply (Finset.lt_inf'_iff _).mpr
  intro i hi
  exact hω.eigenvalues_pos i

theorem minEigenvalue_le_one (ω : State b) (hb : 0 < b) : minEigenvalue ω hb ≤ 1 := by
  have h := TestingSDP.eigenvalue_le_trace ω.positive (⟨0,hb⟩ : Fin b)
  exact (minEigenvalue_le ω hb ⟨0,hb⟩).trans (by simpa [ω.trace_one] using h)

/-- Exact paper rate, with w derived internally as the actual minimum eigenvalue. -/
theorem faithful_replacer_domination (N : KrausChannel a b) (ω : State b)
    (hb : 0 < b) (hω : ω.matrix.PosDef) (n : ℕ) :
    MatrixMap.CPLe (N.tensorPower n).toLinearMap
      (Complex.ofReal ((2 : ℝ) ^ ((n : ℝ) * (Real.logb 2 (b : ℝ) - Real.logb 2 (minEigenvalue ω hb)))) •
        ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap) := by
  exact cpLe_replacer_tensor_rate N ω hb _ (minEigenvalue_pos ω hb hω) (minEigenvalue_le ω hb) n

end GeneralizedChannelStein.DimensionDomination
