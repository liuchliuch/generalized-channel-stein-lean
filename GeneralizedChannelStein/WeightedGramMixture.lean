import GeneralizedChannelStein.SumGram
import GeneralizedChannelStein.BranchExtraction
import GeneralizedChannelStein.TraceDefectCompletion

/-! Weighted matrix Gram domination and actual convex free-channel mixtures. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.WeightedGramMixture
open QuantumChannelStein Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]

theorem weighted_gram_domination (w : ι → ℝ) (A : ι → Matrix κ η ℂ)
    (hw : ∀ i, 0 ≤ w i) :
    ((∑ i, w i) • (∑ i, w i • (A i * (A i)ᴴ)) -
      (∑ i, w i • A i) * (∑ i, w i • A i)ᴴ).PosSemidef := by
  have hp : (∑ i, ∑ j, (w i*w j) • ((A i-A j)*(A i-A j)ᴴ)).PosSemidef := by
    apply Finset.sum_induction
    · intro B C hB hC; exact hB.add hC
    · exact Matrix.PosSemidef.zero
    · intro i _
      apply Finset.sum_induction
      · intro B C hB hC; exact hB.add hC
      · exact Matrix.PosSemidef.zero
      · intro j _
        exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (mul_nonneg (hw i) (hw j))
  have hd1 : (∑ i, ∑ j, (w i*w j) • (A i*(A i)ᴴ)) =
      (∑ j, w j) • (∑ i, w i • (A i*(A i)ᴴ)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, Finset.sum_mul, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  have hd2 : (∑ i, ∑ j, (w i*w j) • (A j*(A j)ᴴ)) =
      (∑ j, w j) • (∑ i, w i • (A i*(A i)ᴴ)) := by
    rw [Finset.sum_comm]
    simpa only [mul_comm] using hd1
  have hc1 : (∑ i, ∑ j, (w i*w j) • (A i*(A j)ᴴ)) =
      (∑ i, w i • A i)*(∑ i, w i • A i)ᴴ := by
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
      Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hc2 : (∑ i, ∑ j, (w i*w j) • (A j*(A i)ᴴ)) =
      (∑ i, w i • A i)*(∑ i, w i • A i)ᴴ := by
    rw [Finset.sum_comm]
    simpa only [mul_comm] using hc1
  have he : (∑ i, ∑ j, (w i*w j) • ((A i-A j)*(A i-A j)ᴴ)) =
      (2:ℝ) • ((∑ i, w i) • (∑ i, w i • (A i*(A i)ᴴ)) -
        (∑ i, w i • A i)*(∑ i, w i • A i)ᴴ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
      smul_sub, Finset.sum_sub_distrib]
    rw [hd1, hd2, hc1, hc2]
    module
  have h := hp.smul (by norm_num : (0:ℝ) ≤ 1/2)
  rw [he, smul_smul] at h
  norm_num at h
  exact h

omit [Fintype κ] in
theorem gram_complex_smul (c : ℂ) (A : Matrix κ η ℂ) :
    (c • A)*(c • A)ᴴ = (‖c‖^2 : ℝ) • (A*Aᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hc : c*star c = ((‖c‖^2:ℝ):ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq] using Complex.mul_conj c
  rw [hc]
  rfl

theorem complex_weighted_gram (c : ι → ℂ) (h : ι → ℝ)
    (F : ι → Matrix κ η ℂ) (hh : ∀ i, 0 < h i) :
    ((∑ i, ‖c i‖*h i) • (∑ i, (‖c i‖/h i) • (F i*(F i)ᴴ)) -
      (∑ i, c i • F i)*(∑ i, c i • F i)ᴴ).PosSemidef := by
  let w : ι → ℝ := fun i => ‖c i‖*h i
  let A : ι → Matrix κ η ℂ := fun i => ((w i : ℂ)⁻¹*c i) • F i
  have hw : ∀ i, 0 ≤ w i := fun i => mul_nonneg (norm_nonneg _) (hh i).le
  have hA : ∀ i, w i • A i = c i • F i := by
    intro i
    by_cases hc : c i = 0
    · simp [A,w,hc]
    · have hwne : w i ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hc) (hh i).ne'
      change ((w i : ℂ) • (((w i : ℂ)⁻¹*c i) • F i)) = _
      rw [smul_smul]
      congr 1
      field_simp
  have hG : ∀ i, w i • (A i*(A i)ᴴ) = (‖c i‖/h i) • (F i*(F i)ᴴ) := by
    intro i
    rw [show A i = ((w i : ℂ)⁻¹*c i) • F i from rfl, gram_complex_smul, smul_smul]
    by_cases hc : c i = 0
    · simp [w,hc]
    · have hn : ‖c i‖ ≠ 0 := norm_ne_zero_iff.mpr hc
      have hwne : w i ≠ 0 := mul_ne_zero hn (hh i).ne'
      congr 1
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      dsimp [w]
      field_simp
  have H := weighted_gram_domination w A hw
  simpa only [hA, hG] using H

def coefficientMass (c : ι → ℂ) (h : ι → ℝ) : ℝ := ∑ i, ‖c i‖*h i
def mixtureWeight (c : ι → ℂ) (h : ι → ℝ) (i : ι) : ℝ :=
  ‖c i‖*h i / coefficientMass c h

theorem mixtureWeight_nonneg (c : ι → ℂ) (h : ι → ℝ)
    (hh : ∀ i, 0 < h i) (hH : 0 < coefficientMass c h) (i : ι) :
    0 ≤ mixtureWeight c h i := div_nonneg (mul_nonneg (norm_nonneg _) (hh i).le) hH.le

theorem sum_mixtureWeight (c : ι → ℂ) (h : ι → ℝ)
    (hH : 0 < coefficientMass c h) : ∑ i, mixtureWeight c h i = 1 := by
  simp only [mixtureWeight, ← Finset.sum_div]
  exact div_self hH.ne'

theorem mixture_gram_domination (c : ι → ℂ) (h : ι → ℝ)
    (F : ι → Matrix κ η ℂ) (G : ι → Matrix κ κ ℂ) {p : ℝ}
    (hp : 0 ≤ p) (hh : ∀ i, 0 < h i) (hH : 0 < coefficientMass c h)
    (hG : ∀ i, (G i - (p/(h i)^2) • (F i*(F i)ᴴ)).PosSemidef) :
    ((∑ i, mixtureWeight c h i • G i) -
      (p/(coefficientMass c h)^2) •
        ((∑ i, c i • F i)*(∑ i, c i • F i)ᴴ)).PosSemidef := by
  have hsum : (∑ i, mixtureWeight c h i •
      (G i - (p/(h i)^2) • (F i*(F i)ᴴ))).PosSemidef := by
    apply Finset.sum_induction
    · intro B C hB hC; exact hB.add hC
    · exact Matrix.PosSemidef.zero
    · intro i _
      exact (hG i).smul (mixtureWeight_nonneg c h hh hH i)
  have hcs := (complex_weighted_gram c h F hh).smul
    (div_nonneg hp (sq_nonneg (coefficientMass c h)))
  have hscalar (i : ι) : mixtureWeight c h i * (p/(h i)^2) =
      (p/(coefficientMass c h)^2) * coefficientMass c h * (‖c i‖/h i) := by
    unfold mixtureWeight
    field_simp
  have hid : (∑ i, mixtureWeight c h i • (G i - (p/(h i)^2) • (F i*(F i)ᴴ))) =
      (∑ i, mixtureWeight c h i • G i) -
        (p/(coefficientMass c h)^2) •
          (coefficientMass c h • (∑ i, (‖c i‖/h i) • (F i*(F i)ᴴ))) := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, hscalar]
    simp only [mul_assoc]
  rw [hid] at hsum
  change ((p/(coefficientMass c h)^2) •
    (coefficientMass c h • (∑ i, (‖c i‖/h i) • (F i*(F i)ᴴ)) -
      (∑ i, c i • F i)*(∑ i, c i • F i)ᴴ)).PosSemidef at hcs
  have H := hsum.add hcs
  rw [smul_sub] at H
  convert H using 1; abel

section Channels
variable {a b : ℕ}

theorem choi_real_sum (w : ι → ℝ) (M : ι → MatrixMap a b) :
    MatrixMap.choi (∑ i, (w i : ℂ) • M i) = ∑ i, w i • MatrixMap.choi (M i) := by
  ext x y
  simp [MatrixMap.choi, Matrix.sum_apply, Complex.real_smul]

theorem convex_finite_mixture_mem (S : Set (MatrixMap a b))
    (hS : Convex ℝ (MatrixMap.choi '' S)) (M : ι → MatrixMap a b)
    (hM : ∀ i, M i ∈ S) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) : (∑ i, (w i : ℂ) • M i) ∈ S := by
  have H := hS.sum_mem (fun i _ => hw i) hsum (fun i _ => ⟨M i,hM i,rfl⟩)
  obtain ⟨N,hN,heq⟩ := H
  have hEq : N = ∑ i, (w i : ℂ) • M i := by
    apply MatrixMap.choi_injective
    rw [choi_real_sum]
    exact heq
  rwa [← hEq]

theorem finite_mixture_isChannel (M : ι → KrausChannel a b)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    IsChannel (∑ i, (w i : ℂ) • (M i).toLinearMap) := by
  constructor
  · apply (MatrixMap.completelyPositive_iff_choi_positive _).2
    rw [choi_real_sum]
    apply Finset.sum_induction
    · intro B C hB hC; exact hB.add hC
    · exact Matrix.PosSemidef.zero
    · intro i _
      exact (MatrixMap.choi_positive_of_completelyPositive _
        (MatrixMap.completelyPositive_toLinearMap (M i))).smul (hw i)
  · intro X
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Matrix.trace_sum, Matrix.trace_smul]
    have htrace (i : ι) : ((M i).toLinearMap X).trace = X.trace := (M i).trace_apply X
    simp only [htrace, ← Finset.sum_smul, ← Complex.ofReal_sum, hsum,
      Complex.ofReal_one, one_smul]

def choiColumn (K : Matrix (Fin b) (Fin a) ℂ) : Matrix (Fin a × Fin b) (Fin 1) ℂ :=
  fun i _ => K i.2 i.1

theorem choi_adMap (K : Matrix (Fin b) (Fin a) ℂ) :
    MatrixMap.choi (BranchExtraction.adMap K) = choiColumn K*(choiColumn K)ᴴ := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [MatrixMap.choi, BranchExtraction.adMap_apply, choiColumn,
    Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, ite_and]

theorem choiColumn_sum (c : ι → ℂ) (K : ι → Matrix (Fin b) (Fin a) ℂ) :
    choiColumn (∑ i, c i • K i) = ∑ i, c i • choiColumn (K i) := by
  ext x y
  simp [choiColumn, Matrix.sum_apply]

/-- Complex phases and zero coefficients are retained literally. The witness is
an actual normalized Kraus channel in the prescribed Choi-convex free set. -/
theorem free_mixture_dominator (S : Set (MatrixMap a b))
    (hS : Convex ℝ (MatrixMap.choi '' S))
    (c : ι → ℂ) (h : ι → ℝ) (K : ι → Matrix (Fin b) (Fin a) ℂ)
    (M : ι → KrausChannel a b) {p : ℝ} (hp : 0 < p)
    (hh : ∀ i, 0 < h i) (hH : 0 < coefficientMass c h)
    (hM : ∀ i, (M i).toLinearMap ∈ S)
    (hdom : ∀ i, MatrixMap.CPLe
      (((p/(h i)^2 : ℝ):ℂ) • BranchExtraction.adMap (K i)) (M i).toLinearMap) :
    ∃ N : KrausChannel a b, N.toLinearMap ∈ S ∧
      MatrixMap.CPLe (((p/(coefficientMass c h)^2 : ℝ):ℂ) •
        BranchExtraction.adMap (∑ i, c i • K i)) N.toLinearMap := by
  let w := mixtureWeight c h
  have hw : ∀ i, 0 ≤ w i := mixtureWeight_nonneg c h hh hH
  have hsum : ∑ i, w i = 1 := sum_mixtureWeight c h hH
  obtain ⟨N,hN⟩ := (isChannel_iff_kraus _).1 (finite_mixture_isChannel M w hw hsum)
  refine ⟨N, ?_, ?_⟩
  · rw [hN]
    exact convex_finite_mixture_mem S hS (fun i => (M i).toLinearMap) hM w hw hsum
  · rw [MatrixMap.cpLe_iff_choi_difference, hN, choi_real_sum,
      MatrixMap.choi_smul, choi_adMap, choiColumn_sum]
    have hd (i : ι) : (MatrixMap.choi (M i).toLinearMap -
        (p/(h i)^2) • (choiColumn (K i)*(choiColumn (K i))ᴴ)).PosSemidef := by
      have H := (MatrixMap.cpLe_iff_choi_difference _ _).1 (hdom i)
      rw [MatrixMap.choi_smul, choi_adMap] at H
      simpa only [Complex.real_smul] using H
    simpa only [Complex.real_smul] using
      mixture_gram_domination c h (fun i => choiColumn (K i))
        (fun i => MatrixMap.choi (M i).toLinearMap) hp.le hh hH hd

end Channels
end GeneralizedChannelStein.WeightedGramMixture
