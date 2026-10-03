import GeneralizedChannelStein.ExpansionBudget
import GeneralizedChannelStein.CloseBranchCompletion

/-! Apply Lemma 28 to the actual corrected finite expansion and its positive budget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.WeightedCorrection
open QuantumChannelStein Matrix LocalExpansion ExpansionBudget FreeMultipliers SiteGrouping
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a d k : ℕ}

def base (a d : ℕ) (t w : ℝ) : ℝ := Real.sqrt (((a*d:ℕ):ℝ)/(t*w))

theorem base_ge_one (ha : 0<a) (hd : 0<d) {t w : ℝ} (ht : 0<t) (ht1 : t≤1)
    (hw : 0<w) (hw1 : w≤1) : 1≤base a d t w := by
  have had : (1:ℝ)≤((a*d:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos ha hd
  have htw : t*w≤1 := by nlinarith
  have hq : 1≤((a*d:ℕ):ℝ)/(t*w) := (le_div_iff₀ (mul_pos ht hw)).mpr (by linarith)
  have hs := Real.sq_sqrt (show 0≤((a*d:ℕ):ℝ)/(t*w) by positivity)
  have hp := Real.sqrt_nonneg (((a*d:ℕ):ℝ)/(t*w))
  unfold base
  nlinarith

theorem weightedCost_eq_paper (E : Expansion (Fin d) k) (ha : 0<a) (hd : 0<d)
    {t w : ℝ} (ht : 0<t) (hw : 0<w) :
    weightedCost E (base a d t w)=∑ i:E.terms, ‖E.coeff i‖*paperCost a d t w (E.sites i).card := by
  simp_rw [← localCost_eq_paperCost ha hd t w ht hw]
  rfl

theorem dominated_correction (F : AlternativeFamily a d) (hF : Admissible F)
    (τ : State a) (hτ : QuantitativeAt F τ) (ω : State d)
    (hωmem : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (ha : 0<a) (hd : 0<d) (hk : 0<k)
    (t w p : ℝ) (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1) (hp : 0<p)
    (htτ : (τ.matrix-t•(1:Operator a)).PosSemidef) (hwω : (ω.matrix-w•(1:Operator d)).PosSemidef)
    (M : KrausChannel (a^k) (d^k)) (hM : M.toLinearMap∈F k)
    (K : Matrix (Fin (d^k)) (Fin (a^k)) ℂ)
    (hdom : MatrixMap.CPLe (Complex.ofReal p•BranchExtraction.adMap K) M.toLinearMap)
    (O : Expansion (Fin d) k) (hO : O.value≠0) :
    ∃ M' : KrausChannel (a^k) (d^k), M'.toLinearMap∈F k ∧
      MatrixMap.CPLe (BranchExtraction.adMap (flatten O.value*K))
        (Complex.ofReal ((max 1 (weightedCost O (base a d t w)))^2/p)•M'.toLinearMap) := by
  have hb := base_ge_one ha hd ht ht1 hw hw1
  have hH := weightedCost_pos O hb hO
  have hP := hH
  rw [weightedCost_eq_paper O ha hd ht hw] at hP
  obtain ⟨M',hM',hD⟩ := multiplier_of_expansion F hF τ hτ ω hωmem ha hd hk t w p ht hw hp
    htτ hwω M hM K hdom O hP
  rw [← weightedCost_eq_paper O ha hd ht hw] at hD
  have hD' := CloseBranchCompletion.cpLe_divide (div_pos hp (sq_pos_of_pos hH)) hD
  simp only [inv_div] at hD'
  refine ⟨M',hM',FreeAmplification.cpLe_scalar_mono _ M' ?_ hD'⟩
  apply div_le_div_of_nonneg_right _ hp.le
  have hmax := le_max_right (1:ℝ) (weightedCost O (base a d t w))
  nlinarith

end GeneralizedChannelStein.WeightedCorrection
