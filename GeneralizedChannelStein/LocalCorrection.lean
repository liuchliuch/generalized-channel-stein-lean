import GeneralizedChannelStein.ExpansionBudget
import GeneralizedChannelStein.CompletionPrecision

/-! Local correction from the actual weighted retained overlap. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.LocalCorrection
open QuantumChannelStein Matrix LocalExpansion SiteGrouping CorrectedBranch CompletionPrecision
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a d k : ℕ}

theorem construct (ha : 0<a) (hd : 0<d) (hk : 2≤k)
    (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (K : Matrix (Fin (d^k)) (Fin (a^k)) ℂ) (hK : ‖K‖≤1)
    (c δ : ℝ) (hc : 0<c) (hc1 : c≤1) (hδ : 0<δ) (hδ1 : δ≤1/16)
    (hcover : (BranchExtraction.realPart ((powerIsometry J k)ᴴ*K)-c•1).PosSemidef)
    (E : Expansion (Fin a) k) (hE : ‖flatten E.value-(powerIsometry J k)ᴴ*K‖≤kappa c*δ) :
    ∃ O : Expansion (Fin d) k,
      O.HasSize (CompletionScalars.correctionDegree (q1 c) (kappa c*δ)*ExpansionBudget.radius E+
        ImageProjectorScalars.filterDegree k (kappa c*δ)) ∧
      O.cost≤CompletionScalars.correctionCost (lam c) E.cost (CompletionScalars.correctionDegree (q1 c) (kappa c*δ))*
        15^(ImageProjectorScalars.filterDegree k (kappa c*δ)) ∧
      ‖flatten O.value*K-powerIsometry J k‖≤(2*Mc c+1)*(kappa c*δ) := by
  letI : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let ξ := kappa c*δ
  let L := CompletionScalars.correctionDegree (q1 c) ξ
  let X := (powerIsometry J k)ᴴ*K
  have hparam := fixed_precision_bounds hc hc1
  obtain ⟨hξ,hξ1,hζ⟩ := scaled_precision_bounds hc hc1 hδ hδ1
  have hq : 0<q1 c := hparam.q0_nonneg.trans_lt hparam.q0_lt_q1
  have hJn : ‖powerIsometry J k‖≤1 := BranchExtraction.norm_isometry_le_one _ (powerIsometry_isometry J hJ k)
  have hX : ‖X‖≤1 := (Matrix.l2_opNorm_mul _ _).trans (by
    rw [Matrix.l2_opNorm_conjTranspose]
    nlinarith [norm_nonneg K,norm_nonneg (powerIsometry J k)])
  have hq0 : ‖1-lam c•X‖≤q0 c := PositiveOverlap.geometric_contraction X hX c hc hc1 hcover
  have hbase : ‖1-lam c•E.value‖≤q1 c := by
    have heq : flatten (1-lam c•E.value)=1-lam c•flatten E.value := by
      rw [show flatten (1-lam c•E.value)=flatten (1:Block (Fin a) k)-lam c•flatten E.value from rfl,flatten_one]
    rw [← norm_flatten (1-lam c•E.value),heq]
    have hid : (1:Operator (a^k))-lam c•flatten E.value=(1-lam c•X)+lam c•(X-flatten E.value) := by module
    rw [hid]
    have he' : ‖X-flatten E.value‖≤ξ := by rw [norm_sub_rev]; exact hE
    calc
      _ ≤ ‖1-lam c•X‖+‖lam c•(X-flatten E.value)‖ := norm_add_le _ _
      _ ≤ q0 c+lam c*ξ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hparam.lam_pos]
        exact add_le_add hq0 (mul_le_mul_of_nonneg_left he' hparam.lam_pos.le)
      _ ≤ q1 c := by
        have hx : ξ≤kappa c := by dsimp [ξ]; nlinarith [hparam.kappa_pos]
        nlinarith [hparam.gap_bound,mul_le_mul_of_nonneg_left hx hparam.lam_pos.le]
  let G := CorrectionPolynomial.correction E (lam c) L
  have hGn : ‖G.value‖≤Mc c := CorrectionPolynomial.correction_norm E (lam c) (q1 c)
    hparam.lam_pos.le hq.le hparam.q1_lt_one hbase L
  let Xs : Block (Fin a) k := Matrix.reindex (encode a k).symm (encode a k).symm X
  have hXs : flatten Xs=X := by ext i j; simp [Xs,flatten,Matrix.reindex_apply]
  have hEx : ‖Xs-E.value‖≤ξ := by
    rw [← norm_flatten (Xs-E.value),flatten_sub,hXs,norm_sub_rev]
    exact hE
  have hGerr := CorrectionPolynomial.correction_error E Xs (lam c) (q1 c) ξ hparam.lam_pos.le
    hq.le hparam.q1_lt_one hbase hEx L (CompletionScalars.correctionDegree_bounds hq hparam.q1_lt_one hξ hξ1).1
  have hGerr' : ‖flatten G.value*X-1‖≤(Mc c+1)*ξ := by
    have hnrm := norm_flatten (G.value*Xs-1)
    rw [flatten_sub,flatten_mul,hXs,flatten_one] at hnrm
    exact hnrm.trans_le hGerr
  have hPP : (J*Jᴴ)*(J*Jᴴ)=J*Jᴴ := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc Jᴴ J Jᴴ,hJ,Matrix.one_mul]
  obtain ⟨H,hHn,hHerr,hHs,hHc⟩ := ImageProjector.product_projector_approximation
    (Matrix.posSemidef_self_mul_conjTranspose J).isHermitian hPP hk hξ hξ1
  let O := operator J hJ ⟨0,ha⟩ G H
  refine ⟨O,?_,?_,?_⟩
  · exact operator_size J hJ ⟨0,ha⟩ G H
      (CorrectionPolynomial.correction_size E (ExpansionBudget.hasSize_radius E) (lam c) L)
      (hHs.mono (min_le_right _ _))
  · rw [operator_cost]
    exact mul_le_mul (CorrectionPolynomial.correction_cost E (lam c) hparam.lam_pos.le L) hHc
      H.cost_nonneg (by have hlam := hparam.lam_pos; have hEc := E.cost_nonneg; unfold CompletionScalars.correctionCost; positivity)
  · exact operator_error J hJ ⟨0,ha⟩ K hK G H (Mc c) ξ hparam.Mc_pos.le hξ.le hGn hHerr hGerr'

end GeneralizedChannelStein.LocalCorrection
