import GeneralizedChannelStein.CanonicalInput
import QuantumInfo.Entropy.DPI

/-! Support-aware convexity foundations for the entropy minimax argument. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.EntropyMinimax
open QuantumChannelStein RelativeEntropy PhyslibStateBridge Matrix EntropyContinuity
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

theorem support_physlib_iff (ρ σ : State n) :
    supportIncluded ρ σ ↔ (toMState σ).M.ker ≤ (toMState ρ).M.ker := by
  constructor
  · exact support_toMState
  · intro h x hx
    have hx' : WithLp.toLp 2 x∈(toMState σ).M.ker := by
      rw [HermitianMat.mem_ker_iff_mulVec_zero]
      exact hx
    have hy := h hx'
    rw [HermitianMat.mem_ker_iff_mulVec_zero] at hy
    exact hy

/-- The existing actual Umegaki divergence agrees with the Physlib quantity
in every finite and infinite support branch, with the base changed to bits. -/
theorem umegaki_eq_physlib (ρ σ : State n) :
    umegaki ρ σ = (((Real.log 2)⁻¹ : ℝ) : EReal) * (qRelativeEnt (toMState ρ) (toMState σ) : EReal) := by
  by_cases hs : supportIncluded ρ σ
  · have hq := qRelativeEnt_ker ((support_physlib_iff ρ σ).mp hs)
    have hr := congrArg EReal.toReal hq
    simp only [EReal.toReal_coe_ennreal,EReal.toReal_coe] at hr
    rw [umegaki_of_supportIncluded _ _ hs,hq,← EReal.coe_mul]
    congr 1
    have hb := entropy_toReal_base_two ρ σ hs
    rw [hr] at hb
    simpa only [div_eq_mul_inv,mul_comm] using hb.symm
  · have hq := qRelativeEnt_eq_top_iff.mpr ((support_physlib_iff ρ σ).not.mp hs)
    rw [umegaki_of_not_supportIncluded _ _ hs,hq,EReal.coe_ennreal_top,
      EReal.coe_mul_top_of_pos (inv_pos.mpr (Real.log_pos (by norm_num : (1:ℝ)<2)))]

/-- Nonnegative extended codomain used only for importing the already proved
joint convexity; this is equal to the support-aware EReal model. -/
def bitsNN (ρ σ : State n) : ENNReal :=
  ENNReal.ofReal ((Real.log 2)⁻¹) * qRelativeEnt (toMState ρ) (toMState σ)

theorem umegaki_eq_bitsNN (ρ σ : State n) : umegaki ρ σ = (bitsNN ρ σ : EReal) := by
  rw [bitsNN,EReal.coe_ennreal_mul,EReal.coe_ennreal_ofReal,
    max_eq_left (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))]
  exact umegaki_eq_physlib ρ σ

theorem physlib_mix (ρ σ : State n) (p : Prob) :
    toMState (mix ρ σ (p:ℝ) p.property.1 p.property.2) = p [toMState ρ ↔ toMState σ] := by
  apply MState.m_inj
  simp only [Mixable.mix,Mixable.mix_ab,MState.instMixable,Prob.coe_one_minus]
  rfl

/-- Actual joint convexity, including singular and infinite branches. -/
theorem bitsNN_joint_convex (ρ₁ ρ₂ σ₁ σ₂ : State n) (p : Prob) :
    bitsNN (mix ρ₁ ρ₂ (p:ℝ) p.property.1 p.property.2)
      (mix σ₁ σ₂ (p:ℝ) p.property.1 p.property.2) ≤
      (p:ENNReal)*bitsNN ρ₁ σ₁ + (1-(p:ENNReal))*bitsNN ρ₂ σ₂ := by
  unfold bitsNN
  rw [physlib_mix,physlib_mix]
  have h := qRelativeEnt_joint_convexity (toMState ρ₁) (toMState ρ₂) (toMState σ₁) (toMState σ₂) p
  have h' := mul_le_mul_left' h (ENNReal.ofReal ((Real.log 2)⁻¹))
  simpa only [mul_add,mul_left_comm,mul_assoc] using h'

/-- Joint convexity transferred to the actual EReal divergence without
losing any infinite-value cases. -/
theorem umegaki_joint_convex (ρ₁ ρ₂ σ₁ σ₂ : State n) (p : Prob) :
    umegaki (mix ρ₁ ρ₂ (p:ℝ) p.property.1 p.property.2)
      (mix σ₁ σ₂ (p:ℝ) p.property.1 p.property.2) ≤
      ((p:ENNReal):EReal)*umegaki ρ₁ σ₁ + ((1-(p:ENNReal):ENNReal):EReal)*umegaki ρ₂ σ₂ := by
  rw [umegaki_eq_bitsNN,umegaki_eq_bitsNN,umegaki_eq_bitsNN]
  have h := bitsNN_joint_convex ρ₁ ρ₂ σ₁ σ₂ p
  have he : (bitsNN (mix ρ₁ ρ₂ (p:ℝ) p.property.1 p.property.2)
      (mix σ₁ σ₂ (p:ℝ) p.property.1 p.property.2) : EReal) ≤
      (((p:ENNReal)*bitsNN ρ₁ σ₁ + (1-(p:ENNReal))*bitsNN ρ₂ σ₂ : ENNReal):EReal) := by
    exact_mod_cast h
  simpa only [EReal.coe_ennreal_add,EReal.coe_ennreal_mul] using he

variable {m : ℕ}

theorem mix_self (ρ : State n) (p : Prob) : mix ρ ρ (p:ℝ) p.property.1 p.property.2=ρ := by
  apply ChannelEntropy.state_eq_of_matrix_eq
  change (p:ℝ)•ρ.matrix+(1-(p:ℝ))•ρ.matrix=ρ.matrix
  rw [← add_smul]
  simp

/-- Canonical outputs depend affinely on the actual channel linear map. -/
theorem canonical_output_mix (Φ Ψ Ω : KrausChannel n m) (ρ : State n) (p : Prob)
    (hΩ : Ω.toLinearMap=(p:ℂ)•Φ.toLinearMap+(1-(p:ℂ))•Ψ.toLinearMap) :
    CanonicalInput.output Ω ρ = mix (CanonicalInput.output Φ ρ) (CanonicalInput.output Ψ ρ)
      (p:ℝ) p.property.1 p.property.2 := by
  apply ChannelEntropy.state_eq_of_matrix_eq
  ext i j
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  change (ChannelEntropy.pureOutput Ω (CanonicalInput.input ρ)).matrix _ _ = _
  simp only [ChannelEntropy.pureOutput_matrix,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    EntropyContinuity.mix,Matrix.add_apply,Matrix.smul_apply]
  change Ω.amplify n (pureMatrix (CanonicalInput.input ρ).val) (i1,i2) (j1,j2) = _
  rw [KrausChannel.amplify_block]
  have h := congrArg (fun M : MatrixMap n m =>
      M (fun u v => pureMatrix (CanonicalInput.input ρ).val (i1,u) (j1,v)) i2 j2) hΩ
  simpa only [LinearMap.add_apply,LinearMap.smul_apply,Pi.add_apply,Pi.smul_apply,
    CanonicalInput.output,ChannelEntropy.pureOutput_matrix,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_apply_apply,KrausChannel.amplify_block,Complex.real_smul,Complex.ofReal_sub,
    Complex.ofReal_one] using h

/-- The alternative-variable convexity asserted in Lemma32, with actual
channel-map mixing and all extended support branches retained. -/
theorem value_convex_alternative (N Φ Ψ Ω : KrausChannel n m) (ρ : State n) (p : Prob)
    (hΩ : Ω.toLinearMap=(p:ℂ)•Φ.toLinearMap+(1-(p:ℂ))•Ψ.toLinearMap) :
    CanonicalInput.value N Ω ρ ≤
      ((p:ENNReal):EReal)*CanonicalInput.value N Φ ρ +
      ((1-(p:ENNReal):ENNReal):EReal)*CanonicalInput.value N Ψ ρ := by
  have h := umegaki_joint_convex (CanonicalInput.output N ρ) (CanonicalInput.output N ρ)
    (CanonicalInput.output Φ ρ) (CanonicalInput.output Ψ ρ) p
  rw [mix_self,← canonical_output_mix Φ Ψ Ω ρ p hΩ] at h
  exact h

theorem prob_coe_ereal (p : Prob) : ((p:ENNReal):EReal)=((p:ℝ):EReal) := by
  rw [Prob.ofNNReal_toNNReal,EReal.coe_ennreal_ofReal,max_eq_left p.property.1]

theorem prob_complement_coe_ereal (p : Prob) :
    ((1-(p:ENNReal):ENNReal):EReal)=((1-(p:ℝ):ℝ):EReal) := by
  rw [Prob.ofNNReal_toNNReal,← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 p.property.1,
    EReal.coe_ennreal_ofReal,max_eq_left (sub_nonneg.mpr p.property.2)]

theorem value_convex_alternative_real (N Φ Ψ Ω : KrausChannel n m) (ρ : State n)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1)
    (hΩ : Ω.toLinearMap=(p:ℂ)•Φ.toLinearMap+((1-p:ℝ):ℂ)•Ψ.toLinearMap) :
    CanonicalInput.value N Ω ρ ≤ (p:EReal)*CanonicalInput.value N Φ ρ+
      ((1-p:ℝ):EReal)*CanonicalInput.value N Ψ ρ := by
  let q : Prob := ⟨p,hp,hp1⟩
  have h := value_convex_alternative N Φ Ψ Ω ρ q (by simpa [q] using hΩ)
  simpa only [prob_coe_ereal,prob_complement_coe_ereal] using h

end GeneralizedChannelStein.EntropyMinimax
