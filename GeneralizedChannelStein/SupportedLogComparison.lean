import QuantumChannelStein.PhyslibStateBridge
import QuantumChannelStein.TraceNormCoordinates
import QuantumChannelStein.TraceNormBounds
import QuantumChannelStein.TestingSDP
import QuantumChannelStein.SharpChannelWeights
import GeneralizedChannelStein.DimensionDomination

/-! # Uniform logarithmic comparison with singular reference marginals

A common kernel is filled with eigenvalue one. This does not change the
actual totalized spectral logarithm, and makes operator monotonicity
applicable without a limiting or cancellation premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
namespace GeneralizedChannelStein.SupportedLogComparison
open QuantumChannelStein Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fill zero eigenvalues by one, leaving every nonzero eigenvalue unchanged. -/
def fillKernel (A : HermitianMat ι ℂ) : HermitianMat ι ℂ :=
  A.cfc (fun x => if x = 0 then 1 else x)

theorem fillKernel_eq_add (A : HermitianMat ι ℂ) :
    fillKernel A = A + A.kerProj := by
  have hk : A.kerProj = 1 - A.supportProj := eq_sub_of_add_eq A.kerProj_add_supportProj
  rw [hk]
  calc
    fillKernel A = A.cfc (fun x => x + (1 - (if x = 0 then 0 else 1))) := by
      apply HermitianMat.cfc_congr
      intro x hx
      dsimp only
      split_ifs <;> simp_all
    _ = A + (1 - A.supportProj) := by
      rw [HermitianMat.cfc_add_apply, HermitianMat.cfc_sub_apply,
        HermitianMat.cfc_id', HermitianMat.cfc_const, one_smul,
        ← HermitianMat.supportProj_eq_cfc]

theorem fillKernel_posDef (A : HermitianMat ι ℂ) (hA : 0 ≤ A) :
    (fillKernel A).mat.PosDef := by
  apply (HermitianMat.cfc_posDef A _).mpr
  intro i
  have hi := (HermitianMat.zero_le_iff.mp hA).eigenvalues_nonneg i
  split_ifs with h
  · norm_num
  · exact lt_of_le_of_ne hi (Ne.symm h)

@[simp] theorem log_fillKernel (A : HermitianMat ι ℂ) :
    (fillKernel A).log = A.log := by
  simp only [fillKernel, HermitianMat.log, ← HermitianMat.cfc_comp_apply]
  apply HermitianMat.cfc_congr
  intro x hx
  dsimp only
  split_ifs <;> simp_all

theorem ker_eq_of_sandwich (A B : HermitianMat ι ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hlo : c • A ≤ B) (hhi : B ≤ d • A) : A.ker = B.ker := by
  apply le_antisymm
  · exact HermitianMat.ker_le_of_le_smul hd.ne' hB hhi
  · have h := HermitianMat.ker_antitone (smul_nonneg hc.le hA) hlo
    simpa only [HermitianMat.ker_pos_smul A hc.ne'] using h

/-- The same common-kernel completion preserves a multiplicative order sandwich. -/
theorem fillKernel_sandwich (A B : HermitianMat ι ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (c d : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hd : 1 ≤ d)
    (hlo : c • A ≤ B) (hhi : B ≤ d • A) :
    c • fillKernel A ≤ fillKernel B ∧ fillKernel B ≤ d • fillKernel A := by
  have hker := ker_eq_of_sandwich A B hA hB c d hc (lt_of_lt_of_le zero_lt_one hd) hlo hhi
  have hk : B.kerProj = A.kerProj := by simp only [HermitianMat.kerProj, hker]
  have hp : 0 ≤ A.kerProj := HermitianMat.projector_nonneg A.ker
  rw [fillKernel_eq_add, fillKernel_eq_add, hk, smul_add, smul_add]
  constructor
  · exact add_le_add hlo (by simpa using smul_le_smul_of_nonneg_right hc1 hp)
  · exact add_le_add hhi (by simpa using smul_le_smul_of_nonneg_right hd hp)

/-- Uniform full-space log width, including a singular common support. -/
theorem log_sandwich (A B : HermitianMat ι ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (c d : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hd : 1 ≤ d)
    (hlo : c • A ≤ B) (hhi : B ≤ d • A) :
    Real.log c • 1 ≤ B.log - A.log ∧ B.log - A.log ≤ Real.log d • 1 := by
  have hfill := fillKernel_sandwich A B hA hB c d hc hc1 hd hlo hhi
  letI : (fillKernel A).NonSingular := HermitianMat.nonSingular_of_posDef (fillKernel_posDef A hA)
  have hlo' := HermitianMat.log_mono ((fillKernel_posDef A hA).smul hc) hfill.1
  have hhi' := HermitianMat.log_mono (fillKernel_posDef B hB) hfill.2
  rw [HermitianMat.log_smul hc.ne', log_fillKernel, log_fillKernel] at hlo'
  rw [HermitianMat.log_smul (ne_of_gt (lt_of_lt_of_le zero_lt_one hd)),
    log_fillKernel, log_fillKernel] at hhi'
  exact ⟨le_sub_iff_add_le.mpr hlo', sub_le_iff_le_add.mpr (by simpa [add_comm] using hhi')⟩

/-- Centering an actual Hermitian spectral interval gives its sharp operator-radius bound. -/
theorem norm_centered_le (H : HermitianMat ι ℂ) (l u : ℝ) (hlu : l ≤ u)
    (hlo : l • 1 ≤ H) (hhi : H ≤ u • 1) :
    ‖H.mat - ((l+u)/2) • (1 : Matrix ι ι ℂ)‖ ≤ (u-l)/2 := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  have hlo' : 0 ≤ H.cfc (fun x => x-l) := by
    rw [HermitianMat.cfc_sub_apply, HermitianMat.cfc_id', HermitianMat.cfc_const]
    exact sub_nonneg.mpr hlo
  have hhi' : 0 ≤ H.cfc (fun x => u-x) := by
    rw [HermitianMat.cfc_sub_apply, HermitianMat.cfc_id', HermitianMat.cfc_const]
    exact sub_nonneg.mpr hhi
  have h := norm_cfc_le (a := H.mat) (f := fun x : ℝ => x-(l+u)/2)
    (by linarith : 0 ≤ (u-l)/2) (by
      intro x hx
      rw [H.H.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i,rfl⟩ := hx
      have hlow := (HermitianMat.cfc_nonneg_iff H _).mp hlo' i
      have hhigh := (HermitianMat.cfc_nonneg_iff H _).mp hhi' i
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> dsimp only at hlow hhigh ⊢ <;> linarith)
  rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => (l+u)/2) H.mat,
    cfc_id' ℝ H.mat H.H.isSelfAdjoint, cfc_const ((l+u)/2 : ℝ) H.mat H.H.isSelfAdjoint] at h
  simpa only [Algebra.algebraMap_eq_smul_one] using h

/-- A trace-zero matrix pairs with an actual spectral interval by half its width.
This is proved in the full trace norm, not assumed as a state-distance interface. -/
theorem abs_trace_pairing_le_width (H : HermitianMat ι ℂ) (X : Matrix ι ι ℂ)
    (hX : X.trace = 0) (l u : ℝ) (hlu : l ≤ u)
    (hlo : l • 1 ≤ H) (hhi : H ≤ u • 1) :
    |(X * H.mat).trace.re| ≤ TraceNorm.traceNorm X / 2 * (u-l) := by
  have heq : ((H.mat - ((l+u)/2) • (1 : Matrix ι ι ℂ)) * X).trace =
      (X * H.mat).trace := by
    rw [Matrix.trace_mul_comm X H.mat]
    simp [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul, hX]
  calc
    _ = |(((H.mat - ((l+u)/2) • (1 : Matrix ι ι ℂ)) * X).trace).re| :=
      congrArg (fun z : ℂ => |z.re|) heq.symm
    _ ≤ ‖((H.mat - ((l+u)/2) • (1 : Matrix ι ι ℂ)) * X).trace‖ := Complex.abs_re_le_norm _
    _ ≤ ‖H.mat - ((l+u)/2) • (1 : Matrix ι ι ℂ)‖ * TraceNorm.traceNorm X :=
      TraceNorm.norm_trace_mul_le _ _
    _ ≤ ((u-l)/2) * TraceNorm.traceNorm X :=
      mul_le_mul_of_nonneg_right (norm_centered_le H l u hlu hlo hhi)
        (TraceNorm.traceNorm_nonneg X)
    _ = _ := by ring

/-- Exact singular tensor-identity logarithm; the kernel terms vanish, not diverge. -/
theorem log_kronecker_one {r b : ℕ} (μ : HermitianMat (Fin r) ℂ) :
    (μ.kronecker (1 : HermitianMat (Fin b) ℂ)).log.mat =
      μ.log.mat ⊗ₖ (1 : Operator b) := by
  rw [HermitianMat.log_kron_with_proj]
  simp

/-- Equal actual reference marginals cancel every reference-only observable. -/
theorem reference_pairing_cancel {r b : ℕ}
    (ρ ν : Matrix (Fin r × Fin b) (Fin r × Fin b) ℂ)
    (hmarginal : KrausChannel.traceOutput ρ = KrausChannel.traceOutput ν)
    (K : Operator r) : ((ρ-ν) * (K ⊗ₖ (1 : Operator b))).trace = 0 := by
  rw [Matrix.sub_mul, Matrix.trace_sub, TestingSDP.traceOutput_pairing,
    TestingSDP.traceOutput_pairing, hmarginal, sub_self]

/-- Natural-log cross-entropy comparison, uniformly over singular reference states.
No support cutoff, cancellation premise, or continuity limit is supplied by the caller. -/
theorem abs_crossEntropy_sub_le {r b : ℕ}
    (ρ ν : Matrix (Fin r × Fin b) (Fin r × Fin b) ℂ)
    (σ : HermitianMat (Fin r × Fin b) ℂ) (μ : HermitianMat (Fin r) ℂ)
    (hσ : 0 ≤ σ) (hμ : 0 ≤ μ)
    (hmarginal : KrausChannel.traceOutput ρ = KrausChannel.traceOutput ν)
    (c d : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hd : 1 ≤ d)
    (hlo : c • (μ.kronecker (1 : HermitianMat (Fin b) ℂ)) ≤ σ)
    (hhi : σ ≤ d • (μ.kronecker (1 : HermitianMat (Fin b) ℂ))) :
    |((ρ-ν) * σ.log.mat).trace.re| ≤
      TraceNorm.traceNorm (ρ-ν) / 2 * (Real.log d - Real.log c) := by
  let A := μ.kronecker (1 : HermitianMat (Fin b) ℂ)
  have hA : 0 ≤ A := by
    rw [HermitianMat.zero_le_iff]
    exact MatrixMap.posSemidef_kronecker (HermitianMat.zero_le_iff.mp hμ) Matrix.PosSemidef.one
  have hb := log_sandwich A σ hA hσ c d hc hc1 hd hlo hhi
  have hcd : Real.log c ≤ Real.log d := Real.log_le_log hc (hc1.trans hd)
  have ht : (ρ-ν).trace = 0 := by
    rw [Matrix.trace_sub, ← TestingSDP.trace_traceOutput ρ,
      ← TestingSDP.trace_traceOutput ν, hmarginal, sub_self]
  have hcancel : ((ρ-ν) * A.log.mat).trace = 0 := by
    rw [show A.log.mat = μ.log.mat ⊗ₖ (1 : Operator b) from log_kronecker_one μ]
    exact reference_pairing_cancel ρ ν hmarginal μ.log.mat
  have h := abs_trace_pairing_le_width (σ.log-A.log) (ρ-ν) ht
    (Real.log c) (Real.log d) hcd hb.1 hb.2
  simpa only [HermitianMat.mat_sub, Matrix.mul_sub, Matrix.trace_sub,
    hcancel, sub_zero] using h

/-- The uniform cross-entropy difference in the project's flattened state
coordinates and base-two spectral logarithm. The reference density may be singular. -/
theorem abs_state_crossEntropy_sub_le {r b : ℕ}
    (ρ ν σ : State (r*b)) (μ : State r)
    (hmarginal : SharpChannel.marginalLinear r b ρ.matrix =
      SharpChannel.marginalLinear r b ν.matrix)
    (c d : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hd : 1 ≤ d)
    (hlo : (SharpChannel.unflatten (a := r) (b := b) σ.matrix - c • (μ.matrix ⊗ₖ (1 : Operator b))).PosSemidef)
    (hhi : (d • (μ.matrix ⊗ₖ (1 : Operator b)) - SharpChannel.unflatten (a := r) (b := b) σ.matrix).PosSemidef) :
    |((ρ.matrix-ν.matrix) * RelativeEntropy.spectralLog2 σ).trace.re| ≤
      TraceNorm.traceNorm (ρ.matrix-ν.matrix) / 2 * (Real.logb 2 d - Real.logb 2 c) := by
  let S := (PhyslibStateBridge.toMState σ).M.reindex finProdFinEquiv.symm
  let M := (PhyslibStateBridge.toMState μ).M
  have hS : 0 ≤ S := HermitianMat.zero_le_iff.mpr (σ.positive.submatrix finProdFinEquiv)
  have hM : 0 ≤ M := (PhyslibStateBridge.toMState μ).nonneg
  have hl : c • (M.kronecker (1 : HermitianMat (Fin b) ℂ)) ≤ S := by
    exact HermitianMat.le_iff.mpr hlo
  have hu : S ≤ d • (M.kronecker (1 : HermitianMat (Fin b) ℂ)) := by
    exact HermitianMat.le_iff.mpr hhi
  have h := abs_crossEntropy_sub_le (SharpChannel.unflatten (a := r) (b := b) ρ.matrix)
    (SharpChannel.unflatten (a := r) (b := b) ν.matrix) S M hS hM hmarginal c d hc hc1 hd hl hu
  have hlog : S.log.mat = SharpChannel.unflatten (a := r) (b := b) (PhyslibStateBridge.toMState σ).M.log.mat := by
    dsimp only [S]
    rw [HermitianMat.reindex_log, HermitianMat.mat_reindex]
    rfl
  have hnorm : TraceNorm.traceNorm (SharpChannel.unflatten (a := r) (b := b) ρ.matrix - SharpChannel.unflatten (a := r) (b := b) ν.matrix) =
      TraceNorm.traceNorm (ρ.matrix-ν.matrix) :=
    TraceNorm.traceNorm_reindex (finProdFinEquiv.symm : Fin (r*b) ≃ Fin r × Fin b) (ρ.matrix-ν.matrix)
  have htrace : ((SharpChannel.unflatten (a := r) (b := b) ρ.matrix - SharpChannel.unflatten (a := r) (b := b) ν.matrix) *
      SharpChannel.unflatten (a := r) (b := b) (PhyslibStateBridge.toMState σ).M.log.mat).trace =
      ((ρ.matrix-ν.matrix) * (PhyslibStateBridge.toMState σ).M.log.mat).trace := by
    change ((Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv.symm) (ρ.matrix-ν.matrix) *
      (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv.symm) _).trace = _
    rw [← map_mul]
    exact ChannelEntropy.trace_reindex_equiv finProdFinEquiv.symm _
  rw [hlog, hnorm, htrace] at h
  have hnlog : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  have hh := mul_le_mul_of_nonneg_left h hnlog
  rw [PhyslibStateBridge.spectralLog2_eq_scaled_log, Matrix.mul_smul, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul, abs_mul, abs_of_nonneg hnlog]
  convert hh using 1
  simp only [Real.logb]
  ring

/-- The common reference marginal and a strictly positive reference-identity
lower bound force the genuine support inclusion, even for singular μ. -/
theorem supportIncluded_of_reference_lower {r b : ℕ}
    (ρ σ : State (r*b)) (μ : State r)
    (hmarginal : SharpChannel.marginalLinear r b ρ.matrix = μ.matrix)
    (c : ℝ) (hc : 0 < c)
    (hlo : (SharpChannel.unflatten (a := r) (b := b) σ.matrix - c • (μ.matrix ⊗ₖ (1 : Operator b))).PosSemidef) :
    RelativeEntropy.supportIncluded ρ σ := by
  have hd := DimensionDomination.dimension_order (SharpChannel.unflatten (a := r) (b := b) ρ.matrix)
    (ρ.positive.submatrix finProdFinEquiv)
  change ((b : ℝ) • (SharpChannel.marginalLinear r b ρ.matrix ⊗ₖ (1 : Operator b)) -
    SharpChannel.unflatten (a := r) (b := b) ρ.matrix).PosSemidef at hd
  rw [hmarginal] at hd
  have hp := (hlo.smul (div_nonneg (Nat.cast_nonneg b) hc.le)).add hd
  have heq : ((b : ℝ)/c) •
      (SharpChannel.unflatten (a := r) (b := b) σ.matrix - c • (μ.matrix ⊗ₖ (1 : Operator b))) +
      ((b : ℝ) • (μ.matrix ⊗ₖ (1 : Operator b)) - SharpChannel.unflatten (a := r) (b := b) ρ.matrix) =
      ((b : ℝ)/c) • SharpChannel.unflatten (a := r) (b := b) σ.matrix - SharpChannel.unflatten (a := r) (b := b) ρ.matrix := by
    rw [smul_sub, smul_smul, div_mul_cancel₀ _ hc.ne']
    abel
  rw [heq] at hp
  have hf := hp.submatrix finProdFinEquiv.symm
  have hflat : ((((b : ℝ)/c) • σ.matrix) - ρ.matrix).PosSemidef := by
    convert hf using 1
    ext i j
    simp only [SharpChannel.unflatten, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.sub_apply, Matrix.smul_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact SupportDomination.ker_le_of_posSemidef_smul_sub ρ.positive hflat

end GeneralizedChannelStein.SupportedLogComparison
