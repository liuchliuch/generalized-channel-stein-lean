import QuantumInfo.Entropy.Relative

/-!
# A. Faithful kernel-filled alternatives

Replace zero eigenvalues of an alternative density matrix by one, then
normalize. Its logarithm changes only by the normalization scalar. This is
an exact, dimension-preserving route from a supported singular alternative
to a faithful alternative; no relative-entropy continuity assertion is used.
-/


noncomputable section
open ComplexOrder
open scoped RealInnerProductSpace InnerProductSpace HermitianMat

namespace StateSteinAudit

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The alternative matrix with its zero eigenvalues filled by one. -/
def fillKernel (sigma : MState d) : HermitianMat d ℂ :=
  sigma.M.cfc (fun x : ℝ => if x = 0 then 1 else x)

lemma fillKernel_posDef (sigma : MState d) : (fillKernel sigma).mat.PosDef := by
  change (sigma.M.cfc (fun x : ℝ => if x = 0 then 1 else x)).mat.PosDef
  rw [HermitianMat.cfc_posDef]
  intro i
  have hi := HermitianMat.eigenvalues_nonneg sigma.nonneg i
  split_ifs with hz
  · norm_num
  · exact lt_of_le_of_ne hi (Ne.symm hz)

lemma le_fillKernel (sigma : MState d) : sigma.M ≤ fillKernel sigma := by
  apply sub_nonneg.mp
  have hid : fillKernel sigma - sigma.M =
      sigma.M.cfc (fun x : ℝ => (if x = 0 then 1 else x) - x) := by
    rw [HermitianMat.cfc_sub_apply, HermitianMat.cfc_id']
    rfl
  rw [hid]
  apply (HermitianMat.cfc_nonneg_iff _ _).mpr
  intro i
  split_ifs <;> simp_all

lemma fillKernel_log (sigma : MState d) : (fillKernel sigma).log = sigma.M.log := by
  unfold fillKernel HermitianMat.log
  rw [← HermitianMat.cfc_comp_apply]
  apply HermitianMat.cfc_congr
  intro x _
  by_cases hx : x = 0 <;> simp [hx]

/-- The positive normalization constant of the kernel-filled alternative. -/
def fillingConstant (sigma : MState d) : ℝ := (fillKernel sigma).trace

lemma one_le_fillingConstant (sigma : MState d) : 1 ≤ fillingConstant sigma := by
  have h := HermitianMat.trace_nonneg (sub_nonneg.mpr (le_fillKernel sigma))
  rw [HermitianMat.trace_sub, sigma.tr] at h
  exact sub_nonneg.mp h

lemma fillingConstant_pos (sigma : MState d) : 0 < fillingConstant sigma :=
  zero_lt_one.trans_le (one_le_fillingConstant sigma)

/-- The normalized faithful alternative on the original coordinate space. -/
def faithfulFill (sigma : MState d) : MState d where
  M := (fillingConstant sigma)⁻¹ • fillKernel sigma
  nonneg := by
    apply HermitianMat.zero_le_iff.mpr
    exact ((fillKernel_posDef sigma).smul (inv_pos.mpr (fillingConstant_pos sigma))).posSemidef
  tr := by
    rw [HermitianMat.trace_smul]
    exact inv_mul_cancel₀ (fillingConstant_pos sigma).ne'

lemma faithfulFill_posDef (sigma : MState d) : (faithfulFill sigma).m.PosDef :=
  (fillKernel_posDef sigma).smul (inv_pos.mpr (fillingConstant_pos sigma))

lemma domination_by_faithfulFill (sigma : MState d) :
    sigma.M ≤ fillingConstant sigma • (faithfulFill sigma).M := by
  change sigma.M ≤ fillingConstant sigma • ((fillingConstant sigma)⁻¹ • fillKernel sigma)
  rw [smul_smul, mul_inv_cancel₀ (fillingConstant_pos sigma).ne', one_smul]
  exact le_fillKernel sigma

lemma faithfulFill_log (sigma : MState d) :
    (faithfulFill sigma).M.log = -(Real.log (fillingConstant sigma)) • 1 + sigma.M.log := by
  let _ : (fillKernel sigma).NonSingular := HermitianMat.nonSingular_of_posDef (fillKernel_posDef sigma)
  change ((fillingConstant sigma)⁻¹ • fillKernel sigma).log = _
  rw [HermitianMat.log_smul (inv_ne_zero (fillingConstant_pos sigma).ne'), Real.log_inv, fillKernel_log]

lemma faithfulFill_trace_entropy_shift (rho sigma : MState d) :
    ⟪rho.M, rho.M.log - (faithfulFill sigma).M.log⟫ =
      ⟪rho.M, rho.M.log - sigma.M.log⟫ + Real.log (fillingConstant sigma) := by
  rw [faithfulFill_log]
  simp only [HermitianMat.inner_sub_left, HermitianMat.inner_add_right,
    HermitianMat.inner_smul_right, HermitianMat.inner_one, rho.tr]
  ring

/-- Exact natural-log entropy shift under kernel filling, under the genuine
support condition on the original alternative. -/
theorem qRelativeEnt_faithfulFill_shift (rho sigma : MState d)
    (hsupport : sigma.M.ker ≤ rho.M.ker) :
    (qRelativeEnt rho (faithfulFill sigma)).toEReal =
      (qRelativeEnt rho sigma).toEReal + (Real.log (fillingConstant sigma) : EReal) := by
  let _ : (faithfulFill sigma).M.NonSingular :=
    HermitianMat.nonSingular_of_posDef (faithfulFill_posDef sigma)
  rw [qRelativeEnt_rank, qRelativeEnt_ker hsupport,
    faithfulFill_trace_entropy_shift, EReal.coe_add]

end StateSteinAudit
