/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0; see LICENSE at the repository root.
Adapted from Physlib commit f6e446ca99fd83b3a60743a61900cb2acb98f531,
QuantumInfo/ForMathlib/Isometry.lean, the shared-eigenbasis proof only.
All new declarations have the _qcs suffix to avoid upstream collisions.
-/
import QuantumChannelStein.SpectralDecompositionCFC
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.IsDiag

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
open Matrix
variable {d d₂ d₃ R : Type*}
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]
variable [CommRing R] [StarRing R]
variable {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix d d 𝕜}

theorem Matrix.commute_euclideanLin_qcs (hAB : Commute A B) :
    Commute A.toEuclideanLin B.toEuclideanLin := by
  rw [commute_iff_eq] at hAB ⊢
  ext v i
  convert congr(($hAB).mulVec (WithLp.ofLp v) i) using 0
  simp only [Module.End.mul_apply, ← Matrix.mulVec_mulVec];
  simp only [ofLp_toLpLin, toLin'_apply, mulVec_mulVec]

section commute_module
open Module.End

--TODO: All of these have Pi versions (instead of the "just two" operators versions below),
--  see the tail end of `JointEigenspace.lean` to see how it should generalize. This would
--  also give a Pi version for Matrix. That would be useful for e.g. we have a large number
--  of projectors that all pairwise commute, and we want to simultaneously diagonalize all
--  of them.

/-- Similar to `LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace`, but here the direct sum
is indexed by only the pairs of eigenvalues, as opposed to all pairs of `𝕜` values, giving a finite
decomposition. -/
theorem LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace'_qcs {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {A B : E →ₗ[𝕜] E}
  (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun (μ₁₂ : Eigenvalues A × Eigenvalues B) ↦
      ↥(eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2)) fun μ₁₂ ↦
    (eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2).subtypeₗᵢ := by
  have h := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB
  simp only [OrthogonalFamily, Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply,
    Subtype.forall, Submodule.mem_inf, mem_genEigenspace_one, and_imp] at h ⊢
  intro i j hij a ha hb a' ha' hb'
  contrapose! h
  simp only [Pairwise, ne_eq, Prod.forall, Prod.mk.injEq, not_and, not_forall]
  refine ⟨_, _, _, _, ?_, a, ha, hb, a', ha', hb', h⟩
  intro h' h''
  exact hij (Prod.ext (Subtype.ext h'') (Subtype.ext h'))

/-- Variant of `iSup_mono'` that allows for an easier handling of bottom elements. -/
theorem iSup_mono_bot_qcs {α : Type*} {ι ι' : Sort*} [CompleteLattice α]
  {f : ι → α} {g : ι' → α} (h : ∀ (i : ι), f i = ⊥ ∨ ∃ i', f i ≤ g i') :
    iSup f ≤ iSup g := by
  rcases isEmpty_or_nonempty ι'
  · simp only [IsEmpty.exists_iff, or_false] at h
    simp [h]
  · refine iSup_mono' (fun i ↦ ?_)
    rcases h i with h | h <;> simp [h]

@[reducible]
noncomputable def Commute.isSymmetric_directSumDecomposition_qcs  {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {A B : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E]
  (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    DirectSum.Decomposition fun (μ₁₂ : Eigenvalues A × Eigenvalues B) ↦
      (eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2) := by
  apply (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace'_qcs hA hB).decomposition
  have h := LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
    hA hB hAB
  rw [iSup_prod'] at h
  apply le_antisymm le_top
  rw [← h, iSup_le_iff]
  rintro ⟨fst, snd⟩
  by_cases h₁ : Module.End.HasEigenvalue A fst
  · by_cases h₂ : Module.End.HasEigenvalue B snd
    · exact le_iSup_of_le ⟨⟨fst, h₁⟩, ⟨snd, h₂⟩⟩ le_rfl
    · replace h₂ : eigenspace B snd = ⊥ := by simpa [Module.End.HasUnifEigenvalue] using h₂
      simp [h₂]
  · replace h₁ : eigenspace A fst = ⊥ := by simpa [Module.End.HasUnifEigenvalue] using h₁
    simp [h₁]

set_option backward.isDefEq.respectTransparency false in
/-- Similar to `LinearMap.IsSymmetric.directSum_isInternal_of_commute`, but here the direct sum
is indexed by only the pairs of eigenvalues, as opposed to all pairs of `𝕜` values, giving a finite
decomposition. -/
theorem LinearMap.IsSymmetric.directSum_isInternal_of_commute'_qcs {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {A B : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E]
  (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    DirectSum.IsInternal fun (μ₁₂ : Eigenvalues A × Eigenvalues B) ↦
      eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2 := by
  classical
  have h := LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  constructor
  · intro x y hxy
    -- Since the subspaces are orthogonal, the only way their sum can be zero is if each component is zero. Hence, x - y = 0, which implies x = y.
    rw [← sub_eq_zero]
    suffices h_diff_zero : ∀ (x : DirectSum (Eigenvalues A × Eigenvalues B) fun μ₁₂ ↦ ↥(eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2)), x.coeAddMonoidHom _ = 0 → x = 0 from
      h_diff_zero (x - y) (by simp [hxy])
    clear x y hxy; intro x hx;
    ext μ₁₂
    simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero]
    rw [← inner_self_eq_zero (𝕜 := 𝕜)]
    have h_inner_zero : inner 𝕜 (x μ₁₂ : E) (x.coeAddMonoidHom _) = 0 := by
      simp [hx]
    rw [← h_inner_zero]
    simp only [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, ZeroMemClass.coe_zero, implies_true,
      DFinsupp.sum_eq_sum_fintype, DFinsupp.equivFunOnFintype_apply]
    -- Since the decomposition is orthogonal, the inner product of x μ₁₂ with any other component is zero. Therefore, the sum simplifies to just the inner product of x μ₁₂ with itself.
    rw [inner_sum, Finset.sum_eq_add_sum_diff_singleton_of_mem (by simp)]
    rw [Finset.sdiff_singleton_eq_erase, left_eq_add]
    apply Finset.sum_eq_zero
    intro μ hμ
    exact orthogonalFamily_eigenspace_inf_eigenspace'_qcs hA hB (Finset.ne_of_mem_erase hμ).symm _ _
  · -- Since the decomposition is orthogonal, the direct sum of the intersections is isomorphic to their sum. Therefore, the isomorphism implies that the sum is equal to E.
    have h_sum : ⨆ (μ₁₂ : Eigenvalues A × Eigenvalues B), eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2 = ⊤ := by
      rw [eq_top_iff]
      intro x hx
      obtain ⟨y, rfl⟩ := h.2 x
      rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
      refine Submodule.sum_mem _ fun i hi ↦ ?_
      have hyi := Submodule.coe_mem (y i)
      simp only [Submodule.mem_inf, mem_genEigenspace_one] at hyi
      refine Submodule.mem_iSup_of_mem ⟨⟨i.2, ?_⟩, ⟨i.1, ?_⟩⟩ (by simp)
      <;> simp only [HasUnifEigenvalue, ne_eq, Submodule.eq_bot_iff, mem_genEigenspace_one, not_forall]
      <;> refine ⟨y i, by tauto, by simpa using hi⟩
    intro x
    rw [Submodule.eq_top_iff'] at h_sum
    specialize h_sum x
    rw [Submodule.mem_iSup_iff_exists_finsupp] at h_sum
    rcases h_sum with ⟨f, hf₁, hf₂⟩
    exact ⟨∑ i ∈ f.support, .of _ i ⟨f i, hf₁ i⟩, by simp_all; exact hf₂⟩

noncomputable def LinearMap.sharedEigenbasis_qcs {A B : EuclideanSpace 𝕜 d →ₗ[𝕜] EuclideanSpace 𝕜 d}
  (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    OrthonormalBasis d 𝕜 (EuclideanSpace 𝕜 d) :=
  ((hA.directSum_isInternal_of_commute'_qcs hB hAB).subordinateOrthonormalBasis rfl
    (hA.orthogonalFamily_eigenspace_inf_eigenspace'_qcs hB)).reindex
    (Fintype.equivOfCardEq (by simp))

noncomputable def LinearMap.sharedEigenvaluesA_qcs {A B : EuclideanSpace 𝕜 d →ₗ[𝕜] EuclideanSpace 𝕜 d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) : d → ℝ :=
  fun i => RCLike.re (inner 𝕜 (LinearMap.sharedEigenbasis_qcs hA hB hAB i) (A (LinearMap.sharedEigenbasis_qcs hA hB hAB i)))

noncomputable def LinearMap.sharedEigenvaluesB_qcs {A B : EuclideanSpace 𝕜 d →ₗ[𝕜] EuclideanSpace 𝕜 d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) : d → ℝ :=
  fun i => RCLike.re (inner 𝕜 (LinearMap.sharedEigenbasis_qcs hA hB hAB i) (B (LinearMap.sharedEigenbasis_qcs hA hB hAB i)))

omit [DecidableEq d] in
theorem LinearMap.mem_eigenspace_inf_of_sharedEigenbasis_qcs {A B : EuclideanSpace 𝕜 d →ₗ[𝕜] EuclideanSpace 𝕜 d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) (i : d) :
    ∃ (μ : Module.End.Eigenvalues A) (ν : Module.End.Eigenvalues B),
      LinearMap.sharedEigenbasis_qcs hA hB hAB i ∈ Module.End.eigenspace A μ ⊓ Module.End.eigenspace B ν := by
  rw [LinearMap.sharedEigenbasis_qcs]
  rw [OrthonormalBasis.reindex_apply]
  let hV := hA.directSum_isInternal_of_commute'_qcs hB hAB
  let hV' := hA.orthogonalFamily_eigenspace_inf_eigenspace'_qcs hB
  let hn : Module.finrank 𝕜 (EuclideanSpace 𝕜 d) = Module.finrank 𝕜 (EuclideanSpace 𝕜 d) := rfl
  let e := Fintype.equivOfCardEq (show Fintype.card (Fin (Module.finrank 𝕜 (EuclideanSpace 𝕜 d))) = Fintype.card d by simp)
  let j := e.symm i
  let idx := hV.subordinateOrthonormalBasisIndex hn j hV'
  exists idx.1, idx.2
  exact hV.subordinateOrthonormalBasis_subordinate hn j hV'

omit [DecidableEq d] in
theorem LinearMap.apply_A_sharedEigenbasis_qcs {A B : EuclideanSpace 𝕜 d →ₗ[𝕜] EuclideanSpace 𝕜 d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) (i : d) :
    A (sharedEigenbasis_qcs hA hB hAB i) = (sharedEigenvaluesA_qcs hA hB hAB i : 𝕜) • (sharedEigenbasis_qcs hA hB hAB i) := by
  obtain ⟨μ, ν, h⟩ := mem_eigenspace_inf_of_sharedEigenbasis_qcs hA hB hAB i
  have h₂ := Module.End.mem_eigenspace_iff.mp h.1
  rw [h₂]
  congr; symm
  simp only [sharedEigenvaluesA_qcs, h₂, inner_smul_right, OrthonormalBasis.inner_eq_one,
    mul_one, ← RCLike.conj_eq_iff_re, ← RCLike.star_def]
  have h₃ : (sharedEigenbasis_qcs hA hB hAB) i ≠ 0 := by
    have := (sharedEigenbasis_qcs hA hB hAB).orthonormal.1 i
    exact fun h => by simp [h] at this
  simpa [inner_smul_left, inner_smul_right, h₂, h₃] using
    hA ((sharedEigenbasis_qcs hA hB hAB) i) ((sharedEigenbasis_qcs hA hB hAB) i)

omit [DecidableEq d] in
theorem LinearMap.apply_B_sharedEigenbasis_qcs {A B : EuclideanSpace 𝕜 d →ₗ[𝕜] EuclideanSpace 𝕜 d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) (i : d) :
    B (sharedEigenbasis_qcs hA hB hAB i) = (sharedEigenvaluesB_qcs hA hB hAB i : 𝕜) • (sharedEigenbasis_qcs hA hB hAB i) := by
  obtain ⟨μ, ν, h⟩ := mem_eigenspace_inf_of_sharedEigenbasis_qcs hA hB hAB i
  have h₂ := Module.End.mem_eigenspace_iff.mp h.2
  rw [h₂]
  congr; symm
  simp only [sharedEigenvaluesB_qcs, h₂, inner_smul_right, OrthonormalBasis.inner_eq_one,
    mul_one, ← RCLike.conj_eq_iff_re, ← RCLike.star_def]
  have h₃ : (sharedEigenbasis_qcs hA hB hAB) i ≠ 0 := by
    have := (sharedEigenbasis_qcs hA hB hAB).orthonormal.1 i
    exact fun h => by simp [h] at this
  simpa [inner_smul_left, inner_smul_right, h₂, h₃] using
    hB ((sharedEigenbasis_qcs hA hB hAB) i) ((sharedEigenbasis_qcs hA hB hAB) i)

noncomputable def Matrix.sharedEigenbasis_qcs
  (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    OrthonormalBasis d 𝕜 (EuclideanSpace 𝕜 d) :=
  LinearMap.sharedEigenbasis_qcs (isHermitian_iff_isSymmetric.mp hA)
    (isHermitian_iff_isSymmetric.mp hB) (commute_euclideanLin_qcs hAB)

noncomputable def Matrix.sharedEigenvectorUnitary_qcs (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : Commute A B) : Matrix.unitaryGroup d 𝕜 :=
  ⟨(EuclideanSpace.basisFun d 𝕜).toBasis.toMatrix (sharedEigenbasis_qcs hA hB hAB).toBasis,
    (EuclideanSpace.basisFun d 𝕜).toMatrix_orthonormalBasis_mem_unitary (sharedEigenbasis_qcs hA hB hAB)⟩

namespace Matrix.SharedEigenbasisQCS

variable (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B)

/-- Analogous to `Matrix.IsHermitian.eigenvectorUnitary_mulVec` for the shared basis. -/
theorem sharedEigenvectorUnitary_mulVec_qcs (j : d) : (sharedEigenvectorUnitary_qcs hA hB hAB) *ᵥ
    Pi.single j 1 = WithLp.ofLp (sharedEigenbasis_qcs hA hB hAB j) := by
  simp_all only [mulVec_single, MulOpposite.op_one, one_smul]
  rfl

noncomputable def sharedEigenvalueA_qcs (j : d) : ℝ :=
  LinearMap.sharedEigenvaluesA_qcs
    (isHermitian_iff_isSymmetric.mp hA)
    (isHermitian_iff_isSymmetric.mp hB)
    (commute_euclideanLin_qcs hAB) j

noncomputable def sharedEigenvalueB_qcs (j : d) : ℝ :=
  LinearMap.sharedEigenvaluesB_qcs
    (isHermitian_iff_isSymmetric.mp hA)
    (isHermitian_iff_isSymmetric.mp hB)
    (commute_euclideanLin_qcs hAB) j

/-- Analogous to `Matrix.IsHermitian.mulVec_eigenvectorBasis` for the shared basis. -/
theorem mulVec_sharedEigenbasisA_qcs (j : d) :
    A *ᵥ (sharedEigenbasis_qcs hA hB hAB j) =
    (sharedEigenvalueA_qcs hA hB hAB) j • WithLp.ofLp (sharedEigenbasis_qcs hA hB hAB j) := by
  rw [isHermitian_iff_isSymmetric] at hA hB
  have h := LinearMap.apply_A_sharedEigenbasis_qcs hA hB (Matrix.commute_euclideanLin_qcs hAB) j
  simp only [algebraMap_smul] at h
  have := congr_arg WithLp.ofLp h
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply] at this
  exact this

theorem mulVec_sharedEigenbasisB_qcs (j : d) :
    B *ᵥ (sharedEigenbasis_qcs hA hB hAB j) =
    (sharedEigenvalueB_qcs hA hB hAB) j • WithLp.ofLp (sharedEigenbasis_qcs hA hB hAB j) := by
  rw [isHermitian_iff_isSymmetric] at hA hB
  have h := LinearMap.apply_B_sharedEigenbasis_qcs hA hB (Matrix.commute_euclideanLin_qcs hAB) j
  simp only [algebraMap_smul] at h
  have := congr_arg WithLp.ofLp h
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply] at this
  exact this

/-
PROVIDED SOLUTION
This is exactly analogous to star_shared_mul_B_mul_IsDiag_qcs (which is proved below in this file), but for A instead of B. Use the same proof structure: rw isDiag_iff_diagonal_diag, apply toEuclideanLin.injective, ext with basis, simp, then use mulVec_sharedEigenbasisA_qcs (instead of mulVec_sharedEigenbasisB_qcs), sharedEigenvectorUnitary_mulVec_qcs, h_simp2 (orthogonality/unit property), and by_cases on index equality, simplifying with simp +decide. Reference the B version's proof approach for the exact tactic sequence.
-/
set_option maxHeartbeats 0 in

theorem star_shared_mul_A_mul_IsDiag_qcs : IsDiag
    ((star (sharedEigenvectorUnitary_qcs hA hB hAB : Matrix d d 𝕜)) * A *
      (sharedEigenvectorUnitary_qcs hA hB hAB : Matrix d d 𝕜)) := by
  intro i j hij;
  have := @mulVec_sharedEigenbasisA_qcs d;
  specialize this hA hB hAB j;
  replace this := congr_arg ( fun x => star ( ( sharedEigenbasis_qcs hA hB hAB i ).ofLp ) ⬝ᵥ x ) this
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, mulVec, Finset.mul_sum, mul_comm,
    mul_assoc, Pi.smul_apply, Algebra.smul_mul_assoc] at this
  simp only [mul_assoc]
  convert this using 1;
  · simp [ Matrix.mul_apply, mul_assoc, mul_comm, Finset.sum_mul ]
    congr! 3;
  · have := ( sharedEigenbasis_qcs hA hB hAB ).orthonormal;
    rw [ orthonormal_iff_ite ] at this;
    simp only [inner, ← starRingEnd_apply] at this
    rw [ ← Finset.smul_sum, this i j, if_neg hij, smul_zero ]

/-- Analogous to `Matrix.IsHermitian.star_mul_self_mul_eq_diagonal` for the shared basis. -/
theorem star_shared_mul_B_mul_IsDiag_qcs : IsDiag
    ((star (sharedEigenvectorUnitary_qcs hA hB hAB : Matrix d d 𝕜)) * B *
      (sharedEigenvectorUnitary_qcs hA hB hAB : Matrix d d 𝕜)) := by
  intro i j hij;
  have := @mulVec_sharedEigenbasisB_qcs d;
  specialize this hA hB hAB j;
  replace this := congr_arg ( fun x => star ( ( sharedEigenbasis_qcs hA hB hAB i ).ofLp ) ⬝ᵥ x ) this
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, mulVec, Finset.mul_sum, mul_comm,
    mul_assoc, Pi.smul_apply, Algebra.smul_mul_assoc] at this
  simp only [mul_assoc]
  convert this using 1;
  · simp [ Matrix.mul_apply, mul_assoc, mul_comm, Finset.sum_mul ]
    congr! 3;
  · have := ( sharedEigenbasis_qcs hA hB hAB ).orthonormal;
    rw [ orthonormal_iff_ite ] at this;
    simp only [inner, ← starRingEnd_apply] at this
    rw [ ← Finset.smul_sum, this i j, if_neg hij, smul_zero ]

end Matrix.SharedEigenbasisQCS

end commute_module

theorem Commute.exists_unitary_qcs (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ U : Matrix.unitaryGroup d 𝕜, (U.val * A * Uᴴ).IsDiag ∧ (U.val * B * Uᴴ).IsDiag := by
  use (Matrix.sharedEigenvectorUnitary_qcs hA hB hAB)⁻¹
  constructor
  · convert Matrix.SharedEigenbasisQCS.star_shared_mul_A_mul_IsDiag_qcs hA hB hAB
    simp [Matrix.star_eq_conjTranspose]
  · convert Matrix.SharedEigenbasisQCS.star_shared_mul_B_mul_IsDiag_qcs hA hB hAB
    simp [Matrix.star_eq_conjTranspose]

