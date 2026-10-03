import QuantumChannelStein.PermutationHistogram
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-! # Polynomial spectral complexity of permutation-invariant operators
A faithful left-regular representation on the invariant algebra supplies
an annihilating polynomial whose degree is bounded by the polynomial
histogram count, not by the exponentially large Hilbert dimension.
-/
noncomputable section
namespace QuantumChannelStein.TensorPermutation
open TensorPower Matrix Polynomial

/-- A polynomial-dimensional algebra supplies an annihilator of that degree. -/
theorem exists_monic_annihilator_le_finrank {A : Type*} [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] (a : A) :
    ∃ p : ℂ[X], p.Monic ∧ p.natDegree = Module.finrank ℂ A ∧ aeval a p = 0 := by
  let f := Algebra.lmul ℂ A a
  refine ⟨f.charpoly, f.charpoly_monic, f.charpoly_natDegree, ?_⟩
  apply Algebra.lmul_injective (R := ℂ) (A := A)
  rw [map_zero, ← aeval_algHom_apply]
  exact f.aeval_self_charpoly

/-- Every concrete permutation-invariant tensor operator has a monic
annihilator with a polynomial bound in the tensor length. -/
theorem invariant_monic_annihilator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : invariantAlgebra ι k) :
    ∃ p : ℂ[X], p.Monic ∧
      p.natDegree ≤ (k + 1) ^ (Fintype.card ι * Fintype.card ι) ∧
      aeval A.val p = 0 := by
  obtain ⟨p, hp, hdeg, heval⟩ := exists_monic_annihilator_le_finrank A
  refine ⟨p, hp, hdeg.le.trans (finrank_invariantAlgebra_le ι k), ?_⟩
  rw [show A.val = (invariantAlgebra ι k).val A from rfl,
    aeval_algHom_apply, heval, map_zero]

/-- An annihilating polynomial bounds the actual algebraic spectrum. -/
theorem spectrum_subset_roots_of_annihilator {A : Type*} [Ring A] [Algebra ℂ A]
    (a : A) (p : ℂ[X]) (hp : p.Monic) (heval : aeval a p = 0) :
    spectrum ℂ a ⊆ p.rootSet ℂ := by
  rcases subsingleton_or_nontrivial A with h | h
  · letI := h
    simp [spectrum.of_subsingleton]
  · letI := h
    intro z hz
    have hz' := spectrum.subset_polynomial_aeval a p ⟨z, hz, rfl⟩
    rw [heval, spectrum.zero_eq] at hz'
    rw [hp.mem_rootSet]
    simpa only [Set.mem_singleton_iff, aeval_def, Algebra.algebraMap_self,
      eval₂_id] using hz'

/-- The number of distinct eigenvalues of an invariant tensor operator is
polynomially bounded. This also covers zero-dimensional tensor spaces. -/
theorem ncard_spectrum_invariant_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : invariantAlgebra ι k) :
    (spectrum ℂ A.val).ncard ≤ (k + 1) ^ (Fintype.card ι * Fintype.card ι) := by
  obtain ⟨p, hp, hdeg, heval⟩ := invariant_monic_annihilator k A
  exact (Set.ncard_le_ncard
    (spectrum_subset_roots_of_annihilator A.val p hp heval)
    (p.rootSet_finite ℂ)).trans ((p.ncard_rootSet_le ℂ).trans hdeg)

theorem finite_spectrum_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : invariantAlgebra ι k) : (spectrum ℂ A.val).Finite := by
  obtain ⟨p, hp, _, heval⟩ := invariant_monic_annihilator k A
  exact (p.rootSet_finite ℂ).subset
    (spectrum_subset_roots_of_annihilator A.val p hp heval)

end QuantumChannelStein.TensorPermutation
