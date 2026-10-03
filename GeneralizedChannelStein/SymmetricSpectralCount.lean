import GeneralizedChannelStein.InvariantOrbitDimension
import QuantumChannelStein.InvariantSpectralBound

/-! # Exact spectral complexity of permutation-invariant operators -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.SymmetricSpectralCount
open QuantumChannelStein TensorPermutation TensorPower Matrix Polynomial

/-- The actual spectrum is bounded by the dimension of the actual invariant algebra. -/
theorem ncard_spectrum_le_finrank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (A : invariantAlgebra ι n) :
    (spectrum ℂ A.val).ncard ≤ Module.finrank ℂ (invariantAlgebra ι n) := by
  obtain ⟨p, hp, hdeg, heval⟩ := exists_monic_annihilator_le_finrank A
  have heval' : aeval A.val p = 0 := by
    rw [show A.val = (invariantAlgebra ι n).val A from rfl,
      aeval_algHom_apply, heval, map_zero]
  exact (Set.ncard_le_ncard
    (spectrum_subset_roots_of_annihilator A.val p hp heval')
    (p.rootSet_finite ℂ)).trans ((p.ncard_rootSet_le ℂ).trans hdeg.le)

/-- The exact binomial overhead in Lemma 33, before taking its base-two logarithm. -/
theorem ncard_spectrum_le_binomial (d n : ℕ) (hd : 0 < d)
    (A : invariantAlgebra (Fin d) n) :
    (spectrum ℂ A.val).ncard ≤ (n+d^2-1).choose (d^2-1) :=
  (ncard_spectrum_le_finrank n A).trans
    (InvariantOrbitDimension.finrank_invariantAlgebra_le_binomial d n hd)

end GeneralizedChannelStein.SymmetricSpectralCount
