import QuantumChannelStein.RelativeEntropyBound
import QuantumChannelStein.CPOrder
import QuantumChannelStein.Testing
import QuantumChannelStein.TensorChannel

/-!
# Reference-assisted channel Umegaki divergence

`channelD` is the exact supremum of state Umegaki relative entropy over
unit pure inputs with reference dimension equal to the input dimension.
The outputs are the actual Kraus amplifications, flattened by the
canonical equivalence `Fin r × Fin m ≃ Fin (r*m)`.

`regularizedD` is defined as the supremum of the per-use divergences of
the actual tensor-power channels. This file does not identify that
supremum with a limit, invoke Fekete's lemma, or assume a pure-to-mixed
input reduction. Those require separate entropy theorems.
-/

noncomputable section
namespace QuantumChannelStein.ChannelEntropy

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n m r : ℕ}

/-- A normalized pure input on a reference and an input register. -/
def UnitPureInput (r n : ℕ) :=
  {ψ : EuclideanSpace ℂ (Fin r × Fin n) // ‖ψ‖ = 1}

/-- The rank-one input matrix is genuinely positive semidefinite. -/
theorem pureMatrix_positive {ι : Type*} [Fintype ι]
    (ψ : EuclideanSpace ℂ ι) : (pureMatrix ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

/-- Unit vectors give complex trace one, not merely real part one. -/
theorem trace_pureMatrix_of_norm_one {ι : Type*} [Fintype ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : (pureMatrix ψ).trace = 1 := by
  apply Complex.ext
  · simpa [hψ] using trace_pureMatrix_re ψ
  · exact (Complex.nonneg_iff.mp (pureMatrix_positive ψ).trace_nonneg).2.symm

/-- Simultaneous bijective row and column relabeling preserves trace. -/
theorem trace_reindex_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  exact Equiv.sum_comp e.symm (fun i => A i i)

/-- The actual reference-assisted channel output density matrix. -/
def pureOutput (Φ : KrausChannel n m) (ψ : UnitPureInput r n) : State (r * m) where
  matrix := Matrix.reindex finProdFinEquiv finProdFinEquiv (Φ.amplify r (pureMatrix ψ.val))
  positive := (Φ.amplify_positive r (pureMatrix_positive ψ.val)).submatrix finProdFinEquiv.symm
  trace_one := by
    rw [trace_reindex_equiv, Φ.trace_amplify]
    exact trace_pureMatrix_of_norm_one ψ.val ψ.property

@[simp]
theorem pureOutput_matrix (Φ : KrausChannel n m) (ψ : UnitPureInput r n) :
    (pureOutput Φ ψ).matrix =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Φ.amplify r (pureMatrix ψ.val)) := rfl

/-- CP domination gives PSD domination for every finite reference and
every positive input matrix. -/
theorem amplify_domination (Φ Ψ : KrausChannel n m) (c : ℝ)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap))
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) (hX : X.PosSemidef) :
    (c • Ψ.amplify r X - Φ.amplify r X).PosSemidef := by
  have hp := h r X hX
  have heq : MatrixMap.amplify ((c : ℂ) • Ψ.toLinearMap - Φ.toLinearMap) r X =
      c • Ψ.amplify r X - Φ.amplify r X := by
    ext ⟨a, u⟩ ⟨b, v⟩
    simp [MatrixMap.amplify, KrausChannel.amplify_block, KrausChannel.toLinearMap]
  rw [heq] at hp
  exact hp

/-- Reindexing the actual amplified outputs preserves their domination. -/
theorem pureOutput_domination (Φ Ψ : KrausChannel n m) (c : ℝ)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap))
    (ψ : UnitPureInput r n) :
    (c • (pureOutput Ψ ψ).matrix - (pureOutput Φ ψ).matrix).PosSemidef :=
  (amplify_domination Φ Ψ c h (pureMatrix ψ.val)
    (pureMatrix_positive ψ.val)).submatrix finProdFinEquiv.symm

/-- One fixed pure reference-assisted input obeys the logarithmic bound. -/
theorem pureOutput_umegaki_le (Φ Ψ : KrausChannel n m) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap))
    (ψ : UnitPureInput r n) :
    RelativeEntropy.umegaki (pureOutput Φ ψ) (pureOutput Ψ ψ) ≤
      (Real.logb 2 c : EReal) :=
  RelativeEntropy.umegaki_le_log2_of_domination _ _ c hc
    (pureOutput_domination Φ Ψ c h ψ)

/-- Channel Umegaki relative entropy, optimized over unit pure states
with a reference system isomorphic to the input system. -/
def channelD (Φ Ψ : KrausChannel n m) : EReal :=
  ⨆ ψ : UnitPureInput n n, RelativeEntropy.umegaki (pureOutput Φ ψ) (pureOutput Ψ ψ)

/-- Every allowed pure input is a lower bound for the channel supremum. -/
theorem umegaki_pureOutput_le_channelD (Φ Ψ : KrausChannel n m)
    (ψ : UnitPureInput n n) :
    RelativeEntropy.umegaki (pureOutput Φ ψ) (pureOutput Ψ ψ) ≤ channelD Φ Ψ := by
  unfold channelD
  exact le_iSup (fun φ : UnitPureInput n n =>
    RelativeEntropy.umegaki (pureOutput Φ φ) (pureOutput Ψ φ)) ψ

/-- CP scalar domination uniformly bounds the exact channel supremum. -/
theorem channelD_le_log2_of_cpLe (Φ Ψ : KrausChannel n m) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    channelD Φ Ψ ≤ (Real.logb 2 c : EReal) := by
  apply iSup_le
  intro ψ
  exact pureOutput_umegaki_le Φ Ψ c hc h ψ

/-- A finite CP-domination constant guarantees finite channel divergence. -/
theorem channelD_lt_top_of_cpLe (Φ Ψ : KrausChannel n m) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    channelD Φ Ψ < ⊤ :=
  lt_of_le_of_lt (channelD_le_log2_of_cpLe Φ Ψ c hc h) (EReal.coe_lt_top _)

/-- A nonzero input dimension has an explicit unit product input. -/
def unitProductInput (hn : 0 < n) : UnitPureInput n n :=
  ⟨EuclideanSpace.single (⟨0, hn⟩, ⟨0, hn⟩) 1, by simp⟩

/-- Nonnegativity of the optimized divergence on a nonzero input space. -/
theorem channelD_nonneg (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    0 ≤ channelD Φ Ψ := by
  exact (RelativeEntropy.umegaki_nonneg (pureOutput Φ (unitProductInput hn))
    (pureOutput Ψ (unitProductInput hn))).trans
      (umegaki_pureOutput_le_channelD Φ Ψ (unitProductInput hn))

/-- A channel has zero divergence from itself. The nonzero input
dimension ensures that the optimizing family is nonempty. -/
theorem channelD_self (Φ : KrausChannel n m) (hn : 0 < n) : channelD Φ Φ = 0 := by
  apply le_antisymm _ (channelD_nonneg Φ Φ hn)
  apply iSup_le
  intro ψ
  simp

/-- Regularized channel divergence as the supremum of actual tensor-power
per-use divergences, with only positive block lengths included. This
definition does not assert equality to an asymptotic limit. -/
def regularizedD (Φ Ψ : KrausChannel n m) : EReal :=
  ⨆ k : ℕ, ⨆ (_ : 0 < k),
    (((k : ℝ)⁻¹ : ℝ) : EReal) * channelD (Φ.tensorPower k) (Ψ.tensorPower k)

/-- Every positive block length contributes to the regularized supremum. -/
theorem tensorPower_rate_le_regularizedD (Φ Ψ : KrausChannel n m)
    (k : ℕ) (hk : 0 < k) :
    (((k : ℝ)⁻¹ : ℝ) : EReal) * channelD (Φ.tensorPower k) (Ψ.tensorPower k) ≤
      regularizedD Φ Ψ :=
  le_iSup_of_le k (le_iSup_of_le hk le_rfl)

end QuantumChannelStein.ChannelEntropy
