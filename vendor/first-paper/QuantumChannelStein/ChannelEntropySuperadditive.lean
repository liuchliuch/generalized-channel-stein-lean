import QuantumChannelStein.ChannelEntropyTensor
import QuantumChannelStein.ChannelPowerReindex

/-! # Coordinate invariance and actual block-divergence superadditivity -/

noncomputable section
namespace QuantumChannelStein.ChannelEntropy

open Matrix ChannelPowerReindex
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n m n' m' r r' : ℕ}

/-- A coordinate permutation of a normalized reference-assisted input. -/
def reindexInput (en : Fin n ≃ Fin n') (ψ : UnitPureInput n n) : UnitPureInput n' n' :=
  ⟨WithLp.toLp 2 (fun p => ψ.val ((en.prodCongr en).symm p)), by
    have hs : ‖WithLp.toLp 2 (fun p => ψ.val ((en.prodCongr en).symm p))‖ ^ 2 = ‖ψ.val‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, PiLp.toLp_apply]
      exact Equiv.sum_comp (en.prodCongr en).symm (fun p => ‖ψ.val p‖ ^ 2)
    rw [ψ.property] at hs
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun p => ψ.val ((en.prodCongr en).symm p)))]⟩

/-- The optimizing pure-input spaces are equivalent under a coordinate
permutation of the input and its isomorphic reference. -/
def inputEquiv (en : Fin n ≃ Fin n') : UnitPureInput n n ≃ UnitPureInput n' n' where
  toFun := reindexInput en
  invFun := reindexInput en.symm
  left_inv ψ := by
    apply Subtype.ext
    ext ⟨i, j⟩
    simp [reindexInput, Equiv.prodCongr_apply]
  right_inv ψ := by
    apply Subtype.ext
    ext ⟨i, j⟩
    simp [reindexInput, Equiv.prodCongr_apply]

theorem pureMatrix_reindexInput (en : Fin n ≃ Fin n') (ψ : UnitPureInput n n) :
    pureMatrix (reindexInput en ψ).val =
      Matrix.reindex (en.prodCongr en) (en.prodCongr en) (pureMatrix ψ.val) := by
  ext p q
  rfl

/-- Actual amplification respects a simultaneous input, output, and
reference coordinate permutation. -/
theorem amplify_reindexChannel (er : Fin r ≃ Fin r')
    (en : Fin n ≃ Fin n') (em : Fin m ≃ Fin m') (Φ : KrausChannel n m)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    (reindexChannel en em Φ).amplify r'
      (Matrix.reindex (er.prodCongr en) (er.prodCongr en) X) =
      Matrix.reindex (er.prodCongr em) (er.prodCongr em) (Φ.amplify r X) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  rw [KrausChannel.amplify_block]
  have hblock :
      (fun x y => Matrix.reindex (er.prodCongr en) (er.prodCongr en) X (i, x) (j, y)) =
      Matrix.reindex en en (fun x y => X (er.symm i, x) (er.symm j, y)) := rfl
  rw [hblock, reindexChannel_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map, KrausChannel.amplify_block]

/-- The induced permutation of flattened reference-output coordinates. -/
def outputReindex (en : Fin n ≃ Fin n') (em : Fin m ≃ Fin m') :
    Fin (n * m) ≃ Fin (n' * m') :=
  finProdFinEquiv.symm.trans ((en.prodCongr em).trans finProdFinEquiv)

theorem pureOutput_reindexChannel (en : Fin n ≃ Fin n') (em : Fin m ≃ Fin m')
    (Φ : KrausChannel n m) (ψ : UnitPureInput n n) :
    pureOutput (reindexChannel en em Φ) (reindexInput en ψ) =
      (pureOutput Φ ψ).reindex (outputReindex en em) := by
  apply state_eq_of_matrix_eq
  rw [pureOutput_matrix, pureMatrix_reindexInput, amplify_reindexChannel]
  ext i j
  simp [State.reindex_matrix, pureOutput_matrix, outputReindex, Matrix.reindex_apply]

/-- The channel divergence is invariant under actual common permutations
of input and output coordinates. -/
theorem channelD_reindexChannel (en : Fin n ≃ Fin n') (em : Fin m ≃ Fin m')
    (Φ Ψ : KrausChannel n m) :
    channelD (reindexChannel en em Φ) (reindexChannel en em Ψ) = channelD Φ Ψ := by
  unfold channelD
  rw [← (inputEquiv en).iSup_comp]
  apply iSup_congr
  intro ψ
  change RelativeEntropy.umegaki (pureOutput (reindexChannel en em Φ) (reindexInput en ψ))
    (pureOutput (reindexChannel en em Ψ) (reindexInput en ψ)) = _
  rw [pureOutput_reindexChannel, pureOutput_reindexChannel, RelativeEntropy.umegaki_reindex]

/-- The proved concrete block-splitting map identity transfers to exact
channel entropy, with no assumed tensor/channel entropy identity. -/
theorem channelD_tensorPower_add (Φ Ψ : KrausChannel n m) (k l : ℕ) :
    channelD (Φ.tensorPower (k + l)) (Ψ.tensorPower (k + l)) =
      channelD ((Φ.tensorPower k).tensor (Φ.tensorPower l))
        ((Ψ.tensorPower k).tensor (Ψ.tensorPower l)) := by
  rw [← channelD_reindexChannel (channelAddEquiv n k l) (channelAddEquiv m k l)
    ((Φ.tensorPower k).tensor (Φ.tensorPower l)) ((Ψ.tensorPower k).tensor (Ψ.tensorPower l))]
  exact (channelD_congr _ _ _ _ (tensorPower_add_toLinearMap Φ k l)
    (tensorPower_add_toLinearMap Ψ k l)).symm

/-- The actual channel block-divergence sequence is superadditive. This
covers finite and infinite divergences and includes zero block lengths. -/
theorem channelD_tensorPower_superadditive (Φ Ψ : KrausChannel n m) (k l : ℕ) :
    channelD (Φ.tensorPower k) (Ψ.tensorPower k) + channelD (Φ.tensorPower l) (Ψ.tensorPower l) ≤
      channelD (Φ.tensorPower (k + l)) (Ψ.tensorPower (k + l)) := by
  rw [channelD_tensorPower_add]
  exact channelD_tensor_superadditive _ _ _ _

end QuantumChannelStein.ChannelEntropy
