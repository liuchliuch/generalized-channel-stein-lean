import QuantumChannelStein.ChannelRenyi
import QuantumChannelStein.SandwichedRenyiTensor
import QuantumChannelStein.ChannelEntropySuperadditive

/-! # Product-input superadditivity for actual sandwiched channel Rényi entropy -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ChannelRenyi
open ChannelEntropy ChannelPowerReindex SandwichedRenyi
variable {n m a b n' m' : ℕ}

theorem renyi_productInput (α : ℝ) (hα : 1 < α)
    (Φ Ψ : KrausChannel n m) (Γ Θ : KrausChannel a b)
    (ψ : UnitPureInput n n) (φ : UnitPureInput a a) :
    renyi α hα (pureOutput (Φ.tensor Γ) (productInput ψ φ))
      (pureOutput (Ψ.tensor Θ) (productInput ψ φ)) =
      renyi α hα (pureOutput Φ ψ) (pureOutput Ψ ψ) +
        renyi α hα (pureOutput Γ φ) (pureOutput Θ φ) := by
  rw [pureOutput_productInput, pureOutput_productInput, renyi_reindex, renyi_tensor]

/-- The supremum need not be attained: strict real lower approximants suffice. -/
theorem channelD_tensor_superadditive (α : ℝ) (hα : 1 < α)
    (Φ Ψ : KrausChannel n m) (Γ Θ : KrausChannel a b) :
    channelD α hα Φ Ψ + channelD α hα Γ Θ ≤ channelD α hα (Φ.tensor Γ) (Ψ.tensor Θ) := by
  apply EReal.add_le_of_forall_lt
  intro x hx y hy
  obtain ⟨ψ, hψ⟩ := lt_iSup_iff.mp hx
  obtain ⟨φ, hφ⟩ := lt_iSup_iff.mp hy
  calc
    x + y ≤ renyi α hα (pureOutput Φ ψ) (pureOutput Ψ ψ) +
        renyi α hα (pureOutput Γ φ) (pureOutput Θ φ) := add_le_add hψ.le hφ.le
    _ = renyi α hα (pureOutput (Φ.tensor Γ) (productInput ψ φ))
        (pureOutput (Ψ.tensor Θ) (productInput ψ φ)) := (renyi_productInput α hα Φ Ψ Γ Θ ψ φ).symm
    _ ≤ channelD α hα (Φ.tensor Γ) (Ψ.tensor Θ) := renyi_pureOutput_le_channelD α hα _ _ _

theorem channelD_reindexChannel (α : ℝ) (hα : 1 < α)
    (en : Fin n ≃ Fin n') (em : Fin m ≃ Fin m') (Φ Ψ : KrausChannel n m) :
    channelD α hα (reindexChannel en em Φ) (reindexChannel en em Ψ) = channelD α hα Φ Ψ := by
  unfold channelD
  rw [← (inputEquiv en).iSup_comp]
  apply iSup_congr
  intro ψ
  change renyi α hα (pureOutput (reindexChannel en em Φ) (reindexInput en ψ))
    (pureOutput (reindexChannel en em Ψ) (reindexInput en ψ)) = _
  rw [pureOutput_reindexChannel, pureOutput_reindexChannel, renyi_reindex]

theorem channelD_tensorPower_add (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m) (k l : ℕ) :
    channelD α hα (Φ.tensorPower (k + l)) (Ψ.tensorPower (k + l)) =
      channelD α hα ((Φ.tensorPower k).tensor (Φ.tensorPower l))
        ((Ψ.tensorPower k).tensor (Ψ.tensorPower l)) := by
  rw [← channelD_reindexChannel α hα (channelAddEquiv n k l) (channelAddEquiv m k l)
    ((Φ.tensorPower k).tensor (Φ.tensorPower l)) ((Ψ.tensorPower k).tensor (Ψ.tensorPower l))]
  exact (channelD_congr α hα _ _ _ _ (tensorPower_add_toLinearMap Φ k l)
    (tensorPower_add_toLinearMap Ψ k l)).symm

/-- Superadditivity of the actual block sequence, including singular/infinite branches. -/
theorem channelD_tensorPower_superadditive (α : ℝ) (hα : 1 < α)
    (Φ Ψ : KrausChannel n m) (k l : ℕ) :
    channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k) +
      channelD α hα (Φ.tensorPower l) (Ψ.tensorPower l) ≤
        channelD α hα (Φ.tensorPower (k + l)) (Ψ.tensorPower (k + l)) := by
  rw [channelD_tensorPower_add]
  exact channelD_tensor_superadditive α hα _ _ _ _

end QuantumChannelStein.ChannelRenyi
