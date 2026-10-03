import QuantumChannelStein.DiamondNorm

/-!
# Corollary 5.2: actual exponentially close CP-dominated subchannels

The proof normalizes the actual approximation from Theorem 2.2 and uses the
full all-reference, all-matrix unhalved diamond norm proved from trace-square-
root duality. Both CP domination and approximation refer to the original
channel powers, not surrogate maps.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.DominatedSubchannelFamilies
open Matrix DominatedSubchannels DiamondNorm ExponentialStinespring ChannelDilationPower
  ChannelEntropy ParallelConverse
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
variable {a b eN eM : ℕ}

/-- Rescaling the approximate dilation costs at most `4*error` in the
actual unhalved diamond norm and preserves the CP-domination budget. -/
theorem normalized_subchannel_diamond
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVN : VNᴴ * VN = 1) (C : Matrix (Fin eN) (Fin eM) ℂ)
    (error c : ℝ) (he : 0 ≤ error) (hc : 0 ≤ c)
    (hC : ‖C‖ ^ 2 ≤ c) (herr : ‖VN - ((1 : Operator b) ⊗ₖ C) * VM‖ ≤ error) :
    ∃ L : Subchannel a b,
      MatrixMap.CPLe L.toLinearMap ((c : ℂ) • dilationMap VM) ∧
      diamondNorm (L.toLinearMap - dilationMap VN) ≤ ENNReal.ofReal (4 * error) := by
  obtain ⟨L, W, _, hLW, hW, hdom, heW⟩ :=
    normalized_dominated_subchannel VN VM hVN C error c he hc hC herr
  refine ⟨L, hdom, ?_⟩
  rw [hLW]
  apply (diamondNorm_dilation_difference_le W VN hW
    (UniformApproximation.norm_isometry_le_one VN hVN)).trans
  apply ENNReal.ofReal_le_ofReal
  rw [norm_sub_rev]
  linarith

/-- **Corollary 5.2 (Dominated subchannels)**, equation (5.1).
The concrete subchannels form one family, with a positive exponential rate,
a positive prefactor, and an explicit eventual threshold. -/
theorem corollary_5_2 (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (S : ℝ)
    (hS : (regularizedD Φ Ψ).toReal < S) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧
      ∃ L : (k : ℕ) → Subchannel (a ^ k) (b ^ k),
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        MatrixMap.CPLe (L k).toLinearMap
          (Complex.ofReal ((2 : ℝ) ^ ((k : ℝ) * S)) • (Ψ.tensorPower k).toLinearMap) ∧
        diamondNorm ((L k).toLinearMap - (Φ.tensorPower k).toLinearMap) ≤
          ENNReal.ofReal (K * Real.exp (-γ * k)) := by
  classical
  obtain ⟨K, γ, hK, hγ, C, N, hC⟩ := theorem_2_2_squared Φ Ψ ha
    Φ.stinespring Ψ.stinespring Φ.stinespring_isometry Ψ.stinespring_isometry
    (dilationMap_stinespring Φ) (dilationMap_stinespring Ψ) hfinite S hS
  have hpoint (k : ℕ) (hk : N ≤ k) :
      ∃ L : Subchannel (a ^ k) (b ^ k),
        MatrixMap.CPLe L.toLinearMap
          (Complex.ofReal ((2 : ℝ) ^ ((k : ℝ) * S)) • (Ψ.tensorPower k).toLinearMap) ∧
        diamondNorm (L.toLinearMap - (Φ.tensorPower k).toLinearMap) ≤
          ENNReal.ofReal ((4 * K) * Real.exp (-γ * k)) := by
    have hCk := hC k hk
    obtain ⟨L, hdom, herr⟩ := normalized_subchannel_diamond
      (powerDilation Φ.stinespring k) (powerDilation Ψ.stinespring k)
      (powerDilation_isometry Φ.stinespring Φ.stinespring_isometry k) (C k)
      (K * Real.exp (-γ * k)) ((2 : ℝ) ^ ((k : ℝ) * S)) (by positivity)
      (by positivity) hCk.1 hCk.2
    rw [dilationMap_powerDilation Ψ Ψ.stinespring (dilationMap_stinespring Ψ) k] at hdom
    rw [dilationMap_powerDilation Φ Φ.stinespring (dilationMap_stinespring Φ) k] at herr
    exact ⟨L, hdom, by simpa only [mul_assoc] using herr⟩
  let L : (k : ℕ) → Subchannel (a ^ k) (b ^ k) := fun k =>
    if hk : N ≤ k then Classical.choose (hpoint k hk) else
      subchannelOfDilation (Φ.tensorPower k).stinespring
        (UniformApproximation.norm_isometry_le_one _ (Φ.tensorPower k).stinespring_isometry)
  refine ⟨4 * K, γ, by positivity, hγ, L, N, ?_⟩
  intro k hk
  dsimp [L]
  rw [dif_pos hk]
  exact Classical.choose_spec (hpoint k hk)

end QuantumChannelStein.DominatedSubchannelFamilies
