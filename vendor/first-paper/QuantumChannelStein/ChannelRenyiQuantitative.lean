import QuantumChannelStein.ChannelRenyiAsymptotic
import QuantumChannelStein.RenyiPurificationEstimate
import QuantumChannelStein.TensorPurificationDecomposition
import QuantumChannelStein.ParallelConverse
import QuantumChannelStein.PseudoinverseDomination

/-! # The quantitative regularized Rényi estimate (3.6)

The hypotheses below concern actual Kraus channels and actual Stinespring
matrices. The purification split is constructed by Theorem 2.2, and the
quasi estimate is the proved singular-support Lemma 3.8. No entropy bound,
block additivity, limit identification, or factor decomposition is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ChannelRenyi
open Matrix ChannelEntropy SandwichedRenyi RenyiExponentialScalars
  PurificationDecomposition Filter ParallelConverse EnvironmentTensor
open scoped Topology Matrix.Norms.L2Operator ComplexOrder
variable {n m eN eM : ℕ}

/-- Exact quantitative estimate with a prescribed comparison rate and environments. -/
theorem exists_quantitative_bound_of_exact (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (VN : Matrix (Fin m × Fin eN) (Fin n) ℂ)
    (VM : Matrix (Fin m × Fin eM) (Fin n) ℂ)
    (hVNiso : VNᴴ * VN = 1) (hVMiso : VMᴴ * VM = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤) (S L : ℝ)
    (hS : (ChannelEntropy.regularizedD Φ Ψ).toReal < S) (hSL : S ≤ L)
    (D : Matrix (Fin eN) (Fin eM) ℂ) (hexact : VN = applyEnvironment VM D)
    (hD : ‖D‖ ≤ (2 : ℝ) ^ (L / 2)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ α : ℝ, ∀ hα : 1 < α, α ≤ 2 →
      regularizedD α hα Φ Ψ ≤ (max S (L - 2 * γ / ((α - 1) * Real.log 2)) : ℝ) := by
  obtain ⟨K, γ, hK, hγ, N, hsplit⟩ := tensor_power_decomposition_of_exact
    Φ Ψ hn VN VM hVNiso hVMiso hVN hVM hfinite S L hS hSL D hexact hD
  obtain ⟨c, hc, hcp⟩ := (ChannelEntropy.regularizedD_lt_top_iff_exists_cpLe Φ Ψ hn).mp hfinite
  refine ⟨γ, hγ, ?_⟩
  intro α hα hα2
  apply regularizedD_le_of_eventually_quasi_root_bound α hα hα2 Φ Ψ hn c hc hcp
    (max S (L - 2 * γ / ((α - 1) * Real.log 2))) (envelopeConstant α K)
    (envelopeConstant_pos α K hK)
  filter_upwards [eventually_ge_atTop N] with k hk
  intro ψ
  obtain ⟨F₀, F₁, hρ, h₀, h₁, hF₀, hF₁⟩ := hsplit k hk (n ^ k) ψ
  exact quasi_root_le_exponential_of_decomposition α hα hα2 _ _ F₀ F₁ hρ.symm
    K γ k S L hK hγ.le (Nat.cast_nonneg k) h₀ h₁ hF₀ hF₁

/-- The literal rate log₂ c from a genuine CP comparison is retained unchanged. -/
theorem exists_quantitative_bound_of_cpLe (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (c : ℝ) (hc : 1 ≤ c)
    (hcp : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap))
    (S : ℝ) (hS : (ChannelEntropy.regularizedD Φ Ψ).toReal < S)
    (hSL : S ≤ Real.logb 2 c) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ α : ℝ, ∀ hα : 1 < α, α ≤ 2 →
      regularizedD α hα Φ Ψ ≤
        (max S (Real.logb 2 c - 2 * γ / ((α - 1) * Real.log 2)) : ℝ) := by
  have hfinite := ChannelEntropy.regularizedD_lt_top_of_cpLe Φ Ψ c hc hcp
  obtain ⟨D, hD, hDn⟩ := exact_auxiliary_map Φ.stinespring Ψ.stinespring hc
    (by rw [dilationMap_stinespring, dilationMap_stinespring]; exact hcp)
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hpow : (2 : ℝ) ^ (Real.logb 2 c) = c :=
    Real.rpow_logb (by norm_num) (by norm_num) hcpos
  have hsqrt : Real.sqrt c = (2 : ℝ) ^ (Real.logb 2 c / 2) := by
    calc
      Real.sqrt c = Real.sqrt ((2 : ℝ) ^ (Real.logb 2 c)) := congrArg Real.sqrt hpow.symm
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  exact exists_quantitative_bound_of_exact Φ Ψ hn Φ.stinespring Ψ.stinespring
    Φ.stinespring_isometry Ψ.stinespring_isometry (dilationMap_stinespring Φ)
    (dilationMap_stinespring Ψ) hfinite S (Real.logb 2 c) hS hSL D hD (hDn.trans_eq hsqrt)

/-- Displayed bound (3.6), with the actual pseudoinverse domination rate from Lemma 3.1. -/
theorem equation_3_6 (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤) (S : ℝ)
    (hS : (ChannelEntropy.regularizedD Φ Ψ).toReal < S)
    (hSL : S < Real.logb 2 (Pseudoinverse.choiConstant Φ Ψ)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ α : ℝ, ∀ hα : 1 < α, α ≤ 2 →
      regularizedD α hα Φ Ψ ≤
        (max S (Real.logb 2 (Pseudoinverse.choiConstant Φ Ψ) -
          2 * γ / ((α - 1) * Real.log 2)) : ℝ) := by
  have hs := (ChannelEntropy.regularizedD_lt_top_iff_choi_support Φ Ψ hn).mp hfinite
  exact exists_quantitative_bound_of_cpLe Φ Ψ hn _ (Pseudoinverse.one_le_choiConstant Φ Ψ hn hs)
    (Pseudoinverse.cpLe_choiConstant Φ Ψ hs) S hS hSL.le

/-- For every slope strictly above d, the exact exponential estimate supplies
some finite comparison rate. This version also handles the endpoint d=L. -/
theorem exists_quantitative_bound (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤) (S : ℝ)
    (hS : (ChannelEntropy.regularizedD Φ Ψ).toReal < S) :
    ∃ L γ : ℝ, 0 < γ ∧ ∀ α : ℝ, ∀ hα : 1 < α, α ≤ 2 →
      regularizedD α hα Φ Ψ ≤ (max S (L - 2 * γ / ((α - 1) * Real.log 2)) : ℝ) := by
  obtain ⟨L, hSL, K, γ, hK, hγ, N, hsplit⟩ := tensor_power_decomposition
    Φ Ψ hn Φ.stinespring Ψ.stinespring Φ.stinespring_isometry Ψ.stinespring_isometry
    (dilationMap_stinespring Φ) (dilationMap_stinespring Ψ) hfinite S hS
  obtain ⟨c, hc, hcp⟩ := (ChannelEntropy.regularizedD_lt_top_iff_exists_cpLe Φ Ψ hn).mp hfinite
  refine ⟨L, γ, hγ, ?_⟩
  intro α hα hα2
  apply regularizedD_le_of_eventually_quasi_root_bound α hα hα2 Φ Ψ hn c hc hcp
    (max S (L - 2 * γ / ((α - 1) * Real.log 2))) (envelopeConstant α K)
    (envelopeConstant_pos α K hK)
  filter_upwards [eventually_ge_atTop N] with k hk
  intro ψ
  obtain ⟨F₀, F₁, hρ, h₀, h₁, hF₀, hF₁⟩ := hsplit k hk (n ^ k) ψ
  exact quasi_root_le_exponential_of_decomposition α hα hα2 _ _ F₀ F₁ hρ.symm
    K γ k S L hK hγ.le (Nat.cast_nonneg k) h₀ h₁ hF₀ hF₁

end QuantumChannelStein.ChannelRenyi
