import QuantumChannelStein.PurificationDecomposition

/-! # Uniform actual tensor-power purification factors from Theorem 2.2 -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.PurificationDecomposition
open Matrix ChannelEntropy ReferenceAcceptance TensorNorm SandwichedRenyi
  EnvironmentTensor ChannelDilationPower UniformApproximation UniformApproximationFromTesting
  ExponentialStinespring
open scoped BigOperators Kronecker Matrix.Norms.L2Operator ComplexOrder
variable {a b eN eM : ℕ}

/-- The exact tensor-power comparison is transported to the literal finite
environment powers, with its genuine operator-norm rate. -/
theorem exists_exact_power_auxiliary
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (D : Matrix (Fin eN) (Fin eM) ℂ) (L : ℝ)
    (hexact : VN = applyEnvironment VM D) (hD : ‖D‖ ≤ (2 : ℝ) ^ (L / 2)) (k : ℕ) :
    ∃ E : Matrix (Fin (eN ^ k)) (Fin (eM ^ k)) ℂ,
      ‖E‖ ≤ (2 : ℝ) ^ ((k : ℝ) * L / 2) ∧
      powerDilation VN k = applyEnvironment (powerDilation VM k) E := by
  obtain ⟨E, hE, he⟩ := exact_approxAt VN VM D L hexact hD k
  refine ⟨finiteAuxiliary k E, by simpa only [norm_finiteAuxiliary] using hE, ?_⟩
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  rw [finiteAuxiliary_error]
  exact he

/-- The square of the paper's half-rate norm bound is exactly its domination budget. -/
theorem half_rate_sq (k : ℕ) (S : ℝ) :
    ((2 : ℝ) ^ ((k : ℝ) * S / 2)) ^ 2 = (2 : ℝ) ^ ((k : ℝ) * S) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  norm_num

/-- The actual uniform purification split required in Theorem 3.7.
The factors retain the original null environment, and all five conclusions
hold uniformly for every finite reference and every unit pure input. -/
theorem tensor_power_decomposition (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1) (hVMiso : VMᴴ * VM = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (hfinite : regularizedD Φ Ψ < ⊤) (S : ℝ)
    (hS : (regularizedD Φ Ψ).toReal < S) :
    ∃ L : ℝ, S ≤ L ∧ ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ r : ℕ, ∀ ψ : UnitPureInput r (a ^ k),
        ∃ F₀ F₁ : Matrix (Fin (r * b ^ k)) (Fin (eN ^ k)) ℂ,
          (pureOutput (Φ.tensorPower k) ψ).matrix = (F₀ + F₁) * (F₀ + F₁)ᴴ ∧
          ((2 : ℝ) ^ ((k : ℝ) * S) • (pureOutput (Ψ.tensorPower k) ψ).matrix -
            F₀ * F₀ᴴ).PosSemidef ∧
          ((4 * (2 : ℝ) ^ ((k : ℝ) * L)) • (pureOutput (Ψ.tensorPower k) ψ).matrix -
            F₁ * F₁ᴴ).PosSemidef ∧
          frobeniusNorm F₀ ≤ 1 + K * Real.exp (-γ * k) ∧
          frobeniusNorm F₁ ≤ K * Real.exp (-γ * k) := by
  obtain ⟨D, L₀, hexact, hD⟩ :=
    exists_exact_comparison_of_finite_regularizedD Φ Ψ ha VN VM hVN hVM hfinite
  let L : ℝ := max L₀ S
  have hSL : S ≤ L := le_max_right _ _
  have hDL : ‖D‖ ≤ (2 : ℝ) ^ (L / 2) := hD.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (div_le_div_of_nonneg_right (le_max_left L₀ S) (by norm_num)))
  obtain ⟨K, γ, hK, hγ, C, N, hC⟩ :=
    theorem_2_2 Φ Ψ ha VN VM hVNiso hVMiso hVN hVM hfinite S hS
  refine ⟨L, hSL, K, γ, hK, hγ, N, ?_⟩
  intro k hk r ψ
  obtain ⟨E, hE, he⟩ := exists_exact_power_auxiliary VN VM D L hexact hDL k
  have hCk := hC k hk
  have hCsq : ‖C k‖ ^ 2 ≤ (2 : ℝ) ^ ((k : ℝ) * S) :=
    (pow_le_pow_left₀ (norm_nonneg _) hCk.1 2).trans_eq (half_rate_sq k S)
  have hCL : ‖C k‖ ≤ (2 : ℝ) ^ ((k : ℝ) * L / 2) := hCk.1.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSL (Nat.cast_nonneg k)) (by norm_num)))
  have hEC : ‖E - C k‖ ≤ 2 * (2 : ℝ) ^ ((k : ℝ) * L / 2) := by
    have ht := (norm_sub_le E (C k)).trans (add_le_add hE hCL)
    linarith
  have hECsq : ‖E - C k‖ ^ 2 ≤ 4 * (2 : ℝ) ^ ((k : ℝ) * L) := by
    calc
      _ ≤ (2 * (2 : ℝ) ^ ((k : ℝ) * L / 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hEC 2
      _ = _ := by rw [mul_pow, half_rate_sq]; norm_num
  exact one_shot_decomposition (Φ.tensorPower k) (Ψ.tensorPower k)
    (powerDilation VN k) (powerDilation VM k)
    (dilationMap_powerDilation Φ VN hVN k) (dilationMap_powerDilation Ψ VM hVM k)
    (C k) E he ((2 : ℝ) ^ ((k : ℝ) * S)) (4 * (2 : ℝ) ^ ((k : ℝ) * L))
    (K * Real.exp (-γ * k)) (by positivity) (by positivity) hCsq hECsq hCk.2 ψ


/-- Prescribed-rate version: the same genuine split keeps the exact comparison
rate L unchanged, as in the quantitative bound (3.6). -/
theorem tensor_power_decomposition_of_exact (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1) (hVMiso : VMᴴ * VM = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (hfinite : regularizedD Φ Ψ < ⊤) (S L : ℝ)
    (hS : (regularizedD Φ Ψ).toReal < S) (hSL : S ≤ L)
    (D : Matrix (Fin eN) (Fin eM) ℂ) (hexact : VN = applyEnvironment VM D)
    (hD : ‖D‖ ≤ (2 : ℝ) ^ (L / 2)) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ r : ℕ, ∀ ψ : UnitPureInput r (a ^ k),
        ∃ F₀ F₁ : Matrix (Fin (r * b ^ k)) (Fin (eN ^ k)) ℂ,
          (pureOutput (Φ.tensorPower k) ψ).matrix = (F₀ + F₁) * (F₀ + F₁)ᴴ ∧
          ((2 : ℝ) ^ ((k : ℝ) * S) • (pureOutput (Ψ.tensorPower k) ψ).matrix -
            F₀ * F₀ᴴ).PosSemidef ∧
          ((4 * (2 : ℝ) ^ ((k : ℝ) * L)) • (pureOutput (Ψ.tensorPower k) ψ).matrix -
            F₁ * F₁ᴴ).PosSemidef ∧
          frobeniusNorm F₀ ≤ 1 + K * Real.exp (-γ * k) ∧
          frobeniusNorm F₁ ≤ K * Real.exp (-γ * k) := by
  obtain ⟨K, γ, hK, hγ, C, N, hC⟩ :=
    theorem_2_2 Φ Ψ ha VN VM hVNiso hVMiso hVN hVM hfinite S hS
  refine ⟨K, γ, hK, hγ, N, ?_⟩
  intro k hk r ψ
  obtain ⟨E, hE, he⟩ := exists_exact_power_auxiliary VN VM D L hexact hD k
  have hCk := hC k hk
  have hCsq : ‖C k‖ ^ 2 ≤ (2 : ℝ) ^ ((k : ℝ) * S) :=
    (pow_le_pow_left₀ (norm_nonneg _) hCk.1 2).trans_eq (half_rate_sq k S)
  have hCL : ‖C k‖ ≤ (2 : ℝ) ^ ((k : ℝ) * L / 2) := hCk.1.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSL (Nat.cast_nonneg k)) (by norm_num)))
  have hEC : ‖E - C k‖ ≤ 2 * (2 : ℝ) ^ ((k : ℝ) * L / 2) := by
    have ht := (norm_sub_le E (C k)).trans (add_le_add hE hCL)
    linarith
  have hECsq : ‖E - C k‖ ^ 2 ≤ 4 * (2 : ℝ) ^ ((k : ℝ) * L) := by
    calc
      _ ≤ (2 * (2 : ℝ) ^ ((k : ℝ) * L / 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hEC 2
      _ = _ := by rw [mul_pow, half_rate_sq]; norm_num
  exact one_shot_decomposition (Φ.tensorPower k) (Ψ.tensorPower k)
    (powerDilation VN k) (powerDilation VM k)
    (dilationMap_powerDilation Φ VN hVN k) (dilationMap_powerDilation Ψ VM hVM k)
    (C k) E he ((2 : ℝ) ^ ((k : ℝ) * S)) (4 * (2 : ℝ) ^ ((k : ℝ) * L))
    (K * Real.exp (-γ * k)) (by positivity) (by positivity) hCsq hECsq hCk.2 ψ

end QuantumChannelStein.PurificationDecomposition
