import QuantumChannelStein.SandwichedSchattenTriangle

/-! # Second inequality of Lemma 3.8

The rectangular factor spaces are identical. The proof combines the actual
Schatten `2α` triangle inequality with the first quasi-bound. The hypotheses
also force the sum to remain supported on the alternative, so the real
formula agrees with the support-aware extended quasi-divergence.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
attribute [local instance] matrixCStar
variable {n e : ℕ}

/-- Actual weighted factor whose Gram matrix is the sandwich. -/
def weightedFactor (α : ℝ) (B : Operator n) (F : Matrix (Fin n) (Fin e) ℂ) :
    Matrix (Fin n) (Fin e) ℂ := CFC.rpow B (sandwichExponent α) * F

theorem weightedFactor_gram (α : ℝ) (B : Operator n) (F : Matrix (Fin n) (Fin e) ℂ) :
    weightedFactor α B F * (weightedFactor α B F)ᴴ = sandwichedOperator α (F * Fᴴ) B := by
  have hP : (CFC.rpow B (sandwichExponent α)).PosSemidef := CFC.rpow_nonneg.posSemidef
  simp only [weightedFactor, sandwichedOperator, Matrix.conjTranspose_mul,
    hP.isHermitian.eq, Matrix.mul_assoc]

theorem quasi_root_eq_schatten (α : ℝ) (B : Operator n) (F : Matrix (Fin n) (Fin e) ℂ) :
    quasi α (F * Fᴴ) B ^ (1 / (2 * α)) = schattenTwoAlpha α (weightedFactor α B F) := by
  rw [schattenTwoAlpha, weightedFactor_gram]
  rfl

/-- The genuine weighted Schatten triangle for the raw spectral quasi-trace. -/
theorem quasi_sum_root_le (α : ℝ) (hα : 1 < α) (B : Operator n)
    (F G : Matrix (Fin n) (Fin e) ℂ) :
    quasi α ((F + G) * (F + G)ᴴ) B ^ (1 / (2 * α)) ≤
      quasi α (F * Fᴴ) B ^ (1 / (2 * α)) + quasi α (G * Gᴴ) B ^ (1 / (2 * α)) := by
  rw [quasi_root_eq_schatten, quasi_root_eq_schatten, quasi_root_eq_schatten]
  have hlin : weightedFactor α B (F + G) = weightedFactor α B F + weightedFactor α B G :=
    Matrix.mul_add _ _ _
  rw [hlin]
  exact schattenTwoAlpha_add α hα _ _

theorem quasi_factor_root_le_of_domination (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (F : Matrix (Fin n) (Fin e) ℂ) (B : Operator n) (hB : B.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) (hdom : (t • B - F * Fᴴ).PosSemidef) :
    quasi α (F * Fᴴ) B ^ (1 / (2 * α)) ≤
      t ^ ((α - 1) / (2 * α)) * frobeniusNorm F ^ (1 / α) :=
  SchattenScalar.root_bound_of_domination (quasi_nonneg _ _ _) ht (frobeniusNorm_nonneg F)
    (by linarith) (quasi_factor_le_of_domination α hα hα2 F B hB t ht hdom)

/-- **Lemma 3.8, second assertion**, in the stronger arbitrary-PSD-alternative form. -/
theorem quasi_sum_le_of_domination (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (B : Operator n) (hB : B.PosSemidef) (F G : Matrix (Fin n) (Fin e) ℂ)
    (t₀ t₁ : ℝ) (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁)
    (hF : (t₀ • B - F * Fᴴ).PosSemidef) (hG : (t₁ • B - G * Gᴴ).PosSemidef) :
    quasi α ((F + G) * (F + G)ᴴ) B ^ (1 / (2 * α)) ≤
      t₀ ^ ((α - 1) / (2 * α)) * frobeniusNorm F ^ (1 / α) +
      t₁ ^ ((α - 1) / (2 * α)) * frobeniusNorm G ^ (1 / α) :=
  (quasi_sum_root_le α hα B F G).trans <| add_le_add
    (quasi_factor_root_le_of_domination α hα hα2 F B hB t₀ ht₀ hF)
    (quasi_factor_root_le_of_domination α hα hα2 G B hB t₁ ht₁ hG)

/-- Domination of each rectangular factor forces support of their sum. -/
theorem sum_gram_domination (B : Operator n) (F G : Matrix (Fin n) (Fin e) ℂ)
    (t₀ t₁ : ℝ) (hF : (t₀ • B - F * Fᴴ).PosSemidef)
    (hG : (t₁ • B - G * Gᴴ).PosSemidef) :
    ((2 * (t₀ + t₁)) • B - (F + G) * (F + G)ᴴ).PosSemidef := by
  have h := ((hF.smul (by norm_num : (0 : ℝ) ≤ 2)).add
    (hG.smul (by norm_num : (0 : ℝ) ≤ 2))).add (gram_positive (F - G))
  convert h using 1
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    smul_sub, SemigroupAction.mul_smul, add_smul, two_smul ℝ]
  abel

theorem quasiExtended_sum_eq_real (α : ℝ) (hα : 1 < α)
    (B : Operator n) (hB : B.PosSemidef) (F G : Matrix (Fin n) (Fin e) ℂ)
    (t₀ t₁ : ℝ) (hF : (t₀ • B - F * Fᴴ).PosSemidef)
    (hG : (t₁ • B - G * Gᴴ).PosSemidef) :
    quasiExtended α hα ((F + G) * (F + G)ᴴ) B (gram_positive _) hB =
      (quasi α ((F + G) * (F + G)ᴴ) B : EReal) :=
  quasiExtended_of_support _ _ _ _ _ _ <|
    SupportDomination.ker_le_of_posSemidef_smul_sub (gram_positive _) (sum_gram_domination B F G t₀ t₁ hF hG)

/-- The literal trace-one-alternative specialization of the second 3.8 assertion. -/
theorem lemma_3_8_sum (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (σ : State n) (F₀ F₁ : Matrix (Fin n) (Fin e) ℂ)
    (t₀ t₁ : ℝ) (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁)
    (h₀ : (t₀ • σ.matrix - F₀ * F₀ᴴ).PosSemidef)
    (h₁ : (t₁ • σ.matrix - F₁ * F₁ᴴ).PosSemidef) :
    quasi α ((F₀ + F₁) * (F₀ + F₁)ᴴ) σ.matrix ^ (1 / (2 * α)) ≤
      t₀ ^ ((α - 1) / (2 * α)) * frobeniusNorm F₀ ^ (1 / α) +
      t₁ ^ ((α - 1) / (2 * α)) * frobeniusNorm F₁ ^ (1 / α) :=
  quasi_sum_le_of_domination α hα hα2 σ.matrix σ.positive F₀ F₁ t₀ t₁ ht₀ ht₁ h₀ h₁

end QuantumChannelStein.SandwichedRenyi
