import QuantumChannelStein.FixedBlockConstruction
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Uniform auxiliary-map approximation rates

The predicates here refer to actual matrices on the prescribed tensor-power
environments. They are definitions, not interfaces supplying tensor or norm axioms.
-/
noncomputable section
namespace QuantumChannelStein.UniformApproximation
open scoped BigOperators Kronecker Matrix.Norms.L2Operator Topology
open Matrix TensorPower EnvironmentTensor Filter

variable {a b e f : Type*}
  [Fintype a] [Fintype b] [Fintype e] [Fintype f]
  [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]

/-- The actual uniform dilation error at a tensor blocklength. -/
def auxiliaryError (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ)
    (k : ℕ) (C : Matrix (Index e k) (Index f k) ℂ) : ℝ :=
  ‖blockDilation VN k - applyEnvironment (blockDilation VM k) C‖

/-- Existence of an actual auxiliary matrix with a given rate and error. -/
def ApproxAt (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ)
    (k : ℕ) (S error : ℝ) : Prop :=
  ∃ C : Matrix (Index e k) (Index f k) ℂ,
    ‖C‖ ≤ (2 : ℝ) ^ ((k : ℝ) * S / 2) ∧ auxiliaryError VN VM k C ≤ error

/-- Vanishing uniform error at the fixed squared-norm rate S. -/
def VanishingAtRate (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ) (S : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ApproxAt VN VM k S ε

/-- Exponential uniform error at the fixed squared-norm rate S. -/
def ExponentialAtRate (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ) (S : ℝ) : Prop :=
  ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧
    ∀ᶠ k : ℕ in atTop, ApproxAt VN VM k S (K * Real.exp (-γ * k))

omit [DecidableEq b] [DecidableEq e] in
/-- Matrix isometries are contractions in the actual Hilbert operator norm. -/
theorem norm_isometry_le_one (V : Matrix (b × e) a ℂ) (hV : Vᴴ * V = 1) : ‖V‖ ≤ 1 := by
  have hI := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix a a ℂ)
  simp only [Matrix.conjTranspose_one, Matrix.one_mul] at hI
  have hIn := norm_nonneg (1 : Matrix a a ℂ)
  have hIle : ‖(1 : Matrix a a ℂ)‖ ≤ 1 := by nlinarith
  have hsq := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hV] at hsq
  have hn := norm_nonneg V
  nlinarith

omit [DecidableEq b] [DecidableEq e] in
/-- Canonically regrouping tensor outputs and environments preserves the norm. -/
theorem norm_blockDilation (V : Matrix (b × e) a ℂ) (k : ℕ) :
    ‖blockDilation V k‖ = ‖tensorPower V k‖ :=
  TensorPower.norm_reindex _ _ _

/-- Tensor powers of a contraction remain contractions after regrouping. -/
theorem norm_blockDilation_le_one (V : Matrix (b × e) a ℂ) (hV : ‖V‖ ≤ 1) (k : ℕ) :
    ‖blockDilation V k‖ ≤ 1 := by
  rw [norm_blockDilation]
  exact norm_tensorPower_le_one V hV k

omit [Fintype e] [DecidableEq e] [DecidableEq f] in
/-- Exact environmental comparison tensorizes on the prescribed environments. -/
theorem blockDilation_environment (V : Matrix (b × f) a ℂ) (C : Matrix e f ℂ) (k : ℕ) :
    blockDilation (applyEnvironment V C) k =
      applyEnvironment (blockDilation V k) (tensorPower C k) := by
  unfold applyEnvironment blockDilation
  rw [tensorPower_mul]
  have hreindex := Matrix.reindexLinearEquiv_mul ℂ ℂ
    (indexProdEquiv b e k) (indexProdEquiv b f k) (Equiv.refl (Index a k))
    (tensorPower ((1 : Matrix b b ℂ) ⊗ₖ C) k) (tensorPower V k)
  simp only [Matrix.reindexLinearEquiv_apply] at hreindex
  rw [← hreindex, tensorPower_kronecker, tensorPower_one]

/-- An exact finite-rate comparison supplies exact auxiliary maps at every tensor power. -/
theorem exact_approxAt (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ)
    (D : Matrix e f ℂ) (L : ℝ) (hexact : VN = applyEnvironment VM D)
    (hD : ‖D‖ ≤ (2 : ℝ) ^ (L / 2)) (k : ℕ) : ApproxAt VN VM k L 0 := by
  refine ⟨tensorPower D k, ?_, ?_⟩
  · calc
      ‖tensorPower D k‖ ≤ ‖D‖ ^ k := norm_tensorPower_le D k
      _ ≤ ((2 : ℝ) ^ (L / 2)) ^ k := pow_le_pow_left₀ (norm_nonneg D) hD k
      _ = (2 : ℝ) ^ ((k : ℝ) * L / 2) := by
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  · simp [auxiliaryError, hexact, blockDilation_environment]


omit [DecidableEq e] in
/-- Increasing the rate or error allowance preserves an actual approximation. -/
theorem approxAt_mono (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ)
    (k : ℕ) {S R ε δ : ℝ} (hSR : S ≤ R) (hεδ : ε ≤ δ)
    (h : ApproxAt VN VM k S ε) : ApproxAt VN VM k R δ := by
  obtain ⟨C,hC,he⟩ := h
  refine ⟨C, hC.trans ?_, he.trans hεδ⟩
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSR (Nat.cast_nonneg k)) (by norm_num))

/-- Exact finite-rate comparison already gives exponential approximation at
all larger rates (indeed its error is zero). -/
theorem exponential_of_exact (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ)
    (D : Matrix e f ℂ) (L R : ℝ) (hexact : VN = applyEnvironment VM D)
    (hD : ‖D‖ ≤ (2 : ℝ) ^ (L / 2)) (hLR : L ≤ R) : ExponentialAtRate VN VM R := by
  refine ⟨1,1,by norm_num,by norm_num,Filter.Eventually.of_forall ?_⟩
  intro k
  exact approxAt_mono VN VM k hLR (by positivity) (exact_approxAt VN VM D L hexact hD k)

omit [DecidableEq e] in
/-- A concrete auxiliary family whose actual errors converge to zero provides
the vanishing-at-rate premise used in the amplification theorem. -/
theorem vanishing_of_family (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ)
    (S : ℝ) (A : (k : ℕ) → Matrix (Index e k) (Index f k) ℂ)
    (hrate : ∀ᶠ k : ℕ in atTop, ‖A k‖ ≤ (2 : ℝ) ^ ((k : ℝ) * S / 2))
    (herror : Tendsto (fun k => auxiliaryError VN VM k (A k)) atTop (𝓝 0)) :
    VanishingAtRate VN VM S := by
  intro ε hε
  filter_upwards [hrate, herror.eventually_le_const hε] with k hk he
  exact ⟨A k,hk,he⟩

end QuantumChannelStein.UniformApproximation

