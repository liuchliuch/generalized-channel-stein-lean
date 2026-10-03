import QuantumChannelStein.ChannelEntropyFiniteness
import QuantumChannelStein.PseudoinverseCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The exact pseudoinverse scalar-domination constant

The central norm bound is the C*-algebra order estimate for the concrete
positive sandwich `B⁺¹ᐟ² A B⁺¹ᐟ²`, conjugated back by the actual square root
of `B`. Singular operators are handled using the proved support projection.
-/

noncomputable section
namespace QuantumChannelStein.Pseudoinverse

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reconstructing `A` from a positive sandwich transfers its operator-norm
bound back to a scalar domination by `B`. -/
theorem sandwich_norm_domination (A B R S : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hR : R.IsHermitian) (hS : S.IsHermitian)
    (hSS : S * S = B) (hrec : S * (R * A * R) * S = A) :
    (‖R * A * R‖ • B - A).PosSemidef := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  have hC : (R * A * R).PosSemidef := by
    simpa only [hR.eq] using hA.mul_mul_conjTranspose_same R
  have hle : R * A * R ≤ ‖R * A * R‖ • (1 : Matrix ι ι ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hC.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
  have hp : (‖R * A * R‖ • (1 : Matrix ι ι ℂ) - R * A * R).PosSemidef := hle
  have hs := hp.mul_mul_conjTranspose_same S
  simpa only [hS.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hSS, hrec] using hs

omit [DecidableEq ι] in
/-- Equal positive trace forces every PSD domination constant to be at
least one. This includes unnormalized Choi matrices. -/
theorem one_le_of_domination_of_trace_eq (A B : Matrix ι ι ℂ) (c : ℝ)
    (h : (c • B - A).PosSemidef) (htr : A.trace = B.trace) (hpos : 0 < B.trace.re) :
    1 ≤ c := by
  have hre := (Complex.nonneg_iff.mp h.trace_nonneg).1
  simp only [Matrix.trace_sub, Matrix.trace_smul, htr, Complex.sub_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hre
  nlinarith

/-- A trace-preserving channel's unnormalized Choi matrix has trace equal
to its input dimension. -/
theorem choi_trace {n m : ℕ} (Φ : KrausChannel n m) : Φ.choi.trace = (n : ℂ) := by
  have h := congrArg Matrix.trace Φ.traceOutput_choi
  simpa only [Matrix.trace, Matrix.diag, KrausChannel.traceOutput,
    Fintype.sum_prod_type, Matrix.one_apply_eq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using h

/-- The explicit finite-dimensional pseudoinverse norm constant.
The inverse square root is the actual finite spectral function, zero
precisely on the kernel of the reference matrix. -/
def dominationConstant (A B : Matrix ι ι ℂ) (hB : B.PosSemidef) : ℝ :=
  ‖inverseSqrt B hB * A * inverseSqrt B hB‖

/-- The norm formula uses exactly the positive square root of the actual
Moore–Penrose pseudoinverse. -/
theorem dominationConstant_eq_sqrt_pseudoinverse (A B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    dominationConstant A B hB =
      ‖CFC.sqrt (pseudoinverse B hB) * A * CFC.sqrt (pseudoinverse B hB)‖ := by
  rw [sqrt_pseudoinverse]
  rfl

theorem dominationConstant_nonneg (A B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    0 ≤ dominationConstant A B hB := norm_nonneg _

/-- The exact pseudoinverse norm is a valid domination constant whenever
the supports are nested, including for singular matrices. -/
theorem dominationConstant_domination (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    (dominationConstant A B hB • B - A).PosSemidef := by
  exact sandwich_norm_domination A B (inverseSqrt B hB) (root B hB) hA
    (inverseSqrt_isHermitian B hB) (root_isHermitian B hB)
    (root_mul_root B hB) (reconstruct_of_ker_le A B hA hB hker)

/-- Equal positive trace gives the required lower bound of one for the
explicit norm constant. -/
theorem one_le_dominationConstant (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin)
    (htr : A.trace = B.trace) (hpos : 0 < B.trace.re) :
    1 ≤ dominationConstant A B hB :=
  one_le_of_domination_of_trace_eq A B _
    (dominationConstant_domination A B hA hB hker) htr hpos

/-- The paper's explicit Choi pseudoinverse norm constant. -/
def choiConstant {n m : ℕ} (Φ Ψ : KrausChannel n m) : ℝ :=
  dominationConstant Φ.choi Ψ.choi Ψ.choi_positive

/-- The displayed Choi constant has the paper's pseudoinverse-square-root
sandwich form in the Hilbert operator norm. -/
theorem choiConstant_eq_sqrt_pseudoinverse {n m : ℕ} (Φ Ψ : KrausChannel n m) :
    choiConstant Φ Ψ =
      ‖CFC.sqrt (pseudoinverse Ψ.choi Ψ.choi_positive) * Φ.choi *
        CFC.sqrt (pseudoinverse Ψ.choi Ψ.choi_positive)‖ :=
  dominationConstant_eq_sqrt_pseudoinverse _ _ _

theorem choiConstant_nonneg {n m : ℕ} (Φ Ψ : KrausChannel n m) :
    0 ≤ choiConstant Φ Ψ := dominationConstant_nonneg _ _ _

/-- The explicit Choi norm yields actual CP domination. -/
theorem cpLe_choiConstant {n m : ℕ} (Φ Ψ : KrausChannel n m)
    (hker : LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) :
    MatrixMap.CPLe Φ.toLinearMap (((choiConstant Φ Ψ : ℝ) : ℂ) • Ψ.toLinearMap) := by
  apply (ChannelEntropy.choi_domination_iff_cpLe Φ Ψ _).mp
  exact dominationConstant_domination Φ.choi Ψ.choi Φ.choi_positive Ψ.choi_positive hker

/-- For nonzero input dimension, the exact Choi constant is at least one. -/
theorem one_le_choiConstant {n m : ℕ} (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (hker : LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) :
    1 ≤ choiConstant Φ Ψ := by
  apply one_le_dominationConstant Φ.choi Ψ.choi Φ.choi_positive Ψ.choi_positive hker
  · rw [choi_trace, choi_trace]
  · rw [choi_trace]
    exact_mod_cast hn

/-- The actual one-use channel divergence is bounded by the logarithm
of the explicit Choi pseudoinverse norm. -/
theorem channelD_le_log2_choiConstant {n m : ℕ} (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (hker : LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) :
    ChannelEntropy.channelD Φ Ψ ≤ (Real.logb 2 (choiConstant Φ Ψ) : EReal) :=
  ChannelEntropy.channelD_le_log2_of_cpLe Φ Ψ _ (one_le_choiConstant Φ Ψ hn hker)
    (cpLe_choiConstant Φ Ψ hker)

/-- The exact tensor-power supremum rate obeys the explicit-constant bound. -/
theorem regularizedD_le_log2_choiConstant {n m : ℕ} (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (hker : LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) :
    ChannelEntropy.regularizedD Φ Ψ ≤ (Real.logb 2 (choiConstant Φ Ψ) : EReal) :=
  ChannelEntropy.regularizedD_le_log2_of_cpLe Φ Ψ _ (one_le_choiConstant Φ Ψ hn hker)
    (cpLe_choiConstant Φ Ψ hker)

/-- All finite-block bounds with the actual explicit pseudoinverse
constant, rather than an existential or assumed scalar. -/
theorem tensorPower_bounds_choiConstant {n m : ℕ} (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (hker : LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) (k : ℕ) :
    0 ≤ ChannelEntropy.channelD (Φ.tensorPower k) (Ψ.tensorPower k) ∧
      ChannelEntropy.channelD (Φ.tensorPower k) (Ψ.tensorPower k) ≤
        ((k : ℝ) : EReal) * ChannelEntropy.regularizedD Φ Ψ ∧
      ((k : ℝ) : EReal) * ChannelEntropy.regularizedD Φ Ψ ≤
        ((k : ℝ) : EReal) * (Real.logb 2 (choiConstant Φ Ψ) : EReal) :=
  ChannelEntropy.tensorPower_bounds_of_cpLe Φ Ψ hn _ (one_le_choiConstant Φ Ψ hn hker)
    (cpLe_choiConstant Φ Ψ hker) k

end QuantumChannelStein.Pseudoinverse
