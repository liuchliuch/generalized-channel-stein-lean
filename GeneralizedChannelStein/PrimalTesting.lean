import GeneralizedChannelStein.CompositeTesting
import QuantumChannelStein.TestingSDPStrong

/-! # Exact compact convex tester coordinates for composite testing

The stored density in the inherited primal convention is the transpose of
paper's physical input density. This is a bijective relabeling, not omission of
the transpose. The same realized pure input/effect gives its Choi trace value
for every channel simultaneously, including singular input marginals.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy TestingSDP TestingPrimal
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

variable {a b : ℕ}

/-- Unrestricted real Choi trace pairing. -/
def testerValue (x : Operator a × BipartiteOperator a b) (C : BipartiteOperator a b) : ℝ :=
  (C * x.2).trace.re

/-- The compact convex tester feasible set at a specified target and error. -/
def testerSet (N : KrausChannel a b) (ε : ℝ) : Set (Operator a × BipartiteOperator a b) :=
  primalSet a b ∩ {x | 1-ε ≤ testerValue x N.choi}

theorem pureTestPrimal_acceptance (N : KrausChannel a b)
    (ψ : UnitPureInput a a) (T : Effect (a*b)) :
    (pureTestPrimal ψ T).value N.choi = T.probability (pureOutput N ψ) := by
  simpa only [channelDifference, zero_smul, sub_zero, pureScore, zero_mul] using
    pureTestPrimal_value N N 0 ψ T

/-- One realization represents all channel hypotheses, not just a fixed pair. -/
theorem exists_uniform_primal_realization (P : PrimalFeasible a b) :
    ∃ ψ : UnitPureInput a a, ∃ T : Effect (a*b),
      ∀ N : KrausChannel a b, T.probability (pureOutput N ψ) = P.value N.choi := by
  obtain ⟨T,hT⟩ := exists_effect_realizing_primal P
  refine ⟨densityInput P.omega,T,?_⟩
  intro N
  rw [← pureTestPrimal_acceptance]
  change (N.choi * (pureTestPrimal (densityInput P.omega) T).Q).trace.re = _
  rw [hT]
  rfl

theorem continuous_testerValue :
    Continuous (fun p : (Operator a × BipartiteOperator a b) × BipartiteOperator a b =>
      testerValue p.1 p.2) := by
  unfold testerValue Matrix.trace Matrix.diag
  fun_prop

theorem isCompact_testerSet (N : KrausChannel a b) (ε : ℝ) :
    IsCompact (testerSet N ε) := by
  apply (isCompact_primalSet a b).inter_right
  have h : Continuous (fun x : Operator a × BipartiteOperator a b => testerValue x N.choi) := by
    unfold testerValue Matrix.trace Matrix.diag
    fun_prop
  exact isClosed_le continuous_const h

theorem testerValue_mix_left (x y : Operator a × BipartiteOperator a b)
    (C : BipartiteOperator a b) (r s : ℝ) :
    testerValue (r • x + s • y) C = r * testerValue x C + s * testerValue y C := by
  simp [testerValue, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]

theorem testerValue_mix_right (x : Operator a × BipartiteOperator a b)
    (C D : BipartiteOperator a b) (r s : ℝ) :
    testerValue x (r • C + s • D) = r * testerValue x C + s * testerValue x D := by
  simp [testerValue, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]

theorem convex_primalSet (a b : ℕ) : Convex ℝ (primalSet a b) := by
  intro x hx y hy r s hr hs hrs
  refine ⟨(hx.1.smul hr).add (hy.1.smul hs), ?_,
    (hx.2.2.1.smul hr).add (hy.2.2.1.smul hs), ?_⟩
  · change (r • x.1 + s • y.1).trace = 1
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hx.2.1, hy.2.1,
      ← add_smul, hrs, one_smul]
  · convert (hx.2.2.2.smul hr).add (hy.2.2.2.smul hs) using 1
    change ((r • x.1 + s • y.1) ⊗ₖ (1 : Operator b)) - (r • x.2 + s • y.2) = _
    rw [Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker]
    module

theorem convex_testerSet (N : KrausChannel a b) (ε : ℝ) : Convex ℝ (testerSet N ε) := by
  intro x hx y hy r s hr hs hrs
  refine ⟨convex_primalSet a b hx.1 hy.1 hr hs hrs, ?_⟩
  change 1-ε ≤ testerValue (r • x + s • y) N.choi
  rw [testerValue_mix_left]
  calc
    1-ε = r*(1-ε)+s*(1-ε) := by rw [← add_mul, hrs, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx.2 hr)
      (mul_le_mul_of_nonneg_left hy.2 hs)

theorem testerSet_nonempty (N : KrausChannel a b) (ha : 0 < a)
    (ε : ℝ) (hε : 0 ≤ ε) : (testerSet N ε).Nonempty := by
  let P := pureTestPrimal (unitProductInput ha) (OperationalTesting.acceptAll (a*b))
  refine ⟨(P.omega.matrix,P.Q), P.mem_primalSet, ?_⟩
  change 1-ε ≤ P.value N.choi
  dsimp [P]
  rw [pureTestPrimal_acceptance, OperationalTesting.acceptAll_probability]
  linarith

/-- All raw feasible tester objectives are genuine probabilities on channels. -/
theorem testerValue_bounds (x : Operator a × BipartiteOperator a b)
    (hx : x ∈ primalSet a b) (N : KrausChannel a b) :
    0 ≤ testerValue x N.choi ∧ testerValue x N.choi ≤ 1 := by
  obtain ⟨ψ,T,h⟩ := exists_uniform_primal_realization (primalOfMem x hx)
  have heq : testerValue x N.choi = T.probability (pureOutput N ψ) := (h N).symm
  rw [heq]
  exact ⟨T.probability_nonneg _,T.probability_le_one _⟩

end GeneralizedChannelStein
