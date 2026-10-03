import QuantumChannelStein.OperationalTesting
import QuantumChannelStein.TestingSDP

/-! Compactness and actual minimum attainment of the literal optimization (2.4). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ParallelTestingAttainment
open Matrix ChannelEntropy OperationalTesting
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

/-- The literal unit-pure input sphere, in its finite-dimensional Euclidean space. -/
def pureSphere (a : ℕ) : Set (EuclideanSpace ℂ (Fin a × Fin a)) := {ψ | ‖ψ‖ = 1}

/-- The actual matrix effect interval: positive matrix and positive complement. -/
def effectSet (d : ℕ) : Set (Operator d) := {T | T.PosSemidef ∧ (1 - T).PosSemidef}

theorem isCompact_pureSphere (a : ℕ) : IsCompact (pureSphere a) := by
  apply Metric.isCompact_of_isClosed_isBounded
    (isClosed_eq continuous_norm continuous_const)
  exact isBounded_iff_forall_norm_le.mpr ⟨1, fun ψ hψ => hψ.le⟩

theorem isClosed_effectSet (d : ℕ) : IsClosed (effectSet d) := by
  letI : CStarAlgebra (Operator d) := CStarAlgebra.mk
  have hc : IsClosed {T : Operator d | 0 ≤ T ∧ T ≤ 1} :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_id continuous_const)
  simpa only [effectSet, Matrix.nonneg_iff_posSemidef, Matrix.le_iff, sub_zero] using hc

theorem isCompact_effectSet (d : ℕ) : IsCompact (effectSet d) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_effectSet d)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  intro T hT
  exact (show Effect d from ⟨T, hT.1, hT.2⟩).norm_matrix_le_one

/-- Born trace polynomial on the ambient vector/matrix product, prior to constraints. -/
def rawAcceptance {a b : ℕ} (Φ : KrausChannel a b)
    (x : EuclideanSpace ℂ (Fin a × Fin a) × Operator (a * b)) : ℝ :=
  (x.2 * Matrix.reindex finProdFinEquiv finProdFinEquiv (Φ.amplify a (pureMatrix x.1))).trace.re

@[simp] theorem rawAcceptance_test {a b : ℕ} (Φ : KrausChannel a b)
    (ψ : UnitPureInput a a) (T : Effect (a * b)) :
    rawAcceptance Φ (ψ.val, T.matrix) = T.probability (pureOutput Φ ψ) := rfl

theorem continuous_pureMatrix {ι : Type*} [Fintype ι] :
    Continuous (pureMatrix : EuclideanSpace ℂ ι → Matrix ι ι ℂ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun ψ : EuclideanSpace ℂ ι => ψ i * star (ψ j))
  fun_prop

theorem continuous_rawAcceptance {a b : ℕ} (Φ : KrausChannel a b) :
    Continuous (rawAcceptance Φ) := by
  have hp := continuous_pureMatrix (ι := Fin a × Fin a)
  have ha : Continuous (fun ψ : EuclideanSpace ℂ (Fin a × Fin a) => Φ.amplify a (pureMatrix ψ)) := by
    unfold KrausChannel.amplify
    fun_prop
  have hr : Continuous (fun ψ : EuclideanSpace ℂ (Fin a × Fin a) =>
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Φ.amplify a (pureMatrix ψ))) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun ψ : EuclideanSpace ℂ (Fin a × Fin a) =>
      Φ.amplify a (pureMatrix ψ) (finProdFinEquiv.symm i) (finProdFinEquiv.symm j))
    fun_prop
  have hm : Continuous (fun x : EuclideanSpace ℂ (Fin a × Fin a) × Operator (a * b) =>
      x.2 * Matrix.reindex finProdFinEquiv finProdFinEquiv (Φ.amplify a (pureMatrix x.1))) :=
    continuous_snd.mul (hr.comp continuous_fst)
  unfold rawAcceptance Matrix.trace Matrix.diag
  fun_prop

/-- Exactly the paper's pure fixed-reference feasible pairs, in raw coordinates. -/
def feasibleSet {a b : ℕ} (Φ : KrausChannel a b) (ε : ℝ) :
    Set (EuclideanSpace ℂ (Fin a × Fin a) × Operator (a * b)) :=
  (pureSphere a ×ˢ effectSet (a * b)) ∩ {x | 1 - ε ≤ rawAcceptance Φ x}

/-- The literal fixed-error feasible set is compact. -/
theorem isCompact_feasibleSet {a b : ℕ} (Φ : KrausChannel a b) (ε : ℝ) :
    IsCompact (feasibleSet Φ ε) :=
  ((isCompact_pureSphere a).prod (isCompact_effectSet (a * b))).inter_right
    (isClosed_le continuous_const (continuous_rawAcceptance Φ))

theorem feasibleSet_nonempty {a b : ℕ} (Φ : KrausChannel a b) (ha : 0 < a)
    (ε : ℝ) (hε : 0 ≤ ε) : (feasibleSet Φ ε).Nonempty := by
  let ψ := unitProductInput ha
  let T := acceptAll (a * b)
  refine ⟨(ψ.val, T.matrix), ⟨⟨ψ.property, T.positive, T.complement_positive⟩, ?_⟩⟩
  change 1 - ε ≤ T.probability (pureOutput Φ ψ)
  rw [acceptAll_probability]
  linarith

/-- An actual minimum exists without assuming an optimizer or compactness. -/
theorem exists_minimizing_pure_test {a b : ℕ} (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ ψ : UnitPureInput a a, ∃ T : Effect (a * b),
      1 - ε ≤ T.probability (pureOutput Φ ψ) ∧
      ∀ ψ' : UnitPureInput a a, ∀ T' : Effect (a * b),
        1 - ε ≤ T'.probability (pureOutput Φ ψ') →
        T.probability (pureOutput Ψ ψ) ≤ T'.probability (pureOutput Ψ ψ') := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_feasibleSet Φ ε).exists_isMinOn
    (feasibleSet_nonempty Φ ha ε hε) (continuous_rawAcceptance Ψ).continuousOn
  let ψ : UnitPureInput a a := ⟨x.1, hx.1.1⟩
  let T : Effect (a * b) := ⟨x.2, hx.1.2.1, hx.1.2.2⟩
  refine ⟨ψ, T, hx.2, ?_⟩
  intro ψ' T' htest
  exact hmin (show (ψ'.val, T'.matrix) ∈ feasibleSet Φ ε from
    ⟨⟨ψ'.property, T'.positive, T'.complement_positive⟩, htest⟩)

/-- The infimum in equation (2.4) is attained by an actual admissible pure test. -/
theorem parallelPureBeta_attained {a b : ℕ} (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ ψ : UnitPureInput (a ^ k) (a ^ k), ∃ T : Effect (a ^ k * b ^ k),
      1 - ε ≤ T.probability (pureOutput (Φ.tensorPower k) ψ) ∧
      parallelPureBeta Φ Ψ k ε = ENNReal.ofReal (T.probability (pureOutput (Ψ.tensorPower k) ψ)) := by
  obtain ⟨ψ, T, hp, hmin⟩ := exists_minimizing_pure_test (Φ.tensorPower k) (Ψ.tensorPower k)
    (pow_pos ha k) ε hε
  refine ⟨ψ, T, hp, le_antisymm ?_ ?_⟩
  · exact iInf_le_of_le ⟨(ψ, T), hp⟩ le_rfl
  · apply le_iInf
    intro test
    exact ENNReal.ofReal_le_ofReal (hmin test.val.1 test.val.2 test.property)

end QuantumChannelStein.ParallelTestingAttainment
