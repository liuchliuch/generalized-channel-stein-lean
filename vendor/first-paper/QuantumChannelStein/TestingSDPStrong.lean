import QuantumChannelStein.TestingSDP
import QuantumChannelStein.DualRepair
import QuantumChannelStein.External.Minimax
import Mathlib.Analysis.Convex.Topology

/-!
# Compact finite-witness minimax for channel-testing duality

An unbounded positive multiplier cone is handled by a finite open subcover:
only finitely many witnesses are needed on the compact relaxed primal domain.
Their convex hull is compact, so the bounded real-valued Sion theorem applies.
-/

set_option maxHeartbeats 1000000
noncomputable section
namespace QuantumChannelStein.TestingSDPStrong
open Filter Set
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

/-- Pointwise strict separating witnesses in a convex set can be replaced by
one uniform witness, with an arbitrarily prescribed strict margin. The proof
uses a finite witness hull, so no boundedness of the original witness set is
assumed. -/
theorem exists_uniform_bound_of_pointwise
    {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    {S : Set M} {T : Set N} {f : N → M → ℝ} {s r : ℝ}
    (hS : IsCompact S) (hSne : S.Nonempty) (hSc : Convex ℝ S) (hTc : Convex ℝ T)
    (hcont : Continuous (fun p : N × M => f p.1 p.2))
    (hconv : ∀ x ∈ S, QuasiconvexOn ℝ T (fun y => f y x))
    (hconc : ∀ y ∈ T, QuasiconcaveOn ℝ S (f y))
    (hsr : s < r) (hpoint : ∀ x ∈ S, ∃ y ∈ T, f y x < s) :
    ∃ y ∈ T, ∀ x ∈ S, f y x < r := by
  classical
  let U : T → Set M := fun y => {x | f y x < s}
  have hopen : ∀ y, IsOpen (U y) := by
    intro y
    exact isOpen_lt (hcont.comp (continuous_const.prodMk continuous_id)) continuous_const
  have hcover : S ⊆ ⋃ y : T, U y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hpoint x hx
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  obtain ⟨ys, hys⟩ := hS.elim_finite_subcover U hopen hcover
  let C : Set N := convexHull ℝ (Subtype.val '' (ys : Set T))
  have hCc : Convex ℝ C := convex_convexHull _ _
  have hC : IsCompact C := (ys.finite_toSet.image Subtype.val).isCompact_convexHull ℝ
  have hCT : C ⊆ T := convexHull_min (by rintro _ ⟨y, _, rfl⟩; exact y.property) hTc
  have hwitness : ∀ x ∈ S, ∃ y : C, f y x < s := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hys hx)
    obtain ⟨hyfin, hvalue⟩ := mem_iUnion.mp hy
    exact ⟨⟨y, subset_convexHull ℝ _ ⟨y, hyfin, rfl⟩⟩, hvalue⟩
  have hCne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    obtain ⟨y, _⟩ := hwitness x hx
    exact ⟨y, y.property⟩
  letI : Nonempty S := hSne.to_subtype
  letI : Nonempty C := hCne.to_subtype
  have hba : BddAbove (Set.image2 f C S) := by
    rw [← Set.image_prod]
    exact (hC.prod hS).bddAbove_image hcont.continuousOn
  have hbb : BddBelow (Set.image2 f C S) := by
    rw [← Set.image_prod]
    exact (hC.prod hS).bddBelow_image hcont.continuousOn
  have heq : (⨅ y : C, ⨆ x : S, f y x) = (⨆ x : S, ⨅ y : C, f y x) := by
    apply sion_minimax (f := f) (S := C) (T := S)
    · intro x hx
      exact (hcont.comp (continuous_id.prodMk (continuous_const (y := x)))).lowerSemicontinuous.lowerSemicontinuousOn C
    · exact hC
    · exact hCne
    · exact hSne
    · intro y hy
      exact (hcont.comp ((continuous_const (y := y)).prodMk continuous_id)).upperSemicontinuous.upperSemicontinuousOn S
    · intro x hx
      exact (hconv x hx).subset hCT hCc
    · intro y hy
      exact hconc y (hCT hy)
    · exact hSc
    · exact hCc
    · exact hba
    · exact hbb
  have hsup : (⨆ x : S, ⨅ y : C, f y x) ≤ s := by
    apply ciSup_le
    intro x
    obtain ⟨y, hy⟩ := hwitness x x.property
    have hbounded : BddBelow (Set.range (fun y : C => f y x)) := by
      apply hbb.mono
      rintro _ ⟨y, rfl⟩
      exact ⟨y, y.property, x, x.property, rfl⟩
    exact (ciInf_le hbounded y).trans hy.le
  have hinf : (⨅ y : C, ⨆ x : S, f y x) < r := heq ▸ hsup.trans_lt hsr
  obtain ⟨y, hy⟩ := exists_lt_of_ciInf_lt hinf
  refine ⟨y, hCT y.property, ?_⟩
  intro x hx
  have hbounded : BddAbove (Set.range (fun x : S => f y x)) := by
    apply hba.mono
    rintro _ ⟨x, rfl⟩
    exact ⟨y, y.property, x, x.property, rfl⟩
  exact (le_ciSup hbounded (⟨x, hx⟩ : S)).trans_lt hy

open TestingSDP

/-- Compact relaxed primal domain: a density matrix and an independent effect.
The original constraint is imposed by the positive multiplier. -/
def relaxedPrimalSet (a b : ℕ) : Set (Operator a × BipartiteOperator a b) :=
  {p | p.1.PosSemidef ∧ p.1.trace = 1 ∧ p.2.PosSemidef ∧ (1 - p.2).PosSemidef}

/-- The actual matrix Lagrangian, with a real trace objective. -/
def lagrangian {a b : ℕ} (Delta Y : BipartiteOperator a b)
    (p : Operator a × BipartiteOperator a b) : ℝ :=
  (Delta * p.2).trace.re + (Y * ((p.1 ⊗ₖ (1 : Operator b)) - p.2)).trace.re

/-- Joint continuity of the finite matrix Lagrangian. -/
theorem continuous_lagrangian {a b : ℕ} (Delta : BipartiteOperator a b) :
    Continuous (fun p : BipartiteOperator a b × (Operator a × BipartiteOperator a b) =>
      lagrangian Delta p.1 p.2) := by
  unfold lagrangian Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.sub_apply, Matrix.kroneckerMap_apply]
  fun_prop

/-- Closedness of the relaxed density/effect domain. -/
theorem isClosed_relaxedPrimalSet (a b : ℕ) : IsClosed (relaxedPrimalSet a b) := by
  letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
  letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
  have htrace : Continuous (fun p : Operator a × BipartiteOperator a b => p.1.trace) := by
    unfold Matrix.trace
    fun_prop
  have hclosed : IsClosed {p : Operator a × BipartiteOperator a b |
      0 ≤ p.1 ∧ p.1.trace = 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_eq htrace continuous_const).inter
        ((isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_const)))
  simpa only [relaxedPrimalSet, Matrix.nonneg_iff_posSemidef, Matrix.le_iff, sub_zero] using hclosed

/-- Compactness of the relaxed density/effect domain. -/
theorem isCompact_relaxedPrimalSet (a b : ℕ) : IsCompact (relaxedPrimalSet a b) := by
  letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_relaxedPrimalSet a b)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  intro p hp
  have homega : ‖p.1‖ ≤ 1 := state_norm_le_one ⟨p.1, hp.1, hp.2.1⟩
  have hQ : ‖p.2‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg p.2 hp.2.2.1.nonneg).mpr hp.2.2.2
  exact max_le homega hQ

/-- Convexity of the relaxed density/effect domain. -/
theorem convex_relaxedPrimalSet (a b : ℕ) : Convex ℝ (relaxedPrimalSet a b) := by
  intro p hp q hq r s hr hs hrs
  refine ⟨(hp.1.smul hr).add (hq.1.smul hs), ?_,
    (hp.2.2.1.smul hr).add (hq.2.2.1.smul hs), ?_⟩
  · change (r • p.1 + s • q.1).trace = 1
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hp.2.1, hq.2.1,
      ← add_smul, hrs, one_smul]
  · have hpos := (hp.2.2.2.smul hr).add (hq.2.2.2.smul hs)
    convert hpos using 1
    change 1 - (r • p.2 + s • q.2) = r • (1 - p.2) + s • (1 - q.2)
    calc
      _ = (r + s) • (1 : BipartiteOperator a b) - (r • p.2 + s • q.2) := by rw [hrs, one_smul]
      _ = _ := by module

/-- Nonemptiness of the relaxed domain from one density matrix. -/
theorem relaxedPrimalSet_nonempty {a : ℕ} (omega0 : State a) (b : ℕ) :
    (relaxedPrimalSet a b).Nonempty := by
  refine ⟨(omega0.matrix, 0), omega0.positive, omega0.trace_one, Matrix.PosSemidef.zero, ?_⟩
  simpa using (Matrix.PosSemidef.one : (1 : BipartiteOperator a b).PosSemidef)

/-- Affine dependence of the Lagrangian on the multiplier. -/
theorem lagrangian_mix_dual {a b : ℕ} (Delta Y Z : BipartiteOperator a b)
    (p : Operator a × BipartiteOperator a b) (r s : ℝ) (hrs : r + s = 1) :
    lagrangian Delta (r • Y + s • Z) p = r * lagrangian Delta Y p + s * lagrangian Delta Z p := by
  simp only [lagrangian, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  nlinarith [congrArg (fun t : ℝ => t * (Delta * p.2).trace.re) hrs]

/-- Linear dependence of the Lagrangian on the relaxed primal pair. -/
theorem lagrangian_mix_primal {a b : ℕ} (Delta Y : BipartiteOperator a b)
    (p q : Operator a × BipartiteOperator a b) (r s : ℝ) :
    lagrangian Delta Y (r • p + s • q) = r * lagrangian Delta Y p + s * lagrangian Delta Y q := by
  simp only [lagrangian, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul]
  ring

/-- Quasiconvexity in the positive multiplier cone. -/
theorem lagrangian_quasiconvex {a b : ℕ} (Delta : BipartiteOperator a b)
    (p : Operator a × BipartiteOperator a b) :
    QuasiconvexOn ℝ {Y : BipartiteOperator a b | Y.PosSemidef} (fun Y => lagrangian Delta Y p) := by
  apply ConvexOn.quasiconvexOn
  refine ⟨convex_positiveCone, ?_⟩
  intro Y _ Z _ r s _ _ hrs
  exact (lagrangian_mix_dual Delta Y Z p r s hrs).le

/-- Quasiconcavity in the compact relaxed primal domain. -/
theorem lagrangian_quasiconcave {a b : ℕ} (Delta Y : BipartiteOperator a b) :
    QuasiconcaveOn ℝ (relaxedPrimalSet a b) (lagrangian Delta Y) := by
  apply ConcaveOn.quasiconcaveOn
  refine ⟨convex_relaxedPrimalSet a b, ?_⟩
  intro p _ q _ r s _ _ _
  exact (lagrangian_mix_primal Delta Y p q r s).ge

/-- At every relaxed primal point, a positive multiplier makes the Lagrangian
strictly smaller than any strict upper bound on the genuine primal maximum. -/
theorem exists_pointwise_multiplier {a b : ℕ} (Delta : BipartiteOperator a b)
    (Pmax : PrimalFeasible a b)
    (hmax : ∀ P : PrimalFeasible a b, P.value Delta ≤ Pmax.value Delta)
    {c : ℝ} (hc : Pmax.value Delta < c)
    {p : Operator a × BipartiteOperator a b} (hp : p ∈ relaxedPrimalSet a b) :
    ∃ Y : BipartiteOperator a b, Y.PosSemidef ∧ lagrangian Delta Y p < c := by
  by_cases hscore : (Delta * p.2).trace.re < c
  · exact ⟨0, Matrix.PosSemidef.zero, by simpa [lagrangian] using hscore⟩
  have hnot : ¬ ((p.1 ⊗ₖ (1 : Operator b)) - p.2).PosSemidef := by
    intro hpos
    let P : PrimalFeasible a b := ⟨⟨p.1, hp.1, hp.2.1⟩, p.2, hp.2.2.1, hpos⟩
    have h := hmax P
    exact hscore (h.trans_lt hc)
  have hherm : ((p.1 ⊗ₖ (1 : Operator b)) - p.2).IsHermitian :=
    (kronecker_one_positive hp.1).isHermitian.sub hp.2.2.1.isHermitian
  obtain ⟨Y, hY, hneg⟩ := exists_positive_negative_trace_of_not_positive hherm hnot
  rw [Matrix.trace_mul_comm] at hneg
  let v := (Y * ((p.1 ⊗ₖ (1 : Operator b)) - p.2)).trace.re
  let t := ((Delta * p.2).trace.re - c + 1) / (-v)
  have ht : 0 < t := div_pos (by linarith) (neg_pos.mpr hneg)
  refine ⟨t • Y, hY.smul ht.le, ?_⟩
  have htprod : t * v = -((Delta * p.2).trace.re - c + 1) := by
    dsimp [t]
    field_simp [show v ≠ 0 from ne_of_lt hneg]
  simp only [lagrangian, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  change (Delta * p.2).trace.re + t * v < c
  linarith

/-- The unbounded multiplier cone admits an actual uniform Lagrangian witness
for every strict upper bound on the attained primal optimum. -/
theorem exists_uniform_lagrangian_bound {a b : ℕ} (omega0 : State a)
    (Delta : BipartiteOperator a b) (Pmax : PrimalFeasible a b)
    (hmax : ∀ P : PrimalFeasible a b, P.value Delta ≤ Pmax.value Delta)
    {r : ℝ} (hr : Pmax.value Delta < r) :
    ∃ Y : BipartiteOperator a b, Y.PosSemidef ∧
      ∀ omega : State a, ∀ Q : BipartiteOperator a b,
        Q.PosSemidef → (1 - Q).PosSemidef → lagrangian Delta Y (omega.matrix, Q) < r := by
  obtain ⟨s, hps, hsr⟩ := exists_between hr
  obtain ⟨Y, hY, hbound⟩ := exists_uniform_bound_of_pointwise
    (isCompact_relaxedPrimalSet a b) (relaxedPrimalSet_nonempty omega0 b)
    (convex_relaxedPrimalSet a b) convex_positiveCone (continuous_lagrangian Delta)
    (fun p _ => lagrangian_quasiconvex Delta p) (fun Y _ => lagrangian_quasiconcave Delta Y)
    hsr (fun _ hp => exists_pointwise_multiplier Delta Pmax hmax hps hp)
  refine ⟨Y, hY, ?_⟩
  intro omega Q hQ hQc
  exact hbound (omega.matrix, Q) ⟨omega.positive, omega.trace_one, hQ, hQc⟩

/-- Strong duality with an actual dual optimizer at any attained primal
maximum. The proof combines finite-witness minimax with the proved spectral
positive-part repair; no duality assertion is assumed. -/
theorem exists_dual_attaining_primal_max {a b : ℕ} (omega0 : State a)
    (Delta : BipartiteOperator a b) (hDelta : Delta.IsHermitian)
    (Pmax : PrimalFeasible a b)
    (hmax : ∀ P : PrimalFeasible a b, P.value Delta ≤ Pmax.value Delta) :
    ∃ D : DualFeasible Delta, D.value = Pmax.value Delta := by
  obtain ⟨Dmin, hmin⟩ := exists_dual_minimizer_of_hermitian Delta hDelta
  refine ⟨Dmin, le_antisymm ?_ (weak_duality Pmax Dmin)⟩
  by_contra hnot
  have hgap : Pmax.value Delta < Dmin.value := lt_of_not_ge hnot
  obtain ⟨r, hpr, hrd⟩ := exists_between hgap
  obtain ⟨Y, hY, hbound⟩ := exists_uniform_lagrangian_bound omega0 Delta Pmax hmax hpr
  obtain ⟨D, hD⟩ := repair_lagrange_multiplier omega0 Delta Y hDelta hY r
    (fun omega Q hQ hQc => (hbound omega Q hQ hQc).le)
  have h := (hmin D).trans hD
  exact (not_lt_of_ge h) hrd

/-- Attained primal/dual equality for the concrete matrix channel-testing SDP
of Lemma 4.1. Both optimizers and both extremal properties are supplied. -/
theorem exists_primal_dual_optimal_pair {a b : ℕ} (omega0 : State a)
    (Delta : BipartiteOperator a b) (hDelta : Delta.IsHermitian) :
    ∃ P : PrimalFeasible a b, ∃ D : DualFeasible Delta,
      P.value Delta = D.value ∧
      (∀ P' : PrimalFeasible a b, P'.value Delta ≤ P.value Delta) ∧
      (∀ D' : DualFeasible Delta, D.value ≤ D'.value) := by
  obtain ⟨P, hP⟩ := exists_primal_maximizer omega0 Delta
  obtain ⟨D, hD⟩ := exists_dual_attaining_primal_max omega0 Delta hDelta P hP
  refine ⟨P, D, hD.symm, hP, ?_⟩
  intro D'
  rw [hD]
  exact weak_duality P D'

/-- Equality of the primal supremum and dual infimum, with their feasible
sets defined by actual matrix inequalities. Attainment was established above. -/
theorem primalSup_eq_dualInf {a b : ℕ} (omega0 : State a)
    (Delta : BipartiteOperator a b) (hDelta : Delta.IsHermitian) :
    sSup (Set.range (fun P : PrimalFeasible a b => P.value Delta)) =
      sInf (Set.range (fun D : DualFeasible Delta => D.value)) := by
  obtain ⟨P, D, heq, hP, hD⟩ := exists_primal_dual_optimal_pair omega0 Delta hDelta
  have hgreat : IsGreatest (Set.range (fun P : PrimalFeasible a b => P.value Delta)) (P.value Delta) := by
    refine ⟨⟨P, rfl⟩, ?_⟩
    rintro _ ⟨P', rfl⟩
    exact hP P'
  have hleast : IsLeast (Set.range (fun D : DualFeasible Delta => D.value)) D.value := by
    refine ⟨⟨D, rfl⟩, ?_⟩
    rintro _ ⟨D', rfl⟩
    exact hD D'
  rw [hgreat.csSup_eq, hleast.csInf_eq, heq]

end QuantumChannelStein.TestingSDPStrong
