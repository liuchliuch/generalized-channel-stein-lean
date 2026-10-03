import GeneralizedChannelStein.LocalExpansion
import GeneralizedChannelStein.CompactConvexHull
import Mathlib.Analysis.Convex.Integral

/-! # Compact local contraction atoms and finite expansion extraction -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.LocalExpansion
open QuantumChannelStein Matrix MeasureTheory
open scoped ENNReal
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The literal support embedding is a complex-linear map. -/
def embedLinear (S : Finset (Fin k)) :
    Matrix (LocalIndex ι S) (LocalIndex ι S) ℂ →ₗ[ℂ] Block ι k where
  toFun := embed S
  map_add' B C := by ext i j; simp [embed,Matrix.add_kronecker,Matrix.reindex_apply]
  map_smul' c B := by ext i j; simp [embed,Matrix.smul_kronecker,Matrix.reindex_apply]

theorem supportedOn_iff_range (S : Finset (Fin k)) (A : Block ι k) :
    SupportedOn S A ↔ A ∈ LinearMap.range (embedLinear (ι := ι) S) := by
  constructor
  · rintro ⟨B,rfl⟩
    exact ⟨B,rfl⟩
  · rintro ⟨B,hB⟩
    exact ⟨B,hB.symm⟩

theorem isClosed_supportedOn (S : Finset (Fin k)) :
    IsClosed {A : Block ι k | SupportedOn S A} := by
  have h : {A : Block ι k | SupportedOn S A} = (LinearMap.range (embedLinear (ι := ι) S) : Set (Block ι k)) := by
    ext A
    exact supportedOn_iff_range S A
  rw [h]
  exact Submodule.closed_of_finiteDimensional _

/-- Actual unit-ball operators with a chosen literal tensor-site support. -/
def supportedBall (S : Finset (Fin k)) : Set (Block ι k) := {A | SupportedOn S A ∧ ‖A‖ ≤ 1}

theorem isCompact_supportedBall (S : Finset (Fin k)) : IsCompact (supportedBall (ι := ι) S) := by
  have h : supportedBall (ι := ι) S = {A | SupportedOn S A} ∩ Metric.closedBall 0 1 := by
    ext A
    simp [supportedBall,Metric.mem_closedBall,dist_zero_right]
  rw [h]
  exact (isCompact_closedBall (0:Block ι k) 1).inter_left (isClosed_supportedOn S)

/-- Finite union over all subsets of cardinality at most R. -/
def localAtoms (R : ℕ) : Set (Block ι k) :=
  ⋃ S : {S : Finset (Fin k) // S.card ≤ R}, supportedBall (ι := ι) S.val

theorem isCompact_localAtoms (R : ℕ) : IsCompact (localAtoms (ι := ι) (k := k) R) := by
  apply isCompact_iUnion
  intro S
  exact isCompact_supportedBall S.val

theorem zero_mem_localAtoms (R : ℕ) : (0:Block ι k) ∈ localAtoms R := by
  apply Set.mem_iUnion.mpr
  exact ⟨⟨∅,by simp⟩,supportedOn_zero _,by simp⟩

theorem supportedOn_smul (S : Finset (Fin k)) (A : Block ι k) (hA : SupportedOn S A) (c : ℂ) :
    SupportedOn S (c • A) := by
  obtain ⟨B,rfl⟩ := hA
  refine ⟨c • B,?_⟩
  exact (map_smul (embedLinear (ι := ι) S) c B).symm

theorem phase_mem_localAtoms (R : ℕ) (A : Block ι k) (hA : A ∈ localAtoms R)
    (c : ℂ) (hc : ‖c‖ ≤ 1) : c • A ∈ localAtoms R := by
  obtain ⟨S,hS⟩ := Set.mem_iUnion.mp hA
  apply Set.mem_iUnion.mpr
  refine ⟨S,supportedOn_smul S.val A hS.1 c,?_⟩
  rw [norm_smul]
  exact (mul_le_mul hc hS.2 (norm_nonneg A) (by norm_num)).trans_eq (by norm_num)

def unitPhase (c : ℂ) : ℂ := c/(‖c‖:ℂ)

theorem norm_unitPhase_le (c : ℂ) : ‖unitPhase c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [unitPhase,hc]
  · rw [unitPhase,norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg c),div_self (norm_ne_zero_iff.mpr hc)]

theorem norm_weight_phase (c : ℂ) (B : ℝ) (A : Block ι k) :
    (‖c‖/B) • (unitPhase c • A) = B⁻¹ • (c • A) := by
  by_cases hc : c = 0
  · simp [hc,unitPhase]
  · have hn : (‖c‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)
    change ((‖c‖/B:ℝ):ℂ) • ((c/(‖c‖:ℂ)) • A) = ((B⁻¹:ℝ):ℂ) • (c • A)
    rw [smul_smul,smul_smul,Complex.ofReal_div,Complex.ofReal_inv]
    congr 1
    field_simp

/-- Bounded coefficient mass puts the explicit operator in a fixed compact convex hull. -/
theorem expansion_scaled_mem_hull (E : Expansion ι k) (R : ℕ) (hsize : E.HasSize R)
    (B : ℝ) (hB : 0 < B) (hcost : E.cost ≤ B) :
    B⁻¹ • E.value ∈ convexHull ℝ (localAtoms R) := by
  classical
  let w : Option E.terms → ℝ := Option.elim' (1-E.cost/B) (fun i => ‖E.coeff i‖/B)
  let z : Option E.terms → Block ι k := Option.elim' 0 (fun i => unitPhase (E.coeff i) • E.factor i)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    cases i with
    | none => exact sub_nonneg.mpr ((div_le_one hB).mpr hcost)
    | some i => exact div_nonneg (norm_nonneg _) hB.le
  have hsum : ∑ i, w i = 1 := by
    simp only [w,Fintype.sum_option,Option.elim',← Finset.sum_div]
    change 1-E.cost/B+E.cost/B=1
    ring
  have hz : ∀ i, z i ∈ convexHull ℝ (localAtoms R) := by
    intro i
    apply subset_convexHull
    cases i with
    | none => exact zero_mem_localAtoms R
    | some i =>
      apply phase_mem_localAtoms R (E.factor i) _ _ (norm_unitPhase_le _)
      exact Set.mem_iUnion.mpr ⟨⟨E.sites i,hsize i⟩,E.supported i,E.contraction i⟩
  have hm := (convex_convexHull ℝ (localAtoms (ι := ι) (k := k) R)).sum_mem
    (fun i _ => hw i) hsum (fun i _ => hz i)
  have heq : (∑ i, w i • z i) = B⁻¹ • E.value := by
    simp only [w,z,Fintype.sum_option,Option.elim',smul_zero,zero_add,norm_weight_phase]
    rw [← Finset.smul_sum]
    rfl
  rwa [heq] at hm

/-- Caratheodory yields actual finite coefficients and support witnesses after integration. -/
theorem exists_expansion_of_scaled_hull (P : Block ι k) (R : ℕ) (B : ℝ) (hB : 0 < B)
    (hP : B⁻¹ • P ∈ convexHull ℝ (localAtoms R)) :
    ∃ E : Expansion ι k, E.value=P ∧ E.HasSize R ∧ E.cost ≤ B := by
  classical
  obtain ⟨m,_,w,z,hw,hsum,hz,hvalue⟩ := CompactConvexHull.exists_convex_sum hP
  have hs : ∀ i : Fin m, ∃ S : Finset (Fin k), S.card ≤ R ∧ SupportedOn S (z i) ∧ ‖z i‖ ≤ 1 := by
    intro i
    obtain ⟨S,hS⟩ := Set.mem_iUnion.mp (hz i)
    exact ⟨S.val,S.property,hS.1,hS.2⟩
  choose S hS using hs
  let E : Expansion ι k := {
    terms := Fin m
    finiteTerms := inferInstance
    coeff := fun i => (B*w i:ℝ)
    factor := z
    sites := S
    supported := fun i => (hS i).2.1
    contraction := fun i => (hS i).2.2 }
  refine ⟨E,?_,fun i => (hS i).1,?_⟩
  · change (∑ i, (B*w i) • z i) = P
    simp only [SemigroupAction.mul_smul,← Finset.smul_sum]
    rw [hvalue,smul_smul,mul_inv_cancel₀ hB.ne',one_smul]
  · change ∑ i, ‖((B*w i:ℝ):ℂ)‖ ≤ B
    simp only [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hB.le (hw _)),← Finset.mul_sum,hsum,mul_one,le_refl]

/-- A genuine Bochner average of uniformly bounded local expansions has a finite local expansion. -/
theorem exists_expansion_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (P : Ω → Block ι k) (hP : MeasureTheory.Integrable P μ)
    (R : ℕ) (B : ℝ) (hB : 0 < B)
    (hlocal : ∀ᵐ x ∂μ, B⁻¹ • P x ∈ convexHull ℝ (localAtoms R)) :
    ∃ E : Expansion ι k, E.value = ∫ x, P x ∂μ ∧ E.HasSize R ∧ E.cost ≤ B := by
  apply exists_expansion_of_scaled_hull _ R B hB
  have hclosed : IsClosed (convexHull ℝ (localAtoms (ι := ι) (k := k) R)) :=
    (CompactConvexHull.isCompact_convexHull (isCompact_localAtoms R)).isClosed
  have hi := (convex_convexHull ℝ (localAtoms (ι := ι) (k := k) R)).integral_mem
    hclosed hlocal (hP.smul B⁻¹)
  simpa only [MeasureTheory.integral_smul] using hi

end GeneralizedChannelStein.LocalExpansion
