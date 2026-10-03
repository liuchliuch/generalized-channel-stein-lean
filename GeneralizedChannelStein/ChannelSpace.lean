import GeneralizedChannelStein.Families
import QuantumChannelStein.TestingSDP

/-! Compact convex Choi space of actual channels, and closed affine state-preserving slices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TestingSDP
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {a b : ℕ}

/-- All normalized positive Choi matrices, in the unnormalized input-first convention. -/
def channelChoiSet (a b : ℕ) : Set (BipartiteOperator a b) :=
  {C | C.PosSemidef ∧ KrausChannel.traceOutput C = 1}

theorem channelChoiSet_eq_image (a b : ℕ) :
    channelChoiSet a b = MatrixMap.choi '' {Φ : MatrixMap a b | IsChannel Φ} := by
  ext C
  constructor
  · intro h
    obtain ⟨Φ,hΦ⟩ := (KrausChannel.is_choi_iff C).mpr h
    refine ⟨Φ.toLinearMap,(isChannel_iff_kraus _).mpr ⟨Φ,rfl⟩,?_⟩
    simpa using hΦ
  · rintro ⟨Φ,hΦ,rfl⟩
    exact ⟨MatrixMap.choi_positive_of_completelyPositive Φ hΦ.1,
      MatrixMap.traceOutput_choi_of_trace_preserving Φ hΦ.2⟩

theorem continuous_traceOutput : Continuous (@KrausChannel.traceOutput a b) := by
  unfold KrausChannel.traceOutput
  fun_prop

theorem isClosed_channelChoiSet (a b : ℕ) : IsClosed (channelChoiSet a b) := by
  letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
  have h : IsClosed {C : BipartiteOperator a b | 0 ≤ C ∧ KrausChannel.traceOutput C = 1} :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_eq continuous_traceOutput continuous_const)
  simpa only [channelChoiSet, Matrix.nonneg_iff_posSemidef] using h

theorem channelChoiSet_trace {C : BipartiteOperator a b} (hC : C ∈ channelChoiSet a b) :
    C.trace = (a:ℂ) := by
  have ht := congrArg Matrix.trace hC.2
  simpa [KrausChannel.traceOutput, Matrix.trace, Matrix.diag, Fintype.sum_prod_type] using ht

theorem isCompact_channelChoiSet (a b : ℕ) : IsCompact (channelChoiSet a b) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_channelChoiSet a b)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(a:ℝ), fun C hC => ?_⟩
  have h := positive_norm_le_trace hC.1
  simpa only [channelChoiSet_trace hC,Complex.natCast_re] using h

theorem convex_channelChoiSet (a b : ℕ) : Convex ℝ (channelChoiSet a b) := by
  intro C hC D hD r s hr hs hrs
  refine ⟨(hC.1.smul hr).add (hD.1.smul hs),?_⟩
  have he : KrausChannel.traceOutput (r • C+s • D) =
      r • KrausChannel.traceOutput C+s • KrausChannel.traceOutput D := by
    ext i j
    simp [KrausChannel.traceOutput,Finset.sum_add_distrib,Finset.mul_sum]
  rw [he,hC.2,hD.2,←add_smul,hrs,one_smul]

/-- Choi reconstruction applied to a specified matrix. -/
def choiAction (C : BipartiteOperator a b) (X : Operator a) : Operator b :=
  fun i j => ∑ u, ∑ v, X u v*C (u,i) (v,j)

theorem choiAction_choi (Φ : MatrixMap a b) (X : Operator a) :
    choiAction (MatrixMap.choi Φ) X = Φ X := by
  ext i j
  exact (MatrixMap.apply_eq_sum_choi Φ X i j).symm

theorem continuous_choiAction (X : Operator a) :
    Continuous (fun C : BipartiteOperator a b => choiAction C X) := by
  unfold choiAction
  fun_prop

theorem choiAction_mix (C D : BipartiteOperator a b) (X : Operator a) (r s : ℝ) :
    choiAction (r • C+s • D) X = r • choiAction C X+s • choiAction D X := by
  ext i j
  simp [choiAction,mul_add,Finset.sum_add_distrib,Finset.mul_sum,← mul_assoc,mul_comm,mul_left_comm]

/-- CPTP maps satisfying one literal fixed-input/fixed-output equality. -/
def preservingSet (τ : State a) (ω : State b) : Set (MatrixMap a b) :=
  {Φ | IsChannel Φ ∧ Φ τ.matrix = ω.matrix}

theorem preservingSet_choi_image (τ : State a) (ω : State b) :
    MatrixMap.choi '' preservingSet τ ω =
      channelChoiSet a b ∩ {C | choiAction C τ.matrix = ω.matrix} := by
  ext C
  constructor
  · rintro ⟨Φ,hΦ,rfl⟩
    refine ⟨?_,?_⟩
    · rw [channelChoiSet_eq_image]; exact ⟨Φ,hΦ.1,rfl⟩
    · simpa only [Set.mem_setOf_eq,choiAction_choi] using hΦ.2
  · rintro ⟨hC,hout⟩
    rw [channelChoiSet_eq_image] at hC
    obtain ⟨Φ,hΦ,rfl⟩ := hC
    exact ⟨Φ,⟨hΦ,by simpa only [Set.mem_setOf_eq,choiAction_choi] using hout⟩,rfl⟩

theorem isCompact_preservingSet_choi (τ : State a) (ω : State b) :
    IsCompact (MatrixMap.choi '' preservingSet τ ω) := by
  rw [preservingSet_choi_image]
  exact (isCompact_channelChoiSet a b).inter_right
    (isClosed_eq (continuous_choiAction τ.matrix) continuous_const)

theorem convex_preservingSet_choi (τ : State a) (ω : State b) :
    Convex ℝ (MatrixMap.choi '' preservingSet τ ω) := by
  rw [preservingSet_choi_image]
  apply (convex_channelChoiSet a b).inter
  intro C hC D hD r s hr hs hrs
  change choiAction (r • C+s • D) τ.matrix = ω.matrix
  rw [choiAction_mix,hC,hD,←add_smul,hrs,one_smul]

end GeneralizedChannelStein
