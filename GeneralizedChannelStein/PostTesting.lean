import GeneralizedChannelStein.OutputPreimage
import GeneralizedChannelStein.AuxiliaryExtensions

/-! Arbitrary-reference composite testing under actual output postprocessing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix OperationalTesting ChannelEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b c : ℕ}

def postprocessTest (P : KrausChannel b c) (t : ChannelTest a c) : ChannelTest a b where
  reference := t.reference
  input := t.input
  effect := ((KrausChannel.identity t.reference).tensor P).pullbackEffect t.effect

theorem postprocessTest_acceptance (P : KrausChannel b c) (t : ChannelTest a c)
    (N : KrausChannel a b) : (postprocessTest P t).acceptance N=t.acceptance (P.compose N) := by
  change (((KrausChannel.identity t.reference).tensor P).pullbackEffect t.effect).probability
    (outputState N t.reference t.input)=_
  rw [KrausChannel.pullbackEffect_probability,← ChannelLocality.outputState_eq_tensor,
    ← AuxiliaryExtensions.outputState_compose]
  rfl

theorem compositeBeta_map_congr (N M : KrausChannel a b) (F : Set (MatrixMap a b))
    (h : N.toLinearMap=M.toLinearMap) (ε : ℝ) : compositeBeta N F ε=compositeBeta M F ε := by
  have ht : ∀ t : ChannelTest a b, t.acceptance N=t.acceptance M :=
    fun t => AuxiliaryExtensions.acceptance_congr t N M h
  have hp : (fun t : ChannelTest a b => 1-ε≤t.acceptance N)=
      (fun t : ChannelTest a b => 1-ε≤t.acceptance M) := by
    funext t
    rw [ht t]
  exact congrArg (fun p : ChannelTest a b → Prop =>
    ⨅ t : {t : ChannelTest a b // p t}, worstAcceptance F t.val) hp

/-- One output channel transports each single tester before the common family supremum. -/
theorem compositeBeta_postprocess_le (N : KrausChannel a b) (P : KrausChannel b c)
    (F : Set (MatrixMap a b)) (G : Set (MatrixMap a c))
    (hFG : ∀ M : KrausChannel a b, M.toLinearMap∈F → (P.compose M).toLinearMap∈G) (ε : ℝ) :
    compositeBeta N F ε≤compositeBeta (P.compose N) G ε := by
  unfold compositeBeta
  apply le_iInf
  intro t
  let s := postprocessTest P t.val
  have hs : 1-ε≤s.acceptance N := by rw [postprocessTest_acceptance]; exact t.property
  apply (iInf_le _ ⟨s,hs⟩).trans
  unfold worstAcceptance
  apply iSup_le
  intro M
  rw [show s.acceptance M.val=t.val.acceptance (P.compose M.val) from postprocessTest_acceptance P t.val M.val]
  exact le_iSup_of_le ⟨P.compose M.val,hFG M.val M.property⟩ le_rfl

end GeneralizedChannelStein
