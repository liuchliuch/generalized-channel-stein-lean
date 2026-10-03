import GeneralizedChannelStein.CorrelatedExample
import GeneralizedChannelStein.EntropyMinimaxResults
import GeneralizedChannelStein.MIOOperational
import GeneralizedChannelStein.QuantitativeCompletion
import GeneralizedChannelStein.ToleranceComparison

/-!
# Paper statement specification

Explicit propositions for arXiv:2609.30762v1. Read these quantified contracts
alongside `docs/paper-correspondence.md` and the shared definitions.
No proposition is defined by referring to an implementation theorem's type.
Supporting definitions are imported from the mathematical library; some of
those modules also contain proofs. The review boundary includes those imports.
-/
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.PaperStatements

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DiamondNorm Filter
open scoped Topology ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.theorem_2`. -/
def theorem_2 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F),
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → Tendsto (testingRateReal N F ε) atTop (𝓝 R)) ∧
      Tendsto (entropyRateReal N F) atTop (𝓝 R) ∧
      (∀ ω : State b, ω.matrix.PosDef →
        ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1 →
        R ≤ replacerRate ω hb)

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DiamondNorm Filter
open scoped Topology ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.theorem_3`. -/
def theorem_3 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (S : ℝ) (hS : steinRate N F < S),
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ L M : KrausChannel (a^n) (b^n), M.toLinearMap ∈ F n ∧
        MatrixMap.CPLe L.toLinearMap (Complex.ofReal ((2:ℝ)^((n:ℝ)*S)) • M.toLinearMap) ∧
        DiamondNorm.diamondNorm (L.toLinearMap-(N.tensorPower n).toLinearMap) ≤
          ENNReal.ofReal (K*Real.exp (-γ*(n:ℝ)))

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DimensionDomination
open scoped ComplexOrder MatrixOrder

/-- Paper interface for `GeneralizedChannelStein.lemma_4`. -/
def lemma_4 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1),
    let C := replacerRate ω hb
    let E := familyEntropy (N.tensorPower n) (F n)
    let β := compositeBeta (N.tensorPower n) (F n) ε
    (0 ≤ E ∧ E ≤ ((n:ℝ)*C : EReal)) ∧
    (ENNReal.ofReal ((1-ε)*(2:ℝ)^(-(n:ℝ)*C)) ≤ β ∧ β ≤ ENNReal.ofReal (1-ε)) ∧
    (1-ε)*(-Real.logb 2 β.toReal) ≤ E.toReal+1

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy TestingSDP TestingPrimal Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

/-- Paper interface for `GeneralizedChannelStein.lemma_5_minimax`. -/
def lemma_5_minimax : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (hF : ∀ M ∈ F, IsChannel M)
    (hc : IsCompact (MatrixMap.choi '' F)) (hv : Convex ℝ (MatrixMap.choi '' F))
    (hne : F.Nonempty) (ε : ℝ) (hε : 0 ≤ ε),
    compositeBeta N F ε = ⨆ M : FreeChannel F, singleBeta N M.val ε

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy TestingSDP TestingPrimal Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

/-- Paper interface for `GeneralizedChannelStein.lemma_5_hardest`. -/
def lemma_5_hardest : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (hF : ∀ M ∈ F, IsChannel M)
    (hc : IsCompact (MatrixMap.choi '' F)) (hv : Convex ℝ (MatrixMap.choi '' F))
    (hne : F.Nonempty) (ε : ℝ) (hε : 0 ≤ ε),
    ∃ M : KrausChannel a b, M.toLinearMap ∈ F ∧
      compositeBeta N F ε = singleBeta N M ε

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy TestingSDP TestingPrimal Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

/-- Paper interface for `GeneralizedChannelStein.lemma_5_optimal_tester`. -/
def lemma_5_optimal_tester : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (ε : ℝ) (hε : 0 ≤ ε),
    ∃ ψ : UnitPureInput a a, ∃ T : Effect (a*b),
      1-ε ≤ T.probability (pureOutput N ψ) ∧
      compositeBeta N F ε =
        ⨆ M : FreeChannel F, ENNReal.ofReal (T.probability (pureOutput M.val ψ))

end

section
open GeneralizedChannelStein.UniformAuxiliary
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal HockeyStickApproximation
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.UniformAuxiliary.lemma_6_testing`. -/
def lemma_6_testing : Prop :=
  ∀ {a b e f : ℕ} (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (hV : dilationMap V = Φ.toLinearMap) (hW : dilationMap W = Ψ.toLinearMap)
    (t : ℝ) (ht : 0 ≤ t),
    ∃ A : Matrix (Fin e) (Fin f) ℂ, ‖A‖ ≤ Real.sqrt t ∧
      ‖V - ((1 : Operator b) ⊗ₖ A) * W‖ ^ 2 ≤ channelHockeyStick Φ Ψ t

end

section
open GeneralizedChannelStein.UniformAuxiliary
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal HockeyStickApproximation
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.UniformAuxiliary.lemma_6_diamond`. -/
def lemma_6_diamond : Prop :=
  ∀ {a b e f : ℕ} (Φ Ψ Λ : KrausChannel a b) (ha : 0 < a)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (hV : dilationMap V = Φ.toLinearMap) (hW : dilationMap W = Ψ.toLinearMap)
    (t δ : ℝ) (ht : 0 ≤ t) (hδ : 0 ≤ δ)
    (hdom : MatrixMap.CPLe Λ.toLinearMap ((t : ℂ) • Ψ.toLinearMap))
    (hclose : DiamondNorm.diamondNorm (Λ.toLinearMap - Φ.toLinearMap) ≤ ENNReal.ofReal δ),
    ∃ A : Matrix (Fin e) (Fin f) ℂ, ‖A‖ ≤ Real.sqrt t ∧
      ‖V - ((1 : Operator b) ⊗ₖ A) * W‖ ^ 2 ≤ δ / 2

end

section
open GeneralizedChannelStein.UniformAuxiliary
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal HockeyStickApproximation
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.UniformAuxiliary.lemma_6_exact`. -/
def lemma_6_exact : Prop :=
  ∀ {a b e f : ℕ} (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hdom : MatrixMap.CPLe (dilationMap V) ((t : ℂ) • dilationMap W)),
    ∃ A : Matrix (Fin e) (Fin f) ℂ, ‖A‖ ≤ Real.sqrt t ∧
      V - ((1 : Operator b) ⊗ₖ A) * W = 0

end

section
open GeneralizedChannelStein.UniformAuxiliary
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal HockeyStickApproximation
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.UniformAuxiliary.lemma_6_converse`. -/
def lemma_6_converse : Prop :=
  ∀ {a b e f : ℕ} (W : Matrix (Fin b × Fin f) (Fin a) ℂ) (A : Matrix (Fin e) (Fin f) ℂ),
    MatrixMap.CompletelyPositive (dilationMap (((1 : Operator b) ⊗ₖ A) * W)) ∧
    MatrixMap.CPLe (dilationMap (((1 : Operator b) ⊗ₖ A) * W))
      (((‖A‖ ^ 2 : ℝ) : ℂ) • dilationMap W)

end

section
open GeneralizedChannelStein.TraceDefectCompletion
open QuantumChannelStein Matrix ChannelEntropy TestingSDP DiamondNorm
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.TraceDefectCompletion.lemma_7`. -/
def lemma_7 : Prop :=
  ∀ {a b : ℕ} (F : Set (MatrixMap a b)) (hF : Convex ℝ (MatrixMap.choi '' F))
    (Q : Subchannel a b) (N M : KrausChannel a b) (ha : 0 < a)
    (ω : State b) (hM : M.toLinearMap ∈ F)
    (hR : (ReplacerChannel.channel a ω).toLinearMap ∈ F)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hdom : MatrixMap.CPLe Q.toLinearMap ((lam : ℂ) • M.toLinearMap)),
    let d := ‖defect Q.toLinearMap‖
    0 ≤ d ∧ d ≤ 1 ∧ ENNReal.ofReal d ≤ DiamondNorm.diamondNorm (Q.toLinearMap - N.toLinearMap) ∧
    ∃ L S : KrausChannel a b, S.toLinearMap ∈ F ∧
      MatrixMap.CPLe L.toLinearMap (((lam + d : ℝ) : ℂ) • S.toLinearMap) ∧
      DiamondNorm.diamondNorm (L.toLinearMap - N.toLinearMap) ≤
        2 * DiamondNorm.diamondNorm (Q.toLinearMap - N.toLinearMap)

end

section
open GeneralizedChannelStein.FreeAmplification
open QuantumChannelStein Matrix ChannelEntropy ChannelDilationPower
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

/-- Paper interface for `GeneralizedChannelStein.FreeAmplification.proposition_8_unbounded`. -/
def proposition_8_unbounded : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (F : AlternativeFamily a b)
    (ha : 0<a) (hb : 0<b)
    (hconv : ∀ n, 0<n → Convex ℝ (MatrixMap.choi '' F n))
    (htensor : ∀ n m, 0<n → 0<m →
      ∀ (P : KrausChannel (a^n) (b^n)) (Q : KrausChannel (a^m) (b^m)),
      P.toLinearMap ∈ F n → Q.toLinearMap ∈ F m → (tensorBlocks n m P Q).toLinearMap ∈ F (n+m))
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (k : ℕ→ℕ) (hk : ∀ B : ℕ, ∃ᶠ j : ℕ in Filter.atTop, B≤k j)
    (L M : (j : ℕ) → KrausChannel (a^(k j)) (b^(k j))) (lam : ℕ→ℝ)
    (hlam : ∀ j, 1≤lam j) (hM : ∀ j, (M j).toLinearMap ∈ F (k j))
    (hdom : ∀ j, MatrixMap.CPLe (L j).toLinearMap ((lam j : ℂ) • (M j).toLinearMap))
    (herror : Filter.Tendsto (fun j => DiamondNorm.diamondNorm ((L j).toLinearMap-(N.tensorPower (k j)).toLinearMap))
      Filter.atTop (𝓝 0)) (r₀ S : ℝ) (hr₀ : 0≤r₀) (hS : r₀<S)
    (hrate : Filter.limsup (fun j => ((Real.logb 2 (lam j)/(k j:ℝ) : ℝ) : EReal)) Filter.atTop ≤ (r₀:EReal)),
    ExponentialFreeApprox N F S

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DimensionDomination FreeAmplification Filter
open scoped Topology ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.proposition_9`. -/
def proposition_9 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε S : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hS : lowerTestingRate N F ε < (S:EReal)),
    ExponentialFreeApprox N F S

end

section
open QuantumChannelStein Matrix ChannelEntropy OperationalTesting SharpChannel
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.EntropyComparison.lemma_10`. -/
def lemma_10 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (hb : 0 < b)
    (F : AlternativeFamily a b) (ω : State b) (hω : ω.matrix.PosDef)
    (n : ℕ) (_hn : 0 < n)
    (hF : Convex ℝ (MatrixMap.choi '' F n))
    (hR : ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ F n)
    (L S : KrausChannel (a^n) (b^n)) (hS : S.toLinearMap ∈ F n)
    (z δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdom : MatrixMap.CPLe L.toLinearMap (Complex.ofReal ((2:ℝ)^z) • S.toLinearMap))
    (hclose : DiamondNorm.diamondNorm (L.toLinearMap-(N.tensorPower n).toLinearMap) ≤ ENNReal.ofReal δ),
    familyEntropy (N.tensorPower n) (F n) ≤
      ((z+1 + δ/2 * ((n:ℝ) * (replacerRate ω hb + Real.logb 2 (a*b)) + 1) +
        EntropyContinuity.binaryEntropy (δ/2) : ℝ) : EReal)

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DiamondNorm DimensionDomination Filter Asymptotics
open scoped Topology ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.theorem_11`. -/
def theorem_11 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) (δ : ℕ → ℝ) (δbar : ℝ)
    (hδ : ∀ n, 0 < n → 0 < δ n ∧ δ n ≤ δbar) (hbar : δbar < 2)
    (hsub : (fun n => Real.logb 2 (1/δ n)) =o[atTop] (fun n : ℕ => (n:ℝ))),
    Tendsto (fun n : ℕ => (smoothedResourceMax (N.tensorPower n) (F n) (δ n)).toReal/(n:ℝ))
      atTop (𝓝 (steinRate N F))

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter Asymptotics
open scoped Topology ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.theorem_11_extended`. -/
def theorem_11_extended : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) (δ : ℕ → ℝ) (δbar : ℝ)
    (hδ : ∀ n, 0 < n → 0 < δ n ∧ δ n ≤ δbar) (hbar : δbar < 2)
    (hsub : (fun n => Real.logb 2 (1/δ n)) =o[atTop] (fun n : ℕ => (n:ℝ))),
    Tendsto (smoothedRate N F δ) atTop (𝓝 (steinRate N F:EReal))

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy OperationalTesting Filter
open scoped Topology

/-- Paper interface for `GeneralizedChannelStein.theorem_12`. -/
def theorem_12 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F),
    (∃ t : (n : ℕ) → ChannelTest (a^n) (b^n),
      Tendsto (fun n => (t n).acceptance (N.tensorPower n)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => -Real.logb 2 (worstAcceptance (F n) (t n)).toReal/(n:ℝ))
        atTop (𝓝 (steinRate N F))) ∧
    (∀ r : ℝ, steinRate N F < r → ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ n : ℕ, ∀ t : ChannelTest (a^n) (b^n),
      worstAcceptance (F n) t ≤ ENNReal.ofReal ((2:ℝ)^(-(n:ℝ)*r)) →
      t.acceptance (N.tensorPower n) ≤ K*(2:ℝ)^(-c*(n:ℝ)))

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DiamondNorm ParallelExponent Filter
open scoped Topology ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.corollary_13`. -/
def corollary_13 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (T : (n : ℕ) → KrausChannel (a^n) (b^n))
    (hclose : Tendsto (fun n => DiamondNorm.diamondNorm ((T n).toLinearMap-(N.tensorPower n).toLinearMap))
      atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1),
    Tendsto (fun n : ℕ => -Real.logb 2 (compositeBeta (T n) (F n) ε).toReal/(n:ℝ))
      atTop (𝓝 (steinRate N F))

end

section
open GeneralizedChannelStein
open QuantumChannelStein Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.theorem_16_uniform_lowerBounds`. -/
def theorem_16_uniform_lowerBounds : Prop :=
  ∀ {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (t w ε : ℝ) (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1)
    (hε : 0<ε) (hε1 : ε<1),
    ∀ (N : KrausChannel a b) (F : AlternativeFamily a b), Admissible F →
    ∀ (τ : State a), QuantitativeAt F τ → ∀ (ω : State b), ω.matrix.PosDef →
    ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1 →
    (τ.matrix-t•(1:Operator a)).PosSemidef → (ω.matrix-w•(1:Operator b)).PosSemidef →
    CompletionProperty N F ε (generalCompletionConstant a b t w ε)

end

section
open GeneralizedChannelStein
open QuantumChannelStein Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.theorem_16`. -/
def theorem_16 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (τ : State a) (hQ : QuantitativeAt F τ)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1),
    CompletionProperty N F ε (generalCompletionConstant a b
      (DimensionDomination.minEigenvalue τ ha) (DimensionDomination.minEigenvalue ω hb) ε)

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter
open scoped Topology

/-- Paper interface for `GeneralizedChannelStein.corollary_17`. -/
def corollary_17 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1),
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 0<n → ∀ δ : ℝ, 0<δ → δ≤1/16 → ε+δ/2<1 →
      (((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
        Real.logb 2 (1-ε-δ/2) : ℝ) : EReal) ≤ smoothedResourceMax (N.tensorPower n) (F n) δ) ∧
      (smoothedResourceMax (N.tensorPower n) (F n) δ ≤
        ((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
          completionLoss K n δ : ℝ) : EReal))

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter
open scoped Topology

/-- Paper interface for `GeneralizedChannelStein.corollary_17_lower`. -/
def corollary_17_lower : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) (n : ℕ) (hn : 0<n)
    (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ<2*(1-ε)),
    ((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
      Real.logb 2 (1-ε-δ/2) : ℝ) : EReal) ≤ smoothedResourceMax (N.tensorPower n) (F n) δ

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter
open scoped Topology

/-- Paper interface for `GeneralizedChannelStein.lemma_18`. -/
def lemma_18 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (εlo εhi : ℝ) (hlo : 0<εlo) (hle : εlo≤εhi) (hhi : εhi<1),
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 0<n →
      ToleranceComparison.intervalDifference N F εlo εhi n ≤
        K*((n:ℝ)^((2:ℝ)/3)*Real.logb 2 ((n:ℝ)+1))

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter
open scoped Topology

/-- Paper interface for `GeneralizedChannelStein.lemma_18_normalized`. -/
def lemma_18_normalized : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (ε ε' : ℝ) (hε : 0<ε) (hε1 : ε<1) (hε' : 0<ε') (hε'1 : ε'<1),
    Tendsto (fun n : ℕ =>
      (ToleranceComparison.exponent N F ε n-ToleranceComparison.exponent N F ε' n)/(n:ℝ))
      atTop (𝓝 0)

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy RelativeEntropy Filter
open scoped Topology ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.proposition_19_complete`. -/
def proposition_19_complete : Prop :=
  ∀ {a b : ℕ} (τ : State a) (ω ρ : State b) (ha : 0 < a) (hb : 0 < b)
    (hτ : τ.matrix.PosDef) (hω : ω.matrix.PosDef),
    Admissible (statePreservingFamily τ ω) ∧ QuantitativeAt (statePreservingFamily τ ω) τ ∧
    (∀ n, familyEntropy ((ReplacerChannel.channel a ρ).tensorPower n) (statePreservingFamily τ ω n) =
      ((n:ℝ):EReal)*umegaki ρ ω) ∧
    (∀ n ε, compositeBeta ((ReplacerChannel.channel a ρ).tensorPower n) (statePreservingFamily τ ω n) ε =
      stateBeta (PerfectDiscrimination.statePower ρ n) (PerfectDiscrimination.statePower ω n) ε) ∧
    (steinRate (ReplacerChannel.channel a ρ) (statePreservingFamily τ ω):EReal) = umegaki ρ ω

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix
open scoped BigOperators Kronecker ComplexOrder
open ChannelEntropy RelativeEntropy OperationalTesting ChannelLocality DivergenceOptimization

/-- Paper interface for `GeneralizedChannelStein.stateBeta_attained`. -/
def stateBeta_attained : Prop :=
  ∀ {b : ℕ} (ρ σ : State b) (ε : ℝ) (hε : 0≤ε),
    ∃ T : Effect b, 1-ε ≤ T.probability ρ ∧ stateBeta ρ σ ε = ENNReal.ofReal (T.probability σ)

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.proposition_20`. -/
def proposition_20 : Prop :=
  ∀ {a b : ℕ} (ha : 0<a) (hb : 0<b),
    Admissible (MIOFamily a b) ∧
    QuantitativeAt (MIOFamily a b) (FaithfulDensity.maximallyMixed a ha) ∧
    Admissible (DIOFamily a b) ∧
    QuantitativeAt (DIOFamily a b) (FaithfulDensity.maximallyMixed a ha)

end

section
open GeneralizedChannelStein.MIOOperational
open QuantumChannelStein Matrix ChannelPowerReindex
open scoped BigOperators Kronecker ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.MIOOperational.mem_MIOFamily_iff_map`. -/
def mem_MIOFamily_iff_map : Prop :=
  ∀ {a b : ℕ} (n : ℕ) (Φ : MatrixMap (a ^ n) (b ^ n)),
    Φ ∈ MIOFamily a b n ↔ IsChannel Φ ∧
      ∀ ρ : State (a ^ n), IsDiagonal ρ.matrix → IsDiagonal (Φ ρ.matrix)

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.proposition_21`. -/
def proposition_21 : Prop :=
  ∀ {a b : ℕ} {G : Type*} [Group G]
    (U : G →* Matrix.unitaryGroup (Fin a) ℂ) (V : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (τ : State a) (ω : State b) (hτ : τ.matrix.PosDef) (hω : ω.matrix.PosDef)
    (hτinv : ∀ g, (U g).val*τ.matrix*(U g).valᴴ=τ.matrix)
    (hωinv : ∀ g, (V g).val*ω.matrix*(V g).valᴴ=ω.matrix),
    Admissible (unitaryCovariantFamily U V) ∧ QuantitativeAt (unitaryCovariantFamily U V) τ

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.intersection_admissible`. -/
def intersection_admissible : Prop :=
  ∀ {a b : ℕ} {ι : Type*} (F : ι → AlternativeFamily a b)
    (hF : ∀ i, Admissible (F i)) (ω : State b) (hω : ω.matrix.PosDef)
    (hR : ∀ i, ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F i 1),
    Admissible (familyIntersection F)

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.intersection_quantitative`. -/
def intersection_quantitative : Prop :=
  ∀ {a b : ℕ} {ι : Type*} (F : ι → AlternativeFamily a b)
    (τ : State a) (hτ : τ.matrix.PosDef) (hF : ∀ i, QuantitativeAt (F i) τ),
    QuantitativeAt (familyIntersection F) τ

end

section
open GeneralizedChannelStein
open QuantumChannelStein Matrix TestingSDP ChannelPowerReindex PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.proposition_22_families`. -/
def proposition_22_families : Prop :=
  ∀ {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (τ : State a) (ω : State b) (hτ : τ.matrix.PosDef) (hω : ω.matrix.PosDef),
    Admissible (EBFamily a b) ∧ QuantitativeAt (EBFamily a b) τ ∧
    Admissible (PPTFamily a b) ∧ QuantitativeAt (PPTFamily a b) τ

end

section
open GeneralizedChannelStein
open QuantumChannelStein Matrix TestingSDP ChannelEntropy PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open OperationalTesting RelativeEntropy

/-- Paper interface for `GeneralizedChannelStein.proposition_22_benchmarks`. -/
def proposition_22_benchmarks : Prop :=
  ∀ {a b : ℕ} (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (n : ℕ) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1),
    familyEntropy ((isometryChannel J hJ).tensorPower n) (EBFamily a b n) =
      ((n:ℝ)*Real.logb 2 (a:ℝ):ℝ) ∧
    familyEntropy ((isometryChannel J hJ).tensorPower n) (PPTFamily a b n) =
      ((n:ℝ)*Real.logb 2 (a:ℝ):ℝ) ∧
    compositeBeta ((isometryChannel J hJ).tensorPower n) (EBFamily a b n) ε =
      ENNReal.ofReal ((1-ε)/(a:ℝ)^n) ∧
    compositeBeta ((isometryChannel J hJ).tensorPower n) (PPTFamily a b n) ε =
      ENNReal.ofReal ((1-ε)/(a:ℝ)^n)

end

section
open GeneralizedChannelStein
open QuantumChannelStein Matrix TestingSDP ChannelEntropy DiamondNorm TraceNorm TraceDefectCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.corollary_23`. -/
def corollary_23 : Prop :=
  ∀ {a b : ℕ} (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (n : ℕ) (δ : ℝ) (hδ : 0≤δ) (hδ2 : δ≤2),
    smoothedResourceMax ((isometryChannel J hJ).tensorPower n) (EBFamily a b n) δ =
      (Real.logb 2 (max 1 ((a:ℝ)^n*(1-δ/2))):EReal) ∧
    smoothedResourceMax ((isometryChannel J hJ).tensorPower n) (PPTFamily a b n) δ =
      (Real.logb 2 (max 1 ((a:ℝ)^n*(1-δ/2))):EReal)

end

section
open GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix ChannelPowerReindex PerfectDiscrimination TensorPower ChannelEntropy RelativeEntropy
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

/-- Paper interface for `GeneralizedChannelStein.Correlated.example_24`. -/
def example_24 : Prop :=
  ∀ {b : ℕ} (ρ ω : State b) (hne : ρ≠ω) (hb : 0<b) (hω : ω.matrix.PosDef)
    (c : ℝ) (hc : 0<c) (hc1 : c<1),
    Admissible (alternativeFamily ρ ω c hc.le hc1.le) ∧
    QuantitativeAt (alternativeFamily ρ ω c hc.le hc1.le) scalarState ∧
    ((ReplacerChannel.channel 1 ρ).tensorPower 1).toLinearMap∉alternativeFamily ρ ω c hc.le hc1.le 1 ∧
    (∀ n, 0<n → 0≤familyEntropy ((ReplacerChannel.channel 1 ρ).tensorPower n)
      (alternativeFamily ρ ω c hc.le hc1.le n) ∧
      familyEntropy ((ReplacerChannel.channel 1 ρ).tensorPower n) (alternativeFamily ρ ω c hc.le hc1.le n)≤
        (Real.logb 2 (1/c):EReal)) ∧
    (∀ n, 0<n → ∀ ε : ℝ, ENNReal.ofReal (c*(1-ε))≤
      compositeBeta ((ReplacerChannel.channel 1 ρ).tensorPower n) (alternativeFamily ρ ω c hc.le hc1.le n) ε) ∧
    steinRate (ReplacerChannel.channel 1 ρ) (alternativeFamily ρ ω c hc.le hc1.le)=0

end

section
open GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix PerfectDiscrimination
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.Correlated.alternativeFamily_one`. -/
def alternativeFamily_one : Prop :=
  ∀ {b : ℕ} (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1),
    alternativeFamily ρ ω c hc hc1 1 = convexHull ℝ
      {ReplacerChannel.linearMap (1^1) (statePower ω 1),
        c • ReplacerChannel.linearMap (1^1) (statePower ρ 1)+
          (1-c) • ReplacerChannel.linearMap (1^1) (statePower ω 1)}

end

section
open GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix ChannelPowerReindex PerfectDiscrimination TensorPower
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.Correlated.generator_block_formula`. -/
def generator_block_formula : Prop :=
  ∀ {b : ℕ} (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) (d : PartitionDescription n) (i j : Index (Fin b) n),
    (partitionGenerator ρ ω c hc hc1 n d).matrix (channelIndexEquiv b n i) (channelIndexEquiv b n j) =
    ∏ l : Fin n, if d.2 l then
      (c:ℂ)*(∏ s : {s : Fin n // d.1 s=l}, ρ.matrix (indexEquiv (Fin b) n i s.1) (indexEquiv (Fin b) n j s.1))+
      ((1-c:ℝ):ℂ)*(∏ s : {s : Fin n // d.1 s=l}, ω.matrix (indexEquiv (Fin b) n i s.1) (indexEquiv (Fin b) n j s.1))
    else ∏ s : {s : Fin n // d.1 s=l}, ω.matrix (indexEquiv (Fin b) n i s.1) (indexEquiv (Fin b) n j s.1)

end

section
open GeneralizedChannelStein.BranchExtraction
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal EnvironmentTensor
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.BranchExtraction.lemma_25`. -/
def lemma_25 : Prop :=
  ∀ {a b : ℕ} (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (M : KrausChannel a b) (ha : 0<a) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hβ : 0<singleBeta (isometryChannel J hJ) M δ),
    ∃ V : Matrix (Fin b) (Fin a) ℂ, ‖V‖≤1 ∧
      (BranchExtraction.realPart (Jᴴ*V)-((1-Real.sqrt (1-δ))/(1+Real.sqrt (1-δ))) • (1 : Operator a)).PosSemidef ∧
      MatrixMap.CPLe (((singleBeta (isometryChannel J hJ) M δ).toReal : ℂ) • BranchExtraction.adMap V) M.toLinearMap

end

section
open GeneralizedChannelStein.ExtensionComparison
open QuantumChannelStein Matrix ChannelEntropy OperationalTesting
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.ExtensionComparison.lemma_26`. -/
def lemma_26 : Prop :=
  ∀ {a b e : ℕ} (N : KrausChannel a b) (ha : 0<a)
    (F : Set (MatrixMap a b)) (hF : ∀ M ∈ F, IsChannel M)
    (hc : IsCompact (MatrixMap.choi '' F)) (hv : Convex ℝ (MatrixMap.choi '' F)) (hne : F.Nonempty)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (hVN : dilationMap V=N.toLinearMap)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1),
    0<tolerance ε ∧ tolerance ε<1 ∧ 0<factor ε ∧
    ENNReal.ofReal (factor ε)*compositeBeta N F ε ≤
      compositeBeta (isometryChannel (AuxiliaryExtensions.outputIsometry V) (AuxiliaryExtensions.outputIsometry_isometry V hV))
        (AuxiliaryExtensions.extensionFamily F) (tolerance ε) ∧
    compositeBeta (isometryChannel (AuxiliaryExtensions.outputIsometry V) (AuxiliaryExtensions.outputIsometry_isometry V hV))
      (AuxiliaryExtensions.extensionFamily F) ε ≤ compositeBeta N F ε

end

section
open GeneralizedChannelStein
open QuantumChannelStein Matrix TensorPower TensorPermutation MeasureTheory LocalExpansion
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.lemma_27`. -/
def lemma_27 : Prop :=
  ∀  {d : ℕ} (hd : 0<d) (τ : State d) (hτ : τ.matrix.PosDef)
    (n : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ≤1/16)
    (hn : WeightedDiscardingScalars.blockThreshold d (DimensionDomination.minEigenvalue τ hd)≤n)
    (hma : (WeightedDiscardingScalars.discardCount n ξ : ℝ)≤(n:ℝ)/2)
    (W : Matrix (Index (Fin d) n) (Index (Fin d) n) ℂ)
    (hW : W∈invariantAlgebra (Fin d) n) (hWn : ‖W‖≤1),
    ∃ E : Expansion (Fin d) (Lemma27Parameters.k n ξ),
      (∀ i, ((E.sites i).card:ℝ)≤WeightedDiscardingScalars.supportConstant d
        (DimensionDomination.minEigenvalue τ hd)*(n:ℝ)^(2/3:ℝ)) ∧
      E.cost≤Real.exp (WeightedDiscardingScalars.supportConstant d
        (DimensionDomination.minEigenvalue τ hd)*(n:ℝ)^(2/3:ℝ)) ∧
      ‖E.value-weightedExpectationSplit τ (Lemma27Parameters.k n ξ) (Lemma27Parameters.m n ξ)
        (Lemma27Parameters.paper_parameters (DimensionDomination.minEigenvalue_pos τ hd hτ) hξ hξ1 hn hma).split W‖≤ξ

end

section
open GeneralizedChannelStein.FreeMultipliers
open QuantumChannelStein Matrix ChannelEntropy ChannelPowerReindex PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.FreeMultipliers.lemma_28`. -/
def lemma_28 : Prop :=
  ∀ {a d n : ℕ} (F : AlternativeFamily a d) (hF : Admissible F)
    (τ : State a) (hτ : QuantitativeAt F τ) (ω : State d) (hωpos : ω.matrix.PosDef)
    (hω : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (ha : 0<a) (hd : 0<d) (hn : 0<n)
    (M : KrausChannel (a^n) (d^n)) (hM : M.toLinearMap∈F n)
    (K : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (p : ℝ) (hp : 0<p)
    (hdom : MatrixMap.CPLe (Complex.ofReal p • BranchExtraction.adMap K) M.toLinearMap)
    (E : LocalExpansion.Expansion (Fin d) n)
    (hH : 0<∑ i : E.terms, ‖E.coeff i‖*paperCost a d
      (DimensionDomination.minEigenvalue τ ha) (DimensionDomination.minEigenvalue ω hd) (E.sites i).card),
    ∃ M' : KrausChannel (a^n) (d^n), M'.toLinearMap∈F n ∧
      MatrixMap.CPLe
        (Complex.ofReal (p/(∑ i : E.terms, ‖E.coeff i‖*paperCost a d
          (DimensionDomination.minEigenvalue τ ha) (DimensionDomination.minEigenvalue ω hd) (E.sites i).card)^2) •
          BranchExtraction.adMap (SiteGrouping.flatten E.value*K)) M'.toLinearMap

end

section
open GeneralizedChannelStein.ImageProjector
open QuantumChannelStein Matrix LocalExpansion ImageProjectorScalars
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.ImageProjector.lemma_29`. -/
def lemma_29 : Prop :=
  ∀ {k : ℕ} {A C : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype C] [DecidableEq C] [Nonempty C] (v : EuclideanSpace ℂ C) (hv : ‖v‖=1) (hk : 2≤k)
    {ξ : ℝ} (hξ : 0<ξ) (hξupper : ξ≤1/16),
    ∃ E : Expansion (A×C) k,
      ‖E.value‖≤1 ∧
      ‖Matrix.reindex (regroup A C k) (regroup A C k) E.value -
        (1:Matrix (Fin k→A) (Fin k→A) ℂ) ⊗ₖ TensorPower.finTensorPower (pureMatrix v) k‖≤ξ ∧
      E.HasSize (min k (filterDegree k ξ)) ∧ E.cost≤(15:ℝ)^(filterDegree k ξ)

end

section
open GeneralizedChannelStein.IsometricCompletion
open QuantumChannelStein Matrix ChannelEntropy ChannelPowerReindex PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.IsometricCompletion.proposition_30`. -/
def proposition_30 : Prop :=
  ∀ {a d : ℕ} (ha : 0<a) (hd : 0<d) {t w c : ℝ}
    (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1) (hc : 0<c),
    ∃ K : ℝ, IsometricCompletionProperty a d t w c K

end

section
open GeneralizedChannelStein.IsometricCompletion
open QuantumChannelStein
open scoped ComplexOrder MatrixOrder

/-- Paper interface for `GeneralizedChannelStein.IsometricCompletion.proposition_30_minEigen`. -/
def proposition_30_minEigen : Prop :=
  ∀  {a d : ℕ} (ha : 0<a) (hd : 0<d)
    (τ : State a) (hτ : τ.matrix.PosDef) (ω : State d) (hω : ω.matrix.PosDef)
    (c : ℝ) (hc : 0<c),
    ∃ K : ℝ, IsometricCompletionProperty a d
      (DimensionDomination.minEigenvalue τ ha) (DimensionDomination.minEigenvalue ω hd) c K

end

section
open GeneralizedChannelStein.CanonicalConcavity
open QuantumChannelStein Matrix ChannelEntropy PureReferenceRecovery EntropyContinuity CanonicalInput
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

/-- Paper interface for `GeneralizedChannelStein.CanonicalConcavity.value_concave_input`. -/
def value_concave_input : Prop :=
  ∀ {n m : ℕ} (N M : KrausChannel n m) (ρ σ : State n)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1),
    (p:EReal)*value N M ρ+((1-p:ℝ):EReal)*value N M σ ≤ value N M (mix ρ σ p hp hp1)

end

section
open GeneralizedChannelStein.EntropyMinimax
open QuantumChannelStein RelativeEntropy PhyslibStateBridge Matrix EntropyContinuity
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Paper interface for `GeneralizedChannelStein.EntropyMinimax.value_convex_alternative`. -/
def value_convex_alternative : Prop :=
  ∀ {n m : ℕ} (N Φ Ψ Ω : KrausChannel n m) (ρ : State n) (p : Prob)
    (hΩ : Ω.toLinearMap=(p:ℂ)•Φ.toLinearMap+(1-(p:ℂ))•Ψ.toLinearMap),
    CanonicalInput.value N Ω ρ ≤
      ((p:ENNReal):EReal)*CanonicalInput.value N Φ ρ +
      ((1-(p:ENNReal):ENNReal):EReal)*CanonicalInput.value N Ψ ρ

end

section
open GeneralizedChannelStein.EntropyMinimaxResults
open QuantumChannelStein Matrix ChannelEntropy RelativeEntropy CanonicalInput CanonicalAttainment CanonicalRegularization
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

/-- Paper interface for `GeneralizedChannelStein.EntropyMinimaxResults.lemma_32`. -/
def lemma_32 : Prop :=
  ∀  {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (k : ℕ) (hk : 0<k),
    familyEntropy (N.tensorPower k) (F k)=
      (⨆ ρ : State (a^k), familyInputValue (N.tensorPower k) (F k) ρ) ∧
      ∃ ρ : State (a^k), familyInputValue (N.tensorPower k) (F k) ρ=familyEntropy (N.tensorPower k) (F k)

end

section
open GeneralizedChannelStein.EntropyMinimaxResults
open QuantumChannelStein Matrix ChannelEntropy RelativeEntropy CanonicalInput CanonicalAttainment CanonicalRegularization
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

/-- Paper interface for `GeneralizedChannelStein.EntropyMinimaxResults.lemma_32_permutation_optimizer`. -/
def lemma_32_permutation_optimizer : Prop :=
  ∀  {a b : ℕ}
    (N : KrausChannel a b) (ha : 0<a) (hb : 0<b) (k : ℕ)
    (M : KrausChannel (a^k) (b^k))
    (hM : CovariantOrbitRecovery.Covariant (TensorChannelCovariance.channelPermutation a k)
      (TensorChannelCovariance.channelPermutation b k) M)
    (ω : State b) (hω : ω.matrix.PosDef) (η : ℝ) (hη : 0<η)
    (hR : MatrixMap.CPLe ((η:ℂ)•((ReplacerChannel.channel a ω).tensorPower k).toLinearMap) M.toLinearMap),
    ∃ ρ : State (a^k),
      (∀ π : Equiv.Perm (Fin k), Matrix.reindex (TensorChannelCovariance.channelPermutation a k π)
        (TensorChannelCovariance.channelPermutation a k π) ρ.matrix=ρ.matrix) ∧
      value (N.tensorPower k) M ρ=channelD (N.tensorPower k) M

end

section
open QuantumChannelStein ChannelEntropy
open scoped ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.NearSubadditiveEntropy.lemma_33`. -/
def lemma_33 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0<n)
    (hperm : ∀ π : Equiv.Perm (Fin n), ∀ M : KrausChannel (a^n) (b^n),
      M.toLinearMap ∈ F n → (permuteChannel n π M).toLinearMap ∈ F n)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1),
    ((familyEntropy (N.tensorPower n) (F n)).toReal -
      (1-ε)*((n:ℝ)*replacerRate ω hb+1) -
      Real.logb 2 (((n+(a*b)^2-1).choose ((a*b)^2-1) : ℕ) : ℝ))/ε - 1 ≤
        -Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal

end

section
open Filter Set Asymptotics
open scoped Topology

/-- Paper interface for `GeneralizedChannelStein.NearSubadditive.lemma_34`. -/
def lemma_34 : Prop :=
  ∀  {a F : ℕ → ℝ} {C₀ C₁ : ℝ}
    (ha0 : ∀ n, 0 < n → 0 ≤ a n)
    (haB : ∀ n, 0 < n → a n ≤ C₀*n+C₁)
    (hF0 : ∀ n, 0 ≤ F n) (hFmono : Monotone F)
    (hFO : F =O[atTop] (fun n : ℕ =>
      (n:ℝ)^((2:ℝ)/3) * (Real.log ((n:ℝ)+1)/Real.log 2)))
    (hadd : ∀ n m, 0 < n → 0 < m → a (n+m) ≤ a n+a m+F (n+m)),
    ∃ R : ℝ, 0 ≤ R ∧ Tendsto (fun n : ℕ => a n/(n:ℝ)) atTop (𝓝 R)

end

section
open QuantumChannelStein ChannelEntropy DiamondNorm ChannelPowerReindex
open scoped ComplexOrder Topology

/-- Paper interface for `GeneralizedChannelStein.AppendixTestingLimit.appendix_b_theorem_2`. -/
def appendix_b_theorem_2 : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F),
    ∃ R : ℝ, 0≤R ∧
      (∀ ε : ℝ, 0<ε → ε<1 → Filter.Tendsto (testingRateReal N F ε) Filter.atTop (𝓝 R)) ∧
      Filter.Tendsto (entropyRateReal N F) Filter.atTop (𝓝 R) ∧
      (∀ ω : State b, ω.matrix.PosDef →
        ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1 → R≤replacerRate ω hb)

end

section
open GeneralizedChannelStein
open QuantumChannelStein
open ChannelEntropy ChannelPowerReindex
open scoped ComplexOrder

/-- Paper interface for `GeneralizedChannelStein.isChannel_iff_kraus`. -/
def isChannel_iff_kraus : Prop :=
  ∀ {a b : ℕ} (Φ : MatrixMap a b),
    IsChannel Φ ↔ ∃ K : KrausChannel a b, K.toLinearMap = Φ

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy OperationalTesting
open ParallelTestingReduction IdenticalChannelTesting

/-- Paper interface for `GeneralizedChannelStein.compositeBeta_eq_pure`. -/
def compositeBeta_eq_pure : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b)
    (F : Set (MatrixMap a b)) (ε : ℝ),
    compositeBeta N F ε = compositePureBeta N F ε

end

section
open GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DimensionDomination
open scoped ComplexOrder MatrixOrder

/-- Paper interface for `GeneralizedChannelStein.admissible_values_finite`. -/
def admissible_values_finite : Prop :=
  ∀ {a b : ℕ} (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1),
    familyEntropy (N.tensorPower n) (F n) ≠ ⊤ ∧
    familyEntropy (N.tensorPower n) (F n) ≠ ⊥ ∧
    0 < compositeBeta (N.tensorPower n) (F n) ε ∧
    compositeBeta (N.tensorPower n) (F n) ε < ⊤

end

end GeneralizedChannelStein.PaperStatements
