import GeneralizedChannelStein.PPTFamilies
import QuantumChannelStein.ChannelEntropyChoi

/-! Finite separable positive decompositions and an actual Choi/operational
entanglement-breaking equivalence. No separability oracle is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TestingSDP ChannelPowerReindex
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- The separable positive cone: finite sums of positive product operators. -/
def Separable (C : BipartiteOperator a b) : Prop :=
  ∃ k : ℕ, ∃ A : Fin k → Operator a, ∃ B : Fin k → Operator b,
    (∀ i, (A i).PosSemidef) ∧ (∀ i, (B i).PosSemidef) ∧ C=∑ i, A i ⊗ₖ B i

namespace Separable

theorem product {X : Operator a} {Y : Operator b} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    Separable (X ⊗ₖ Y) := ⟨1,fun _ => X,fun _ => Y,fun _ => hX,fun _ => hY,by simp⟩

theorem zero : Separable (0 : BipartiteOperator a b) :=
  ⟨0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0,by simp⟩

theorem add {C D : BipartiteOperator a b} (hC : Separable C) (hD : Separable D) : Separable (C+D) := by
  obtain ⟨k,A,B,hA,hB,rfl⟩ := hC
  obtain ⟨l,X,Y,hX,hY,rfl⟩ := hD
  refine ⟨k+l,Fin.addCases A X,Fin.addCases B Y,?_,?_,?_⟩
  · intro i; refine Fin.addCases (fun j => by simpa using hA j) (fun j => by simpa using hX j) i
  · intro i; refine Fin.addCases (fun j => by simpa using hB j) (fun j => by simpa using hY j) i
  · simp [Fin.sum_univ_add]

theorem sum {ι : Type*} [Fintype ι] (C : ι → BipartiteOperator a b)
    (hC : ∀ i, Separable (C i)) : Separable (∑ i, C i) := by
  classical
  exact Finset.sum_induction C (fun C => Separable C) (fun _ _ => Separable.add) Separable.zero
    (fun i hi => hC i)

theorem smul {C : BipartiteOperator a b} (hC : Separable C) {t : ℝ} (ht : 0≤t) : Separable (t • C) := by
  obtain ⟨k,A,B,hA,hB,rfl⟩ := hC
  refine ⟨k,fun i => t • A i,B,fun i => (hA i).smul ht,hB,?_⟩
  simp [Finset.smul_sum,Matrix.smul_kronecker]

theorem positive {C : BipartiteOperator a b} (hC : Separable C) : C.PosSemidef := by
  obtain ⟨k,A,B,hA,hB,rfl⟩ := hC
  exact Finset.sum_induction _ (fun C : BipartiteOperator a b => C.PosSemidef) (fun _ _ hX hY => hX.add hY)
    Matrix.PosSemidef.zero (fun i hi => MatrixMap.posSemidef_kronecker (hA i) (hB i))

theorem ppt {C : BipartiteOperator a b} (hC : Separable C) : (partialTranspose C).PosSemidef := by
  obtain ⟨k,A,B,hA,hB,rfl⟩ := hC
  have he : partialTranspose (∑ i, A i ⊗ₖ B i) = ∑ i, A i ⊗ₖ (B i).transpose := by
    ext i j; simp [partialTranspose,Matrix.sum_apply]
  rw [he]
  exact Finset.sum_induction _ (fun C : BipartiteOperator a b => C.PosSemidef) (fun _ _ hX hY => hX.add hY)
    Matrix.PosSemidef.zero (fun i hi => MatrixMap.posSemidef_kronecker (hA i) (hB i).transpose)

theorem reindex {a' b' : ℕ} {C : BipartiteOperator a b} (hC : Separable C)
    (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b') :
    Separable (Matrix.reindex (Equiv.prodCongr ea eb) (Equiv.prodCongr ea eb) C) := by
  obtain ⟨k,A,B,hA,hB,rfl⟩ := hC
  refine ⟨k,fun i => Matrix.reindex ea ea (A i),fun i => Matrix.reindex eb eb (B i),
    fun i => (hA i).submatrix _,fun i => (hB i).submatrix _,?_⟩
  ext i j
  simp [Matrix.reindex_apply,Matrix.sum_apply]

theorem left_filter {r : ℕ} {C : BipartiteOperator a b} (hC : Separable C)
    (L : Matrix (Fin r) (Fin a) ℂ) :
    Separable ((L ⊗ₖ (1:Operator b))*C*(L ⊗ₖ (1:Operator b))ᴴ) := by
  obtain ⟨k,A,B,hA,hB,rfl⟩ := hC
  refine ⟨k,fun i => L*A i*Lᴴ,B,fun i => (hA i).mul_mul_conjTranspose_same L,hB,?_⟩
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,Matrix.conjTranspose_one,Matrix.one_mul,Matrix.mul_one]

theorem amplify {c : ℕ} {C : BipartiteOperator a b} (hC : Separable C)
    (Φ : KrausChannel b c) : Separable (Φ.amplify a C) := by
  obtain ⟨k,A,B,hA,hB,rfl⟩ := hC
  refine ⟨k,A,fun i => Φ.apply (B i),hA,fun i => Φ.apply_positive (hB i),?_⟩
  rw [← MatrixMap.amplify_toLinearMap]
  ext ⟨i,x⟩ ⟨j,y⟩
  change Φ.toLinearMap (fun u v => (∑ s, A s ⊗ₖ B s) (i,u) (j,v)) x y = _
  have he : (fun u v => (∑ s, A s ⊗ₖ B s) (i,u) (j,v)) = ∑ s, A s i j • B s := by
    ext u v; simp [Matrix.sum_apply]
  rw [he,map_sum]
  simp [map_smul,Matrix.sum_apply,Matrix.smul_apply]
  rfl

end Separable

/-- Entanglement breaking on every finite reference and every positive input.
The cone formulation includes normalized states and their nonnegative multiples. -/
def IsEntanglementBreaking (Φ : KrausChannel a b) : Prop :=
  ∀ r, ∀ X : BipartiteOperator r a, X.PosSemidef → Separable (Φ.amplify r X)

/-- A rectangular coefficient matrix realizes the pure-input Choi congruence. -/
theorem amplify_outer_eq_choi {r : ℕ} (Φ : KrausChannel a b)
    (v : Fin r × Fin a → ℂ) :
    Φ.amplify r (Matrix.vecMulVec v (star v)) =
      ((fun i j => v (i,j)) ⊗ₖ (1:Operator b))*Φ.choi*
        ((fun i j => v (i,j)) ⊗ₖ (1:Operator b))ᴴ := by
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [KrausChannel.amplify_block]
  change Φ.toLinearMap (fun u w => v (i,u)*star (v (j,w))) x y = _
  rw [MatrixMap.apply_eq_sum_choi]
  simp only [MatrixMap.choi_toLinearMap]
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Matrix.one_apply,Finset.sum_mul,apply_ite]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u hu
  apply Finset.sum_congr rfl; intro w hw
  ring

/-- The operational property and separable Choi criterion are proved equivalent. -/
theorem entanglementBreaking_iff_separable_choi (Φ : KrausChannel a b) :
    IsEntanglementBreaking Φ ↔ Separable Φ.choi := by
  constructor
  · intro h
    have hh := h a (MatrixMap.maximallyEntangled a) (MatrixMap.maximallyEntangled_positive a)
    rw [← MatrixMap.amplify_toLinearMap,MatrixMap.amplify_maximallyEntangled,MatrixMap.choi_toLinearMap] at hh
    exact hh
  · intro h r X hX
    let S := CFC.sqrt X
    have hS : S*Sᴴ=X := by
      have hs : Sᴴ=S := (CFC.sqrt_nonneg X).posSemidef.isHermitian.eq
      rw [hs]
      exact CFC.sqrt_mul_sqrt_self _ hX.nonneg
    have he : X=∑ j : Fin r × Fin a, Matrix.vecMulVec (fun i => S i j) (star (fun i => S i j)) := by
      rw [← hS]
      ext i j
      simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.sum_apply,Matrix.vecMulVec,Pi.star_apply]
    rw [he]
    have hsum : Φ.amplify r (∑ j : Fin r × Fin a,
        Matrix.vecMulVec (fun i => S i j) (star (fun i => S i j))) =
        ∑ j : Fin r × Fin a, Φ.amplify r (Matrix.vecMulVec (fun i => S i j) (star (fun i => S i j))) := by
      simp only [KrausChannel.amplify,Matrix.mul_sum,Matrix.sum_mul]
      rw [Finset.sum_comm]
    rw [hsum]
    apply Separable.sum
    intro j
    rw [amplify_outer_eq_choi]
    exact h.left_filter _

/-- Entanglement breaking implies PPT, with the full output transposed. -/
theorem entanglementBreaking_isPPT (Φ : KrausChannel a b) (hΦ : IsEntanglementBreaking Φ) :
    IsPPT Φ.toLinearMap := ((entanglementBreaking_iff_separable_choi Φ).mp hΦ).ppt


/-- Tensor separable operators, regrouping both reference factors before both outputs. -/
theorem Separable.tensor_shuffle {c d : ℕ} {C : BipartiteOperator a b} {D : BipartiteOperator c d}
    (hC : Separable C) (hD : Separable D) :
    Separable (Matrix.reindex (MatrixMap.choiShuffle a b c d) (MatrixMap.choiShuffle a b c d) (C ⊗ₖ D)) := by
  obtain ⟨k,A,B,hA,hB,rfl⟩ := hC
  obtain ⟨l,X,Y,hX,hY,rfl⟩ := hD
  let L (p : Fin k × Fin l) : Operator (a*c) :=
    Matrix.reindex finProdFinEquiv finProdFinEquiv (A p.1 ⊗ₖ X p.2)
  let R (p : Fin k × Fin l) : Operator (b*d) :=
    Matrix.reindex finProdFinEquiv finProdFinEquiv (B p.1 ⊗ₖ Y p.2)
  refine ⟨k*l,fun i => L (finProdFinEquiv.symm i),fun i => R (finProdFinEquiv.symm i),?_,?_,?_⟩
  · intro i
    exact (MatrixMap.posSemidef_kronecker (hA _) (hX _)).submatrix _
  · intro i
    exact (MatrixMap.posSemidef_kronecker (hB _) (hY _)).submatrix _
  · rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type]
    ext ⟨i,x⟩ ⟨j,y⟩
    simp [L,R,Matrix.reindex_apply,MatrixMap.choiShuffle,Matrix.sum_apply,
      Finset.sum_mul,Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p hp
    apply Finset.sum_congr rfl; intro q hq
    ring

theorem compose_amplify {c : ℕ} (Ψ : KrausChannel b c) (Φ : KrausChannel a b)
    (r : ℕ) (X : BipartiteOperator r a) :
    (Ψ.compose Φ).amplify r X = Ψ.amplify r (Φ.amplify r X) := by
  have he : (Ψ.compose Φ).toLinearMap = Ψ.toLinearMap.comp Φ.toLinearMap := by
    ext Y i j
    exact congrFun (congrFun (KrausChannel.compose_apply Ψ Φ Y) i) j
  rw [← MatrixMap.amplify_toLinearMap,he,← MatrixMap.amplify_toLinearMap,
    ← MatrixMap.amplify_toLinearMap]
  rfl

theorem IsEntanglementBreaking.postcompose {c : ℕ} {Φ : KrausChannel a b}
    (hΦ : IsEntanglementBreaking Φ) (Ψ : KrausChannel b c) : IsEntanglementBreaking (Ψ.compose Φ) := by
  intro r X hX
  rw [compose_amplify]
  exact (hΦ r X hX).amplify Ψ

theorem IsEntanglementBreaking.precompose {c : ℕ} {Φ : KrausChannel a b}
    (hΦ : IsEntanglementBreaking Φ) (Ψ : KrausChannel c a) : IsEntanglementBreaking (Φ.compose Ψ) := by
  intro r X hX
  rw [compose_amplify]
  exact hΦ r _ (Ψ.amplify_positive r hX)

theorem IsEntanglementBreaking.reindex {a' b' : ℕ} {Φ : KrausChannel a b}
    (hΦ : IsEntanglementBreaking Φ) (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b') :
    IsEntanglementBreaking (reindexChannel ea eb Φ) := by
  apply (entanglementBreaking_iff_separable_choi _).mpr
  rw [reindexChannel_choi]
  exact ((entanglementBreaking_iff_separable_choi Φ).mp hΦ).reindex ea eb

theorem IsEntanglementBreaking.tensor {c d : ℕ} {Φ : KrausChannel a b} {Ψ : KrausChannel c d}
    (hΦ : IsEntanglementBreaking Φ) (hΨ : IsEntanglementBreaking Ψ) :
    IsEntanglementBreaking (Φ.tensor Ψ) := by
  apply (entanglementBreaking_iff_separable_choi _).mpr
  rw [← MatrixMap.choi_toLinearMap,← MatrixMap.tensor_kraus_toLinearMap,MatrixMap.choi_tensor]
  exact ((entanglementBreaking_iff_separable_choi Φ).mp hΦ).tensor_shuffle
    ((entanglementBreaking_iff_separable_choi Ψ).mp hΨ)

theorem replacer_entanglementBreaking (d : ℕ) (ω : State b) :
    IsEntanglementBreaking (ReplacerChannel.channel d ω) := by
  apply (entanglementBreaking_iff_separable_choi _).mpr
  rw [ReplacerChannel.channel_choi]
  exact Separable.product Matrix.PosSemidef.one ω.positive

/-- The family uses separable Choi matrices, now proved equivalent to the operational definition. -/
def EBFamily (a b : ℕ) : AlternativeFamily a b := fun n =>
  {Φ | IsChannel Φ ∧ Separable (MatrixMap.choi Φ)}

theorem mem_EBFamily_iff (n : ℕ) (Φ : KrausChannel (a^n) (b^n)) :
    Φ.toLinearMap ∈ EBFamily a b n ↔ IsEntanglementBreaking Φ := by
  rw [entanglementBreaking_iff_separable_choi]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,h⟩

theorem EBFamily_subset_PPTFamily (n : ℕ) : EBFamily a b n ⊆ PPTFamily a b n := by
  intro Φ hΦ
  exact ⟨hΦ.1,hΦ.2.ppt⟩

theorem eb_quantitative (τ : State a) (hτ : τ.matrix.PosDef) : QuantitativeAt (EBFamily a b) τ where
  faithful := hτ
  permutation_closed n hn π Φ hΦ := by
    apply (mem_EBFamily_iff _ _).mpr
    exact ((mem_EBFamily_iff _ _).mp hΦ).reindex _ _
  marginal_closed n hn Φ hΦ := by
    apply (mem_EBFamily_iff _ _).mpr
    have h := ((mem_EBFamily_iff _ _).mp hΦ).reindex
      (channelAddEquiv a n 1).symm (channelAddEquiv b n 1).symm
    exact (h.precompose _).postcompose _

end GeneralizedChannelStein
