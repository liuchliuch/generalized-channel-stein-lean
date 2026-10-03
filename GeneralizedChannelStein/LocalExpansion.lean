import QuantumChannelStein.TensorPower
import QuantumChannelStein.SharpTensorTransport

/-! Literal finite-site support and costed contraction expansions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.LocalExpansion
open QuantumChannelStein Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {k : ℕ}

abbrev Block (ι : Type u) (k : ℕ) := Matrix (Fin k → ι) (Fin k → ι) ℂ
abbrev LocalIndex (ι : Type u) (S : Finset (Fin k)) := (i : {i // i∈S}) → ι

def splitEquiv (S : Finset (Fin k)) : (Fin k → ι) ≃
    LocalIndex ι S × ((i : {i // i∉S}) → ι) :=
  Equiv.piEquivPiSubtypeProd (·∈S) (fun _ => ι)

/-- A literal operator on S tensored with identity on the complement. -/
def embed (S : Finset (Fin k)) (B : Matrix (LocalIndex ι S) (LocalIndex ι S) ℂ) : Block ι k :=
  Matrix.reindex (splitEquiv S).symm (splitEquiv S).symm (B ⊗ₖ 1)

/-- Chosen site support, explicitly witnessed by a tensor factor. -/
def SupportedOn (S : Finset (Fin k)) (A : Block ι k) : Prop := ∃ B, A=embed S B

theorem embed_apply (S : Finset (Fin k)) (B : Matrix (LocalIndex ι S) (LocalIndex ι S) ℂ)
    (x y : Fin k → ι) :
    embed S B x y = B (fun i => x i) (fun i => y i) *
      if (fun i : {i // i∉S} => x i) = (fun i : {i // i∉S} => y i) then 1 else 0 := by
  simp [embed, Matrix.reindex_apply, splitEquiv, Matrix.kronecker_apply, Matrix.one_apply]

theorem embed_mul (S : Finset (Fin k)) (B C : Matrix (LocalIndex ι S) (LocalIndex ι S) ℂ) :
    embed S (B*C) = embed S B * embed S C := by
  unfold embed
  rw [← SupportedGeometricMean.reindex_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

@[simp] theorem embed_one (S : Finset (Fin k)) : embed S (1 : Matrix (LocalIndex ι S) (LocalIndex ι S) ℂ) = 1 := by
  simp [embed, Matrix.one_kronecker_one, Matrix.reindex_apply]

@[simp] theorem embed_zero (S : Finset (Fin k)) : embed S (0 : Matrix (LocalIndex ι S) (LocalIndex ι S) ℂ) = 0 := by
  simp [embed]

theorem norm_embed_le (S : Finset (Fin k)) (B : Matrix (LocalIndex ι S) (LocalIndex ι S) ℂ) :
    ‖embed S B‖ ≤ ‖B‖ := by
  rw [embed,TensorPower.norm_reindex]
  exact TensorNorm.kronecker_one_opNorm_le B

theorem supportedOn_one (S : Finset (Fin k)) : SupportedOn S (1 : Block ι k) := ⟨1,(embed_one S).symm⟩
theorem supportedOn_zero (S : Finset (Fin k)) : SupportedOn S (0 : Block ι k) := ⟨0,(embed_zero S).symm⟩

/-- Enlarging the chosen support only adds identity factors. -/
theorem SupportedOn.mono {S T : Finset (Fin k)} {A : Block ι k}
    (hA : SupportedOn S A) (hST : S⊆T) : SupportedOn T A := by
  classical
  obtain ⟨B,rfl⟩ := hA
  let r : LocalIndex ι T → LocalIndex ι S := fun x i => x ⟨i,hST i.property⟩
  let C : Matrix (LocalIndex ι T) (LocalIndex ι T) ℂ := fun x y =>
    B (r x) (r y) * if ∀ i : {i // i∈T}, i.val∉S → x i=y i then 1 else 0
  refine ⟨C,?_⟩
  ext x y
  rw [embed_apply,embed_apply]
  change B _ _ * (if _ then 1 else 0) =
    (B _ _ * if ∀ i : {i // i∈T}, i.val∉S → x i=y i then 1 else 0) *
      (if (fun i : {i // i∉T} => x i)=(fun i : {i // i∉T} => y i) then 1 else 0)
  have heq : ((fun i : {i // i∉S} => x i)=(fun i : {i // i∉S} => y i)) ↔
      (∀ i : {i // i∈T}, i.val∉S → x i=y i) ∧
        ((fun i : {i // i∉T} => x i)=(fun i : {i // i∉T} => y i)) := by
    constructor
    · intro h
      constructor
      · intro i hi
        exact congrFun h ⟨i,hi⟩
      · funext i
        exact congrFun h ⟨i,fun hi => i.property (hST hi)⟩
    · rintro ⟨h₁,h₂⟩
      funext i
      by_cases hi : i.val∈T
      · exact h₁ ⟨i,hi⟩ i.property
      · exact congrFun h₂ ⟨i,hi⟩
  simp only [heq]
  split_ifs <;> simp_all [r]

/-- Products have literal support on the union, including overlapping supports. -/
theorem SupportedOn.mul {S T : Finset (Fin k)} {A B : Block ι k}
    (hA : SupportedOn S A) (hB : SupportedOn T B) : SupportedOn (S∪T) (A*B) := by
  obtain ⟨A',rfl⟩ := hA.mono (show S ⊆ S∪T from Finset.subset_union_left)
  obtain ⟨B',rfl⟩ := hB.mono (show T ⊆ S∪T from Finset.subset_union_right)
  exact ⟨A'*B',(embed_mul _ _ _).symm⟩

/-- A finite contraction expansion with literal support witnesses. -/
structure Expansion (ι : Type u) [Fintype ι] [DecidableEq ι] (k : ℕ) where
  terms : Type
  finiteTerms : Fintype terms
  coeff : terms → ℂ
  factor : terms → Block ι k
  sites : terms → Finset (Fin k)
  supported : ∀ i, SupportedOn (sites i) (factor i)
  contraction : ∀ i, ‖factor i‖ ≤ 1
attribute [instance] Expansion.finiteTerms

namespace Expansion
variable (E F : Expansion ι k)
def value : Block ι k := ∑ i, E.coeff i • E.factor i
def cost : ℝ := ∑ i, ‖E.coeff i‖
def HasSize (s : ℕ) : Prop := ∀ i, (E.sites i).card ≤ s

theorem cost_nonneg : 0 ≤ E.cost := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem hasSize_sites : E.HasSize k := by
  intro i
  exact (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)

/-- Arbitrary complex scalar multiplication affects only the coefficients. -/
def scale (c : ℂ) : Expansion ι k where
  terms := E.terms
  finiteTerms := E.finiteTerms
  coeff i := c * E.coeff i
  factor := E.factor
  sites := E.sites
  supported := E.supported
  contraction := E.contraction

@[simp] theorem value_scale (c : ℂ) : (E.scale c).value = c • E.value := by
  simp [value,scale,SemigroupAction.mul_smul,Finset.smul_sum]
@[simp] theorem cost_scale (c : ℂ) : (E.scale c).cost = ‖c‖ * E.cost := by
  simp [cost,scale,norm_mul,Finset.mul_sum]
theorem hasSize_scale {s : ℕ} (h : E.HasSize s) (c : ℂ) : (E.scale c).HasSize s := h

/-- Sum concatenates the two finite expansions. -/
def add : Expansion ι k where
  terms := E.terms ⊕ F.terms
  finiteTerms := inferInstance
  coeff := Sum.elim E.coeff F.coeff
  factor := Sum.elim E.factor F.factor
  sites := Sum.elim E.sites F.sites
  supported := by intro i; cases i <;> simp [E.supported,F.supported]
  contraction := by intro i; cases i <;> simp [E.contraction,F.contraction]

@[simp] theorem value_add : (E.add F).value = E.value + F.value := by simp [value,add,Fintype.sum_sum_type]
@[simp] theorem cost_add : (E.add F).cost = E.cost + F.cost := by simp [cost,add,Fintype.sum_sum_type]
theorem hasSize_add {s : ℕ} (hE : E.HasSize s) (hF : F.HasSize s) : (E.add F).HasSize s := by
  intro i; cases i <;> simp_all [HasSize,add]

/-- Product coefficients multiply and chosen supports unite. -/
def mul : Expansion ι k where
  terms := E.terms × F.terms
  finiteTerms := inferInstance
  coeff i := E.coeff i.1 * F.coeff i.2
  factor i := E.factor i.1 * F.factor i.2
  sites i := E.sites i.1 ∪ F.sites i.2
  supported i := (E.supported i.1).mul (F.supported i.2)
  contraction i := (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul (E.contraction i.1) (F.contraction i.2) (norm_nonneg _) zero_le_one).trans_eq (by ring))

@[simp] theorem value_mul : (E.mul F).value = E.value * F.value := by
  simp only [value,mul,Fintype.sum_prod_type,Matrix.sum_mul,Matrix.mul_sum,
    Matrix.smul_mul,Matrix.mul_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  rw [mul_comm]
@[simp] theorem cost_mul : (E.mul F).cost = E.cost * F.cost := by
  simp only [cost,mul,Fintype.sum_prod_type,norm_mul,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm
theorem hasSize_mul {s t : ℕ} (hE : E.HasSize s) (hF : F.HasSize t) : (E.mul F).HasSize (s+t) := by
  intro i
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hE i.1) (hF i.2))

/-- A single supported contraction with unit coefficient. -/
def single (A : Block ι k) (S : Finset (Fin k)) (hS : SupportedOn S A) (hA : ‖A‖≤1) : Expansion ι k where
  terms := Unit
  finiteTerms := inferInstance
  coeff _ := 1
  factor _ := A
  sites _ := S
  supported _ := hS
  contraction _ := hA

@[simp] theorem value_single (A : Block ι k) (S : Finset (Fin k)) (hS : SupportedOn S A) (hA : ‖A‖≤1) :
    (single A S hS hA).value = A := by simp [single,value]
@[simp] theorem cost_single (A : Block ι k) (S : Finset (Fin k)) (hS : SupportedOn S A) (hA : ‖A‖≤1) :
    (single A S hS hA).cost = 1 := by simp [single,cost]

def one [Nonempty ι] : Expansion ι k := single 1 ∅ (supportedOn_one _) (by simp)
@[simp] theorem value_one [Nonempty ι] : (one (ι:=ι) (k:=k)).value = 1 := by simp [one]
@[simp] theorem cost_one [Nonempty ι] : (one (ι:=ι) (k:=k)).cost = 1 := by simp [one]
theorem hasSize_one [Nonempty ι] (s : ℕ) : (one (ι:=ι) (k:=k)).HasSize s := by simp [one,single,HasSize]

def sum {η : Type} [Fintype η] (G : η → Expansion ι k) : Expansion ι k where
  terms := Σ i, (G i).terms
  finiteTerms := inferInstance
  coeff j := (G j.1).coeff j.2
  factor j := (G j.1).factor j.2
  sites j := (G j.1).sites j.2
  supported j := (G j.1).supported j.2
  contraction j := (G j.1).contraction j.2

@[simp] theorem value_sum {η : Type} [Fintype η] (G : η → Expansion ι k) :
    (sum G).value = ∑ i, (G i).value := by simp [sum,value,Fintype.sum_sigma]
@[simp] theorem cost_sum {η : Type} [Fintype η] (G : η → Expansion ι k) :
    (sum G).cost = ∑ i, (G i).cost := by simp [sum,cost,Fintype.sum_sigma]
theorem hasSize_sum {η : Type} [Fintype η] (G : η → Expansion ι k) {s : ℕ}
    (hG : ∀ i, (G i).HasSize s) : (sum G).HasSize s := fun j => hG j.1 j.2

theorem HasSize.mono {E : Expansion ι k} {s t : ℕ} (h : E.HasSize s) (hst : s≤t) : E.HasSize t := fun i => (h i).trans hst

theorem hasSize_min {s : ℕ} (h : E.HasSize s) : E.HasSize (min k s) :=
  fun i => le_min (E.hasSize_sites i) (h i)

end Expansion

/-- The coordinate of a singleton site's Hilbert space. -/
def singletonEquiv (i : Fin k) : LocalIndex ι {i} ≃ ι where
  toFun x := x ⟨i,by simp⟩
  invFun x := fun _ => x
  left_inv x := by
    funext j
    apply congrArg x
    apply Subtype.ext
    exact (Finset.mem_singleton.mp j.property).symm
  right_inv x := rfl

/-- Place an actual local operator at one site and identity elsewhere. -/
def oneSite (i : Fin k) (A : Matrix ι ι ℂ) : Block ι k :=
  embed {i} (Matrix.reindex (singletonEquiv i).symm (singletonEquiv i).symm A)

theorem supportedOn_oneSite (i : Fin k) (A : Matrix ι ι ℂ) : SupportedOn {i} (oneSite i A) := ⟨_,rfl⟩
theorem norm_oneSite_le (i : Fin k) (A : Matrix ι ι ℂ) : ‖oneSite i A‖ ≤ ‖A‖ := by
  exact (norm_embed_le _ _).trans_eq (TensorPower.norm_reindex _ _ _)

def oneSiteExpansion (i : Fin k) (A : Matrix ι ι ℂ) (hA : ‖A‖≤1) : Expansion ι k :=
  Expansion.single (oneSite i A) {i} (supportedOn_oneSite i A) ((norm_oneSite_le i A).trans hA)
@[simp] theorem value_oneSiteExpansion (i : Fin k) (A : Matrix ι ι ℂ) (hA : ‖A‖≤1) :
    (oneSiteExpansion i A hA).value = oneSite i A := by simp [oneSiteExpansion]
@[simp] theorem cost_oneSiteExpansion (i : Fin k) (A : Matrix ι ι ℂ) (hA : ‖A‖≤1) :
    (oneSiteExpansion i A hA).cost = 1 := by simp [oneSiteExpansion]
theorem size_oneSiteExpansion (i : Fin k) (A : Matrix ι ι ℂ) (hA : ‖A‖≤1) :
    (oneSiteExpansion i A hA).HasSize 1 := by simp [oneSiteExpansion,Expansion.HasSize,Expansion.single]
/-- Matrix Chebyshev recurrence with exactly the scalar polynomial coefficients. -/
def chebyshevMatrix (X : Block ι k) : ℕ → Block ι k
  | 0 => 1
  | 1 => X
  | n+2 => (2:ℂ) • (X * chebyshevMatrix X (n+1)) - chebyshevMatrix X n

namespace Expansion
variable [Nonempty ι]
def chebyshev (E : Expansion ι k) : ℕ → Expansion ι k
  | 0 => one
  | 1 => E
  | n+2 => ((E.mul (chebyshev E (n+1))).scale 2).add ((chebyshev E n).scale (-1))

theorem value_chebyshev (E : Expansion ι k) (n : ℕ) :
    (E.chebyshev n).value = chebyshevMatrix E.value n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebyshev,chebyshevMatrix]
  | one => rfl
  | more n ih0 ih1 => simp [chebyshev,chebyshevMatrix,ih0,ih1,sub_eq_add_neg]

theorem size_chebyshev (E : Expansion ι k) (hE : E.HasSize 1) (n : ℕ) :
    (E.chebyshev n).HasSize n := by
  induction n using Nat.twoStepInduction with
  | zero => exact hasSize_one 0
  | one => exact hE
  | more n ih0 ih1 =>
    apply hasSize_add
    · exact hasSize_scale _ ((hasSize_mul E _ hE ih1).mono (by omega)) 2
    · exact hasSize_scale _ (ih0.mono (by omega)) (-1)

/-- A one-site expansion of cost at most seven gives the exact `15^n`
coefficient budget used by the product-image filter. -/
theorem cost_chebyshev (E : Expansion ι k) (hE : E.cost ≤ 7) (n : ℕ) :
    (E.chebyshev n).cost ≤ (15:ℝ)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebyshev]
  | one => simpa [chebyshev] using hE.trans (by norm_num : (7:ℝ)≤15)
  | more n ih0 ih1 =>
    simp only [chebyshev,cost_add,cost_scale,cost_mul]
    norm_num only [Complex.norm_ofNat, norm_neg, norm_one]
    have hcost := (E.chebyshev (n+1)).cost_nonneg
    have hm := mul_le_mul hE ih1 hcost (by norm_num : (0:ℝ)≤7)
    rw [pow_succ,pow_succ] at *
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤15) n]
end Expansion

end GeneralizedChannelStein.LocalExpansion
