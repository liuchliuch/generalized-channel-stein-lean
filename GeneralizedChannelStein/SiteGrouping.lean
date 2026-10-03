import GeneralizedChannelStein.LocalExpansion
import GeneralizedChannelStein.RepeatedBlocks
import GeneralizedChannelStein.QuantitativeFamilies
import Mathlib.Data.Finset.Sort

/-! # Simultaneous site grouping, preserving literal finite supports -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.SiteGrouping
open QuantumChannelStein Matrix TensorPower ChannelPowerReindex LocalExpansion RepeatedBlocks
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
variable {n d : ℕ}

/-- The physical numerical coordinates associated to a site string. -/
def encode (d n : ℕ) : (Fin n → Fin d) ≃ Fin (d^n) :=
  (indexEquiv (Fin d) n).symm.trans (channelIndexEquiv d n)

def flatten (F : Block (Fin d) n) : Operator (d^n) := Matrix.reindex (encode d n) (encode d n) F

@[simp] theorem norm_flatten (F : Block (Fin d) n) : ‖flatten F‖=‖F‖ := TensorPower.norm_reindex _ _ _

theorem card_compl (S : Finset (Fin n)) : (Sᶜ).card=n-S.card := by simpa only [Fintype.card_fin] using Finset.card_compl S

def supportEnum (S : Finset (Fin n)) : Fin S.card ≃ {i // i∈S} := (S.orderIsoOfFin rfl).toEquiv

def complementEnum (S : Finset (Fin n)) : Fin (n-S.card) ≃ {i // i∉S} :=
  ((Sᶜ).orderIsoOfFin (card_compl S)).toEquiv |>.trans
    { toFun := fun i => ⟨i.val,Finset.mem_compl.mp i.property⟩
      invFun := fun i => ⟨i.val,Finset.mem_compl.mpr i.property⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }

theorem keep_add_card (S : Finset (Fin n)) : n-S.card+S.card=n :=
  Nat.sub_add_cancel (by simpa using S.card_le_univ)

/-- Group complement sites first and chosen supporting sites last. -/
def groupSites (S : Finset (Fin n)) : Fin n ≃ Fin (n-S.card+S.card) :=
  (Equiv.sumCompl (fun i : Fin n => i∈S)).symm.trans
    ((Equiv.sumComm _ _).trans
      ((Equiv.sumCongr (complementEnum S).symm (supportEnum S).symm).trans finSumFinEquiv))

def permutation (S : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  (groupSites S).trans (finCongr (keep_add_card S))

@[simp] theorem groupSites_support (S : Finset (Fin n)) (i : Fin S.card) :
    groupSites S (supportEnum S i)=Fin.natAdd (n-S.card) i := by
  simp [groupSites,Equiv.sumCompl_symm_apply_of_pos,(supportEnum S i).property]

@[simp] theorem groupSites_complement (S : Finset (Fin n)) (i : Fin (n-S.card)) :
    groupSites S (complementEnum S i)=Fin.castAdd S.card i := by
  simp [groupSites,Equiv.sumCompl_symm_apply_of_neg,(complementEnum S i).property]

/-- Coordinate regrouping directly from the chosen support/complement enumerations. -/
def groupStrings (S : Finset (Fin n)) : (Fin n → Fin d) ≃
    (Fin (n-S.card) → Fin d) × (Fin S.card → Fin d) :=
  (splitEquiv S).trans ((Equiv.prodComm _ _).trans
    (Equiv.prodCongr (Equiv.arrowCongr (complementEnum S).symm (Equiv.refl _))
      (Equiv.arrowCongr (supportEnum S).symm (Equiv.refl _))))

def localMatrix (S : Finset (Fin n)) (B : Matrix (LocalIndex (Fin d) S) (LocalIndex (Fin d) S) ℂ) :
    Operator (d^S.card) := Matrix.reindex
      ((Equiv.arrowCongr (supportEnum S).symm (Equiv.refl _)).trans (encode d S.card))
      ((Equiv.arrowCongr (supportEnum S).symm (Equiv.refl _)).trans (encode d S.card)) B

def groupIndex (d : ℕ) (S : Finset (Fin n)) : Fin (d^n) ≃ Fin (d^(n-S.card)*d^S.card) :=
  (encode d n).symm.trans ((groupStrings S).trans
    ((Equiv.prodCongr (encode d (n-S.card)) (encode d S.card)).trans finProdFinEquiv))

/-- Grouping a supported operator yields identity on the retained sites and
its literal local factor on the final sites. -/
theorem group_embed (S : Finset (Fin n))
    (B : Matrix (LocalIndex (Fin d) S) (LocalIndex (Fin d) S) ℂ) :
    Matrix.reindex (groupIndex d S) (groupIndex d S) (flatten (embed S B)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Operator (d^(n-S.card))) ⊗ₖ localMatrix S B) := by
  ext i j
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨x,rfl⟩ := (encode d (n-S.card)).surjective i1
  obtain ⟨y,rfl⟩ := (encode d S.card).surjective i2
  obtain ⟨z,rfl⟩ := (encode d (n-S.card)).surjective j1
  obtain ⟨w,rfl⟩ := (encode d S.card).surjective j2
  simp [groupIndex,flatten,groupStrings,localMatrix,embed,Matrix.reindex_apply,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Equiv.arrowCongr,splitEquiv,
    Equiv.prodCongr_apply,Equiv.piEquivPiSubtypeProd]
  have hneg (i : {i : Fin n // i∉S}) : ¬ i.val∈S := i.property
  simp only [hneg,dite_false]
  have heq : (fun i : {i : Fin n // i∉S} => x ((complementEnum S).symm i)) =
      (fun i => z ((complementEnum S).symm i)) ↔ x=z := by
    constructor
    · intro h
      funext i
      have hi := congrFun h (complementEnum S i)
      simpa using hi
    · intro h
      rw [h]
  simp only [heq,Function.comp_def]

@[simp] theorem sitePermutation_encode (d n : ℕ) (π : Equiv.Perm (Fin n)) (x : Fin n→Fin d) :
    sitePermutation d n π (encode d n x)=encode d n (fun i => x (π.symm i)) := by
  simp [sitePermutation,encode,TensorPermutation.factorPermutation]

theorem encode_cast (d n m : ℕ) (h : n=m) (x : Fin n→Fin d) :
    finCongr (congrArg (d^·) h) (encode d n x)=
      encode d m (fun i => x ((finCongr h).symm i)) := by
  subst m
  rfl

theorem encode_append (d k r : ℕ) (x : Fin k→Fin d) (y : Fin r→Fin d) :
    encode d (k+r) (Fin.append x y)=
      finCongr (Nat.pow_add d k r).symm (finProdFinEquiv (encode d k x,encode d r y)) := by
  have hh : indexAddEquiv (Fin d) k r ((indexEquiv (Fin d) k).symm x,(indexEquiv (Fin d) r).symm y) =
      (indexEquiv (Fin d) (k+r)).symm (Fin.append x y) := by
    apply (indexEquiv (Fin d) (k+r)).injective
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp
  have he := channelConcatEquiv_apply d k r ((indexEquiv (Fin d) k).symm x) ((indexEquiv (Fin d) r).symm y)
  rw [hh] at he
  have hleft : channelConcatEquiv d k r (encode d k x,encode d r y)=
      channelAddEquiv d k r (finProdFinEquiv (encode d k x,encode d r y)) := by simp [channelAddEquiv]
  change channelConcatEquiv d k r (encode d k x,encode d r y)=encode d (k+r) (Fin.append x y) at he
  rw [hleft,channelAddEquiv_eq_cast] at he
  exact he.symm

/-- The site permutation generated by grouping is the same for all local
physical dimensions, exactly as required by F4. -/
theorem groupIndex_eq_sitePermutation (d : ℕ) (S : Finset (Fin n)) :
    groupIndex d S=(sitePermutation d n (permutation S)).trans
      (finCongr ((Nat.pow_add d (n-S.card) S.card).symm.trans (congrArg (d^·) (keep_add_card S))).symm) := by
  ext i
  obtain ⟨x,rfl⟩ := (encode d n).surjective i
  simp only [Equiv.trans_apply,sitePermutation_encode]
  let l : Fin (n-S.card)→Fin d := fun j => x (complementEnum S j)
  let r : Fin S.card→Fin d := fun j => x (supportEnum S j)
  have happ : (fun i => x ((permutation S).symm i)) =
      fun i => (Fin.append l r) ((finCongr (keep_add_card S)).symm i) := by
    funext i
    obtain ⟨j,rfl⟩ := (finCongr (keep_add_card S)).surjective i
    simp only [Equiv.symm_apply_apply]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hj : (permutation S).symm (finCongr (keep_add_card S) (Fin.castAdd S.card j))=
          (complementEnum S j).val := by
        apply (permutation S).injective
        simp [permutation]
      simpa only [Fin.append_left,l] using congrArg x hj
    · have hj : (permutation S).symm (finCongr (keep_add_card S) (Fin.natAdd (n-S.card) j))=
          (supportEnum S j).val := by
        apply (permutation S).injective
        simp [permutation]
      simpa only [Fin.append_right,r] using congrArg x hj
  rw [happ,← encode_cast,encode_append]
  simp [groupIndex,groupStrings,l,r,Equiv.arrowCongr,splitEquiv,
    Equiv.piEquivPiSubtypeProd,finCongr_apply,Function.comp_def]

/-- Every chosen supported contraction becomes a true local contraction
under the same physical site grouping. -/
theorem exists_local_contraction (S : Finset (Fin n)) (F : Block (Fin d) n)
    (hS : SupportedOn S F) (hF : ‖F‖≤1) (hd : 0<d) :
    ∃ G : Operator (d^S.card), ‖G‖≤1 ∧
      Matrix.reindex (groupIndex d S) (groupIndex d S) (flatten F)=
        Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Operator (d^(n-S.card))) ⊗ₖ G) := by
  obtain ⟨B,rfl⟩ := hS
  refine ⟨localMatrix S B,?_,group_embed S B⟩
  have hh : ‖Matrix.reindex (groupIndex d S) (groupIndex d S) (flatten (embed S B))‖≤1 := by
    rw [TensorPower.norm_reindex,norm_flatten]
    exact hF
  rw [group_embed,TensorPower.norm_reindex] at hh
  letI : Nonempty (Fin (d^(n-S.card))) := ⟨⟨0,pow_pos hd _⟩⟩
  rwa [TensorNorm.one_kronecker_opNorm] at hh

theorem groupIndex_eq_permutation_add (d : ℕ) (S : Finset (Fin n)) :
    groupIndex d S=((sitePermutation d n (permutation S)).trans
      (finCongr (congrArg (d^·) (keep_add_card S).symm))).trans
        (channelAddEquiv d (n-S.card) S.card).symm := by
  rw [groupIndex_eq_sitePermutation,channelAddEquiv_eq_cast]
  ext i
  rfl

theorem sitePermutation_symm (d n : ℕ) (π : Equiv.Perm (Fin n)) :
    sitePermutation d n π.symm=(sitePermutation d n π).symm := by
  ext i
  apply congrArg Fin.val
  apply (sitePermutation d n π).injective
  rw [Equiv.apply_symm_apply]
  obtain ⟨x,rfl⟩ := (encode d n).surjective i
  simp only [sitePermutation_encode,Equiv.symm_symm,Equiv.apply_symm_apply]

end GeneralizedChannelStein.SiteGrouping
