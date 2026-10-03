import GeneralizedChannelStein.HeisenbergTensor

/-! Literal site-preserving tensor UCP action and transport of finite local expansions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.TensorLocalLift
open QuantumChannelStein Matrix LocalExpansion SiteGrouping HeisenbergTensor
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b n : ℕ}

/-- The actual n-fold channel adjoint in site-string coordinates. -/
def action (Φ : KrausChannel a b) (n : ℕ) : Block (Fin b) n →ₗ[ℂ] Block (Fin a) n :=
  (Matrix.reindexLinearEquiv ℂ ℂ (encode a n).symm (encode a n).symm).toLinearMap.comp
    ((heisenbergMap (Φ.tensorPower n)).comp
      (Matrix.reindexLinearEquiv ℂ ℂ (encode b n) (encode b n)).toLinearMap)

theorem flatten_action (Φ : KrausChannel a b) (n : ℕ) (X : Block (Fin b) n) :
    flatten (action Φ n X)=heisenbergMap (Φ.tensorPower n) (flatten X) := by
  ext i j
  simp [action,flatten,Matrix.reindex_apply,Matrix.submatrix_submatrix]

theorem norm_action_le (Φ : KrausChannel a b) (n : ℕ) (X : Block (Fin b) n) :
    ‖action Φ n X‖≤‖X‖ := by
  rw [← norm_flatten (action Φ n X),flatten_action,← norm_flatten X]
  exact norm_heisenbergMap_le _ _

theorem action_one (Φ : KrausChannel a b) (n : ℕ) : action Φ n 1=1 := by
  change Matrix.reindex (encode a n).symm (encode a n).symm
    (heisenbergMap (Φ.tensorPower n) (Matrix.reindex (encode b n) (encode b n) 1))=1
  rw [show Matrix.reindex (encode b n) (encode b n) (1:Block (Fin b) n)=1 from
    Matrix.reindexLinearEquiv_one ℂ ℂ _,heisenbergMap_one]
  exact Matrix.reindexLinearEquiv_one ℂ ℂ _

theorem supported_action (Φ : KrausChannel a b) (n : ℕ) (S : Finset (Fin n))
    (X : Block (Fin b) n) (hX : SupportedOn S X) : SupportedOn S (action Φ n X) := by
  obtain ⟨B,rfl⟩ := hX
  let e : LocalIndex (Fin a) S ≃ Fin (a^S.card) :=
    (Equiv.arrowCongr (supportEnum S).symm (Equiv.refl _)).trans (encode a S.card)
  let C := heisenbergMap (Φ.tensorPower S.card) (localMatrix S B)
  let B' := Matrix.reindex e.symm e.symm C
  refine ⟨B',?_⟩
  apply (Matrix.reindexLinearEquiv ℂ ℂ (encode a n) (encode a n)).injective
  change flatten (action Φ n (embed S B))=flatten (embed S B')
  apply (Matrix.reindexLinearEquiv ℂ ℂ (groupIndex a S) (groupIndex a S)).injective
  change Matrix.reindex (groupIndex a S) (groupIndex a S) (flatten (action Φ n (embed S B))) =
    Matrix.reindex (groupIndex a S) (groupIndex a S) (flatten (embed S B'))
  rw [flatten_action,group_apply,group_embed,tensor_product,heisenbergMap_one,group_embed]
  have he : localMatrix S B'=C := by
    change Matrix.reindex e e (Matrix.reindex e.symm e.symm C)=C
    ext i j
    simp [Matrix.reindex_apply,Matrix.submatrix_submatrix]
  rw [he]

/-- Apply the genuine tensor UCP map to each factor. Coefficients and chosen
supports are unchanged, so cost and support budgets are preserved exactly. -/
def expansion (Φ : KrausChannel a b) (E : Expansion (Fin b) n) : Expansion (Fin a) n where
  terms := E.terms
  finiteTerms := E.finiteTerms
  coeff := E.coeff
  factor i := action Φ n (E.factor i)
  sites := E.sites
  supported i := supported_action Φ n (E.sites i) (E.factor i) (E.supported i)
  contraction i := (norm_action_le Φ n _).trans (E.contraction i)

theorem expansion_value (Φ : KrausChannel a b) (E : Expansion (Fin b) n) :
    (expansion Φ E).value=action Φ n E.value := by
  simp [Expansion.value,expansion,map_sum,map_smul]

theorem expansion_cost (Φ : KrausChannel a b) (E : Expansion (Fin b) n) :
    (expansion Φ E).cost=E.cost := rfl

theorem expansion_size (Φ : KrausChannel a b) (E : Expansion (Fin b) n)
    {r : ℕ} (hE : E.HasSize r) : (expansion Φ E).HasSize r := hE

end GeneralizedChannelStein.TensorLocalLift
