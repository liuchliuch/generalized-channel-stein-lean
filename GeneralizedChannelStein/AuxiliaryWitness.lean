import GeneralizedChannelStein.DilationTensor
import GeneralizedChannelStein.RepeatedBlocks
import GeneralizedChannelStein.UniformAuxiliary

/-! # Concrete auxiliary approximation witnesses and exact padding -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelDilationPower ChannelPowerReindex
  EnvironmentTensor DilationTensor ChannelTransport RepeatedBlocks
open scoped Kronecker Matrix.Norms.L2Operator

/-- All environmental spaces and maps are actual finite matrices. -/
structure AuxiliaryWitness {a b : ℕ} (N M : KrausChannel a b) (c δ : ℝ) where
  e : ℕ
  f : ℕ
  V : Matrix (Fin b × Fin e) (Fin a) ℂ
  W : Matrix (Fin b × Fin f) (Fin a) ℂ
  A : Matrix (Fin e) (Fin f) ℂ
  isometry : Vᴴ*V=1
  target_map : dilationMap V=N.toLinearMap
  dominator_map : dilationMap W=M.toLinearMap
  cost : ‖A‖^2 ≤ c
  error : ‖V-applyEnvironment W A‖ ≤ δ

namespace AuxiliaryWitness
variable {a b a' b' : ℕ} {N M : KrausChannel a b} {c δ : ℝ}

def transport (Wit : AuxiliaryWitness N M c δ)
    (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (N' M' : KrausChannel a' b')
    (hN : reindexMap ea eb N.toLinearMap=N'.toLinearMap)
    (hM : reindexMap ea eb M.toLinearMap=M'.toLinearMap) : AuxiliaryWitness N' M' c δ where
  e := Wit.e
  f := Wit.f
  V := Matrix.reindex (Equiv.prodCongr eb (Equiv.refl _)) ea Wit.V
  W := Matrix.reindex (Equiv.prodCongr eb (Equiv.refl _)) ea Wit.W
  A := Wit.A
  isometry := reindex_isometry _ _ _ Wit.isometry
  target_map := by rw [dilationMap_reindex,Wit.target_map,hN]
  dominator_map := by rw [dilationMap_reindex,Wit.dominator_map,hM]
  cost := Wit.cost
  error := by
    have he := TensorBlockReindex.applyEnvironment_reindex ea eb (Equiv.refl _) (Equiv.refl _)
      Wit.W Wit.A
    simp only [Matrix.reindex_refl_refl] at he
    rw [← he]
    change ‖Matrix.reindex (Equiv.prodCongr eb (Equiv.refl (Fin Wit.e))) ea
      (Wit.V-applyEnvironment Wit.W Wit.A)‖ ≤ δ
    rw [TensorPower.norm_reindex]
    exact Wit.error

def tensorExact {a₂ b₂ : ℕ} {N₂ M₂ : KrausChannel a₂ b₂} {c₂ : ℝ}
    (Wit : AuxiliaryWitness N M c δ) (Wit₂ : AuxiliaryWitness N₂ M₂ c₂ 0)
    (hc : 0 ≤ c) (hc₂ : 0 ≤ c₂) :
    AuxiliaryWitness (N.tensor N₂) (M.tensor M₂) (c*c₂) δ where
  e := Wit.e*Wit₂.e
  f := Wit.f*Wit₂.f
  V := tensorDilation Wit.V Wit₂.V
  W := tensorDilation Wit.W Wit₂.W
  A := tensorAuxiliary Wit.A Wit₂.A
  isometry := tensorDilation_isometry _ _ Wit.isometry Wit₂.isometry
  target_map := by rw [dilationMap_tensorDilation,Wit.target_map,Wit₂.target_map,MatrixMap.tensor_kraus_toLinearMap]
  dominator_map := by rw [dilationMap_tensorDilation,Wit.dominator_map,Wit₂.dominator_map,MatrixMap.tensor_kraus_toLinearMap]
  cost := by
    calc
      _ ≤ (‖Wit.A‖ * ‖Wit₂.A‖)^2 := pow_le_pow_left₀ (norm_nonneg (tensorAuxiliary Wit.A Wit₂.A)) (tensorAuxiliary_norm Wit.A Wit₂.A) 2
      _ = ‖Wit.A‖^2 * ‖Wit₂.A‖^2 := mul_pow _ _ _
      _ ≤ c*c₂ := mul_le_mul Wit.cost Wit₂.cost (sq_nonneg _) hc
  error := by
    have hExact : Wit₂.V = applyEnvironment Wit₂.W Wit₂.A :=
      sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm Wit₂.error (norm_nonneg _)))
    rw [← tensorDilation_environment, ← hExact, ← tensorDilation_sub_left]
    exact (tensorDilation_norm _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
      (UniformApproximation.norm_isometry_le_one _ Wit₂.isometry)).trans Wit.error)

/-- Convert the actual tensor-environment coefficient from a truncation proof. -/
def ofRepeated {e f : ℕ} (N M : KrausChannel a b)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (hV : Vᴴ*V=1) (hN : dilationMap V=N.toLinearMap) (hM : dilationMap W=M.toLinearMap)
    (m : ℕ) (A : Matrix (TensorPower.Index (Fin e) m) (TensorPower.Index (Fin f) m) ℂ)
    (c δ : ℝ) (hc : ‖A‖^2≤c)
    (he : ‖blockDilation V m-applyEnvironment (blockDilation W m) A‖≤δ) :
    AuxiliaryWitness (N.tensorPower m) (M.tensorPower m) c δ where
  e := e^m
  f := f^m
  V := powerDilation V m
  W := powerDilation W m
  A := finiteAuxiliary m A
  isometry := powerDilation_isometry V hV m
  target_map := dilationMap_powerDilation N V hN m
  dominator_map := dilationMap_powerDilation M W hM m
  cost := by simpa only [norm_finiteAuxiliary] using hc
  error := by simpa only [finiteAuxiliary_error] using he

/-- Exact CP domination has an exact concrete environmental witness. -/
def ofExact (N M : KrausChannel a b) (c : ℝ) (hc : 0 ≤ c)
    (h : MatrixMap.CPLe N.toLinearMap ((c : ℂ) • M.toLinearMap)) : AuxiliaryWitness N M c 0 := by
  apply Classical.choice
  obtain ⟨A,hA,he⟩ := UniformAuxiliary.lemma_6_exact N.stinespring M.stinespring c hc
    (by simpa only [ParallelConverse.dilationMap_stinespring] using h)
  refine ⟨⟨N.rank,M.rank,N.stinespring,M.stinespring,A,N.stinespring_isometry,
    ParallelConverse.dilationMap_stinespring N,ParallelConverse.dilationMap_stinespring M,?_,?_⟩⟩
  · exact (pow_le_pow_left₀ (norm_nonneg A) hA 2).trans_eq (Real.sq_sqrt hc)
  · simp only [EnvironmentTensor.applyEnvironment,he,norm_zero,le_refl]

/-- Transport repeated channel powers into the exact original-use coordinate spaces. -/
def repeatOriginal {a b k m : ℕ} (N : KrausChannel a b)
    (M : KrausChannel (a^k) (b^k)) {c δ : ℝ}
    (Wit : AuxiliaryWitness ((N.tensorPower k).tensorPower m) (M.tensorPower m) c δ) :
    AuxiliaryWitness (N.tensorPower (k*m)) (repeatBlock k m M) c δ :=
  Wit.transport (finCongr (Nat.pow_mul a k m).symm) (finCongr (Nat.pow_mul b k m).symm)
    _ _ (by rw [← reindexChannel_map,reindexChannel_finCongr]; exact repeatBlock_target_map N k m)
    (by rw [← reindexChannel_map,reindexChannel_finCongr]; rfl)

/-- Exact padding preserves the error and multiplies the true auxiliary cost. -/
def padOriginal {a b p q : ℕ} (N : KrausChannel a b)
    (M : KrausChannel (a^p) (b^p)) (R : KrausChannel (a^q) (b^q))
    {c d δ : ℝ} (Wit : AuxiliaryWitness (N.tensorPower p) M c δ)
    (Wit₂ : AuxiliaryWitness (N.tensorPower q) R d 0) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    AuxiliaryWitness (N.tensorPower (p+q)) (tensorBlocks p q M R) (c*d) δ :=
  (Wit.tensorExact Wit₂ hc hd).transport (channelAddEquiv a p q) (channelAddEquiv b p q) _ _
    (by rw [← reindexChannel_map]; exact tensorPower_add_toLinearMap N p q)
    (by rw [← reindexChannel_map]; rfl)

/-- Numerical blocklength equality is transported simultaneously in all types. -/
def castOriginal {a b p q : ℕ} (N : KrausChannel a b)
    (M : KrausChannel (a^p) (b^p)) {c δ : ℝ} (Wit : AuxiliaryWitness (N.tensorPower p) M c δ)
    (h : p=q) : AuxiliaryWitness (N.tensorPower q)
      (M.cast (congrArg (a^·) h) (congrArg (b^·) h)) c δ := by
  subst q
  exact Wit

end AuxiliaryWitness
end GeneralizedChannelStein
