import GeneralizedChannelStein.WeightedPowers
import GeneralizedChannelStein.AuxiliaryExtensions

/-! Unital completely positive lifting along a genuine rectangular isometry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.IsometryLift
open QuantumChannelStein Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a d : ℕ}

def complement (J : Matrix (Fin d) (Fin a) ℂ) : Operator d := 1-J*Jᴴ

theorem complement_hermitian (J : Matrix (Fin d) (Fin a) ℂ) :
    (complement J).IsHermitian := by
  unfold complement Matrix.IsHermitian
  simp

theorem complement_mul_isometry (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    complement J*J=0 := by
  simp [complement,Matrix.sub_mul,Matrix.mul_assoc,hJ]

theorem complement_sq (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    complement J*complement J=complement J := by
  have h : (J*Jᴴ)*(J*Jᴴ)=J*Jᴴ := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc Jᴴ J Jᴴ,hJ,Matrix.one_mul]
  simp only [complement,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,h]
  abel

/-- Recovery from the isometric image, completing its orthogonal complement
with a fixed output state. Its Heisenberg adjoint is unital on the entire space. -/
def recovery (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a) : KrausChannel d a where
  rank := 1+d
  kraus := Fin.addCases (fun _ : Fin 1 => Jᴴ) (KrausRecovery.rowKraus (complement J) z)
  normalized := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right,Fin.sum_univ_one,
      Matrix.conjTranspose_conjTranspose,KrausRecovery.sum_rowKraus_gram]
    rw [(complement_hermitian J).eq,complement_sq J hJ]
    simp [complement]

/-- The full operator-norm contractive unital CP extension of an input operator. -/
def lift (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a) : MatrixMap a d :=
  heisenbergMap (recovery J hJ z)

theorem lift_cp (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a) :
    MatrixMap.CompletelyPositive (lift J hJ z) := heisenbergMap_cp _

theorem lift_one (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a) :
    lift J hJ z 1=1 := heisenbergMap_one _

theorem norm_lift_le (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a) (X : Operator a) :
    ‖lift J hJ z X‖≤‖X‖ := norm_heisenbergMap_le _ _

theorem row_complement_mul (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (z : Fin a) (i : Fin d) : KrausRecovery.rowKraus (complement J) z i * J=0 := by
  ext u v
  by_cases hu : u=z
  · subst u
    simpa [Matrix.mul_apply,KrausRecovery.rowKraus] using congrFun (congrFun (complement_mul_isometry J hJ) i) v
  · simp [Matrix.mul_apply,KrausRecovery.rowKraus,hu]

/-- Exact intertwining, valid for every input operator, not just Hermitian ones. -/
theorem lift_mul_isometry (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (z : Fin a) (X : Operator a) : lift J hJ z X * J=J*X := by
  rw [lift,heisenbergMap_apply]
  change (∑ i : Fin (1+d), ((recovery J hJ z).kraus i)ᴴ*X*(recovery J hJ z).kraus i)*J=J*X
  rw [Fin.sum_univ_add]
  simp only [recovery,Fin.addCases_left,Fin.addCases_right,Fin.sum_univ_one,
    Matrix.conjTranspose_conjTranspose,Matrix.add_mul,Matrix.sum_mul]
  simp only [Matrix.mul_assoc,hJ,Matrix.mul_one,row_complement_mul,Matrix.mul_zero,
    Finset.sum_const_zero,add_zero]

end GeneralizedChannelStein.IsometryLift
