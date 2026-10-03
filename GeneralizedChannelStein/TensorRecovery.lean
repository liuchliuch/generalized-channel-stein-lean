import GeneralizedChannelStein.TensorLocalLift
import GeneralizedChannelStein.IsometricBenchmarks

/-! Tensor-stable exact recovery and UCP intertwining on an isometric image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.TensorRecovery
open QuantumChannelStein Matrix ChannelPowerReindex IsometryLift
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b c d a' b' : ℕ}

/-- Every Kraus branch acts as a scalar identity on the encoded subspace. -/
def ScalarRecovery (Φ : KrausChannel b a) (J : Matrix (Fin b) (Fin a) ℂ) : Prop :=
  ∃ z : Fin Φ.rank → ℂ, ∀ i, Φ.kraus i*J=z i•(1:Operator a)

theorem scalarRecovery_intertwines (Φ : KrausChannel b a) (J : Matrix (Fin b) (Fin a) ℂ)
    (h : ScalarRecovery Φ J) (X : Operator a) : heisenbergMap Φ X*J=J*X := by
  obtain ⟨z,hz⟩ := h
  have hsum : ∑ i, z i•(Φ.kraus i)ᴴ=J := by
    have hh := congrArg (fun Y => Y*J) Φ.normalized
    simp only [Matrix.sum_mul,Matrix.mul_assoc,hz,Matrix.mul_smul,Matrix.mul_one,Matrix.one_mul] at hh
    exact hh
  rw [heisenbergMap_apply,Matrix.sum_mul]
  simp only [Matrix.mul_assoc,hz,Matrix.mul_smul,Matrix.mul_one]
  simp only [← Matrix.smul_mul]
  rw [← Matrix.sum_mul,hsum]

theorem recovery_scalar (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a) :
    ScalarRecovery (recovery J hJ z) J := by
  refine ⟨Fin.addCases (fun _ : Fin 1 => 1) (fun _ : Fin b => 0),?_⟩
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [recovery] using hJ
  · intro j
    simpa [recovery] using row_complement_mul J hJ z j

theorem scalarRecovery_tensor (Φ : KrausChannel b a) (Ψ : KrausChannel d c)
    (J : Matrix (Fin b) (Fin a) ℂ) (K : Matrix (Fin d) (Fin c) ℂ)
    (hΦ : ScalarRecovery Φ J) (hΨ : ScalarRecovery Ψ K) :
    ScalarRecovery (Φ.tensor Ψ) (Matrix.reindex finProdFinEquiv finProdFinEquiv (J ⊗ₖ K)) := by
  obtain ⟨x,hx⟩ := hΦ
  obtain ⟨y,hy⟩ := hΨ
  refine ⟨fun i => x (finProdFinEquiv.symm i).1*y (finProdFinEquiv.symm i).2,?_⟩
  intro i
  obtain ⟨⟨u,v⟩,rfl⟩ := finProdFinEquiv.surjective i
  simp only [KrausChannel.tensor,Equiv.symm_apply_apply,KrausChannel.tensorKraus]
  change Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (Φ.kraus u ⊗ₖ Ψ.kraus v) *
    Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (J ⊗ₖ K) = _
  rw [Matrix.reindexLinearEquiv_mul,← Matrix.mul_kronecker_mul,hx,hy,
    Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,Matrix.one_kronecker_one,map_smul,
    Matrix.reindexLinearEquiv_one]

theorem scalarRecovery_cast (Φ : KrausChannel b a) (J : Matrix (Fin b) (Fin a) ℂ)
    (h : ScalarRecovery Φ J) (ha : a=a') (hb : b=b') :
    ScalarRecovery (Φ.cast hb ha) (Matrix.reindex (finCongr hb) (finCongr ha) J) := by
  subst a'; subst b'; exact h

/-- Tensor product coordinates are exactly those used for physical channels. -/
theorem powerIsometry_succ (J : Matrix (Fin b) (Fin a) ℂ) (n : ℕ) :
    powerIsometry J (n+1) =
      Matrix.reindex (finCongr (show b*b^n=b^(n+1) by rw [Nat.pow_succ'])) (finCongr (show a*a^n=a^(n+1) by rw [Nat.pow_succ']))
        (Matrix.reindex finProdFinEquiv finProdFinEquiv (J ⊗ₖ powerIsometry J n)) := by
  ext i j
  rfl

theorem scalarRecovery_power (Φ : KrausChannel b a) (J : Matrix (Fin b) (Fin a) ℂ)
    (h : ScalarRecovery Φ J) (n : ℕ) : ScalarRecovery (Φ.tensorPower n) (powerIsometry J n) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 1,?_⟩
    intro i
    ext u v
    have huv : u=v := Fin.ext (by have hu := u.isLt; have hv := v.isLt; simp only [pow_zero] at hu hv; omega)
    simp [KrausChannel.tensorPower,KrausChannel.identity,powerIsometry,TensorPower.tensorPower,
      Matrix.reindex_apply,Matrix.one_apply,huv]
  | succ n ih =>
    rw [KrausChannel.tensorPower,powerIsometry_succ]
    exact scalarRecovery_cast _ _ (scalarRecovery_tensor Φ (Φ.tensorPower n) J (powerIsometry J n) h ih) _ _

theorem recovery_power_intertwines (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a)
    (n : ℕ) (X : Operator (a^n)) :
    heisenbergMap ((recovery J hJ z).tensorPower n) X * powerIsometry J n = powerIsometry J n*X :=
  scalarRecovery_intertwines _ _ (scalarRecovery_power _ _ (recovery_scalar J hJ z) n) X

end GeneralizedChannelStein.TensorRecovery
