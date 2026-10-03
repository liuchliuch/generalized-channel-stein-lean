import GeneralizedChannelStein.CorrelatedHull

/-! Explicit equality with the product of zeta/omega operators over partition fibers.
Empty fibers contribute one and are absent from the actual set partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix ChannelPowerReindex PerfectDiscrimination TensorPower
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {b : ℕ}

theorem bernoulli_fiber_product {n k : ℕ} (f : Fin n → Fin k) (p : Fin k → ℝ)
    (R W : Fin n → ℂ) :
    (∑ ξ : Fin k → Bool, (bernoulliWeight p ξ:ℂ)*∏ s, if ξ (f s) then R s else W s) =
      ∏ l : Fin k, ((p l:ℂ)*(∏ s : {s : Fin n // f s=l}, R s.1)+
        ((1-p l:ℝ):ℂ)*(∏ s : {s : Fin n // f s=l}, W s.1)) := by
  have h := Fintype.prod_sum (κ:=fun _ : Fin k => Bool)
    (fun l (x:Bool) => ((if x then p l else 1-p l:ℝ):ℂ)*
      ∏ s : {s : Fin n // f s=l}, if x then R s.1 else W s.1)
  have hout : (∏ l : Fin k, ∑ x : Bool, ((if x then p l else 1-p l:ℝ):ℂ)*
      ∏ s : {s : Fin n // f s=l}, if x then R s.1 else W s.1) =
      ∏ l : Fin k, ((p l:ℂ)*(∏ s : {s : Fin n // f s=l}, R s.1)+
        ((1-p l:ℝ):ℂ)*(∏ s : {s : Fin n // f s=l}, W s.1)) := by
    simp [Fintype.sum_bool]
  rw [←hout,h]
  apply Finset.sum_congr rfl; intro ξ hξ
  rw [Finset.prod_mul_distrib]
  have hw : (bernoulliWeight p ξ:ℂ)=∏ l : Fin k, ((if ξ l then p l else 1-p l:ℝ):ℂ) := by
    simp [bernoulliWeight]
  rw [hw]
  congr 1
  calc
    (∏ s : Fin n, if ξ (f s) then R s else W s) =
        ∏ l : Fin k, ∏ s : {s : Fin n // f s=l}, if ξ (f s.1) then R s.1 else W s.1 :=
      (Fintype.prod_fiberwise f (fun s => if ξ (f s) then R s else W s)).symm
    _ = _ := by
      apply Finset.prod_congr rfl; intro l hl
      apply Finset.prod_congr rfl; intro s hs
      rw [s.property]

/-- Matrix entries of a generator are exactly products of the stated block mixture entries. -/
theorem generator_block_formula (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) (d : PartitionDescription n) (i j : Index (Fin b) n) :
    (partitionGenerator ρ ω c hc hc1 n d).matrix (channelIndexEquiv b n i) (channelIndexEquiv b n j) =
    ∏ l : Fin n, if d.2 l then
      (c:ℂ)*(∏ s : {s : Fin n // d.1 s=l}, ρ.matrix (indexEquiv (Fin b) n i s.1) (indexEquiv (Fin b) n j s.1))+
      ((1-c:ℝ):ℂ)*(∏ s : {s : Fin n // d.1 s=l}, ω.matrix (indexEquiv (Fin b) n i s.1) (indexEquiv (Fin b) n j s.1))
    else ∏ s : {s : Fin n // d.1 s=l}, ω.matrix (indexEquiv (Fin b) n i s.1) (indexEquiv (Fin b) n j s.1) := by
  simp only [partitionGenerator,partitionState,ensembleState,Matrix.sum_apply,Matrix.smul_apply,
    Complex.real_smul,smul_eq_mul,productState_entry,apply_ite]
  have hm (x : Bool) (u v : Fin b) : (if x then ρ else ω).matrix u v =
      if x then ρ.matrix u v else ω.matrix u v := by cases x <;> rfl
  simp_rw [hm]
  rw [bernoulli_fiber_product]
  apply Finset.prod_congr rfl; intro l hl
  cases he : d.2 l <;> simp [blockProbability,he]

end GeneralizedChannelStein.Correlated
