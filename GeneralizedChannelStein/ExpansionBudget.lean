import GeneralizedChannelStein.FreeMultipliers
import GeneralizedChannelStein.CorrectedBranch

/-! Exact finite-support radius and positive weighted local-multiplier budget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.ExpansionBudget
open QuantumChannelStein Matrix LocalExpansion
open scoped BigOperators Matrix.Norms.L2Operator
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

def radius (E : Expansion ι n) : ℕ := Finset.univ.sup (fun i => (E.sites i).card)

theorem hasSize_radius (E : Expansion ι n) : E.HasSize (radius E) := by
  intro i
  exact Finset.le_sup (f:=fun i => (E.sites i).card) (Finset.mem_univ i)

theorem radius_le_real (E : Expansion ι n) {B : ℝ} (hB : 0≤B)
    (h : ∀ i, ((E.sites i).card:ℝ)≤B) : (radius E:ℝ)≤B := by
  have hr : radius E≤Nat.floor B := Finset.sup_le fun i _ => (Nat.le_floor (h i))
  exact (by exact_mod_cast hr : (radius E:ℝ)≤(Nat.floor B:ℝ)).trans (Nat.floor_le hB)

theorem norm_value_le_cost (E : Expansion ι n) : ‖E.value‖≤E.cost := by
  calc
    _ ≤ ∑ i, ‖E.coeff i • E.factor i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖E.coeff i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (E.contraction i)
    _ = _ := rfl

def weightedCost (E : Expansion ι n) (b : ℝ) : ℝ := ∑ i, ‖E.coeff i‖*b^(E.sites i).card

theorem cost_le_weightedCost (E : Expansion ι n) {b : ℝ} (hb : 1≤b) : E.cost≤weightedCost E b := by
  apply Finset.sum_le_sum
  intro i _
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hb)

theorem weightedCost_bound (E : Expansion ι n) {b : ℝ} (hb : 1≤b) {r : ℕ} (hr : E.HasSize r) :
    weightedCost E b≤E.cost*b^r := by
  rw [Expansion.cost,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (hr i)) (norm_nonneg _)

theorem weightedCost_pos (E : Expansion ι n) {b : ℝ} (hb : 1≤b) (hE : E.value≠0) :
    0<weightedCost E b :=
  (norm_pos_iff.mpr hE).trans_le ((norm_value_le_cost E).trans (cost_le_weightedCost E hb))

theorem norm_isometry_eq_one {a d : ℕ} (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a) :
    ‖J‖=1 := by
  letI : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
  have h := Matrix.l2_opNorm_conjTranspose_mul_self J
  rw [hJ] at h
  have h1 : ‖(1:Operator a)‖=1 := norm_one
  rw [h1] at h
  nlinarith [norm_nonneg J]

theorem value_ne_zero_of_close {a d : ℕ} (E : Expansion (Fin d) n)
    (J K : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    {ζ : ℝ} (hζ : ζ<1) (hclose : ‖SiteGrouping.flatten E.value*K-J‖≤ζ) : E.value≠0 := by
  intro he
  have hjn := norm_isometry_eq_one J hJ (pow_pos ha n)
  have hz : SiteGrouping.flatten E.value=0 := by rw [he]; rfl
  rw [hz,Matrix.zero_mul,zero_sub,norm_neg,hjn] at hclose
  linarith

end GeneralizedChannelStein.ExpansionBudget
