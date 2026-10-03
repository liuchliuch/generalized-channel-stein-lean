import QuantumChannelStein.TwoRateScalars

/-! # Exact scalar rate accounting for whole blocks and ignored remainders -/
namespace QuantumChannelStein.ParallelSteinAssembly
open Filter
open scoped Topology

theorem tendsto_nat_div_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ => N / k) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  filter_upwards [eventually_ge_atTop (M * k)] with N hN
  exact (Nat.le_div_iff_mul_le hk).mpr hN

/-- A strict within-block rate gap absorbs every exact remainder for all
large total blocklengths; no asymptotic tensor or rate assumption occurs. -/
theorem eventually_block_cost_ge (k : ℕ) (hk : 0 < k) (R u : ℝ)
    (hR : 0 ≤ R) (hgap : (k : ℝ) * R < u) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) * R ≤ (N / k : ℕ) * u := by
  have hg : 0 < u - (k : ℝ) * R := sub_pos.mpr hgap
  have hm : ∀ᶠ N : ℕ in atTop,
      (k : ℝ) * R / (u - (k : ℝ) * R) ≤ (N / k : ℕ) :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).comp
      (tendsto_nat_div_atTop k hk)).eventually (eventually_ge_atTop _)
  filter_upwards [hm] with N hN
  have hbudget := (div_le_iff₀ hg).mp hN
  have hrem : ((N % k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.mod_lt N hk).le
  have hdecomp : (N : ℝ) = (k : ℝ) * (N / k : ℕ) + (N % k : ℕ) := by
    exact_mod_cast (Nat.div_add_mod N k).symm
  have hremcost := mul_le_mul_of_nonneg_right hrem hR
  rw [hdecomp]
  nlinarith

end QuantumChannelStein.ParallelSteinAssembly
