import QuantumChannelStein.ChannelRenyiQuantitative
import QuantumChannelStein.RenyiRightLimitScalars

/-! # The right upper-limit half of Theorem 3.7

The value at and below one is assigned the already defined Umegaki rate;
this totalization has no effect on a limit from strictly above one.
The lower-limit half requires the separately proved state comparison
between Umegaki and sandwiched Rényi relative entropy.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ChannelRenyi
open Filter RenyiExponentialScalars
open scoped Topology
variable {n m : ℕ}

/-- Total real-order function for stating a right limit of the genuine alpha>1 rate. -/
def regularizedDAt (Φ Ψ : KrausChannel n m) (α : ℝ) : EReal :=
  if hα : 1 < α then regularizedD α hα Φ Ψ else ChannelEntropy.regularizedD Φ Ψ

theorem regularizedDAt_of_gt_one (Φ Ψ : KrausChannel n m) (α : ℝ) (hα : 1 < α) :
    regularizedDAt Φ Ψ α = regularizedD α hα Φ Ψ := dif_pos hα

/-- Every strict upper neighborhood of d contains all sufficiently near-right Rényi rates. -/
theorem eventually_regularizedDAt_lt (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤) (b : EReal)
    (hb : ChannelEntropy.regularizedD Φ Ψ < b) :
    ∀ᶠ α : ℝ in 𝓝[>] (1 : ℝ), regularizedDAt Φ Ψ α < b := by
  have hbot : ChannelEntropy.regularizedD Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (ChannelEntropy.regularizedD_nonneg Φ Ψ hn))
  have hcoe := EReal.coe_toReal hfinite.ne hbot
  apply eventually_lt_of_exponential_bounds (regularizedDAt Φ Ψ)
    (ChannelEntropy.regularizedD Φ Ψ).toReal _ b (by rwa [hcoe])
  intro S hS
  obtain ⟨L, γ, hγ, hbound⟩ := exists_quantitative_bound Φ Ψ hn hfinite S hS
  refine ⟨L, γ, hγ, ?_⟩
  intro α hα hα2
  rw [regularizedDAt_of_gt_one Φ Ψ α hα]
  exact hbound α hα hα2

/-- The domination upper bound uses the same exact pseudoinverse rate as Lemma 3.1. -/
theorem regularizedDAt_le_choi_rate (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤) (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2) :
    regularizedDAt Φ Ψ α ≤ (Real.logb 2 (Pseudoinverse.choiConstant Φ Ψ) : EReal) := by
  have hs := (ChannelEntropy.regularizedD_lt_top_iff_choi_support Φ Ψ hn).mp hfinite
  rw [regularizedDAt_of_gt_one Φ Ψ α hα]
  exact regularizedD_le_log2_of_cpLe α hα hα2 Φ Ψ _
    (Pseudoinverse.one_le_choiConstant Φ Ψ hn hs) (Pseudoinverse.cpLe_choiConstant Φ Ψ hs)

end QuantumChannelStein.ChannelRenyi
