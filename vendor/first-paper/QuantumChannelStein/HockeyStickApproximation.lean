import QuantumChannelStein.TestingPrimal
import QuantumChannelStein.TestingSDPStrong
import QuantumChannelStein.ApproximationFromDual
import QuantumChannelStein.AuxiliaryMinimum
import QuantumChannelStein.Purification
import QuantumChannelStein.ScalarBounds
import QuantumChannelStein.UniformApproximation

/-!
# Actual fixed-environment approximation and channel hockey-stick testing

The approximation parameter is attained by an actual rectangular auxiliary
matrix in the prescribed environmental spaces. The scalar error is also
identified with the infimum in equation (4.4).
-/
noncomputable section
namespace QuantumChannelStein.HockeyStickApproximation
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open Matrix ChannelEntropy TestingSDP TestingPrimal

variable {a b eN eM : ℕ}

/-- The genuine fixed-environment operator-norm error of an auxiliary matrix. -/
def auxiliaryDistance
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (C : Matrix (Fin eN) (Fin eM) ℂ) : ℝ :=
  ‖VN - ((1 : Operator b) ⊗ₖ C) * VM‖

/-- Choose an actually attained constrained minimizer, with no inverse or
non-singularity assumption on either dilation. -/
def minimizingAuxiliary
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (t : ℝ) :
    Matrix (Fin eN) (Fin eM) ℂ :=
  Classical.choose (exists_minimizing_auxiliary VN VM t)

/-- The actual minimum s_t from equation (4.4). -/
def auxiliaryMinimum
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (t : ℝ) : ℝ :=
  auxiliaryDistance VN VM (minimizingAuxiliary VN VM t)

theorem minimizingAuxiliary_norm
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (t : ℝ) :
    ‖minimizingAuxiliary VN VM t‖ ≤ Real.sqrt t :=
  (Classical.choose_spec (exists_minimizing_auxiliary VN VM t)).1

theorem auxiliaryMinimum_le
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (t : ℝ)
    (C : Matrix (Fin eN) (Fin eM) ℂ) (hC : ‖C‖ ≤ Real.sqrt t) :
    auxiliaryMinimum VN VM t ≤ auxiliaryDistance VN VM C :=
  (Classical.choose_spec (exists_minimizing_auxiliary VN VM t)).2 C hC

theorem auxiliaryMinimum_nonneg
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (t : ℝ) :
    0 ≤ auxiliaryMinimum VN VM t := norm_nonneg _

/-- The chosen minimum equals the actual infimum over all admissible maps. -/
theorem auxiliaryMinimum_eq_sInf
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (t : ℝ) :
    auxiliaryMinimum VN VM t = sInf (Set.range (fun C :
      {C : Matrix (Fin eN) (Fin eM) ℂ // ‖C‖ ≤ Real.sqrt t} => auxiliaryDistance VN VM C.val)) := by
  let S := Set.range (fun C :
    {C : Matrix (Fin eN) (Fin eM) ℂ // ‖C‖ ≤ Real.sqrt t} => auxiliaryDistance VN VM C.val)
  have hmem : auxiliaryMinimum VN VM t ∈ S :=
    ⟨⟨minimizingAuxiliary VN VM t, minimizingAuxiliary_norm VN VM t⟩, rfl⟩
  have hb : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro y ⟨C, rfl⟩
    exact norm_nonneg _
  apply le_antisymm
  · apply le_csInf ⟨_, hmem⟩
    rintro y ⟨C, rfl⟩
    exact auxiliaryMinimum_le VN VM t C.val C.property
  · exact csInf_le hb hmem

/-- A feasible auxiliary attains s_t in the prescribed environments. -/
theorem auxiliaryMinimum_attained
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (t : ℝ) :
    ∃ C : Matrix (Fin eN) (Fin eM) ℂ, ‖C‖ ≤ Real.sqrt t ∧
      auxiliaryDistance VN VM C = auxiliaryMinimum VN VM t :=
  ⟨minimizingAuxiliary VN VM t, minimizingAuxiliary_norm VN VM t, rfl⟩

/-- The zero auxiliary gives the universal norm upper bound. -/
theorem auxiliaryMinimum_le_norm
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (t : ℝ) :
    auxiliaryMinimum VN VM t ≤ ‖VN‖ := by
  simpa [auxiliaryDistance] using auxiliaryMinimum_le VN VM t 0 (by simp)

/-- Isometric null dilations put the minimizing error in [0,1]. -/
theorem auxiliaryMinimum_le_one
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (hVN : VNᴴ * VN = 1) (t : ℝ) :
    auxiliaryMinimum VN VM t ≤ 1 :=
  (auxiliaryMinimum_le_norm VN VM t).trans (UniformApproximation.norm_isometry_le_one VN hVN)

/-- Representing a channel identifies the prescribed dilation's Choi Gram matrix. -/
theorem columns_gram_of_dilationMap (Φ : KrausChannel a b)
    (V : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (hV : dilationMap V = Φ.toLinearMap) :
    dilationColumns V * (dilationColumns V)ᴴ = Φ.choi := by
  rw [← choi_dilationMap, hV]
  rfl

/-- Every feasible dual matrix already bounds the square of the actual
minimum error, independently of strong duality. -/
theorem auxiliaryMinimum_sq_le_dual (Φ Ψ : KrausChannel a b)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (t : ℝ) (ht : 0 ≤ t) (D : DualFeasible (channelDifference Φ Ψ t)) :
    auxiliaryMinimum VN VM t ^ 2 ≤ D.value := by
  have hN := columns_gram_of_dilationMap Φ VN hVN
  have hM := columns_gram_of_dilationMap Ψ VM hVM
  obtain ⟨C, hC, herror⟩ := approximation_of_dual_feasible VN VM t ht D.Y D.positive (by
    simpa only [hN, hM, channelDifference] using D.dominates)
  exact (pow_le_pow_left₀ (auxiliaryMinimum_nonneg VN VM t)
    (auxiliaryMinimum_le VN VM t C hC) 2).trans herror

/-- A prescribed dilation map equality gives the exact partial-trace
representation used in the mixed/pure amplitude theorem. -/
theorem traceEnvironment_of_dilationMap (Φ : KrausChannel a b)
    (V : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (hV : dilationMap V = Φ.toLinearMap) (X : Operator a) :
    ReferenceAcceptance.traceEnvironment (V * X * Vᴴ) = Φ.apply X := by
  change KrausChannel.traceEnvironment (V * X * Vᴴ) = _
  rw [← dilationMap_apply, hV]
  rfl

/-- The sharp scalar upper bound applies to every actual pure input/effect,
using the error of a concrete prescribed-environment auxiliary map. -/
theorem pureScore_le_of_auxiliary (Φ Ψ : KrausChannel a b)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (t : ℝ) (ht : 0 ≤ t) (C : Matrix (Fin eN) (Fin eM) ℂ)
    (hC : ‖C‖ ≤ Real.sqrt t) (herror : auxiliaryDistance VN VM C ≤ 1)
    (ψ : UnitPureInput a a) (T : Effect (a * b)) :
    pureScore Φ Ψ t ψ T ≤ 2 * auxiliaryDistance VN VM C - auxiliaryDistance VN VM C ^ 2 := by
  have hamp := Purification.lemma_3_4 Φ Ψ VN VM
    (traceEnvironment_of_dilationMap Φ VN hVN) (traceEnvironment_of_dilationMap Ψ VM hVM)
    C (pureMatrix ψ.val) (pureMatrix_positive ψ.val)
    (trace_pureMatrix_of_norm_one ψ.val ψ.property) (rawEffect T)
    (rawEffect_positive T) (rawEffect_complement_positive T)
  rw [← pureOutput_probability_raw, ← pureOutput_probability_raw] at hamp
  apply ScalarBounds.probability_hockeyStick_bound
    (T.probability_nonneg _) (T.probability_le_one _) (T.probability_nonneg _) ht
    (norm_nonneg _) herror
  exact hamp.trans (add_le_add
    (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)) le_rfl)

/-- The upper inequality in Proposition 4.2 for arbitrary prescribed
isometric dilations, using an attained auxiliary minimum. -/
theorem channelHockeyStick_le_minimum_error (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (t : ℝ) (ht : 0 ≤ t) :
    channelHockeyStick Φ Ψ t ≤ 2 * auxiliaryMinimum VN VM t - auxiliaryMinimum VN VM t ^ 2 := by
  obtain ⟨ψ, T, hscore⟩ := exists_pure_maximizer Φ Ψ ha t
  rw [← hscore]
  exact pureScore_le_of_auxiliary Φ Ψ VN VM hVN hVM t ht
    (minimizingAuxiliary VN VM t) (minimizingAuxiliary_norm VN VM t)
    (auxiliaryMinimum_le_one VN VM hVNiso t) ψ T

end QuantumChannelStein.HockeyStickApproximation

noncomputable section
namespace QuantumChannelStein.HockeyStickApproximation
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix ChannelEntropy TestingSDP TestingPrimal
variable {a b eN eM : ℕ}

/-- The Choi difference in channel testing is genuinely Hermitian. -/
theorem channelDifference_isHermitian (Φ Ψ : KrausChannel a b) (t : ℝ) (ht : 0 ≤ t) :
    (channelDifference Φ Ψ t).IsHermitian :=
  Φ.choi_positive.isHermitian.sub (Ψ.choi_positive.smul ht).isHermitian

/-- Attained strong duality converts the constructive per-dual estimate
into the lower inequality of Proposition 4.2. -/
theorem auxiliaryMinimum_sq_le_channelHockeyStick (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (t : ℝ) (ht : 0 ≤ t) :
    auxiliaryMinimum VN VM t ^ 2 ≤ channelHockeyStick Φ Ψ t := by
  obtain ⟨P, hvalue, hmax⟩ := exists_primal_maximizer_eq_channelHockeyStick Φ Ψ ha t
  obtain ⟨D, hD⟩ := TestingSDPStrong.exists_dual_attaining_primal_max
    (inputDensity (maximallyEntangledInput ha)) (channelDifference Φ Ψ t)
    (channelDifference_isHermitian Φ Ψ t ht) P hmax
  have h := auxiliaryMinimum_sq_le_dual Φ Ψ VN VM hVN hVM t ht D
  rw [hD, ← hvalue] at h
  exact h

/-- Proposition 4.2 of arXiv:2609.27196v1 for actual prescribed Stinespring
isometries and the actual attained environmental minimum s_t. -/
theorem proposition_4_2 (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1) (_hVMiso : VMᴴ * VM = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (t : ℝ) (ht : 0 ≤ t) :
    auxiliaryMinimum VN VM t ^ 2 ≤ channelHockeyStick Φ Ψ t ∧
      channelHockeyStick Φ Ψ t ≤ 2 * auxiliaryMinimum VN VM t - auxiliaryMinimum VN VM t ^ 2 :=
  ⟨auxiliaryMinimum_sq_le_channelHockeyStick Φ Ψ ha VN VM hVN hVM t ht,
    channelHockeyStick_le_minimum_error Φ Ψ ha VN VM hVNiso hVN hVM t ht⟩

end QuantumChannelStein.HockeyStickApproximation
