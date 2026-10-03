import GeneralizedChannelStein.FreeApproximation
import GeneralizedChannelStein.DimensionDomination
import GeneralizedChannelStein.RepeatedBlocks
import GeneralizedChannelStein.DilationTensor
import GeneralizedChannelStein.AuxiliaryWitness
import QuantumChannelStein.DominatedSubchannelFamilies
import QuantumChannelStein.FixedBlockConstruction
import QuantumChannelStein.FixedBlockRates

/-! # Fixed-block amplification with varying free dominators -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.FreeAmplification
open QuantumChannelStein Matrix ChannelEntropy ChannelDilationPower
  ChannelPowerReindex EnvironmentTensor TraceDefectCompletion UniformAuxiliary
  DiamondNorm DominatedSubchannelFamilies RepeatedBlocks DilationTensor ChannelTransport
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
variable {a b : ℕ}

/-- Scalar enlargement of an actual channel domination bound. -/
theorem cpLe_scalar_mono (P : MatrixMap a b) (M : KrausChannel a b)
    {x y : ℝ} (hxy : x ≤ y) (h : MatrixMap.CPLe P ((x : ℂ) • M.toLinearMap)) :
    MatrixMap.CPLe P ((y : ℂ) • M.toLinearMap) := by
  apply MatrixMap.cpLe_trans h
  rw [MatrixMap.cpLe_iff_choi_difference, MatrixMap.choi_smul, MatrixMap.choi_smul]
  have hp := M.choi_positive.smul (sub_nonneg.mpr hxy)
  simpa [sub_smul, Complex.real_smul] using hp

/-- The convex common dominator, with its actual normalized Kraus realization. -/
def halfMix (P Q : KrausChannel a b) : KrausChannel a b :=
  ((isChannel_iff_kraus _).mp (isChannel_combination P Q (1/2) (1/2)
    (by norm_num) (by norm_num) (by norm_num))).choose

theorem halfMix_map (P Q : KrausChannel a b) :
    (halfMix P Q).toLinearMap = (1/2 : ℂ) • P.toLinearMap + (1/2 : ℂ) • Q.toLinearMap := by
  simpa [halfMix] using ((isChannel_iff_kraus _).mp (isChannel_combination P Q (1/2) (1/2)
    (by norm_num) (by norm_num) (by norm_num))).choose_spec

theorem halfMix_mem (F : Set (MatrixMap a b)) (hF : Convex ℝ (MatrixMap.choi '' F))
    (P Q : KrausChannel a b) (hP : P.toLinearMap ∈ F) (hQ : Q.toLinearMap ∈ F) :
    (halfMix P Q).toLinearMap ∈ F := by
  rw [halfMix_map]
  simpa using convex_map_combination_mem F hF P.toLinearMap Q.toLinearMap hP hQ
    (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)

theorem halfMix_dominates_left (P Q : KrausChannel a b) :
    MatrixMap.CPLe P.toLinearMap ((2 : ℂ) • (halfMix P Q).toLinearMap) := by
  rw [halfMix_map]
  have heq : (2 : ℂ) • ((1/2 : ℂ) • P.toLinearMap + (1/2 : ℂ) • Q.toLinearMap) -
      P.toLinearMap = Q.toLinearMap := by module
  change MatrixMap.CompletelyPositive _
  rw [heq]
  exact MatrixMap.completelyPositive_toLinearMap Q

theorem halfMix_dominates_right (P Q : KrausChannel a b) :
    MatrixMap.CPLe Q.toLinearMap ((2 : ℂ) • (halfMix P Q).toLinearMap) := by
  have heq : (halfMix P Q).toLinearMap = (halfMix Q P).toLinearMap := by
    rw [halfMix_map,halfMix_map,add_comm]
  rw [heq]
  exact halfMix_dominates_left Q P

/-- Completing a concrete auxiliary approximation retains its actual free
set and costs only one additional unit of CP domination. -/
theorem complete_auxiliary {e f : ℕ}
    (F : Set (MatrixMap a b)) (hF : Convex ℝ (MatrixMap.choi '' F))
    (N M : KrausChannel a b) (ha : 0 < a) (ω : State b)
    (hM : M.toLinearMap ∈ F) (hR : (ReplacerChannel.channel a ω).toLinearMap ∈ F)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (hV : Vᴴ*V=1) (hVN : dilationMap V=N.toLinearMap) (hWM : dilationMap W=M.toLinearMap)
    (A : Matrix (Fin e) (Fin f) ℂ) (c δ : ℝ) (hc : 1 ≤ c) (hδ : 0 ≤ δ)
    (hA : ‖A‖^2 ≤ c) (herr : ‖V-applyEnvironment W A‖ ≤ δ) :
    ∃ L S : KrausChannel a b, S.toLinearMap ∈ F ∧
      MatrixMap.CPLe L.toLinearMap (((c+1 : ℝ) : ℂ) • S.toLinearMap) ∧
      diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal (8*δ) := by
  obtain ⟨Q,hQ,herror⟩ := normalized_subchannel_diamond V W hV A δ c hδ (by linarith) hA herr
  rw [hVN] at herror
  rw [hWM] at hQ
  obtain ⟨_,hd,_,L,S,hS,hdom,he⟩ := lemma_7 F hF Q N M ha ω hM hR c hc hQ
  refine ⟨L,S,hS,cpLe_scalar_mono _ S (by linarith) hdom,?_⟩
  apply he.trans
  calc
    2 * diamondNorm (Q.toLinearMap-N.toLinearMap) ≤ 2 * ENNReal.ofReal (4*δ) := by gcongr
    _ = ENNReal.ofReal (8*δ) := by rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

/-- Completing a repeated-block auxiliary map on the correct km-use spaces.
The coefficient A is the concrete indexed environment operator supplied by
both tensor truncation constructions. -/
theorem complete_repeated_auxiliary {e f : ℕ}
    (N : KrausChannel a b) (F : AlternativeFamily a b) (ha : 0 < a)
    (k m : ℕ) (M : KrausChannel (a^k) (b^k))
    (hF : Convex ℝ (MatrixMap.choi '' F (k*m)))
    (hM : (repeatBlock k m M).toLinearMap ∈ F (k*m))
    (ω : State (b^(k*m)))
    (hR : (ReplacerChannel.channel (a^(k*m)) ω).toLinearMap ∈ F (k*m))
    (V : Matrix (Fin (b^k) × Fin e) (Fin (a^k)) ℂ)
    (W : Matrix (Fin (b^k) × Fin f) (Fin (a^k)) ℂ)
    (hV : Vᴴ*V=1) (hVN : dilationMap V=(N.tensorPower k).toLinearMap)
    (hWM : dilationMap W=M.toLinearMap)
    (A : Matrix (TensorPower.Index (Fin e) m) (TensorPower.Index (Fin f) m) ℂ)
    (c δ : ℝ) (hc : 1 ≤ c) (hδ : 0 ≤ δ)
    (hA : ‖A‖^2 ≤ c)
    (herr : ‖blockDilation V m - applyEnvironment (blockDilation W m) A‖ ≤ δ) :
    ∃ L S : KrausChannel (a^(k*m)) (b^(k*m)), S.toLinearMap ∈ F (k*m) ∧
      MatrixMap.CPLe L.toLinearMap (((c+1 : ℝ) : ℂ) • S.toLinearMap) ∧
      diamondNorm (L.toLinearMap-(N.tensorPower (k*m)).toLinearMap) ≤ ENNReal.ofReal (8*δ) := by
  let ea := finCongr (Nat.pow_mul a k m).symm
  let eb := finCongr (Nat.pow_mul b k m).symm
  let U := Matrix.reindex (Equiv.prodCongr eb (Equiv.refl (Fin (e^m)))) ea (powerDilation V m)
  let Z := Matrix.reindex (Equiv.prodCongr eb (Equiv.refl (Fin (f^m)))) ea (powerDilation W m)
  have hU : Uᴴ*U=1 := reindex_isometry _ _ _ (powerDilation_isometry V hV m)
  have hUN : dilationMap U = (N.tensorPower (k*m)).toLinearMap := by
    rw [dilationMap_reindex, dilationMap_powerDilation (N.tensorPower k) V hVN m]
    rw [← reindexChannel_map, reindexChannel_finCongr]
    exact repeatBlock_target_map N k m
  have hZM : dilationMap Z = (repeatBlock k m M).toLinearMap := by
    rw [dilationMap_reindex, dilationMap_powerDilation M W hWM m]
    rw [← reindexChannel_map, reindexChannel_finCongr]
    rfl
  have herror : ‖U-applyEnvironment Z (finiteAuxiliary m A)‖ ≤ δ := by
    have he := TensorBlockReindex.applyEnvironment_reindex ea eb
      (Equiv.refl (Fin (e^m))) (Equiv.refl (Fin (f^m))) (powerDilation W m) (finiteAuxiliary m A)
    simp only [Matrix.reindex_refl_refl] at he
    change ‖Matrix.reindex (Equiv.prodCongr eb (Equiv.refl (Fin (e^m)))) ea (powerDilation V m) -
      applyEnvironment (Matrix.reindex (Equiv.prodCongr eb (Equiv.refl (Fin (f^m)))) ea
        (powerDilation W m)) (finiteAuxiliary m A)‖ ≤ δ
    rw [← he]
    change ‖Matrix.reindex (Equiv.prodCongr eb (Equiv.refl (Fin (e^m)))) ea
      (powerDilation V m - applyEnvironment (powerDilation W m) (finiteAuxiliary m A))‖ ≤ δ
    rw [TensorPower.norm_reindex, finiteAuxiliary_error]
    exact herr
  exact complete_auxiliary (F (k*m)) hF (N.tensorPower (k*m)) (repeatBlock k m M)
    (pow_pos ha _) ω hM hR U Z hU hUN hZM (finiteAuxiliary m A) c δ hc hδ
    (by simpa only [norm_finiteAuxiliary] using hA) herror

/-- Completion accepts the transparent concrete witness record. -/
theorem complete_witness (F : Set (MatrixMap a b)) (hF : Convex ℝ (MatrixMap.choi '' F))
    (N M : KrausChannel a b) (ha : 0 < a) (ω : State b)
    (hM : M.toLinearMap ∈ F) (hR : (ReplacerChannel.channel a ω).toLinearMap ∈ F)
    (c δ : ℝ) (hc : 1 ≤ c) (hδ : 0 ≤ δ) (Wit : AuxiliaryWitness N M c δ) :
    ∃ L S : KrausChannel a b, S.toLinearMap ∈ F ∧
      MatrixMap.CPLe L.toLinearMap (((c+1 : ℝ) : ℂ) • S.toLinearMap) ∧
      diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal (8*δ) :=
  complete_auxiliary F hF N M ha ω hM hR Wit.V Wit.W Wit.isometry Wit.target_map
    Wit.dominator_map Wit.A c δ hc hδ Wit.cost Wit.error

/-- The bounded remainder and additive completion unit fit every strict rate gap. -/
theorem eventually_padded_cost (k : ℕ) (hk : 0 < k) (v C S : ℝ)
    (hv : 0 ≤ v) (hC : 0 ≤ C) (hgap : v<S) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ)^((k : ℝ)*(n/k : ℕ)*v+(n%k : ℕ)*C)+1 ≤ (2 : ℝ)^((n : ℝ)*S) := by
  let R := (v+S)/2
  have hvR : v<R := by dsimp [R]; linarith
  have hRS : R<S := by dsimp [R]; linarith
  obtain ⟨n₀,hn₀⟩ := exists_nat_ge (1/(S-R))
  filter_upwards [FixedBlockRates.eventually_padding_exponent_le k hk (L:=C) hvR,
    Filter.eventually_ge_atTop n₀] with n hn hnlarge
  have hbudget : 1 ≤ (n : ℝ)*(S-R) := by
    apply (div_le_iff₀ (sub_pos.mpr hRS)).mp
    exact hn₀.trans (by exact_mod_cast hnlarge)
  have hpos : 1 ≤ (2 : ℝ)^((k : ℝ)*(n/k : ℕ)*v+(n%k : ℕ)*C) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc
    _ ≤ 2 * (2 : ℝ)^((k : ℝ)*(n/k : ℕ)*v+(n%k : ℕ)*C) := by linarith
    _ ≤ 2 * (2 : ℝ)^((n : ℝ)*R) := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hn) (by norm_num)
    _ = (2 : ℝ)^((n : ℝ)*R+1) := by rw [Real.rpow_add (by norm_num),Real.rpow_one,mul_comm]
    _ ≤ (2 : ℝ)^((n : ℝ)*S) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

/-- The constructive fixed-block heart of Proposition 8. All free dominators
may contain arbitrary correlations within the chosen block. -/
theorem exponential_of_fixed_block {e f : ℕ}
    (N : KrausChannel a b) (F : AlternativeFamily a b) (ha : 0 < a)
    (hconv : ∀ n, 0<n → Convex ℝ (MatrixMap.choi '' F n))
    (htensor : ∀ n m, 0<n → 0<m →
      ∀ (P : KrausChannel (a^n) (b^n)) (Q : KrausChannel (a^m) (b^m)),
      P.toLinearMap ∈ F n → Q.toLinearMap ∈ F m → (tensorBlocks n m P Q).toLinearMap ∈ F (n+m))
    (ω : State b) (hR : ∀ n, 0<n → ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ F n)
    (C : ℝ) (hC : 0≤C)
    (hexact : ∀ n, MatrixMap.CPLe (N.tensorPower n).toLinearMap
      (Complex.ofReal ((2:ℝ)^((n:ℝ)*C)) • ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap))
    (k : ℕ) (hk : 0<k) (M : KrausChannel (a^k) (b^k)) (hM : M.toLinearMap ∈ F k)
    (V : Matrix (Fin (b^k) × Fin e) (Fin (a^k)) ℂ)
    (W : Matrix (Fin (b^k) × Fin f) (Fin (a^k)) ℂ)
    (hV : Vᴴ*V=1) (hVN : dilationMap V=(N.tensorPower k).toLinearMap) (hWM : dilationMap W=M.toLinearMap)
    (A B : Matrix (Fin e) (Fin f) ℂ) (r L ε η S : ℝ)
    (hr : 0≤r) (hrL : r≤L) (hε : 0≤ε) (hη : 0<η)
    (hsmall : ε≤1/(1+(4:ℝ)^(1/η)))
    (hA : ‖A‖≤(2:ℝ)^((k:ℝ)*r/2)) (hB : ‖B‖≤(2:ℝ)^((k:ℝ)*L/2))
    (hExact : V=applyEnvironment W B) (hError : ‖V-applyEnvironment W A‖≤ε)
    (hgap : r+η*(L-r)+2*Real.logb 2 3/(k:ℝ)<S) :
    ExponentialFreeApprox N F S := by
  let Rbar := r+η*(L-r)
  let v := Rbar+2*Real.logb 2 3/(k:ℝ)
  have hRbar : 0≤Rbar := add_nonneg hr (mul_nonneg hη.le (sub_nonneg.mpr hrL))
  have hv : 0≤v := by
    dsimp [v]
    exact add_nonneg hRbar (div_nonneg (mul_nonneg (by norm_num)
      (Real.logb_nonneg (by norm_num) (by norm_num))) (Nat.cast_nonneg k))
  refine ⟨16,Real.log 2/(k:ℝ),by norm_num,FixedBlockRates.fixed_block_decay_rate_pos k hk,?_⟩
  filter_upwards [eventually_padded_cost k hk v C S hv hC hgap, Filter.eventually_ge_atTop k]
    with n hcost hn
  let m := n/k
  let l := n%k
  have hm : 0<m := Nat.div_pos hn hk
  have hnpos : 0<n := hk.trans_le hn
  obtain ⟨D,hD,herr⟩ := FixedBlockConstruction.fixed_block_auxiliary V W A B k m r L ε η
    (UniformApproximation.norm_isometry_le_one V hV) hExact hError hε hη hsmall hrL hA hB
  have hDn : ‖D‖≤(2:ℝ)^((k:ℝ)*m*v/2) := by
    have he := FixedBlockRates.retained_cost_eq_adjusted_rate k m 0 hk Rbar 0
    simp only [Nat.cast_zero,zero_mul,zero_div,add_zero] at he
    exact hD.trans_eq he
  have hDsq : ‖D‖^2≤(2:ℝ)^((k:ℝ)*m*v) := by
    have h := pow_le_pow_left₀ (norm_nonneg D) hDn 2
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)] at h
    convert h using 1 <;> congr 1 <;> ring
  let Wit := AuxiliaryWitness.repeatOriginal N M
    (AuxiliaryWitness.ofRepeated (N.tensorPower k) M V W hV hVN hWM m D _ _ hDsq herr)
  let R := (ReplacerChannel.channel a ω).tensorPower l
  let Pad := AuxiliaryWitness.ofExact (N.tensorPower l) R ((2:ℝ)^((l:ℝ)*C)) (by positivity) (hexact l)
  let Full := Wit.padOriginal N (repeatBlock k m M) R Pad (by positivity) (by positivity)
  let FullN := Full.castOriginal N (tensorBlocks (k*m) l (repeatBlock k m M) R) (Nat.div_add_mod n k)
  have hfree : (tensorBlocks (k*m) l (repeatBlock k m M) R).toLinearMap ∈ F (k*m+l) :=
    paddedBlock_mem F htensor ω hR (k*m) (Nat.mul_pos hk hm) _
      (repeatBlock_mem F htensor k hk M hM m hm) l
  have hfreeN := (cast_mem_family F (Nat.div_add_mod n k) _).mpr hfree
  have hrep : (ReplacerChannel.channel (a^n) (PerfectDiscrimination.statePower ω n)).toLinearMap ∈ F n := by
    rw [ReplacerChannel.channel_map, ← ReplacerChannel.tensorPower_map]
    exact hR n hnpos
  have hbudget : 1≤(2:ℝ)^((k:ℝ)*m*v)*(2:ℝ)^((l:ℝ)*C) := by
    have h1 : 1≤(2:ℝ)^((k:ℝ)*m*v) := Real.one_le_rpow (by norm_num) (by positivity)
    have h2 : 1≤(2:ℝ)^((l:ℝ)*C) := Real.one_le_rpow (by norm_num) (by positivity)
    nlinarith
  obtain ⟨Lout,Sout,hS,hdom,he⟩ := complete_witness (F n) (hconv n hnpos) (N.tensorPower n) _
    (pow_pos ha n) (PerfectDiscrimination.statePower ω n) hfreeN hrep _ _ hbudget (by positivity) FullN
  refine ⟨Lout,Sout,hS,cpLe_scalar_mono _ Sout ?_ hdom,?_⟩
  · rw [← Real.rpow_add (by norm_num)]
    exact hcost
  · apply he.trans
    apply ENNReal.ofReal_le_ofReal
    have h := FixedBlockRates.half_pow_div_le_exponential n k hk
    change 8*(1/2:ℝ)^m ≤ _
    dsimp [m]
    nlinarith

theorem cpLe_smul_real {P Q : MatrixMap a b} (h : MatrixMap.CPLe P Q)
    (c : ℝ) (hc : 0≤c) : MatrixMap.CPLe ((c:ℂ) • P) ((c:ℂ) • Q) := by
  rw [MatrixMap.cpLe_iff_choi_difference] at h ⊢
  rw [MatrixMap.choi_smul,MatrixMap.choi_smul]
  simpa only [smul_sub,Complex.real_smul] using h.smul hc

theorem sqrt_rpow_two (x : ℝ) : Real.sqrt ((2:ℝ)^x) = (2:ℝ)^(x/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

/-- Exact domination already supplies exponential approximation at larger rates. -/
theorem exponential_of_exact_replacer (N : KrausChannel a b) (F : AlternativeFamily a b)
    (ω : State b) (hR : ∀ n, 0<n → ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ F n)
    (C S : ℝ) (hCS : C≤S)
    (hdom : ∀ n, MatrixMap.CPLe (N.tensorPower n).toLinearMap
      (Complex.ofReal ((2:ℝ)^((n:ℝ)*C)) • ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap)) :
    ExponentialFreeApprox N F S := by
  refine ⟨1,1,by norm_num,by norm_num,?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  refine ⟨N.tensorPower n,(ReplacerChannel.channel a ω).tensorPower n,hR n (by omega),?_,?_⟩
  · exact cpLe_scalar_mono _ _ (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hCS (Nat.cast_nonneg n))) (hdom n)
  · rw [sub_self]
    apply iSup_le
    intro r
    apply iSup_le
    intro X
    have hz : MatrixMap.amplify (0 : MatrixMap (a^n) (b^n)) r X.val = 0 := rfl
    rw [hz,TraceNorm.traceNorm_zero,ENNReal.ofReal_zero]
    exact zero_le _

/-- Proposition 8 core, stated with literal arbitrarily late normalized
approximations. No finite-dimensional rate or approximation oracle is assumed. -/
theorem exponential_of_vanishing (N : KrausChannel a b) (F : AlternativeFamily a b) (ha : 0<a)
    (hconv : ∀ n, 0<n → Convex ℝ (MatrixMap.choi '' F n))
    (htensor : ∀ n m, 0<n → 0<m →
      ∀ (P : KrausChannel (a^n) (b^n)) (Q : KrausChannel (a^m) (b^m)),
      P.toLinearMap ∈ F n → Q.toLinearMap ∈ F m → (tensorBlocks n m P Q).toLinearMap ∈ F (n+m))
    (ω : State b) (hR : ∀ n, 0<n → ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ F n)
    (C : ℝ) (hC : 0≤C)
    (hexact : ∀ n, MatrixMap.CPLe (N.tensorPower n).toLinearMap
      (Complex.ofReal ((2:ℝ)^((n:ℝ)*C)) • ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap))
    (r₀ S : ℝ) (hr₀ : 0≤r₀) (hS : r₀<S) (hvan : VanishingFreeApprox N F r₀) :
    ExponentialFreeApprox N F S := by
  by_cases hCS : C≤S
  · exact exponential_of_exact_replacer N F ω hR C S hCS hexact
  have hSC : S<C := lt_of_not_ge hCS
  let r := (r₀+S)/2
  let r₁ := (r₀+r)/2
  let L := C+1
  have hr₀r : r₀<r := by dsimp [r]; linarith
  have hrS : r<S := by dsimp [r]; linarith
  have hr₀r₁ : r₀<r₁ := by dsimp [r₁]; linarith
  have hr₁r : r₁<r := by dsimp [r₁]; linarith
  have hSL : S<L := by dsimp [L]; linarith
  obtain ⟨η,hη,hη1,hmix⟩ := FixedBlockRates.exists_mixing_fraction hrS hSL
  let ε := 1/(1+(4:ℝ)^(1/η))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hgapEvent : ∀ᶠ k : ℕ in Filter.atTop,
      r+η*(L-r)+2*Real.logb 2 3/(k:ℝ)<S := by
    have hcst : Filter.Tendsto (fun _ : ℕ => r+η*(L-r)) Filter.atTop (𝓝 (r+η*(L-r))) :=
      tendsto_const_nhds
    have ht := hcst.add (tendsto_const_div_atTop_nhds_zero_nat (2*Real.logb 2 3))
    have ht' : Filter.Tendsto (fun k : ℕ => r+η*(L-r)+2*Real.logb 2 3/(k:ℝ))
        Filter.atTop (𝓝 (r+η*(L-r))) := by simpa using ht
    exact ht'.eventually (gt_mem_nhds hmix)
  obtain ⟨k₀,hk₀⟩ := Filter.eventually_atTop.mp hgapEvent
  obtain ⟨k₁,hk₁⟩ := exists_nat_ge (1/(r-r₁))
  obtain ⟨k,hklarge,hk,Lapp,M,hM,hLM,hclose⟩ := hvan r₁ hr₀r₁ (2*ε^2) (by positivity) (max k₀ k₁)
  have hgap := hk₀ k (le_trans (le_max_left _ _) hklarge)
  have hbudget : 1≤(k:ℝ)*(r-r₁) := by
    apply (div_le_iff₀ (sub_pos.mpr hr₁r)).mp
    exact hk₁.trans (by exact_mod_cast le_trans (le_max_right _ _) hklarge)
  let R := (ReplacerChannel.channel a ω).tensorPower k
  let U := halfMix M R
  have hU : U.toLinearMap ∈ F k := halfMix_mem (F k) (hconv k hk) M R hM (hR k hk)
  have hLU : MatrixMap.CPLe Lapp.toLinearMap
      (Complex.ofReal (2*(2:ℝ)^((k:ℝ)*r₁)) • U.toLinearMap) := by
    have h := MatrixMap.cpLe_trans hLM (cpLe_smul_real (halfMix_dominates_left M R)
      ((2:ℝ)^((k:ℝ)*r₁)) (by positivity))
    simpa only [smul_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,mul_comm] using h
  have hNU : MatrixMap.CPLe (N.tensorPower k).toLinearMap
      (Complex.ofReal (2*(2:ℝ)^((k:ℝ)*C)) • U.toLinearMap) := by
    have h := MatrixMap.cpLe_trans (hexact k) (cpLe_smul_real (halfMix_dominates_right M R)
      ((2:ℝ)^((k:ℝ)*C)) (by positivity))
    simpa only [smul_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,mul_comm] using h
  have hcostA : 2*(2:ℝ)^((k:ℝ)*r₁) ≤ (2:ℝ)^((k:ℝ)*r) := by
    rw [show 2*(2:ℝ)^((k:ℝ)*r₁) = (2:ℝ)^((k:ℝ)*r₁+1) by
      rw [Real.rpow_add (by norm_num),Real.rpow_one,mul_comm]]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hcostB : 2*(2:ℝ)^((k:ℝ)*C) ≤ (2:ℝ)^((k:ℝ)*L) := by
    rw [show 2*(2:ℝ)^((k:ℝ)*C) = (2:ℝ)^((k:ℝ)*C+1) by
      rw [Real.rpow_add (by norm_num),Real.rpow_one,mul_comm]]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hkreal : (1:ℝ)≤k := by exact_mod_cast hk
    dsimp [L]
    nlinarith
  obtain ⟨A,hA,he⟩ := lemma_6_diamond (N.tensorPower k) U Lapp (pow_pos ha k)
    (N.tensorPower k).stinespring U.stinespring (ParallelConverse.dilationMap_stinespring _)
    (ParallelConverse.dilationMap_stinespring _) _ (2*ε^2) (by positivity) (by positivity) hLU hclose
  obtain ⟨B,hB,hBe⟩ := lemma_6_exact (N.tensorPower k).stinespring U.stinespring
    (2*(2:ℝ)^((k:ℝ)*C)) (by positivity)
    (by simpa only [ParallelConverse.dilationMap_stinespring] using hNU)
  apply exponential_of_fixed_block N F ha hconv htensor ω hR C hC hexact k hk U hU
    (N.tensorPower k).stinespring U.stinespring (N.tensorPower k).stinespring_isometry
    (ParallelConverse.dilationMap_stinespring _) (ParallelConverse.dilationMap_stinespring _)
    A B r L ε η S (hr₀.trans hr₀r.le) (hrS.trans hSL).le hε.le hη le_rfl
    ((hA.trans (Real.sqrt_le_sqrt hcostA)).trans_eq (sqrt_rpow_two _))
    ((hB.trans (Real.sqrt_le_sqrt hcostB)).trans_eq (sqrt_rpow_two _))
    (sub_eq_zero.mp hBe) ?_ hgap
  have hn := norm_nonneg ((N.tensorPower k).stinespring-applyEnvironment U.stinespring A)
  change ‖(N.tensorPower k).stinespring-applyEnvironment U.stinespring A‖≤ε
  change ‖(N.tensorPower k).stinespring-applyEnvironment U.stinespring A‖^2≤2*ε^2/2 at he
  nlinarith

/-- Faithfulness supplies the exact initial rate internally; only the three
structural requirements used by Proposition 8 appear here. -/
theorem exponential_of_vanishing_faithful (N : KrausChannel a b) (F : AlternativeFamily a b)
    (ha : 0<a) (hb : 0<b)
    (hconv : ∀ n, 0<n → Convex ℝ (MatrixMap.choi '' F n))
    (htensor : ∀ n m, 0<n → 0<m →
      ∀ (P : KrausChannel (a^n) (b^n)) (Q : KrausChannel (a^m) (b^m)),
      P.toLinearMap ∈ F n → Q.toLinearMap ∈ F m → (tensorBlocks n m P Q).toLinearMap ∈ F (n+m))
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (r₀ S : ℝ) (hr₀ : 0≤r₀) (hS : r₀<S) (hvan : VanishingFreeApprox N F r₀) :
    ExponentialFreeApprox N F S := by
  have hC : 0≤Real.logb 2 (b:ℝ)-Real.logb 2 (DimensionDomination.minEigenvalue ω hb) := by
    have h1 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) (show (1:ℝ)≤b by exact_mod_cast hb)
    have h2 := Real.logb_nonpos (by norm_num : (1:ℝ)<2)
      (DimensionDomination.minEigenvalue_pos ω hb hω).le (DimensionDomination.minEigenvalue_le_one ω hb)
    linarith
  exact exponential_of_vanishing N F ha hconv htensor ω (replacer_power_mem F htensor ω hOne)
    _ hC (DimensionDomination.faithful_replacer_domination N ω hb hω) r₀ S hr₀ hS hvan

/-- The paper's actual unbounded sequence and extended limsup imply the
concrete arbitrarily-late approximation property. The error is the actual
full diamond norm, not a separate error oracle. -/
theorem vanishing_of_subsequence (N : KrausChannel a b) (F : AlternativeFamily a b)
    (k : ℕ→ℕ) (hk : Filter.Tendsto k Filter.atTop Filter.atTop)
    (L M : (j : ℕ) → KrausChannel (a^(k j)) (b^(k j))) (lam : ℕ→ℝ)
    (hlam : ∀ j, 1≤lam j) (hM : ∀ j, (M j).toLinearMap ∈ F (k j))
    (hdom : ∀ j, MatrixMap.CPLe (L j).toLinearMap ((lam j : ℂ) • (M j).toLinearMap))
    (herror : Filter.Tendsto (fun j => diamondNorm ((L j).toLinearMap-(N.tensorPower (k j)).toLinearMap))
      Filter.atTop (𝓝 0)) (r₀ : ℝ)
    (hrate : Filter.limsup (fun j => ((Real.logb 2 (lam j)/(k j:ℝ) : ℝ) : EReal)) Filter.atTop ≤ (r₀:EReal)) :
    VanishingFreeApprox N F r₀ := by
  intro r hr δ hδ k₀
  have hrate' : ∀ᶠ j : ℕ in Filter.atTop, ((Real.logb 2 (lam j)/(k j:ℝ) : ℝ) : EReal)<(r:EReal) :=
    Filter.eventually_lt_of_limsup_lt (hrate.trans_lt (by exact_mod_cast hr))
  have herr : ∀ᶠ j : ℕ in Filter.atTop,
      diamondNorm ((L j).toLinearMap-(N.tensorPower (k j)).toLinearMap)≤ENNReal.ofReal δ :=
    herror.eventually_le_const (ENNReal.ofReal_pos.mpr hδ)
  have hlarge : ∀ᶠ j : ℕ in Filter.atTop, max k₀ 1≤k j :=
    hk.eventually (Filter.eventually_ge_atTop (max k₀ 1))
  obtain ⟨j,hjrate,hjerror,hjlarge⟩ := (hrate'.and (herr.and hlarge)).exists
  have hkj : 0<k j := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hjlarge)
  refine ⟨k j,le_trans (le_max_left _ _) hjlarge,hkj,L j,M j,hM j,?_,hjerror⟩
  apply cpLe_scalar_mono _ _ ?_ (hdom j)
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by linarith [hlam j])).mp
  have hrj : Real.logb 2 (lam j)/(k j:ℝ)<r := by exact_mod_cast hjrate
  have ht := (div_lt_iff₀ (show (0:ℝ)<k j by exact_mod_cast hkj)).mp hrj
  nlinarith

/-- Proposition 8 in its literal sequence/limsup form. There is no compactness,
permutation symmetry, marginal closure, or family-dependent rate hypothesis. -/
theorem proposition_8 (N : KrausChannel a b) (F : AlternativeFamily a b)
    (ha : 0<a) (hb : 0<b)
    (hconv : ∀ n, 0<n → Convex ℝ (MatrixMap.choi '' F n))
    (htensor : ∀ n m, 0<n → 0<m →
      ∀ (P : KrausChannel (a^n) (b^n)) (Q : KrausChannel (a^m) (b^m)),
      P.toLinearMap ∈ F n → Q.toLinearMap ∈ F m → (tensorBlocks n m P Q).toLinearMap ∈ F (n+m))
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (k : ℕ→ℕ) (hk : Filter.Tendsto k Filter.atTop Filter.atTop)
    (L M : (j : ℕ) → KrausChannel (a^(k j)) (b^(k j))) (lam : ℕ→ℝ)
    (hlam : ∀ j, 1≤lam j) (hM : ∀ j, (M j).toLinearMap ∈ F (k j))
    (hdom : ∀ j, MatrixMap.CPLe (L j).toLinearMap ((lam j : ℂ) • (M j).toLinearMap))
    (herror : Filter.Tendsto (fun j => diamondNorm ((L j).toLinearMap-(N.tensorPower (k j)).toLinearMap))
      Filter.atTop (𝓝 0)) (r₀ S : ℝ) (hr₀ : 0≤r₀) (hS : r₀<S)
    (hrate : Filter.limsup (fun j => ((Real.logb 2 (lam j)/(k j:ℝ) : ℝ) : EReal)) Filter.atTop ≤ (r₀:EReal)) :
    ExponentialFreeApprox N F S :=
  exponential_of_vanishing_faithful N F ha hb hconv htensor ω hω hOne r₀ S hr₀ hS
    (vanishing_of_subsequence N F k hk L M lam hlam hM hdom herror r₀ hrate)

/-- Unbounded tail subsequences suffice even when the original block list is not ordered. -/
theorem vanishing_of_unbounded_sequence (N : KrausChannel a b) (F : AlternativeFamily a b)
    (k : ℕ→ℕ) (hk : ∀ B : ℕ, ∃ᶠ j : ℕ in Filter.atTop, B≤k j)
    (L M : (j : ℕ) → KrausChannel (a^(k j)) (b^(k j))) (lam : ℕ→ℝ)
    (hlam : ∀ j, 1≤lam j) (hM : ∀ j, (M j).toLinearMap ∈ F (k j))
    (hdom : ∀ j, MatrixMap.CPLe (L j).toLinearMap ((lam j : ℂ) • (M j).toLinearMap))
    (herror : Filter.Tendsto (fun j => diamondNorm ((L j).toLinearMap-(N.tensorPower (k j)).toLinearMap))
      Filter.atTop (𝓝 0)) (r₀ : ℝ)
    (hrate : Filter.limsup (fun j => ((Real.logb 2 (lam j)/(k j:ℝ) : ℝ) : EReal)) Filter.atTop ≤ (r₀:EReal)) :
    VanishingFreeApprox N F r₀ := by
  intro r hr δ hδ k₀
  have hrate' : ∀ᶠ j : ℕ in Filter.atTop, ((Real.logb 2 (lam j)/(k j:ℝ) : ℝ) : EReal)<(r:EReal) :=
    Filter.eventually_lt_of_limsup_lt (hrate.trans_lt (by exact_mod_cast hr))
  have herr : ∀ᶠ j : ℕ in Filter.atTop,
      diamondNorm ((L j).toLinearMap-(N.tensorPower (k j)).toLinearMap)≤ENNReal.ofReal δ :=
    herror.eventually_le_const (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨j,hjlarge,hjrate,hjerror⟩ :=
    ((hk (max k₀ 1)).and_eventually (hrate'.and herr)).exists
  have hkj : 0<k j := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hjlarge)
  refine ⟨k j,le_trans (le_max_left _ _) hjlarge,hkj,L j,M j,hM j,?_,hjerror⟩
  apply cpLe_scalar_mono _ _ ?_ (hdom j)
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by linarith [hlam j])).mp
  have hrj : Real.logb 2 (lam j)/(k j:ℝ)<r := by exact_mod_cast hjrate
  have ht := (div_lt_iff₀ (show (0:ℝ)<k j by exact_mod_cast hkj)).mp hrj
  nlinarith


/-- Proposition 8 also holds on any unbounded tail sequence of blocklengths. -/
theorem proposition_8_unbounded (N : KrausChannel a b) (F : AlternativeFamily a b)
    (ha : 0<a) (hb : 0<b)
    (hconv : ∀ n, 0<n → Convex ℝ (MatrixMap.choi '' F n))
    (htensor : ∀ n m, 0<n → 0<m →
      ∀ (P : KrausChannel (a^n) (b^n)) (Q : KrausChannel (a^m) (b^m)),
      P.toLinearMap ∈ F n → Q.toLinearMap ∈ F m → (tensorBlocks n m P Q).toLinearMap ∈ F (n+m))
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (k : ℕ→ℕ) (hk : ∀ B : ℕ, ∃ᶠ j : ℕ in Filter.atTop, B≤k j)
    (L M : (j : ℕ) → KrausChannel (a^(k j)) (b^(k j))) (lam : ℕ→ℝ)
    (hlam : ∀ j, 1≤lam j) (hM : ∀ j, (M j).toLinearMap ∈ F (k j))
    (hdom : ∀ j, MatrixMap.CPLe (L j).toLinearMap ((lam j : ℂ) • (M j).toLinearMap))
    (herror : Filter.Tendsto (fun j => diamondNorm ((L j).toLinearMap-(N.tensorPower (k j)).toLinearMap))
      Filter.atTop (𝓝 0)) (r₀ S : ℝ) (hr₀ : 0≤r₀) (hS : r₀<S)
    (hrate : Filter.limsup (fun j => ((Real.logb 2 (lam j)/(k j:ℝ) : ℝ) : EReal)) Filter.atTop ≤ (r₀:EReal)) :
    ExponentialFreeApprox N F S :=
  exponential_of_vanishing_faithful N F ha hb hconv htensor ω hω hOne r₀ S hr₀ hS
    (vanishing_of_unbounded_sequence N F k hk L M lam hlam hM hdom herror r₀ hrate)

end GeneralizedChannelStein.FreeAmplification
