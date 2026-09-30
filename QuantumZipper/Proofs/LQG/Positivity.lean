import QuantumZipper.Proofs.LQG.BoundaryExistenceAS
import QuantumZipper.Proofs.LQG.GoodSample
import QuantumZipper.Proofs.LQG.RegularSample
import QuantumZipper.Proofs.LQG.ZeroOneCM

/-!
# M4-P2: positivity of the boundary LQG measure

Blueprint `M4_BLUEPRINT.md`, node M4-P2 (boundary part).

For the free field `X` (`IsFreeGFFModConstH X P`) and `γ ∈ (0,2)`, almost surely
`qBoundaryMeasure γ (X ω)` charges every nondegenerate interval
(`ae_forall_pos_qBoundaryMeasure_Ioo`).

Proof, for a fixed interval `(a,b)` and `R = |a| + |b| + 1`, `Z = zField X R`:
* The Gaussian process is `Y_i = Z(fc(q_i, 2^{-k_i}))`, indexed by the recorded dyadic circles
  with centre in `Hbar` (`PIdx`). Its covariance `K(·,i)` is the pairing with a continuous
  function `ψ_i` (`covK_pY`), so the path shift `y ↦ y + q K(·,i)` is `Z ↦ Z + ofFun (q ψ_i)`.
* The event is `A = {y | limsup_k ∫⁻ g dν_k(recP y) = 0}` for a tent `g` supported on `(a,b)`;
  it is measurable (`recP` is a measurable reconstruction). On regular samples with a vague
  limit, `y = Y(ω) ∈ A ↔ ν_Z(a,b) = 0`.
* Invariance: on regular samples, adding a continuous `φ` multiplies the approximating densities
  by `exp(γ/2 ∫ φ dfc)`, bounded above and below on `supp g` uniformly in `k`
  (`limsup_eq_zero_iff_add_ofFun`). So `A` is shift invariant up to null sets.
* P1 (`measure_preimage_eq_zero_or_one_of_ratShift`) gives `P(ν_Z(a,b) = 0) ∈ {0,1}`; it is not
  `1` since `E ∫ g dν_Z = lim E ∫ g dν_k ≥ ∫ g > 0`.
* `ν_X = e^{γX(fc(0,R))/2} ν_Z` a.s., and a countable intersection over rational intervals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Positivity

open Factorization GaussTK BdryExist GoodSample

/-! ### Coordinates of the recorded circles with centre in `Hbar` -/

/-- The recorded circle `fc(q_i, 2^{-k_i})`. -/
def pcirc (i : ℕ) : Measure ℂ := foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)

instance (i : ℕ) : IsProbabilityMeasure (pcirc i) := by unfold pcirc; infer_instance

/-- Indices of recorded circles with centre in `Hbar`. -/
abbrev PIdx := {i : ℕ // (dyadicIndex i).1 ∈ Hbar}

open Classical in
/-- Measurable reconstruction of a field sample from the coordinates indexed by `PIdx`. -/
def recP (y : PIdx → ℝ) : FieldSample := fun μ =>
  if h : ∃ i : PIdx, pcirc i.1 = μ then y h.choose else 0

theorem measurable_recP : Measurable recP := by
  refine measurable_pi_iff.2 fun μ => ?_
  unfold recP
  by_cases h : ∃ i : PIdx, pcirc i.1 = μ
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

theorem recP_apply {x : FieldSample} {y : PIdx → ℝ} (hy : ∀ i, y i = x (pcirc i.1))
    (i : PIdx) : recP y (pcirc i.1) = x (pcirc i.1) := by
  have h : ∃ j : PIdx, pcirc j.1 = pcirc i.1 := ⟨i, rfl⟩
  unfold recP
  rw [dif_pos h, hy, h.choose_spec]

theorem dyadicRoundC_mem_Hbar (n : ℕ) {z : ℂ} (hz : z ∈ Hbar) : dyadicRoundC n z ∈ Hbar := by
  have h0 : 0 ≤ z.im := hz
  show 0 ≤ dyadicRound n z.im
  unfold dyadicRound
  have : (0 : ℝ) ≤ 2 ^ n * z.im := mul_nonneg (by positivity) h0
  exact div_nonneg (Int.cast_nonneg (Int.floor_nonneg.2 this)) (by positivity)

theorem avgReg_congr_pcirc {x x' : FieldSample} (h : ∀ i : PIdx, x (pcirc i.1) = x' (pcirc i.1))
    (k : ℕ) {z : ℂ} (hz : z ∈ Hbar) : avgReg x k z = avgReg x' k z := by
  unfold avgReg
  congr 1
  funext n
  obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
  have hm : (dyadicIndex i).1 ∈ Hbar := by rw [hi]; exact dyadicRoundC_mem_Hbar n hz
  have := h ⟨i, hm⟩
  simp only [pcirc, hi] at this
  exact this

theorem bdryApprox_congr_pcirc {x x' : FieldSample}
    (h : ∀ i : PIdx, x (pcirc i.1) = x' (pcirc i.1)) (γ : ℝ) :
    bdryApprox γ x = bdryApprox γ x' := by
  funext k
  unfold bdryApprox
  congr 1
  funext t
  rw [avgReg_congr_pcirc h k (ofReal_mem_Hbar t)]

/-! ### The Gaussian process of the normalized field -/

section Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The index `(q_i, 2^{-k_i}, 0, R)` of `Z(fc(q_i, 2^{-k_i}))`. -/
def pidx (R : ℝ) (i : PIdx) : FcIdx := ((dyadicIndex i.1).1, radius (dyadicIndex i.1).2, 0, R)

theorem pidx_good {R : ℝ} (hR : 0 < R) (i : PIdx) : (pidx R i).Good :=
  good_Z i.2 (radius_pos _) hR

/-- The coordinate process `Y_i = Z(fc(q_i, 2^{-k_i}))`. -/
def pY (X : Ω → FieldSample) (R : ℝ) (i : PIdx) (ω : Ω) : ℝ := fcPairVal X (pidx R i) ω

theorem pY_eq (R : ℝ) (i : PIdx) (ω : Ω) : pY X R i ω = zField X R ω (pcirc i.1) :=
  (addConst_fc_eq_fcPairVal (X := X) R _ _ ω).symm

theorem isGaussianProcess_pY (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR : 0 < R) :
    IsGaussianProcess (pY X R) P := by
  have := (isGaussianProcess_fcPair hX).comp_right
    (fun i : PIdx => (⟨pidx R i, pidx_good hR i⟩ : {p : FcIdx // p.Good}))
  exact this

/-- The covariance potential `ψ_i`: `K(j,i) = ∫ ψ_i d fc_j`. -/
def psiP (R : ℝ) (i : PIdx) (u : ℂ) : ℝ :=
  (KernelId.fcPot (radius (dyadicIndex i.1).2) (dyadicIndex i.1).1 u - KernelId.fcPot R 0 u) +
    (kernelCov neumannH (foldedCircle 0 R) (foldedCircle 0 R) -
      kernelCov neumannH (foldedCircle 0 R) (pcirc i.1))

theorem continuous_psiP {R : ℝ} (hR : 0 < R) (i : PIdx) : Continuous (psiP R i) :=
  ((KernelId.continuous_fcPot (radius_pos _) _).sub (KernelId.continuous_fcPot hR _)).add
    continuous_const

theorem kernelCov_fc_right (μ : Measure ℂ) (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    kernelCov neumannH μ (foldedCircle w ρ) = ∫ x, KernelId.fcPot ρ w x ∂μ := by
  unfold kernelCov
  simp_rw [KernelId.integral_neumannH_foldedCircle_right' w _ hρ]

theorem covK_pY (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR : 0 < R) (j i : PIdx) :
    CameronMartin.covK (pY X R) P j i = ∫ u, psiP R i u ∂pcirc j.1 := by
  have hc : CameronMartin.covK (pY X R) P j i = fcPairCov (pidx R j) (pidx R i) :=
    covariance_fcPairVal hX (pidx_good hR j) (pidx_good hR i)
  have hr := radius_pos (dyadicIndex i.1).2
  have hint1 : Integrable (KernelId.fcPot (radius (dyadicIndex i.1).2) (dyadicIndex i.1).1)
      (pcirc j.1) :=
    RegClosure.integrable_fc (KernelId.continuous_fcPot hr _).continuousOn _ (radius_pos _).le
  have hint2 : Integrable (KernelId.fcPot R 0) (pcirc j.1) :=
    RegClosure.integrable_fc (KernelId.continuous_fcPot hR _).continuousOn _ (radius_pos _).le
  rw [hc]
  unfold psiP
  rw [integral_add (f := fun u => KernelId.fcPot (radius (dyadicIndex i.1).2) (dyadicIndex i.1).1 u -
      KernelId.fcPot R 0 u) (hint1.sub hint2) (integrable_const _), integral_sub hint1 hint2,
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, ← kernelCov_fc_right _ _ hr,
    ← kernelCov_fc_right _ _ hR]
  simp only [fcPairCov, kernelCov2, pidx, pcirc]
  ring

end Gauss

/-! ### Pathwise comparison under a continuous shift -/

theorem avgReg_add_ofFun {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (k : ℕ) (t : ℝ) :
    avgReg (x + ofFun φ) k t = avgReg x k t + ∫ v, φ v ∂foldedCircle (t : ℂ) (radius k) := by
  rw [(gs_add_ofFun hF hφ.continuousOn).avgReg_eq k (ofReal_mem_Hbar t),
    hF.avgReg_eq k (ofReal_mem_Hbar t)]

theorem abs_smooth_le {φ : ℂ → ℝ} {M T : ℝ} (hM : ∀ u ∈ CircleFubini.ballH (T + 1), |φ u| ≤ M)
    (k : ℕ) {t : ℝ} (ht : |t| ≤ T) :
    |∫ v, φ v ∂foldedCircle (t : ℂ) (radius k)| ≤ M := by
  have hsupp := CircleFubini.foldedCircle_support (radius_pos k).le (z := (t : ℂ)) (R := T + 1)
    (by have := radius_le_one k; simp only [Complex.norm_real, Real.norm_eq_abs]; linarith)
  have hae : ∀ᵐ u ∂foldedCircle (t : ℂ) (radius k), ‖φ u‖ ≤ M :=
    (ae_iff.2 hsupp).mono fun u hu => by rw [Real.norm_eq_abs]; exact hM u hu
  have := MeasureTheory.norm_integral_le_of_norm_le_const hae
  simpa [Real.norm_eq_abs] using this

theorem lintegral_bdryApprox_add_ofFun_le {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (γ : ℝ) {φ : ℂ → ℝ} (hφ : Continuous φ) {g : ℝ → ℝ}
    (hg : Measurable g) {T : ℝ} (hgT : ∀ t, g t ≠ 0 → |t| ≤ T) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ (x + ofFun φ) k ≤
      C * ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ x k := by
  obtain ⟨M, hM⟩ :=
    (CircleFubini.isCompact_ballH (T + 1)).exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨ENNReal.ofReal (Real.exp (|γ| / 2 * M)), ENNReal.ofReal_ne_top, fun k => ?_⟩
  have hm : ∀ y : FieldSample, Measurable fun t : ℝ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg y k t)) := fun y =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (((RegClosure.measurable_avgReg_slice y k).comp
        Complex.continuous_ofReal.measurable).const_mul _).exp)
  unfold bdryApprox
  rw [lintegral_withDensity_eq_lintegral_mul _ (hm _) hg.ennreal_ofReal,
    lintegral_withDensity_eq_lintegral_mul _ (hm _) hg.ennreal_ofReal,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun t => ?_
  simp only [Pi.mul_apply]
  by_cases h0 : g t = 0
  · simp [h0]
  have ht := hgT t h0
  set s := ∫ v, φ v ∂foldedCircle (t : ℂ) (radius k) with hs_def
  have hs : |s| ≤ M := abs_smooth_le (fun u hu => by simpa [Real.norm_eq_abs] using hM u hu) k ht
  rw [avgReg_add_ofFun hF hφ k t, ← hs_def]
  have hle : γ / 2 * s ≤ |γ| / 2 * M := by
    calc γ / 2 * s ≤ |γ / 2 * s| := le_abs_self _
      _ = |γ| / 2 * |s| := by rw [abs_mul, abs_div, abs_two]
      _ ≤ |γ| / 2 * M := mul_le_mul_of_nonneg_left hs (by positivity)
  set A := avgReg x k (t : ℂ)
  have hr : 0 ≤ radius k ^ (γ ^ 2 / 4) := Real.rpow_nonneg (radius_pos k).le _
  have hd : ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * (A + s))) ≤
      ENNReal.ofReal (Real.exp (|γ| / 2 * M)) *
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * A)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    calc radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * (A + s))
        = (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * A)) * Real.exp (γ / 2 * s) := by
          rw [mul_add, Real.exp_add]; ring
      _ ≤ (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * A)) * Real.exp (|γ| / 2 * M) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) (by positivity)
      _ = Real.exp (|γ| / 2 * M) * (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * A)) :=
          mul_comm _ _
  calc ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * (A + s))) *
        ENNReal.ofReal (g t)
      ≤ (ENNReal.ofReal (Real.exp (|γ| / 2 * M)) *
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * A))) *
          ENNReal.ofReal (g t) := by gcongr
    _ = _ := mul_assoc _ _ _

theorem limsup_add_ofFun_eq_zero {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (γ : ℝ) {φ : ℂ → ℝ} (hφ : Continuous φ) {g : ℝ → ℝ} (hg : Measurable g) {T : ℝ}
    (hgT : ∀ t, g t ≠ 0 → |t| ≤ T)
    (h0 : limsup (fun k => ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ x k) atTop = 0) :
    limsup (fun k => ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ (x + ofFun φ) k) atTop = 0 := by
  obtain ⟨C, hC, hle⟩ := lintegral_bdryApprox_add_ofFun_le hF γ hφ hg hgT
  refine le_antisymm ?_ zero_le
  calc limsup (fun k => ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ (x + ofFun φ) k) atTop
      ≤ limsup (fun k => C * ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ x k) atTop :=
        limsup_le_limsup (Eventually.of_forall hle)
    _ = C * limsup (fun k => ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ x k) atTop :=
        ENNReal.limsup_const_mul_of_ne_top hC
    _ = 0 := by rw [h0, mul_zero]

/-- Invariance of the null event under a continuous shift, on regular samples. -/
theorem limsup_eq_zero_iff_add_ofFun {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (γ : ℝ) {φ : ℂ → ℝ} (hφ : Continuous φ) {g : ℝ → ℝ}
    (hg : Measurable g) {T : ℝ} (hgT : ∀ t, g t ≠ 0 → |t| ≤ T) :
    limsup (fun k => ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ x k) atTop = 0 ↔
      limsup (fun k => ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ (x + ofFun φ) k) atTop = 0 := by
  refine ⟨limsup_add_ofFun_eq_zero hF γ hφ hg hgT, fun h => ?_⟩
  have hF' := gs_add_ofFun hF hφ.continuousOn
  have e : x + ofFun φ + ofFun (-φ) = x := by
    funext μ; simp only [Pi.add_apply, Pi.neg_apply, ofFun, integral_neg]; ring
  have := limsup_add_ofFun_eq_zero hF' γ hφ.neg hg hgT h
  rwa [e] at this

/-- On a regular sample with a vague limit, the `limsup` of the approximations is the limit. -/
theorem limsup_lintegral_eq_ofReal {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {γ : ℝ} {ν : Measure ℝ} (hν : IsVagueLimitR (bdryApprox γ x) ν) {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ t, 0 ≤ g t) :
    limsup (fun k => ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ x k) atTop =
      ENNReal.ofReal (∫ t, g t ∂ν) := by
  have e : ∀ k, ∫⁻ t, ENNReal.ofReal (g t) ∂bdryApprox γ x k =
      ENNReal.ofReal (∫ t, g t ∂bdryApprox γ x k) := by
    intro k
    have : IsFiniteMeasureOnCompacts (bdryApprox γ x k) := ⟨fun K hK => by
      rw [← bdryR_radius γ hF k]
      exact bdryR_lt_top γ hF (by rw [one_mul]; exact radius_pos k) hK⟩
    rw [ofReal_integral_eq_lintegral_ofReal (hg.integrable_of_hasCompactSupport hgc)
      (ae_of_all _ hg0)]
  simp_rw [e]
  exact ((ENNReal.continuous_ofReal.tendsto _).comp (hν.2 g hg hgc)).limsup_eq

/-! ### The tent function of an interval -/

/-- Tent function, positive exactly on `(a,b)`. -/
def tent (a b : ℝ) (t : ℝ) : ℝ := max 0 (min (t - a) (b - t))

theorem continuous_tent (a b : ℝ) : Continuous (tent a b) := by
  unfold tent; fun_prop

theorem tent_nonneg (a b t : ℝ) : 0 ≤ tent a b t := le_max_left _ _

theorem tent_pos_iff {a b t : ℝ} : 0 < tent a b t ↔ a < t ∧ t < b := by
  unfold tent
  constructor
  · intro h
    rcases lt_max_iff.1 h with h | h
    · exact absurd h (lt_irrefl _)
    · exact ⟨by linarith [min_le_left (t - a) (b - t)], by linarith [min_le_right (t - a) (b - t)]⟩
  · rintro ⟨h1, h2⟩
    exact lt_max_of_lt_right (lt_min (by linarith) (by linarith))

theorem tent_eq_zero_of_notMem {a b t : ℝ} (ht : t ∉ Icc a b) : tent a b t = 0 := by
  refine le_antisymm (not_lt.1 fun h => ht ?_) (tent_nonneg a b t)
  obtain ⟨h1, h2⟩ := tent_pos_iff.1 h
  exact ⟨h1.le, h2.le⟩

theorem hasCompactSupport_tent (a b : ℝ) : HasCompactSupport (tent a b) :=
  HasCompactSupport.intro isCompact_Icc fun _ ht => tent_eq_zero_of_notMem ht

theorem tent_bound {a b t : ℝ} (h : tent a b t ≠ 0) : |t| ≤ |a| + |b| := by
  obtain ⟨h1, h2⟩ := tent_pos_iff.1 (lt_of_le_of_ne (tent_nonneg a b t) (Ne.symm h))
  exact abs_le.2 ⟨by linarith [neg_abs_le a, abs_nonneg b], by linarith [le_abs_self b, abs_nonneg a]⟩

theorem ofReal_integral_tent_eq_zero_iff {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (a b : ℝ) :
    ENNReal.ofReal (∫ t, tent a b t ∂ν) = 0 ↔ ν (Ioo a b) = 0 := by
  have hi : Integrable (tent a b) ν :=
    (continuous_tent a b).integrable_of_hasCompactSupport (hasCompactSupport_tent a b)
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (tent_nonneg a b)),
    lintegral_eq_zero_iff (continuous_tent a b).measurable.ennreal_ofReal,
    Filter.EventuallyEq, ae_iff]
  have : {t | ¬ENNReal.ofReal (tent a b t) = (0 : ℝ → ℝ≥0∞) t} = Ioo a b := by
    ext t
    simp only [mem_setOf_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le, mem_Ioo]
    exact tent_pos_iff
  rw [this]

/-! ### Positivity for one interval -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem one_le_bDens_mean {γ R : ℝ} (hR1 : 1 ≤ R) (k : ℕ) :
    1 ≤ radius k ^ (γ ^ 2 / 4) * Real.exp (bV R k * (γ / 2) ^ 2 / 2) := by
  have hr := radius_pos k
  have hbV : 2 * Real.log R - 2 * Real.log (radius k) ≤ (bV R k : ℝ) := by
    simp only [bV]; exact Real.le_coe_toNNReal _
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
  apply Real.one_le_exp
  nlinarith [mul_le_mul_of_nonneg_right hbV (sq_nonneg γ), mul_nonneg hlogR (sq_nonneg γ)]

/-- **M4-P2 for one interval, normalized field.** -/
theorem ae_pos_qBoundaryMeasure_zField [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {a b : ℝ} (hab : a < b) :
    ∀ᵐ ω ∂P, 0 < qBoundaryMeasure γ (zField X (|a| + |b| + 1) ω) (Ioo a b) := by
  set R := |a| + |b| + 1 with hRdef
  have hR1 : 1 ≤ R := by linarith [abs_nonneg a, abs_nonneg b]
  have hR : 0 < R := by linarith
  have hgT : ∀ t, tent a b t ≠ 0 → |t| ≤ |a| + |b| := fun t h => tent_bound h
  have hSR : ∀ t ∈ Icc a b, |t| + 1 ≤ R := fun t ht => by
    have : |t| ≤ |a| + |b| := abs_le.2 ⟨by linarith [ht.1, neg_abs_le a, abs_nonneg b],
      by linarith [ht.2, le_abs_self b, abs_nonneg a]⟩
    linarith
  -- the event
  set Φ : (PIdx → ℝ) → ℝ≥0∞ := fun y =>
    limsup (fun k => ∫⁻ t, ENNReal.ofReal (tent a b t) ∂bdryApprox γ (recP y) k) atTop
    with hΦdef
  have hΦ : Measurable Φ := Measurable.limsup fun k =>
    (Measure.measurable_lintegral
      (ENNReal.measurable_ofReal.comp (continuous_tent a b).measurable)).comp
      ((measurable_bdryApprox γ k).comp measurable_recP)
  set A : Set (PIdx → ℝ) := Φ ⁻¹' {0} with hAdef
  have hA : MeasurableSet A := hΦ (measurableSet_singleton 0)
  set Yv : Ω → PIdx → ℝ := fun ω j => pY X R j ω with hYvdef
  have hYv : Measurable Yv := measurable_pi_iff.2 fun j => measurable_fcPairVal hX _
  have hrec : ∀ ω, bdryApprox γ (recP (Yv ω)) = bdryApprox γ (zField X R ω) := fun ω =>
    bdryApprox_congr_pcirc (recP_apply (fun i => pY_eq R i ω)) γ
  have hgood : ∀ᵐ ω ∂P, IsRegularSample (zField X R ω) ∧
      IsVagueLimitR (bdryApprox γ (zField X R ω)) (qBoundaryMeasure γ (zField X R ω)) := by
    filter_upwards [RegSample.ae_isRegularSample hX,
      ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R] with ω h1 h2
    exact ⟨h1.addConst' _, h2⟩
  have hiff : ∀ᵐ ω ∂P, (Yv ω ∈ A ↔ qBoundaryMeasure γ (zField X R ω) (Ioo a b) = 0) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨⟨F, hF⟩, hν⟩ := hω
    have := hν.1
    show Φ (Yv ω) = 0 ↔ _
    rw [hΦdef]
    simp only [hrec ω]
    rw [limsup_lintegral_eq_ofReal hF hν (continuous_tent a b) (hasCompactSupport_tent a b)
      (tent_nonneg a b), ofReal_integral_tent_eq_zero_iff]
  -- invariance under the rational covariance shifts
  have hinv : ∀ (i : PIdx) (q : ℚ), (fun y : PIdx → ℝ ↦ y + (q : ℝ) • fun j ↦
      CameronMartin.covK (pY X R) P j i) ⁻¹' A =ᵐ[P.map fun ω j ↦ pY X R j ω] A := by
    intro i q
    set s := fun y : PIdx → ℝ ↦ y + (q : ℝ) • fun j ↦ CameronMartin.covK (pY X R) P j i
      with hsdef
    have hs : Measurable s := ZeroOneCM.zo_measurable_add _
    have hpt : ∀ ω, IsRegularSample (zField X R ω) → (Yv ω ∈ s ⁻¹' A ↔ Yv ω ∈ A) := by
      rintro ω ⟨F, hF⟩
      have hφ : Continuous fun u => (q : ℝ) * psiP R i u :=
        continuous_const.mul (continuous_psiP hR i)
      have hsh : bdryApprox γ (recP (s (Yv ω))) =
          bdryApprox γ (zField X R ω + ofFun fun u => (q : ℝ) * psiP R i u) := by
        refine bdryApprox_congr_pcirc (recP_apply fun j => ?_) γ
        simp only [hsdef, hYvdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofFun]
        rw [covK_pY hX hR j i, pY_eq, integral_const_mul]
      show Φ (s (Yv ω)) = 0 ↔ Φ (Yv ω) = 0
      rw [hΦdef]
      simp only [hsh, hrec ω]
      exact (limsup_eq_zero_iff_add_ofFun hF γ hφ (continuous_tent a b).measurable hgT).symm
    have hnull : P {ω | ¬ IsRegularSample (zField X R ω)} = 0 :=
      ae_iff.1 (hgood.mono fun ω h => h.1)
    rw [ae_eq_set]
    constructor
    · rw [Measure.map_apply hYv ((hs hA).diff hA)]
      refine measure_mono_null (fun ω hω => ?_) hnull
      intro hreg
      exact hω.2 ((hpt ω hreg).1 hω.1)
    · rw [Measure.map_apply hYv (hA.diff (hs hA))]
      refine measure_mono_null (fun ω hω => ?_) hnull
      intro hreg
      exact hω.2 ((hpt ω hreg).2 hω.1)
  have h01 := ZeroOneCM.measure_preimage_eq_zero_or_one_of_ratShift
    (isGaussianProcess_pY hX hR) (fun j => measurable_fcPairVal hX _)
    (fun j => integral_fcPairVal hX (pidx_good hR j)) hA hinv
  rcases h01 with h0 | h1
  · have hn : ∀ᵐ ω ∂P, ω ∉ Yv ⁻¹' A := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [hn, hiff] with ω h hi
    exact pos_iff_ne_zero.2 fun h' => h (hi.2 h')
  · exfalso
    have hae : ∀ᵐ ω ∂P, ω ∈ Yv ⁻¹' A := mem_ae_iff.2 ((prob_compl_eq_zero_iff (hYv hA)).2 h1)
    have hz : ∀ᵐ ω ∂P, ∫ t, tent a b t ∂qBoundaryMeasure γ (zField X R ω) = 0 := by
      filter_upwards [hae, hiff] with ω h hi
      have hν0 := hi.1 h
      refine integral_eq_zero_of_ae ?_
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun t ht => ?_) hν0
      exact tent_pos_iff.1 (lt_of_le_of_ne (tent_nonneg a b t) (Ne.symm ht))
    have hE0 : ∫ ω, ∫ t, tent a b t ∂qBoundaryMeasure γ (zField X R ω) ∂P = 0 :=
      integral_eq_zero_of_ae hz
    have hSf : volume (Icc a b) < ∞ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    obtain ⟨-, hlim⟩ := tendsto_integral_bdryApprox hX hγ hγ2 measurableSet_Icc hSf hSR
      (continuous_tent a b) (hasCompactSupport_tent a b) (fun t ht => tent_eq_zero_of_notMem ht)
    obtain ⟨M, hM⟩ := (continuous_tent a b).bounded_above_of_compact_support
      (hasCompactSupport_tent a b)
    have hM' : ∀ t, |tent a b t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
    have hlow : ∀ k : ℕ, ∫ t in Icc a b, tent a b t ≤
        ∫ ω, ∫ t, tent a b t ∂bdryApprox γ (zField X R ω) k ∂P := by
      intro k
      simp_rw [integral_bdryApprox_zField (X := X) γ R k measurableSet_Icc
        (fun t ht => tent_eq_zero_of_notMem ht)]
      have hint := integrable_fDens hX measurableSet_Icc hSf hSR γ
        (continuous_tent a b).measurable hM' k
      rw [integral_integral_swap (f := fun ω t => tent a b t * bDens γ X R k t ω) hint]
      refine setIntegral_mono_on (continuous_tent a b).integrableOn_Icc hint.integral_prod_right
        measurableSet_Icc fun t ht => ?_
      have hmean : ∫ ω, bDens γ X R k t ω ∂P =
          radius k ^ (γ ^ 2 / 4) * Real.exp (bV R k * (γ / 2) ^ 2 / 2) := by
        simp only [bDens]
        rw [integral_const_mul, integral_exp_bU hX hSR k ht]
      rw [integral_const_mul, hmean]
      calc tent a b t = tent a b t * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_bDens_mean hR1 k) (tent_nonneg a b t)
    have hge := ge_of_tendsto hlim (Eventually.of_forall hlow)
    rw [hE0] at hge
    have hsupp : Function.support (tent a b) = Ioo a b := by
      ext t
      simp only [Function.mem_support, mem_Ioo]
      exact ⟨fun h => tent_pos_iff.1 (lt_of_le_of_ne (tent_nonneg a b t) (Ne.symm h)),
        fun h => (tent_pos_iff.2 h).ne'⟩
    have hpos : 0 < ∫ t in Icc a b, tent a b t := by
      rw [integral_pos_iff_support_of_nonneg (fun t => tent_nonneg a b t)
        (continuous_tent a b).integrableOn_Icc, hsupp,
        Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.2 Ioo_subset_Icc_self,
        Real.volume_Ioo]
      exact ENNReal.ofReal_pos.2 (by linarith)
    linarith

/-- A.s. `ν_X = e^{γ X(fc(0,R))/2} ν_Z`. -/
theorem ae_qBoundaryMeasure_eq_smul_zField [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (X ω) =
      ENNReal.ofReal (Real.exp (γ / 2 * X ω (foldedCircle 0 R))) •
        qBoundaryMeasure γ (zField X R ω) := by
  filter_upwards [ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R,
    ae_bdryApprox_eq_smul hX γ R] with ω hν hs
  have hν' := BdryVague.IsVagueLimitR.const_smul hν
    (c := ENNReal.ofReal (Real.exp (γ / 2 * X ω (foldedCircle 0 R)))) ENNReal.ofReal_ne_top
  have e : bdryApprox γ (X ω) = fun k => ENNReal.ofReal (Real.exp (γ / 2 *
      X ω (foldedCircle 0 R))) • bdryApprox γ (zField X R ω) k := funext hs
  rw [← e] at hν'
  exact qBoundaryMeasure_eq hν'

/-- **M4-P2 (boundary).** For the free field and `γ ∈ (0,2)`, almost surely the boundary LQG
measure charges every nondegenerate interval. -/
theorem ae_forall_pos_qBoundaryMeasure_Ioo [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b → 0 < qBoundaryMeasure γ (X ω) (Ioo a b) := by
  have hq : ∀ᵐ ω ∂P, ∀ a b : ℚ, (a : ℝ) < b → 0 < qBoundaryMeasure γ (X ω) (Ioo a b) := by
    rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro b
    by_cases hab : (a : ℝ) < b
    · filter_upwards [ae_pos_qBoundaryMeasure_zField hX hγ hγ2 hab,
        ae_qBoundaryMeasure_eq_smul_zField hX hγ hγ2 (|(a : ℝ)| + |(b : ℝ)| + 1)] with ω h1 h2 _
      rw [h2, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' h1.ne'
    · exact Eventually.of_forall fun ω h => absurd h hab
  filter_upwards [hq] with ω h a b hab
  obtain ⟨a', ha1, ha2⟩ := exists_rat_btwn hab
  obtain ⟨b', hb1, hb2⟩ := exists_rat_btwn ha2
  exact (h a' b' hb1).trans_le (measure_mono (Ioo_subset_Ioo ha1.le hb2.le))

/-- **M4-P2 (boundary), any interval with nonempty interior.** -/
theorem ae_forall_pos_qBoundaryMeasure [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ I : Set ℝ, (interior I).Nonempty → 0 < qBoundaryMeasure γ (X ω) I := by
  filter_upwards [ae_forall_pos_qBoundaryMeasure_Ioo hX hγ hγ2] with ω h I hI
  obtain ⟨t, ht⟩ := hI
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior t ht
  have hsub : Ioo (t - ε) (t + ε) ⊆ I := by
    rw [← Real.ball_eq_Ioo]; exact hball.trans interior_subset
  exact (h _ _ (by linarith)).trans_le (measure_mono hsub)

end Main

end Positivity
end QuantumZipper
