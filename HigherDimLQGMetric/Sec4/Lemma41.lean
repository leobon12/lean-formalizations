import HigherDimLQGMetric.Sec4.LocAnalysis
import HigherDimLQGMetric.ConvField.RadialPair
import HigherDimLQGMetric.ConvField.WholeSpaceRadial
import HigherDimLQGMetric.ConvField.JointMain
import HigherDimLQGMetric.Growth.Main
import HigherDimLQGMetric.DGZ.FunctionalsMeas

/-!
# [1] Lemma 4.1: the localized field is uniformly close to `h*_ε` (packet L9b, MA6 P9)

For a normalized LGF and every `R > 0`, `sup_{|x| ≤ R} |h*_ε(x) - ĥ*_ε(x)| → 0` in probability as `ε ↓ 0`
(`ref1_lemma41`). The proof is MA6 P9's: the polar formulas of both fields (L2b) and the growth bound
`|h_r(z)| ≤ C G(r)` of [1] Lemma 2.13 (L2a) give the deterministic bound `l9b_locField_error`; the random
constant is replaced by a measurable one (a supremum over a countable dense set of `(r, z)`), and the
supremum over the ball by one over a countable dense set (continuity of both fields).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

theorem l9b_measurable_convMollify_apply (κ : Rd d → ℝ) (ε : ℝ) (z : Rd d) :
    Measurable fun g : DistRd d => convMollify κ ε g z := by
  unfold convMollify
  exact (StronglyMeasurable.limUnder (l := atTop) fun n =>
    (measurable_distOn_apply (convTrunc κ ε z n)).stronglyMeasurable).measurable

/-! ## The truncation radius -/

theorem locRad_div (ε : ℝ) (hε : 0 < ε) : locRad ε / (2 * ε) = (Real.log ε⁻¹) ^ 10 / 2 := by
  unfold locRad
  field_simp

theorem tendsto_log_inv_nhdsGT_zero :
    Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

/-- `(1 + L)/√(L^{10}/2) → 0` as `L → ∞` -/
theorem l9b_tendsto_ratio :
    Tendsto (fun L : ℝ => (1 + L) / Real.sqrt (L ^ 10 / 2)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun L : ℝ => 2 / L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hsq : L ^ 2 ≤ Real.sqrt (L ^ 10 / 2) := by
    apply Real.le_sqrt_of_sq_le
    have h6 : (2 : ℝ) ≤ L ^ 6 := by
      calc (2 : ℝ) ≤ 2 ^ 6 := by norm_num
        _ ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL 6
    nlinarith [pow_pos hL0 4]
  have hL2 : 0 < L ^ 2 := by positivity
  rw [div_le_div_iff₀ (lt_of_lt_of_le hL2 hsq) hL0]
  calc (1 + L) * L ≤ 2 * L ^ 2 := by nlinarith
    _ ≤ 2 * Real.sqrt (L ^ 10 / 2) := by gcongr

/-! ## The deterministic error function -/

/-- the explicit localization error of `l9b_locField_error` at `s = locRad ε` -/
def l9bErr (d : ℕ) (κ : Rd d → ℝ) (CK ε : ℝ) : ℝ :=
  sphArea d * (1 + Real.log ε⁻¹) * (6 * CK / Real.sqrt (locRad ε / (2 * ε))) *
    (1 + 2 * sphArea d * l9bKernelMoment κ)

theorem tendsto_l9bErr (κ : Rd d → ℝ) (CK : ℝ) :
    Tendsto (fun ε => l9bErr d κ CK ε) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun ε : ℝ => (1 + Real.log ε⁻¹) / Real.sqrt ((Real.log ε⁻¹) ^ 10 / 2))
      (𝓝[>] 0) (𝓝 0) := l9b_tendsto_ratio.comp tendsto_log_inv_nhdsGT_zero
  have h := hc.const_mul (sphArea d * 6 * CK * (1 + 2 * sphArea d * l9bKernelMoment κ))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  simp only [l9bErr, locRad_div ε hε0]
  ring

/-- eventually (as `ε ↓ 0`) the hypotheses of `l9b_locField_error` on `ε` hold at `s = locRad ε` -/
theorem l9b_eventually_locHyp {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 ∧ 0 < locRad ε ∧ 1 ≤ locRad ε / (2 * ε) ∧
      1 / 2 ≤ locMass κ ε (locRad ε) := by
  obtain ⟨CK, hCK0, hCK⟩ := l9b_kernel_axis_decay hd hκ
  have hL := tendsto_log_inv_nhdsGT_zero
  have hZ : Tendsto (fun ε : ℝ => sphArea d * (6 * CK / Real.sqrt ((Real.log ε⁻¹) ^ 10 / 2)))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => Real.sqrt (L ^ 10 / 2)) atTop atTop := by
      refine Real.tendsto_sqrt_atTop.comp ?_
      exact (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
    have h2 := (tendsto_const_nhds (x := 6 * CK)).div_atTop (h1.comp hL)
    simpa using h2.const_mul (sphArea d)
  have hZev := (hZ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  filter_upwards [self_mem_nhdsWithin, hL.eventually (eventually_ge_atTop 2),
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1), hZev] with ε hε hL2 hε1 hZε
  have hε0 : 0 < ε := hε
  have hLpos : 0 < Real.log ε⁻¹ := by linarith
  have hrad : 0 < locRad ε := by unfold locRad; positivity
  have ha : 1 ≤ locRad ε / (2 * ε) := by
    rw [locRad_div ε hε0]
    have : (2 : ℝ) ^ 10 ≤ (Real.log ε⁻¹) ^ 10 := pow_le_pow_left₀ (by norm_num) hL2 10
    linarith
  refine ⟨hε0, hε1.2.le, hrad, ha, ?_⟩
  have h := l9b_locMass_sub_one_le hd hκ hCK0 hCK hε0 hrad ha
  rw [locRad_div ε hε0] at h
  have := abs_le.1 (h.trans hZε.le)
  linarith [this.1]

/-! ## A measurable growth constant -/

/-- **Measurable random constant in [1] Lemma 2.13** on a ball: a measurable `Ĉ`, a.s. finite, with
`|h_r(z)| ≤ Ĉ G(r)` for all `|z| ≤ R`, `r > 0`, almost surely. -/
theorem l9b_exists_growth_const (hd : 2 ≤ d) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) {R : ℝ} (hR : 0 < R) :
    ∃ Ĉ : Ω → ℝ≥0∞, Measurable Ĉ ∧ (∀ᵐ ω ∂P, Ĉ ω < ⊤) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ closedBall (0 : Rd d) R, ∀ r : ℝ, 0 < r →
        |sphereAvg (h ω) r z| ≤ (Ĉ ω).toReal * l2b_growthWeight r := by
  let S : Set (ℝ × Rd d) := Ioi 0 ×ˢ closedBall (0 : Rd d) R
  obtain ⟨T, hTc, hTS, hST⟩ := TopologicalSpace.exists_countable_dense_subset S
  have hTc' : Countable T := hTc.to_subtype
  let F : DistRd d → ℝ × Rd d → ℝ := fun g p => |sphereAvg g p.1 p.2| / l2b_growthWeight p.1
  let Ĉ : Ω → ℝ≥0∞ := fun ω => ⨆ p : T, ENNReal.ofReal (F (h ω) p)
  have hhm := hh.1.measurable
  have hĈm : Measurable Ĉ := Measurable.iSup fun p => ENNReal.measurable_ofReal.comp
    ((continuous_abs.measurable.comp ((measurable_sphereAvg_left p.1.1 p.1.2).comp
      hhm)).div_const _)
  have hgrowth := l2a_sphereAvgGrowth d hd P h hh R (1 / 2) hR (by norm_num)
  have hcont := hh.1.ae_continuousOn_sphereAvg hd
  -- finiteness
  have hfin : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ Ĉ ω ≤ ENNReal.ofReal C ∧
      ∀ z ∈ closedBall (0 : Rd d) R, ∀ r : ℝ, 0 < r →
        |sphereAvg (h ω) r z| ≤ C * l2b_growthWeight r := by
    filter_upwards [hgrowth] with ω ⟨C, hC⟩
    have hC' : ∀ z ∈ closedBall (0 : Rd d) R, ∀ r : ℝ, 0 < r →
        |sphereAvg (h ω) r z| ≤ max C 0 * l2b_growthWeight r := fun z hz r hr =>
      (hC z hz r hr).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (l9b_growthWeight_nonneg r))
    refine ⟨max C 0, le_max_right _ _, iSup_le fun p => ?_, hC'⟩
    have hp := hTS p.2
    have hG := l9b_one_le_growthWeight p.1.1
    refine ENNReal.ofReal_le_ofReal ((div_le_iff₀ (by linarith)).2 ?_)
    exact hC' p.1.2 hp.2 p.1.1 hp.1
  refine ⟨Ĉ, hĈm, ?_, ?_⟩
  · filter_upwards [hfin] with ω ⟨C, _, hle, _⟩
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  · filter_upwards [hfin, hcont] with ω ⟨C, hC0, hle, _⟩ ⟨_, hcω⟩
    have hĈfin : Ĉ ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    intro z hz r hr
    have hFc : ContinuousOn (F (h ω)) S := by
      have h1 : ContinuousOn (fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2) S :=
        hcω.mono (prod_mono subset_rfl (subset_univ _))
      have h2 : ContinuousOn (fun p : ℝ × Rd d => l2b_growthWeight p.1) S :=
        l2b_continuousOn_growthWeight.comp continuous_fst.continuousOn fun p hp => hp.1
      exact h1.abs.div h2 fun p _ => (lt_of_lt_of_le one_pos (l9b_one_le_growthWeight _)).ne'
    have hTle : F (h ω) '' T ⊆ Iic (Ĉ ω).toReal := by
      rintro _ ⟨p, hp, rfl⟩
      have h1 : ENNReal.ofReal (F (h ω) p) ≤ Ĉ ω :=
        le_iSup (fun q : T => ENNReal.ofReal (F (h ω) q)) ⟨p, hp⟩
      exact (ENNReal.ofReal_le_iff_le_toReal hĈfin).1 h1
    have hmem := DGZ.image_subset_closure_image_of_dense hFc hTS hST
      (mem_image_of_mem _ (show ((r, z) : ℝ × Rd d) ∈ S from ⟨hr, hz⟩))
    have hle' : F (h ω) (r, z) ≤ (Ĉ ω).toReal :=
      (isClosed_Iic.closure_subset_iff.2 hTle) hmem
    have hG := l9b_one_le_growthWeight r
    exact (div_le_iff₀ (by linarith)).1 hle'

/-! ## The pathwise bound at a fixed cutoff -/

theorem l9bErr_nonneg (κ : Rd d → ℝ) {CK : ℝ} (hCK0 : 0 ≤ CK) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) : 0 ≤ l9bErr d κ CK ε := by
  have hL : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε, hε1⟩)
  have := sphArea_nonneg d
  have := l9bKernelMoment_nonneg κ
  unfold l9bErr
  positivity

/-- For a fixed small cutoff, almost surely `|h*_ε - ĥ*_ε| ≤ Ĉ · err(ε)` on the ball. -/
theorem l9b_ae_locField_le (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ CK * (1 + u) ^ (-((d : ℝ) + 1)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) {R : ℝ} {Ĉ : Ω → ℝ≥0∞}
    (hĈ : ∀ᵐ ω ∂P, ∀ z ∈ closedBall (0 : Rd d) R, ∀ r : ℝ, 0 < r →
      |sphereAvg (h ω) r z| ≤ (Ĉ ω).toReal * l2b_growthWeight r)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hrad : 0 < locRad ε) (ha : 1 ≤ locRad ε / (2 * ε))
    (hZ : 1 / 2 ≤ locMass κ ε (locRad ε)) :
    ∀ᵐ ω ∂P, ∀ x ∈ closedBall (0 : Rd d) R,
      |convMollify κ ε (h ω) x - locField κ ε (h ω) x| ≤ (Ĉ ω).toReal * l9bErr d κ CK ε := by
  have hK := convKernel_contDiff (d := d) (by omega) hκ
  obtain ⟨D, hDc, hDB, hBD⟩ := TopologicalSpace.exists_countable_dense_subset
    (closedBall (0 : Rd d) R)
  have hDc' : Countable D := hDc.to_subtype
  have hpair : ∀ᵐ ω ∂P, ∀ x : D, h ω (locTest κ ε (locRad ε) x) =
      sphArea d * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        locTest κ ε (locRad ε) x ((x : Rd d) + r • e₁ d) * sphereAvg (h ω) r x := by
    rw [ae_all_iff]
    intro x
    exact l2b_ae_radial_pairing hd hh.1 (locTest κ ε (locRad ε) x) x
      (locTest_radial (by omega) hK hrad x)
  filter_upwards [l2b_ae_radial_wholeSpace d hd κ hκ P h hh.1, hpair, hĈ,
    hh.1.ae_continuousOn_sphereAvg hd, l2b_ae_convMollify_continuousOn d hd κ hκ P h hh]
    with ω hφ hψ hgrowth ⟨_, hcont⟩ hcc
  have hconvc : Continuous fun z => convMollify κ ε (h ω) z := by
    have hc : Continuous fun z : Rd d => (ε, z) := continuous_const.prodMk continuous_id
    have hf := hcc.comp_continuous hc (fun _ => ⟨hε, mem_univ _⟩)
    simpa only [Function.comp_def] using hf
  have hfc : Continuous fun z => |convMollify κ ε (h ω) z - locField κ ε (h ω) z| :=
    (hconvc.sub (continuous_locField hK hrad _)).abs
  have hD : ∀ x ∈ D, |convMollify κ ε (h ω) x - locField κ ε (h ω) x| ≤
      (Ĉ ω).toReal * l9bErr d κ CK ε := by
    intro x hx
    have hxB := hDB hx
    have hmap : MapsTo (fun r : ℝ => ((r, x) : ℝ × Rd d)) (Ioi 0) (Ioi 0 ×ˢ univ) :=
      fun r hr => mk_mem_prod hr (mem_univ x)
    have hpc : Continuous fun r : ℝ => ((r, x) : ℝ × Rd d) :=
      continuous_id.prodMk continuous_const
    have hcx : ContinuousOn (fun r => sphereAvg (h ω) r x) (Ioi 0) :=
      ContinuousOn.comp (f := fun r : ℝ => ((r, x) : ℝ × Rd d))
        (g := fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2) hcont hpc.continuousOn hmap
    have := l9b_locField_error hd hκ hCK0 hCK hε hε1 hrad ha hZ ENNReal.toReal_nonneg
      (hφ ε hε x) (hψ ⟨x, hx⟩) hcx (hgrowth x hxB)
    unfold locField
    calc |convMollify κ ε (h ω) x - (locMass κ ε (locRad ε))⁻¹ * h ω (locTest κ ε (locRad ε) x)|
        ≤ _ := this
      _ = (Ĉ ω).toReal * l9bErr d κ CK ε := by unfold l9bErr; ring
  intro x hx
  have hcl : IsClosed {z : Rd d | |convMollify κ ε (h ω) z - locField κ ε (h ω) z| ≤
      (Ĉ ω).toReal * l9bErr d κ CK ε} := isClosed_le hfc continuous_const
  exact hcl.closure_subset_iff.2 (fun z hz => hD z hz) (hBD hx)

/-- **[1] Lemma 4.1** (MA6 P9; in probability, which is what is consumed): for a normalized LGF and every
`R, η > 0`, `P[sup_{|x| ≤ R} |h*_ε(x) - ĥ*_ε(x)| > η] → 0` as `ε ↓ 0` (outer measure; no measurability of
the supremum is claimed). -/
theorem ref1_lemma41 (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {R : ℝ} (hR : 0 < R) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun ε => P {ω | ∃ x ∈ closedBall (0 : Rd d) R,
      η < |convMollify κ ε (h ω) x - locField κ ε (h ω) x|}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨CK, hCK0, hCK⟩ := l9b_kernel_axis_decay hd hκ
  obtain ⟨Ĉ, hĈm, hĈfin, hĈ⟩ := l9b_exists_growth_const hd hh hR
  -- tail of the measurable constant
  let s : ℕ → Set Ω := fun n => {ω | (n : ℝ≥0∞) < Ĉ ω}
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_lt measurable_const hĈm
  have hsa : Antitone s := by
    intro m n hmn ω hω
    show (m : ℝ≥0∞) < Ĉ ω
    exact lt_of_le_of_lt (Nat.cast_le.2 hmn) hω
  have hsI : P (⋂ n, s n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hĈfin)
    simp only [mem_iInter, s, mem_ofPred_eq] at hω
    simp only [mem_ofPred_eq, not_lt, top_le_iff]
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
    exact (lt_asymm hn (hω n))
  have hstend : Tendsto (fun n => P (s n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P) (fun n => (hsm n).nullMeasurableSet) hsa
      ⟨0, measure_ne_top _ _⟩
    rwa [hsI] at this
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  obtain ⟨M, hM⟩ := (hstend.eventually (ge_mem_nhds hθ)).exists
  have herr := (tendsto_l9bErr κ CK).eventually
    (gt_mem_nhds (show (0 : ℝ) < η / (M + 1) by positivity))
  filter_upwards [herr, l9b_eventually_locHyp hd hκ] with ε hεerr ⟨hε, hε1, hrad, ha, hZ⟩
  refine le_trans (measure_mono_ae ?_) hM
  filter_upwards [l9b_ae_locField_le hd hκ hCK0 hCK hh hĈ hε hε1 hrad ha hZ] with ω hω hbad
  obtain ⟨x, hx, hlt⟩ := hbad
  show (M : ℝ≥0∞) < Ĉ ω
  by_contra hle
  push Not at hle
  have hfin : Ĉ ω ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top M) hle
  have hCM : (Ĉ ω).toReal ≤ M := by
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top M) hle
    simpa using this
  have he0 := l9bErr_nonneg κ hCK0 hε hε1
  have : (Ĉ ω).toReal * l9bErr d κ CK ε < η := by
    calc (Ĉ ω).toReal * l9bErr d κ CK ε ≤ M * l9bErr d κ CK ε :=
          mul_le_mul_of_nonneg_right hCM he0
      _ ≤ (M + 1) * l9bErr d κ CK ε := by nlinarith
      _ < (M + 1) * (η / (M + 1)) := by gcongr
      _ = η := by field_simp
  linarith [hω x hx]

end HigherDimLQGMetric
