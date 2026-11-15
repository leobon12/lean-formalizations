/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartFilt
import InteractingSLE.Spec.Restart.ConverseBeforeK2
import InteractingSLE.Spec.Sec7.Lemma71DChart
import InteractingSLE.Spec.Sec7.Lemma71KData
import InteractingSLE.Spec.Sec6.Prop65Gauss
import InteractingSLE.GFF.PushforwardLoewner

/-!
# The image word of the contact step, part 9: Lemma 2.11's martingale hypothesis from the chart clause at fixed
image times (steps B3 → B4)

Packet PROVE-WW-B18. PROVE-WW-B17 reduced the contact step to `ImageWordFiltStatement`: the explicit coupling means of
the killed image word `(imgW, imgVL, imgVR)` are local martingales before `min (swallowTime z) imgT` in the
filtration of the image word `imgFilt` (the usual augmentation of the raw filtration `imgRaw`). This file carries out
step B4 of the route recorded there — everything after the field content — with the landed tools of Lemma 7.1's
pipeline:

* the **chart** `imgChart s y = (Ψ, Ψ⁻¹, 0)` of `ℍ \ G`, `Ψ = R ∘ f_s ∘ R` for the recentred frozen reverse driver
  (`revDrv0`), conformal for every history, with lift `0` (at `κ = 4` the lift coefficient `χ` vanishes), and its
  domain, forward map and lift are measurable for the time-zero σ-algebra of `imgFilt` (they are functions of the
  stopped reverse history);
* the **fixed-time chart clause** on the raw filtration (`ImgChartConstStatement`, the named input: the conditional
  law of the field given `imgRaw r`, step B3) is lifted to every stopping time of `imgFilt`
  (`Lemma71D.isChartCouplingCharFun_usualAugmentation`), transported to the half-plane through the chart
  (`MartMeans2.isCouplingCharFun_of_isChartTransport`, field `chartField`), turned into local martingales of the
  coupling means with a null modification (`MartMeans2.exists_isLocalMartingaleBefore_meanProcOn`), and the null
  modification is removed (`ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn`, which allows the random
  initial word of the image: its marks are the images of the reverse force points);
* the pairings of the transported field are **integrable** although the initial word is random
  (`integrable_apply_of_isCouplingCharFun_of_bounded`: at time `0` the conditional law is Gaussian with a bounded
  `𝓖₀`-measurable mean and the deterministic variance `E₀(φ)`).

## Main results

* `imgChart`, `isConformal_imgChart`, `measurableSet_mem_dom_imgChart`, `measurable_indicator_fwd_imgChart`;
* `integrable_apply_of_isCouplingCharFun_of_bounded`;
* `ImgChartConstStatement` (**named input**, the fixed-image-time chart clause: step B3);
* **`imageWordFiltStatement_of_chartConst`**: `ImgChartConstStatement → ImageWordFiltStatement`;
* `reverseTipContactStatement_of_chartConst`.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open LQGMetric (DistOn TestOn)
open LawUnique ImgWord
open ImgDrv MartChar Sec7.PhaseSelFull

/-! ### The chart of `ℍ \ G` -/

namespace ImgWord

/-- **The chart of `ℍ \ G`** read from a reverse history: `Ψ = R ∘ f_s ∘ R` for the recentred frozen reverse driver,
its inverse `Ψ⁻¹ = R ∘ F_s ∘ R`, and the lift `0` (unused: at `κ = 4` the lift coefficient vanishes). -/
def imgChart (s : ℚ) (y : HistorySpace 1 1) : Chart :=
  (revChart (revDrv0 s y) s, revChartInv (revDrv0 s y) s, fun _ => 0)

end ImgWord

section Chart

variable {s : ℚ}

theorem revDrv0_zero (y : HistorySpace 1 1) : revDrv0 s y 0 = 0 := by
  simp only [revDrv0, sub_self]

theorem isConformal_imgChart (hs : 0 < s) (y : HistorySpace 1 1) : (imgChart s y).IsConformal := by
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  have hb := isConformalBijection_revChartInv (continuous_revDrv0 (s := s) y) (revDrv0_zero y) hs'
  refine ⟨hb.1, fun w hw => (hb.2.mapsTo hw).1, fun w hw => ?_⟩
  exact revChart_revChartInv (continuous_revDrv0 (s := s) y) (revDrv0_zero y) hs' hw

theorem continuousOn_lift_imgChart (y : HistorySpace 1 1) :
    ContinuousOn (imgChart s y).2.2 (imgChart s y).dom :=
  continuousOn_const

/-- The domain of the chart is `ℍ \ G`, `G = R(K_s)`. -/
theorem mem_dom_imgChart_iff (hs : 0 < s) (y : HistorySpace 1 1) {z : ℂ} :
    z ∈ (imgChart s y).dom ↔ z ∈ H ∧ negInv z ∉ fwdHull (revDrv0 s y) s := by
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  have hb := isConformalBijection_revChartInv (continuous_revDrv0 (s := s) y) (revDrv0_zero y) hs'
  rw [← SetLike.mem_coe, (isConformal_imgChart hs y).coe_dom]
  change z ∈ revChartInv (revDrv0 s y) s '' H ↔ _
  rw [hb.2.image_eq]
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, fun h => hn ⟨negInv z, h, negInv_negInv' z⟩⟩
  · rintro ⟨hz, hn⟩
    refine ⟨hz, ?_⟩
    rintro ⟨x, hx, rfl⟩
    exact hn (by rwa [negInv_negInv'])

/-- The recentred frozen reverse driver as a process on the glued space. -/
def revProc (s : ℚ) {Ω : Type*} : ℝ≥0 → Ω × HistorySpace 1 1 → ℝ := fun t p => revDrv0 s p.2 t

theorem rpath_revProc {Ω : Type*} (p : Ω × HistorySpace 1 1) : Ito.rpath (revProc s · p) = revDrv0 s p.2 := by
  funext r
  show revDrv0 s p.2 (r.toNNReal : ℝ) = revDrv0 s p.2 r
  simp only [revDrv0, Ito.rpath, Real.toNNReal_coe]

theorem loewnerChartAt_revProc_dom {Ω : Type*} (hs : 0 < s) (p : Ω × HistorySpace 1 1) {x : ℂ} :
    x ∈ (Chart.loewnerChartAt (revProc s) (s : ℝ).toNNReal p).dom ↔ x ∈ H ∧ x ∉ fwdHull (revDrv0 s p.2) s := by
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  have hw := continuous_revDrv0 (s := s) p.2
  have hw0 : revDrv0 s p.2 0 = 0 := revDrv0_zero p.2
  have hc := Chart.isConformal_id.loewner hw hw0 hs'
  have e : Chart.loewnerChartAt (revProc s) (s : ℝ).toNNReal p = Chart.id.loewner (revDrv0 s p.2) s := by
    rw [Chart.loewnerChartAt, rpath_revProc, Real.coe_toNNReal _ hs']
  rw [e, ← SetLike.mem_coe, hc.coe_dom]
  change x ∈ fwdMapInv (revDrv0 s p.2) s '' H ↔ _
  rw [QuantumZipper.RS.image_fwdMapInv_H hw hw0 hs']
  rfl

end Chart

section ChartMeas

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {E : Set (Ω × HistorySpace 1 1)} {μ : Measure (Ω × HistorySpace 1 1)}

/-- The recentred frozen reverse driver is known at time `0` (it is a function of the stopped reverse history). -/
theorem measurable_revProc_imgFilt (t : ℝ≥0) :
    Measurable[imgFilt μ s ζ W E 0] (revProc s t : Ω × HistorySpace 1 1 → ℝ) := by
  have hF : Measurable fun y' : HistorySpace 1 1 =>
      Ito.rpath (Sec4.regPath y') (t : ℝ) - Ito.rpath (Sec4.regPath y') 0 :=
    (Sec4.measurable_regPath_apply _).sub (Sec4.measurable_regPath_apply _)
  exact hF.comp (measurable_revStop_imgFilt (μ := μ) (s := s) (ζ := ζ) (W := W) (E := E) 0)

/-- The constant filtration at the time-zero σ-algebra of `imgFilt`. -/
abbrev imgFilt0 (μ : Measure (Ω × HistorySpace 1 1)) (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (E : Set (Ω × HistorySpace 1 1)) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 1 1)) :=
  Filtration.const ℝ≥0 (imgFilt μ s ζ W E 0) ((imgFilt μ s ζ W E).le 0)

theorem adapted_revProc_imgFilt0 : Adapted (imgFilt0 μ s ζ W E) (revProc s : ℝ≥0 → Ω × HistorySpace 1 1 → ℝ) :=
  fun t => measurable_revProc_imgFilt t

omit mΩ in
theorem continuous_revProc (p : Ω × HistorySpace 1 1) : Continuous fun t => revProc s t p :=
  (continuous_revDrv0 (s := s) p.2).comp NNReal.continuous_coe

omit mΩ in
theorem revProc_zero (p : Ω × HistorySpace 1 1) : revProc s 0 p = 0 := revDrv0_zero p.2

omit mΩ in
theorem setOf_mem_dom_imgChart (hs : 0 < s) {z : ℂ} (hz : z ∈ H) :
    {p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom} =
      {p | negInv z ∈ (Chart.loewnerChartAt (revProc s) (s : ℝ).toNNReal p).dom} := by
  ext p
  simp only [mem_ofPred_eq, mem_dom_imgChart_iff hs, loewnerChartAt_revProc_dom hs, hz, true_and, negInv_mem_H hz]

omit mΩ in
theorem setOf_mem_dom_imgChart_of_notMem (hs : 0 < s) {z : ℂ} (hz : z ∉ H) :
    {p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom} = ∅ := by
  ext p
  simp only [mem_ofPred_eq, mem_dom_imgChart_iff hs, hz, false_and, mem_empty_iff_false]

/-- **The domain events of the chart are known at time `0`.** -/
theorem measurableSet_mem_dom_imgChart (hs : 0 < s) (z : ℂ) :
    MeasurableSet[imgFilt μ s ζ W E 0] {p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom} := by
  by_cases hz : z ∈ H
  · rw [setOf_mem_dom_imgChart hs hz]
    exact Chart.measurableSet_mem_dom_loewnerChartAt (𝓖 := imgFilt0 μ s ζ W E) adapted_revProc_imgFilt0
      continuous_revProc revProc_zero _ _
  · rw [setOf_mem_dom_imgChart_of_notMem hs hz]
    exact @MeasurableSet.empty _ (imgFilt μ s ζ W E 0)

/-- **The forward map of the chart is known at time `0`** (on its domain). -/
theorem measurable_indicator_fwd_imgChart (hs : 0 < s) (z : ℂ) :
    Measurable[imgFilt μ s ζ W E 0]
      ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).1 z) := by
  classical
  by_cases hz : z ∈ H
  · have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
    have h := Chart.measurable_indicator_fwd_loewnerChartAt (𝓖 := imgFilt0 μ s ζ W E) adapted_revProc_imgFilt0
      continuous_revProc revProc_zero (s : ℝ).toNNReal (negInv z)
    have e : ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).1 z) =
        negInv ∘ ({p | negInv z ∈ (Chart.loewnerChartAt (revProc s) (s : ℝ).toNNReal p).dom}.indicator
          fun p => (Chart.loewnerChartAt (revProc s) (s : ℝ).toNNReal p).1 (negInv z)) := by
      rw [setOf_mem_dom_imgChart hs hz]
      funext p
      by_cases hp : p ∈ {p | negInv z ∈ (Chart.loewnerChartAt (revProc s) (s : ℝ).toNNReal p).dom}
      · rw [indicator_of_mem hp, Function.comp_apply, indicator_of_mem hp]
        simp only [imgChart, revChart, Chart.loewnerChartAt, Chart.loewner, Chart.id, rpath_revProc,
          Real.coe_toNNReal _ hs']
      · rw [indicator_of_notMem hp, Function.comp_apply, indicator_of_notMem hp]
        simp [negInv]
    rw [e]
    exact measurable_negInv.comp h
  · rw [setOf_mem_dom_imgChart_of_notMem hs hz, indicator_empty]
    exact measurable_const

/-- The lift of the chart (`0`) is known at time `0`. -/
theorem measurable_indicator_lift_imgChart (z : ℂ) :
    Measurable[imgFilt μ s ζ W E 0]
      ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).2.2 z) := by
  have e : ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).2.2 z) =
      fun _ => 0 := by
    funext p
    simp [imgChart]
  rw [e]
  exact measurable_const

end ChartMeas

/-! ### Integrable pairings for a random initial word -/

section Integrable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The explicit mean is bounded uniformly in the force positions. -/
theorem abs_meanExt_le (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ)
    {z : ℂ} (hz : z ∈ H) :
    |meanExt κ ρL ρR w vL vR z| ≤ |Real.pi / Real.sqrt κ| *
      (3 + 2 * ∑ i, |(Ito.weightWord ρL ρR).ρL i| + ∑ i, |(Ito.weightWord ρL ρR).ρR i|) :=
  Impl.abs_forceExt_le κ (Ito.weightWord ρL ρR) _ _ hz

/-- **Integrable pairings of a coupled field with a random initial word.** If `h` satisfies the coupling clause
(`IsCouplingCharFun`), and almost surely the lifetime is positive, the driver starts at `0` and is continuous before
the lifetime, then every pairing `(h, φ)` is integrable: given `𝓖₀` it is Gaussian with the bounded mean
`∫ 𝔥₀ φ` (`𝔥₀` the explicit extension of the random initial word) and the deterministic variance `E₀(φ)`. -/
theorem integrable_apply_of_isCouplingCharFun_of_bounded [IsProbabilityMeasure P]
    (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
    (h0 : ∀ᵐ ω ∂P, 0 < ζ ω ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    (φ : TestOn upperHalfPlaneOpens) (hφm : Measurable fun ω => h ω φ) :
    Integrable (fun ω => h ω φ) P := by
  set E₀ : ℝ := loewnerGreenEnergy (fun _ => 0) 0 φ with hE₀
  have hE0 : 0 ≤ E₀ := Coupling.MartMeans2.loewnerGreenEnergy_zero_nonneg φ
  have hτ : IsStoppingTime 𝓖 fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓖 0
  have hτm : hτ.measurableSpace = 𝓖 0 := IsStoppingTime.measurableSpace_const 𝓖 0
  have hlt : ∀ᵐ ω ∂P, ((((0 : ℝ≥0) : WithTop ℝ≥0)) : ℝ≥0∞) < ζ ω := by
    filter_upwards [h0] with ω hω
    exact hω.1
  set u : Ω → ℂ → ℝ := fun ω => meanExt κ ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun i => VR i 0 ω) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω -
          W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω -
          W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω))
      (u ω) := fun ω => isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _
  set M : Ω → ℝ := fun ω => ∫ z, u ω z * φ z with hMdef
  have hcond : ∀ θ : ℝ, P[fun ω => cexp (I * ((θ * h ω φ : ℝ) : ℂ)) | 𝓖 0] =ᵐ[P]
      fun ω => cexp (I * ((θ * M ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (θ ^ 2 * E₀)) : ℝ) : ℂ) := by
    intro θ
    have hcl := hcf _ hτ hlt u hu (θ • φ)
    rw [hτm] at hcl
    have e1 : (fun ω' => cexp (I * (h ω' (θ • φ) : ℂ))) = fun ω' => cexp (I * ((θ * h ω' φ : ℝ) : ℂ)) := by
      funext ω'
      rw [map_smul, smul_eq_mul]
    rw [e1] at hcl
    filter_upwards [hcl, h0] with ω hω hgω
    obtain ⟨hζ, hwc, hw0⟩ := hgω
    have ht0 : (((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : ℝ) = 0 := by
      rw [WithTop.untopD_coe, NNReal.coe_zero]
    have hK : fwdHull (fun s : ℝ => W s.toNNReal ω) (((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : ℝ) = ∅ := by
      rw [ht0]
      exact Coupling.MartMeans2.fwdHull_rpath_zero (w := fun t => W t ω) hwc hζ
    rw [hω (by rw [hK]; exact disjoint_empty _), ht0]
    have hr0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by
      simp only [Real.toNNReal_zero, hw0]
    have hcoe : (⇑(θ • φ) : ℂ → ℝ) = θ • ⇑φ := by
      funext y
      simp
    have hmean : (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) 0 (u ω) z * (θ • φ) z) = θ * M ω := by
      rw [hcoe, ← Coupling.MartMeans.integral_mul_smul (u ω) θ φ]
      congr 1
      funext z
      by_cases hz : (θ • ⇑φ) z = 0
      · simp only [hz, mul_zero]
      · have hzH : z ∈ H := φ.tsupport_subset (subset_tsupport _ fun h0 => hz (by
          simp only [Pi.smul_apply, smul_eq_mul, h0, mul_zero]))
        have hz0 : z ≠ 0 := by
          intro h; rw [h] at hzH; exact lt_irrefl _ (show (0 : ℂ).im > 0 from hzH)
        rw [Coupling.MartMeans2.couplingMean_zero κ hr0 (u ω) hz0]
    have hen : loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) 0 ⇑(θ • φ) = θ ^ 2 * E₀ := by
      rw [hcoe, Coupling.MartMeans.loewnerGreenEnergy_smul, Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hr0 φ]
    rw [hmean, hen, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- a `𝓖₀`-measurable version of the mean
  obtain ⟨M', hM'm, hM'e⟩ := Sec6.Prop65.exists_measurable_ae_eq_of_condCharFun
    (V := fun _ => E₀) (@measurable_const _ _ _ (𝓖 0) _) hcond
  have hcond' : ∀ θ : ℝ, P[fun ω => cexp (I * ((θ * h ω φ : ℝ) : ℂ)) | 𝓖 0] =ᵐ[P]
      fun ω => cexp (I * ((θ * M' ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (θ ^ 2 * E₀)) : ℝ) : ℂ) := by
    intro θ
    filter_upwards [hcond θ, hM'e] with ω h1 h2
    rw [h1, h2]
  have hsub : ∀ θ : ℝ, P[fun ω => cexp (I * ((θ * (h ω φ - M' ω) : ℝ) : ℂ)) | 𝓖 0] =ᵐ[P]
      fun _ => ((Real.exp (-(1 / 2) * (θ ^ 2 * E₀)) : ℝ) : ℂ) := fun θ =>
    Sec6.Prop65.condCharFun_sub_of_condCharFun (V := fun _ => E₀) hφm hM'm (𝓖.le 0) θ (hcond' θ)
  have hY := Sec6.Prop65.integrable_pow_of_condCharFun (𝓖.le 0) (hφm.sub (hM'm.mono (𝓖.le 0) le_rfl))
    (V := fun _ => E₀) measurable_const (fun _ => hE0) (K := E₀) (fun _ => le_rfl) hsub 1
  simp only [pow_one] at hY
  -- the mean is bounded
  set C : ℝ := |Real.pi / Real.sqrt κ| *
    (3 + 2 * ∑ i, |(Ito.weightWord ρL ρR).ρL i| + ∑ i, |(Ito.weightWord ρL ρR).ρR i|) with hC
  have hφi : Integrable (fun z => C * |φ z|) :=
    (φ.continuous.abs.integrable_of_hasCompactSupport φ.hasCompactSupport.abs).const_mul C
  have hMb : ∀ ω, |M ω| ≤ ∫ z, C * |φ z| := fun ω => by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hφi (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : φ z = 0
    · simp [hz]
    · have hzH : z ∈ H := φ.tsupport_subset (subset_tsupport _ hz)
      exact mul_le_mul_of_nonneg_right (abs_meanExt_le κ ρL ρR _ _ _ hzH) (abs_nonneg _)
  have hM'i : Integrable M' P := by
    refine Integrable.of_bound (hM'm.mono (𝓖.le 0) le_rfl).aestronglyMeasurable (∫ z, C * |φ z|) ?_
    filter_upwards [hM'e] with ω hω
    rw [hω, Real.norm_eq_abs]
    exact hMb ω
  have e : (fun ω => h ω φ) = fun ω => (h ω φ - M' ω) + M' ω := by
    funext ω; ring
  rw [e]
  exact hY.add hM'i

end Integrable

/-! ### Step B4: from the chart clause at fixed image times to Lemma 2.11's martingale hypothesis -/

/-- **Named input: the chart coupling clause of the image word at fixed image times** (step B3 of PROVE-WW-B15's plan,
the field content of Wang–Wu's proof of Proposition 4.18: "conditionally on the stopped reverse line the forward line
before contact is `SLE₄(ρ)` in `ℍ \ G`"). In the setting of `ReverseTipContactStatement`, for each rational `s > 0`,
at every fixed image time `r`, for every choice `u` of the bounded harmonic extensions of the image word's data at `r`
and every test function `φ`, almost surely on `{r < imgT} ∩ {supp φ ⊆ Ψ⁻¹(ℍ \ K̃_r)}` the conditional characteristic
function of `(h, φ)` given the raw image filtration `imgRaw r` is that of the image coupling mean pulled back by the
chart `Ψ` plus a zero-boundary GFF on `Ψ⁻¹(ℍ \ K̃_r)` (`Lemma71D.IsChartCouplingCharFunConst` with the chart
`imgChart`, height shift `0` and lift coefficient `0`). -/
def ImgChartConstStatement : Prop :=
  ∀ (rL rR : ℝ), 0 ≤ rL → 0 ≤ rR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (𝓕₂ : Filtration ℝ≥0 mΩ₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ)
      (ζ₂ : Ω₂ → ℝ≥0∞) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ →
      P.map h = P₂.map (fun ω => reflectField (h₂ ω)) →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k],
        P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
          P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k →
        ∀ s : ℚ, 0 < s →
          Sec7.Lemma71D.IsChartCouplingCharFunConst 4 (imgρ rL) (imgρ rR) (glueMeasure P k h hC.2.1)
            (imgRaw s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W))
            (imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W))
            (imgVL s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W))
            (imgVR s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W))
            (fun p => (imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p : ℝ≥0∞))
            (fun p => imgChart s p.2) 0 0 (fun p => h p.1)

/-- **Lemma 2.11's martingale hypothesis for the explicit image word from the chart clause at fixed image times**
(step B4): the clause is lifted to every stopping time of `imgFilt`, transported to `ℍ` through the chart, and turned
into local martingales of the explicit coupling means (Lemma 7.1's pipeline, with the random initial word allowed). -/
theorem imageWordFiltStatement_of_chartConst (hI : ImgChartConstStatement.{u}) : ImageWordFiltStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs z hz
  set μ := glueMeasure P k h hC.2.1 with hμ
  set E := glueGood μ s ζ W with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood
  have hEg : ∀ p ∈ E, IsGlueGood s ζ W p := isGlueGood_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hK := isKilledWord_img hs hEg (ζ := ζ) (W := W)
  set 𝓖 := imgFilt μ s ζ W E with h𝓖
  have : 𝓖.IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  set ζ' : Ω × HistorySpace 1 1 → ℝ≥0∞ := fun p => (imgT s ζ W E p : ℝ≥0∞) with hζ'
  set hF : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens := fun p => h p.1 with hFdef
  have hFm : Measurable hF := hC.2.1.comp measurable_fst
  have hcc : ∀ p : Ω × HistorySpace 1 1, (imgChart s p.2).IsConformal := fun p => isConformal_imgChart hs p.2
  -- the chart clause at every stopping time of `imgFilt`
  have hcf0 := hI rL rR hL hR P 𝓕 W VL VR B ζ h hC P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs
  have hcfU : Coupling.MartMeans2.IsChartCouplingCharFun 4 (imgρ rL) (imgρ rR) μ 𝓖 (imgW s ζ W E)
      (imgVL s ζ W E) (imgVR s ζ W E) ζ' (fun p => imgChart s p.2) 0 0 hF :=
    Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation hFm hcc
      (fun p => continuousOn_lift_imgChart p.2) (fun p => hK.contW p) (fun i p => (hK.pathL p i).1)
      (fun j p => (hK.pathR p j).1) (fun p t ht => ⟨fun i => hK.ordL p t i ht, fun j => hK.ordR p t j ht⟩) hcf0
  -- the transported field
  set h' : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens :=
    fun p => Sec7.Lemma71K.chartField (imgChart s p.2) 0 0 (hF p) with hh'
  have ht : ∀ p, IsChartTransport (imgChart s p.2) 1 0 0 (hF p) (h' p) := fun p =>
    Sec7.Lemma71K.isChartTransport_chartField (hcc p) (continuousOn_lift_imgChart p.2) 0 0 (hF p)
  have hdom : ∀ z, MeasurableSet[𝓖 0] {p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom} := fun z =>
    measurableSet_mem_dom_imgChart hs z
  have hfwd : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).1 z) := fun z =>
    measurable_indicator_fwd_imgChart hs z
  have hliftm : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).2.2 z) := fun z =>
    measurable_indicator_lift_imgChart z
  have hcf' : Coupling.MartMeans.IsCouplingCharFun 4 (imgρ rL) (imgρ rR) μ 𝓖 (imgW s ζ W E) (imgVL s ζ W E)
      (imgVR s ζ W E) ζ' h' :=
    Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hcc hdom hfwd hliftm
      (fun p => continuousOn_lift_imgChart p.2) hFm (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p⟩)
      hcfU ht
  -- measurability of the transported field
  have hh'm : Measurable h' := by
    have hm := Chart.measurable_chartTransport_random' hcc (fun z => 𝓖.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl)
      (fun p => continuousOn_lift_imgChart p.2) hFm 1 0 0
    have e : h' = fun p => Chart.chartTransport (hcc p) 1 0 0 (hF p) := by
      funext p
      simp only [hh', Sec7.Lemma71K.chartField, hcc p, ↓reduceDIte]
    rw [e]
    exact hm
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun p => h' p φ) μ := fun φ =>
    integrable_apply_of_isCouplingCharFun_of_bounded hcf'
      (Eventually.of_forall fun p => ⟨(isKilledArc_gCurve hs hEg (ζ := ζ) (W := W) p).zero_lt_kLife, hK.contW p,
        hK.w_zero p⟩)
      φ ((LQGMetric.measurable_distOn_apply φ).comp hh'm)
  -- the filtration clauses
  have hnull : ∀ A, MeasurableSet A → μ A = 0 → MeasurableSet[𝓖 0] A := fun A hA h0 =>
    Ito.measurableSet_usualAugmentation_of_null hA h0 0
  have hζm : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {p | ζ' p ≤ t} := by
    intro t
    have h1 := (measurableSet_imgFilt_of_gen (μ := μ) ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩
      (measurableSet_lt_imgT hs hWad hE hEg t)).compl
    convert h1 using 1
    ext p
    simp only [hζ', mem_ofPred_eq, mem_compl_iff, not_lt]
    rfl
  have hWa : StronglyAdapted 𝓖 (imgW s ζ W E) :=
    stronglyAdapted_imgFilt_of (measurable_imgW hs hWad hE hEg) fun r B hB => ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inl rfl⟩⟩
  have hVLa : ∀ i, StronglyAdapted 𝓖 (imgVL s ζ W E i) := fun i =>
    stronglyAdapted_imgFilt_of (measurable_imgVL hs hWad hE hEg i) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩
  have hVRa : ∀ j, StronglyAdapted 𝓖 (imgVR s ζ W E j) := fun j =>
    stronglyAdapted_imgFilt_of (measurable_imgVR hs hWad hE hEg j) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inr ⟨j, rfl⟩)⟩⟩
  have hσ : ∀ n, IsStoppingTime 𝓖 fun p => (imgAnn s ζ W E n p : WithTop ℝ≥0) := by
    intro n r
    have e : {p : Ω × HistorySpace 1 1 | ((imgAnn s ζ W E n p : ℝ≥0) : WithTop ℝ≥0) ≤ r} =
        {p | imgAnn s ζ W E n p ≤ r} := by
      ext p
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    rw [e]
    exact measurableSet_imgFilt_of_gen ⟨r, le_rfl, Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))⟩
      (measurableSet_le (measurable_imgAnn hs hWad hE hEg n) measurable_const)
  have hT : Coupling.IsAnnouncingSeq 𝓖 μ ζ' (imgAnn s ζ W E) := by
    refine ⟨hσ, monotone_imgAnn hs hEg, fun n => Eventually.of_forall fun p => imgAnn_lt_imgT hs hEg n p, ?_⟩
    filter_upwards [ae_mem_glueGood (ae_isGlueGood hL hR hC hC₂ hlaw k hk hs)] with p hp
    exact fun u hu => exists_le_imgAnn hs hEg hp hu
  obtain ⟨G, hG, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull
    (MartChar.adaptedBefore_of_stronglyAdapted hζm hWa)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVLa i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVRa j))
    (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p, ⟨fun i => (hK.pathL p i).1, fun j => (hK.pathR p j).1⟩,
      fun t ht => ⟨fun i => hK.ordL p t i ht, fun j => hK.ordR p t j ht⟩⟩)
    hT hint hcf' (fun p t => meanExt 4 (imgρ rL) (imgρ rR) (imgW s ζ W E t p) (fun i => imgVL s ζ W E i t p)
      (fun j => imgVR s ζ W E j t p))
    (fun p t => isBoundedHarmonicExtension_meanExt 4 (imgρ rL) (imgρ rR) _ _ _) hz
  exact Restart.ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG hGae
    (Restart.ConverseBefore.measurable_coupProc_zero hK.w_zero (fun i => measurable_imgVL hs hWad hE hEg i 0)
      (fun j => measurable_imgVR hs hWad hE hEg j 0) hz) hloc

/-- **The contact step from the chart clause at fixed image times** (with PROVE-WW-B15–B17's reductions). -/
theorem reverseTipContactStatement_of_chartConst (hI : ImgChartConstStatement.{u}) :
    ReverseTipContactStatement.{u} :=
  reverseTipContactStatement_of_imageWordFilt (imageWordFiltStatement_of_chartConst hI)

end InteractingSLE.WangWu
