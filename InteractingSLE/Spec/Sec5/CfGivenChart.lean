/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfGivenBridge
import InteractingSLE.Spec.Sec7.Lemma71DChart
import InteractingSLE.Spec.Exist.StagedLaw3Rand
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart
import InteractingSLE.Spec.Restart.DomainMarkovMeanLoc
import InteractingSLE.Spec.Sec7.LocalExtOChart

/-!
# K2's input (S) for the image counterflow from the chart coupling clause at fixed times

Packet PROVE-CFGIVEN. The Lemma 4.7 chain of the cross-conditioning (PROVE-CFRESTART*, PROVE-L47-ANGLE) proves the
coupling clause of the image counterflow in **chart form at fixed times** (`Sec7.Lemma71D.IsChartCouplingCharFunConst`):
the field `−h` read in the chart `Ψ ∘ R`, with the counterflow constants `(a, k) = (−πχ, −χ)`, has given the raw
filtration of the image word at each fixed image time the Gaussian law of the image word's coupling mean. K2 wants
instead (S) (`DomainMarkov.K2.HasSafeLaw`) for the field read in the image chart. This file converts the first into the
second for the image chart of the record of a flow prefix:

* `cfChart r = (recChart r).trans infinitySourceChart` — the record chart (tip to `0`, `∞` fixed) followed by
  `R(z) = −1/z`; it is conformal, its domain is the record chart's, its lift is continuous there, and its domain,
  forward map and lift are measurable in the record (`measurableSet_mem_dom_cfChart`,
  `measurable_indicator_fwd_cfChart`, `measurable_indicator_lift_cfChart`);
* `isChartTransport_cfChart_imgField`: `imgField κ r f` is the transport of `−f` through `cfChart r` with
  `(σ, a, k) = (1, −πχ, −χ)` (composition of the record rule and the counterflow rule, `isChartTransport_trans_sign`);
* **`hasSafeLaw_imgField_of_chartConst`**: the fixed-time chart clause for a raw filtration `𝓐 ⊇ σ(R)` gives (S) for
  `imgField κ R h` (the clause at every stopping time of the usual augmentation,
  `isChartCouplingCharFun_usualAugmentation`; the transported clause,
  `MartMeans2.isCouplingCharFun_of_isChartTransport`; constant stopping times).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfGiven

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.PocketTraversal
open Exist Exist.Staged Exist.StagedLaw

/-! ### The image chart -/

/-- **The image chart of a record**: the record chart (tip to `0`, `∞` fixed) followed by `R(z) = −1/z`. -/
def cfChart (r : RecData) : Chart := (recChart r).trans infinitySourceChart

theorem isConformal_cfChart (r : RecData) : (cfChart r).IsConformal :=
  (isConformal_recChart r).trans Chart.isConformal_infinitySourceChart

/-- `R(z) = −1/z` maps `ℍ` onto `ℍ`. -/
theorem image_infinitySourceChart_inv_H : infinitySourceChart.2.1 '' H = H := by
  refine Subset.antisymm (fun _ ⟨w, hw, e⟩ => e ▸ WangWu.negInv_mem_H hw) fun z hz =>
    ⟨WangWu.negInv z, WangWu.negInv_mem_H hz, WangWu.negInv_negInv z⟩

theorem coe_dom_cfChart (r : RecData) : ((cfChart r).dom : Set ℂ) = (recChart r).dom := by
  rw [(isConformal_cfChart r).coe_dom, (isConformal_recChart r).coe_dom, cfChart, Chart.trans_image,
    image_infinitySourceChart_inv_H]

theorem mem_dom_cfChart_iff (r : RecData) {z : ℂ} : z ∈ (cfChart r).dom ↔ z ∈ (recChart r).dom := by
  rw [← SetLike.mem_coe, coe_dom_cfChart, SetLike.mem_coe]

/-- **The forward map of the record chart is continuous on its domain, with values in `ℍ`.** -/
theorem continuousOn_fst_recChart (r : RecData) :
    ContinuousOn (recChart r).1 (recChart r).dom ∧ MapsTo (recChart r).1 (recChart r).dom H := by
  set y := recHist r
  have hw : Continuous (Ito.rpath (LocalExt.histDrv y)) :=
    (LocalExt.continuous_histDrv y).comp continuous_real_toNNReal
  have hw0 : Ito.rpath (LocalExt.histDrv y) 0 = 0 := by
    simp only [Ito.rpath, Real.toNNReal_zero, LocalExt.histDrv_zero]
  have hs : (0 : ℝ) ≤ (LocalExt.histTime y : ℝ) := (LocalExt.histTime y).coe_nonneg
  have hdom : ((recChart r).dom : Set ℂ) = H \ fwdHull (Ito.rpath (LocalExt.histDrv y)) (LocalExt.histTime y) := by
    rw [(isConformal_recChart r).coe_dom]
    exact QuantumZipper.RS.image_fwdMapInv_H hw hw0 hs
  have e : (recChart r).1 = QuantumZipper.fwdMap (Ito.rpath (LocalExt.histDrv y)) (LocalExt.histTime y) := rfl
  refine ⟨?_, ?_⟩
  · rw [show ((recChart r).dom : Set ℂ) = _ from hdom, e]
    exact (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs).continuousOn
  · rw [show ((recChart r).dom : Set ℂ) = _ from hdom, e]
    exact fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs hz

/-- **The lift of the image chart is continuous on its domain.** -/
theorem continuousOn_lift_cfChart (r : RecData) : ContinuousOn (cfChart r).2.2 (cfChart r).dom := by
  obtain ⟨hf, hmap⟩ := continuousOn_fst_recChart r
  have hR : ContinuousOn infinitySourceChart.2.2 H := Sec7.StripSysField.continuousOn_infinitySourceChart_lift'
  have hl : ContinuousOn (recChart r).2.2 (recChart r).dom := LocalExt.continuousOn_lift_histChart (recHist r)
  have hd : ((cfChart r).dom : Set ℂ) = (recChart r).dom := coe_dom_cfChart r
  rw [show ((cfChart r).dom : Set ℂ) = ((recChart r).dom : Set ℂ) from hd]
  exact (hR.comp hf hmap).add hl

/-- The lift of the record chart, in the coordinate of `ℍ`, is continuous. -/
theorem continuousOn_lift_inv_cfChart (r : RecData) :
    ContinuousOn (fun w => (cfChart r).2.2 ((cfChart r).2.1 w)) H :=
  Theorem14.GW2JointKernel.continuousOn_trans_lift (isConformal_recChart r) Chart.isConformal_infinitySourceChart
    (continuousOn_recChart_lift r) Chart.continuousOn_infinitySourceChart_lift

/-! ### Measurability in the record -/

theorem setOf_mem_dom_cfChart (z : ℂ) :
    {r : RecData | z ∈ (cfChart r).dom} = {r : RecData | z ∈ (recChart r).dom} := by
  ext r
  exact mem_dom_cfChart_iff r

theorem measurableSet_mem_dom_cfChart (z : ℂ) : MeasurableSet {r : RecData | z ∈ (cfChart r).dom} := by
  rw [setOf_mem_dom_cfChart]
  exact measurableSet_mem_dom_recChart z

theorem measurable_indicator_fwd_cfChart (z : ℂ) :
    Measurable ({r : RecData | z ∈ (cfChart r).dom}.indicator fun r => (cfChart r).1 z) := by
  classical
  have e : ({r : RecData | z ∈ (cfChart r).dom}.indicator fun r => (cfChart r).1 z) =
      (fun v : ℂ => -v⁻¹) ∘ ({r : RecData | z ∈ (recChart r).dom}.indicator fun r => (recChart r).1 z) := by
    rw [setOf_mem_dom_cfChart]
    funext r
    by_cases hr : r ∈ {r : RecData | z ∈ (recChart r).dom}
    · rw [indicator_of_mem hr, Function.comp_apply, indicator_of_mem hr]
      rfl
    · rw [indicator_of_notMem hr, Function.comp_apply, indicator_of_notMem hr, inv_zero, neg_zero]
  rw [e]
  exact (measurable_inv.neg).comp (measurable_indicator_fwd_recChart z)

theorem measurable_indicator_lift_cfChart (z : ℂ) :
    Measurable ({r : RecData | z ∈ (cfChart r).dom}.indicator fun r => (cfChart r).2.2 z) := by
  classical
  set D := {r : RecData | z ∈ (recChart r).dom} with hD
  set F : ℂ → ℝ := fun v => (-2 * log v).im with hF
  have hFm : Measurable F := continuous_im.measurable.comp (measurable_const.mul measurable_log)
  have e : ({r : RecData | z ∈ (cfChart r).dom}.indicator fun r => (cfChart r).2.2 z) =
      fun r => F (D.indicator (fun r => (recChart r).1 z) r) + D.indicator (fun r => (recChart r).2.2 z) r := by
    rw [setOf_mem_dom_cfChart]
    funext r
    by_cases hr : r ∈ D
    · rw [indicator_of_mem hr, indicator_of_mem hr, indicator_of_mem hr]
      rfl
    · rw [indicator_of_notMem hr, indicator_of_notMem hr, indicator_of_notMem hr, add_zero]
      simp only [hF, log_zero, mul_zero, zero_im]
  rw [e]
  exact (hFm.comp (measurable_indicator_fwd_recChart z)).add (measurable_indicator_lift_recChart z)

/-! ### The image field as a transport through the image chart -/

/-- **`imgField κ r f` is the transport of `−f` through `cfChart r`** with `(σ, a, k) = (1, −πχ, −χ)`. -/
theorem isChartTransport_cfChart_imgField {κ : ℝ} (hκ : 0 < κ) (r : RecData) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport (cfChart r) 1 (-(π * chiC κ)) (-chiC κ) (-f) (imgField κ r f) := by
  have h₁ := isChartTransport_recField κ r f
  have h₂ := isChartTransport_imgField κ r f
  rw [Sec4.chiC_sixteen_div hκ, show -chiC κ = (-1) * chiC κ by ring] at h₂
  have h := Theorem14.GW2JointKernel.isChartTransport_trans_sign (isConformal_recChart r)
    Chart.isConformal_infinitySourceChart (continuousOn_recChart_lift r)
    Chart.continuousOn_infinitySourceChart_lift h₁ h₂
  intro φ φ' hs hφ
  have hn : (-f) φ = -(f φ) := rfl
  rw [h φ φ' hs hφ, hn]
  change (-1 * 1 * f φ + (-1 * 0 + -(π * chiC κ)) * ∫ w, φ' w) +
      -1 * chiC κ * ∫ w, (cfChart r).2.2 ((cfChart r).2.1 w) * φ' w = _
  ring

/-! ### (S) from the chart clause at fixed times -/

section Safe

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **K2's (S) for the image field from the chart coupling clause at fixed times.** Let `𝓐 ⊇ σ(R)` be a raw
filtration, `W` a globally continuous driver from `0` with the geometric images of a word as force points. If the
field `−h` read in the image charts `cfChart R` with `(a, k) = (−πχ, −χ)` satisfies the chart coupling clause at fixed
times of `𝓐` (lifetime `⊤`), then `imgField κ R h` satisfies (S) for `𝓐` with lifetime `⊤`. -/
theorem hasSafeLaw_imgField_of_chartConst (hκ : 0 < κ) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {R : Ω → RecData} {𝓐 : Filtration ℝ≥0 mΩ} (h𝒢 : MeasurableSpace.comap R inferInstance ≤ 𝓐 0)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω)
    (hcf : Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 W (geomLW W xL) (geomRW W xR)
      (fun _ => ⊤) (fun ω => cfChart (R ω)) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω)) :
    HasSafeLaw (16 / κ) ρL ρR P 𝓐 univ (fun _ => ⊤) W (geomLW W xL) (geomRW W xR)
      (fun ω => imgField κ (R ω) (h ω)) := by
  have hhn : Measurable fun ω => -h ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ => ((LQGMetric.measurable_distOn_apply φ).comp hh).neg
  have hc : ∀ ω, (cfChart (R ω)).IsConformal := fun ω => isConformal_cfChart (R ω)
  have hliftc : ∀ ω, ContinuousOn (cfChart (R ω)).2.2 (cfChart (R ω)).dom := fun ω =>
    continuousOn_lift_cfChart (R ω)
  have hU := Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation hhn hc hliftc
    (fun ω => (hWc ω).continuousOn) (fun i ω => (isForcePath_geomLW hWc xL ω i).1.continuousOn)
    (fun j ω => (isForcePath_geomRW hWc xR ω j).1.continuousOn)
    (fun ω t _ => ⟨fun i => geomLW_le hWc xL ω t i, fun j => le_geomRW hWc xR ω t j⟩) hcf
  have hR0 : Measurable[usualAugmentation 𝓐 P 0] R :=
    (Measurable.of_comap_le h𝒢).mono (Ito.le_usualAugmentation 𝓐 P 0) le_rfl
  have hRm : Measurable R := (Measurable.of_comap_le h𝒢).mono (𝓐.le 0) le_rfl
  have hX : Measurable fun ω => imgField κ (R ω) (h ω) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => imgField κ p.1 p.2)
      (f := fun ω => (R ω, h ω)) (measurable_imgField κ) (hRm.prodMk hh)
  have hC := Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hc
    (fun z => hR0 (measurableSet_mem_dom_cfChart z)) (fun z => (measurable_indicator_fwd_cfChart z).comp hR0)
    (fun z => (measurable_indicator_lift_cfChart z).comp hR0) hliftc hhn
    (ae_of_all _ fun ω => ⟨hW0 ω, (hWc ω).continuousOn⟩) hU
    (fun ω => isChartTransport_cfChart_imgField hκ (R ω) (h ω))
  refine Mean.hasSafeLaw_of_ae_condExp hX (fun _ q => usualAugmentation 𝓐 P q)
    (fun _ q => Ito.le_usualAugmentation 𝓐 P q) (fun _ q => (usualAugmentation 𝓐 P).le q) ?_
  intro ψ q D _ hDa
  have hτ := isStoppingTime_const (usualAugmentation 𝓐 P) q
  have h1 := hC (fun _ => (q : WithTop ℝ≥0)) hτ (ae_of_all _ fun _ => ENNReal.coe_lt_top)
    (fun ω => bheProc (16 / κ) ρL ρR W (geomLW W xL) (geomRW W xR) ω q)
    (fun ω => isBoundedHarmonicExtension_bheProc ω q) ψ
  rw [IsStoppingTime.measurableSpace_const] at h1
  filter_upwards [h1, hDa] with ω h1ω hDω hωD
  obtain ⟨-, -, hdis⟩ := hDω hωD
  rw [h1ω hdis]
  simp only [Coupling.cfAt, WithTop.untopD_coe]
  congr 1
  push_cast
  ring

end Safe

/-! ### (L) from the locality of the physical union -/

/-- **The lift of the image chart is harmonic on its domain** (`−2 arg` composed with the record chart's forward map,
plus the record chart's harmonic lift). -/
theorem harmonicOnNhd_lift_cfChart (r : RecData) :
    InnerProductSpace.HarmonicOnNhd (cfChart r).2.2 (cfChart r).dom := by
  set y := recHist r
  have hw : Continuous (Ito.rpath (LocalExt.histDrv y)) :=
    (LocalExt.continuous_histDrv y).comp continuous_real_toNNReal
  have hw0 : Ito.rpath (LocalExt.histDrv y) 0 = 0 := by
    simp only [Ito.rpath, Real.toNNReal_zero, LocalExt.histDrv_zero]
  have hs : (0 : ℝ) ≤ (LocalExt.histTime y : ℝ) := (LocalExt.histTime y).coe_nonneg
  have hdom : ((recChart r).dom : Set ℂ) = H \ fwdHull (Ito.rpath (LocalExt.histDrv y)) (LocalExt.histTime y) := by
    rw [(isConformal_recChart r).coe_dom]
    exact QuantumZipper.RS.image_fwdMapInv_H hw hw0 hs
  have hd : ((cfChart r).dom : Set ℂ) = (recChart r).dom := coe_dom_cfChart r
  have hf : DifferentiableOn ℂ (recChart r).1 (recChart r).dom := by
    rw [show ((recChart r).dom : Set ℂ) = _ from hdom]
    exact QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs
  have h1 : InnerProductSpace.HarmonicOnNhd (infinitySourceChart.2.2 ∘ (recChart r).1) (recChart r).dom :=
    LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H (recChart r).dom.isOpen
      Sec7.StripSysField.harmonicOnNhd_infinitySourceChart_lift hf (continuousOn_fst_recChart r).2
  have h2 : InnerProductSpace.HarmonicOnNhd (recChart r).2.2 (recChart r).dom :=
    LocalExt.harmonicOnNhd_lift_histChart y
  intro z hz
  have hz' : z ∈ (recChart r).dom := by rw [← SetLike.mem_coe, ← hd]; exact hz
  exact (h1 z hz').add (h2 z hz')

/-- **The image field is the canonical transport of `−f` through the image chart.** -/
theorem imgField_eq_chartTransport {κ : ℝ} (hκ : 0 < κ) (r : RecData) (f : DistOn upperHalfPlaneOpens) :
    imgField κ r f = Chart.chartTransport (isConformal_cfChart r) 1 (-(π * chiC κ)) (-chiC κ) (-f) :=
  (isChartTransport_cfChart_imgField hκ r f).eq_chartTransport (isConformal_cfChart r)
    (Chart.locallyIntegrableOn_of_continuousOn (continuousOn_lift_inv_cfChart r))

section Members

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}

/-- **K2's (L) for the image field from the history-marked locality of the physical union.** With `𝓗 ⊇ σ(R)`,
marks `ℋ_s ⊇ 𝓗_s`, the physical union `B_s` (relatively closed, hitting-measurable) history-marked local for the
centred field `−h − u₀` given `ℋ_s`, and `ℍ ∖ B_s` the image under the inverse image chart of `ℍ ∖ K̃_s`
(`K̃_s` the hull of the image driver `W`), the image field `imgField κ R h` satisfies (L) with lifetime `⊤`. -/
theorem hasSafeMembers_imgField_of_loc (hκ : 0 < κ) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {R : Ω → RecData} {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : MeasurableSpace.comap R inferInstance ≤ 𝓗 0)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField (fun ω => -h ω) u₀) P)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓗ℋ : ∀ s, 𝓗 s ≤ ℋ s) (hℋ : ∀ s, ℋ s ≤ mΩ) (B : ℝ≥0 → Ω → Set ℂ)
    (hBm : ∀ s, Measurable[mΩ, hittingSigma] (B s)) (hBc : ∀ s ω, B s ω ⊆ H ∧ IsOpen (H \ B s ω))
    (hloc : ∀ s, WholeField.IsHistoryAvoidanceLocal (ℋ s) (B s) (WholeField.centredField (fun ω => -h ω) u₀) P)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hBK : ∀ s : ℝ≥0, ∀ᵐ ω ∂P,
      H \ B s ω = (cfChart (R ω)).2.1 '' (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) s)) :
    HasSafeMembers P 𝓗 univ (fun _ => ⊤) W (fun ω => imgField κ (R ω) (h ω)) := by
  have hhn : Measurable fun ω => -h ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ => ((LQGMetric.measurable_distOn_apply φ).comp hh).neg
  have hR : Measurable[MeasurableSpace.comap R inferInstance] R := Measurable.of_comap_le le_rfl
  have e : (fun ω => imgField κ (R ω) (h ω)) =
      fun ω => Chart.chartTransport (isConformal_cfChart (R ω)) 1 (-(π * chiC κ)) (-chiC κ) (-h ω) :=
    funext fun ω => imgField_eq_chartTransport hκ (R ω) (h ω)
  rw [e]
  exact Mean.hasSafeMembers_chartTransport (𝒢 := MeasurableSpace.comap R inferInstance) h𝒢 hhn hu₀ hh0
    (fun ω => isConformal_cfChart (R ω)) (fun z => hR (measurableSet_mem_dom_cfChart z))
    (fun z => (measurable_indicator_fwd_cfChart z).comp hR) (fun z => (measurable_indicator_lift_cfChart z).comp hR)
    (fun ω => continuousOn_lift_cfChart (R ω)) (fun ω => harmonicOnNhd_lift_cfChart (R ω)) _ _ ℋ h𝓗ℋ hℋ B hBm hBc
    hloc (fun s => (hBK s).mono fun ω h _ _ => h) (ae_of_all _ fun ω _ => ⟨(hWc ω).continuousOn, hW0 ω⟩)

end Members

end InteractingSLE.Sec5.CfGiven
