/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIProofMean
import InteractingSLE.Spec.Restart.StoppedK2Kernel
import InteractingSLE.Spec.Restart.FlowStopIdentCMIStmt

/-!
# Lemma G3's Cameron–Martin identification at a stop (step (b))

Packet PROVE-L1-CMI (continuation). At a stopping time `τ` of the driving filtration of the `b`-coupling of a flow line
`Γ` of `H₀`, before the lifetime, whose hull closure lies in the chart buffer, the tilted measure
`Q* = k e^{−Λ} · Q₀` gives the shifted chart field `h' + T_y` the **reference (`bR`) word's kernel**: the tilt of the
frozen kernel (`FlowStopIdentCM.ae_condExp_withDensity_add_of_coupling`) with the chart tests `s_n(· + y)`, its
hypotheses (b) verified here, and the mean identity (c) (`integral_couplingMean_shift_eq`, `…_zero`).

* `CMCut.src_shift`, `CMCut.tsupport_greenDensity_shift`: the source in the chart;
* `exists_bound_couplingMean_src`: the coupling mean is bounded on the source's support (`GB7a.exists_far`);
* **`ae_condExp_shift_eq_ref`**: the reference kernel under `Q*` at the stop.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol greenH)

/-! ### The source in the chart -/

namespace CMCut

variable (F : CMCut)

theorem src_shift (y : ℝ) (z : ℂ) : (F.shift y).src z = F.src (z + y) := by
  by_cases hz : z ∈ H
  · rw [src_of_mem _ hz, src_of_mem _ (Exist.add_real_mem_H hz y), greenDensity_shift]
  · have hz' : z + (y : ℂ) ∉ H := fun h => hz (by
      have := Exist.add_real_mem_H h (-y)
      simpa using this)
    rw [src_of_notMem _ hz, src_of_notMem _ hz']

end CMCut

/-! ### A bound of the coupling mean on the source -/

/-- **The coupling mean is bounded on the support of a source that vanishes on a buffer containing the hull
closure**: the points of `tsupport (gD F.f) ∩ ℍ̄` are alive through `t` and uniformly far from the driver
(`GB7a.exists_far`), so `|Im log f_t'| ≤ 2t/m²` there. -/
theorem exists_bound_couplingMean_src (κ : ℝ) (F : CMCut) {N : Set ℂ} (hNo : IsOpen N) (h0N : (0 : ℂ) ∈ N)
    (hΔN : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) (hKN : closure (fwdHull w t) ⊆ N) {u : ℂ → ℝ} {Cu : ℝ} (hCu : ∀ z ∈ H, |u z| ≤ Cu) :
    ∃ C, ∀ z, F.src z ≠ 0 → |couplingMean κ w t u z| ≤ C := by
  have hvs : HasCompactSupport (QuantumZipper.K3.greenDensity F.f) := F.hasCompactSupport_greenDensity
  have htsupN : Disjoint (tsupport (QuantumZipper.K3.greenDensity F.f)) N := by
    rw [Set.disjoint_right]
    intro z hzN hzt
    have hev : QuantumZipper.K3.greenDensity F.f =ᶠ[𝓝 z] 0 := by
      filter_upwards [hNo.mem_nhds hzN] with v hv
      rw [hΔN v hv, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.2 hev) hzt
  have halive : ∀ z ∈ tsupport (QuantumZipper.K3.greenDensity F.f) ∩ Hbar, ∃ v, IsForwardSol w z t v := by
    rintro z ⟨hzt, hzH⟩
    have hzN : z ∉ N := Set.disjoint_left.1 htsupN hzt
    rcases (show (0 : ℝ) ≤ z.im from hzH).lt_or_eq with hpos | hzero
    · exact Ito.exists_isForwardSol_of_mem ht ⟨hpos, fun hK => hzN (hKN (subset_closure hK))⟩
    · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have hz0 : z.re ≠ 0 := fun h => hzN (by rw [hzr, h, Complex.ofReal_zero]; exact h0N)
      have hzcl : z ∉ closure (fwdHull w t) := fun h => hzN (hKN h)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hzcl
      have hd : Disjoint (ball ((z.re : ℝ) : ℂ) r) (fwdHull w t) := by
        rw [← hzr]
        exact Set.disjoint_left.2 fun v hv hvK => hball hv (subset_closure hvK)
      obtain ⟨v, hv⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hw hw0 hz0 ht hr hd
      exact ⟨v, by rw [hzr]; exact hv⟩
  obtain ⟨m, hm, hmfar⟩ := GB7a.exists_far hw ht ((hvs.isCompact).inter_right
    (isClosed_le continuous_const Complex.continuous_im)) halive
  refine ⟨Cu + |QuantumZipper.chiC κ| * (2 / m ^ 2 * t), fun z hz => ?_⟩
  obtain ⟨hzH, hzt⟩ := F.mem_of_src_ne_zero hz
  have hzK : z ∈ tsupport (QuantumZipper.K3.greenDensity F.f) ∩ Hbar :=
    ⟨hzt, show (0 : ℝ) ≤ z.im from le_of_lt hzH⟩
  have hzN : z ∉ N := Set.disjoint_left.1 htsupN hzt
  have hzalive : z ∈ H \ fwdHull w t := ⟨hzH, fun hK => hzN (hKN (subset_closure hK))⟩
  have hfH : fwdMap w t z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht hzalive
  have hlog : ‖QuantumZipper.logDerivFwd w t z‖ ≤ 2 / m ^ 2 * t := by
    rw [QuantumZipper.logDerivFwd, norm_neg]
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
      (C := 2 / m ^ 2) (f := fun s => 2 / fwdMap w s z ^ 2) fun s hs => by
        rw [uIoc_of_le ht] at hs
        have hn := hmfar z hzK s ⟨hs.1.le, hs.2⟩
        rw [norm_div, norm_pow, Complex.norm_two]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hm.le hn 2)
    rwa [sub_zero, abs_of_nonneg ht] at h1
  rw [couplingMean]
  refine (abs_sub _ _).trans (add_le_add (hCu _ hfH) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hlog) (abs_nonneg _)

/-! ### Chart tests -/

/-- A test function read in the chart of the seed `y`: `z ↦ φ(z + y)`. -/
def chartTest (y : ℝ) (φ : LQGMetric.TestOn upperHalfPlaneOpens) : LQGMetric.TestOn upperHalfPlaneOpens :=
  Chart.pushTest (Exist.isConformal_shiftChart (-y)) φ

theorem chartTest_apply (y : ℝ) (φ : LQGMetric.TestOn upperHalfPlaneOpens) (z : ℂ) :
    chartTest y φ z = φ (z + y) := by
  rw [chartTest, Exist.pushTest_shiftChart_apply]
  congr 1
  push_cast
  ring

/-- A set where a function vanishes near every point is disjoint from its support. -/
theorem disjoint_tsupport_of_eq_zero {g : ℂ → ℝ} {N : Set ℂ} (hNo : IsOpen N) (hN : ∀ z ∈ N, g z = 0) :
    Disjoint (tsupport g) N := by
  rw [Set.disjoint_right]
  intro z hzN hzt
  have hev : g =ᶠ[𝓝 z] 0 := by
    filter_upwards [hNo.mem_nhds hzN] with v hv
    rw [hN v hv, Pi.zero_apply]
  exact (notMem_tsupport_iff_eventuallyEq.2 hev) hzt

/-! ### The tilt's hypotheses along one path (step (b)) -/

/-- **The hypotheses of the tilt along one path.** For a driver path `w₀'` agreeing on `[0, t₂]` (`t < t₂`) with a
continuous `w₁'` (`w₁' 0 = 0`) whose hull at `t` has closure in the chart buffer `N − y`, the chart tests
`s'_n = s_n(· + y)` avoid the hull, and the mean, energy and cross-energy pairings of `s'_n` converge to those of
the chart source `F_y.src`. -/
theorem chart_tilt_inputs (κ : ℝ) {F : CMCut} {N : Set ℂ} (hNo : IsOpen N)
    (hFΔ : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) {y : ℝ} (hyN : (y : ℂ) ∈ N)
    {s : ℕ → LQGMetric.TestOn upperHalfPlaneOpens} (hsle : ∀ n z, |s n z| ≤ |F.src z|)
    (hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) {w₀' w₁' : ℝ≥0 → ℝ} (hw₁ : Continuous w₁')
    (hw₁0 : w₁' 0 = 0) {t : ℝ≥0} {t₂ : ℝ} (htt₂ : (t : ℝ) < t₂)
    (hag : ∀ r ∈ Icc (0 : ℝ) t₂, Ito.rpath w₁' r = Ito.rpath w₀' r)
    (hKN : closure (fwdHull (Ito.rpath w₁') t) ⊆ (fun z => z + y) ⁻¹' N) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) {Cu : ℝ} (hCu : ∀ z ∈ H, |u z| ≤ Cu) :
    (∀ n, Disjoint (tsupport (chartTest y (s n))) (fwdHull (Ito.rpath w₀') t)) ∧
    Tendsto (fun n => ∫ z, couplingMean κ (Ito.rpath w₀') t u z * chartTest y (s n) z) atTop
      (𝓝 (∫ z, couplingMean κ (Ito.rpath w₀') t u z * (F.shift y).src z)) ∧
    Tendsto (fun n => loewnerGreenEnergy (Ito.rpath w₀') t (chartTest y (s n))) atTop
      (𝓝 (loewnerGreenEnergy (Ito.rpath w₀') t (F.shift y).src)) ∧
    ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, Disjoint (tsupport φ) (fwdHull (Ito.rpath w₀') t) →
      Tendsto (fun n => LocalExt.greenCross (Ito.rpath w₀') t φ (chartTest y (s n))) atTop
        (𝓝 (LocalExt.greenCross (Ito.rpath w₀') t φ (F.shift y).src)) := by
  set w₁ : ℝ → ℝ := Ito.rpath w₁' with hw₁def
  set w₀ : ℝ → ℝ := Ito.rpath w₀' with hw₀def
  have hw₁c : Continuous w₁ := hw₁.comp continuous_real_toNNReal
  have hw₁00 : w₁ 0 = 0 := by simp [hw₁def, Ito.rpath, hw₁0]
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hK : fwdHull w₀ t = fwdHull w₁ t :=
    (fwdHull_eq_of_eqOn ht0 htt₂ fun r hr => hag r hr).symm
  have hw₀c : ContinuousOn w₀ (Icc 0 t₂) := hw₁c.continuousOn.congr fun r hr => (hag r hr).symm
  set N' : Set ℂ := (fun z => z + y) ⁻¹' N with hN'
  have hN'o : IsOpen N' := hNo.preimage (continuous_id.add continuous_const)
  have h0N' : (0 : ℂ) ∈ N' := by simp only [hN', mem_preimage, zero_add]; exact hyN
  have hΔN' : ∀ z ∈ N', QuantumZipper.K3.greenDensity (F.shift y).f z = 0 := fun z hz => by
    rw [CMCut.greenDensity_shift]; exact hFΔ _ hz
  have hdisN' := disjoint_tsupport_of_eq_zero hN'o hΔN'
  -- chart tests are dominated by the chart source
  have hs'le : ∀ n z, |chartTest y (s n) z| ≤ |(F.shift y).src z| := fun n z => by
    rw [chartTest_apply, CMCut.src_shift]; exact hsle n _
  have hs'lim : ∀ z, Tendsto (fun n => chartTest y (s n) z) atTop (𝓝 ((F.shift y).src z)) := fun z => by
    simp only [chartTest_apply, CMCut.src_shift]; exact hslim _
  -- the hull lies in the buffer
  have hKN' : fwdHull w₀ t ⊆ N' := fun z hz => hKN (subset_closure (hK ▸ hz))
  -- (i) the chart tests avoid the hull
  have hsd : ∀ n, Disjoint (tsupport (chartTest y (s n))) (fwdHull w₀ t) := fun n => by
    refine Set.disjoint_of_subset_right hKN' ?_
    rw [Set.disjoint_left]
    intro z hzt hzN
    have hsub : tsupport (chartTest y (s n)) ⊆ tsupport (QuantumZipper.K3.greenDensity (F.shift y).f) := by
      refine closure_minimal (fun v hv => ?_) (isClosed_tsupport _)
      have h1 : (F.shift y).src v ≠ 0 := fun h0 => hv (by
        have := hs'le n v
        rw [h0, abs_zero] at this
        exact abs_nonpos_iff.1 this)
      exact ((F.shift y).mem_of_src_ne_zero h1).2
    exact Set.disjoint_left.1 hdisN' (hsub hzt) hzN
  have hdsrc : Disjoint (tsupport (QuantumZipper.K3.greenDensity (F.shift y).f)) (fwdHull w₀ t) :=
    Set.disjoint_of_subset_right hKN' hdisN'
  -- Green tests
  have hgS := (F.shift y).isGreenTest_src hdsrc
  have hgs : ∀ n, LocalExt.IsGreenTest w₀ t (chartTest y (s n)) := fun n =>
    LocalExt.isGreenTest_of_testOn _ (hsd n)
  have hgc := fun (φ : LQGMetric.TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull w₀ t)) =>
    FlowStopIdentCM.tendsto_greenCross_of_dominated ht0 htt₂ hw₀c (LocalExt.isGreenTest_of_testOn φ hφ) hgS hgs
      hgS hs'le hs'lim
  refine ⟨hsd, ?_, (hgc _ (hsd 0)).2, fun φ hφ => (hgc φ hφ).1⟩
  -- (ii) the means, by dominated convergence
  have hKN1 : closure (fwdHull w₁ t) ⊆ N' := hKN
  obtain ⟨C, hC⟩ := exists_bound_couplingMean_src κ (F.shift y) hN'o h0N' hΔN' hw₁c hw₁00 ht0 hKN1 hCu
  have hcongr : ∀ z, couplingMean κ w₀ t u z = couplingMean κ w₁ t u z := fun z =>
    StoppedK2.couplingMean_congr_Icc ht0 (fun r hr => (hag r ⟨hr.1, hr.2.trans htt₂.le⟩).symm) κ u z
  have hw₀ct : ContinuousOn (Ito.rpath w₀') (Icc 0 ((t : ℝ≥0) : ℝ)) := hw₀c.mono (Icc_subset_Icc le_rfl htt₂.le)
  refine tendsto_integral_of_dominated_convergence (fun z => C * |(F.shift y).src z|)
    (fun n => (LocalExt.integrable_couplingMean_mul (κ := κ) hw₀ct hu (hsd n)).aestronglyMeasurable)
    ((F.shift y).integrable_src.abs.const_mul C) (fun n => ae_of_all _ fun z => ?_)
    (ae_of_all _ fun z => (hs'lim z).const_mul _)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hz : (F.shift y).src z = 0
  · have h0 := hs'le n z
    rw [hz, abs_zero] at h0
    rw [abs_nonpos_iff.1 h0, hz, abs_zero, mul_zero, mul_zero]
  · rw [hcongr z]
    exact mul_le_mul (hC z hz) (hs'le n z) (abs_nonneg _) ((abs_nonneg _).trans (hC z hz))

/-! ### The reference kernel under the tilted measure at a stop -/

section Stop

variable {κ : ℝ} {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {O : Set ℝ} [DecidablePred (· ∈ O)]
  {S : Type*} [MeasurableSpace S] {Q₀ : Measure S} [IsProbabilityMeasure Q₀]

/-- **Lemma G3's Cameron–Martin identification at a stop.** Let `h'` be the chart field of the `b`-flow line from `y`
(an optional hull coupling with `(W₀, V^L₀, V^R₀, B₀, U)`), `τ < U` a stopping time of its driving filtration, and
`W₁` a continuous driver agreeing with `W₀` on `[0, t₂]` for some `t₂ > τ`, at whose geometric images the `b`-marks sit
at `τ`, whose hull at `τ` has closure in the chart buffer, and which is generated by a trace up to `τ` (when `τ > 0`).
Then, under `Q* = k e^{−Λ} · Q₀`, the shifted chart field `h' + T_y` has, given the stopped σ-algebra, the kernel of the
**reference word** at the geometric images of `W₁`. -/
theorem ae_condExp_shift_eq_ref (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {y : ℝ} (hy : y ∈ O)
    (θ : ℝ) {F : CMCut} {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q) {N : Set ℂ}
    (hNo : IsOpen N) (hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O) (hFq : ∀ z ∈ N, z ∈ H → F.f z = q z)
    (hFΔ : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) (hyN : (y : ℂ) ∈ N)
    {H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens} {s : ℕ → LQGMetric.TestOn upperHalfPlaneOpens}
    (hsle : ∀ n z, |s n z| ≤ |F.src z|) (hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z)))
    {Λ : S → ℝ} (hΛm : Measurable Λ) (hΛ : ∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))) {k : ℝ}
    (hk : 0 < k) (hprob : IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))))
    {h' : S → LQGMetric.DistOn upperHalfPlaneOpens}
    (htr : ∀ x, IsTranslateAddConst y (θ * QuantumZipper.chiC κ) (H₀ x) (h' x))
    {𝓕₀ : Filtration ℝ≥0 ‹MeasurableSpace S›} {W₀ : ℝ≥0 → S → ℝ}
    {VL₀ : Fin (flowLineNL b J y) → ℝ≥0 → S → ℝ} {VR₀ : Fin (flowLineNR b J y) → ℝ≥0 → S → ℝ}
    {B₀ : ℝ≥0 → S → ℝ} {U : S → ℝ≥0∞}
    (hC : IsOptionalHullCoupling κ (flowLineXL b J y) (flowLineXR b J y) (flowLineRhoL κ b J y θ)
      (flowLineRhoR κ b J y θ) Q₀ 𝓕₀ W₀ VL₀ VR₀ B₀ U h')
    (hX : IsMeasurableKilledDriving W₀ VL₀ VR₀ U) {τ : S → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration Q₀ hX) τ) (hτU : ∀ᵐ ω ∂Q₀, (τ ω : ℝ≥0∞) < U ω)
    {W₁ : ℝ≥0 → S → ℝ}
    (hpath : ∀ᵐ ω ∂Q₀, Continuous (W₁ · ω) ∧ W₁ 0 ω = 0 ∧
      (∃ t₂ : ℝ, (((τ ω).untopD 0 : ℝ≥0) : ℝ) < t₂ ∧
        ∀ r ∈ Icc (0 : ℝ) t₂, Ito.rpath (W₁ · ω) r = Ito.rpath (W₀ · ω) r) ∧
      (∀ i, VL₀ i ((τ ω).untopD 0) ω - W₀ ((τ ω).untopD 0) ω =
        geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL b J y i)) ∧
      (∀ j, VR₀ j ((τ ω).untopD 0) ω - W₀ ((τ ω).untopD 0) ω =
        geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR b J y j)) ∧
      closure (fwdHull (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)) ⊆ (fun z => z + y) ⁻¹' N ∧
      (0 < (τ ω).untopD 0 → ∃ η : ℝ → ℂ, ContinuousOn η (Icc 0 (((τ ω).untopD 0 : ℝ≥0) : ℝ)) ∧
        ∀ r ∈ Ioc (0 : ℝ) (((τ ω).untopD 0 : ℝ≥0) : ℝ), fwdHull (Ito.rpath (W₁ · ω)) r = fillH (η '' Icc 0 r)))
    {uR : S → ℂ → ℝ}
    (huR : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
        (fun i => geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL bR Ĵ y i))
        (fun j => geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR bR Ĵ y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL bR Ĵ y i))
        (fun j => geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR bR Ĵ y j))) (uR ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂(Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))),
      Disjoint (tsupport φ) (fwdHull (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)) →
      (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)))[fun ω' =>
          Complex.exp (Complex.I * ((h' ω' + chartShift F q y) φ : ℂ)) | hτ.measurableSpace] ω =
        LocalExt.cfVal (∫ z, couplingMean κ (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (uR ω) z * φ z)
          (loewnerGreenEnergy (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) φ) := by
  classical
  set Q := Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)) with hQ
  set c : ℝ := θ * QuantumZipper.chiC κ with hc
  set s' : ℕ → LQGMetric.TestOn upperHalfPlaneOpens := fun n => chartTest y (s n) with hs'
  set I₀ : ℝ := ∫ z, F.src z with hI₀
  set Λ' : S → ℝ := fun x => Λ x + c * I₀ with hΛ'def
  set k' : ℝ := k * Real.exp (c * I₀) with hk'def
  -- the chart pairing
  have hints : ∀ n, ∫ z, s' n z = ∫ z, s n z := fun n => by
    simp only [hs', chartTest_apply]
    exact integral_add_right_eq_self (fun z => s n z) (y : ℂ)
  have hI : Tendsto (fun n => ∫ z, s n z) atTop (𝓝 I₀) :=
    tendsto_integral_of_dominated_convergence (fun z => |F.src z|) (fun n => (s n).continuous.aestronglyMeasurable)
      F.integrable_src.abs (fun n => ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hsle n z)
      (ae_of_all _ hslim)
  have hΛ' : ∀ᵐ x ∂Q₀, Tendsto (fun n => h' x (s' n)) atTop (𝓝 (Λ' x)) := by
    filter_upwards [hΛ] with x hx
    have e : ∀ n, h' x (s' n) = H₀ x (s n) + c * ∫ z, s' n z := fun n =>
      htr x (s n) (s' n) fun z => chartTest_apply y (s n) z
    simp only [e, hints]
    exact hx.add (hI.const_mul c)
  have hΛ'm : Measurable Λ' := hΛm.add_const _
  have hk' : 0 < k' := mul_pos hk (Real.exp_pos _)
  have hdens : (fun x => ENNReal.ofReal (k' * Real.exp (-Λ' x))) = fun x => ENNReal.ofReal (k * Real.exp (-Λ x)) := by
    funext x
    congr 1
    simp only [hk'def, hΛ'def, neg_add, Real.exp_add]
    rw [show k * Real.exp (c * I₀) * (Real.exp (-Λ x) * Real.exp (-(c * I₀))) =
      k * Real.exp (-Λ x) * (Real.exp (c * I₀) * Real.exp (-(c * I₀))) by ring, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, mul_one]
  have hint' : Integrable (fun x => Real.exp (-Λ' x)) Q₀ := by
    refine ((integrable_exp_neg_of_prob hΛm hk hprob).const_mul (Real.exp (-(c * I₀)))).congr
      (ae_of_all _ fun x => ?_)
    simp only [hΛ'def, neg_add, Real.exp_add]; ring
  -- the `b`-family of extensions
  set τ' : S → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'
  set ub : S → ℂ → ℝ := fun ω => MartChar.meanExt κ (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
    (W₀ (τ' ω) ω) (fun i => VL₀ i (τ' ω) ω) (fun j => VR₀ j (τ' ω) ω) with hub
  have hubH : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
        (fun i => VL₀ i ((τ ω).untopD 0) ω - W₀ ((τ ω).untopD 0) ω)
        (fun j => VR₀ j ((τ ω).untopD 0) ω - W₀ ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL₀ i ((τ ω).untopD 0) ω - W₀ ((τ ω).untopD 0) ω)
        (fun j => VR₀ j ((τ ω).untopD 0) ω - W₀ ((τ ω).untopD 0) ω)) (ub ω) := fun ω =>
    MartChar.isBoundedHarmonicExtension_meanExt κ _ _ _ _ _
  -- the tilt's hypotheses, pathwise
  have hin : ∀ᵐ ω ∂Q₀, (∀ n, Disjoint (tsupport (s' n))
        (fwdHull (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))) ∧
      Tendsto (fun n => ∫ z, couplingMean κ (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (ub ω) z *
        s' n z) atTop (𝓝 (∫ z, couplingMean κ (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (ub ω) z *
          (F.shift y).src z)) ∧
      Tendsto (fun n => loewnerGreenEnergy (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (s' n)) atTop
        (𝓝 (loewnerGreenEnergy (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (F.shift y).src)) ∧
      ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens,
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
        Tendsto (fun n => LocalExt.greenCross (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) ψ (s' n))
          atTop (𝓝 (LocalExt.greenCross (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) ψ
            (F.shift y).src)) := by
    filter_upwards [hpath] with ω hp
    obtain ⟨hc1, hc0, ⟨t₂, ht₂, hag⟩, -, -, hKN, -⟩ := hp
    obtain ⟨Cu, hCu⟩ := (hubH ω).2.1
    exact chart_tilt_inputs κ hNo hFΔ hyN hsle hslim hc1 hc0 ht₂ hag hKN (hubH ω).1 hCu
  have htilt := FlowStopIdentCM.ae_condExp_withDensity_add_of_coupling hC hX hτ hτU hubH hΛ'm hΛ' hint'
    (hin.mono fun ω h => h.1) (hin.mono fun ω h => h.2.1) (hin.mono fun ω h => h.2.2.1) hk' (chartShift F q y) φ
    (hin.mono fun ω h hφ => h.2.2.2 φ hφ)
  rw [hdens] at htilt
  -- the mean identity
  filter_upwards [htilt, (withDensity_absolutelyContinuous _ _).ae_le hpath] with ω h1 hp hφ
  obtain ⟨hc1, hc0, ⟨t₂, ht₂, hag⟩, hL, hR, hKN, hη⟩ := hp
  have ht0 : (0 : ℝ) ≤ (τ' ω : ℝ) := (τ' ω).coe_nonneg
  have hK : fwdHull (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) =
      fwdHull (Ito.rpath (W₁ · ω)) ((τ ω).untopD 0 : ℝ≥0) :=
    fwdHull_eq_of_eqOn ht0 ht₂ fun r hr => (hag r hr).symm
  have hagt : EqOn (Ito.rpath (W₁ · ω)) (fun r : ℝ => W₀ r.toNNReal ω) (Icc 0 (τ' ω : ℝ)) := fun r hr =>
    hag r ⟨hr.1, hr.2.trans ht₂.le⟩
  have hφ0 : Disjoint (tsupport φ) (fwdHull (fun r : ℝ => W₀ r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
    rw [hK]; exact hφ
  rw [h1 hφ0]
  -- transport to the continuous driver `W₁`
  have hmean : ∀ u : ℂ → ℝ, ∫ z, couplingMean κ (fun r : ℝ => W₀ r.toNNReal ω) (τ' ω) u z * φ z =
      ∫ z, couplingMean κ (Ito.rpath (W₁ · ω)) (τ' ω) u z * φ z := fun u => by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [StoppedK2.couplingMean_congr_Icc ht0 hagt κ u z]
  have hfwd : fwdMap (fun r : ℝ => W₀ r.toNNReal ω) (τ' ω) = fwdMap (Ito.rpath (W₁ · ω)) (τ' ω) := by
    funext z
    exact fwdMap_eq_of_eqOn ht0 fun r hr => (hagt hr).symm
  have hE : loewnerGreenEnergy (fun r : ℝ => W₀ r.toNNReal ω) (τ' ω) φ =
      loewnerGreenEnergy (Ito.rpath (W₁ · ω)) (τ' ω) φ :=
    (StoppedK2.loewnerGreenEnergy_congr_Icc hagt φ).symm
  rw [hmean, LocalExt.greenCross_congr hfwd, hE]
  congr 1
  -- the `b`-extension at the geometric images
  have hpos_b : (fun i => VL₀ i (τ' ω) ω - W₀ (τ' ω) ω) =
      fun i => geomL (Ito.rpath (W₁ · ω)) (τ' ω) (flowLineXL b J y i) := funext hL
  have hpos_bR : (fun j => VR₀ j (τ' ω) ω - W₀ (τ' ω) ω) =
      fun j => geomR (Ito.rpath (W₁ · ω)) (τ' ω) (flowLineXR b J y j) := funext hR
  have hub' := hubH ω
  rw [hpos_b, hpos_bR] at hub'
  rcases eq_zero_or_pos (τ' ω) with h0 | hpos
  · have huR' := huR ω
    rw [show (τ ω).untopD 0 = (0 : ℝ≥0) from h0, NNReal.coe_zero] at huR'
    rw [h0, NNReal.coe_zero] at hub' ⊢
    rw [show (τ ω).untopD 0 = (0 : ℝ≥0) from h0, NNReal.coe_zero]
    exact integral_couplingMean_shift_eq_zero hκ hb hbR hO hbO hy θ F hq hc1 hc0 huR' hub' φ
  · obtain ⟨η, hηc, hfill⟩ := hη hpos
    exact integral_couplingMean_shift_eq hκ hb hbR hO hbO hy θ hq hNo hNO hFq hFΔ hyN hc1 hc0 hpos hηc hfill hKN
      (huR ω) hub' φ hφ


end Stop

end FlowStopIdentCMI

end Restart

end InteractingSLE
