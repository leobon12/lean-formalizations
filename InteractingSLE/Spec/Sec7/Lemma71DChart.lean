/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71DUsual
import InteractingSLE.Spec.Coupling.MartMeans2Chart
import InteractingSLE.Spec.Coupling.Assembly11Path
import InteractingSLE.Spec.Sec4.Special3Thin

/-!
# The chart coupling clause at every stopping time of the usual augmentation, from fixed times

Packet PROVE-LEMMA71D, item (2) for the chart form of the coupling clause (PROVE-LEMMA71C, "What remains" B). The
named input of Lemma 7.1 (`Lemma71C.Lemma71PocketCurveStatement`) asks for `MartMeans2.IsChartCouplingCharFun` in a
right-continuous filtration, at every stopping time. The source (p. 224–225) obtains the conditional law of the field
"for each bounded stopping time of this mapped path" from Lemma 6.2's history locality (which, by ruling R37, is
available at path-functional times) and states "Their time continuity is Proposition 6.5". This file proves that the
clause at **fixed times** of a raw filtration `𝓐` (`IsChartCouplingCharFunConst`, killed at the lifetime) implies
the clause at **every stopping time** of `usualAugmentation 𝓐 P` (`isChartCouplingCharFun_usualAugmentation`).

The time continuity used is pathwise and elementary: along times `sᵢ ↓ t` (`t < ζ`, `supp φ ⊆ inv(ℍ ∖ K_t)`):

* the complements `ℍ ∖ K_{sᵢ}` increase to `ℍ ∖ K_t` (`iUnion_H_diff_fwdHull`; a point outside `K_t` has swallowing
  time `> t`), so the compact `fwd(supp φ)` lies outside some `K_{sᵢ₀}` (directed open cover) and is safe there
  (`exists_isSafeAt`); hence `supp φ ⊆ inv(ℍ ∖ K_{sᵢ})` eventually;
* the chart mean `∫ (𝔥_s ∘ fwd − a − k lift) φ` is continuous in `s ≤ sᵢ₀` by dominated convergence with the uniform
  bound of the explicit mean `meanCan` on safe sets (PROVE-T11-ASM's `IsSafeAt.abs_meanCan_le`,
  `IsSafeAt.continuousOn_meanCan_time`);
* the chart variance `G_{inv(ℍ ∖ K_{sᵢ})}(φ, φ)` converges by monotone Dirichlet-space approximation
  (`LocalSets.tendsto_zeroGFFTestCov_iUnion`).

The probabilistic step is `ae_condExp_stopping_eq_of_forall_const_complex` (`Lemma71DUsual.lean`).

## Main results

* `chartMean`, `chartVar`, `IsChartAvoid`; `tendsto_chart_of_isChartAvoid` (right-continuity along one path);
* `integral_couplingMean_eq_chartMean`: the clause's mean equals the explicit chart mean, for every bounded harmonic
  extension;
* `IsChartCouplingCharFunConst` (def): the chart clause at fixed times of `𝓐`, killed at `ζ`;
* **`isChartCouplingCharFun_usualAugmentation`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H zeroGFFTestCov fwdHull swallowTime)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Lemma71D

open Ito Coupling

variable {nL nR : ℕ}

/-! ### Hulls along decreasing times -/

section Hull

/-- Along times `sᵢ → t` from above, the complements of the hulls exhaust the complement at `t`. -/
theorem iUnion_H_diff_fwdHull {W : ℝ → ℝ} {t : ℝ≥0} {s : ℕ → ℝ≥0} (hts : ∀ i, t ≤ s i)
    (hlim : Tendsto s atTop (𝓝 t)) (n₀ : ℕ) :
    ⋃ j, (H \ fwdHull W (s (j + n₀) : ℝ)) = H \ fwdHull W (t : ℝ) := by
  ext z
  simp only [mem_iUnion, Set.mem_sdiff]
  constructor
  · rintro ⟨j, hz, hzK⟩
    exact ⟨hz, fun h => hzK (QuantumZipper.CoreArc.fwdHull_mono_coreArc (by exact_mod_cast hts _) h)⟩
  · rintro ⟨hz, hzK⟩
    have hlt : ENNReal.ofReal (t : ℝ) < swallowTime W z := by
      by_contra hc
      exact hzK ⟨hz, not_lt.1 hc⟩
    have hl : Tendsto (fun j => ENNReal.ofReal (s (j + n₀) : ℝ)) atTop (𝓝 (ENNReal.ofReal (t : ℝ))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((NNReal.continuous_coe.tendsto _).comp (hlim.comp (tendsto_add_atTop_nat n₀)))
    obtain ⟨j, hj⟩ := (hl.eventually (gt_mem_nhds hlt)).exists
    exact ⟨j, hz, fun h => absurd h.2 (not_le.2 hj)⟩

/-- A compact set outside the hull at a time `r < ζ` is safe at `r` for some level `δ > 0`. -/
theorem exists_isSafeAt {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    {K : Set ℂ} (hK : IsCompact K) {r : ℝ≥0} (hrζ : (r : ℝ≥0∞) < ζ)
    (hKr : K ⊆ H \ fwdHull (rpath w) r) : ∃ δ > 0, IsSafeAt K δ r r ζ w r := by
  have hwr := continuousOn_rpath hw hrζ
  have hc := continuous_clampDrv r.coe_nonneg hwr
  have halive : ∀ z ∈ K, ∃ u, QuantumZipper.IsForwardSol (rpath w) z r u := fun z hz =>
    QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull r.coe_nonneg (hKr hz).1 (hKr hz).2
  have hKt : K ⊆ H \ fwdHull (clampDrv (rpath w) r) r := fun z hz =>
    mem_diff_fwdHull_clampDrv r.coe_nonneg hwr (hKr hz).1 (halive z hz)
  obtain ⟨δ, hδ, hprot⟩ := exists_isProtected_of_isCompact hc r.coe_nonneg hK hKt
  refine ⟨δ, hδ, hrζ, le_rfl, le_rfl, fun z hz => ⟨halive z hz, ?_⟩⟩
  have := (hprot z hz).2
  rwa [fwdMap_clampDrv_of_le le_rfl] at this

end Hull

/-! ### The chart mean and variance along one path -/

section Path

/-- The chart mean `∫ (𝔥_t ∘ fwd − a − k · lift) φ`, with the explicit mean `meanCan`, along one path. -/
def chartMean (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (c : Chart) (a k : ℝ) (φ : ℂ → ℝ) (t : ℝ≥0) : ℝ :=
  ∫ z, (meanCan κ ρL ρR w vL vR t (c.1 z) - a - k * c.2.2 z) * φ z

/-- The chart variance `G_{inv(ℍ ∖ K_t)}(φ, φ)` along one path. -/
def chartVar (w : ℝ≥0 → ℝ) (c : Chart) (φ : TestOn upperHalfPlaneOpens) (t : ℝ≥0) : ℝ :=
  zeroGFFTestCov (c.2.1 '' (H \ fwdHull (rpath w) (t : ℝ))) φ φ

/-- The validity event of the chart clause at time `t`: alive at `t`, and `supp φ` inside the remaining chart
domain `inv(ℍ ∖ K_t)`. -/
def IsChartAvoid (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (c : Chart) (φ : TestOn upperHalfPlaneOpens) (t : ℝ≥0) : Prop :=
  (t : ℝ≥0∞) < ζ ∧ tsupport φ ⊆ c.2.1 '' (H \ fwdHull (rpath w) (t : ℝ))

variable {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
  {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {c : Chart} {a k : ℝ} {φ : TestOn upperHalfPlaneOpens} {t : ℝ≥0}

/-- The forward chart map sends `supp φ` to a compact set outside the hull, and inverts on it. -/
theorem IsChartAvoid.image (hc : c.IsConformal) (ht : IsChartAvoid w ζ c φ t) :
    IsCompact (c.1 '' tsupport φ) ∧ c.1 '' tsupport φ ⊆ H \ fwdHull (rpath w) (t : ℝ) ∧
      tsupport φ ⊆ c.dom ∧ ContinuousOn c.1 (tsupport φ) ∧ ∀ x ∈ tsupport φ, c.2.1 (c.1 x) = x := by
  have hfx : ∀ x ∈ tsupport φ, c.1 x ∈ H \ fwdHull (rpath w) (t : ℝ) ∧ c.2.1 (c.1 x) = x :=
    fun x hx => by
      obtain ⟨y, hy, rfl⟩ := ht.2 hx
      rw [hc.2.2 y hy.1]
      exact ⟨hy, rfl⟩
  have hdom : tsupport φ ⊆ c.dom := fun x hx => by
    rw [hc.coe_dom]
    exact ⟨c.1 x, (hfx x hx).1.1, (hfx x hx).2⟩
  have hfc : ContinuousOn c.1 (tsupport φ) := hc.differentiableOn_fwd.continuousOn.mono hdom
  refine ⟨φ.hasCompactSupport.isCompact.image_of_continuousOn hfc, ?_, hdom, hfc,
    fun x hx => (hfx x hx).2⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (hfx x hx).1

/-- A function continuous on `supp φ` and vanishing off it is measurable. -/
theorem aestronglyMeasurable_of_continuousOn_tsupport {f : ℂ → ℝ} (hf : ContinuousOn f (tsupport φ))
    (h0 : ∀ z ∉ tsupport φ, f z = 0) : AEStronglyMeasurable f volume := by
  classical
  have e : f = (tsupport φ).piecewise f fun _ => 0 := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · simp [Set.piecewise, hz]
    · simp [Set.piecewise, hz, h0 z hz]
  rw [e]
  exact (hf.measurable_piecewise continuousOn_const (isClosed_tsupport φ).measurableSet).aestronglyMeasurable

/-- **Right-continuity of the chart clause along one path.** If `t < ζ` and `supp φ ⊆ inv(ℍ ∖ K_t)`, then along
every decreasing sequence `sᵢ ↓ t` (strictly above `t`) the clause's validity holds eventually, and the chart mean and
the chart variance converge. -/
theorem tendsto_chart_of_isChartAvoid (hc : c.IsConformal) (hliftc : ContinuousOn c.2.2 c.dom)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) (ht : IsChartAvoid w ζ c φ t)
    {s : ℕ → ℝ≥0} (hsa : Antitone s) (hts : ∀ i, t < s i) (hlim : Tendsto s atTop (𝓝 t)) :
    (∀ᶠ i in atTop, IsChartAvoid w ζ c φ (s i)) ∧
      Tendsto (fun i => chartMean κ ρL ρR w vL vR c a k φ (s i)) atTop
        (𝓝 (chartMean κ ρL ρR w vL vR c a k φ t)) ∧
      Tendsto (fun i => chartVar w c φ (s i)) atTop (𝓝 (chartVar w c φ t)) := by
  obtain ⟨hK', hK'H, hdom, hfc, hinv⟩ := ht.image hc
  set K' := c.1 '' tsupport φ with hK'_def
  have hK'H' : K' ⊆ H := fun z hz => (hK'H hz).1
  -- eventually alive
  have hζev : ∀ᶠ i in atTop, (s i : ℝ≥0∞) < ζ :=
    (ENNReal.tendsto_coe.2 hlim).eventually (gt_mem_nhds ht.1)
  obtain ⟨i₁, hi₁⟩ := eventually_atTop.1 hζev
  -- the directed open cover of `K'`
  set U : ℕ → Set ℂ := fun j => H \ fwdHull (rpath w) (s (j + i₁) : ℝ) with hU_def
  have hUo : ∀ j, IsOpen (U j) := fun j =>
    MartMeans2.isOpen_H_diff_fwdHull_rpath hw (hi₁ _ (Nat.le_add_left _ _))
  have hUmono : Monotone U := fun a b hab =>
    sdiff_subset_sdiff_right (QuantumZipper.CoreArc.fwdHull_mono_coreArc
      (by exact_mod_cast hsa (Nat.add_le_add_right hab i₁)))
  have hUun : ⋃ j, U j = H \ fwdHull (rpath w) (t : ℝ) :=
    iUnion_H_diff_fwdHull (fun i => (hts i).le) hlim i₁
  obtain ⟨j₀, hj₀⟩ := hK'.elim_directed_cover U hUo (hUun ▸ hK'H) hUmono.directed_le
  set i₀ := j₀ + i₁ with hi₀
  set r := s i₀ with hr
  have hrζ : (r : ℝ≥0∞) < ζ := hi₁ _ (Nat.le_add_left _ _)
  obtain ⟨δ, hδ, hsafe⟩ := exists_isSafeAt hw hK' hrζ hj₀
  have hsr : ∀ i ≥ i₀, s i ≤ r := fun i hi => hsa hi
  have htr : t ≤ r := (hts i₀).le
  refine ⟨?_, ?_, ?_⟩
  · -- eventually valid
    filter_upwards [eventually_ge_atTop i₀] with i hi
    refine ⟨hi₁ i (le_trans (Nat.le_add_left _ _) hi), fun x hx => ⟨c.1 x, ?_, hinv x hx⟩⟩
    have hx' := hj₀ (mem_image_of_mem c.1 hx)
    exact ⟨hx'.1, fun h => hx'.2 (QuantumZipper.CoreArc.fwdHull_mono_coreArc
      (by exact_mod_cast hsr i hi) h)⟩
  · -- the chart mean, by dominated convergence
    set C₀ := meanHarmonicBound κ ρL ρR + |QuantumZipper.chiC κ| * (2 / δ ^ 2 * r)
    obtain ⟨L, hL⟩ := φ.hasCompactSupport.isCompact.exists_bound_of_continuousOn (hliftc.mono hdom)
    have hcont : ∀ u ≤ r, ContinuousOn
        (fun z => (meanCan κ ρL ρR w vL vR u (c.1 z) - a - k * c.2.2 z) * φ z) (tsupport φ) :=
      fun u hu => ((((hsafe.continuousOn_meanCan_space hw hK'H' hδ hu).comp hfc
        (mapsTo_image _ _)).sub continuousOn_const).sub
        (continuousOn_const.mul (hliftc.mono hdom))).mul φ.continuous.continuousOn
    have hmeas : ∀ u ≤ r, AEStronglyMeasurable
        (fun z => (meanCan κ ρL ρR w vL vR u (c.1 z) - a - k * c.2.2 z) * φ z) volume :=
      fun u hu => aestronglyMeasurable_of_continuousOn_tsupport (hcont u hu) fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
    have hbound : ∀ u ≤ r, ∀ z, ‖(meanCan κ ρL ρR w vL vR u (c.1 z) - a - k * c.2.2 z) * φ z‖ ≤
        (C₀ + |a| + |k| * L) * |φ z| := by
      intro u hu z
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hz : z ∈ tsupport φ
      · refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have h1 := hsafe.abs_meanCan_le (κ := κ) (ρL := ρL) (ρR := ρR) (vL := vL) (vR := vR) hw hK'H' hδ hu
          (mem_image_of_mem c.1 hz)
        have h2 : |c.2.2 z| ≤ L := by simpa [Real.norm_eq_abs] using hL z hz
        have h3 := abs_sub (meanCan κ ρL ρR w vL vR u (c.1 z) - a) (k * c.2.2 z)
        have h4 := abs_sub (meanCan κ ρL ρR w vL vR u (c.1 z)) a
        rw [abs_mul] at h3
        have h5 : |k| * |c.2.2 z| ≤ |k| * L := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        linarith
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have hint : Integrable (fun z => (C₀ + |a| + |k| * L) * |φ z|) volume :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).abs.const_mul _
    have hsi : Tendsto (fun i => s (i + i₀)) atTop (𝓝[Iic r] t) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim.comp (tendsto_add_atTop_nat i₀),
        Eventually.of_forall fun i => hsr _ (Nat.le_add_left _ _)⟩
    have hlimz : ∀ z, Tendsto (fun i => (meanCan κ ρL ρR w vL vR (s (i + i₀)) (c.1 z) - a - k * c.2.2 z) * φ z)
        atTop (𝓝 ((meanCan κ ρL ρR w vL vR t (c.1 z) - a - k * c.2.2 z) * φ z)) := by
      intro z
      by_cases hz : z ∈ tsupport φ
      · have hct := hsafe.continuousOn_meanCan_time (κ := κ) (ρL := ρL) (ρR := ρR) hw hvL hvR hK'H' hδ
          (mem_image_of_mem c.1 hz)
        exact ((((hct t htr).tendsto.comp hsi).sub tendsto_const_nhds).sub tendsto_const_nhds).mul
          tendsto_const_nhds
      · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
        exact tendsto_const_nhds
    have hdc := tendsto_integral_of_dominated_convergence (fun z => (C₀ + |a| + |k| * L) * |φ z|)
      (fun i => hmeas _ (hsr _ (Nat.le_add_left _ _))) hint
      (fun i => ae_of_all _ (hbound _ (hsr _ (Nat.le_add_left _ _)))) (ae_of_all _ hlimz)
    exact (tendsto_add_atTop_iff_nat i₀).1 hdc
  · -- the chart variance, by monotone Dirichlet-space approximation
    have hVo : ∀ j, IsOpen (c.2.1 '' U j) := fun j =>
      SmallGammaGeodesics.CC.isOpen_image_conf (hUo j) (hc.1.mono sdiff_subset) (hc.injOn.mono sdiff_subset)
    have hVmono : Monotone fun j => c.2.1 '' U j := fun a b hab => image_mono (hUmono hab)
    have hVH : ∀ j, c.2.1 '' U j ⊆ H := fun j => (image_mono sdiff_subset).trans hc.2.1.image_subset
    have hlimV := LocalSets.tendsto_zeroGFFTestCov_iUnion hVo hVmono hVH φ
    rw [← image_iUnion, hUun] at hlimV
    exact (tendsto_add_atTop_iff_nat i₁).1 hlimV

/-- **The clause's mean is the explicit chart mean**, for every bounded harmonic extension at time `t`. -/
theorem integral_couplingMean_eq_chartMean (hc : c.IsConformal)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (ht : IsChartAvoid w ζ c φ t)
    (hvL : ∀ i, vL i t ≤ w t) (hvR : ∀ i, w t ≤ vR i t) {v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t))
      (forceJumpSet (fun i => vL i t - w t) (fun i => vR i t - w t)) v) :
    ∫ z, (couplingMean κ (rpath w) (t : ℝ) v (c.1 z) - a - k * c.2.2 z) * φ z =
      chartMean κ ρL ρR w vL vR c a k φ t := by
  obtain ⟨hK', hK'H, -, -, -⟩ := ht.image hc
  obtain ⟨δ, hδ, hsafe⟩ := exists_isSafeAt hw hK' ht.1 hK'H
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport φ
  · simp only
    rw [couplingMean_eq_meanCan hw (fun z hz => (hK'H hz).1) hsafe hδ le_rfl (mem_image_of_mem c.1 hz) hvL hvR hv]
  · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]

end Path

/-! ### The clause at fixed times of a raw filtration -/

section Random

/-- **The chart coupling clause at fixed times, killed at the lifetime**, for a filtration `𝓐` (e.g. the raw
filtration generated by the revealed curves): for every fixed time `t`, every choice `u` of the bounded harmonic
extensions at `t` and every test function `φ`, almost surely on `{t < ζ} ∩ {supp φ ⊆ inv(ℍ ∖ K_t)}`, the
conditional characteristic function of `(h, φ)` given `𝓐_t` is that of the chart mean plus a zero-boundary GFF on
`inv(ℍ ∖ K_t)`. This is `MartMeans2.IsChartCouplingCharFun` with the stopping times replaced by fixed times (and
the a.s. condition `τ < ζ` by the event `{t < ζ}`). -/
def IsChartCouplingCharFunConst (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (𝓐 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (c : Ω → Chart) (a k : ℝ) (h : Ω → DistOn upperHalfPlaneOpens) :
    Prop :=
  ∀ (t : ℝ≥0) (u : Ω → ℂ → ℝ),
    (∀ ω, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω)) →
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζ ω →
        tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) →
          condExp (𝓐 t) P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
            Complex.exp (Complex.I * ((∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) (t : ℝ) (u ω)
                ((c ω).1 z) - a - k * (c ω).2.2 z) * φ z : ℝ) : ℂ) -
              (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω)
                (t : ℝ))) φ φ : ℝ) : ℂ))

variable {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {a k : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The chart coupling clause at every stopping time of the usual augmentation, from fixed times.** Let the
charts be conformal with lifts continuous on their domains, `W`, `V^L`, `V^R` continuous before `ζ` with
`V^L ≤ W ≤ V^R` there, and `h` measurable. If the chart clause holds at fixed times of `𝓐`
(`IsChartCouplingCharFunConst`), it holds at every stopping time of `usualAugmentation 𝓐 P` (a right-continuous
filtration containing the null sets). -/
theorem isChartCouplingCharFun_usualAugmentation [IsProbabilityMeasure P] (hh : Measurable h)
    (hc : ∀ ω, (c ω).IsConformal) (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hW : ∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVL : ∀ i ω, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVR : ∀ i ω, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hord : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω ≤ W t ω) ∧ ∀ i, W t ω ≤ VR i t ω)
    (hcf : IsChartCouplingCharFunConst κ ρL ρR P 𝓐 W VL VR ζ c a k h) :
    MartMeans2.IsChartCouplingCharFun κ ρL ρR P (usualAugmentation 𝓐 P) W VL VR ζ c a k h := by
  intro τ hτ hτζ u hu φ
  set X : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) with hX_def
  have hXm : Measurable X := by
    have hφm : Measurable fun ω => h ω φ := (LQGMetric.measurable_distOn_apply φ).comp hh
    exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hφm))
  have hX : MemLp X 2 P := by
    refine MemLp.of_bound hXm.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    show ‖Complex.exp (Complex.I * (h ω φ : ℂ))‖ ≤ 1
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  set E : ℝ≥0 → Set Ω := fun t => {ω | IsChartAvoid (fun s => W s ω) (ζ ω) (c ω) φ t} with hE_def
  set F : ℝ≥0 → Ω → ℂ := fun t ω => Complex.exp (Complex.I *
      (chartMean κ ρL ρR (fun s => W s ω) (fun i s => VL i s ω) (fun i s => VR i s ω) (c ω) a k φ t : ℂ) -
      (((1 / 2 : ℝ) * chartVar (fun s => W s ω) (c ω) φ t : ℝ) : ℂ)) with hF_def
  -- fixed times
  have hdet : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ E q → P[X | 𝓐 q] ω = F q ω := by
    intro q
    choose u₀ hu₀ using fun ω => Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
      (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)
    filter_upwards [hcf q u₀ hu₀ φ] with ω hω hE
    have hE' : IsChartAvoid (fun s => W s ω) (ζ ω) (c ω) φ q := hE
    have key : (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) (q : ℝ) (u₀ ω) ((c ω).1 z) - a -
        k * (c ω).2.2 z) * φ z) =
        chartMean κ ρL ρR (fun s => W s ω) (fun i s => VL i s ω) (fun i s => VR i s ω) (c ω) a k φ q :=
      integral_couplingMean_eq_chartMean (κ := κ) (ρL := ρL) (ρR := ρR) (vL := fun i s => VL i s ω)
        (vR := fun i s => VR i s ω) (hc ω) (hW ω) hE' (hord ω q hE'.1).1 (hord ω q hE'.1).2 (hu₀ ω)
    rw [hω hE'.1 hE'.2, key]
    rfl
  -- right-continuity
  have hright : ∀ ω t, ω ∈ E t → ∀ s : ℕ → ℝ≥0, Antitone s → (∀ i, t < s i) → Tendsto s atTop (𝓝 t) →
      (∀ᶠ i in atTop, ω ∈ E (s i)) ∧ Tendsto (fun i => F (s i) ω) atTop (𝓝 (F t ω)) := by
    intro ω t hE s hsa hts hlim
    obtain ⟨h1, h2, h3⟩ := tendsto_chart_of_isChartAvoid (κ := κ) (ρL := ρL) (ρR := ρR) (a := a) (k := k)
      (hc ω) (hliftc ω) (hW ω) (fun i => hVL i ω) (fun i => hVR i ω) hE hsa hts hlim
    refine ⟨h1, ?_⟩
    have hm := (Complex.continuous_ofReal.tendsto _).comp h2
    have hv := (Complex.continuous_ofReal.tendsto _).comp (h3.const_mul (1 / 2 : ℝ))
    exact (Complex.continuous_exp.tendsto _).comp ((hm.const_mul Complex.I).sub hv)
  have hmain := ae_condExp_stopping_eq_of_forall_const_complex hX hdet hright hτ
  filter_upwards [hmain, hτζ] with ω hω hωζ hsupp
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, τ ω = t :=
    WithTop.ne_top_iff_exists.1 (ne_top_of_lt hωζ) |>.imp fun _ h => h.symm
  rw [ht, WithTop.untopD_coe] at hsupp ⊢
  rw [ht] at hωζ
  have hE : ω ∈ E t := ⟨hωζ, hsupp⟩
  have hu' := hu ω
  rw [ht, WithTop.untopD_coe] at hu'
  have hE' : IsChartAvoid (fun s => W s ω) (ζ ω) (c ω) φ t := hE
  have key : (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) (t : ℝ) (u ω) ((c ω).1 z) - a -
      k * (c ω).2.2 z) * φ z) =
      chartMean κ ρL ρR (fun s => W s ω) (fun i s => VL i s ω) (fun i s => VR i s ω) (c ω) a k φ t :=
    integral_couplingMean_eq_chartMean (κ := κ) (ρL := ρL) (ρR := ρR) (vL := fun i s => VL i s ω)
      (vR := fun i s => VR i s ω) (hc ω) (hW ω) hE' (hord ω t hωζ).1 (hord ω t hωζ).2 hu'
  rw [hω t ht hE, key]
  rfl

end Random

end Lemma71D

end Sec7

end InteractingSLE
