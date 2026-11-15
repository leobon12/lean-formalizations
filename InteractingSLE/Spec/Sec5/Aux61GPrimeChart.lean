/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GPrimeNested
import InteractingSLE.Spec.Sec5.Aux61SlitVChart

/-! # The actual chart Gaussian mean compared along free components

Construct a physical conditional decomposition and identify its chart
transport with the given Gaussian mean by uniqueness. The inverse chart
need only eventually lie in a free component near the selected landing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GPrime

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open LocalSets (germSigma IsLocalSetMean lowerUnion)
open WholeField (IsHistoryAvoidanceLocal centredField)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Aux61Fib (FibCode)
open Aux61FibK (codeFiltration)
open Aux61ChLoc (IsChartGaussAt liveEv liveSet liveSet_of_mem liveSet_of_notMem measurableSet_live
  isHistoryAvoidanceLocal_liveSet ae_condExp_eq_of_eqOn)
open Aux61UnionK (chartHull norm_cexp_I_mul_ofReal_le measurable_field_apply measurable_apply_of_measurable
  isOpen_H_diff_chartHull)

open Aux61SlitV
open InteractingSLE.Theorem14.SB.FinRel

variable {X : Type u} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]

/-- Componentwise comparison for every actual chart Gaussian mean.
No identity for that unknown mean is assumed. -/
theorem ae_tendsto_chart_sub_flowMean_comp {μ : Measure X} [IsProbabilityMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) {Y : X → FibCode} (hY : Measurable Y) (q : ℝ≥0)
    {h : X → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ)
    {c : X → Chart} (hc : ∀ x, (c x).IsConformal) (a k : ℝ)
    (hfield : ∀ x, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → (Y x).field = Chart.chartTransport (hc x) 1 a k (h x))
    (hℋ : ℋ ≤ mX) (hZℋ : mβ.comap Z ≤ ℋ)
    (hYℋ : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ ℋ)
    (hdom : ∀ z, MeasurableSet[ℋ] {x | z ∈ (c x).dom})
    (hfwd : ∀ z, Measurable[ℋ] ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z))
    (hliftm : ∀ z, Measurable[ℋ] ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z))
    (hliftc : ∀ x, ContinuousOn (c x).2.2 (c x).dom)
    (hlift : ∀ x, InnerProductSpace.HarmonicOnNhd (c x).2.2 (c x).dom)
    {A : X → Set ℂ} (hAm : Measurable[mX, hittingSigma] A) (hAc : ∀ x, A x ⊆ H ∧ IsOpen (H \ A x))
    (hloc : IsHistoryAvoidanceLocal ℋ A (centredField h u₀) μ)
    (hgeo : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → H \ A x = (c x).2.1 '' (H \ chartHull Y q x))
    {ι : Type*} [Countable ι] {L : ι → X → Set ℂ} {g₂ : ι → X → DistOn upperHalfPlaneOpens}
    (hLm : ∀ i, Measurable[mX, hittingSigma] (L i)) (hLc : ∀ i, ∀ᵐ x ∂μ, L i x ⊆ H ∧ IsOpen (H \ L i x))
    (hLunb : ∀ i, ∀ᵐ x ∂μ, ∀ z ∈ lowerUnion (L i x),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (L i x)) z))
    (hg₂ : ∀ i, IsLocalSetMean (L i) (centredField h u₀) μ (g₂ i))
    {M₂ : ι → X → ℂ → ℝ} (hM₂h : ∀ i, ∀ᵐ x ∂μ, InnerProductSpace.HarmonicOnNhd (M₂ i x) (H \ L i x))
    (hM₂ : ∀ i, ∀ᵐ x ∂μ, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L i x →
      g₂ i x φ = ∫ z, (M₂ i x z - u₀ z) * φ z)
    {A' : ι → X → Set ℂ} {ℳ : ι → MeasurableSpace X} (hℳ : ∀ i, ℳ i ≤ mX)
    (hA'm : ∀ i, Measurable[mX, hittingSigma] (A' i)) (hA'c : ∀ i x, A' i x ⊆ H ∧ IsOpen (H \ A' i x))
    (hloc' : ∀ i, IsHistoryAvoidanceLocal (ℳ i) (A' i) (centredField h u₀) μ)
    (hℋℳ : ∀ i, ℋ ≤ ℳ i) (hAℳ : ∀ i, Measurable[ℳ i, hittingSigma] A) (hAA' : ∀ i x, A x ∩ H ⊆ A' i x)
    (hLℳ : ∀ i, Measurable[ℳ i, hittingSigma] (L i)) (hLA' : ∀ i x, L i x ∩ H ⊆ A' i x)
    {S' : ι → Set X} (hS' : ∀ i, MeasurableSet[ℋ] (S' i)) (hSA : ∀ i, ∀ᵐ x ∂μ, x ∈ S' i → A' i x = A x)
    {h₁ : X → DistOn upperHalfPlaneOpens}
    (hG : @IsChartGaussAt X mX β mβ μ Z B Y q
      (germSigma (liveSet (liveEv Z B Y q) A) (centredField h u₀) ⊔ ℋ) h₁) :
    ∀ᵐ x ∂μ, ∀ i, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → x ∈ S' i →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∀ z₀ ∈ L i x ∪ {z : ℂ | z.im = 0}, ∀ r > 0,
      ∀ l : Filter ℂ, l ≤ 𝓟 (H \ chartHull Y q x) → Tendsto (c x).2.1 l (𝓝 z₀) →
      (∀ᶠ ζ in l, (c x).2.1 ζ ∈ freeNear (A x) (L i x) z₀ r) →
        Tendsto (fun ζ => v ζ - (M₂ i x ((c x).2.1 ζ) + a + k * (c x).2.2 ((c x).2.1 ζ))) l (𝓝 0) := by
  classical
  set S := liveEv Z B Y q with hSdef
  set h0 := centredField h u₀ with hh0def
  have hh0m : Measurable h0 := WholeField.measurable_centredField hhm u₀
  have hSℋ : MeasurableSet[ℋ] S := measurableSet_live hZℋ hYℋ hB
  have hS : MeasurableSet S := hℋ _ hSℋ
  have hSℳ : ∀ i, MeasurableSet[ℳ i] S := fun i => hℋℳ i _ hSℋ
  -- the physical union on the live event and its germ decomposition
  set Al : X → Set ℂ := liveSet S A with hAldef
  have hAlm : Measurable[mX, hittingSigma] Al := Measurable.piecewise hS hAm measurable_const
  have hAlc : ∀ x, Al x ⊆ H ∧ IsOpen (H \ Al x) := fun x => by
    by_cases hx : x ∈ S
    · rw [hAldef, liveSet_of_mem hx]; exact hAc x
    · rw [hAldef, liveSet_of_notMem hx, Set.sdiff_self]; exact ⟨subset_rfl, isOpen_empty⟩
  have hlocl : IsHistoryAvoidanceLocal ℋ Al h0 μ := isHistoryAvoidanceLocal_liveSet hloc hSℋ
  obtain ⟨g, hgm, hgh, hgc⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh0 hAlm hℋ hlocl (ae_of_all _ hAlc)
  have h𝒢 : germSigma Al h0 ⊔ ℋ ≤ mX := sup_le (LocalSets.germSigma_le hAlm hh0m) hℋ
  have hg𝒢 : Measurable[germSigma Al h0 ⊔ ℋ] g := hgm.mono le_sup_left le_rfl
  have hℋ𝒢 : ℋ ≤ germSigma Al h0 ⊔ ℋ := le_sup_right
  -- the physical comparison for the live versions of the larger unions
  have hA'lm : ∀ i, Measurable[mX, hittingSigma] (liveSet S (A' i)) := fun i =>
    Measurable.piecewise hS (hA'm i) measurable_const
  have hA'lc : ∀ i, ∀ᵐ x ∂μ, liveSet S (A' i) x ⊆ H ∧ IsOpen (H \ liveSet S (A' i) x) := fun i =>
    ae_of_all _ fun x => by
      by_cases hx : x ∈ S
      · rw [liveSet_of_mem hx]; exact hA'c i x
      · rw [liveSet_of_notMem hx, Set.sdiff_self]; exact ⟨subset_rfl, isOpen_empty⟩
  have hAlℳ : ∀ i, Measurable[ℳ i, hittingSigma] Al := fun i =>
    Measurable.piecewise (hSℳ i) (hAℳ i) measurable_const
  have hsubl : ∀ (E : X → Set ℂ) (i : ι), (∀ x, E x ∩ H ⊆ A' i x) → ∀ x, liveSet S E x ∩ H ⊆ liveSet S (A' i) x :=
    fun E i hE x => by
      by_cases hx : x ∈ S
      · rw [liveSet_of_mem hx, liveSet_of_mem hx]; exact hE x
      · rw [liveSet_of_notMem hx, liveSet_of_notMem hx]; exact inter_subset_left
  have hLsub : ∀ i x, L i x ∩ H ⊆ liveSet S (A' i) x := fun i x => by
    by_cases hx : x ∈ S
    · rw [liveSet_of_mem hx]; exact hLA' i x
    · rw [liveSet_of_notMem hx]; exact inter_subset_right
  have hphys := ae_tendsto_sub_flowMean_comp (𝒢 := germSigma Al h0 ⊔ ℋ) (S := S') hh0 hAlm hg𝒢 hgh hgc hLm hLc hLunb hg₂
    hℳ hA'lm hA'lc (fun i => isHistoryAvoidanceLocal_liveSet (hloc' i) (hSℳ i)) hAlℳ
    (fun i => hsubl A i (hAA' i)) hLℳ hLsub (fun i => sup_le_sup_left (hℋℳ i) _)
    (fun i => hℋ𝒢 _ (hS' i)) (fun i => by
      filter_upwards [hSA i] with x hx hxS'
      by_cases hxS : x ∈ S
      · rw [hAldef, liveSet_of_mem hxS, liveSet_of_mem hxS, hx hxS']
      · rw [hAldef, liveSet_of_notMem hxS, liveSet_of_notMem hxS])
  -- the explicit chart decomposition, and uniqueness
  have hM := isChartGaussAt_chartTransport (𝒢 := germSigma Al h0 ⊔ ℋ) hB hY q hhm hu₀ hc a k hfield h𝒢
    (hZℋ.trans hℋ𝒢) (hYℋ.trans hℋ𝒢) (fun z => hℋ𝒢 _ (hdom z)) (fun z => (hfwd z).mono hℋ𝒢 le_rfl)
    (fun z => (hliftm z).mono hℋ𝒢 le_rfl) hliftc hlift hgeo hg𝒢
    (by filter_upwards [hgh] with x hx hxB hxq; rwa [hAldef, liveSet_of_mem (show x ∈ S from ⟨hxB, hxq⟩)] at hx)
    hgc
  have huniq := Aux61MeanId.gauss_ae_forall_apply_eq hG hM hY hB
  filter_upwards [hphys, huniq, ae_all_iff.2 hM₂, ae_all_iff.2 hM₂h, hgeo, ae_all_iff.2 hSA, ae_all_iff.2 hLc]
    with x hph hun hM₂x hM₂hx hgeox hSAx hLcx
  intro i hxB hxq hxS' v hv hrep z₀ hz₀ r hr l hl hinv hfree
  have hxS : x ∈ S := ⟨hxB, hxq⟩
  have hAl : Al x = A x := liveSet_of_mem hxS
  have hA'A : A' i x = A x := hSAx i hxS'
  obtain ⟨u, hu, hurep, hulim⟩ := hph i hxS'
  rw [hAl] at hu hurep hulim
  have hOo : IsOpen (H \ chartHull Y q x) := isOpen_H_diff_chartHull Y hxq
  have hgx : H \ A x = (c x).2.1 '' (H \ chartHull Y q x) := hgeox hxB hxq
  have hLA : L i x ∩ H ⊆ A x := hA'A ▸ hLA' i x
  have hAL : H \ A x ⊆ H \ L i x := fun z hz => ⟨hz.1, fun hzL => hz.2 (hLA ⟨hzL, hz.1⟩)⟩
  have hAo : IsOpen (H \ A x) := (hAc x).2
  have hinvO : MapsTo (c x).2.1 (H \ chartHull Y q x) (H \ A x) := by rw [hgx]; exact mapsTo_image _ _
  have hinvd : DifferentiableOn ℂ (c x).2.1 (H \ chartHull Y q x) := (hc x).1.mono sdiff_subset
  -- the harmonic candidate `u ∘ inv + w₂`
  have huinv : InnerProductSpace.HarmonicOnNhd (u ∘ (c x).2.1) (H \ chartHull Y q x) :=
    LQGMetric.harmonicOnNhd_comp_holo hAo hOo hu hinvd hinvO
  have hM₂inv : InnerProductSpace.HarmonicOnNhd (M₂ i x ∘ (c x).2.1) (H \ chartHull Y q x) :=
    LQGMetric.harmonicOnNhd_comp_holo (hLcx i).2 hOo (hM₂hx i) hinvd (hinvO.mono_right hAL)
  have hlinv : InnerProductSpace.HarmonicOnNhd ((c x).2.2 ∘ (c x).2.1) (H \ chartHull Y q x) :=
    LQGMetric.harmonicOnNhd_comp_holo (c x).dom.isOpen hOo (hlift x) hinvd fun w hw => (hc x).inv_mem_dom hw.1
  set w₂ : ℂ → ℝ := fun ζ => M₂ i x ((c x).2.1 ζ) + a + k * (c x).2.2 ((c x).2.1 ζ) with hw₂def
  have hw₂ : InnerProductSpace.HarmonicOnNhd w₂ (H \ chartHull Y q x) := by
    have h3 := (hM₂inv.add (InnerProductSpace.harmonicOnNhd_const a)).add (hlinv.const_smul (c := k))
    convert h3 using 1
    funext ζ
    simp only [Pi.add_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, hw₂def]
  have hsum : InnerProductSpace.HarmonicOnNhd (fun ζ => u ((c x).2.1 ζ) + w₂ ζ) (H \ chartHull Y q x) :=
    huinv.add hw₂
  -- the pairings of `h₁` against tests off the chart hull
  set sm := smoothDist upperHalfPlaneOpens u₀ with hsmdef
  have hu₀c : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := fun z hz =>
    (hu₀ z hz).1.continuousAt.continuousWithinAt
  have hM₂c : ContinuousOn (M₂ i x) (H \ L i x) := continuousOn_of_harmonicOnNhd (hM₂hx i)
  have hrep₂ : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (c x).2.1 '' (H \ chartHull Y q x) →
      (g₂ i x + sm) φ = ∫ z, M₂ i x z * φ z := by
    intro φ hφ
    have hφL : tsupport φ ⊆ H \ L i x := (hgx ▸ hφ).trans hAL
    have i₁ : Integrable fun z => (M₂ i x z - u₀ z) * φ z :=
      WholeField.integrable_mul_testOn (hM₂c.sub (hu₀c.mono (sdiff_subset))) φ hφL
    have i₂ : Integrable fun z => u₀ z * φ z := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
    rw [add_apply, hM₂x i φ hφL, hsmdef, SupercriticalConformalCovariance.GM24.smoothDist_apply hu₀c,
      ← integral_add i₁ (by simpa only [mul_comm] using i₂)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    ring
  have hpair : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x →
      ∫ z, v z * ψ z = ∫ z, (u ((c x).2.1 z) + w₂ z) * ψ z := by
    intro ψ hψ
    have hdisj : Disjoint (tsupport ψ) (chartHull Y q x) :=
      Set.disjoint_left.2 fun z hz hzK => (hψ hz).2 hzK
    rw [← hrep ψ hψ, hun hxB hxq ψ hdisj]
    have hsplit : Chart.chartTransport (hc x) 1 a k (g x + sm) ψ =
        Chart.chartTransport (hc x) 1 a k (g₂ i x + sm) ψ + Chart.pullField (hc x) (g x - g₂ i x) ψ := by
      have e := congrArg (fun T : DistOn upperHalfPlaneOpens => T ψ)
        (Chart.chartTransport_sub (hc x) 1 a k (g x + sm) (g₂ i x + sm))
      have e' : g x + sm - (g₂ i x + sm) = g x - g₂ i x := by abel
      simp only [sub_apply, one_smul, e'] at e
      linarith
    have h1 : Chart.chartTransport (hc x) 1 a k (g₂ i x + sm) ψ = ∫ w, w₂ w * ψ w :=
      chartTransport_apply_eq_integral_of_subset (hc x) (hliftc x) sdiff_subset (hM₂c.mono (hgx ▸ hAL)) hrep₂ a k
        hψ
    have h2 : Chart.pullField (hc x) (g x - g₂ i x) ψ = ∫ w, u ((c x).2.1 w) * ψ w :=
      pullField_apply_eq_integral_of_subset (hc x) sdiff_subset (fun φ hφ => by
        rw [sub_apply]; exact hurep φ (hgx ▸ hφ)) hψ
    have i₁ : Integrable fun w => w₂ w * ψ w :=
      WholeField.integrable_mul_testOn (continuousOn_of_harmonicOnNhd hw₂) ψ hψ
    have i₂ : Integrable fun w => u ((c x).2.1 w) * ψ w :=
      WholeField.integrable_mul_testOn (continuousOn_of_harmonicOnNhd huinv) ψ hψ
    rw [hsplit, h1, h2, ← integral_add i₁ i₂]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only
    ring
  have hEq : EqOn v (fun ζ => u ((c x).2.1 ζ) + w₂ ζ) (H \ chartHull Y q x) :=
    Sec6.eqOn_of_integral_mul_eq hOo sdiff_subset hv hsum hpair
  -- the limit
  have hO : H \ chartHull Y q x ∈ l := hl (mem_principal_self _)
  have hinv' : Tendsto (c x).2.1 l (𝓝[freeNear (A x) (L i x) z₀ r] z₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hinv, hfree⟩
  have hlim : Tendsto (fun ζ => u ((c x).2.1 ζ)) l (𝓝 0) := (hulim z₀ hz₀ r hr).comp hinv'
  refine hlim.congr' ?_
  filter_upwards [hO] with ζ hζ
  rw [hEq hζ]
  simp only [hw₂def]
  ring

end InteractingSLE.Sec5.Aux61GPrime
