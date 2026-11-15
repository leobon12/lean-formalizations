/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBGlue
import InteractingSLE.Spec.Supplement.GB6CoordBCompat

/-!
# A measurable relative driver from countably many separated physical prefixes

The geometric assumptions concern the given drivers and traces on measurable
events. All measurable choices and compatibility of relative drivers are
proved, including at real counterflow visits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.CoordB

open Sec7.PocketTraversal Sec7.Lemma71C

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Measurable local choices glue to a relative driver on the full union of
a countable family of separated physical prefix events. -/
theorem exists_measurable_driver_of_separated_prefixes
    {V : ℝ≥0 → Ω → ℝ} (hVm : ∀ t, Measurable (V t))
    (hVc : ∀ ω, Continuous (V · ω)) (hV0 : ∀ ω, V 0 ω = 0)
    {γ : Ω → ℝ≥0 → ℂ} (hγm : ∀ t, Measurable fun ω => γ ω t)
    {w : Ω → ℝ≥0 → ℝ} {s : ℝ≥0} (hs : 0 < s)
    {E : ℕ → Set Ω} (hE : ∀ n, MeasurableSet (E n))
    {T : ℕ → ℝ≥0} (hT : ∀ n, 0 < T n)
    (hgeom : ∀ n ω, ω ∈ E n → Continuous (w ω) ∧ w ω 0 = 0 ∧
      IsGeneratingTrace (w ω) ⊤ (γ ω) ∧ ∃ p : ℂ,
        Tendsto (QuantumZipper.fwdMapInv (Ito.rpath (V · ω)) s) (𝓝[H] 0) (𝓝 p) ∧
        Disjoint (closure (fwdHull (Ito.rpath (V · ω)) s))
          (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath (w ω)) (T n)))) :
    ∃ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞),
      (∀ t, Measurable (D t)) ∧ Measurable L ∧
      (∀ ω, ContinuousOn (D · ω) {t | (t : ℝ≥0∞) < L ω}) ∧
      (∀ ω, D 0 ω = 0) ∧ AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) L D ∧
      (∀ ω (r : ℝ≥0), (r : ℝ≥0∞) < L ω → ∃ n, ω ∈ E n ∧
        ∃ t : ℝ≥0, t < T n ∧ (r : ℝ) < relClock (Ito.rpath (V · ω)) s (Ito.rpath (w ω)) t) ∧
      ∀ n ω, ω ∈ E n → ∀ t : ℝ≥0, t < T n →
        0 ≤ relClock (Ito.rpath (V · ω)) s (Ito.rpath (w ω)) t ∧
        ENNReal.ofReal (relClock (Ito.rpath (V · ω)) s (Ito.rpath (w ω)) t) < L ω ∧
        fwdHull (fun r : ℝ => D r.toNNReal ω)
          (relClock (Ito.rpath (V · ω)) s (Ito.rpath (w ω)) t) =
            relMap (Ito.rpath (V · ω)) s '' fwdHull (Ito.rpath (w ω)) t := by
  let Γ : ℕ → Ω → ℝ → ℂ := fun n ω => localCurve (Ito.rpath (V · ω)) s (γ ω) (T n)
  have hgn : ∀ n ω, ω ∈ E n → ∃ (w' : ℝ≥0 → ℝ) (p : ℂ),
      Continuous w' ∧ w' 0 = 0 ∧ IsGeneratingTrace w' ⊤ (γ ω) ∧
      Tendsto (QuantumZipper.fwdMapInv (Ito.rpath (V · ω)) s) (𝓝[H] 0) (𝓝 p) ∧
      Disjoint (closure (fwdHull (Ito.rpath (V · ω)) s))
        (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w') (T n))) := by
    intro n ω hω
    obtain ⟨hw, hw0, hγ, p, htip, hd⟩ := hgeom n ω hω
    exact ⟨w ω, p, hw, hw0, hγ, htip, hd⟩
  have hΓ : ∀ n ω, ω ∈ E n → IsDrivenCurve (Γ n ω) :=
    fun n => isDrivenCurve_localCurve_on hVc hV0 hs (hT n) (hgn n)
  have hΓm : ∀ n u, 0 ≤ u → Measurable ((E n).indicator fun ω => Γ n ω u) :=
    fun n => measurable_indicator_localCurve hVm hVc hV0 hγm (hE n) (hT n) (hgn n)
  have hcompat : ∀ n k ω (r : ℝ≥0), ω ∈ E n → ω ∈ E k →
      (r : ℝ≥0∞) < capLife (Γ n ω) → (r : ℝ≥0∞) < capLife (Γ k ω) →
      drivenDriver (Γ n) r ω = drivenDriver (Γ k) r ω := by
    intro n k ω r hn hk hrn hrk
    obtain ⟨hw, hw0, hγ, p, htip, hdn⟩ := hgeom n ω hn
    obtain ⟨-, -, -, _, -, hdk⟩ := hgeom k ω hk
    have hU := Chart.continuous_rpath_of_continuous (hVc ω)
    have hU0 := Chart.rpath_zero_of (hV0 ω)
    rcases le_total (T n) (T k) with hnk | hkn
    · exact localDriver_eq_of_le hU hU0 (by exact_mod_cast hs) htip hw hw0 hγ
        (hT n) (hT k) hnk hdn hdk hrn
    · exact (localDriver_eq_of_le hU hU0 (by exact_mod_cast hs) htip hw hw0 hγ
        (hT k) (hT n) hkn hdk hdn hrk).symm
  let l : ℕ → Ω → ℝ≥0∞ := fun n => (E n).indicator fun ω => capLife (Γ n ω)
  obtain ⟨D, hDm, hDn, hDc, hD0, hLm, hDa⟩ :=
    exists_driver_of_atlas (driverAtlas_of_curves hE hΓ hΓm hcompat)
  refine ⟨D, atlasLife l, hDm, hLm, hDc, hD0, hDa, ?_, fun n ω hω t ht => ?_⟩
  · intro ω r hr
    obtain ⟨n, hn⟩ := (lt_atlasLife_iff r ω).1 hr
    have hω : ω ∈ E n := by
      by_contra hnot
      have hz : l n ω = 0 := indicator_of_notMem hnot _
      rw [hz] at hn
      exact not_lt_zero hn
    have hn' : (r : ℝ≥0∞) < capLife (Γ n ω) := by
      simpa only [l, indicator_of_mem hω] using hn
    obtain ⟨hw, hw0, hγ, p, htip, hd⟩ := hgeom n ω hω
    exact ⟨n, hω, (lt_localLife_iff (Chart.continuous_rpath_of_continuous (hVc ω))
      (Chart.rpath_zero_of (hV0 ω)) (by exact_mod_cast hs) htip hw hw0 hγ (hT n) hd r).1 hn'⟩
  · obtain ⟨hw, hw0, hγ, p, htip, hd⟩ := hgeom n ω hω
    have hU := Chart.continuous_rpath_of_continuous (hVc ω)
    have hU0 := Chart.rpath_zero_of (hV0 ω)
    have hL := relClock_lt_localLife hU hU0 (by exact_mod_cast hs) htip hw hw0 hγ hd (hT n) ht
    obtain ⟨u, hu, he⟩ := exists_clockOf_eq ht
    have ha0 : 0 ≤ relClock (Ito.rpath (V · ω)) s (Ito.rpath (w ω)) t := by
      rw [← he, ← capClock_localCurve hU hU0 (by exact_mod_cast hs) htip hw hw0 hγ hd (hT n) hu]
      exact (hΓ n ω hω).capClock_nonneg hu
    have hLn : capLife (Γ n ω) = l n ω :=
      (indicator_of_mem hω (fun ω => capLife (Γ n ω))).symm
    refine ⟨ha0, (hL.trans_le (hLn.trans_le (le_iSup (fun n => l n ω) n))), ?_⟩
    obtain ⟨b, hab, hbL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hL
    have hab' : relClock (Ito.rpath (V · ω)) s (Ito.rpath (w ω)) t < b :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0).1
        (by simpa only [ENNReal.ofReal_coe_nnreal] using hab)
    have heq : fwdHull (fun r : ℝ => D r.toNNReal ω)
        (relClock (Ito.rpath (V · ω)) s (Ito.rpath (w ω)) t) =
        fwdHull (fun r : ℝ => drivenDriver (Γ n) r.toNNReal ω)
          (relClock (Ito.rpath (V · ω)) s (Ito.rpath (w ω)) t) := by
      apply fwdHull_eq_of_eqOn ha0 hab'
      intro r hr
      have hrL : (r.toNNReal : ℝ≥0∞) < l n ω := by
        rw [← hLn]
        exact (ENNReal.ofReal_le_coe.2 hr.2).trans_lt hbL
      rw [hDn n ω r.toNNReal hrL, indicator_of_mem hω]
    rw [heq]
    exact fwdHull_localDriver hU hU0 (by exact_mod_cast hs) htip hw hw0 hγ hd (hT n) ht

end InteractingSLE.Supp8.GB6.CoordB
