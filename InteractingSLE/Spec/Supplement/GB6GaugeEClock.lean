/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeEChart

/-!
# The original physical clock in the retained record chart

The decoded driver agrees through the retained endpoint. Its hull, relative
map and clock therefore agree with the original locally continuous driver.
The existing glued-chain clock and the source range clause give exact
coverage of every live relative capacity time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Supp8.GB6.GaugeE

open Exist.StagedLaw

section Record

variable {Ω : Type*} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {ω : Ω} (s : ℝ≥0)
  (h0 : Wα 0 ω = 0) (hc : ContinuousOn (Wα · ω) {t | (t : ℝ≥0∞) < ζα ω})
  (hs : (s : ℝ≥0∞) < ζα ω)

include h0 hc hs

theorem record_prefix_eq : EqOn (rdrv (gb6Rec s Wα ζα ω)) (Ito.rpath (Wα · ω)) (Icc 0 s) :=
  fun _ hx => rdrv_recOf_cfE s h0 hc hs hx.2

theorem record_relMap_eq : relMap (rdrv (gb6Rec s Wα ζα ω)) s = relMap (Ito.rpath (Wα · ω)) s :=
  relMap_eq_of_eqOn s.coe_nonneg (record_prefix_eq s h0 hc hs)

theorem record_relClock_eq (W : ℝ → ℝ) :
    relClock (rdrv (gb6Rec s Wα ζα ω)) s W = relClock (Ito.rpath (Wα · ω)) s W :=
  relClock_eq_of_eqOn s.coe_nonneg (record_prefix_eq s h0 hc hs) W

theorem record_hull_eq : fwdHull (rdrv (gb6Rec s Wα ζα ω)) s = fwdHull (Ito.rpath (Wα · ω)) s := by
  let V := rdrv (gb6Rec s Wα ζα ω)
  have hV : Continuous (fun t : ℝ≥0 => V t) := (continuous_rdrv _).comp NNReal.continuous_coe
  have hV0 : V 0 = 0 := rdrv_zero _
  have he : ∀ t ≤ s, V t = Wα t ω := fun t ht => by
    have h := rdrv_recOf_cfE s h0 hc hs (x := (t : ℝ)) (NNReal.coe_le_coe.2 ht)
    change rdrv (gb6Rec s Wα ζα ω) (t : ℝ) = Wα t ω
    rw [show rdrv (gb6Rec s Wα ζα ω) (t : ℝ) = Wα (t : ℝ).toNNReal ω from h]
    rw [Real.toNNReal_coe]
  have hpath : Ito.rpath (fun t : ℝ≥0 => V t) = V := by
    funext x
    simp only [Ito.rpath, V, rdrv, Real.toNNReal_coe]
  have h := (SourceC.chart_prefix_eq hc h0 hV hV0 hs he).1
  rwa [hpath] at h

end Record

/-- A continuous physical clock from zero reaching above `u` reaches `u`
exactly on that physical prefix. -/
theorem exists_clock_eq {a : ℝ≥0 → ℝ} {T : ℝ≥0} (hc : ContinuousOn a (Icc 0 T))
    (h0 : a 0 = 0) {u : ℝ≥0} (hu : (u : ℝ) ≤ a T) :
    ∃ t ∈ Icc 0 T, a t = u :=
  intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ T) hc (by rw [h0]; exact ⟨u.coe_nonneg, hu⟩)

/-- On separated generating prefixes, the intrinsic relative clock is
continuous and strictly increasing from zero throughout the contact interval. -/
theorem relative_clock_regular {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 < s)
    {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) {Tc : ℝ≥0∞} (hTc : 0 < Tc)
    (hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T))) :
    relClock U s (Ito.rpath w) 0 = 0 ∧
      StrictMonoOn (fun t : ℝ≥0 => relClock U s (Ito.rpath w) t) {t | (t : ℝ≥0∞) < Tc} ∧
      ContinuousOn (fun t : ℝ≥0 => relClock U s (Ito.rpath w) t) {t | (t : ℝ≥0∞) < Tc} := by
  obtain ⟨_, _, h0, hm, hc, _, _⟩ := exists_glued_relChain hw hw0 hU hU0 hs htip hTc hd
    (fun t _ => hγ.2.2 t ENNReal.coe_lt_top)
  exact ⟨h0, hm, hc⟩

end InteractingSLE.Supp8.GB6.GaugeE
