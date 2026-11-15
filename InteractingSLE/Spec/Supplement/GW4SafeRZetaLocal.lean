/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaAdded

/-!
# GW4: nested canonical hulls retain component locality

On each live line the canonical safe hull equals the given local-set
witness. Off that event it is all of H, so it contains that witness.
The existing enlargement theorem transfers marked locality. Passing to
the physical past gives nested, physically measurable reference sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Supp8.RelSafe LocalSets WholeField Restart

/-- Canonical safe hulls increase with the physical line time, including
all outcomes where the clipped traversal has already stopped. -/
theorem safeHull_mono {Ω : Type*} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (ω : Ω) :
    Monotone (fun t => safeHull F Wd GT R V t ω) := by
  intro s t hst
  have hClock := Frame.monotone_min_physClockG hF hGT (V := V) ω hst
  by_cases ht : lineClock F Wd GT V t ω < V ω
  · have hs : lineClock F Wd GT V s ω < V ω := hClock.trans_lt ht
    have hfin := (ht.trans_le le_top).ne
    have hst' : (lineClock F Wd GT V s ω).toNNReal ≤
        (lineClock F Wd GT V t ω).toNNReal := ENNReal.toNNReal_mono hfin hClock
    simp only [safeHull, hs, ht, ↓reduceIte]
    exact inter_subset_inter_right _
      (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 hst'))
  · simp only [safeHull, ht, ↓reduceIte]
    exact safeHull_subset_H F Wd GT R V s ω

/-- Component marked locality supplies the canonical safe hull's locality
with its actual physical history as marks. -/
theorem component_safeHull_locality {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hF : F.IsOk) (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B) (t : ℝ≥0) :
    IsHistoryAvoidanceLocal (physFilt Frame.measurable_gw4Rec hWm ν t)
      (safeHull F Wd GT R V t) (centredField X u₀) ν := by
  obtain ⟨-, hphys, -, -, hBc, hBl, hShape⟩ := hloc
  have hMeas := Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver t
  have hSub : ∀ᵐ ω ∂ν, B t ω ⊆ safeHull F Wd GT R V t ω := by
    filter_upwards [hShape t] with ω hShapeω z hz
    have hzH := (hBc t ω).1 hz
    by_cases ht : lineClock F Wd GT V t ω < V ω
    · simp only [safeHull, ht, ↓reduceIte]
      refine ⟨hzH, ?_⟩
      by_contra hn
      have hm : z ∈ H \ B t ω := (Set.ext_iff.mp (hShapeω ht) z).2 ⟨hzH, hn⟩
      exact hm.2 hz
    · simpa only [safeHull, ht, ↓reduceIte] using hzH
  have hL := Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set (hBl t)
    (hMeas.mono (hphys t) le_rfl) hSub
  exact fun U G hUH hG hd E hE => hL U G hUH hG hd E (hphys t _ hE)

end InteractingSLE.Theorem14.GW4Fix
