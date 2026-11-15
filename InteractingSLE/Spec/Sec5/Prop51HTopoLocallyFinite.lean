/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoExcursions
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Compact sets meet only finitely many chart-Q excursions

Excursions are the connected components of the open set of positive times at
which the proper arc lies outside the counterflow hull. A compact set strictly
inside that complementary domain has a compact set of visiting times. Its cover
by open excursion intervals has a finite subcover. Thus no assumption on the
number of contacts with the nonsimple hull is needed.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

variable {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}

/-- The positive times belonging to counterflow-complement excursions. -/
def excursionTimes (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) : Set ℝ :=
  Ioi 0 ∩ η ⁻¹' (H \ cfHullQ w s)

/-- Excursion times form an open subset of the real time line. -/
theorem isOpen_excursionTimes (hη : IsProperArc η) (hw : Continuous w)
    (hs : 0 ≤ s) : IsOpen (excursionTimes η w s) :=
  (hη.cont.mono Ioi_subset_Ici_self).isOpen_inter_preimage isOpen_Ioi
    (isOpen_H_diff_negInv_fwdHull hw hs)

/-- Properness makes the nonnegative visiting times of any compact set compact. -/
theorem isCompact_visitingTimes (hη : IsProperArc η) {K : Set ℂ}
    (hK : IsCompact K) : IsCompact (Ici 0 ∩ η ⁻¹' K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨T, hT⟩ := eventually_atTop.1 (tendsto_atTop.1 hη.tendsto (R + 1))
  refine (isCompact_Icc (a := (0 : ℝ)) (b := T)).of_isClosed_subset
    (hη.cont.preimage_isClosed_of_isClosed isClosed_Ici hK.isClosed) ?_
  rintro t ⟨ht0, htK⟩
  refine ⟨ht0, le_of_not_gt fun hTt => ?_⟩
  have htR := hR (η t) htK
  have htlarge := hT t hTt.le
  linarith only [htR, htlarge]

/-- Only finitely many components of an open subset of the real line can meet
a compact subset contained in it. -/
theorem finite_components_meeting_compact {U S : Set ℝ} (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U) :
    ((fun t => connectedComponentIn U t) '' S).Finite := by
  have hcover : S ⊆ ⋃ t ∈ S, connectedComponentIn U t := by
    intro t ht
    exact mem_iUnion.2 ⟨t, mem_iUnion.2 ⟨ht, mem_connectedComponentIn (hSU ht)⟩⟩
  obtain ⟨T, _, hTf, hTcover⟩ := hS.elim_finite_subcover_image
    (fun _ _ => hU.connectedComponentIn) hcover
  refine (hTf.image (fun t => connectedComponentIn U t)).subset ?_
  rintro C ⟨t, ht, rfl⟩
  obtain ⟨u, huT, htu⟩ := mem_iUnion₂.1 (hTcover ht)
  exact ⟨u, huT, connectedComponentIn_eq htu⟩

/-- Finitely many physical excursion ranges meet any compact subset of the
counterflow-complement domain. The index is the excursion interval itself. -/
theorem finite_excursions_meeting_compact (hη : IsProperArc η)
    (hw : Continuous w) (hs : 0 ≤ s) {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ H \ cfHullQ w s) :
    ((fun t => connectedComponentIn (excursionTimes η w s) t) ''
      (Ici 0 ∩ η ⁻¹' K)).Finite := by
  refine finite_components_meeting_compact (isOpen_excursionTimes hη hw hs)
    (isCompact_visitingTimes hη hK) ?_
  rintro t ⟨ht0, htK⟩
  refine ⟨?_, hKD htK⟩
  show 0 < t
  refine lt_of_le_of_ne ht0 ?_
  intro ht
  have hH := (hKD htK).1
  rw [← ht, hη.zero] at hH
  exact ne_zero_of_mem_H hH rfl

/-- A compact set in chart space has only finitely many corresponding physical
excursions, by continuous inverse-chart transport. -/
theorem finite_excursions_meeting_chart_compact (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ((fun t => connectedComponentIn (excursionTimes η w s) t) ''
      (Ici 0 ∩ η ⁻¹' (revChartInv w s '' K))).Finite :=
  finite_excursions_meeting_compact hη hw hs
    (hK.image_of_continuousOn ((continuousOn_revChartInv hw hw0 hs).mono hKH))
    (by rintro _ ⟨z, hz, rfl⟩; exact revChartInv_mem hw hw0 hs (hKH hz))

end InteractingSLE.Sec5.Prop51HTopo
