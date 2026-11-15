/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS5SideFixed
import InteractingSLE.Spec.Supplement.SBLemmaS2LiftSide
import InteractingSLE.Spec.Supplement.S9BOrder

/-!
# Side transport for the physical gluing in Lemma S5

`s5JunctionGermStatement` and `s5InteriorTransportStatement` discharge the two
remaining inputs of the corrected helper. Consequently `s5SideUpperStatement`
and the source-facing `s5Statement` are proved without extra inputs.

Components of the upper part of a proper curve's left side have an untouched
negative real gate. These gates prove inverse-chart left-side transport even
with real contacts. Local Jordan sectors and a far-right anchor then give right
transport. Properness of the inverse extension classifies the old-domain
boundary on the new left: its points are in the domain or on the untouched real
ray left of `L`. The same gate argument covers the new upper left side by the
old left side and the old domain, both disjoint from the old range. This proves
old-range preservation, including real junctions and buried old-range points.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B

namespace InteractingSLE.Theorem14.SB

/-- A component's closure acquires no new point inside its ambient set. -/
theorem s5_closure_component_inter_subset {U : Set ℂ} {w : ℂ} (hw : w ∈ U) :
    closure (connectedComponentIn U w) ∩ U ⊆ connectedComponentIn U w := by
  rintro z ⟨hz, hzU⟩
  have hpc : IsPreconnected (insert z (connectedComponentIn U w)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hz subset_closure)
  have hsub : insert z (connectedComponentIn U w) ⊆ U :=
    insert_subset hzU (connectedComponentIn_subset _ _)
  exact hpc.subset_connectedComponentIn
    (mem_insert_of_mem _ (mem_connectedComponentIn hw)) hsub (mem_insert _ _)

/-- Every component of the left side in `H` has a negative real gate off the
curve. Unbounded components are included. -/
theorem s5_exists_negative_gate {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    {w : ℂ} (hw : w ∈ leftSide γ ∩ H) :
    ∃ x : ℝ, x < 0 ∧ (x : ℂ) ∉ range γ ∧
      (x : ℂ) ∈ closure (connectedComponentIn (leftSide γ ∩ H) w) := by
  set C := connectedComponentIn (leftSide γ ∩ H) w
  have hCsub : C ⊆ leftSide γ ∩ H := connectedComponentIn_subset _ _
  have hwC : w ∈ C := mem_connectedComponentIn hw
  by_contra hgate
  have hcl : closure C ∩ leftSide γ ⊆ C := by
    rintro z ⟨hz, hzL⟩
    have him : 0 ≤ z.im := closure_minimal
      (fun v hv => le_of_lt (hCsub hv).2) (isClosed_le continuous_const continuous_im) hz
    rcases him.lt_or_eq with hpos | hzero
    · exact s5_closure_component_inter_subset hw ⟨hz, hzL, hpos⟩
    · have hx : z.re < 0 := by
        simpa only [hγ0, zero_re] using
          re_lt_of_mem_leftSide hγ (by rw [hγ0]; rfl) hzL (by linarith)
      have hzreal : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [← hzero])
      exact (hgate ⟨z.re, hx, by rw [hzreal]; exact notMem_range_of_mem_leftSide hzL,
        by rw [hzreal]; exact hz⟩).elim
  have hCo : IsOpen C := ((isOpen_leftSide' hγ).inter QuantumZipper.isOpen_H).connectedComponentIn
  have hLC : leftSide γ ⊆ C :=
    isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hCo ⟨w, hw.1, hwC⟩ hcl
  have href : γ 0 - 1 - I ∈ leftSide γ := leftRef_mem_leftSide hγ.2.2.1 (by rw [hγ0]; rfl)
  have : γ 0 - 1 - I ∈ H := (hCsub (hLC href)).2
  norm_num [QuantumZipper.H, hγ0] at this

/-- The inverse chart transports the left side once untouched negative gates
and avoidance of the physical closed curve have been identified. -/
theorem s5_left_transport_of_negative_gates {bt Γ : ℝ≥0 → ℂ} {g : ℂ → ℂ}
    (hbt : IsProperCurve bt) (hbt0 : bt 0 = 0) (hΓ : IsProperCurve Γ)
    (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hoff : ∀ w ∈ leftSide bt ∩ H, g w ∉ seedRayClosure Γ)
    (hnegative : ∀ x : ℝ, x < 0 → (x : ℂ) ∉ range bt → g x ∈ leftSide Γ) :
    g '' (leftSide bt ∩ H) ⊆ leftSide Γ := by
  rintro _ ⟨w, hw, rfl⟩
  set C := connectedComponentIn (leftSide bt ∩ H) w
  have hCsub : C ⊆ leftSide bt ∩ H := connectedComponentIn_subset _ _
  have hwC : w ∈ C := mem_connectedComponentIn hw
  obtain ⟨x, hx, hxbt, hxC⟩ := s5_exists_negative_gate hbt hbt0 hw
  have hcont : ContinuousOn g (closure C) := hgc.mono (closure_minimal
    (fun z hz => show 0 ≤ z.im from le_of_lt (hCsub hz).2)
      (isClosed_le continuous_const continuous_im))
  have hgcl : g (x : ℂ) ∈ closure (g '' C) :=
    ((hcont _ hxC).mono subset_closure).mem_closure_image hxC
  obtain ⟨r, hr, hrL⟩ := Metric.isOpen_iff.1 (isOpen_leftSide' hΓ) _ (hnegative x hx hxbt)
  obtain ⟨v, hv, hvdist⟩ := Metric.mem_closure_iff.1 hgcl r hr
  have hvL : v ∈ leftSide Γ := hrL (by rwa [mem_ball, dist_comm])
  have himg : IsPreconnected (g '' C) := isPreconnected_connectedComponentIn.image g
    (hgc.mono fun z hz => show 0 ≤ z.im from le_of_lt (hCsub hz).2)
  have himgoff : g '' C ⊆ (seedRayClosure Γ)ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hoff z (hCsub hz)
  have hsub := himg.subset_connectedComponentIn hv himgoff
  rw [← connectedComponentIn_eq hvL] at hsub
  exact hsub ⟨w, hwC, rfl⟩

section Glued

variable {p : ℝ → ℂ} {β β' : ℝ≥0 → ℂ} {a₂ tL : ℝ≥0}
  {c : Chart} {g : ℂ → ℂ} {bt : ℝ≥0 → ℂ}

/-- The head through `L` stays in the old filled hull. -/
theorem s5_head_subset_hullK (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hβ' : IsProperCompletion β a₂ β') (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (htL : tL ≤ a₂) (hβtL : β tL = realMin (p '' Icc 0 1)) :
    β' '' Icc 0 tL ⊆ hullK (p '' Icc 0 1) := by
  have hβ'P := isProperCurve_of_isProperCompletion hβ'
  have hβ'0 : β' 0 = 0 := (hβ'.2.2.2.2 0 zero_le).trans hβ0
  have hβ'tL : β' tL = realMin (p '' Icc 0 1) := (hβ'.2.2.2.2 tL htL).trans hβtL
  obtain ⟨_, t, ht, _, hhead, _, _⟩ := s2HullStatement p β' hp hp0 hpH hβ'P hβ'0 hA
  have heq : t = tL := hβ'P.2.1 (ht.trans hβ'tL.symm)
  simpa only [heq] using hhead

/-- An interior point off the relative curve cannot map onto the physical
closed curve: the head is in the old hull and the tail has exactly the prescribed
relative preimages. -/
theorem s5_inv_notMem_glued {A : Set ℂ} (hD : IsDomainChart (H \ fillH A) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hhead : β' '' Icc 0 tL ⊆ hullK A) (hbt : IsProperCurve bt)
    (hΓ0 : gluedCurve β' g bt tL 0 = 0) {w : ℂ} (hw : w ∈ H) (hwb : w ∉ range bt) :
    g w ∉ seedRayClosure (gluedCurve β' g bt tL) := by
  have hwD := g_mem_of_mem_H hD hgi hw
  rintro (⟨s, hs⟩ | ⟨_, him⟩)
  · by_cases hst : s ≤ tL
    · rw [gluedCurve_of_le hst] at hs
      exact notMem_hullK_of_mem_D hwD (hhead ⟨s, ⟨zero_le, hst⟩, hs⟩)
    · rw [gluedCurve_of_lt (not_le.1 hst)] at hs
      rcases (hbt.2.2.1 (s - tL)).lt_or_eq with hpos | hzero
      · have heq : bt (s - tL) = w := hD.1.injOn hpos hw (by rwa [hgi hpos, hgi hw] at hs)
        exact hwb ⟨s - tL, heq⟩
      · have hb : bt (s - tL) = (((bt (s - tL)).re : ℝ) : ℂ) :=
          Complex.ext (by simp) (by simp [← hzero])
        exact g_ofReal_notMem hD hgc hgi (bt (s - tL)).re (by rw [← hb, hs]; exact hwD)
  · rw [hΓ0, zero_im] at him
    exact (not_le.2 hwD.1) him

/-- Untouched negative relative gates map to untouched physical real gates on
the left of the glued curve. -/
theorem s5_negative_gate_image (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hhead : β' '' Icc 0 tL ⊆ hullK (p '' Icc 0 1)) (hbt : IsProperCurve bt)
    (hΓ : IsProperCurve (gluedCurve β' g bt tL)) (hΓ0 : gluedCurve β' g bt tL 0 = 0)
    {x : ℝ} (hx : x < 0) (hxbt : (x : ℂ) ∉ range bt) :
    g x ∈ leftSide (gluedCurve β' g bt tL) := by
  obtain ⟨e, he, _, hge, hsurj⟩ := hc.exists_boundary_orient hp hp0 hgc hgi
  obtain ⟨y, hy, hey⟩ := hsurj x hx
  have hgx : g x = (y : ℂ) := by rw [← hey]; exact (hge y hy).2
  rw [hgx]
  apply ofReal_mem_leftSide' hΓ hΓ0 (lt_of_lt_of_le hy (realBase_facts hp hp0).2.2.2.1)
  rintro ⟨s, hs⟩
  by_cases hst : s ≤ tL
  · rw [gluedCurve_of_le hst] at hs
    exact ofReal_notMem_hullK hy (hhead ⟨s, ⟨zero_le, hst⟩, hs⟩)
  · rw [gluedCurve_of_lt (not_le.1 hst)] at hs
    rcases (hbt.2.2.1 (s - tL)).lt_or_eq with hpos | hzero
    · have hH := (g_mem_of_mem_H hc.1 hgi hpos).1
      rw [hs] at hH
      exact absurd hH (by simp [QuantumZipper.H])
    · have hb : bt (s - tL) = (((bt (s - tL)).re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simp [← hzero])
      have heq : (bt (s - tL)).re = e y := eq_of_g_ofReal_eq hc.1 hgc hgi (he y hy)
        (by rw [← hb]; exact hs)
      exact hxbt ⟨s - tL, by rw [hb, heq, hey]⟩

/-- The inverse left-entry chart takes every interior point of the relative
left side into the physical left side, including components cut off by real
contacts. This assertion does not assume the old range is on the new right. -/
theorem s5_image_leftSide_inter_H (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hβ' : IsProperCompletion β a₂ β') (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (htL : tL ≤ a₂) (hβtL : β tL = realMin (p '' Icc 0 1)) (hbt : IsProperCurve bt)
    (hbt0 : bt 0 = 0) (hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s))
    (hreal : ∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) :
    g '' (leftSide bt ∩ H) ⊆ leftSide (gluedCurve β' g bt tL) := by
  have hΓC := isProperCompletion_gluedCurve hp hp0 hpH hβ0 hβ' hA hc hgc hgi
    htL hβtL hbt hbtβ hreal
  have hΓ := isProperCurve_of_isProperCompletion hΓC
  have hΓ0 : gluedCurve β' g bt tL 0 = 0 := (hΓC.2.2.2.2 0 zero_le).trans hβ0
  have hhead := s5_head_subset_hullK hp hp0 hpH hβ0 hβ' hA htL hβtL
  exact s5_left_transport_of_negative_gates hbt hbt0 hΓ hgc
    (fun w hw => s5_inv_notMem_glued hc.1 hgc hgi hhead hbt hΓ0 hw.2
      (notMem_range_of_mem_leftSide hw.1))
    (fun x hx hxbt => s5_negative_gate_image hp hp0 hc hgc hgi hhead hbt hΓ hΓ0 hx hxbt)

end Glued

/-- For a chart carrying the relative curve into the physical curve, left-side
transport forces right-side transport. Local Jordan sectors rule out a wrong
component adjacent to the curve; connectedness of `H` and one right-side image
rule out a component with no interior boundary. -/
theorem s5_right_transport_of_left {D : Set ℂ} {c : Chart} {g : ℂ → ℂ}
    {bt Γ : ℝ≥0 → ℂ} (hD : IsDomainChart D c) (hgi : EqOn g c.2.1 H)
    (hgc : ContinuousOn g H) (hbt : IsProperCurve bt) (hbt0 : bt 0 = 0)
    (hΓ : IsProperCurve Γ) (hΓ0 : Γ 0 = 0)
    (hcurve : ∀ t, bt t ∈ H → g (bt t) ∈ seedRayClosure Γ)
    (hoff : ∀ w ∈ H, w ∉ range bt → g w ∉ seedRayClosure Γ)
    (hleft : g '' (leftSide bt ∩ H) ⊆ leftSide Γ)
    (hanchor : ∃ w ∈ H, g w ∈ rightSide Γ) :
    g '' (rightSide bt ∩ H) ⊆ rightSide Γ := by
  have himbt : (bt 0).im = 0 := by rw [hbt0]; rfl
  have himΓ : (Γ 0).im = 0 := by rw [hΓ0]; rfl
  have hgD : ∀ w ∈ H, g w ∈ D := fun w hw => by rw [hgi hw]; exact hD.inv_mem hw
  have hfg : ∀ w ∈ H, c.1 (g w) = w := fun w hw => by rw [hgi hw]; exact hD.fwd_inv hw
  have hgf : ∀ z ∈ D, g (c.1 z) = z := fun z hz => by
    rw [hgi (hD.fwd_mem hz)]; exact hD.inv_fwd hz
  set S := rightSide bt ∩ (H ∩ g ⁻¹' leftSide Γ)
  have hSo : IsOpen S := (isOpen_rightSide' hbt).inter
    (hgc.isOpen_inter_preimage QuantumZipper.isOpen_H (isOpen_leftSide' hΓ))
  have hSleft : g '' S ⊆ leftSide Γ := by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2
  have hcl : closure S ∩ H ⊆ S := by
    rintro w ⟨hwcl, hwH⟩
    have hgcl : g w ∈ closure (leftSide Γ) := closure_mono hSleft
      (((hgc w hwH).mono (fun v hv => hv.2.1)).mem_closure_image hwcl)
    by_cases hwrange : w ∈ range bt
    · obtain ⟨t, rfl⟩ := hwrange
      have hlocal := exists_local_sides hbt himbt (t : ℝ)
        (N := H) (by rw [seedLine_coe]; exact QuantumZipper.isOpen_H.mem_nhds hwH)
      obtain ⟨PL, PR, hPLc, hPRc, hPL, hPR, hev⟩ := hlocal
      rw [seedLine_coe] at hev
      obtain ⟨v, hvS, hvlocal⟩ := ((mem_closure_iff_frequently.1 hwcl).and_eventually hev).exists
      have hvPR : v ∈ PR := hvlocal.2 hvS.1
      have hPRoff : g '' PR ⊆ (seedRayClosure Γ)ᶜ := by
        rintro _ ⟨z, hz, rfl⟩
        exact hoff z (hPR hz).2 (notMem_range_of_mem_rightSide (hPR hz).1)
      have hPRimg : g '' PR ⊆ leftSide Γ := by
        have hpc := hPRc.image g (hgc.mono fun z hz => (hPR hz).2)
        have hsub := hpc.subset_connectedComponentIn (mem_image_of_mem g hvPR) hPRoff
        rw [← connectedComponentIn_eq (show g v ∈ leftSide Γ from hvS.2.2)] at hsub
        exact hsub
      have hqD := hgD (bt t) hwH
      have hfcont : ContinuousAt c.1 (g (bt t)) :=
        ((hD.differentiableOn_fwd _ hqD).differentiableAt (hD.isOpen.mem_nhds hqD)).continuousAt
      have hfevent : ∀ᶠ z in 𝓝 (g (bt t)), c.1 z ∈ H ∧
          ((c.1 z ∈ leftSide bt → c.1 z ∈ PL) ∧
            (c.1 z ∈ rightSide bt → c.1 z ∈ PR)) := by
        have h := (Filter.eventually_mem_set.2 (QuantumZipper.isOpen_H.mem_nhds hwH)).and hev
        rw [← hfg (bt t) hwH] at h
        exact hfcont.tendsto.eventually h
      have hqcl := seedRayClosure_subset_closure_rightSide hΓ himΓ (hcurve t hwH)
      have hne : (𝓝[rightSide Γ] (g (bt t))).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hqcl
      have hDevent : ∀ᶠ z in 𝓝 (g (bt t)), z ∈ D :=
        Filter.eventually_mem_set.2 (hD.isOpen.mem_nhds hqD)
      have hRevent : ∀ᶠ z in 𝓝[rightSide Γ] (g (bt t)), z ∈ rightSide Γ := self_mem_nhdsWithin
      obtain ⟨z, hzR, hzD, hzlocal⟩ :=
        (hRevent.and ((hDevent.and hfevent).filter_mono nhdsWithin_le_nhds)).exists
      have hzoff : c.1 z ∉ range bt := by
        rintro ⟨u, hu⟩
        have huH : bt u ∈ H := hu ▸ hzlocal.1
        have huΓ := hcurve u huH
        rw [hu, hgf z hzD] at huΓ
        exact connectedComponentIn_subset _ _ hzR huΓ
      have hzL : z ∈ leftSide Γ := by
        rw [← hgf z hzD]
        rcases mem_leftSide_or_mem_rightSide_of_mem_H hbt hbt0 hzlocal.1 hzoff with hl | hr
        · exact hleft ⟨c.1 z, ⟨hl, hzlocal.1⟩, rfl⟩
        · exact hPRimg ⟨c.1 z, hzlocal.2.2 hr, rfl⟩
      exact (Set.disjoint_left.1 (disjoint_leftSide_rightSide hΓ himΓ) hzL hzR).elim
    · have hwR : w ∈ rightSide bt := by
        rcases mem_leftSide_or_mem_rightSide_of_mem_H hbt hbt0 hwH hwrange with hl | hr
        · exact (notMem_closure_of_isOpen (isOpen_leftSide' hbt)
            (Set.disjoint_left.2 fun z hz hzL =>
              Set.disjoint_left.1 (disjoint_leftSide_rightSide hbt himbt) hzL hz.1) hl hwcl).elim
        · exact hr
      have hgL : g w ∈ leftSide Γ := by
        rcases mem_leftSide_or_mem_rightSide hΓ hΓ0 (hoff w hwH hwrange) with hl | hr
        · exact hl
        · exact (notMem_closure_of_isOpen (isOpen_rightSide' hΓ)
            (disjoint_leftSide_rightSide hΓ himΓ) hr hgcl).elim
      exact ⟨hwR, hwH, hgL⟩
  have hSempty : S = ∅ := by
    by_contra hne
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hHS : H ⊆ S := (convex_halfSpace_im_gt 0).isPreconnected.subset_of_closure_inter_subset
      hSo ⟨w, hw.2.1, hw⟩ hcl
    obtain ⟨v, hvH, hvR⟩ := hanchor
    exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hΓ himΓ) (hHS hvH).2.2 hvR
  rintro _ ⟨w, hw, rfl⟩
  rcases mem_leftSide_or_mem_rightSide hΓ hΓ0
      (hoff w hw.2 (notMem_range_of_mem_rightSide hw.1)) with hl | hr
  · exact (show w ∈ (∅ : Set ℂ) from hSempty ▸ ⟨hw.1, hw.2, hl⟩).elim
  · exact hr

section Interior

variable {p : ℝ → ℂ} {β β' : ℝ≥0 → ℂ} {a₂ tL : ℝ≥0}
  {c : Chart} {g : ℂ → ℂ} {bt : ℝ≥0 → ℂ}

/-- A far-right original-real collar supplies a point of the chart image on the
physical right side. -/
theorem s5_exists_right_anchor (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hβ' : IsProperCompletion β a₂ β') (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (htL : tL ≤ a₂) (hβtL : β tL = realMin (p '' Icc 0 1)) (hbt : IsProperCurve bt)
    (hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s))
    (hreal : ∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) :
    ∃ w ∈ H, g w ∈ rightSide (gluedCurve β' g bt tL) := by
  have hΓC := isProperCompletion_gluedCurve hp hp0 hpH hβ0 hβ' hA hc hgc hgi
    htL hβtL hbt hbtβ hreal
  have hΓ := isProperCurve_of_isProperCompletion hΓC
  have hΓ0 : gluedCurve β' g bt tL 0 = 0 := (hΓC.2.2.2.2 0 zero_le).trans hβ0
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hβ'.1.continuousOn).isBounded.exists_norm_le
    (s := β' '' Icc 0 a₂)
  set x : ℝ := |M| + |realMax (p '' Icc 0 1)| + 1
  have hx0 : 0 < x := by positivity
  have hxM : M < x := by dsimp [x]; linarith [le_abs_self M, abs_nonneg (realMax (p '' Icc 0 1))]
  have hxR : realMax (p '' Icc 0 1) < x := by
    dsimp [x]; linarith [le_abs_self (realMax (p '' Icc 0 1)), abs_nonneg M]
  have hxΓ : (x : ℂ) ∉ range (gluedCurve β' g bt tL) := by
    rintro ⟨s, hs⟩
    by_cases hsa : s ≤ a₂
    · have hβx : β' s = x := (hβ'.2.2.2.2 s hsa).trans ((hΓC.2.2.2.2 s hsa).symm.trans hs)
      have hb := hM _ ⟨s, ⟨zero_le, hsa⟩, hβx⟩
      rw [norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hb
      exact (not_le.2 hxM) hb
    · rcases gluedCurve_mem_of_lt hp hp0 hβ'.2.2.2.2 hc hgc hgi htL hbt hbtβ hreal
        (not_le.1 hsa) with hD | ⟨y, hy, he⟩
      · rw [hs] at hD
        exact absurd hD.1 (by simp [QuantumZipper.H])
      · have hyx : y = x := ofReal_injective (he.symm.trans hs)
        have hy0 := lt_of_lt_of_le hy (realBase_facts hp hp0).2.2.2.1
        exact (not_lt.2 hx0.le) (hyx ▸ hy0)
  have hxright : (x : ℂ) ∈ rightSide (gluedCurve β' g bt tL) := ofReal_mem_rightSide hΓ hΓ0 hx0 hxΓ
  have hfree := isFreeAt_of_gt (isCompact_Icc.image_of_continuousOn hp)
    (fun y hy => (realBase_facts hp hp0).2.2.1 y hy |>.2) hxR
  have hDev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ fillH (p '' Icc 0 1) :=
    eventually_mem_of_isFreeAt hfree
  have hRev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ rightSide (gluedCurve β' g bt tL) :=
    Filter.eventually_mem_set.2 (nhdsWithin_le_nhds ((isOpen_rightSide' hΓ).mem_nhds hxright))
  have hne : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1
    (mem_closure_H_of_im_nonneg (by simp))
  obtain ⟨z, hzD, hzR⟩ := (hDev.and hRev).exists
  refine ⟨c.1 z, hc.1.fwd_mem hzD, ?_⟩
  rw [hgi (hc.1.fwd_mem hzD), hc.1.inv_fwd hzD]
  exact hzR

/-- Interior right-side transport does not require prior preservation of `A`. -/
theorem s5_image_rightSide_inter_H (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hβ' : IsProperCompletion β a₂ β') (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (htL : tL ≤ a₂) (hβtL : β tL = realMin (p '' Icc 0 1)) (hbt : IsProperCurve bt)
    (hbt0 : bt 0 = 0) (hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s))
    (hreal : ∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) :
    g '' (rightSide bt ∩ H) ⊆ rightSide (gluedCurve β' g bt tL) := by
  have hΓC := isProperCompletion_gluedCurve hp hp0 hpH hβ0 hβ' hA hc hgc hgi
    htL hβtL hbt hbtβ hreal
  have hΓ := isProperCurve_of_isProperCompletion hΓC
  have hΓ0 : gluedCurve β' g bt tL 0 = 0 := (hΓC.2.2.2.2 0 zero_le).trans hβ0
  have hhead := s5_head_subset_hullK hp hp0 hpH hβ0 hβ' hA htL hβtL
  have hj : β' tL = g (bt 0) := by rw [hbtβ 0 zero_le, add_zero, hβ'.2.2.2.2 tL htL]
  exact s5_right_transport_of_left hc.1 hgi (hgc.mono H_subset_im_nonneg) hbt hbt0 hΓ hΓ0
    (fun u _ => Or.inl ⟨tL + u, gluedCurve_add hj u⟩)
    (fun z hz hzb => s5_inv_notMem_glued hc.1 hgc hgi hhead hbt hΓ0 hz hzb)
    (s5_image_leftSide_inter_H hp hp0 hpH hβ0 hβ' hA hc hgc hgi htL hβtL hbt hbt0 hbtβ hreal)
    (s5_exists_right_anchor hp hp0 hpH hβ0 hβ' hA hc hgc hgi htL hβtL hbt hbtβ hreal)

/-- Interior side transport is unconditional, including retained real contacts. -/
theorem s5InteriorTransportStatement : S5InteriorTransportStatement := by
  intro p β β' a₂ hp hp0 hpH hβ0 hβ' hA c g hc hgc hgi _
    tL bt htL hβtL hbt hbt0 hbtβ hreal _ w hw
  exact Or.inl (s5_image_rightSide_inter_H hp hp0 hpH hβ0 hβ' hA hc hgc hgi
    htL hβtL hbt hbt0 hbtβ hreal ⟨w, hw, rfl⟩)

end Interior

/-- A continuous inverse extension with the existing linear lower growth bound
maps closed upper-half-plane sets to closed sets. -/
theorem s5_isClosed_image_upper {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgrowth : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂)
    {S : Set ℂ} (hS : IsClosed S) (hSH : S ⊆ {z | 0 ≤ z.im}) : IsClosed (g '' S) := by
  let K : Set ℂ := {z | 0 ≤ z.im}
  have hKc : IsClosed K := isClosed_le continuous_const continuous_im
  let G : K → ℂ := fun w => g w
  have hGc : Continuous G := hgc.comp_continuous continuous_subtype_val fun w => w.2
  obtain ⟨C₁, C₂, hC₁, hg⟩ := hgrowth
  have hcompact : ∀ R : ℝ, IsCompact {w : K | ‖G w‖ ≤ R} := by
    intro R
    have hclosed : IsClosed (K ∩ g ⁻¹' closedBall 0 R) :=
      hgc.preimage_isClosed_of_isClosed hKc isClosed_closedBall
    have hbound : Bornology.IsBounded (K ∩ g ⁻¹' closedBall 0 R) :=
      isBounded_iff_forall_norm_le.2 ⟨C₁ * R + C₂, fun w hw =>
        (hg w hw.1).trans (add_le_add_left (mul_le_mul_of_nonneg_left
          (mem_closedBall_zero_iff.1 hw.2) hC₁) C₂)⟩
    have hcmp := hKc.isClosedEmbedding_subtypeVal.isCompact_preimage
      (Metric.isCompact_of_isClosed_isBounded hclosed hbound)
    convert hcmp using 1
    ext w
    simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_closedBall_zero_iff, w.2, true_and, G]
  have hclosed := isClosed_image_of_isCompact_norm_le hGc hcompact
    (hS.preimage continuous_subtype_val)
  have heq : G '' (Subtype.val ⁻¹' S) = g '' S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hSH hw⟩, hw, rfl⟩
  rwa [heq] at hclosed

/-- The image of the relative upper left side is relatively closed in the
physical upper left side. Relative real boundary points either map to real
negative gates or to the physical closed right side. -/
theorem s5_left_image_closure_inter_subset {g : ℂ → ℂ} {bt Γ : ℝ≥0 → ℂ}
    (hbt : IsProperCurve bt) (hbt0 : bt 0 = 0) (hΓ : IsProperCurve Γ) (hΓ0 : Γ 0 = 0)
    (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgrowth : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂)
    (hcurve : ∀ t, g (bt t) ∈ seedRayClosure Γ)
    (hright : g '' (closedRightSide bt ∩ {w | 0 ≤ w.im}) ⊆ closedRightSide Γ)
    (hnegative : ∀ x : ℝ, x < 0 → (g x).im = 0) :
    closure (g '' (leftSide bt ∩ H)) ∩ (leftSide Γ ∩ H) ⊆ g '' (leftSide bt ∩ H) := by
  have hLH : closure (leftSide bt ∩ H) ⊆ {z : ℂ | 0 ≤ z.im} := closure_minimal
    (fun z hz => show 0 ≤ z.im from le_of_lt hz.2) (isClosed_le continuous_const continuous_im)
  have hclosed := s5_isClosed_image_upper hgc hgrowth isClosed_closure hLH
  rintro z ⟨hzcl, hzL, hzH⟩
  have hzimg : z ∈ g '' closure (leftSide bt ∩ H) := hclosed.closure_subset
    (closure_mono (image_mono subset_closure) hzcl)
  obtain ⟨w, hwcl, hwz⟩ := hzimg
  rcases (show 0 ≤ w.im from hLH hwcl).lt_or_eq with hwH | hwzero
  · have hwL : w ∈ leftSide bt := by
      by_cases hwcurve : w ∈ range bt
      · obtain ⟨t, rfl⟩ := hwcurve
        exact (connectedComponentIn_subset _ _ hzL (hwz ▸ hcurve t)).elim
      · rcases mem_leftSide_or_mem_rightSide_of_mem_H hbt hbt0 hwH hwcurve with hl | hr
        · exact hl
        · have hclL : w ∈ closure (leftSide bt) := closure_mono inter_subset_left hwcl
          exact (notMem_closure_of_isOpen (isOpen_rightSide' hbt)
            (disjoint_leftSide_rightSide hbt (by rw [hbt0]; rfl)) hr hclL).elim
    exact ⟨w, ⟨hwL, hwH⟩, hwz⟩
  · have hwr : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [← hwzero])
    by_cases hwneg : w.re < 0
    · have him := hnegative w.re hwneg
      rw [← hwr, hwz] at him
      exact (not_lt.2 him.le hzH).elim
    · have hwR : (w.re : ℂ) ∈ closedRightSide bt := by
        rw [s5_closedRightSide_eq_compl hbt (by rw [hbt0]; rfl)]
        intro hwL
        have hx := re_lt_of_mem_leftSide hbt (by rw [hbt0]; rfl) hwL (by simp)
        simp only [hbt0, zero_re, ofReal_re] at hx
        exact hwneg hx
      have hzR := hright ⟨w, ⟨by rw [hwr]; exact hwR, hLH hwcl⟩, hwz⟩
      exact (notMem_closedRightSide_of_mem_leftSide hΓ hΓ0 hzL hzR).elim

/-- A domain-side criterion for preserving the old range. Upper components on
the new left are covered by the old left side and the old domain; their negative
gates exclude any further component. This includes terminal junctions on `A`. -/
theorem s5_oldRange_of_domain_sides {A D : Set ℂ} {γ₁ γ₂ : ℝ≥0 → ℂ} {a : ℝ≥0} {L : ℝ}
    (h₁ : IsProperCurve γ₁) (h₂ : IsProperCurve γ₂) (h₁0 : γ₁ 0 = 0) (h₂0 : γ₂ 0 = 0)
    (hAH : ∀ z ∈ A, 0 ≤ z.im) (hA : A ⊆ closedRightSide γ₁)
    (hDo : IsOpen D) (hDH : D ⊆ H) (hDA : Disjoint D A)
    (hagree : ∀ t ≤ a, γ₂ t = γ₁ t) (hpost : ∀ t, a < t → γ₁ t ∈ closure D)
    (hboundary : ∀ z ∈ closure D, z ∈ leftSide γ₂ → z ∈ D ∨ ∃ x < L, z = (x : ℂ))
    (hfree : ∀ x < L, ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ D)
    (hbase : ∀ x : ℝ, (x : ℂ) ∈ A → L ≤ x) : A ⊆ closedRightSide γ₂ := by
  have him₁ : (γ₁ 0).im = 0 := by rw [h₁0]; rfl
  have him₂ : (γ₂ 0).im = 0 := by rw [h₂0]; rfl
  let U := leftSide γ₂ ∩ H
  let E := U ∩ D
  let F := E ∪ (leftSide γ₁ ∩ U)
  have hUo : IsOpen U := (isOpen_leftSide' h₂).inter QuantumZipper.isOpen_H
  have hEo : IsOpen E := hUo.inter hDo
  have hFo : IsOpen F := hEo.union ((isOpen_leftSide' h₁).inter hUo)
  have hclE : closure E ∩ U ⊆ E := by
    rintro z ⟨hzcl, hzU⟩
    rcases hboundary z (closure_mono inter_subset_right hzcl) hzU.1 with hzD | ⟨x, _, hx⟩
    · exact ⟨hzU, hzD⟩
    · have hzH := hzU.2
      rw [hx] at hzH
      exact absurd hzH (by simp [QuantumZipper.H])
  have hclF : closure F ∩ U ⊆ F := by
    rintro z ⟨hzcl, hzU⟩
    rw [show closure F = closure E ∪ closure (leftSide γ₁ ∩ U) from closure_union] at hzcl
    rcases hzcl with hzE | hzold
    · exact Or.inl (hclE ⟨hzE, hzU⟩)
    · by_cases hzS : z ∈ seedRayClosure γ₁
      · rcases hzS with ⟨t, ht⟩ | ⟨_, him⟩
        · by_cases hta : t ≤ a
          · exact (connectedComponentIn_subset _ _ hzU.1 (Or.inl ⟨t, (hagree t hta).trans ht⟩)).elim
          · rcases hboundary z (ht ▸ hpost t (not_le.1 hta)) hzU.1 with hzD | ⟨x, _, hx⟩
            · exact Or.inl ⟨hzU, hzD⟩
            · have hzH := hzU.2
              rw [hx] at hzH
              exact absurd hzH (by simp [QuantumZipper.H])
        · rw [h₁0, zero_im] at him
          exact (not_le.2 hzU.2 him).elim
      · rcases mem_leftSide_or_mem_rightSide h₁ h₁0 hzS with hl | hr
        · exact Or.inr ⟨hl, hzU⟩
        · exact (notMem_closure_of_isOpen (isOpen_rightSide' h₁)
            (disjoint_leftSide_rightSide h₁ him₁) hr (closure_mono inter_subset_left hzold)).elim
  have hUF : U ⊆ F := by
    intro w hw
    set C := connectedComponentIn U w
    have hCsub : C ⊆ U := connectedComponentIn_subset _ _
    have hwC : w ∈ C := mem_connectedComponentIn hw
    obtain ⟨x, hx, hxγ₂, hxC⟩ := s5_exists_negative_gate h₂ h₂0 hw
    have hxL : (x : ℂ) ∈ leftSide γ₂ := ofReal_mem_leftSide' h₂ h₂0 hx hxγ₂
    have hmeet : (C ∩ F).Nonempty := by
      by_cases hxγ₁ : (x : ℂ) ∈ range γ₁
      · obtain ⟨t, ht⟩ := hxγ₁
        have hta : a < t := lt_of_not_ge fun hta => hxγ₂ ⟨t, (hagree t hta).trans ht⟩
        have hxbound := hboundary (x : ℂ) (ht ▸ hpost t hta) hxL
        obtain ⟨y, hyL, hyx⟩ : ∃ y < L, (x : ℂ) = (y : ℂ) := by
          rcases hxbound with hD | hy
          · exact absurd (hDH hD) (by simp [QuantumZipper.H])
          · exact hy
        have hxbase : x < L := by rwa [← ofReal_injective hyx] at hyL
        have hne : (𝓝[C] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxC
        have hDev : ∀ᶠ z in 𝓝[C] (x : ℂ), z ∈ D :=
          (hfree x hxbase).filter_mono (nhdsWithin_mono _ fun z hz => (hCsub hz).2)
        have hCev : ∀ᶠ z in 𝓝[C] (x : ℂ), z ∈ C := self_mem_nhdsWithin
        obtain ⟨z, hzC, hzD⟩ := (hCev.and hDev).exists
        exact ⟨z, hzC, Or.inl ⟨hCsub hzC, hzD⟩⟩
      · have hxold : (x : ℂ) ∈ leftSide γ₁ := ofReal_mem_leftSide' h₁ h₁0 hx hxγ₁
        obtain ⟨z, hzC, hzold⟩ := ((mem_closure_iff_frequently.1 hxC).and_eventually
          (Filter.eventually_mem_set.2 ((isOpen_leftSide' h₁).mem_nhds hxold))).exists
        exact ⟨z, hzC, Or.inr ⟨hzold, hCsub hzC⟩⟩
    have hCF : C ⊆ F := isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hFo
      hmeet (fun z hz => hclF ⟨hz.1, hCsub hz.2⟩)
    exact hCF hwC
  intro z hzA
  rw [s5_closedRightSide_eq_compl h₂ him₂]
  intro hzL
  rcases (hAH z hzA).lt_or_eq with hzH | hzero
  · rcases hUF ⟨hzL, hzH⟩ with ⟨_, hzD⟩ | ⟨hzold, _⟩
    · exact Set.disjoint_left.1 hDA hzD hzA
    · exact notMem_closedRightSide_of_mem_leftSide h₁ h₁0 hzold (hA hzA)
  · have hzreal : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
    have hxneg : z.re < 0 := by
      simpa only [h₂0, zero_re] using re_lt_of_mem_leftSide h₂ him₂ hzL (by linarith)
    have hzoldrange : z ∈ range γ₁ := by
      by_contra hnot
      have hzold : z ∈ leftSide γ₁ := by
        rw [hzreal]
        exact ofReal_mem_leftSide' h₁ h₁0 hxneg (by rwa [← hzreal])
      exact notMem_closedRightSide_of_mem_leftSide h₁ h₁0 hzold (hA hzA)
    obtain ⟨t, ht⟩ := hzoldrange
    have hta : a < t := lt_of_not_ge fun hta =>
      connectedComponentIn_subset _ _ hzL (Or.inl ⟨t, (hagree t hta).trans ht⟩)
    rcases hboundary z (ht ▸ hpost t hta) hzL with hzD | ⟨x, hx, hzx⟩
    · exact absurd (hDH hzD) (by rw [hzreal]; simp [QuantumZipper.H])
    · exact (not_le.2 hx) (hbase x (hzx ▸ hzA))

/-- The terminal old-range junction germ, including real and buried contacts. -/
theorem s5JunctionGermStatement : S5JunctionGermStatement := by
  intro p β β' a₂ hp hp0 hpH hβ0 hβ' hA c g hc hgc hgi _
    tL bt htL hβtL hbt hbt0 hbtβ hreal _
  set A := p '' Icc 0 1
  set D := H \ fillH A
  set Γ := gluedCurve β' g bt tL
  have hΓC := isProperCompletion_gluedCurve hp hp0 hpH hβ0 hβ' hA hc hgc hgi
    htL hβtL hbt hbtβ hreal
  have hΓ : IsProperCurve Γ := isProperCurve_of_isProperCompletion hΓC
  have hΓ0 : Γ 0 = 0 := (hΓC.2.2.2.2 0 zero_le).trans hβ0
  have hβ'P := isProperCurve_of_isProperCompletion hβ'
  have hβ'0 : β' 0 = 0 := (hβ'.2.2.2.2 0 zero_le).trans hβ0
  have hj : β' tL = g (bt 0) := by rw [hbtβ 0 zero_le, add_zero, hβ'.2.2.2.2 tL htL]
  have hright : g '' (closedRightSide bt ∩ {w | 0 ≤ w.im}) ⊆ closedRightSide Γ :=
    s5_image_right_upper_of_interior hbt hbt0 hΓ hΓ0 hgc
      (fun u => Or.inr (Or.inl ⟨tL + u, gluedCurve_add hj u⟩))
      (fun w hw => Or.inl (s5_image_rightSide_inter_H hp hp0 hpH hβ0 hβ' hA hc hgc hgi
        htL hβtL hbt hbt0 hbtβ hreal ⟨w, hw, rfl⟩))
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have h0A : (0 : ℂ) ∈ A := ⟨0, left_mem_Icc.2 zero_le_one, hp0⟩
  have hAconn : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) :=
    IsPreconnected.union 0 h0A (by simp)
      (isPreconnected_Icc.image p hp)
      (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
  have hgrowth := exists_norm_le_norm_g hc hAc.isBounded hAconn hgc hgi
  have hGclosed : IsClosed (g '' {w : ℂ | 0 ≤ w.im}) :=
    s5_isClosed_image_upper hgc hgrowth (isClosed_le continuous_const continuous_im) subset_rfl
  have hDG : D ⊆ g '' {w : ℂ | 0 ≤ w.im} := by
    intro z hz
    refine ⟨c.1 z, le_of_lt (show 0 < (c.1 z).im from hc.1.fwd_mem hz), ?_⟩
    rw [hgi (hc.1.fwd_mem hz), hc.1.inv_fwd hz]
  have hclDG : closure D ⊆ g '' {w : ℂ | 0 ≤ w.im} := closure_minimal hDG hGclosed
  obtain ⟨e, _, _, hge, hsurj⟩ := hc.exists_boundary_orient hp hp0 hgc hgi
  have hboundary : ∀ z ∈ closure D, z ∈ leftSide Γ →
      z ∈ D ∨ ∃ x < realMin A, z = (x : ℂ) := by
    intro z hz hzL
    obtain ⟨w, hwH, hwz⟩ := hclDG hz
    rcases (show 0 ≤ w.im from hwH).lt_or_eq with hwpos | hwzero
    · exact Or.inl (hwz ▸ g_mem_of_mem_H hc.1 hgi hwpos)
    · have hw : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [← hwzero])
      by_cases hwneg : w.re < 0
      · obtain ⟨x, hx, hex⟩ := hsurj w.re hwneg
        refine Or.inr ⟨x, hx, ?_⟩
        rw [← hwz, hw, ← hex]
        exact (hge x hx).2
      · have hwR : w ∈ closedRightSide bt := by
          rw [s5_closedRightSide_eq_compl hbt (by rw [hbt0]; rfl)]
          intro hwL
          have hn := re_lt_of_mem_leftSide hbt (by rw [hbt0]; rfl) hwL (by linarith)
          simp only [hbt0, zero_re] at hn
          exact hwneg hn
        exact (notMem_closedRightSide_of_mem_leftSide hΓ hΓ0 hzL
          (hright ⟨w, ⟨hwR, hwH⟩, hwz⟩)).elim
  obtain ⟨_, t, ht, _, _, htail, _⟩ := s2HullStatement p β' hp hp0 hpH hβ'P hβ'0 hA
  have hteq : t = tL := hβ'P.2.1 (ht.trans ((hβ'.2.2.2.2 tL htL).trans hβtL).symm)
  subst hteq
  have hAg : A ⊆ closedRightSide Γ := s5_oldRange_of_domain_sides hβ'P hΓ hβ'0 hΓ0
    (by rintro z ⟨s, hs, rfl⟩; exact hpH s hs) hA hc.1.isOpen (fun z hz => hz.1)
    (Set.disjoint_left.2 fun z hzD hzA => hzD.2 ⟨hzD.1, Or.inl (subset_closure hzA)⟩)
    (fun s hs => (hΓC.2.2.2.2 s hs).trans (hβ'.2.2.2.2 s hs).symm)
    (fun s hs => htail ⟨s, lt_of_le_of_lt htL hs, rfl⟩) hboundary
    (fun x hx => eventually_mem_of_isFreeAt (isFreeAt_of_lt hAc
      (fun y hy => (realBase_facts hp hp0).2.2.1 y hy |>.1) hx))
    (fun x hx => (realBase_facts hp hp0).2.2.1 x hx |>.1)
  exact Filter.Eventually.of_forall fun z hz => hAg hz

/-- The corrected physical side comparison in Lemma S5, without extra inputs. -/
theorem s5SideUpperStatement : S5SideUpperStatement :=
  s5SideUpperStatement_of_junction_interior s5JunctionGermStatement s5InteriorTransportStatement

/-- Lemma S5's main physical gluing statement, without extra inputs. -/
theorem s5Statement : S5Statement := s5Statement_of_sideUpper s5SideUpperStatement

end InteractingSLE.Theorem14.SB
