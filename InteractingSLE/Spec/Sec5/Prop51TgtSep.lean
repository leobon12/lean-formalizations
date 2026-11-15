/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51TgtGate
import InteractingSLE.Spec.Sec5.Prop51TgtCut

/-!
# The gate component of the chart: its bounding excursions, and its unbounded domain

Packet PROVE-PROP51-TGT (ruling R71; Astra's follow-up 4, §1.7 L377–L501). Fix a free positive gate of the counterflow
chart `Ψ = revChart w s` and the component `G` of `ℍ ∖ closure A` containing its half-ball (`A` the chart flow set, the
`Ψ`-image of the excursions of the proper flow arc `η` in `D = ℍ ∖ R(K_s)`). The excursions **adjacent** to `G` (whose
chart image meets the closure of `G`) are the ones whose current access lies in the original right-target component
(`Prop51Tgt.isTargetComp_of_mem_closure`). This file proves:

* `exists_west_of_adjacent`: under the first-exit barrier, the absence of a last contact and (E1) for target-component
  excursions, every adjacent excursion is bounded and finishes at a **negative** chart point — a positive finish is in
  `(0, junR]` (impossible, `Prop51H.not_hitsEast_finite_of_le_junR`), or on the eastern side proper after the seed
  (excluded by the first exit) or after a contact (an `IsEastCrosscut` whose restarted remainder is in the target
  component, excluded by (E1));
* `not_source_lt_start` (**the orientation step**, "the orientation forces an eastern endpoint"): an adjacent western
  crosscut does not start right of the gate — otherwise its loop winds once about `G`, which is on the right of `η`,
  while the local orientation at an adjacency point (`Prop51HGate.ExcursionChartCut.exists_local_const`) forces winding
  number `2` on its left side, against the Jordan curve theorem (`windNum_loop_eq_zero_or_one`);
* `mem_H_diff_fillH_adj` (**the separation step**): if every adjacent crosscut has both ends left of the gate, the
  gate half-ball is in the unbounded domain of their union (Janiszewski in `ℍ` for the finitely many crosscuts met by a
  segment to a far point, the rest of them through local finiteness);
* `false_of_not_isBounded`: an unbounded chart set on the right of `η` is impossible when the counterflow tip (the
  chart's `∞`) is on the left.

This replaces §1.7's outermost separator by the gate component itself: its bounding excursions are exactly the ones in
the target component, and the separation lemma is Janiszewski's theorem. Deterministic.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Prop51Tgt

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G Prop51HTopo Prop51HGate CrossCond.Word49
open _root_.InteractingSLE.Orientation
open HalfPlaneSep

variable {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}

/-! ### Adjacent excursions finish west -/

/-- A chart limit from the left at the end of an excursion is a cluster point along the excursion. -/
theorem mapClusterPt_of_tendsto_left {m b : ℝ} (hmb : m < b) (hD : ∀ v ∈ Ioo m b, η v ∈ H \ cfHullQ w s)
    {x : ℂ} (hlim : Tendsto (fun t => revChart w s (η t)) (𝓝[<] b) (𝓝 x)) :
    MapClusterPt x (𝓝[Ioo m b] b ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s}) (fun u => revChart w s (η u)) := by
  have heq : 𝓝[Ioo m b] b ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s} = 𝓝[Ioo m b] b :=
    inf_eq_left.2 (le_principal_iff.2 (mem_of_superset self_mem_nhdsWithin fun v hv => hD v hv))
  rw [heq, nhdsWithin_Ioo_eq_nhdsLT hmb]
  exact hlim.mapClusterPt

/-- **Every adjacent excursion is bounded and finishes at a negative chart point.** `htgt` is the target-component
property of the excursion's later points (`isTargetComp_of_mem_closure`); (E1) in target-component form, the first
exit and the absence of a last contact exclude the other finishes. -/
theorem exists_west_of_adjacent (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) (htip : negInv (β s) ∉ arcRange η) (h0 : FirstContactNotEast w s 0 η)
    (hnl : ∀ t : ℝ, ∃ v : ℝ, t < v ∧ η v ∉ H \ cfHullQ w s)
    (hE1 : ∀ t : ℚ, 0 < t → ∀ τ₀ ∈ Ioo (0 : ℝ) t, ∀ u₀ : ℝ, (t : ℝ) < u₀ →
      Aux61Loc.IsEastCrosscut w s η τ₀ u₀ → ∀ u ∈ Ioo (t : ℝ) u₀, ¬ Aux61Kernel.IsTargetComp w s η t (η u))
    {u : ℝ} (hu : u ∈ excursionTimes η w s)
    (htgt : ∀ t : ℝ, 0 ≤ t → t < u → Aux61Kernel.IsTargetComp w s η t (η u)) :
    ∃ e : BoundedExcursionInterval η w s u, ∃ xf : ℝ, xf < 0 ∧
      Tendsto (fun t => revChart w s (η t)) (𝓝[<] e.finish) (𝓝 (xf : ℂ)) := by
  obtain ⟨v, huv, hvD⟩ := hnl u
  have hb : BddAbove (connectedComponentIn (excursionTimes η w s) u) := by
    refine ⟨v, fun y hy => ?_⟩
    by_contra hyv
    push Not at hyv
    have hsub := (isPreconnected_connectedComponentIn (F := excursionTimes η w s) (x := u)).Icc_subset
      (mem_connectedComponentIn hu) hy
    have hvC : v ∈ connectedComponentIn (excursionTimes η w s) u := hsub ⟨huv.le, hyv.le⟩
    exact hvD (connectedComponentIn_subset _ _ hvC).2
  obtain ⟨e⟩ := exists_boundedExcursionInterval_of_bddAbove hη hw hs hu hb
  have hau : e.start < u := e.start_lt
  have hub : u < e.finish := e.lt_finish
  have hD := e.mapsTo
  have ha0 := e.start_nonneg
  set m := (e.start + e.finish) / 2 with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  have hmb : m < e.finish := by rw [hmdef]; linarith
  have hbtip : η e.finish ≠ negInv (β s) := fun h => htip ⟨e.finish, mem_Ici.2 (by linarith), h⟩
  have hDm : ∀ v ∈ Ioo m e.finish, η v ∈ H \ cfHullQ w s := fun t ht =>
    hD ⟨by rw [hmdef] at ht; linarith [ht.1], ht.2⟩
  obtain ⟨x, hx0, hlim⟩ := exists_tendsto_revChart_left hη hβ hw hw0 hs hm0 hmb
    (fun t ht => hD ⟨by rw [hmdef] at ht; linarith [ht.1], ht.2⟩) e.finish_outside hbtip
  refine ⟨e, x, ?_, hlim⟩
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · exact hneg
  exfalso
  have hcl := mapClusterPt_of_tendsto_left hmb hDm hlim
  rcases le_or_gt x (junR w s) with hxj | hxj
  · exact Prop51H.not_hitsEast_finite_of_le_junR hη hw hw0 hβ hs hm0.le hmb hpos hxj hcl
  rcases ha0.eq_or_lt with ha | ha
  · -- the first excursion: excluded by the first exit
    have hD0 : ∀ v ∈ Ioo 0 e.finish, η v ∈ H \ cfHullQ w s := fun t ht => hD ⟨by rw [← ha]; exact ht.1, ht.2⟩
    refine (h0 fun h => absurd h (lt_irrefl 0)).1 e.finish (by linarith) hD0 ⟨x, hpos, ?_⟩
    exact hcl.mono (inf_le_inf_right _ (nhdsWithin_mono _ (Ioo_subset_Ioo_left hm0.le)))
  · -- an eastern crosscut after a contact: excluded by (E1) at a rational restart before `u`
    obtain ⟨xs, hxs⟩ := exists_tendsto_revChart_start hη hβ hw hw0 hs htip ha0 (hau.trans hub) hD
      e.start_outside
    have hcross : Aux61Loc.IsEastCrosscut w s η e.start e.finish :=
      ⟨ha, hau.trans hub, e.start_outside, e.finish_outside, fun v hv => hD hv, Or.inl ⟨xs, hxs⟩, x, hxj,
        hlim⟩
    obtain ⟨q, haq, hqu⟩ := exists_rat_btwn hau
    exact hE1 q (by exact_mod_cast ha.trans haq) e.start ⟨ha, haq⟩ e.finish (hqu.trans hub) hcross u
      ⟨hqu, hub⟩ (htgt q (ha.trans haq).le hqu)

/-! ### The orientation step -/

/-- Near a chart flow point there are chart points off the chart flow set whose physical image is on the left of
`η`. -/
theorem exists_left_near (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {q : ℂ}
    (hq : q ∈ chartFlowSet η w s) {ε : ℝ} (hε : 0 < ε) :
    ∃ z' ∈ ball q ε, z' ∈ H ∧ z' ∉ chartFlowSet η w s ∧ revChartInv w s z' ∈ leftSideOf (arcRange η) := by
  obtain ⟨p, ⟨⟨u, hu0, rfl⟩, hpD⟩, rfl⟩ := hq
  have hupos : 0 < u := by
    rcases (mem_Ici.1 hu0).eq_or_lt with he | he
    · have hH := hpD.1
      rw [← he, hη.zero] at hH
      exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)).elim
    · exact he
  have hDo : IsOpen (H \ cfHullQ w s) := isOpen_H_diff_negInv_fwdHull hw hs
  have hcl : η u ∈ closure ((H \ cfHullQ w s) ∩ leftSideOf (arcRange η)) :=
    hDo.inter_closure ⟨hpD, hη.mem_closure_leftSideOf hupos⟩
  have hcont : ContinuousWithinAt (revChart w s) ((H \ cfHullQ w s) ∩ leftSideOf (arcRange η)) (η u) :=
    ((continuousOn_revChart hw hs) _ hpD).mono inter_subset_left
  obtain ⟨_, ⟨p', ⟨hp'D, hp'L⟩, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 (hcont.mem_closure_image hcl) ε hε
  refine ⟨revChart w s p', by rw [mem_ball, dist_comm]; exact hd, revChart_mem_H hw hs hp'D, ?_, ?_⟩
  · rintro ⟨p'', ⟨hp''A, hp''D⟩, he⟩
    have := injOn_revChart hw hw0 hs hp''D hp'D he
    exact hp'L.1.2 (this ▸ hp''A)
  · rwa [revChartInv_revChart hw hw0 hs hp'D]

/-- **The orientation step.** Let `G` be a preconnected chart set off the chart flow set, containing the gate
half-ball, whose physical image is on the right of `η`. A western crosscut `κ` adjacent to `G` (an interior point of
`κ` in the closure of `G`) does not start right of the gate. -/
theorem not_source_lt_start (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (g : PositiveBoundaryGate η w s) {G : Set ℂ} (hGc : IsPreconnected G) (hGA : G ⊆ H \ chartFlowSet η w s)
    (hGgate : ball (g.source : ℂ) g.radius ∩ H ⊆ G)
    (hGR : ∀ z ∈ G, revChartInv w s z ∈ rightSideOf (arcRange η)) {C : Set ℝ} (κ : ExcursionChartCut η w s C)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hcl : κ.cut t₀ ∈ closure G) : ¬ g.source < κ.start := by
  intro hxs
  have hfx : κ.finish < g.source := κ.finish_neg.trans g.source_pos
  have hγ := κ.continuousOn_loop
  have hl := κ.loop_closed
  set z₀ : ℂ := (g.source : ℂ) + ((g.radius / 2 : ℝ) : ℂ) * I with hz₀def
  have hz₀b : z₀ ∈ ball (g.source : ℂ) g.radius := by
    rw [mem_ball, dist_eq_norm, hz₀def, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith [g.radius_pos])]
    linarith [g.radius_pos]
  have hz₀H : z₀ ∈ H := by
    show (0 : ℝ) < ((g.source : ℂ) + ((g.radius / 2 : ℝ) : ℂ) * I).im
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
    linarith [g.radius_pos]
  have hz₀1 := windNum_loop_eq_one_of_gate κ hw hs g.radius_pos g.avoids hfx hxs hz₀b hz₀H
  have hGd : Disjoint G (κ.loop '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun v hv hvl => ?_
    obtain ⟨t, ht, rfl⟩ := hvl
    obtain ⟨u', hu', he⟩ := κ.exists_of_loop_mem_H ht (hGA hv).1
    exact (hGA hv).2 (he ▸ κ.cut_mem_chartFlowSet hu')
  have hG1 : ∀ z ∈ G, windNum κ.loop z = 1 := fun z hz =>
    (windNum_eq_of_isPreconnected hγ hl hGc hGd hz (hGgate ⟨hz₀b, hz₀H⟩)).trans hz₀1
  obtain ⟨ε, hε, hconst⟩ := κ.exists_local_const hη hw hw0 hs ht₀
  obtain ⟨z, hzG, hzd⟩ := Metric.mem_closure_iff.1 hcl ε hε
  obtain ⟨z', hz'b, hz'H, hz'A, hz'L⟩ := exists_left_near hη hw hw0 hs (κ.cut_mem_chartFlowSet ht₀) hε
  have hzb : z ∈ ball (κ.cut t₀) ε := by rw [mem_ball, dist_comm]; exact hzd
  have h := hconst z hzb z' hz'b (hGA hzG).1 hz'H (hGA hzG).2 hz'A
  have hr0 : windNum (flowReferenceLoop η) (discRevChart w s z) = 0 :=
    windNum_flowReferenceLoop_of_mem_right hη (hGR z hzG)
  have hr1 : windNum (flowReferenceLoop η) (discRevChart w s z') = 1 :=
    windNum_flowReferenceLoop_of_mem_left hη hz'L
  rw [hr0, hr1, hG1 z hzG] at h
  rcases windNum_loop_eq_zero_or_one κ hη hw hw0 hs g.radius_pos g.avoids hfx hxs hz'H hz'A with h' | h' <;>
    · rw [h'] at h; norm_num at h

/-! ### An unbounded chart set on the right is impossible -/

/-- **The chart's `∞` is the counterflow tip**: if the tip is on the left of `η`, no unbounded chart set has its
physical image on the right of `η`. -/
theorem false_of_not_isBounded (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) (hβs : β s ≠ 0) (hL : negInv (β s) ∈ leftSideOf (arcRange η)) {G : Set ℂ}
    (hGH : G ⊆ H) (hGR : ∀ z ∈ G, revChartInv w s z ∈ rightSideOf (arcRange η)) (hGu : ¬ IsBounded G) :
    False := by
  have hlim := tendsto_revChartInv_tip hβ hw hw0 hs hβs (l := Bornology.cobounded ℂ ⊓ 𝓟 H)
    (f := fun z => z) (mem_inf_of_right (mem_principal_self H))
    (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
  have hev : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 H, revChartInv w s z ∈ leftSideOf (arcRange η) :=
    hlim.eventually ((Cond44Ref.isOpen_leftSideOf_arcRange hη).mem_nhds hL)
  rw [Filter.eventually_inf_principal] at hev
  have hfr : ∃ᶠ z in Bornology.cobounded ℂ, z ∈ G := fun h => hGu (Bornology.isBounded_def.2 h)
  obtain ⟨z, hzG, hz⟩ := (hfr.and_eventually hev).exists
  exact Set.disjoint_left.1 hη.disjoint_leftSideOf_rightSideOf (hz (hGH hzG)) (hGR z hzG)

/-! ### The separation step -/

/-- The unbounded domain is antitone in the closed set. -/
theorem mem_H_diff_fillH_mono {F F' : Set ℂ} (hF : IsClosed F) (hF' : IsClosed F') (hsub : F ⊆ F') {z : ℂ}
    (hz : z ∈ H \ fillH F') : z ∈ H \ fillH F := by
  have h := (mem_H_diff_fillH_of_isClosed hF').1 hz
  refine subset_H_diff_fillH_of_not_isBounded hF isPreconnected_connectedComponentIn h.2
    (fun v hv => ?_) (mem_connectedComponentIn h.1)
  have := connectedComponentIn_subset _ _ hv
  exact ⟨this.1, fun hvF => this.2 (hsub hvF)⟩

section Family

variable {𝒜 : Set (Set ℝ)} {Fc : Set ℝ → Set ℂ}

/-- **Local finiteness of completed crosscuts**: a point of `ℍ` in the closure of the union of the completed
crosscuts of a family of excursions lies on one of them. -/
theorem exists_mem_of_mem_closure_iUnion (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (h𝒜 : ∀ C ∈ 𝒜, ∃ u ∈ excursionTimes η w s, C = connectedComponentIn (excursionTimes η w s) u)
    (hFc : ∀ C ∈ 𝒜, ∃ κ : ExcursionChartCut η w s C, Fc C = κ.cut '' Icc 0 1) {𝒜' : Set (Set ℝ)}
    (h𝒜' : 𝒜' ⊆ 𝒜) {z : ℂ} (hzH : z ∈ H) (hz : z ∈ closure (⋃ C ∈ 𝒜', Fc C)) : ∃ C ∈ 𝒜', z ∈ Fc C := by
  set ρ : ℝ := z.im / 2 with hρdef
  have hz0 : 0 < z.im := hzH
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  set N := closedBall z ρ with hNdef
  have hNH : N ⊆ H := fun y hy => by
    have h1 : |(y - z).im| ≤ ‖y - z‖ := abs_im_le_norm _
    rw [← dist_eq_norm] at h1
    have h2 := mem_closedBall.1 hy
    simp only [sub_im] at h1
    show (0 : ℝ) < y.im
    have := (abs_le.1 (h1.trans h2)).1
    rw [hρdef] at this
    linarith
  set E := (fun t => connectedComponentIn (excursionTimes η w s) t) ''
    (Ici 0 ∩ η ⁻¹' (revChartInv w s '' N)) with hEdef
  have hE : E.Finite := finite_excursions_meeting_chart_compact hη hw hw0 hs (isCompact_closedBall z ρ) hNH
  have hsub : (⋃ C ∈ 𝒜', Fc C) ∩ ball z ρ ⊆ ⋃ C ∈ 𝒜' ∩ E, Fc C := by
    rintro y ⟨hy, hyb⟩
    obtain ⟨C, hC, hyC⟩ := mem_iUnion₂.1 hy
    refine mem_iUnion₂.2 ⟨C, ⟨hC, ?_⟩, hyC⟩
    obtain ⟨κ, hκ⟩ := hFc C (h𝒜' hC)
    rw [hκ] at hyC
    obtain ⟨t, ht, rfl⟩ := hyC
    have hyH : κ.cut t ∈ H := hNH (ball_subset_closedBall hyb)
    have ht' := mem_Ioo_of_cut_mem_H κ ht hyH
    obtain ⟨u, -, hCu⟩ := h𝒜 C (h𝒜' hC)
    refine ⟨κ.time t, ⟨mem_Ici.2 (κ.time_pos ht').le, κ.cut t, ball_subset_closedBall hyb, ?_⟩, ?_⟩
    · exact κ.revChartInv_cut hw hw0 hs ht'
    · have hm : κ.time t ∈ connectedComponentIn (excursionTimes η w s) u := hCu.subset (κ.time_mem ht')
      exact (connectedComponentIn_eq hm).symm.trans hCu.symm
  have hclosed : IsClosed (⋃ C ∈ 𝒜' ∩ E, Fc C) := by
    refine (hE.subset inter_subset_right).isClosed_biUnion fun C hC => ?_
    obtain ⟨κ, hκ⟩ := hFc C (h𝒜' hC.1)
    rw [hκ]
    exact (isCompact_Icc.image_of_continuousOn κ.cont).isClosed
  have hzcl : z ∈ closure (⋃ C ∈ 𝒜' ∩ E, Fc C) := by
    rw [Metric.mem_closure_iff] at hz ⊢
    intro ε hε
    obtain ⟨y, hy, hyd⟩ := hz (min ε ρ) (lt_min hε hρ)
    exact ⟨y, hsub ⟨hy, by rw [mem_ball, dist_comm]; exact hyd.trans_le (min_le_right _ _)⟩,
      hyd.trans_le (min_le_left _ _)⟩
  rw [hclosed.closure_eq] at hzcl
  obtain ⟨C, hC, hzC⟩ := mem_iUnion₂.1 hzcl
  exact ⟨C, hC.1, hzC⟩

/-- **The separation step** (Janiszewski): if every completed crosscut of a family of excursions has both ends left
of a free gate, the gate half-ball is in the unbounded domain of the closure of their union. -/
theorem mem_H_diff_fillH_adj (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {x₀ r : ℝ}
    (hr : 0 < r) (havoid : ball (x₀ : ℂ) r ∩ closure (chartFlowSet η w s) = ∅) {R : ℝ} (hR0 : 0 < R)
    (hR : closure (chartFlowSet η w s) ⊆ ball 0 R)
    (h𝒜 : ∀ C ∈ 𝒜, ∃ u ∈ excursionTimes η w s, C = connectedComponentIn (excursionTimes η w s) u)
    (hFc : ∀ C ∈ 𝒜, ∃ κ : ExcursionChartCut η w s C,
      Fc C = κ.cut '' Icc 0 1 ∧ κ.start < x₀ ∧ κ.finish < x₀)
    {w₀ : ℂ} (hw₀b : w₀ ∈ ball (x₀ : ℂ) r) (hw₀H : w₀ ∈ H) :
    w₀ ∈ H \ fillH (closure (⋃ C ∈ 𝒜, Fc C)) := by
  classical
  have hFc' : ∀ C ∈ 𝒜, ∃ κ : ExcursionChartCut η w s C, Fc C = κ.cut '' Icc 0 1 := fun C hC => by
    obtain ⟨κ, h, -⟩ := hFc C hC
    exact ⟨κ, h⟩
  have hFcA : ∀ C ∈ 𝒜, Fc C ⊆ closure (chartFlowSet η w s) := fun C hC => by
    obtain ⟨κ, h, -⟩ := hFc C hC
    rw [h]
    exact κ.image_cut_subset_closure
  have hFcc : ∀ C ∈ 𝒜, IsCompact (Fc C) := fun C hC => by
    obtain ⟨κ, h, -⟩ := hFc C hC
    rw [h]
    exact isCompact_Icc.image_of_continuousOn κ.cont
  -- the segment to a far point
  set w₁ : ℂ := ((R + 1 : ℝ) : ℂ) * I with hw₁def
  have hw₁H : w₁ ∈ H := by
    show (0 : ℝ) < (((R + 1 : ℝ) : ℂ) * I).im
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith
  have hw₁n : R ≤ ‖w₁‖ := by
    rw [hw₁def, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  let σ : ℝ → ℂ := fun t => w₀ + (t : ℂ) * (w₁ - w₀)
  have hσc : Continuous σ := by fun_prop
  set K := σ '' Icc 0 1 with hKdef
  have hKc : IsCompact K := isCompact_Icc.image hσc
  have hKH : K ⊆ H := by
    rintro _ ⟨t, ht, rfl⟩
    have ha : (0 : ℝ) < w₀.im := hw₀H
    have hb : (0 : ℝ) < w₁.im := hw₁H
    show (0 : ℝ) < (w₀ + (t : ℂ) * (w₁ - w₀)).im
    simp only [add_im, mul_im, ofReal_re, sub_im, ofReal_im, sub_re, zero_mul, add_zero]
    nlinarith [mul_nonneg ht.1 (sub_nonneg.2 (min_le_right w₀.im w₁.im)),
      mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 (min_le_left w₀.im w₁.im)), lt_min ha hb]
  have hw₀K : w₀ ∈ K := ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [σ]⟩
  have hw₁K : w₁ ∈ K := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [σ]⟩
  -- the finitely many excursions met by the segment
  set Eσ := (fun t => connectedComponentIn (excursionTimes η w s) t) ''
    (Ici 0 ∩ η ⁻¹' (revChartInv w s '' K)) with hEσdef
  have hEσ : Eσ.Finite := finite_excursions_meeting_chart_compact hη hw hw0 hs hKc hKH
  set S := Eσ ∩ 𝒜 with hSdef
  have hSf : S.Finite := hEσ.subset inter_subset_left
  set Sf := hSf.toFinset with hSfdef
  have hmemSf : ∀ C, C ∈ Sf ↔ C ∈ S := fun C => Set.Finite.mem_toFinset hSf
  -- the remaining excursions
  set T := closure (⋃ C ∈ 𝒜 \ S, Fc C) with hTdef
  have hTA : T ⊆ closure (chartFlowSet η w s) :=
    closure_minimal (iUnion₂_subset fun C hC => hFcA C hC.1) isClosed_closure
  have hTc : IsCompact T :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure ((isBounded_ball).subset (hTA.trans hR))
  have hKT : ∀ z ∈ K, z ∉ T := by
    intro z hzK hzT
    obtain ⟨C, hC, hzC⟩ := exists_mem_of_mem_closure_iUnion hη hw hw0 hs h𝒜 hFc' sdiff_subset (hKH hzK) hzT
    obtain ⟨κ, hκ⟩ := hFc' C hC.1
    rw [hκ] at hzC
    obtain ⟨t, ht, rfl⟩ := hzC
    have ht' := mem_Ioo_of_cut_mem_H κ ht (hKH hzK)
    obtain ⟨u, -, hCu⟩ := h𝒜 C hC.1
    apply hC.2
    refine ⟨⟨κ.time t, ⟨mem_Ici.2 (κ.time_pos ht').le, κ.cut t, hzK, κ.revChartInv_cut hw hw0 hs ht'⟩, ?_⟩,
      hC.1⟩
    have hm : κ.time t ∈ connectedComponentIn (excursionTimes η w s) u := hCu.subset (κ.time_mem ht')
    exact (connectedComponentIn_eq hm).symm.trans hCu.symm
  have hw₀T : w₀ ∈ H \ fillH T := by
    have hw₁T : w₁ ∈ H \ fillH T :=
      mem_H_diff_fillH_of_le_norm isClosed_closure hR0 (hTA.trans hR) hw₁H hw₁n
    have hKsub : K ⊆ connectedComponentIn (H \ T) w₁ :=
      (isPreconnected_Icc.image σ hσc.continuousOn).subset_connectedComponentIn hw₁K
        fun z hz => ⟨hKH hz, hKT z hz⟩
    exact connectedComponentIn_subset_H_diff_fillH isClosed_closure hw₁T (hKsub hw₀K)
  -- Janiszewski over the finitely many
  have hreal : ∀ C ∈ 𝒜, ∀ v ∈ Fc C, v ∉ H → v.im = 0 := by
    intro C hC v hv hvH
    obtain ⟨κ, h, -⟩ := hFc C hC
    rw [h] at hv
    obtain ⟨t, ht, rfl⟩ := hv
    exact le_antisymm (not_lt.1 hvH) (cut_im_nonneg κ hw hs ht)
  have hFF : ∀ i ∈ Sf, ∀ j ∈ Sf, i ≠ j → ∀ v ∈ Fc i ∩ Fc j, v.im = 0 := by
    intro i hi j hj hij v hv
    have hi' := ((hmemSf i).1 hi).2
    have hj' := ((hmemSf j).1 hj).2
    obtain ⟨κ, hκ⟩ := hFc' i hi'
    obtain ⟨κ', hκ'⟩ := hFc' j hj'
    rw [hκ] at hv
    have hv2 := hv.2
    rw [hκ'] at hv2
    exact im_eq_zero_of_mem_cut_inter hη hw hw0 hs κ κ' (h𝒜 i hi') (h𝒜 j hj') hij hv.1 hv2
  have hTF : ∀ i ∈ Sf, ∀ v ∈ Fc i ∩ T, v.im = 0 := by
    intro i hi v hv
    have hi' := (hmemSf i).1 hi
    by_cases hvH : v ∈ H
    · obtain ⟨C, hC, hvC⟩ := exists_mem_of_mem_closure_iUnion hη hw hw0 hs h𝒜 hFc' sdiff_subset hvH hv.2
      have hne : i ≠ C := fun h => hC.2 (h ▸ hi')
      obtain ⟨κ, hκ⟩ := hFc' i hi'.2
      obtain ⟨κ', hκ'⟩ := hFc' C hC.1
      have hv1 := hv.1
      rw [hκ] at hv1
      rw [hκ'] at hvC
      exact im_eq_zero_of_mem_cut_inter hη hw hw0 hs κ κ' (h𝒜 i hi'.2) (h𝒜 C hC.1) hne hv1 hvC
    · exact hreal i hi'.2 v hv.1 hvH
  have hzF : ∀ i ∈ Sf, w₀ ∈ H \ fillH (Fc i) := by
    intro i hi
    obtain ⟨κ, h, hst, hfi⟩ := hFc i ((hmemSf i).1 hi).2
    rw [h]
    exact mem_H_diff_fillH_of_gate κ hw hs hr havoid hst hfi hw₀b hw₀H
  have hJ := mem_H_diff_fillH_union Sf hTc (fun i hi => hFcc i ((hmemSf i).1 hi).2) hTF hFF hw₀T hzF
  -- the whole family is covered
  have hcover : closure (⋃ C ∈ 𝒜, Fc C) ⊆ T ∪ ⋃ i ∈ Sf, Fc i := by
    refine closure_minimal ?_ (isClosed_closure.union ?_)
    · refine iUnion₂_subset fun C hC => ?_
      by_cases hCS : C ∈ S
      · exact subset_union_of_subset_right (subset_biUnion_of_mem (u := Fc) ((hmemSf C).2 hCS)) _
      · exact subset_union_of_subset_left
          ((subset_biUnion_of_mem (u := Fc) (show C ∈ 𝒜 \ S from ⟨hC, hCS⟩)).trans subset_closure) _
    · exact isClosed_biUnion_finset fun i hi => (hFcc i ((hmemSf i).1 hi).2).isClosed
  exact mem_H_diff_fillH_mono isClosed_closure
    (isClosed_closure.union (isClosed_biUnion_finset fun i hi => (hFcc i ((hmemSf i).1 hi).2).isClosed))
    hcover hJ

end Family

end InteractingSLE.Sec5.Prop51Tgt
