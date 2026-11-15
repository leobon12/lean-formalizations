/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterGeomSub

/-!
# Theorem R.7's mixed pockets opening at the flow seed: Aux. lemma 37 along the contained arm

Packet PROVE-R7-OUTERGEOM. The pathwise transfer of `OuterGeomSub` for a mixed pocket whose arms open at the flow seed
(`rightLo = 0`; the last-visit attachment `R7StopIn.BarrierAttachConstInf` along the contained arm read from `y₀`
towards `∞`). The extremal sub-pockets of the contained arm with the certified frontier `M` may be bounded or open at
the flow seed themselves:

* `cfPocket_subset_of_sub'`, `cfPocket_subset_of_subL'`: nesting for pockets bounded or not (the general form of
  `OuterGeomSub`'s, from the `M`-clipping of the outer pocket);
* `false_of_progress`, `false_of_progressInf`: the timing step — two new points of a sub-pocket's contained arc make
  its first-visit (resp. last-visit) attachment move on a no-sub-pocket interval;
* **`barrierAttachConstInf_right_of_sub`** (outer left arm), **`barrierAttachConstInf_left_of_sub`** (outer right
  arm).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal

namespace InteractingSLE.Sec7.OuterGeom

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

section SubInf

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- A change pocket is connected in the counterflow chart, bounded or not. -/
theorem isPreconnected_cfPocket (h : IsChangeConfigInc R L r) : IsPreconnected (cfPocket R L r) := by
  rcases (h.changeCorner_props.1.1).lt_or_eq with hb | hb
  · exact (h.isCfPocket (PocketMarks.zero_notMem_closure_of_rightLo_pos h hb)).isConnected.isPreconnected
  · exact (h.isCfPocketInf hb.symm).isConnected.isPreconnected

/-- A point of the left arc of a change pocket, read at a disc time strictly between its corners, is in the closure
of the pocket, bounded or not. -/
theorem cfPt_left_mem_closure (h : IsChangeConfigInc R L r) {s : ℝ}
    (hs : s ∈ Ioo (leftLo R L r) (leftHi R L r)) :
    cfPt (toDisc (Lemma71I.realPath L) s) ∈ closure (cfPocket R L r) := by
  obtain ⟨-, -, -, hla, hlb, hll, -⟩ := h.changeCorner_props
  refine frontier_subset_closure ?_
  rcases (h.changeCorner_props.1.1).lt_or_eq with hb | hb
  · have hC := h.isCfPocket (PocketMarks.zero_notMem_closure_of_rightLo_pos h hb)
    have hΔ : 0 < leftHi R L r - leftLo R L r := sub_pos.2 hll
    rw [hC.frontier_eq]
    refine Or.inr ⟨(s - leftLo R L r) / (leftHi R L r - leftLo R L r), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (sub_nonneg.2 hs.1.le) hΔ.le
    · rw [div_le_one hΔ]; linarith [hs.2]
    · simp only [cfArcL]; congr 2; field_simp; ring
  · have hC := h.isCfPocketInf hb.symm
    have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero hb.symm
    rw [ha0] at hs
    rw [hC.frontier_eq]
    refine Or.inr ⟨leftHi R L r / s - 1, ?_, ?_⟩
    · rw [mem_Ici, sub_nonneg, le_div_iff₀ hs.1, one_mul]; exact hs.2.le
    · have hne : leftHi R L r ≠ 0 := (hs.1.trans hs.2).ne'
      simp only [cfArcLInf]; congr 2; rw [add_sub_cancel]; field_simp

/-- A point of the right arc of a change pocket, read at a disc time strictly between its corners, is in the closure
of the pocket, bounded or not. -/
theorem cfPt_right_mem_closure (h : IsChangeConfigInc R L r) {s : ℝ}
    (hs : s ∈ Ioo (rightLo R L r) (rightHi R L r)) :
    cfPt (toDisc (Lemma71I.realPath R) s) ∈ closure (cfPocket R L r) := by
  obtain ⟨hra, hrb, hrr, -⟩ := h.changeCorner_props
  refine frontier_subset_closure ?_
  rcases hra.1.lt_or_eq with hb | hb
  · have hC := h.isCfPocket (PocketMarks.zero_notMem_closure_of_rightLo_pos h hb)
    have hΔ : 0 < rightHi R L r - rightLo R L r := sub_pos.2 hrr
    rw [hC.frontier_eq]
    refine Or.inl ⟨(s - rightLo R L r) / (rightHi R L r - rightLo R L r), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (sub_nonneg.2 hs.1.le) hΔ.le
    · rw [div_le_one hΔ]; linarith [hs.2]
    · simp only [cfArcR]; congr 2; field_simp; ring
  · have hC := h.isCfPocketInf hb.symm
    rw [← hb] at hs
    rw [hC.frontier_eq]
    refine Or.inl ⟨rightHi R L r / s - 1, ?_, ?_⟩
    · rw [mem_Ici, sub_nonneg, le_div_iff₀ hs.1, one_mul]; exact hs.2.le
    · have hne : rightHi R L r ≠ 0 := (hs.1.trans hs.2).ne'
      simp only [cfArcRInf]; congr 2; rw [add_sub_cancel]; field_simp

/-- Every frontier point of a change pocket opening at the flow seed is a counterflow-chart point of one of its
walls. -/
theorem frontier_cfPocketInf_mem (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) {z : ℂ}
    (hz : z ∈ frontier (cfPocket R L r)) :
    ∃ p : ℝ, cfPt (toDisc (Lemma71I.realPath R) p) = z ∨ cfPt (toDisc (Lemma71I.realPath L) p) = z := by
  rw [(h.isCfPocketInf h0).frontier_eq] at hz
  rcases hz with ⟨v, -, hv⟩ | ⟨v, -, hv⟩
  · exact ⟨_, Or.inl hv⟩
  · exact ⟨_, Or.inr hv⟩

/-- Every frontier point of a bounded change pocket is a counterflow-chart point of one of its walls. -/
theorem frontier_cfPocket_mem (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) {z : ℂ}
    (hz : z ∈ frontier (cfPocket R L r)) :
    ∃ p : ℝ, cfPt (toDisc (Lemma71I.realPath R) p) = z ∨ cfPt (toDisc (Lemma71I.realPath L) p) = z := by
  rw [(h.isCfPocket (PocketMarks.zero_notMem_closure_of_rightLo_pos h hb)).frontier_eq] at hz
  rcases hz with ⟨v, -, hv⟩ | ⟨v, -, hv⟩
  · exact ⟨_, Or.inl hv⟩
  · exact ⟨_, Or.inr hv⟩

/-- Every frontier point of a change pocket (bounded or not) is a counterflow-chart point of one of its walls. -/
theorem frontier_cfPocket_mem' (h : IsChangeConfigInc R L r) {z : ℂ} (hz : z ∈ frontier (cfPocket R L r)) :
    ∃ p : ℝ, cfPt (toDisc (Lemma71I.realPath R) p) = z ∨ cfPt (toDisc (Lemma71I.realPath L) p) = z := by
  rcases (h.changeCorner_props.1.1).lt_or_eq with hb | hb
  · exact frontier_cfPocket_mem h hb hz
  · exact frontier_cfPocketInf_mem h hb.symm hz

/-- The pocket of a change configuration is open, bounded or not. -/
theorem isOpen_cfPocket (h : IsChangeConfigInc R L r) : IsOpen (cfPocket R L r) := by
  rcases (h.changeCorner_props.1.1).lt_or_eq with hb | hb
  · exact (h.isCfPocket (PocketMarks.zero_notMem_closure_of_rightLo_pos h hb)).isOpen
  · exact (h.isCfPocketInf hb.symm).isOpen

/-- **Nested pockets, general form** (`cfPocket_subset_of_sub` for pockets bounded or opening at the flow seed): a
pocket of `(R, M)` whose left (`M`) arc lies in the `M`-clipping of the pocket of `(R, L)` lies in that pocket, when
`L` is outer beyond `M`. -/
theorem cfPocket_subset_of_sub' (h : IsChangeConfigInc R L r) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcL : NoCommonArc M L) (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {r' : ℝ≥0} (h' : IsChangeConfigInc R M r') {σM τM : ℝ}
    (hin : ∀ t ∈ Icc σM τM, toDisc (Lemma71I.realPath M) t ∈ closure (cayley '' changePocket R L r))
    (hσl : σM ≤ leftLo R M r') (hlτ : leftHi R M r' ≤ τM) : cfPocket R M r' ⊆ cfPocket R L r := by
  have hαR := h.right.isProperArc.isDiscCrosscut_toDisc
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hO' : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath M) :=
    ⟨hO.right, hO.middle, hO.middle, hO.right_middle, Set.disjoint_left.2 fun _ hz hr => hr.1.2 hz⟩
  have hC'r : changePocket R M r' ⊆ rightSideOf (range M) := R7FaceSelect.changePocket_subset_right_of_order h' hO'
  have hCo := isOpen_cfPocket h
  refine Sec6.subset_of_isPreconnected_of_disjoint_frontier (isPreconnected_cfPocket h') hCo ?_ ?_
  · obtain ⟨hg', hj1, hj2, -⟩ := h'.changeCorners
    obtain ⟨-, -, -, hla, hlb, hll, -⟩ := h'.changeCorner_props
    obtain ⟨hgM, -, -⟩ := isContactGap_swap' hαR hαM h'.inc hg'
    rw [hj1, hj2] at hgM
    obtain ⟨t, ht0, hts, htL⟩ := exists_discTime_notMem hcL hla.1 hll hlb.2
    set s := discTime (t : ℝ) with hs
    have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hla.1.trans_lt hts.1, hts.2.trans_le hlb.2⟩
    have hsR : toDisc (Lemma71I.realPath M) s ∉ crossRange (toDisc (Lemma71I.realPath R)) :=
      fun hmem => hgM.2.2.2 s hts ⟨⟨hsI.1.le, hsI.2.le⟩, hmem⟩
    rw [toDisc_mem_crossRange_iff hM h.right hsI, hs, arcTime_discTime ht0.le, Real.toNNReal_coe] at hsR
    have hP := cfPt_toDisc_discTime hM ht0
    rw [Real.toNNReal_coe] at hP
    have hMH : M t ∈ H := hM.2.2.2.1 t (by exact_mod_cast ht0)
    have hPcl : cfPt (toDisc (Lemma71I.realPath M) s) ∈ closure (cfPocket R L r) :=
      cfPt_mem_closure h (hin s ⟨hσl.trans hts.1.le, hts.2.le.trans hlτ⟩) (toDisc_ne_neg_one hM ⟨hsI.1, hsI.2.le⟩)
    have hPC : cfPt (toDisc (Lemma71I.realPath M) s) ∈ cfPocket R L r := by
      by_contra hPC
      have hfr : cfPt (toDisc (Lemma71I.realPath M) s) ∈ frontier (cfPocket R L r) :=
        ⟨hPcl, by rwa [hCo.interior_eq]⟩
      obtain ⟨p, hp | hp⟩ := frontier_cfPocket_mem' h hfr
      · rw [hP] at hp; exact hsR (mem_range_of_cfPt_toDisc h.right hMH hp)
      · rw [hP] at hp; exact htL (mem_range_of_cfPt_toDisc h.left hMH hp)
    obtain ⟨z, hz⟩ := mem_closure_iff.1 (cfPt_left_mem_closure h' hts) _ hCo hPC
    exact ⟨z, hz.2, hz.1⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hz
    have hw' := h'.changePocket_subset hw
    obtain ⟨p, hp | hp⟩ := frontier_cfPocket_mem' h hz
    · exact hw'.2 (Or.inl (mem_range_of_cfPt_toDisc h.right hw'.1 hp))
    · rcases houter (mem_range_of_cfPt_toDisc h.left hw'.1 hp) with hl | hm
      · have hd := (hM.isProperArc).disjoint_leftSideOf_rightSideOf
        rw [arcRange_realPath] at hd
        exact Set.disjoint_left.1 hd hl (hC'r hw)
      · exact hw'.2 (Or.inr hm)

/-- **Nested pockets, mirror, general form** (`cfPocket_subset_of_subL` for pockets bounded or opening at the flow
seed). -/
theorem cfPocket_subset_of_subL' (h : IsChangeConfigInc R L r) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {r' : ℝ≥0} (h' : IsChangeConfigInc M L r') {σM τM : ℝ}
    (hin : ∀ t ∈ Icc σM τM, toDisc (Lemma71I.realPath M) t ∈ closure (cayley '' changePocket R L r))
    (hσl : σM ≤ rightLo M L r') (hlτ : rightHi M L r' ≤ τM) : cfPocket M L r' ⊆ cfPocket R L r := by
  have hO' : WangWu.IsOrderedArcs (Lemma71I.realPath M) (Lemma71I.realPath M) (Lemma71I.realPath L) :=
    ⟨hO.middle, hO.middle, hO.left, Set.disjoint_left.2 fun _ hz hr => hr.1.2 hz, hO.middle_left⟩
  have hC'l : changePocket M L r' ⊆ leftSideOf (range M) := R7FaceSelect.changePocket_subset_left_of_order h' hO'
  have hCo := isOpen_cfPocket h
  refine Sec6.subset_of_isPreconnected_of_disjoint_frontier (isPreconnected_cfPocket h') hCo ?_ ?_
  · obtain ⟨hg', -⟩ := h'.changeCorners
    obtain ⟨hm1, hm2, hmm, -⟩ := h'.changeCorner_props
    obtain ⟨t, ht0, hts, htR⟩ := exists_discTime_notMem hcR hm1.1 hmm hm2.2
    set s := discTime (t : ℝ) with hs
    have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hm1.1.trans_lt hts.1, hts.2.trans_le hm2.2⟩
    have hsL : toDisc (Lemma71I.realPath M) s ∉ crossRange (toDisc (Lemma71I.realPath L)) :=
      fun hmem => hg'.2.2.2 s hts ⟨⟨hsI.1.le, hsI.2.le⟩, hmem⟩
    rw [toDisc_mem_crossRange_iff hM h.left hsI, hs, arcTime_discTime ht0.le, Real.toNNReal_coe] at hsL
    have hP := cfPt_toDisc_discTime hM ht0
    rw [Real.toNNReal_coe] at hP
    have hMH : M t ∈ H := hM.2.2.2.1 t (by exact_mod_cast ht0)
    have hPcl : cfPt (toDisc (Lemma71I.realPath M) s) ∈ closure (cfPocket R L r) :=
      cfPt_mem_closure h (hin s ⟨hσl.trans hts.1.le, hts.2.le.trans hlτ⟩) (toDisc_ne_neg_one hM ⟨hsI.1, hsI.2.le⟩)
    have hPC : cfPt (toDisc (Lemma71I.realPath M) s) ∈ cfPocket R L r := by
      by_contra hPC
      have hfr : cfPt (toDisc (Lemma71I.realPath M) s) ∈ frontier (cfPocket R L r) :=
        ⟨hPcl, by rwa [hCo.interior_eq]⟩
      obtain ⟨p, hp | hp⟩ := frontier_cfPocket_mem' h hfr
      · rw [hP] at hp; exact htR (mem_range_of_cfPt_toDisc h.right hMH hp)
      · rw [hP] at hp; exact hsL (mem_range_of_cfPt_toDisc h.left hMH hp)
    obtain ⟨z, hz⟩ := mem_closure_iff.1 (cfPt_right_mem_closure h' hts) _ hCo hPC
    exact ⟨z, hz.2, hz.1⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hz
    have hw' := h'.changePocket_subset hw
    obtain ⟨p, hp | hp⟩ := frontier_cfPocket_mem' h hz
    · rcases houter (mem_range_of_cfPt_toDisc h.right hw'.1 hp) with hr | hm
      · have hd := (hM.isProperArc).disjoint_leftSideOf_rightSideOf
        rw [arcRange_realPath] at hd
        exact Set.disjoint_left.1 hd (hC'l hw) hr
      · exact hw'.2 (Or.inl hm)
    · exact hw'.2 (Or.inr (mem_range_of_cfPt_toDisc h.left hw'.1 hp))

end SubInf

section Progress

variable {X : ℝ≥0 → ℂ} {η : ℝ → ℂ}

/-- **No attachment progress in a bounded sub-pocket, contradicted** (the timing step of the transfer): if two points
`p₀ < p` of the open arc `[p₁, p₂]` of a reverse-visited wall `X` are first visited during `(a, b]` while `η` avoids
`C'`, the first-visit attachment along that arc moves on a no-`C'` subinterval of `[τ', σ')`. -/
theorem false_of_progress (hX : IsSimpleProper X) (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit X η) (hvis : IsWallVisited X η) {C' : Set ℂ} {p₁ p₂ : ℝ} (hp₁ : 0 < p₁)
    (hp₂ : p₂ ≤ 1)
    (hAC : BarrierAttachConst η C' (fun s => cfPt (toDisc (Lemma71I.realPath X) (p₁ + s * (p₂ - p₁))))
      (firstHit η (cfPt (toDisc (Lemma71I.realPath X) p₂))) (firstHit η (cfPt (toDisc (Lemma71I.realPath X) p₁))))
    {a b p₀ p : ℝ} (hp₀ : p₁ < p₀) (hp₀p : p₀ < p) (hp : p < p₂)
    (hpb : cfPt (toDisc (Lemma71I.realPath X) p) ∈ η '' Icc 0 b)
    (hpa : cfPt (toDisc (Lemma71I.realPath X) p) ∉ η '' Icc 0 a)
    (hp₀b : cfPt (toDisc (Lemma71I.realPath X) p₀) ∈ η '' Icc 0 b) (havoid : ∀ t ∈ Icc a b, η t ∉ C') : False := by
  set Q : ℝ → ℂ := fun ρ => cfPt (toDisc (Lemma71I.realPath X) ρ) with hQ
  have hQinj := cfPt_toDisc_injOn hX
  have hIp : p ∈ Ioc (0 : ℝ) 1 := ⟨hp₁.trans (hp₀.trans hp₀p), (hp.trans_le hp₂).le⟩
  have hIp₀ : p₀ ∈ Ioc (0 : ℝ) 1 := ⟨hp₁.trans hp₀, (hp₀p.trans (hp.trans_le hp₂)).le⟩
  have hIp₁ : p₁ ∈ Ioc (0 : ℝ) 1 := ⟨hp₁, (hp₀.trans (hp₀p.trans (hp.trans_le hp₂))).le⟩
  have hIp₂ : p₂ ∈ Ioc (0 : ℝ) 1 := ⟨hIp.1.trans hp, hp₂⟩
  have hpb' : Q p ∈ η '' Icc 0 b := hpb
  have hp₀b' : Q p₀ ∈ η '' Icc 0 b := hp₀b
  obtain ⟨htp0, htp, -⟩ := firstHit_spec hηc ⟨b, hpb'⟩
  obtain ⟨ht₀0, ht₀, -⟩ := firstHit_spec hηc ⟨b, hp₀b'⟩
  set tp := firstHit η (Q p) with htpdef
  set t₀ := firstHit η (Q p₀) with ht₀def
  have ht₀b : t₀ ≤ b := firstHit_le_of_mem hp₀b
  have hatp : a < tp := lt_of_not_ge fun hle => hpa ⟨tp, ⟨htp0, hle⟩, htp⟩
  have htpt₀ : tp ≤ t₀ :=
    firstHit_le_of_mem (wall_rev hX hη0 hrev hIp₀ hIp hp₀p.le ⟨t₀, ⟨ht₀0, le_rfl⟩, ht₀⟩)
  have hvis₂ : ∃ t, Q p₂ ∈ η '' Icc 0 t := wall_visited hη0 hX hvis hIp₂
  have hvis₁ : ∃ t, Q p₁ ∈ η '' Icc 0 t := wall_visited hη0 hX hvis hIp₁
  obtain ⟨hτ'0, hτ', -⟩ := firstHit_spec hηc hvis₂
  obtain ⟨hσ'0, hσ', -⟩ := firstHit_spec hηc hvis₁
  set τ' := firstHit η (Q p₂) with hτ'def
  set σ' := firstHit η (Q p₁) with hσ'def
  have hτ'tp : τ' < tp := by
    refine lt_of_le_of_ne (firstHit_le_of_mem (wall_rev hX hη0 hrev hIp hIp₂ hp.le
      ⟨tp, ⟨htp0, le_rfl⟩, htp⟩)) fun he => ?_
    have : Q p₂ = Q p := by rw [← hτ', ← htp, he]
    exact hp.ne' (hQinj hIp₂ hIp this)
  have ht₀σ' : t₀ < σ' := by
    refine lt_of_le_of_ne (firstHit_le_of_mem (wall_rev hX hη0 hrev hIp₁ hIp₀ hp₀.le
      ⟨σ', ⟨hσ'0, le_rfl⟩, hσ'⟩)) fun he => ?_
    have : Q p₀ = Q p₁ := by rw [← ht₀, ← hσ', he]
    exact hp₀.ne' (hQinj hIp₀ hIp₁ this)
  set a' := max a τ' with ha'
  have ha'tp : a' < tp := max_lt hatp hτ'tp
  have hAC' := hAC a' t₀ (le_max_right _ _) (ha'tp.le.trans htpt₀) ht₀σ' fun t ht =>
    havoid t ⟨(le_max_left _ _).trans ht.1, ht.2.trans ht₀b⟩
  have hΔ : 0 < p₂ - p₁ := sub_pos.2 (hp₀.trans (hp₀p.trans hp))
  set B : ℝ → ℂ := fun s => Q (p₁ + s * (p₂ - p₁)) with hB
  set s₀ := (p₀ - p₁) / (p₂ - p₁) with hs₀
  set sp := (p - p₁) / (p₂ - p₁) with hsp
  have hs₀Q : B s₀ = Q p₀ := by simp only [hB, hs₀]; congr 1; field_simp; ring
  have hspQ : B sp = Q p := by simp only [hB, hsp]; congr 1; field_simp; ring
  have hs₀sp : s₀ < sp := by rw [hs₀, hsp]; exact div_lt_div_of_pos_right (by linarith) hΔ
  have hs₀I : s₀ ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith) hΔ.le, by rw [hs₀, div_le_one hΔ]; linarith⟩
  have hspI : sp ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith) hΔ.le, by rw [hsp, div_le_one hΔ]; linarith⟩
  have hle : firstVisit (fun t => η '' Icc 0 t) B t₀ ≤ s₀ :=
    csInf_le ⟨0, fun x hx => hx.1.1⟩ ⟨hs₀I, by rw [hs₀Q]; exact ⟨t₀, ⟨ht₀0, le_rfl⟩, ht₀⟩⟩
  have hge : sp ≤ firstVisit (fun t => η '' Icc 0 t) B a' := by
    have hB1 : B 1 = Q p₂ := by simp only [hB, one_mul, add_sub_cancel]
    refine le_csInf ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hB1]; exact ⟨τ', ⟨hτ'0, le_max_right _ _⟩, hτ'⟩⟩
      fun x hx => ?_
    by_contra hlt
    have hm : p₁ + x * (p₂ - p₁) ≤ p₁ + sp * (p₂ - p₁) := by
      have := mul_le_mul_of_nonneg_right (not_le.1 hlt).le hΔ.le; linarith
    have hxI : p₁ + x * (p₂ - p₁) ∈ Ioc (0 : ℝ) 1 :=
      ⟨by have := mul_nonneg hx.1.1 hΔ.le; linarith,
        by have := mul_le_mul_of_nonneg_right hx.1.2 hΔ.le; linarith⟩
    have hspI' : p₁ + sp * (p₂ - p₁) ∈ Ioc (0 : ℝ) 1 :=
      ⟨by have := mul_nonneg hspI.1 hΔ.le; linarith,
        by have := mul_le_mul_of_nonneg_right hspI.2 hΔ.le; linarith⟩
    have hvis := wall_rev hX hη0 hrev hxI hspI' hm hx.2
    have hvis' : B sp ∈ η '' Icc 0 a' := hvis
    rw [hspQ] at hvis'
    exact absurd (firstHit_le_of_mem hvis') (not_le.2 ha'tp)
  rw [hAC'] at hle
  linarith

/-- **No attachment progress in a sub-pocket opening at the flow seed, contradicted**: as `false_of_progress` for the
last-visit attachment along the arm `v ↦ m(X̃(p₂/(1 + v)))`. -/
theorem false_of_progressInf (hX : IsSimpleProper X) (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit X η) (hvis : IsWallVisited X η) {C' : Set ℂ} {p₂ : ℝ} (hp₂0 : 0 < p₂)
    (hp₂ : p₂ ≤ 1)
    (hAC : BarrierAttachConstInf η C' (fun v => cfPt (toDisc (Lemma71I.realPath X) (p₂ / (1 + v))))
      (firstHit η (cfPt (toDisc (Lemma71I.realPath X) p₂))))
    {a b p₀ p : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ < p) (hp : p < p₂)
    (hpb : cfPt (toDisc (Lemma71I.realPath X) p) ∈ η '' Icc 0 b)
    (hpa : cfPt (toDisc (Lemma71I.realPath X) p) ∉ η '' Icc 0 a)
    (hp₀b : cfPt (toDisc (Lemma71I.realPath X) p₀) ∈ η '' Icc 0 b) (havoid : ∀ t ∈ Icc a b, η t ∉ C') : False := by
  set Q : ℝ → ℂ := fun ρ => cfPt (toDisc (Lemma71I.realPath X) ρ) with hQ
  have hQinj := cfPt_toDisc_injOn hX
  have hIp : p ∈ Ioc (0 : ℝ) 1 := ⟨hp₀.trans hp₀p, (hp.trans_le hp₂).le⟩
  have hIp₀ : p₀ ∈ Ioc (0 : ℝ) 1 := ⟨hp₀, (hp₀p.trans (hp.trans_le hp₂)).le⟩
  have hIp₂ : p₂ ∈ Ioc (0 : ℝ) 1 := ⟨hp₂0, hp₂⟩
  have hpb' : Q p ∈ η '' Icc 0 b := hpb
  have hp₀b' : Q p₀ ∈ η '' Icc 0 b := hp₀b
  obtain ⟨htp0, htp, -⟩ := firstHit_spec hηc ⟨b, hpb'⟩
  obtain ⟨ht₀0, ht₀, -⟩ := firstHit_spec hηc ⟨b, hp₀b'⟩
  set tp := firstHit η (Q p) with htpdef
  set t₀ := firstHit η (Q p₀) with ht₀def
  have ht₀b : t₀ ≤ b := firstHit_le_of_mem hp₀b
  have hatp : a < tp := lt_of_not_ge fun hle => hpa ⟨tp, ⟨htp0, hle⟩, htp⟩
  have htpt₀ : tp ≤ t₀ :=
    firstHit_le_of_mem (wall_rev hX hη0 hrev hIp₀ hIp hp₀p.le ⟨t₀, ⟨ht₀0, le_rfl⟩, ht₀⟩)
  have hvis₂ : ∃ t, Q p₂ ∈ η '' Icc 0 t := wall_visited hη0 hX hvis hIp₂
  obtain ⟨hτ'0, hτ', -⟩ := firstHit_spec hηc hvis₂
  set τ' := firstHit η (Q p₂) with hτ'def
  have hτ'tp : τ' < tp := by
    refine lt_of_le_of_ne (firstHit_le_of_mem (wall_rev hX hη0 hrev hIp hIp₂ hp.le
      ⟨tp, ⟨htp0, le_rfl⟩, htp⟩)) fun he => ?_
    have : Q p₂ = Q p := by rw [← hτ', ← htp, he]
    exact hp.ne' (hQinj hIp₂ hIp this)
  set a' := max a τ' with ha'
  have ha'tp : a' < tp := max_lt hatp hτ'tp
  have hAC' := hAC a' t₀ (le_max_right _ _) (ha'tp.le.trans htpt₀) fun t ht =>
    havoid t ⟨(le_max_left _ _).trans ht.1, ht.2.trans ht₀b⟩
  set B : ℝ → ℂ := fun v => Q (p₂ / (1 + v)) with hB
  have hBv : ∀ ρ, 0 < ρ → B (p₂ / ρ - 1) = Q ρ := fun ρ hρ => by
    simp only [hB, add_sub_cancel]; congr 1; field_simp
  set vp := p₂ / p - 1 with hvp
  set v₀ := p₂ / p₀ - 1 with hv₀
  have hvp0 : 0 ≤ vp := by rw [hvp, sub_nonneg, le_div_iff₀ hIp.1, one_mul]; exact hp.le
  have hvpv₀ : vp < v₀ := by
    rw [hvp, hv₀]; have := div_lt_div_of_pos_left hp₂0 hp₀ hp₀p; linarith
  have hrevB := rev_inf_of_wall hX hη0 hrev hp₂0 hp₂
  have hle : lastVisit (fun t => η '' Icc 0 t) B a' ≤ vp := by
    have hB0 : B 0 = Q p₂ := by simp only [hB, add_zero, div_one]
    refine csSup_le ⟨0, ⟨self_mem_Ici, by rw [hB0]; exact ⟨τ', ⟨hτ'0, le_max_right _ _⟩, hτ'⟩⟩⟩ fun x hx => ?_
    by_contra hlt
    have hvis := hrevB a' vp hvp0 x hx.1 (not_le.1 hlt).le hx.2
    have hvis' : B vp ∈ η '' Icc 0 a' := hvis
    rw [hvp, hBv p hIp.1] at hvis'
    exact absurd (firstHit_le_of_mem hvis') (not_le.2 ha'tp)
  have hbdd : BddAbove {x ∈ Ici (0 : ℝ) | B x ∈ η '' Icc 0 t₀} := by
    obtain ⟨K, hK⟩ := (isCompact_Icc.image_of_continuousOn (hηc.mono Icc_subset_Ici_self)).isBounded.exists_norm_le
    have ht := (crosscut_arcInf_props hX.isProperArc.isDiscCrosscut_toDisc hp₂0 hp₂).2.2.1
    obtain ⟨V, hV⟩ := eventually_atTop.1 (ht.eventually_gt_atTop K)
    refine ⟨V, fun x hx => ?_⟩
    by_contra hlt
    exact not_le.2 (hV x (not_le.1 hlt).le) (hK _ hx.2)
  have hge : v₀ ≤ lastVisit (fun t => η '' Icc 0 t) B t₀ :=
    le_csSup hbdd ⟨hvpv₀.le.trans' hvp0, by rw [hv₀, hBv p₀ hp₀]; exact ⟨t₀, ⟨ht₀0, le_rfl⟩, ht₀⟩⟩
  rw [hAC'] at hge
  linarith

end Progress

section TransferInf

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **Aux. lemma 37 along the contained right arm of a mixed pocket opening at the flow seed** (outer left arm; the
last-visit form `BarrierAttachConstInf`), from Aux. lemma 37 in the pockets of `(R, M)`, bounded (`hsub`) or opening
at the flow seed (`hsubI`). Pathwise: as `barrierAttachConst_right_of_sub`, with the arm read from `y₀` towards `∞`. -/
theorem barrierAttachConstInf_right_of_sub (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M)
      (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (hRM : NoCommonArc R M)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M) {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0))
    (hη0 : η 0 = 0) (hrevR : IsWallReverseVisit R η) (hvisR : IsWallVisited R η)
    (hsub : ∀ q : ℚ, 0 < q → IsChangeConfigInc R M (StripSys.rt q) → 0 < rightLo R M (StripSys.rt q) →
      BarrierAttachConst η (cfPocket R M (StripSys.rt q)) (cfArcR R M (StripSys.rt q))
        (firstHit η (cfArcR R M (StripSys.rt q) 1)) (firstHit η (cfArcR R M (StripSys.rt q) 0)))
    (hsubI : ∀ q : ℚ, 0 < q → IsChangeConfigInc R M (StripSys.rt q) → rightLo R M (StripSys.rt q) = 0 →
      BarrierAttachConstInf η (cfPocket R M (StripSys.rt q)) (cfArcRInf R M (StripSys.rt q))
        (firstHit η (cfArcRInf R M (StripSys.rt q) 0))) :
    BarrierAttachConstInf η (cfPocket R L r) (cfArcRInf R L r) (firstHit η (cfArcRInf R L r 0)) := by
  intro a b hτa hab havoid
  have hC := h.isCfPocketInf h0
  obtain ⟨-, hhi1, hlohi, -⟩ := h.changeCorner_props
  have hu0 : 0 < rightHi R L r := h0 ▸ hlohi
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, hin, -⟩ := exists_midTimes h hO hcR hcL
  have hαR := h.right.isProperArc.isDiscCrosscut_toDisc
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hσ0 : σM = 0 := by
    have he : toDisc (Lemma71I.realPath M) σM = toDisc (Lemma71I.realPath M) 0 := by
      rw [hσa, hαM.zero, openPt, h0, hαR.zero]
    exact hαM.inj ⟨h0σ, hστ.le.trans hτ1⟩ ⟨le_rfl, zero_le_one⟩ he
  have hord : Disjoint (range M) (rightSideOf (range R)) := by
    have := hO.right_middle; rwa [arcRange_realPath, arcRange_realPath] at this
  set Q : ℝ → ℂ := fun ρ => cfPt (toDisc (Lemma71I.realPath R) ρ) with hQ
  have hy : Q (rightHi R L r) ∈ η '' Icc 0 a := by
    have hv : ∃ t, Q (rightHi R L r) ∈ η '' Icc 0 t := wall_visited hη0 h.right hvisR ⟨hu0, hhi1.2⟩
    have he : Q (rightHi R L r) = cfArcRInf R L r 0 := by simp only [hQ, cfArcRInf, add_zero, div_one]
    rw [he] at hv ⊢
    obtain ⟨hτ0, hτ, -⟩ := firstHit_spec hηc hv
    exact ⟨_, ⟨hτ0, hτa⟩, hτ⟩
  unfold lastVisit
  congr 1
  ext v
  refine ⟨fun hv => ⟨hv.1, ?_⟩, fun hv => ⟨hv.1, image_mono (Icc_subset_Icc_right hab) hv.2⟩⟩
  by_contra hva
  have hBQ : ∀ w, cfArcRInf R L r w = Q (rightHi R L r / (1 + w)) := fun _ => rfl
  have hv0 : 0 < v := lt_of_le_of_ne hv.1 fun he => hva (by rw [← he, hBQ, add_zero, div_one]; exact hy)
  have hcl := isClosed_visited isClosed_Ici hηc hC.cont₁ a
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl v fun hm => hva hm.2
  set c := max (v - ε / 2) 0 with hc
  have hcv : c < v := max_lt (by linarith) hv0
  have hc0 : 0 ≤ c := le_max_right _ _
  set ρ₁ := rightHi R L r / (1 + v) with hρ₁
  set ρ₂ := rightHi R L r / (1 + c) with hρ₂
  have hρ₁pos : 0 < ρ₁ := div_pos hu0 (by linarith)
  have hρ₁₂ : ρ₁ < ρ₂ := div_lt_div_of_pos_left hu0 (by linarith) (by linarith)
  have hρ₂1 : ρ₂ ≤ rightHi R L r := (div_one_add_mem hu0 hc0).2
  have hrev := rev_inf_of_wall h.right hη0 hrevR hu0 hhi1.2
  have hnew : ∀ ρ ∈ Icc ρ₁ ρ₂, Q ρ ∈ η '' Icc 0 b ∧ Q ρ ∉ η '' Icc 0 a := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁pos.trans_le hρ.1
    set w := rightHi R L r / ρ - 1 with hw
    have hwρ : rightHi R L r / (1 + w) = ρ := by rw [hw, add_sub_cancel]; field_simp
    have hwv : w ≤ v := by
      have h1 : rightHi R L r ≤ ρ * (1 + v) := by
        have := hρ.1; rw [hρ₁, div_le_iff₀ (by linarith)] at this; linarith
      rw [hw, sub_le_iff_le_add, div_le_iff₀ hρ0]; linarith
    have hcw : c ≤ w := by
      have h1 : ρ * (1 + c) ≤ rightHi R L r := by
        have := hρ.2; rw [hρ₂, le_div_iff₀ (by linarith)] at this; linarith
      rw [hw, le_sub_iff_add_le, le_div_iff₀ hρ0]; linarith
    have hw0 : w ∈ Ici (0 : ℝ) := hc0.trans hcw
    refine ⟨?_, fun hwa => ?_⟩
    · have := hrev b w hw0 v hv.1 hwv hv.2
      simp only at this
      rw [hwρ] at this
      exact this
    · refine hball ?_ ⟨hw0, by rw [hBQ, hwρ]; exact hwa⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left (v - ε / 2) 0]
  obtain ⟨p, hpI, hpM⟩ : ∃ p ∈ Ioo ρ₁ ρ₂,
      toDisc (Lemma71I.realPath R) p ∉ crossRange (toDisc (Lemma71I.realPath M)) := by
    by_contra hall
    push Not at hall
    set c₁ := (2 * ρ₁ + ρ₂) / 3 with hc₁
    set c₂ := (ρ₁ + 2 * ρ₂) / 3 with hc₂
    have hc₁₂ : c₁ < c₂ := by rw [hc₁, hc₂]; linarith
    have hc₂1 : c₂ < 1 := by rw [hc₂]; linarith [hhi1.2]
    have hc₁0 : 0 < c₁ := by rw [hc₁]; linarith
    refine false_of_interval_range hRM (arcTime_pos ⟨hc₁0, hc₁₂.trans hc₂1⟩)
      (arcTime_lt_arcTime hc₁0.le hc₁₂ hc₂1) fun t ht => ?_
    have ht0 : 0 < t := (arcTime_pos ⟨hc₁0, hc₁₂.trans hc₂1⟩).trans_le ht.1
    have h1 : c₁ ≤ discTime t := by
      have := discTime_le_discTime (arcTime_pos ⟨hc₁0, hc₁₂.trans hc₂1⟩).le ht.1
      rwa [discTime_arcTime (hc₁₂.trans hc₂1)] at this
    have h2 : discTime t ≤ c₂ := by
      have := discTime_le_discTime ht0.le ht.2
      rwa [discTime_arcTime hc₂1] at this
    have hsI : discTime t ∈ Ioo (0 : ℝ) 1 := ⟨hc₁0.trans_le h1, h2.trans_lt hc₂1⟩
    have := (toDisc_mem_crossRange_iff h.right hM hsI).1
      (hall _ ⟨by rw [hc₁] at h1; linarith, by rw [hc₂] at h2; linarith⟩)
    rwa [arcTime_discTime ht0.le] at this
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨hρ₁pos.trans hpI.1, hpI.2.trans_le (hρ₂1.trans hhi1.2)⟩
  obtain ⟨q, hq, h', -, hHi', hp'⟩ := exists_subPocket h.right hM hord hp01 hpM
  have hτI : τM ∈ Icc (0 : ℝ) 1 := ⟨h0σ.trans hστ.le, hτ1⟩
  have hcHi : rightHi R L r ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) :=
    ⟨hhi1, τM, hτI, hτb⟩
  have hhi' : rightHi R M (StripSys.rt q) ≤ rightHi R L r := by
    rw [hHi']
    exact csInf_le ⟨0, fun x hx => hx.1.1.1⟩ ⟨hcHi, hpI.2.le.trans hρ₂1, hhi1.2⟩
  obtain ⟨hg', -, hj2, -⟩ := h'.changeCorners
  have hjHi : contactMap (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) (rightHi R L r) = τM :=
    contactMap_eq hαM hτI hτb.symm
  have hlτ : leftHi R M (StripSys.rt q) ≤ τM := by
    rw [← hjHi, ← hj2]; exact h'.inc.monotoneOn hg'.2.1 hcHi hhi'
  have hσl : σM ≤ leftLo R M (StripSys.rt q) := by rw [hσ0]; exact (h'.changeCorner_props.2.2.2.1).1
  have hsubC := cfPocket_subset_of_sub' h hM hO hcL houter h' hin hσl hlτ
  set p₁ := rightLo R M (StripSys.rt q) with hp₁
  set p₂ := rightHi R M (StripSys.rt q) with hp₂
  set p₀ := (max ρ₁ p₁ + p) / 2 with hp₀
  have hmx : max ρ₁ p₁ < p := max_lt hpI.1 hp'.1
  have hp₀p : p₀ < p := by rw [hp₀]; linarith
  have hp₀lo : max ρ₁ p₁ < p₀ := by rw [hp₀]; linarith
  have hp₀I : p₀ ∈ Icc ρ₁ ρ₂ := ⟨(le_max_left _ _).trans hp₀lo.le, hp₀p.le.trans hpI.2.le⟩
  have hp₁p₀ : p₁ < p₀ := (le_max_right _ _).trans_lt hp₀lo
  have hp₀0 : 0 < p₀ := hρ₁pos.trans_le ((le_max_left _ _).trans hp₀lo.le)
  have hp₂1 : p₂ ≤ 1 := hhi'.trans hhi1.2
  obtain ⟨hpb, hpa⟩ := hnew p ⟨hpI.1.le, hpI.2.le⟩
  obtain ⟨hp₀b, -⟩ := hnew p₀ hp₀I
  have havoid' : ∀ t ∈ Icc a b, η t ∉ cfPocket R M (StripSys.rt q) := fun t ht htC => havoid t ht (hsubC htC)
  rcases (h'.changeCorner_props.1.1).lt_or_eq with hb' | hb'
  · have hAC := hsub q hq h' hb'
    have e1 : cfArcR R M (StripSys.rt q) 1 = cfPt (toDisc (Lemma71I.realPath R) p₂) := by
      simp only [cfArcR, one_mul, add_sub_cancel]; rfl
    have e0 : cfArcR R M (StripSys.rt q) 0 = cfPt (toDisc (Lemma71I.realPath R) p₁) := by
      simp only [cfArcR, zero_mul, add_zero]; rfl
    rw [e1, e0] at hAC
    exact false_of_progress h.right hηc hη0 hrevR hvisR hb' hp₂1 hAC hp₁p₀ hp₀p hp'.2 hpb hpa hp₀b havoid'
  · have hAC := hsubI q hq h' hb'.symm
    have e0 : cfArcRInf R M (StripSys.rt q) 0 = cfPt (toDisc (Lemma71I.realPath R) p₂) := by
      simp only [cfArcRInf, add_zero, div_one]; rfl
    rw [e0] at hAC
    exact false_of_progressInf h.right hηc hη0 hrevR hvisR (hp₀0.trans (hp₀p.trans hp'.2)) hp₂1 hAC hp₀0 hp₀p
      hp'.2 hpb hpa hp₀b havoid'

/-- **Aux. lemma 37 along the contained left arm of a mixed pocket opening at the flow seed** (outer right arm; the
mirror of `barrierAttachConstInf_right_of_sub`), from Aux. lemma 37 in the pockets of `(M, L)`. Pathwise. -/
theorem barrierAttachConstInf_left_of_sub (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M)
      (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (hLM : NoCommonArc L M)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M) {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0))
    (hη0 : η 0 = 0) (hrevL : IsWallReverseVisit L η) (hvisL : IsWallVisited L η)
    (hsub : ∀ q : ℚ, 0 < q → IsChangeConfigInc M L (StripSys.rt q) → 0 < rightLo M L (StripSys.rt q) →
      BarrierAttachConst η (cfPocket M L (StripSys.rt q)) (cfArcL M L (StripSys.rt q))
        (firstHit η (cfArcR M L (StripSys.rt q) 1)) (firstHit η (cfArcR M L (StripSys.rt q) 0)))
    (hsubI : ∀ q : ℚ, 0 < q → IsChangeConfigInc M L (StripSys.rt q) → rightLo M L (StripSys.rt q) = 0 →
      BarrierAttachConstInf η (cfPocket M L (StripSys.rt q)) (cfArcLInf M L (StripSys.rt q))
        (firstHit η (cfArcRInf M L (StripSys.rt q) 0))) :
    BarrierAttachConstInf η (cfPocket R L r) (cfArcLInf R L r) (firstHit η (cfArcRInf R L r 0)) := by
  intro a b hτa hab havoid
  have hC := h.isCfPocketInf h0
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  obtain ⟨-, -, -, hlo1, hhi1, hlohi, -, hclose⟩ := h.changeCorner_props
  have hu0 : 0 < leftHi R L r := ha0 ▸ hlohi
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, hin, -⟩ := exists_midTimes h hO hcR hcL
  have hαR := h.right.isProperArc.isDiscCrosscut_toDisc
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hαL := h.left.isProperArc.isDiscCrosscut_toDisc
  have hσ0 : σM = 0 := by
    have he : toDisc (Lemma71I.realPath M) σM = toDisc (Lemma71I.realPath M) 0 := by
      rw [hσa, hαM.zero, openPt, h0, hαR.zero]
    exact hαM.inj ⟨h0σ, hστ.le.trans hτ1⟩ ⟨le_rfl, zero_le_one⟩ he
  have hord : Disjoint (range L) (rightSideOf (range M)) := by
    have := hO.middle_left; rwa [arcRange_realPath, arcRange_realPath] at this
  set Q : ℝ → ℂ := fun ρ => cfPt (toDisc (Lemma71I.realPath L) ρ) with hQ
  have hy : Q (leftHi R L r) ∈ η '' Icc 0 a := by
    have hv : ∃ t, Q (leftHi R L r) ∈ η '' Icc 0 t := wall_visited hη0 h.left hvisL ⟨hu0, hhi1.2⟩
    have he : Q (leftHi R L r) = cfArcRInf R L r 0 := by
      rw [← hC.seed]; simp only [hQ, cfArcLInf, add_zero, div_one]
    rw [he] at hv ⊢
    obtain ⟨hτ0, hτ, -⟩ := firstHit_spec hηc hv
    exact ⟨_, ⟨hτ0, hτa⟩, hτ⟩
  unfold lastVisit
  congr 1
  ext v
  refine ⟨fun hv => ⟨hv.1, ?_⟩, fun hv => ⟨hv.1, image_mono (Icc_subset_Icc_right hab) hv.2⟩⟩
  by_contra hva
  have hBQ : ∀ w, cfArcLInf R L r w = Q (leftHi R L r / (1 + w)) := fun _ => rfl
  have hv0 : 0 < v := lt_of_le_of_ne hv.1 fun he => hva (by rw [← he, hBQ, add_zero, div_one]; exact hy)
  have hcl := isClosed_visited isClosed_Ici hηc hC.cont₂ a
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl v fun hm => hva hm.2
  set c := max (v - ε / 2) 0 with hc
  have hcv : c < v := max_lt (by linarith) hv0
  have hc0 : 0 ≤ c := le_max_right _ _
  set ρ₁ := leftHi R L r / (1 + v) with hρ₁
  set ρ₂ := leftHi R L r / (1 + c) with hρ₂
  have hρ₁pos : 0 < ρ₁ := div_pos hu0 (by linarith)
  have hρ₁₂ : ρ₁ < ρ₂ := div_lt_div_of_pos_left hu0 (by linarith) (by linarith)
  have hρ₂1 : ρ₂ ≤ leftHi R L r := (div_one_add_mem hu0 hc0).2
  have hrev := rev_inf_of_wall h.left hη0 hrevL hu0 hhi1.2
  have hnew : ∀ ρ ∈ Icc ρ₁ ρ₂, Q ρ ∈ η '' Icc 0 b ∧ Q ρ ∉ η '' Icc 0 a := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁pos.trans_le hρ.1
    set w := leftHi R L r / ρ - 1 with hw
    have hwρ : leftHi R L r / (1 + w) = ρ := by rw [hw, add_sub_cancel]; field_simp
    have hwv : w ≤ v := by
      have h1 : leftHi R L r ≤ ρ * (1 + v) := by
        have := hρ.1; rw [hρ₁, div_le_iff₀ (by linarith)] at this; linarith
      rw [hw, sub_le_iff_le_add, div_le_iff₀ hρ0]; linarith
    have hcw : c ≤ w := by
      have h1 : ρ * (1 + c) ≤ leftHi R L r := by
        have := hρ.2; rw [hρ₂, le_div_iff₀ (by linarith)] at this; linarith
      rw [hw, le_sub_iff_add_le, le_div_iff₀ hρ0]; linarith
    have hw0 : w ∈ Ici (0 : ℝ) := hc0.trans hcw
    refine ⟨?_, fun hwa => ?_⟩
    · have := hrev b w hw0 v hv.1 hwv hv.2
      simp only at this
      rw [hwρ] at this
      exact this
    · refine hball ?_ ⟨hw0, by rw [hBQ, hwρ]; exact hwa⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left (v - ε / 2) 0]
  obtain ⟨p, hpI, hpM⟩ : ∃ p ∈ Ioo ρ₁ ρ₂,
      toDisc (Lemma71I.realPath L) p ∉ crossRange (toDisc (Lemma71I.realPath M)) := by
    by_contra hall
    push Not at hall
    set c₁ := (2 * ρ₁ + ρ₂) / 3 with hc₁
    set c₂ := (ρ₁ + 2 * ρ₂) / 3 with hc₂
    have hc₁₂ : c₁ < c₂ := by rw [hc₁, hc₂]; linarith
    have hc₂1 : c₂ < 1 := by rw [hc₂]; linarith [hhi1.2]
    have hc₁0 : 0 < c₁ := by rw [hc₁]; linarith
    refine false_of_interval_range hLM (arcTime_pos ⟨hc₁0, hc₁₂.trans hc₂1⟩)
      (arcTime_lt_arcTime hc₁0.le hc₁₂ hc₂1) fun t ht => ?_
    have ht0 : 0 < t := (arcTime_pos ⟨hc₁0, hc₁₂.trans hc₂1⟩).trans_le ht.1
    have h1 : c₁ ≤ discTime t := by
      have := discTime_le_discTime (arcTime_pos ⟨hc₁0, hc₁₂.trans hc₂1⟩).le ht.1
      rwa [discTime_arcTime (hc₁₂.trans hc₂1)] at this
    have h2 : discTime t ≤ c₂ := by
      have := discTime_le_discTime ht0.le ht.2
      rwa [discTime_arcTime hc₂1] at this
    have hsI : discTime t ∈ Ioo (0 : ℝ) 1 := ⟨hc₁0.trans_le h1, h2.trans_lt hc₂1⟩
    have := (toDisc_mem_crossRange_iff h.left hM hsI).1
      (hall _ ⟨by rw [hc₁] at h1; linarith, by rw [hc₂] at h2; linarith⟩)
    rwa [arcTime_discTime ht0.le] at this
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨hρ₁pos.trans hpI.1, hpI.2.trans_le (hρ₂1.trans hhi1.2)⟩
  obtain ⟨q, hq, h', -, hHi', hp'⟩ := exists_subPocketL hM h.left hord hp01 hpM
  have hτI : τM ∈ Icc (0 : ℝ) 1 := ⟨h0σ.trans hστ.le, hτ1⟩
  have hcHi : leftHi R L r ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath L)) (toDisc (Lemma71I.realPath M)) :=
    ⟨hhi1, τM, hτI, hτb.trans hclose.symm⟩
  have hhi' : leftHi M L (StripSys.rt q) ≤ leftHi R L r := by
    rw [hHi']
    exact csInf_le ⟨0, fun x hx => hx.1.1.1⟩ ⟨hcHi, hpI.2.le.trans hρ₂1, hhi1.2⟩
  obtain ⟨hg', -, hj2, -⟩ := h'.changeCorners
  have hτM : τM ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath M)) (toDisc (Lemma71I.realPath L)) :=
    ⟨hτI, leftHi R L r, hhi1, hclose.trans hτb.symm⟩
  have hjHi : contactMap (toDisc (Lemma71I.realPath M)) (toDisc (Lemma71I.realPath L)) τM = leftHi R L r :=
    contactMap_eq hαL hhi1 (hτb.trans hclose.symm)
  have hlτ : rightHi M L (StripSys.rt q) ≤ τM := by
    by_contra hlt
    have := h'.inc hτM hg'.2.1 (not_le.1 hlt)
    rw [hj2, hjHi] at this
    linarith
  have hσl : σM ≤ rightLo M L (StripSys.rt q) := by rw [hσ0]; exact (h'.changeCorner_props.1).1
  have hsubC := cfPocket_subset_of_subL' h hM hO hcR houter h' hin hσl hlτ
  set p₁ := leftLo M L (StripSys.rt q) with hp₁
  set p₂ := leftHi M L (StripSys.rt q) with hp₂
  set p₀ := (max ρ₁ p₁ + p) / 2 with hp₀
  have hmx : max ρ₁ p₁ < p := max_lt hpI.1 hp'.1
  have hp₀p : p₀ < p := by rw [hp₀]; linarith
  have hp₀lo : max ρ₁ p₁ < p₀ := by rw [hp₀]; linarith
  have hp₀I : p₀ ∈ Icc ρ₁ ρ₂ := ⟨(le_max_left _ _).trans hp₀lo.le, hp₀p.le.trans hpI.2.le⟩
  have hp₁p₀ : p₁ < p₀ := (le_max_right _ _).trans_lt hp₀lo
  have hp₀0 : 0 < p₀ := hρ₁pos.trans_le ((le_max_left _ _).trans hp₀lo.le)
  have hp₂1 : p₂ ≤ 1 := hhi'.trans hhi1.2
  obtain ⟨hpb, hpa⟩ := hnew p ⟨hpI.1.le, hpI.2.le⟩
  obtain ⟨hp₀b, -⟩ := hnew p₀ hp₀I
  have havoid' : ∀ t ∈ Icc a b, η t ∉ cfPocket M L (StripSys.rt q) := fun t ht htC => havoid t ht (hsubC htC)
  rcases (h'.changeCorner_props.1.1).lt_or_eq with hb' | hb'
  · have hC' := h'.isCfPocket (PocketMarks.zero_notMem_closure_of_rightLo_pos h' hb')
    have hAC := hsub q hq h' hb'
    have e1 : cfArcR M L (StripSys.rt q) 1 = cfPt (toDisc (Lemma71I.realPath L) p₂) := by
      rw [← hC'.seed]; simp only [cfArcL, one_mul, add_sub_cancel]; rfl
    have e0 : cfArcR M L (StripSys.rt q) 0 = cfPt (toDisc (Lemma71I.realPath L) p₁) := by
      rw [← hC'.junction]; simp only [cfArcL, zero_mul, add_zero]; rfl
    rw [e1, e0] at hAC
    exact false_of_progress h.left hηc hη0 hrevL hvisL
      (h'.leftLo_pos (PocketMarks.zero_notMem_closure_of_rightLo_pos h' hb')) hp₂1 hAC hp₁p₀ hp₀p hp'.2 hpb hpa
      hp₀b havoid'
  · have hC' := h'.isCfPocketInf hb'.symm
    have hAC := hsubI q hq h' hb'.symm
    have e0 : cfArcRInf M L (StripSys.rt q) 0 = cfPt (toDisc (Lemma71I.realPath L) p₂) := by
      rw [← hC'.seed]; simp only [cfArcLInf, add_zero, div_one]; rfl
    rw [e0] at hAC
    exact false_of_progressInf h.left hηc hη0 hrevL hvisL (hp₀0.trans (hp₀p.trans hp'.2)) hp₂1 hAC hp₀0 hp₀p
      hp'.2 hpb hpa hp₀b havoid'

end TransferInf

end InteractingSLE.Sec7.OuterGeom
