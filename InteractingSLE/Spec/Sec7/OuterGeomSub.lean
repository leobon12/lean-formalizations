/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterGeomAttach

/-!
# Theorem R.7's mixed pockets: Aux. lemma 37 along the contained arm from the extremal sub-pockets

Packet PROVE-R7-OUTERGEOM. §5.4 (p. 473): "On a contained strict-angle arm, the proof of Aux. 37 applies verbatim to
that one arm." Here this is reduced, pathwise, to Aux. lemma 37 in the extremal pockets formed by the contained arm and
the certified frontier `M` between the walls (R.3: in a mixed pocket the certified frontier of the outer side runs
between the two corners inside the closed pocket):

* `exists_subPocket`, `exists_subPocketL`: a point of the contained arm off `M` lies on the contained arc of a pocket
  of the contained arm with `M`, selected by a positive rational change time (contact gaps, `isContactGap_swap'`);
* `cfPocket_subset_of_sub`, `cfPocket_subset_of_subL`: that sub-pocket is nested in the mixed pocket (connected, off the
  mixed pocket's frontier, and meeting it at a point of its `M`-arc off both walls);
* **`barrierAttachConst_right_of_sub`** (outer left arm) and **`barrierAttachConst_left_of_sub`** (outer right arm):
  attachment progress along the contained arm on a no-`C` interval makes a nontrivial arc of new points, one of them
  off `M` (`NoCommonArc` of the arm with `M`), and then the attachment of the nested sub-pocket progresses on a
  no-sub-pocket interval — excluded by Aux. lemma 37 there (`hsub`).

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

section Gap

variable {α β : ℝ → ℂ}

/-- **A gap of the lower crosscut's contacts is a gap of the upper one's** (the mirror of
`PocketCoord.isContactGap_swap`): through the increasing contact map `α ↦ β`. -/
theorem isContactGap_swap' (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {a b : ℝ} (hg : IsContactGap α β a b) :
    IsContactGap β α (contactMap α β a) (contactMap α β b) ∧
      contactMap β α (contactMap α β a) = a ∧ contactMap β α (contactMap α β b) = b := by
  obtain ⟨ha, hb, hab, hgap⟩ := hg
  obtain ⟨hu, hβu⟩ := contactMap_mem hβ ha
  obtain ⟨hv, hβv⟩ := contactMap_mem hβ hb
  set u := contactMap α β a
  set v := contactMap α β b
  have hu' : u ∈ Sec7.pocketContactSet β α := ⟨hu, a, ha.1, hβu.symm⟩
  have hv' : v ∈ Sec7.pocketContactSet β α := ⟨hv, b, hb.1, hβv.symm⟩
  have hju : contactMap β α u = a := contactMap_eq hα ha.1 hβu
  have hjv : contactMap β α v = b := contactMap_eq hα hb.1 hβv
  refine ⟨⟨hu', hv', hjm ha hb hab, fun s hs hsC => ?_⟩, hju, hjv⟩
  obtain ⟨hs', hαs'⟩ := contactMap_mem hα hsC
  set s' := contactMap β α s
  have hs'C : s' ∈ Sec7.pocketContactSet α β := ⟨hs', s, hsC.1, hαs'.symm⟩
  have hjs : contactMap α β s' = s := contactMap_eq hβ hsC.1 hαs'
  refine hgap s' ⟨?_, ?_⟩ hs'C
  · by_contra hle
    rcases eq_or_lt_of_le (not_lt.1 hle) with he | hlt
    · rw [he] at hjs; exact hs.1.ne hjs
    · have := hjm hs'C ha hlt
      rw [hjs] at this
      exact lt_asymm hs.1 this
  · by_contra hle
    rcases eq_or_lt_of_le (not_lt.1 hle) with he | hlt
    · rw [← he] at hjs; exact hs.2.ne hjs.symm
    · have := hjm hb hs'C hlt
      rw [hjs] at this
      exact lt_asymm hs.2 this

end Gap

section Sub

variable {R M L X : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- A disc point of a wall lies on another wall's disc crosscut iff the wall point lies on the other wall. -/
theorem toDisc_mem_crossRange_iff (hR : IsSimpleProper R) (hM : IsSimpleProper M) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    toDisc (Lemma71I.realPath R) p ∈ crossRange (toDisc (Lemma71I.realPath M)) ↔
      R (arcTime p).toNNReal ∈ range M := by
  have hRH : R (arcTime p).toNNReal ∈ H := hR.2.2.2.1 _ (Real.toNNReal_pos.2 (arcTime_pos hp))
  rw [toDisc_of_lt hp.2]
  change cayley (R (arcTime p).toNNReal) ∈ _ ↔ _
  rw [hM.isProperArc.cayley_mem_crossRange_iff (H_subset_Hbar' hRH), arcRange_realPath]

theorem strictMonoOn_contactMap_of_ord (hR : IsSimpleProper R) (hM : IsSimpleProper M)
    (hord : Disjoint (range M) (rightSideOf (range R))) :
    StrictMonoOn (contactMap (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)))
      (Sec7.pocketContactSet (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M))) :=
  strictMonoOn_contactMap hR.isProperArc.isDiscCrosscut_toDisc hM.isProperArc.isDiscCrosscut_toDisc
    ((disjoint_rightSideOf_iff hR.isProperArc hM.isProperArc).1 (by
      rw [arcRange_realPath, arcRange_realPath]; exact hord))

/-- **The sub-pocket through a right-wall point** (left wall `M`): for a disc time `p ∈ (0, 1)` of `R` off `M`,
some positive rational change time `q` on `M` selects the pocket of `(R, M)` whose right arc is the gap of the
contacts of `R` with `M` around `p`. -/
theorem exists_subPocket (hR : IsSimpleProper R) (hM : IsSimpleProper M)
    (hord : Disjoint (range M) (rightSideOf (range R))) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpM : toDisc (Lemma71I.realPath R) p ∉ crossRange (toDisc (Lemma71I.realPath M))) :
    ∃ q : ℚ, 0 < q ∧ IsChangeConfigInc R M (StripSys.rt q) ∧
      rightLo R M (StripSys.rt q) = gapLo (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) p ∧
      rightHi R M (StripSys.rt q) = gapHi (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) p ∧
      p ∈ Ioo (rightLo R M (StripSys.rt q)) (rightHi R M (StripSys.rt q)) := by
  have hαR := hR.isProperArc.isDiscCrosscut_toDisc
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hjm := strictMonoOn_contactMap_of_ord hR hM hord
  obtain ⟨hg, hpg⟩ := isContactGap_gapLo_gapHi hαM hαR ⟨hp.1.le, hp.2.le⟩ hpM
  obtain ⟨hg', hj₁, hj₂⟩ := isContactGap_swap' hαR hαM hjm hg
  set p₁ := gapLo (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) p
  set p₂ := gapHi (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) p
  set l₁ := contactMap (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) p₁
  set l₂ := contactMap (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) p₂
  have hgM := hg'
  obtain ⟨hl₁, hl₂, hl, hlgap⟩ := hg'
  set m := (l₁ + l₂) / 2 with hm
  have hm1 : m < 1 := by have := hl₂.1.2; rw [hm]; linarith
  have hl₁m : l₁ < m := by rw [hm]; linarith
  have hA : arcTime l₁ < arcTime m := by
    by_contra hle
    have h' := discTime_le_discTime (arcTime_nonneg ⟨hl₁.1.1.trans hl₁m.le, hm1⟩) (not_lt.1 hle)
    rw [discTime_arcTime (hl₁m.trans hm1), discTime_arcTime hm1] at h'
    linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hA
  have hq0 : (0 : ℝ) < q := (arcTime_nonneg ⟨hl₁.1.1, hl₁m.trans hm1⟩).trans_lt hq1
  have hrt : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have hdq : discTime ((StripSys.rt q : ℝ≥0) : ℝ) ∈ Ioo l₁ l₂ := by
    rw [hrt]
    constructor
    · have := discTime_lt_discTime (arcTime_nonneg ⟨hl₁.1.1, hl₁m.trans hm1⟩) hq1
      rwa [discTime_arcTime (hl₁m.trans hm1)] at this
    · have := discTime_lt_discTime hq0.le hq2
      rw [discTime_arcTime hm1] at this
      exact this.trans (by rw [hm]; linarith)
  have hdqI : discTime ((StripSys.rt q : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨hl₁.1.1.trans hdq.1.le, hdq.2.le.trans hl₂.1.2⟩
  have hoff : toDisc (Lemma71I.realPath M) (discTime ((StripSys.rt q : ℝ≥0) : ℝ)) ∉
      crossRange (toDisc (Lemma71I.realPath R)) := fun hmem => hlgap _ hdq ⟨hdqI, hmem⟩
  have hpos : 0 < StripSys.rt q := by
    rw [← NNReal.coe_pos, hrt]; exact hq0
  have hMH : M (StripSys.rt q) ∈ Hbar := H_subset_Hbar' (hM.2.2.2.1 _ hpos)
  have hoff' : M (StripSys.rt q) ∉ range R := by
    rwa [toDisc_realPath_discTime, hR.isProperArc.cayley_mem_crossRange_iff hMH, arcRange_realPath] at hoff
  have hcfg : IsChangeConfig R M (StripSys.rt q) := ⟨hR, hM, hord, hpos, hoff'⟩
  obtain ⟨hlo, hhi⟩ := gapLo_gapHi_eq hoff hgM hdq
  have hLo : rightLo R M (StripSys.rt q) = p₁ := by
    rw [rightLo, leftLo, hlo, hj₁]
  have hHi : rightHi R M (StripSys.rt q) = p₂ := by
    rw [rightHi, leftHi, hhi, hj₂]
  refine ⟨q, by exact_mod_cast hq0, hcfg.isChangeConfigInc, hLo, hHi, ?_⟩
  rw [hLo, hHi]
  exact hpg

/-- `arcTime` is strictly increasing on `[0, 1)`. -/
theorem arcTime_lt_arcTime {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s') (hs' : s' < 1) : arcTime s < arcTime s' := by
  by_contra hle
  have h' := discTime_le_discTime (arcTime_nonneg ⟨hs.trans hss'.le, hs'⟩) (not_lt.1 hle)
  rw [discTime_arcTime (hss'.trans hs'), discTime_arcTime hs'] at h'
  linarith

/-- **A point of a nontrivial disc-time interval of `M` off a wall `X`** (`NoCommonArc M X`). -/
theorem exists_discTime_notMem (hcX : NoCommonArc M X) {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl : l₁ < l₂) (hl₂ : l₂ ≤ 1) :
    ∃ t : ℝ≥0, 0 < (t : ℝ) ∧ discTime (t : ℝ) ∈ Ioo l₁ l₂ ∧ M t ∉ range X := by
  set m := (l₁ + l₂) / 2 with hm
  have hm1 : m < 1 := by rw [hm]; linarith
  have hl₁m : l₁ < m := by rw [hm]; linarith
  have hA := arcTime_lt_arcTime hl₁ hl₁m hm1
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn hA
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn hq₁b
  have hT0 : 0 ≤ arcTime l₁ := arcTime_nonneg ⟨hl₁, hl₁m.trans hm1⟩
  obtain ⟨t, ht₁, ht₂, htX⟩ := hcX q₁ q₂ (by exact_mod_cast hT0.trans_lt hq₁a) (by exact_mod_cast hq₂a)
  have ht0 : (0 : ℝ) < t := hT0.trans_lt (hq₁a.trans_le ht₁)
  refine ⟨t, ht0, ⟨?_, ?_⟩, htX⟩
  · have := discTime_lt_discTime hT0 (hq₁a.trans_le ht₁)
    rwa [discTime_arcTime (hl₁m.trans hm1)] at this
  · have := discTime_lt_discTime ht0.le (ht₂.trans_lt hq₂b)
    rw [discTime_arcTime hm1] at this
    exact this.trans (by rw [hm]; linarith)

/-- **Nested pockets** (Lemma R.3's geometry): a pocket of the right wall `R` and the middle curve `M` whose right arc
lies between the corners of the pocket of `(R, L)` lies in that pocket, when `L` is outer beyond `M`. -/
theorem cfPocket_subset_of_sub (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {r' : ℝ≥0} (h' : IsChangeConfigInc R M r') (hlo : rightLo R L r ≤ rightLo R M r')
    (hhi : rightHi R M r' ≤ rightHi R L r) : cfPocket R M r' ⊆ cfPocket R L r := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hb' : 0 < rightLo R M r' := hb.trans_le hlo
  have h0' := PocketMarks.zero_notMem_closure_of_rightLo_pos h' hb'
  have hC := h.isCfPocket h0
  have hC' := h'.isCfPocket h0'
  have hαR := h.right.isProperArc.isDiscCrosscut_toDisc
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hO' : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath M) :=
    ⟨hO.right, hO.middle, hO.middle, hO.right_middle, Set.disjoint_left.2 fun _ hz hr => hr.1.2 hz⟩
  have hC'r : changePocket R M r' ⊆ rightSideOf (range M) := R7FaceSelect.changePocket_subset_right_of_order h' hO'
  refine Sec6.subset_of_isPreconnected_of_disjoint_frontier hC'.isConnected.isPreconnected hC.isOpen ?_ ?_
  · obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, hin, -⟩ := exists_midTimes h hO hcR hcL
    have hjm := h'.inc
    obtain ⟨hg', hj1, hj2, -⟩ := h'.changeCorners
    obtain ⟨hlo1, hhi1, -⟩ := h.changeCorner_props
    have hσI : σM ∈ Icc (0 : ℝ) 1 := ⟨h0σ, hστ.le.trans hτ1⟩
    have hτI : τM ∈ Icc (0 : ℝ) 1 := ⟨h0σ.trans hστ.le, hτ1⟩
    have hcLo : rightLo R L r ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) :=
      ⟨hlo1, σM, hσI, hσa⟩
    have hcHi : rightHi R L r ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) :=
      ⟨hhi1, τM, hτI, hτb⟩
    have hjLo : contactMap (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) (rightLo R L r) = σM :=
      contactMap_eq hαM hσI hσa.symm
    have hjHi : contactMap (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) (rightHi R L r) = τM :=
      contactMap_eq hαM hτI hτb.symm
    have hσl : σM ≤ leftLo R M r' := by
      rw [← hjLo, ← hj1]; exact hjm.monotoneOn hcLo hg'.1 hlo
    have hlτ : leftHi R M r' ≤ τM := by
      rw [← hjHi, ← hj2]; exact hjm.monotoneOn hg'.2.1 hcHi hhi
    obtain ⟨-, -, -, hla, hlb, hll, -⟩ := h'.changeCorner_props
    obtain ⟨hgM, -, -⟩ := isContactGap_swap' hαR hαM hjm hg'
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
        ⟨hPcl, by rwa [hC.isOpen.interior_eq]⟩
      rw [hC.frontier_eq, hP] at hfr
      rcases hfr with ⟨u, -, hu⟩ | ⟨u, -, hu⟩
      · exact hsR (mem_range_of_cfPt_toDisc h.right hMH hu)
      · exact htL (mem_range_of_cfPt_toDisc h.left hMH hu)
    have hΔ : 0 < leftHi R M r' - leftLo R M r' := sub_pos.2 hll
    have hPcl' : cfPt (toDisc (Lemma71I.realPath M) s) ∈ closure (cfPocket R M r') := by
      refine frontier_subset_closure ?_
      rw [hC'.frontier_eq]
      refine Or.inr ⟨(s - leftLo R M r') / (leftHi R M r' - leftLo R M r'), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (sub_nonneg.2 hts.1.le) hΔ.le
      · rw [div_le_one hΔ]; linarith [hts.2]
      · simp only [cfArcL]; congr 2; field_simp; ring
    obtain ⟨z, hz⟩ := mem_closure_iff.1 hPcl' _ hC.isOpen hPC
    exact ⟨z, hz.2, hz.1⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hz
    have hw' := h'.changePocket_subset hw
    rw [hC.frontier_eq] at hz
    rcases hz with ⟨u, -, hu⟩ | ⟨u, -, hu⟩
    · exact hw'.2 (Or.inl (mem_range_of_cfPt_toDisc h.right hw'.1 hu))
    · rcases houter (mem_range_of_cfPt_toDisc h.left hw'.1 hu) with hl | hm
      · have hd := (hM.isProperArc).disjoint_leftSideOf_rightSideOf
        rw [arcRange_realPath] at hd
        exact Set.disjoint_left.1 hd hl (hC'r hw)
      · exact hw'.2 (Or.inr hm)

/-- Points of a simple proper wall at disc times in `(0, 1]` are distinct in the counterflow chart. -/
theorem cfPt_toDisc_injOn (hR : IsSimpleProper R) :
    InjOn (fun ρ => cfPt (toDisc (Lemma71I.realPath R) ρ)) (Ioc 0 1) := fun _ hρ _ hρ' he =>
  hR.isProperArc.isDiscCrosscut_toDisc.inj ⟨hρ.1.le, hρ.2⟩ ⟨hρ'.1.le, hρ'.2⟩
    (injOn_cfPt (toDisc_ne_neg_one hR hρ) (toDisc_ne_neg_one hR hρ') he)

/-- **Aux. lemma 37 along the contained right arm of a bounded pocket whose left arm is outer** (§5.4: "On a contained
strict-angle arm, the proof of Aux. 37 applies verbatim to that one arm"), from Aux. lemma 37 in the pockets of the
right wall `R` with the certified frontier `M` between the walls (`hsub`, the extremal pockets): attachment progress
along `R` on a no-`C` interval visits a nontrivial arc of `R`; a point of it off `M` lies on the right arc of a pocket
`C'` of `(R, M)` nested in `C` (`exists_subPocket`, `cfPocket_subset_of_sub`), and the attachment of `C'` progresses
on a no-`C'` subinterval, contradicting `hsub`. Pathwise. -/
theorem barrierAttachConst_right_of_sub (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r)
    (hM : IsSimpleProper M) (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M)
      (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (hRM : NoCommonArc R M)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M) {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0))
    (hη0 : η 0 = 0) (hrevR : IsWallReverseVisit R η) (hvisR : IsWallVisited R η)
    (hsub : ∀ q : ℚ, 0 < q → IsChangeConfigInc R M (StripSys.rt q) → 0 < rightLo R M (StripSys.rt q) →
      BarrierAttachConst η (cfPocket R M (StripSys.rt q)) (cfArcR R M (StripSys.rt q))
        (firstHit η (cfArcR R M (StripSys.rt q) 1)) (firstHit η (cfArcR R M (StripSys.rt q) 0))) :
    BarrierAttachConst η (cfPocket R L r) (cfArcR R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) := by
  intro a b hτa hab _ havoid
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  obtain ⟨hlo1, hhi1, hlohi, -⟩ := h.changeCorner_props
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, -, -⟩ := exists_midTimes h hO hcR hcL
  have hord : Disjoint (range M) (rightSideOf (range R)) := by
    have := hO.right_middle; rwa [arcRange_realPath, arcRange_realPath] at this
  set Q : ℝ → ℂ := fun ρ => cfPt (toDisc (Lemma71I.realPath R) ρ) with hQ
  have hQinj := cfPt_toDisc_injOn h.right
  have hy : Q (rightHi R L r) ∈ η '' Icc 0 a := by
    have hv : ∃ t, Q (rightHi R L r) ∈ η '' Icc 0 t := wall_visited hη0 h.right hvisR ⟨hb.trans hlohi, hhi1.2⟩
    have he : Q (rightHi R L r) = cfArcR R L r 1 := by
      simp only [hQ, cfArcR, one_mul, add_sub_cancel]
    rw [he] at hv ⊢
    obtain ⟨hτ0, hτ, -⟩ := firstHit_spec hηc hv
    exact ⟨_, ⟨hτ0, hτa⟩, hτ⟩
  unfold firstVisit
  congr 1
  ext v
  refine ⟨fun hv => ⟨hv.1, ?_⟩, fun hv => ⟨hv.1, image_mono (Icc_subset_Icc_right hab) hv.2⟩⟩
  by_contra hva
  have hΔ : 0 < rightHi R L r - rightLo R L r := sub_pos.2 hlohi
  have hBQ : ∀ w, cfArcR R L r w = Q (rightLo R L r + w * (rightHi R L r - rightLo R L r)) := fun _ => rfl
  have hv1 : v < 1 := lt_of_le_of_ne hv.1.2 fun he => hva (by rw [he, hBQ, one_mul, add_sub_cancel]; exact hy)
  have hcl := isClosed_visited isClosed_Icc hηc hC.cont₁ a
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl v fun hm => hva hm.2
  set d := min (v + ε / 2) 1 with hd
  have hvd : v < d := lt_min (by linarith) hv1
  set ρ₁ := rightLo R L r + v * (rightHi R L r - rightLo R L r) with hρ₁
  set ρ₂ := rightLo R L r + d * (rightHi R L r - rightLo R L r) with hρ₂
  have hρ₁₂ : ρ₁ < ρ₂ := by have := mul_lt_mul_of_pos_right hvd hΔ; linarith
  have hρ₁0 : rightLo R L r ≤ ρ₁ := by have := mul_nonneg hv.1.1 hΔ.le; linarith
  have hρ₂1 : ρ₂ ≤ rightHi R L r := by
    have := mul_le_mul_of_nonneg_right (min_le_right (v + ε / 2) 1) hΔ.le; linarith
  have hnew : ∀ ρ ∈ Icc ρ₁ ρ₂, Q ρ ∈ η '' Icc 0 b ∧ Q ρ ∉ η '' Icc 0 a := by
    intro ρ hρ
    set w := (ρ - rightLo R L r) / (rightHi R L r - rightLo R L r) with hw
    have hwρ : rightLo R L r + w * (rightHi R L r - rightLo R L r) = ρ := by rw [hw]; field_simp; ring
    have hvw : v ≤ w := by rw [hw, le_div_iff₀ hΔ]; linarith [hρ.1]
    have hwd : w ≤ d := by rw [hw, div_le_iff₀ hΔ]; linarith [hρ.2]
    have hw01 : w ∈ Icc (0 : ℝ) 1 := ⟨hv.1.1.trans hvw, hwd.trans (min_le_right _ _)⟩
    have hrev := cfArcR_rev h h0 hη0 hrevR
    refine ⟨?_, fun hwa => ?_⟩
    · have := hrev b v hv.1 w hw01 hvw hv.2
      rwa [hBQ, hwρ] at this
    · refine hball ?_ ⟨hw01, by rw [hBQ, hwρ]; exact hwa⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left (v + ε / 2) 1]
  -- a point of the new arc off `M`
  have hρ₁pos : 0 < ρ₁ := hb.trans_le hρ₁0
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
  obtain ⟨q, hq, h', hLo', hHi', hp'⟩ := exists_subPocket h.right hM hord hp01 hpM
  set r' := StripSys.rt q with hr'
  set p₁ := rightLo R M r' with hp₁
  set p₂ := rightHi R M r' with hp₂
  -- the sub-pocket lies between the corners
  have hcLo : rightLo R L r ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) :=
    ⟨hlo1, σM, ⟨h0σ, hστ.le.trans hτ1⟩, hσa⟩
  have hcHi : rightHi R L r ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath R)) (toDisc (Lemma71I.realPath M)) :=
    ⟨hhi1, τM, ⟨h0σ.trans hστ.le, hτ1⟩, hτb⟩
  have hlo' : rightLo R L r ≤ p₁ := by
    rw [hLo']
    exact le_csSup ⟨1, fun x hx => hx.1.1.2⟩ ⟨hcLo, hlo1.1, hρ₁0.trans hpI.1.le⟩
  have hhi' : p₂ ≤ rightHi R L r := by
    rw [hHi']
    exact csInf_le ⟨0, fun x hx => hx.1.1.1⟩ ⟨hcHi, hpI.2.le.trans hρ₂1, hhi1.2⟩
  have hb' : 0 < p₁ := hb.trans_le hlo'
  have hsubC := cfPocket_subset_of_sub h hb hM hO hcR hcL houter h' hlo' hhi'
  -- two new points of the right arc of `C'`
  set p₀ := (max ρ₁ p₁ + p) / 2 with hp₀
  have hmx : max ρ₁ p₁ < p := max_lt hpI.1 hp'.1
  have hp₀p : p₀ < p := by rw [hp₀]; linarith
  have hp₀lo : max ρ₁ p₁ < p₀ := by rw [hp₀]; linarith
  have hp₀I : p₀ ∈ Icc ρ₁ ρ₂ := ⟨(le_max_left _ _).trans hp₀lo.le, hp₀p.le.trans hpI.2.le⟩
  have hp₁p₀ : p₁ < p₀ := (le_max_right _ _).trans_lt hp₀lo
  have hp₂1 : p₂ ≤ 1 := hhi'.trans hhi1.2
  have hIp : p ∈ Ioc (0 : ℝ) 1 := ⟨hp01.1, hp01.2.le⟩
  have hIp₀ : p₀ ∈ Ioc (0 : ℝ) 1 := ⟨hb'.trans hp₁p₀, (hp₀p.trans hp01.2).le⟩
  have hIp₁ : p₁ ∈ Ioc (0 : ℝ) 1 := ⟨hb', (hp'.1.trans hp01.2).le⟩
  have hIp₂ : p₂ ∈ Ioc (0 : ℝ) 1 := ⟨hp01.1.trans hp'.2, hp₂1⟩
  obtain ⟨hpb, hpa⟩ := hnew p ⟨hpI.1.le, hpI.2.le⟩
  obtain ⟨hp₀b, -⟩ := hnew p₀ hp₀I
  obtain ⟨htp0, htp, -⟩ := firstHit_spec hηc ⟨b, hpb⟩
  obtain ⟨ht₀0, ht₀, -⟩ := firstHit_spec hηc ⟨b, hp₀b⟩
  set tp := firstHit η (Q p) with htpdef
  set t₀ := firstHit η (Q p₀) with ht₀def
  have htpb : tp ≤ b := firstHit_le_of_mem hpb
  have ht₀b : t₀ ≤ b := firstHit_le_of_mem hp₀b
  have hatp : a < tp := lt_of_not_ge fun hle => hpa ⟨tp, ⟨htp0, hle⟩, htp⟩
  have htpt₀ : tp ≤ t₀ :=
    firstHit_le_of_mem (wall_rev h.right hη0 hrevR hIp₀ hIp hp₀p.le ⟨t₀, ⟨ht₀0, le_rfl⟩, ht₀⟩)
  -- the corners of `C'`
  have hB'1 : cfArcR R M r' 1 = Q p₂ := by simp only [hQ, cfArcR, one_mul, add_sub_cancel, hp₂]
  have hB'0 : cfArcR R M r' 0 = Q p₁ := by simp only [hQ, cfArcR, zero_mul, add_zero, hp₁]
  have hvis₂ : ∃ t, Q p₂ ∈ η '' Icc 0 t := wall_visited hη0 h.right hvisR hIp₂
  have hvis₁ : ∃ t, Q p₁ ∈ η '' Icc 0 t := wall_visited hη0 h.right hvisR hIp₁
  obtain ⟨hτ'0, hτ', -⟩ := firstHit_spec hηc hvis₂
  obtain ⟨hσ'0, hσ', -⟩ := firstHit_spec hηc hvis₁
  set τ' := firstHit η (Q p₂) with hτ'def
  set σ' := firstHit η (Q p₁) with hσ'def
  have hτ'tp : τ' < tp := by
    refine lt_of_le_of_ne (firstHit_le_of_mem (wall_rev h.right hη0 hrevR hIp hIp₂ hp'.2.le
      ⟨tp, ⟨htp0, le_rfl⟩, htp⟩)) fun he => ?_
    have : Q p₂ = Q p := by rw [← hτ', ← htp, he]
    exact hp'.2.ne' (hQinj hIp₂ hIp this)
  have ht₀σ' : t₀ < σ' := by
    refine lt_of_le_of_ne (firstHit_le_of_mem (wall_rev h.right hη0 hrevR hIp₁ hIp₀ hp₁p₀.le
      ⟨σ', ⟨hσ'0, le_rfl⟩, hσ'⟩)) fun he => ?_
    have : Q p₀ = Q p₁ := by rw [← ht₀, ← hσ', he]
    exact hp₁p₀.ne' (hQinj hIp₀ hIp₁ this)
  set a' := max a τ' with ha'
  have ha'tp : a' < tp := max_lt hatp hτ'tp
  have hAC := hsub q hq h' hb' a' t₀ (le_max_right _ _ |>.trans_eq' (by rw [hB'1])) (ha'tp.le.trans htpt₀)
    (by rw [hB'0]; exact ht₀σ') fun t ht htC =>
      havoid t ⟨(le_max_left _ _).trans ht.1, ht.2.trans ht₀b⟩ (hsubC htC)
  -- the attachment of `C'` progresses
  have hΔ' : 0 < p₂ - p₁ := sub_pos.2 (hp'.1.trans hp'.2)
  have hB'Q : ∀ s, cfArcR R M r' s = Q (p₁ + s * (p₂ - p₁)) := fun _ => rfl
  set s₀ := (p₀ - p₁) / (p₂ - p₁) with hs₀
  set sp := (p - p₁) / (p₂ - p₁) with hsp
  have hs₀Q : cfArcR R M r' s₀ = Q p₀ := by rw [hB'Q, hs₀]; congr 1; field_simp; ring
  have hspQ : cfArcR R M r' sp = Q p := by rw [hB'Q, hsp]; congr 1; field_simp; ring
  have hs₀sp : s₀ < sp := by rw [hs₀, hsp]; exact div_lt_div_of_pos_right (by linarith) hΔ'
  have hs₀I : s₀ ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith) hΔ'.le, by
    rw [hs₀, div_le_one hΔ']; linarith [hp₀p, hp'.2]⟩
  have hspI : sp ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hp'.1]) hΔ'.le, by
    rw [hsp, div_le_one hΔ']; linarith [hp'.2]⟩
  have hle : firstVisit (fun t => η '' Icc 0 t) (cfArcR R M r') t₀ ≤ s₀ :=
    csInf_le ⟨0, fun x hx => hx.1.1⟩ ⟨hs₀I, by rw [hs₀Q]; exact ⟨t₀, ⟨ht₀0, le_rfl⟩, ht₀⟩⟩
  have h0' := PocketMarks.zero_notMem_closure_of_rightLo_pos h' hb'
  have hrev' := cfArcR_rev h' h0' hη0 hrevR
  have hge : sp ≤ firstVisit (fun t => η '' Icc 0 t) (cfArcR R M r') a' := by
    refine le_csInf ⟨1, ⟨zero_le_one, le_rfl⟩, by
      rw [hB'1]; exact ⟨τ', ⟨hτ'0, le_max_right _ _⟩, hτ'⟩⟩ fun x hx => ?_
    by_contra hlt
    have hvis := hrev' a' x hx.1 sp hspI (not_le.1 hlt).le hx.2
    rw [hspQ] at hvis
    exact absurd (firstHit_le_of_mem hvis) (not_le.2 ha'tp)
  rw [hAC] at hle
  linarith

/-- A change pocket's right corner parameter is positive when its left one is. -/
theorem rightLo_pos_of_leftLo_pos (h : IsChangeConfigInc R L r) (h0 : 0 < leftLo R L r) : 0 < rightLo R L r := by
  obtain ⟨hlo1, -, -, hla, -, -, hopen, -⟩ := h.changeCorner_props
  refine lt_of_le_of_ne hlo1.1 fun he => h0.ne' ?_
  have hαL := h.left.isProperArc.isDiscCrosscut_toDisc
  have hαR := h.right.isProperArc.isDiscCrosscut_toDisc
  refine hαL.inj hla ⟨le_rfl, zero_le_one⟩ ?_
  rw [hopen, openPt, ← he, hαR.zero, hαL.zero]

/-- **The sub-pocket through a left-wall point** (right wall `M`): for a disc time `p ∈ (0, 1)` of `L` off `M`, some
positive rational change time `q` of `L` in the gap of the contacts of `L` with `M` around `p` selects the pocket of
`(M, L)` whose left arc is that gap. -/
theorem exists_subPocketL (hM : IsSimpleProper M) (hL : IsSimpleProper L)
    (hord : Disjoint (range L) (rightSideOf (range M))) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpM : toDisc (Lemma71I.realPath L) p ∉ crossRange (toDisc (Lemma71I.realPath M))) :
    ∃ q : ℚ, 0 < q ∧ IsChangeConfigInc M L (StripSys.rt q) ∧
      leftLo M L (StripSys.rt q) = gapLo (toDisc (Lemma71I.realPath L)) (toDisc (Lemma71I.realPath M)) p ∧
      leftHi M L (StripSys.rt q) = gapHi (toDisc (Lemma71I.realPath L)) (toDisc (Lemma71I.realPath M)) p ∧
      p ∈ Ioo (leftLo M L (StripSys.rt q)) (leftHi M L (StripSys.rt q)) := by
  have hαL := hL.isProperArc.isDiscCrosscut_toDisc
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  obtain ⟨hg, hpg⟩ := isContactGap_gapLo_gapHi hαM hαL ⟨hp.1.le, hp.2.le⟩ hpM
  set l₁ := gapLo (toDisc (Lemma71I.realPath L)) (toDisc (Lemma71I.realPath M)) p
  set l₂ := gapHi (toDisc (Lemma71I.realPath L)) (toDisc (Lemma71I.realPath M)) p
  have hgL := hg
  obtain ⟨hl₁, hl₂, hl, hlgap⟩ := hg
  set m := (l₁ + l₂) / 2 with hm
  have hm1 : m < 1 := by have := hl₂.1.2; rw [hm]; linarith
  have hl₁m : l₁ < m := by rw [hm]; linarith
  have hA := arcTime_lt_arcTime hl₁.1.1 hl₁m hm1
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hA
  have hq0 : (0 : ℝ) < q := (arcTime_nonneg ⟨hl₁.1.1, hl₁m.trans hm1⟩).trans_lt hq1
  have hrt : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have hdq : discTime ((StripSys.rt q : ℝ≥0) : ℝ) ∈ Ioo l₁ l₂ := by
    rw [hrt]
    constructor
    · have := discTime_lt_discTime (arcTime_nonneg ⟨hl₁.1.1, hl₁m.trans hm1⟩) hq1
      rwa [discTime_arcTime (hl₁m.trans hm1)] at this
    · have := discTime_lt_discTime hq0.le hq2
      rw [discTime_arcTime hm1] at this
      exact this.trans (by rw [hm]; linarith)
  have hdqI : discTime ((StripSys.rt q : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨hl₁.1.1.trans hdq.1.le, hdq.2.le.trans hl₂.1.2⟩
  have hoff : toDisc (Lemma71I.realPath L) (discTime ((StripSys.rt q : ℝ≥0) : ℝ)) ∉
      crossRange (toDisc (Lemma71I.realPath M)) := fun hmem => hlgap _ hdq ⟨hdqI, hmem⟩
  have hpos : 0 < StripSys.rt q := by
    rw [← NNReal.coe_pos, hrt]; exact hq0
  have hLH : L (StripSys.rt q) ∈ Hbar := H_subset_Hbar' (hL.2.2.2.1 _ hpos)
  have hoff' : L (StripSys.rt q) ∉ range M := by
    rwa [toDisc_realPath_discTime, hM.isProperArc.cayley_mem_crossRange_iff hLH, arcRange_realPath] at hoff
  have hcfg : IsChangeConfig M L (StripSys.rt q) := ⟨hM, hL, hord, hpos, hoff'⟩
  obtain ⟨hlo, hhi⟩ := gapLo_gapHi_eq hoff hgL hdq
  refine ⟨q, by exact_mod_cast hq0, hcfg.isChangeConfigInc, hlo, hhi, ?_⟩
  rw [leftLo, leftHi, hlo, hhi]
  exact hpg

/-- **Nested pockets, mirror** (`cfPocket_subset_of_sub` with an outer right arm): a pocket of `(M, L)` whose left arc
lies between the corners of the pocket of `(R, L)` lies in that pocket, when `R` is outer beyond `M`. -/
theorem cfPocket_subset_of_subL (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {r' : ℝ≥0} (h' : IsChangeConfigInc M L r') (hlo : leftLo R L r ≤ leftLo M L r')
    (hhi : leftHi M L r' ≤ leftHi R L r) : cfPocket M L r' ⊆ cfPocket R L r := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hla0 := h.leftLo_pos h0
  have hb' : 0 < rightLo M L r' := rightLo_pos_of_leftLo_pos h' (hla0.trans_le hlo)
  have h0' := PocketMarks.zero_notMem_closure_of_rightLo_pos h' hb'
  have hC := h.isCfPocket h0
  have hC' := h'.isCfPocket h0'
  have hαL := h.left.isProperArc.isDiscCrosscut_toDisc
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hO' : WangWu.IsOrderedArcs (Lemma71I.realPath M) (Lemma71I.realPath M) (Lemma71I.realPath L) :=
    ⟨hO.middle, hO.middle, hO.left, Set.disjoint_left.2 fun _ hz hr => hr.1.2 hz, hO.middle_left⟩
  have hC'l : changePocket M L r' ⊆ leftSideOf (range M) := R7FaceSelect.changePocket_subset_left_of_order h' hO'
  refine Sec6.subset_of_isPreconnected_of_disjoint_frontier hC'.isConnected.isPreconnected hC.isOpen ?_ ?_
  · obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, hin, -⟩ := exists_midTimes h hO hcR hcL
    have hjm := h'.inc
    obtain ⟨hg', hj1, hj2, -⟩ := h'.changeCorners
    obtain ⟨-, -, -, hla, hlb, -, hopen, hclose⟩ := h.changeCorner_props
    obtain ⟨hm1, hm2, hmm, -⟩ := h'.changeCorner_props
    have hσI : σM ∈ Icc (0 : ℝ) 1 := ⟨h0σ, hστ.le.trans hτ1⟩
    have hτI : τM ∈ Icc (0 : ℝ) 1 := ⟨h0σ.trans hστ.le, hτ1⟩
    have hcLo : σM ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath M)) (toDisc (Lemma71I.realPath L)) :=
      ⟨hσI, leftLo R L r, hla, hopen.trans hσa.symm⟩
    have hcHi : τM ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath M)) (toDisc (Lemma71I.realPath L)) :=
      ⟨hτI, leftHi R L r, hlb, hclose.trans hτb.symm⟩
    have hjLo : contactMap (toDisc (Lemma71I.realPath M)) (toDisc (Lemma71I.realPath L)) σM = leftLo R L r :=
      contactMap_eq hαL hla (hσa.trans hopen.symm)
    have hjHi : contactMap (toDisc (Lemma71I.realPath M)) (toDisc (Lemma71I.realPath L)) τM = leftHi R L r :=
      contactMap_eq hαL hlb (hτb.trans hclose.symm)
    have hσl : σM ≤ rightLo M L r' := by
      by_contra hlt
      have := hjm hg'.1 hcLo (not_le.1 hlt)
      rw [hj1, hjLo] at this
      linarith
    have hlτ : rightHi M L r' ≤ τM := by
      by_contra hlt
      have := hjm hcHi hg'.2.1 (not_le.1 hlt)
      rw [hj2, hjHi] at this
      linarith
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
        ⟨hPcl, by rwa [hC.isOpen.interior_eq]⟩
      rw [hC.frontier_eq, hP] at hfr
      rcases hfr with ⟨u, -, hu⟩ | ⟨u, -, hu⟩
      · exact htR (mem_range_of_cfPt_toDisc h.right hMH hu)
      · exact hsL (mem_range_of_cfPt_toDisc h.left hMH hu)
    have hΔ : 0 < rightHi M L r' - rightLo M L r' := sub_pos.2 hmm
    have hPcl' : cfPt (toDisc (Lemma71I.realPath M) s) ∈ closure (cfPocket M L r') := by
      refine frontier_subset_closure ?_
      rw [hC'.frontier_eq]
      refine Or.inl ⟨(s - rightLo M L r') / (rightHi M L r' - rightLo M L r'), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (sub_nonneg.2 hts.1.le) hΔ.le
      · rw [div_le_one hΔ]; linarith [hts.2]
      · simp only [cfArcR]; congr 2; field_simp; ring
    obtain ⟨z, hz⟩ := mem_closure_iff.1 hPcl' _ hC.isOpen hPC
    exact ⟨z, hz.2, hz.1⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hz
    have hw' := h'.changePocket_subset hw
    rw [hC.frontier_eq] at hz
    rcases hz with ⟨u, -, hu⟩ | ⟨u, -, hu⟩
    · rcases houter (mem_range_of_cfPt_toDisc h.right hw'.1 hu) with hr | hm
      · have hd := (hM.isProperArc).disjoint_leftSideOf_rightSideOf
        rw [arcRange_realPath] at hd
        exact Set.disjoint_left.1 hd (hC'l hw) hr
      · exact hw'.2 (Or.inl hm)
    · exact hw'.2 (Or.inr (mem_range_of_cfPt_toDisc h.left hw'.1 hu))

/-- **Aux. lemma 37 along the contained left arm of a bounded pocket whose right arm is outer** (the mirror of
`barrierAttachConst_right_of_sub`), from Aux. lemma 37 in the pockets of the certified frontier `M` with the left wall
`L` (`hsub`, the extremal pockets). Pathwise. -/
theorem barrierAttachConst_left_of_sub (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r)
    (hM : IsSimpleProper M) (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M)
      (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (hLM : NoCommonArc L M)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M) {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0))
    (hη0 : η 0 = 0) (hrevL : IsWallReverseVisit L η) (hvisL : IsWallVisited L η)
    (hsub : ∀ q : ℚ, 0 < q → IsChangeConfigInc M L (StripSys.rt q) → 0 < rightLo M L (StripSys.rt q) →
      BarrierAttachConst η (cfPocket M L (StripSys.rt q)) (cfArcL M L (StripSys.rt q))
        (firstHit η (cfArcR M L (StripSys.rt q) 1)) (firstHit η (cfArcR M L (StripSys.rt q) 0))) :
    BarrierAttachConst η (cfPocket R L r) (cfArcL R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) := by
  intro a b hτa hab _ havoid
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  have hla0 := h.leftLo_pos h0
  obtain ⟨-, -, -, hlo1, hhi1, hlohi, hopen, hclose⟩ := h.changeCorner_props
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, -, -⟩ := exists_midTimes h hO hcR hcL
  have hord : Disjoint (range L) (rightSideOf (range M)) := by
    have := hO.middle_left; rwa [arcRange_realPath, arcRange_realPath] at this
  set Q : ℝ → ℂ := fun ρ => cfPt (toDisc (Lemma71I.realPath L) ρ) with hQ
  have hQinj := cfPt_toDisc_injOn h.left
  have hy : Q (leftHi R L r) ∈ η '' Icc 0 a := by
    have hv : ∃ t, Q (leftHi R L r) ∈ η '' Icc 0 t := wall_visited hη0 h.left hvisL ⟨hla0.trans hlohi, hhi1.2⟩
    have he : Q (leftHi R L r) = cfArcR R L r 1 := by
      rw [← hC.seed]; simp only [hQ, cfArcL, one_mul, add_sub_cancel]
    rw [he] at hv ⊢
    obtain ⟨hτ0, hτ, -⟩ := firstHit_spec hηc hv
    exact ⟨_, ⟨hτ0, hτa⟩, hτ⟩
  unfold firstVisit
  congr 1
  ext v
  refine ⟨fun hv => ⟨hv.1, ?_⟩, fun hv => ⟨hv.1, image_mono (Icc_subset_Icc_right hab) hv.2⟩⟩
  by_contra hva
  have hΔ : 0 < leftHi R L r - leftLo R L r := sub_pos.2 hlohi
  have hBQ : ∀ w, cfArcL R L r w = Q (leftLo R L r + w * (leftHi R L r - leftLo R L r)) := fun _ => rfl
  have hv1 : v < 1 := lt_of_le_of_ne hv.1.2 fun he => hva (by rw [he, hBQ, one_mul, add_sub_cancel]; exact hy)
  have hcl := isClosed_visited isClosed_Icc hηc hC.cont₂ a
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl v fun hm => hva hm.2
  set d := min (v + ε / 2) 1 with hd
  have hvd : v < d := lt_min (by linarith) hv1
  set ρ₁ := leftLo R L r + v * (leftHi R L r - leftLo R L r) with hρ₁
  set ρ₂ := leftLo R L r + d * (leftHi R L r - leftLo R L r) with hρ₂
  have hρ₁₂ : ρ₁ < ρ₂ := by have := mul_lt_mul_of_pos_right hvd hΔ; linarith
  have hρ₁0 : leftLo R L r ≤ ρ₁ := by have := mul_nonneg hv.1.1 hΔ.le; linarith
  have hρ₂1 : ρ₂ ≤ leftHi R L r := by
    have := mul_le_mul_of_nonneg_right (min_le_right (v + ε / 2) 1) hΔ.le; linarith
  have hnew : ∀ ρ ∈ Icc ρ₁ ρ₂, Q ρ ∈ η '' Icc 0 b ∧ Q ρ ∉ η '' Icc 0 a := by
    intro ρ hρ
    set w := (ρ - leftLo R L r) / (leftHi R L r - leftLo R L r) with hw
    have hwρ : leftLo R L r + w * (leftHi R L r - leftLo R L r) = ρ := by rw [hw]; field_simp; ring
    have hvw : v ≤ w := by rw [hw, le_div_iff₀ hΔ]; linarith [hρ.1]
    have hwd : w ≤ d := by rw [hw, div_le_iff₀ hΔ]; linarith [hρ.2]
    have hw01 : w ∈ Icc (0 : ℝ) 1 := ⟨hv.1.1.trans hvw, hwd.trans (min_le_right _ _)⟩
    have hrev := cfArcL_rev h h0 hη0 hrevL
    refine ⟨?_, fun hwa => ?_⟩
    · have := hrev b v hv.1 w hw01 hvw hv.2
      rwa [hBQ, hwρ] at this
    · refine hball ?_ ⟨hw01, by rw [hBQ, hwρ]; exact hwa⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left (v + ε / 2) 1]
  have hρ₁pos : 0 < ρ₁ := hla0.trans_le hρ₁0
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
  obtain ⟨q, hq, h', hLo', hHi', hp'⟩ := exists_subPocketL hM h.left hord hp01 hpM
  set r' := StripSys.rt q with hr'
  set p₁ := leftLo M L r' with hp₁
  set p₂ := leftHi M L r' with hp₂
  have hcLo : leftLo R L r ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath L)) (toDisc (Lemma71I.realPath M)) :=
    ⟨hlo1, σM, ⟨h0σ, hστ.le.trans hτ1⟩, hσa.trans hopen.symm⟩
  have hcHi : leftHi R L r ∈ Sec7.pocketContactSet (toDisc (Lemma71I.realPath L)) (toDisc (Lemma71I.realPath M)) :=
    ⟨hhi1, τM, ⟨h0σ.trans hστ.le, hτ1⟩, hτb.trans hclose.symm⟩
  have hlo' : leftLo R L r ≤ p₁ := by
    rw [hLo']
    exact le_csSup ⟨1, fun x hx => hx.1.1.2⟩ ⟨hcLo, hlo1.1, hρ₁0.trans hpI.1.le⟩
  have hhi' : p₂ ≤ leftHi R L r := by
    rw [hHi']
    exact csInf_le ⟨0, fun x hx => hx.1.1.1⟩ ⟨hcHi, hpI.2.le.trans hρ₂1, hhi1.2⟩
  have hb'L : 0 < p₁ := hla0.trans_le hlo'
  have hb' : 0 < rightLo M L r' := rightLo_pos_of_leftLo_pos h' hb'L
  have hsubC := cfPocket_subset_of_subL h hb hM hO hcR hcL houter h' hlo' hhi'
  set p₀ := (max ρ₁ p₁ + p) / 2 with hp₀
  have hmx : max ρ₁ p₁ < p := max_lt hpI.1 hp'.1
  have hp₀p : p₀ < p := by rw [hp₀]; linarith
  have hp₀lo : max ρ₁ p₁ < p₀ := by rw [hp₀]; linarith
  have hp₀I : p₀ ∈ Icc ρ₁ ρ₂ := ⟨(le_max_left _ _).trans hp₀lo.le, hp₀p.le.trans hpI.2.le⟩
  have hp₁p₀ : p₁ < p₀ := (le_max_right _ _).trans_lt hp₀lo
  have hp₂1 : p₂ ≤ 1 := hhi'.trans hhi1.2
  have hIp : p ∈ Ioc (0 : ℝ) 1 := ⟨hp01.1, hp01.2.le⟩
  have hIp₀ : p₀ ∈ Ioc (0 : ℝ) 1 := ⟨hb'L.trans hp₁p₀, (hp₀p.trans hp01.2).le⟩
  have hIp₁ : p₁ ∈ Ioc (0 : ℝ) 1 := ⟨hb'L, (hp'.1.trans hp01.2).le⟩
  have hIp₂ : p₂ ∈ Ioc (0 : ℝ) 1 := ⟨hp01.1.trans hp'.2, hp₂1⟩
  obtain ⟨hpb, hpa⟩ := hnew p ⟨hpI.1.le, hpI.2.le⟩
  obtain ⟨hp₀b, -⟩ := hnew p₀ hp₀I
  obtain ⟨htp0, htp, -⟩ := firstHit_spec hηc ⟨b, hpb⟩
  obtain ⟨ht₀0, ht₀, -⟩ := firstHit_spec hηc ⟨b, hp₀b⟩
  set tp := firstHit η (Q p) with htpdef
  set t₀ := firstHit η (Q p₀) with ht₀def
  have htpb : tp ≤ b := firstHit_le_of_mem hpb
  have ht₀b : t₀ ≤ b := firstHit_le_of_mem hp₀b
  have hatp : a < tp := lt_of_not_ge fun hle => hpa ⟨tp, ⟨htp0, hle⟩, htp⟩
  have htpt₀ : tp ≤ t₀ :=
    firstHit_le_of_mem (wall_rev h.left hη0 hrevL hIp₀ hIp hp₀p.le ⟨t₀, ⟨ht₀0, le_rfl⟩, ht₀⟩)
  have hb0' := PocketMarks.zero_notMem_closure_of_rightLo_pos h' hb'
  have hC' := h'.isCfPocket hb0'
  have hB'1 : cfArcR M L r' 1 = Q p₂ := by
    rw [← hC'.seed]; simp only [hQ, cfArcL, one_mul, add_sub_cancel, hp₂]
  have hB'0 : cfArcR M L r' 0 = Q p₁ := by
    rw [← hC'.junction]; simp only [hQ, cfArcL, zero_mul, add_zero, hp₁]
  have hvis₂ : ∃ t, Q p₂ ∈ η '' Icc 0 t := wall_visited hη0 h.left hvisL hIp₂
  have hvis₁ : ∃ t, Q p₁ ∈ η '' Icc 0 t := wall_visited hη0 h.left hvisL hIp₁
  obtain ⟨hτ'0, hτ', -⟩ := firstHit_spec hηc hvis₂
  obtain ⟨hσ'0, hσ', -⟩ := firstHit_spec hηc hvis₁
  set τ' := firstHit η (Q p₂) with hτ'def
  set σ' := firstHit η (Q p₁) with hσ'def
  have hτ'tp : τ' < tp := by
    refine lt_of_le_of_ne (firstHit_le_of_mem (wall_rev h.left hη0 hrevL hIp hIp₂ hp'.2.le
      ⟨tp, ⟨htp0, le_rfl⟩, htp⟩)) fun he => ?_
    have : Q p₂ = Q p := by rw [← hτ', ← htp, he]
    exact hp'.2.ne' (hQinj hIp₂ hIp this)
  have ht₀σ' : t₀ < σ' := by
    refine lt_of_le_of_ne (firstHit_le_of_mem (wall_rev h.left hη0 hrevL hIp₁ hIp₀ hp₁p₀.le
      ⟨σ', ⟨hσ'0, le_rfl⟩, hσ'⟩)) fun he => ?_
    have : Q p₀ = Q p₁ := by rw [← ht₀, ← hσ', he]
    exact hp₁p₀.ne' (hQinj hIp₀ hIp₁ this)
  set a' := max a τ' with ha'
  have ha'tp : a' < tp := max_lt hatp hτ'tp
  have hAC := hsub q hq h' hb' a' t₀ (le_max_right _ _ |>.trans_eq' (by rw [hB'1])) (ha'tp.le.trans htpt₀)
    (by rw [hB'0]; exact ht₀σ') fun t ht htC =>
      havoid t ⟨(le_max_left _ _).trans ht.1, ht.2.trans ht₀b⟩ (hsubC htC)
  have hΔ' : 0 < p₂ - p₁ := sub_pos.2 (hp'.1.trans hp'.2)
  have hB'Q : ∀ s, cfArcL M L r' s = Q (p₁ + s * (p₂ - p₁)) := fun _ => rfl
  set s₀ := (p₀ - p₁) / (p₂ - p₁) with hs₀
  set sp := (p - p₁) / (p₂ - p₁) with hsp
  have hs₀Q : cfArcL M L r' s₀ = Q p₀ := by rw [hB'Q, hs₀]; congr 1; field_simp; ring
  have hspQ : cfArcL M L r' sp = Q p := by rw [hB'Q, hsp]; congr 1; field_simp; ring
  have hs₀sp : s₀ < sp := by rw [hs₀, hsp]; exact div_lt_div_of_pos_right (by linarith) hΔ'
  have hs₀I : s₀ ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith) hΔ'.le, by
    rw [hs₀, div_le_one hΔ']; linarith [hp₀p, hp'.2]⟩
  have hspI : sp ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hp'.1]) hΔ'.le, by
    rw [hsp, div_le_one hΔ']; linarith [hp'.2]⟩
  have hle : firstVisit (fun t => η '' Icc 0 t) (cfArcL M L r') t₀ ≤ s₀ :=
    csInf_le ⟨0, fun x hx => hx.1.1⟩ ⟨hs₀I, by rw [hs₀Q]; exact ⟨t₀, ⟨ht₀0, le_rfl⟩, ht₀⟩⟩
  have hrev' := cfArcL_rev h' hb0' hη0 hrevL
  have hge : sp ≤ firstVisit (fun t => η '' Icc 0 t) (cfArcL M L r') a' := by
    refine le_csInf ⟨1, ⟨zero_le_one, le_rfl⟩, by
      rw [hC'.seed, hB'1]; exact ⟨τ', ⟨hτ'0, le_max_right _ _⟩, hτ'⟩⟩ fun x hx => ?_
    by_contra hlt
    have hvis := hrev' a' x hx.1 sp hspI (not_le.1 hlt).le hx.2
    rw [hspQ] at hvis
    exact absurd (firstHit_le_of_mem hvis) (not_le.2 ha'tp)
  rw [hAC] at hle
  linarith

end Sub

end InteractingSLE.Sec7.OuterGeom
