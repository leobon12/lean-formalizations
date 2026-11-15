/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketJordanChange
import InteractingSLE.Spec.Sec7.StripSysSel
import InteractingSLE.Spec.Sec7.Lemma71QSide
import InteractingSLE.Spec.Sec7.OuterGeomSub

/-!
# R.6's nested pockets: deterministic selection

PROVE-R6-NESTED. Supplement §5.6 (`source/spec/p433-480.md` L1032–L1048, pp. 476–477): "Choose a time when the tip
is in `C` but not on `β_R` … The tip lies in a `β_R`–`γ` pocket `U ⊂ C`", and for two outer arms "Inside it take the
extremal pocket `U` bounded by `β_R, β_L`". These are deterministic planar facts about simple proper curves from the
common seed, proved here in original coordinates.

* `exists_rat_changePocket_eq`: every component between two ordered simple proper curves is the change pocket at a
  **rational** change parameter (so the inner pockets form a countable family indexed by `ℚ`);
* `exists_rat_nested_changePocket`: a point of a change pocket of `(R, L)` that is a between point of a second pair
  `(R', L')` whose walls keep `R` on the right of `R'` and `L` on the left of `L'` lies in a change pocket of
  `(R', L')` at a rational parameter, and that pocket is contained in the first one.

No probability is used. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal

namespace InteractingSLE.Sec7.R6Nest

open WangWu PocketCoord PocketJordan Lemma71I

/-- A rational strictly between the disc parameters `a < b` of `[0, 1)` is the disc time of a positive rational
original time. -/
theorem exists_rat_discTime_mem {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ s : ℚ, 0 < s ∧ discTime (StripSys.rt s) ∈ Ioo a b := by
  have ha1 : a < 1 := lt_of_lt_of_le hab hb
  set m := (a + b) / 2 with hm
  have ham : a < m := by rw [hm]; linarith
  have hmb : m < b := by rw [hm]; linarith
  have hm1 : m < 1 := lt_of_lt_of_le hmb hb
  have h₁ : discTime (arcTime a) = a := discTime_arcTime ha1
  have h₂ : discTime (arcTime m) = m := discTime_arcTime hm1
  have ht₁ : 0 ≤ arcTime a := arcTime_nonneg ⟨ha, ha1⟩
  have hlt : arcTime a < arcTime m := by
    rcases lt_trichotomy (arcTime a) (arcTime m) with h | h | h
    · exact h
    · have := congrArg discTime h
      rw [h₁, h₂] at this
      exact absurd this (ne_of_lt ham)
    · have := discTime_lt_discTime (arcTime_nonneg ⟨ha.trans ham.le, hm1⟩) h
      rw [h₁, h₂] at this
      exact absurd this (not_lt.2 ham.le)
  obtain ⟨s, hs₁, hs₂⟩ := exists_rat_btwn hlt
  have hs0 : (0 : ℝ) < s := lt_of_le_of_lt ht₁ hs₁
  refine ⟨s, by exact_mod_cast hs0, ?_⟩
  rw [StripSys.coe_rt (by exact_mod_cast hs0.le)]
  refine ⟨?_, ?_⟩
  · have := discTime_lt_discTime ht₁ hs₁
    rwa [h₁] at this
  · have := discTime_lt_discTime hs0.le hs₂
    rw [h₂] at this
    exact this.trans hmb

/-- **Every component between two ordered simple proper curves is a change pocket at a rational parameter**:
its `L`-arc contains a rational change point off `R`. -/
theorem exists_rat_changePocket_eq {R L : ℝ≥0 → ℂ} (hR : IsSimpleProper R) (hL : IsSimpleProper L)
    (hord : Disjoint (range L) (rightSideOf (range R))) {U : Set ℂ}
    (hU : U ∈ betweenComponents (range R) (range L)) :
    ∃ s : ℚ, 0 < s ∧ IsChangeConfig R L (StripSys.rt s) ∧ U = changePocket R L (StripSys.rt s) := by
  have hU' : U ∈ betweenComponents (arcRange (Lemma71I.realPath R)) (arcRange (Lemma71I.realPath L)) := by
    rwa [arcRange_realPath, arcRange_realPath]
  have hord' : Disjoint (arcRange (Lemma71I.realPath L)) (rightSideOf (arcRange (Lemma71I.realPath R))) := by
    rwa [arcRange_realPath, arcRange_realPath]
  obtain ⟨a, b, hg, hUeq⟩ := exists_contactGap_of_mem_betweenComponents hR.isProperArc hL.isProperArc hord' hU'
  have hα := hR.isProperArc.isDiscCrosscut_toDisc
  have hβ := hL.isProperArc.isDiscCrosscut_toDisc
  have hdisc := (disjoint_rightSideOf_iff hR.isProperArc hL.isProperArc).1 hord'
  have hjm := strictMonoOn_contactMap hα hβ hdisc
  obtain ⟨hg', -, -⟩ := OuterGeom.isContactGap_swap' hα hβ hjm hg
  obtain ⟨hja, hjb, hjab, hjgap⟩ := hg'
  obtain ⟨s, hs0, hsI⟩ := exists_rat_discTime_mem hja.1.1 hjab hjb.1.2
  set r := StripSys.rt s with hr
  have hrpos : 0 < r := by
    rw [hr, StripSys.rt, Real.toNNReal_pos]
    exact_mod_cast hs0
  have hLrH : L r ∈ H := hL.2.2.2.1 r hrpos
  have hLrHbar : L r ∈ Hbar := le_of_lt (show (0 : ℝ) < (L r).im from hLrH)
  have hoff : L r ∉ range R := by
    intro hmem
    have hc : cayley (L r) ∈ crossRange (toDisc (Lemma71I.realPath R)) := by
      rw [hR.isProperArc.cayley_mem_crossRange_iff hLrHbar, arcRange_realPath]
      exact hmem
    rw [← toDisc_realPath_discTime] at hc
    refine hjgap _ hsI ⟨⟨hja.1.1.trans hsI.1.le, hsI.2.le.trans hjb.1.2⟩, ?_⟩
    obtain ⟨u, hu, hu'⟩ := hc
    exact ⟨u, hu, hu'⟩
  have hcfg : IsChangeConfig R L r := ⟨hR, hL, hord, hrpos, hoff⟩
  have hfr := image_subset_frontier_pocket hα hβ hjm hg
  have hcl : cayley (L r) ∈ closure (cayley '' U) := by
    rw [hUeq, ← toDisc_realPath_discTime]
    exact frontier_subset_closure (hfr ⟨_, ⟨hsI.1.le, hsI.2.le⟩, rfl⟩)
  have hUH := IsChangeConfig.subset_H_of_mem_betweenComponents hU
  have hclU : L r ∈ closure U := by
    have := mem_closure_image (continuousAt_cayleyInv (cayley_ne_one_of_Hbar hLrHbar)) hcl
    rwa [cayleyInv_cayley_of_mem_Hbar hLrHbar, image_image,
      image_congr (fun y hy => cayleyInv_cayley_of_mem_Hbar
        (le_of_lt (show (0 : ℝ) < y.im from hUH hy))), image_id'] at this
  exact ⟨s, hs0, hcfg, hcfg.changePocket_eq_of hU hclU⟩

/-- **The nested pocket** (supplement p. 476, "The tip lies in a `β_R`–`γ` pocket `U ⊂ C`"): let `z` lie in the change
pocket of `(R, L)` and be a between point of a second ordered pair `(R', L')` of simple proper curves, such that every
point of `R` in `ℍ` is on `R'` or on its right and every point of `L` in `ℍ` is on `L'` or on its left. Then `z` lies
in a change pocket of `(R', L')` at a rational parameter, and that pocket is contained in the change pocket of
`(R, L)`. -/
theorem exists_rat_nested_changePocket {R L R' L' : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r)
    (hR' : IsSimpleProper R') (hL' : IsSimpleProper L') (hord : Disjoint (range L') (rightSideOf (range R')))
    (hRout : ∀ w ∈ range R, w ∈ H → w ∈ rightSideOf (range R') ∪ range R')
    (hLout : ∀ w ∈ range L, w ∈ H → w ∈ leftSideOf (range L') ∪ range L')
    {z : ℂ} (hz : z ∈ changePocket R L r) (hz' : z ∉ range R' ∪ range L')
    (hzR : z ∉ rightSideOf (range R')) (hzL : z ∉ leftSideOf (range L')) :
    ∃ s : ℚ, 0 < s ∧ IsChangeConfig R' L' (StripSys.rt s) ∧ z ∈ changePocket R' L' (StripSys.rt s) ∧
      changePocket R' L' (StripSys.rt s) ⊆ changePocket R L r := by
  have hzH : z ∈ H := h.changePocket_subset_H hz
  set U := connectedComponentIn (H \ (range R' ∪ range L')) z with hUdef
  have hU : U ∈ betweenComponents (range R') (range L') := ⟨z, ⟨hzH, hz'⟩, hzR, hzL, rfl⟩
  obtain ⟨s, hs0, hcfg, hUeq⟩ := exists_rat_changePocket_eq hR' hL' hord hU
  have hzU : z ∈ U := mem_connectedComponentIn ⟨hzH, hz'⟩
  refine ⟨s, hs0, hcfg, hUeq ▸ hzU, ?_⟩
  rw [← hUeq]
  obtain ⟨z₀, -, hCeq, -⟩ := h.changePocket_eq
  have hzC : z ∈ connectedComponentIn (H \ (range R ∪ range L)) z₀ := hCeq ▸ hz
  rw [hCeq, connectedComponentIn_eq hzC]
  refine (isPreconnected_connectedComponentIn).subset_connectedComponentIn hzU ?_
  intro w hw
  have hwb := Lemma71Pin.isBetweenPt_of_mem hR' hL' hU hw
  obtain ⟨⟨hwH, hwRL⟩, hwR, hwL⟩ := (Lemma71Pin.isBetweenPt_iff hR' hL').1 hwb
  refine ⟨hwH, ?_⟩
  rintro (hwR' | hwL')
  · rcases hRout w hwR' hwH with h1 | h1
    · exact hwR h1
    · exact hwRL (Or.inl h1)
  · rcases hLout w hwL' hwH with h1 | h1
    · exact hwL h1
    · exact hwRL (Or.inr h1)

/-- Membership in a pocket of the counterflow chart is membership of the inverted point in the change pocket. -/
theorem mem_cfPocket_iff {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {w : ℂ} :
    w ∈ cfPocket R L r ↔ negInv w ∈ changePocket R L r := by
  have hinv : ∀ z : ℂ, negInv (negInv z) = z := fun z => by simp only [negInv, inv_neg, inv_inv, neg_neg]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [hinv]
  · intro hw
    exact ⟨negInv w, hw, hinv w⟩

/-- **The nested pocket in the counterflow chart** (`exists_rat_nested_changePocket` after the inversion
`m(z) = −1/z`). -/
theorem exists_rat_nested_cfPocket {R L R' L' : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r)
    (hR' : IsSimpleProper R') (hL' : IsSimpleProper L') (hord : Disjoint (range L') (rightSideOf (range R')))
    (hRout : ∀ w ∈ range R, w ∈ H → w ∈ rightSideOf (range R') ∪ range R')
    (hLout : ∀ w ∈ range L, w ∈ H → w ∈ leftSideOf (range L') ∪ range L')
    {w : ℂ} (hw : w ∈ cfPocket R L r) (hw' : negInv w ∉ range R' ∪ range L')
    (hwR : negInv w ∉ rightSideOf (range R')) (hwL : negInv w ∉ leftSideOf (range L')) :
    ∃ s : ℚ, 0 < s ∧ IsChangeConfig R' L' (StripSys.rt s) ∧ w ∈ cfPocket R' L' (StripSys.rt s) ∧
      cfPocket R' L' (StripSys.rt s) ⊆ cfPocket R L r := by
  obtain ⟨s, hs, hcfg, hzU, hsub⟩ := exists_rat_nested_changePocket h hR' hL' hord hRout hLout
    (mem_cfPocket_iff.1 hw) hw' hwR hwL
  exact ⟨s, hs, hcfg, mem_cfPocket_iff.2 hzU, image_mono hsub⟩

/-- A point of a change pocket is a between point of its walls (global order). -/
theorem isBetweenPt_of_mem_changePocket {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfig R L r) {z : ℂ}
    (hz : z ∈ changePocket R L r) : Lemma71Pin.IsBetweenPt (range R) (range L) z := by
  obtain ⟨C, hC, hcl⟩ := h.exists_changePocket
  rw [← h.changePocket_eq_of hC hcl] at hz
  exact Lemma71Pin.isBetweenPt_of_mem h.right h.left hC hz

end InteractingSLE.Sec7.R6Nest
