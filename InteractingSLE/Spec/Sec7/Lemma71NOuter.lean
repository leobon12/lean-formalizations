/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71NArc
import InteractingSLE.Spec.Sec7.Prop74BOrient
import InteractingSLE.WangWu.Prop418Side
import InteractingSLE.Spec.Sec7.Lemma613Geom

/-!
# Lemma 7.1's side limits: Proposition 6.1 for the two outer curves in the pocket chart

Packet PROVE-LEMMA71N (specification Remark 6.7, `source/spec/p145-192.md` L566–L590; supplement §2.3, "An exact
common branch for a two-arc pocket", `source/spec/p433-480.md` L472–L520; Lemma 7.1's proof, p. 225: "in the active
component they have the two seed heights (CPF2), with the inherited logarithmic-derivative branch").

The side limits of the active component along the outer arcs reduce to those of the pocket chart itself
(`Lemma71NArc.lean`, `OuterSideLimit`). This file proves the pathwise geometry and the assembly of those limits:

* `IsPocketFrame`: the pathwise pocket frame (two ordered simple proper walls `β` (left) and `α` (right), a component
  `C` between them which is a marked pocket of `α`, a conformal chart with boundary map `Ψ`);
* **`IsPocketFrame.land_neg`, `IsPocketFrame.land_pos`** (where the chart inverse lands): at a negative chart point the
  inverse lands at a point `β s`, `s > 0`, of the left wall off the right wall; at a positive chart point at a point
  `α s` of the right wall off the left wall. The first is the orientation of the boundary map
  (`Prop74B.pocketChartOrientationStatement`); the second follows by intermediate values along the wall arc, which
  `Ψ` maps onto the positive half-line, and the contact gap of the pocket (Aux. lemma 33, `isContactGap`);
* `exists_neg_tendsto_of_leftSideOf` (the mirror of `Lemma613.exists_pos_tendsto_of_rightSideOf`),
  `exists_ball_notMem_range`, `exists_ball_tail`;
* **`wall_sideLimit`**: one wall's side limit from Proposition 3.8 (the outer union against the wall's stopped prefix),
  the single-curve side height and the branch;
* `IsPocketBranch`: the inherited branch (the deterministic normalization (2) of supplement §2.3, in the chart);
* **`outerSideLimit_of_heights`**: `OuterSideLimit` of the shifted chart, from the branch, Proposition 3.8 and the
  single-curve heights of the two walls (pathwise).

Conditional helpers (on the branch and on the pathwise heights and comparisons); they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.Lemma71N

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71K (IsMarkedPocket wallPt)

/-- **The pathwise pocket frame**: the two outer curves (`α` right wall, `β` left wall), simple proper and ordered, a
component `C` between them which is a marked pocket `[a, b]` of `α`, and a conformal chart `c` of `C` onto `ℍ` with
boundary map `Ψ` (continuous and injective on `K = cl(cayley C) ∖ {α̃ b}`, `ℍ̄`-valued, `0` at the opening point,
`∞` at the closing point, `c = Ψ ∘ cayley` on `C`). -/
structure IsPocketFrame (β α : ℝ≥0 → ℂ) (C : Set ℂ) (c : Chart) (Ψ : ℂ → ℂ) (a b : ℝ) : Prop where
  hβ : Lemma71I.IsSimpleProper β
  hα : Lemma71I.IsSimpleProper α
  hord : range β ⊆ closedLeftSide α
  hC : C ∈ betweenComponents (range α) (range β)
  hM : IsMarkedPocket α C a b
  hc : c.IsConformal
  hdom : (c.dom : Set ℂ) = C
  hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {wallPt α b})
  hΨi : InjOn Ψ (closure (cayley '' C) \ {wallPt α b})
  hΨH : MapsTo Ψ (closure (cayley '' C) \ {wallPt α b}) Hbar
  hΨ0 : Ψ (wallPt α a) = 0
  hΨtop : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {wallPt α b}] (wallPt α b)) atTop
  hΨe : ∀ x ∈ C, c.1 x = Ψ (cayley x)
  hfr : frontier C ∩ H ⊆ range β ∪ range α

namespace IsPocketFrame

variable {β α : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ}

theorem subset_H (hF : IsPocketFrame β α C c Ψ a b) : C ⊆ H := fun _ hz =>
  (Prop74B.subset_of_mem_betweenComponents hF.hC hz).1

theorem isOpen (hF : IsPocketFrame β α C c Ψ a b) : IsOpen C := hF.hdom ▸ c.dom.isOpen

theorem isOpen_image (hF : IsPocketFrame β α C c Ψ a b) : IsOpen (cayley '' C) :=
  SmallGammaGeodesics.CC.isOpen_image_conf hF.isOpen
    (QuantumZipper.CA.differentiableOn_cayley_Hbar.mono fun z hz =>
      show (0 : ℝ) ≤ z.im from le_of_lt (hF.subset_H hz))
    (QuantumZipper.CA.bijOn_cayley_H.injOn.mono hF.subset_H)

theorem closePt_notMem (hF : IsPocketFrame β α C c Ψ a b) : wallPt α b ∉ cayley '' C := by
  have hf := hF.hM.2.2.2.2.2.2.1
  rw [hF.isOpen_image.frontier_eq] at hf
  exact hf.2

theorem one_notMem (hF : IsPocketFrame β α C c Ψ a b) : (1 : ℂ) ∉ closure (cayley '' C) \ {wallPt α b} := by
  rintro ⟨h1c, h1b⟩
  have hw1 : wallPt α 1 = 1 := WangWu.toDisc_one _
  have hmemI : (1 : ℝ) ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt α s ∈ closure (cayley '' C)} :=
    ⟨⟨zero_le_one, le_rfl⟩, by rw [hw1]; exact h1c⟩
  rw [hF.hM.2.2.2.1] at hmemI
  have hb1 : b = 1 := le_antisymm hF.hM.2.2.1 hmemI.2
  exact h1b (Set.mem_singleton_iff.2 (by rw [hb1, hw1]))

theorem isConformalBijection (hF : IsPocketFrame β α C c Ψ a b) : IsConformalBijection c.1 C H := by
  have hc := hF.hc
  rw [← hF.hdom]
  refine ⟨hc.differentiableOn_fwd, fun z hz => hc.fwd_mem hz, fun z₁ hz₁ z₂ hz₂ h => ?_, fun y hy => ?_⟩
  · rw [← hc.inv_fwd hz₁, ← hc.inv_fwd hz₂, h]
  · exact ⟨c.2.1 y, hc.inv_mem_dom hy, hc.2.2 y hy⟩

/-- `Ψ` maps the pocket image into `ℍ`. -/
theorem mapsTo_H (hF : IsPocketFrame β α C c Ψ a b) {w : ℂ} (hw : w ∈ cayley '' C) : Ψ w ∈ H := by
  obtain ⟨z, hz, rfl⟩ := hw
  rw [← hF.hΨe z hz]
  exact hF.hc.fwd_mem (by rw [← SetLike.mem_coe, hF.hdom]; exact hz)

/-- `Ψ` is real at the frontier points of the pocket image other than the closing point. -/
theorem im_eq_zero (hF : IsPocketFrame β α C c Ψ a b) {w : ℂ} (hwK : w ∈ closure (cayley '' C) \ {wallPt α b})
    (hwC : w ∉ cayley '' C) : (Ψ w).im = 0 := by
  refine le_antisymm (not_lt.1 fun hpos => hwC ?_) (hF.hΨH hwK)
  have hmem : c.2.1 (Ψ w) ∈ C := by rw [← hF.hdom]; exact hF.hc.inv_mem_dom hpos
  have hK' : cayley (c.2.1 (Ψ w)) ∈ closure (cayley '' C) \ {wallPt α b} :=
    ⟨subset_closure (mem_image_of_mem _ hmem), fun h => hF.closePt_notMem ⟨_, hmem, h⟩⟩
  have he : Ψ (cayley (c.2.1 (Ψ w))) = Ψ w := by rw [← hF.hΨe _ hmem, hF.hc.2.2 _ hpos]
  rw [← hF.hΨi hK' hwK he]
  exact mem_image_of_mem _ hmem

/-- **Orientation**: `Ψ` sends the open right-wall arc to the positive half-line
(`Prop74B.pocketChartOrientationStatement`). -/
theorem re_pos (hF : IsPocketFrame β α C c Ψ a b) {s : ℝ} (hs : s ∈ Ioo a b) : 0 < (Ψ (wallPt α s)).re :=
  Prop74B.pocketChartOrientationStatement α β hF.hα hF.hβ hF.hord C hF.hC a b hF.hM c.1 Ψ hF.isConformalBijection
    hF.hΨc hF.hΨi hF.hΨH hF.hΨ0 hF.hΨtop hF.hΨe s hs

/-- The pocket lies on the left of the right wall and on the right of the left wall. -/
theorem subset_sides (hF : IsPocketFrame β α C c Ψ a b) : C ⊆ leftSideOf (range α) ∩ rightSideOf (range β) := by
  have h := WangWu.subset_between_of_mem_betweenComponents hF.hα.isProperArc hF.hβ.isProperArc
    (by rw [Lemma71I.arcRange_realPath, Lemma71I.arcRange_realPath]; exact hF.hC)
  rwa [Lemma71I.arcRange_realPath, Lemma71I.arcRange_realPath] at h

/-- **No real point other than `0` is adherent to the pocket.** -/
theorem eq_zero_of_mem_closure (hF : IsPocketFrame β α C c Ψ a b) {x : ℝ} (hx : (x : ℂ) ∈ closure C) : x = 0 := by
  by_contra hx0
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · obtain ⟨r, hr, hsub⟩ := hF.hβ.isProperArc.exists_ball_inter_H_subset_leftSideOf hneg
    obtain ⟨w, hwC, hwb⟩ := Metric.mem_closure_iff.1 hx r hr
    have hwl : w ∈ leftSideOf (WangWu.arcRange (Lemma71I.realPath β)) :=
      hsub ⟨by rw [mem_ball, dist_comm]; exact hwb, hF.subset_H hwC⟩
    have hwr : w ∈ rightSideOf (WangWu.arcRange (Lemma71I.realPath β)) := by
      rw [Lemma71I.arcRange_realPath]; exact (hF.subset_sides hwC).2
    exact Set.disjoint_left.1 hF.hβ.isProperArc.disjoint_leftSideOf_rightSideOf hwl hwr
  · obtain ⟨r, hr, hsub⟩ := hF.hα.isProperArc.exists_ball_inter_H_subset_rightSideOf hpos
    obtain ⟨w, hwC, hwb⟩ := Metric.mem_closure_iff.1 hx r hr
    have hwr : w ∈ rightSideOf (WangWu.arcRange (Lemma71I.realPath α)) :=
      hsub ⟨by rw [mem_ball, dist_comm]; exact hwb, hF.subset_H hwC⟩
    have hwl : w ∈ leftSideOf (WangWu.arcRange (Lemma71I.realPath α)) := by
      rw [Lemma71I.arcRange_realPath]; exact (hF.subset_sides hwC).1
    exact Set.disjoint_left.1 hF.hα.isProperArc.disjoint_leftSideOf_rightSideOf hwl hwr

/-- The opening point of the pocket image is `cayley 0` if `0` is adherent to the pocket image. -/
theorem wallPt_zero (α : ℝ≥0 → ℂ) (hα0 : α 0 = 0) : wallPt α 0 = cayley 0 := by
  have h := Prop74B.cayley_eq_wallPt (γ := α) 0
  rw [hα0] at h
  rw [h.1]
  congr 1
  simp [WangWu.discTime]

/-- **The landing point of the chart inverse at a real point `ξ ≠ 0`**: `ψ⁻¹ → cayleyInv z` with `Ψ z = ξ`, and the
landing point is a point of `ℍ` on the frontier of the pocket, not on the wall arc's marked points. -/
theorem exists_land (hF : IsPocketFrame β α C c Ψ a b) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ z ∈ closure (cayley '' C) \ {wallPt α b}, z ∉ cayley '' C ∧ Ψ z = ξ ∧ cayleyInv z ∈ H ∧
      cayleyInv z ∈ range β ∪ range α ∧ cayley (cayleyInv z) = z ∧
      Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (cayleyInv z)) := by
  have hξH : ((ξ : ℝ) : ℂ) ∈ closure H := by rw [closure_H]; show (0 : ℝ) ≤ _; simp
  obtain ⟨z, hzK, hΨz, hcz⟩ := Lemma71M.tendsto_inv_of_ext hF.hc hF.hdom hF.subset_H hF.closePt_notMem hF.hΨc
    hF.hΨi hF.hΨtop hF.hΨe hF.one_notMem hξH
  have hz1 : z ≠ 1 := fun h => hF.one_notMem (h ▸ hzK)
  have hzC : z ∉ cayley '' C := fun h => by
    have h' := hF.mapsTo_H h
    rw [hΨz] at h'
    have : (0 : ℝ) < ((ξ : ℝ) : ℂ).im := h'
    simp at this
  have hcz' : cayley (cayleyInv z) = z := QuantumZipper.CA.cayley_cayleyInv hz1
  have hNe : (𝓝[H] ((ξ : ℝ) : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hξH
  have hpcl : cayleyInv z ∈ closure C :=
    mem_closure_of_tendsto hcz (eventually_nhdsWithin_of_forall fun y hy => by
      rw [← hF.hdom]; exact hF.hc.inv_mem_dom hy)
  have hpC : cayleyInv z ∉ C := fun h => hzC ⟨_, h, hcz'⟩
  have hpH : cayleyInv z ∈ H := by
    by_contra hpH
    have hpHb : cayleyInv z ∈ Hbar := by
      have := closure_mono hF.subset_H hpcl
      rwa [closure_H] at this
    have hpim : (cayleyInv z).im = 0 := le_antisymm (not_lt.1 hpH) hpHb
    have hpx : cayleyInv z = (((cayleyInv z).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hpim])
    have hx0 := hF.eq_zero_of_mem_closure (x := (cayleyInv z).re) (by rw [← hpx]; exact hpcl)
    rw [hx0, Complex.ofReal_zero] at hpx
    have hz0 : z = wallPt α 0 := by rw [wallPt_zero α hF.hα.2.2.1, ← hpx, hcz']
    have h0I : (0 : ℝ) ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt α s ∈ closure (cayley '' C)} :=
      ⟨⟨le_rfl, zero_le_one⟩, hz0 ▸ hzK.1⟩
    rw [hF.hM.2.2.2.1] at h0I
    have ha0 : a = 0 := le_antisymm h0I.1 hF.hM.1
    rw [hz0, ← ha0, hF.hΨ0] at hΨz
    exact hξ (by exact_mod_cast hΨz.symm)
  have hfrC : cayleyInv z ∈ frontier C := by rw [hF.isOpen.frontier_eq]; exact ⟨hpcl, hpC⟩
  exact ⟨z, hzK, hzC, hΨz, hpH, hF.hfr ⟨hfrC, hpH⟩, hcz', hcz⟩

/-- A point of the right wall in the closed pocket image is a wall point of time in `[a, b]`. -/
theorem mem_Icc_of_mem_range (hF : IsPocketFrame β α C c Ψ a b) {u : ℝ≥0}
    (hu : cayley (α u) ∈ closure (cayley '' C)) :
    cayley (α u) = wallPt α (WangWu.discTime u) ∧ WangWu.discTime u ∈ Icc a b := by
  obtain ⟨h1, h2⟩ := Prop74B.cayley_eq_wallPt (γ := α) u
  refine ⟨h1, ?_⟩
  have hI : WangWu.discTime u ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt α s ∈ closure (cayley '' C)} :=
    ⟨⟨h2.1, h2.2.le⟩, h1 ▸ hu⟩
  rwa [hF.hM.2.2.2.1] at hI

/-- **Landing on the left wall**: at a negative real point the chart inverse lands at a point `β s` (`s > 0`) of the
left wall off the right wall. -/
theorem land_neg (hF : IsPocketFrame β α C c Ψ a b) {ξ : ℝ} (hξ : ξ < 0) :
    ∃ s : ℝ≥0, 0 < s ∧ β s ∉ range α ∧ Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (β s)) := by
  obtain ⟨z, hzK, hzC, hΨz, hpH, hpβα, hcz', hcz⟩ := hF.exists_land hξ.ne
  have hpα : cayleyInv z ∉ range α := by
    rintro ⟨u, hu⟩
    have hucl : cayley (α u) ∈ closure (cayley '' C) := by rw [hu, hcz']; exact hzK.1
    obtain ⟨hw, hI⟩ := hF.mem_Icc_of_mem_range hucl
    rw [hu, hcz'] at hw
    rcases eq_or_lt_of_le hI.1 with ha | ha
    · rw [hw, ← ha, hF.hΨ0] at hΨz
      exact hξ.ne (by exact_mod_cast hΨz.symm)
    rcases eq_or_lt_of_le hI.2 with hb | hb
    · exact hzK.2 (by rw [hw, hb]; rfl)
    · have := hF.re_pos ⟨ha, hb⟩
      rw [← hw, hΨz] at this
      simp at this
      linarith
  obtain ⟨s, hs⟩ := hpβα.resolve_right hpα
  have hs0 : 0 < s := by
    rcases eq_zero_or_pos s with h | h
    · rw [h, hF.hβ.2.2.1] at hs
      rw [← hs] at hpH
      exact absurd hpH (by simp [H])
    · exact h
  exact ⟨s, hs0, hs ▸ hpα, hs ▸ hcz⟩

/-- The marked pocket's interval is the contact gap of the two walls (Aux. lemma 33). -/
theorem isContactGap (hF : IsPocketFrame β α C c Ψ a b) :
    WangWu.IsContactGap (WangWu.toDisc (Lemma71I.realPath α)) (WangWu.toDisc (Lemma71I.realPath β)) a b := by
  have hA := hF.hα.isProperArc
  have hB := hF.hβ.isProperArc
  have hord : Disjoint (WangWu.arcRange (Lemma71I.realPath β))
      (rightSideOf (WangWu.arcRange (Lemma71I.realPath α))) := by
    rw [Lemma71I.arcRange_realPath, Lemma71I.arcRange_realPath]
    exact Lemma71I.disjoint_rightSideOf_of_subset_closedLeftSide hF.hα.isProperCurve hF.hα.2.2.1 hF.hord
  have hC' : C ∈ betweenComponents (WangWu.arcRange (Lemma71I.realPath α)) (WangWu.arcRange (Lemma71I.realPath β)) := by
    rw [Lemma71I.arcRange_realPath, Lemma71I.arcRange_realPath]; exact hF.hC
  obtain ⟨a₀, b₀, hg, hCU⟩ := WangWu.exists_contactGap_of_mem_betweenComponents hA hB hord hC'
  have hord' := (WangWu.disjoint_rightSideOf_iff hA hB).1 hord
  have hI := Lemma71K.wallTimes_eq_Icc_of_contactGap hA.isDiscCrosscut_toDisc hB.isDiscCrosscut_toDisc hord' hg
  rw [← hCU] at hI
  have heq : Icc a b = Icc a₀ b₀ := hF.hM.2.2.2.1.symm.trans hI
  obtain ⟨rfl, rfl⟩ := (Set.Icc_eq_Icc_iff hF.hM.2.1.le).1 heq
  exact hg

/-- A wall point of time in `[a, b)` lies in `K = cl(cayley C) ∖ {α̃ b}`. -/
theorem wallPt_mem_K (hF : IsPocketFrame β α C c Ψ a b) {s : ℝ} (hs : s ∈ Ico a b) :
    wallPt α s ∈ closure (cayley '' C) \ {wallPt α b} := by
  have hcr := hF.hα.isProperArc.isDiscCrosscut_toDisc
  have hsI : s ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt α s ∈ closure (cayley '' C)} := by
    rw [hF.hM.2.2.2.1]; exact ⟨hs.1, hs.2.le⟩
  refine ⟨hsI.2, fun h => hs.2.ne (hcr.inj hsI.1 ⟨(hF.hM.1.trans hF.hM.2.1.le), hF.hM.2.2.1⟩ h)⟩

/-- The right wall's points are not in the pocket image. -/
theorem wallPt_notMem (hF : IsPocketFrame β α C c Ψ a b) {s : ℝ} (hs1 : s < 1) : wallPt α s ∉ cayley '' C := by
  rintro ⟨y, hy, hye⟩
  have hw : wallPt α s = cayley (Lemma71I.realPath α (WangWu.arcTime s)) := WangWu.toDisc_of_lt hs1
  have hyH : y ∈ Hbar := le_of_lt (show (0 : ℝ) < y.im from hF.subset_H hy)
  have hαH : Lemma71I.realPath α (WangWu.arcTime s) ∈ Hbar := hF.hα.isProperCurve.2.2.1 _
  have hyα : y = Lemma71I.realPath α (WangWu.arcTime s) := by
    have := congrArg cayleyInv (hye.trans hw)
    rwa [WangWu.cayleyInv_cayley_of_mem_Hbar hyH, WangWu.cayleyInv_cayley_of_mem_Hbar hαH] at this
  exact (Prop74B.subset_of_mem_betweenComponents hF.hC hy).2 (Or.inl ⟨_, hyα.symm⟩)

/-- **Landing on the right wall**: at a positive real point the chart inverse lands at a point `α s` (`s > 0`) of the
right wall off the left wall (the wall arc is mapped onto the positive half-line: intermediate values between the
opening point and the closing point). -/
theorem land_pos (hF : IsPocketFrame β α C c Ψ a b) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ s : ℝ≥0, 0 < s ∧ α s ∉ range β ∧ Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (α s)) := by
  obtain ⟨z, hzK, -, hΨz, -, -, -, hcz⟩ := hF.exists_land hξ.ne'
  have hcr := hF.hα.isProperArc.isDiscCrosscut_toDisc
  have hab := hF.hM.2.1
  have ha0 := hF.hM.1
  have hb1 := hF.hM.2.2.1
  have hreal : ∀ s ∈ Ico a b, (Ψ (wallPt α s)).im = 0 := fun s hs =>
    hF.im_eq_zero (hF.wallPt_mem_K hs) (hF.wallPt_notMem (hs.2.trans_le hb1))
  have hwt : Tendsto (wallPt α) (𝓝[<] b) (𝓝[closure (cayley '' C) \ {wallPt α b}] (wallPt α b)) := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hab]
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs => hF.wallPt_mem_K hs⟩
    exact ((hcr.cont b ⟨ha0.trans hab.le, hb1⟩).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc ha0 hb1))).tendsto
  obtain ⟨s₁, hs₁ξ, hs₁I⟩ := ((hF.hΨtop.comp hwt).eventually (eventually_gt_atTop ξ)).and
    (Ico_mem_nhdsLT hab) |>.exists
  have hs₁a : a < s₁ := by
    rcases eq_or_lt_of_le hs₁I.1 with h | h
    · rw [← h, Function.comp_apply, hF.hΨ0, norm_zero] at hs₁ξ; linarith
    · exact h
  set f : ℝ → ℝ := fun s => (Ψ (wallPt α s)).re with hfdef
  have hfs₁ : ξ < f s₁ := by
    have hre := hF.re_pos ⟨hs₁a, hs₁I.2⟩
    have hn : ‖Ψ (wallPt α s₁)‖ = (Ψ (wallPt α s₁)).re := by
      have he : Ψ (wallPt α s₁) = ((Ψ (wallPt α s₁)).re : ℂ) :=
        Complex.ext (by simp) (by simp [hreal s₁ hs₁I])
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using hre)]
      simp
    simp only [Function.comp_apply] at hs₁ξ
    rw [hfdef]; linarith
  have hfc : ContinuousOn f (Icc a s₁) := by
    refine Complex.continuous_re.comp_continuousOn (hF.hΨc.comp (hcr.cont.mono ?_) fun s hs =>
      hF.wallPt_mem_K ⟨hs.1, hs.2.trans_lt hs₁I.2⟩)
    exact Icc_subset_Icc ha0 (hs₁I.2.le.trans hb1)
  have hfa : f a = 0 := by simp [hfdef, hF.hΨ0]
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hs₁a.le hfc ⟨by rw [hfa]; exact hξ.le, hfs₁.le⟩
  have hsa : a < s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hfa] at hfs; linarith
    · exact h
  have hsb : s < b := hs.2.trans_lt hs₁I.2
  have hΨs : Ψ (wallPt α s) = ξ := Complex.ext (by simpa [hfdef] using hfs) (by simpa using hreal s ⟨hs.1, hsb⟩)
  have hzw : z = wallPt α s := hF.hΨi hzK (hF.wallPt_mem_K ⟨hs.1, hsb⟩) (hΨz.trans hΨs.symm)
  set u : ℝ≥0 := (WangWu.arcTime s).toNNReal with hu
  have hwu : wallPt α s = cayley (α u) := WangWu.toDisc_of_lt (hsb.trans_le hb1)
  have hp : cayleyInv z = α u := by
    rw [hzw, hwu, WangWu.cayleyInv_cayley_of_mem_Hbar (hF.hα.isProperCurve.2.2.1 u)]
  have hs0 : 0 < s := ha0.trans_lt hsa
  have hu0 : 0 < u := by
    rw [hu, Real.toNNReal_pos, WangWu.arcTime]
    exact div_pos hs0 (by linarith [hsb.trans_le hb1])
  have hnot : α u ∉ range β := by
    rintro ⟨v, hv⟩
    obtain ⟨hv1, hv2⟩ := Prop74B.cayley_eq_wallPt (γ := β) v
    refine hF.isContactGap.2.2.2 s ⟨hsa, hsb⟩
      ⟨⟨hs0.le, (hsb.trans_le hb1).le⟩, WangWu.discTime v, ⟨hv2.1, hv2.2.le⟩, ?_⟩
    show WangWu.toDisc (Lemma71I.realPath β) (WangWu.discTime v) = WangWu.toDisc (Lemma71I.realPath α) s
    rw [← Lemma71K.wallPt, ← hv1, hv, ← hwu]
    rfl
  exact ⟨u, hu0, hnot, hp ▸ hcz⟩

end IsPocketFrame

/-! ### Sides of approach and distances -/

section Sides

variable {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}

/-- The two sides of a simple proper trace avoid its hulls. -/
theorem sides_subset_H_diff_fwdHull (hη : Lemma71I.IsSimpleProper η) (htr : IsGeneratingTrace W ⊤ η) (q : ℝ≥0) :
    leftSideOf (range η) ∪ rightSideOf (range η) ⊆ H \ QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal) q := by
  have hL : IsLoewnerTrace (fun r : ℝ => W r.toNNReal) (Lemma71I.realPath η) := isLoewnerTrace_of_isGeneratingTrace htr
  have hA := hη.isProperArc
  rintro w (hw | hw) <;> refine ⟨hw.1.1, fun hK => hw.1.2 ?_⟩ <;>
  · have := WangWu.fwdHull_subset_arcRange hL hA q.2 hK
    rwa [Lemma71I.arcRange_realPath] at this

/-- **Along an approach from the left side of the complete curve, the centred Loewner map of a stopped prefix tends
to a negative real** (the mirror image of `Lemma613.exists_pos_tendsto_of_rightSideOf`). -/
theorem exists_neg_tendsto_of_leftSideOf (hη : Lemma71I.IsSimpleProper η) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : IsGeneratingTrace W ⊤ η) {s q : ℝ≥0} (hs : 0 < s) (hsq : s < q) (U : Ultrafilter ℂ)
    (hU : (U : Filter ℂ) ≤ 𝓝[leftSideOf (range η)] (η s)) :
    ∃ y : ℝ, y < 0 ∧ Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q z) U (𝓝 (y : ℂ)) := by
  set W' : ℝ → ℝ := fun r => W r.toNNReal with hW'
  have hW'c : Continuous W' := hW.comp continuous_real_toNNReal
  have hW'0 : W' 0 = 0 := by simp [hW', hW0]
  have hL : IsLoewnerTrace W' (Lemma71I.realPath η) := isLoewnerTrace_of_isGeneratingTrace htr
  have hA := hη.isProperArc
  have hq0 : (0 : ℝ) ≤ q := q.2
  have hS : leftSideOf (range η) = leftSideOf (WangWu.arcRange (Lemma71I.realPath η)) := by
    rw [Lemma71I.arcRange_realPath]
  have hSK : leftSideOf (range η) ⊆ H \ QuantumZipper.fwdHull W' q := fun w hw =>
    sides_subset_H_diff_fwdHull hη htr q (Or.inl hw)
  have hU' : (U : Filter ℂ) ≤ 𝓝[leftSideOf (range η)] (Lemma71I.realPath η s) := by
    rw [Lemma71I.realPath_coe]; exact hU
  obtain ⟨x, hx0, -, hlim, hcl⟩ := WangWu.exists_real_tendsto_fwdMap hL hA hW'c hW'0 (s := (s : ℝ)) (t := (q : ℝ))
    (by exact_mod_cast hs) (by exact_mod_cast hsq) hSK U hU'
  refine ⟨x, lt_of_le_of_ne (not_lt.1 fun hpos => ?_) hx0, hlim.mono_right nhdsWithin_le_nhds⟩
  refine (WangWu.isProperArc_futureArc hL hA hW'c hW'0 hq0).notMem_closure_leftSideOf_of_pos hpos ?_
  have hsub : QuantumZipper.fwdMap W' q '' leftSideOf (range η) ⊆
      leftSideOf (WangWu.arcRange (WangWu.futureArc W' q)) := by
    rw [hS]
    exact image_subset_iff.2 fun w hw => WangWu.fwdMap_mem_leftSideOf_futureArc hL hA hW'c hW'0 hq0 hw
  exact closure_mono hsub hcl

/-- A point off a simple proper curve has a ball around it missing the curve. -/
theorem exists_ball_notMem_range (hη : Lemma71I.IsSimpleProper η) {p : ℂ} (hp : p ∉ range η) :
    ∃ ρ > 0, ∀ t, η t ∉ ball p ρ := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 ((tendsto_atTop.1 hη.2.2.2.2) (‖p‖ + 1))
  obtain ⟨d, hd, hdK⟩ := Lemma613.exists_ball_notMem (isCompact_Icc.image hη.1 : IsCompact (η '' Icc 0 T))
    (fun h => hp (by obtain ⟨t, -, ht⟩ := h; exact ⟨t, ht⟩))
  refine ⟨min d 1, lt_min hd one_pos, fun t ht => ?_⟩
  rcases le_or_gt t T with htT | htT
  · exact hdK _ ⟨t, ⟨zero_le, htT⟩, rfl⟩ (ball_subset_ball (min_le_left _ _) ht)
  · have h1 := hT t htT.le
    have h2 : dist (η t) p < 1 := (mem_ball.1 ht).trans_le (min_le_right _ _)
    rw [dist_eq_norm] at h2
    have := norm_sub_norm_le (η t) p
    linarith

/-- The tail of a simple proper curve after `q` stays away from an earlier point. -/
theorem exists_ball_tail (hη : Lemma71I.IsSimpleProper η) {s q : ℝ≥0} (hsq : s < q) :
    ∃ ρ > 0, ∀ t, q ≤ t → η t ∉ ball (η s) ρ := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 ((tendsto_atTop.1 hη.2.2.2.2) (‖η s‖ + 1))
  have hnot : η s ∉ η '' Icc q (max q T) := by
    rintro ⟨t, ht, he⟩
    exact absurd (hη.2.1 he) (ne_of_gt (hsq.trans_le ht.1))
  obtain ⟨d, hd, hdK⟩ := Lemma613.exists_ball_notMem (isCompact_Icc.image hη.1) hnot
  refine ⟨min d 1, lt_min hd one_pos, fun t hqt ht => ?_⟩
  rcases le_or_gt t (max q T) with htT | htT
  · exact hdK _ ⟨t, ⟨hqt, htT⟩, rfl⟩ (ball_subset_ball (min_le_left _ _) ht)
  · have h1 := hT t ((le_max_right q T).trans htT.le)
    have h2 : dist (η t) (η s) < 1 := (mem_ball.1 ht).trans_le (min_le_right _ _)
    rw [dist_eq_norm] at h2
    have := norm_sub_norm_le (η t) (η s)
    linarith

end Sides

/-! ### The outer side limits from the single-curve heights -/

section Outer

open scoped Real

/-- The stopped prefix `η([0, q]) ∩ ℍ` of a wall at a rational stop. -/
def wallPrefix (η : ℝ≥0 → ℂ) (q : ℚ≥0) : Set ℂ := η '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ((q : ℝ≥0) : ℝ≥0∞)} ∩ H

/-- **One wall of the pocket**: the side limit of `vT + u₀ + k ℓ` at a chart point `ξ` whose landing point `η s` is a
point of the wall `η` off the other wall `η'`, from Proposition 3.8 (`hcmp`: the outer union against the wall's
stopped prefix), the single-curve side height (`hsh`) on the side `P` of the approach (`hsign`), and the branch
(`hN`). -/
theorem wall_sideLimit {C : Set ℂ} {c : Chart} (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C)
    {η η' : ℝ≥0 → ℂ} (hη : Lemma71I.IsSimpleProper η) (hη' : Lemma71I.IsSimpleProper η')
    (hCη : C ⊆ H \ (range η ∪ range η')) {W : ℝ≥0 → ℝ} {AT : Set ℂ} (hAT : AT = (range η ∪ range η') ∩ H)
    {vT u₀ : ℂ → ℝ} {k h : ℝ} {n : ℤ} (vη : ℚ≥0 → ℂ → ℝ) (P : ℝ → Prop)
    (hcmp : ∀ (q : ℚ≥0) (p : ℂ), p ∈ AT ∪ {z : ℂ | z.im = 0} → p ∈ wallPrefix η q ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, wallPrefix η q ∩ ball p r ⊆ AT) → (∃ r > 0, AT ∩ ball p r ⊆ wallPrefix η q) →
      Tendsto (fun z => vT z - vη q z) (𝓝[H \ (AT ∪ wallPrefix η q)] p) (𝓝 0))
    (hsh : ∀ (q : ℚ≥0) (t₀ : ℝ≥0), t₀ < q → η t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
      F ≤ 𝓝[H \ fillH (η '' Icc 0 (q : ℝ≥0))] (η t₀) → ∀ y : ℝ,
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z) F (𝓝 (y : ℂ)) → P y →
      Tendsto (fun z => vη q z + u₀ z + k * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z).im)
        F (𝓝 h))
    (hCfill : ∀ q : ℝ≥0, C ⊆ H \ fillH (η '' Icc 0 q))
    {ξ : ℝ} {s : ℝ≥0} (hs0 : 0 < s) (hsη' : η s ∉ range η') (hland : Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (η s)))
    (hsign : ∀ q : ℝ≥0, s < q → ∀ U : Ultrafilter ℂ, (U : Filter ℂ) ≤ 𝓝[C] (η s) → ∃ y : ℝ, P y ∧
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q z) U (𝓝 (y : ℂ)))
    (hN : ∀ q : ℝ≥0, s < q → Tendsto (fun y => c.2.2 (c.2.1 y) + 2 * π * n -
      (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (c.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 0)) :
    Tendsto (fun y => vT (c.2.1 y) + u₀ (c.2.1 y) + k * (c.2.2 (c.2.1 y) + 2 * π * n)) (𝓝[H] (ξ : ℂ))
      (𝓝 h) := by
  obtain ⟨r, hsr, -⟩ := Lemma71L.exists_nnrat_btwn s.2 (show (s : ℝ) < s + 1 by linarith)
  set q : ℝ≥0 := (r : ℝ≥0) with hq
  have hsq : s < q := by exact_mod_cast hsr
  have hpH : η s ∈ H := hη.2.2.2.1 s hs0
  have hpAT : η s ∈ AT := hAT ▸ ⟨Or.inl ⟨s, rfl⟩, hpH⟩
  have hpB : η s ∈ wallPrefix η r := ⟨⟨s, by exact_mod_cast hsq.le, rfl⟩, hpH⟩
  have hBAT : wallPrefix η r ⊆ AT := by
    rw [hAT]
    rintro z ⟨⟨t, -, rfl⟩, hzH⟩
    exact ⟨Or.inl ⟨t, rfl⟩, hzH⟩
  have hATB : ∃ ρ > 0, AT ∩ ball (η s) ρ ⊆ wallPrefix η r := by
    obtain ⟨ρ₁, hρ₁, h1⟩ := exists_ball_tail hη hsq
    obtain ⟨ρ₂, hρ₂, h2⟩ := exists_ball_notMem_range hη' hsη'
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
    rintro z ⟨hzAT, hzb⟩
    rw [hAT] at hzAT
    obtain ⟨⟨t, rfl⟩ | ⟨t, rfl⟩, hzH⟩ := hzAT
    · refine ⟨⟨t, ?_, rfl⟩, hzH⟩
      by_contra hlt
      have hlt' : ¬ (t : ℝ≥0∞) ≤ (q : ℝ≥0∞) := hlt
      have hqt : q ≤ t := le_of_lt (by exact_mod_cast not_le.1 hlt')
      exact h1 t hqt (ball_subset_ball (min_le_left _ _) hzb)
    · exact absurd (ball_subset_ball (min_le_right _ _) hzb) (h2 t)
  have hcmp' := hcmp r (η s) (Or.inl hpAT) (Or.inl hpB) ⟨1, one_pos, fun z hz => hBAT hz.1⟩ hATB
  have hCAB : C ⊆ H \ (AT ∪ wallPrefix η r) := fun z hz => by
    refine ⟨(hCη hz).1, fun hzA => (hCη hz).2 ?_⟩
    rcases hzA with hzA | hzA
    · rw [hAT] at hzA; exact hzA.1
    · obtain ⟨⟨t, -, rfl⟩, -⟩ := hzA; exact Or.inl ⟨t, rfl⟩
  rw [tendsto_iff_ultrafilter]
  intro U hU
  set V : Ultrafilter ℂ := U.map c.2.1 with hVdef
  have hVC : (V : Filter ℂ) ≤ 𝓝[C] (η s) := by
    rw [hVdef, Ultrafilter.coe_map]
    refine tendsto_nhdsWithin_iff.2 ⟨hland.mono_left hU, ?_⟩
    have hH : ∀ᶠ y in (U : Filter ℂ), y ∈ H := hU self_mem_nhdsWithin
    exact hH.mono fun y hy => by rw [← hdom]; exact hc.inv_mem_dom hy
  obtain ⟨y, hPy, hy⟩ := hsign q hsq V hVC
  have h1 := hsh r s hsq hpH V inferInstance (hVC.trans (nhdsWithin_mono _ (hCfill q))) y hy hPy
  have h2 := hcmp'.mono_left (hVC.trans (nhdsWithin_mono _ hCAB))
  have h3 : Tendsto (fun z => c.2.2 z + 2 * π * n -
      (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q z).im) (V : Filter ℂ) (𝓝 0) := by
    rw [hVdef, Ultrafilter.coe_map]
    exact tendsto_map'_iff.2 ((hN q hsq).mono_left hU)
  have hsum := (h2.add h1).add (h3.const_mul k)
  rw [zero_add, mul_zero, add_zero] at hsum
  have hfin : Tendsto (fun z => vT z + u₀ z + k * (c.2.2 z + 2 * π * n)) (V : Filter ℂ) (𝓝 h) :=
    hsum.congr fun z => by ring
  rw [hVdef, Ultrafilter.coe_map] at hfin
  exact tendsto_map'_iff.1 hfin

/-- **The inherited branch of a pocket chart** (supplement §2.3, "Deterministic normalization lemma", (2), in the
chart coordinate; Lemma 7.1's proof, p. 225: "with the inherited logarithmic-derivative branch"): with the integer
shift `n`, at every negative (positive) chart point whose landing point is `β s` (`α s`) the lift of the chart plus
`2πn` minus the canonical derivative argument of every own prefix `[0, q]`, `q > s`, of that wall tends to `0`. -/
def IsPocketBranch (β α : ℝ≥0 → ℂ) (c : Chart) (n : ℤ) : Prop :=
  ∀ (Wβ Wα : ℝ≥0 → ℝ), IsGeneratingTrace Wβ ⊤ β → IsGeneratingTrace Wα ⊤ α → ∀ (ξ : ℝ) (s q : ℝ≥0), s < q →
    (ξ < 0 → Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (β s)) →
      Tendsto (fun y => c.2.2 (c.2.1 y) + 2 * π * n -
        (QuantumZipper.logDerivFwd (fun r : ℝ => Wβ r.toNNReal) q (c.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 0)) ∧
    (0 < ξ → Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (α s)) →
      Tendsto (fun y => c.2.2 (c.2.1 y) + 2 * π * n -
        (QuantumZipper.logDerivFwd (fun r : ℝ => Wα r.toNNReal) q (c.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 0))

variable {β α : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ}

/-- **Proposition 6.1 for the two outer curves, in the pocket chart** (Remark 6.7: "In a component to the right of
`γ` … the full-curve conditional means follow exactly from the two-curve result"; the two-curve result itself from
Proposition 3.8 and the single-curve heights): pathwise, from the inherited branch, Proposition 3.8 for the outer
union against each wall's stopped prefixes, and the single-curve side heights (right side of `β`: height `hL`; left
side of `α`: height `hR`), the shifted pocket chart has the outer side limits. -/
theorem outerSideLimit_of_heights (hF : IsPocketFrame β α C c Ψ a b) {n : ℤ} (hN : IsPocketBranch β α c n)
    {Wβ Wα : ℝ≥0 → ℝ} (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (htrβ : IsGeneratingTrace Wβ ⊤ β)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (htrα : IsGeneratingTrace Wα ⊤ α)
    {AT : Set ℂ} (hAT : AT = (range β ∪ range α) ∩ H) {vT u₀ : ℂ → ℝ} {k hL hR : ℝ}
    (vβ vα : ℚ≥0 → ℂ → ℝ)
    (hcmpβ : ∀ (q : ℚ≥0) (p : ℂ), p ∈ AT ∪ {z : ℂ | z.im = 0} → p ∈ wallPrefix β q ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, wallPrefix β q ∩ ball p r ⊆ AT) → (∃ r > 0, AT ∩ ball p r ⊆ wallPrefix β q) →
      Tendsto (fun z => vT z - vβ q z) (𝓝[H \ (AT ∪ wallPrefix β q)] p) (𝓝 0))
    (hcmpα : ∀ (q : ℚ≥0) (p : ℂ), p ∈ AT ∪ {z : ℂ | z.im = 0} → p ∈ wallPrefix α q ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, wallPrefix α q ∩ ball p r ⊆ AT) → (∃ r > 0, AT ∩ ball p r ⊆ wallPrefix α q) →
      Tendsto (fun z => vT z - vα q z) (𝓝[H \ (AT ∪ wallPrefix α q)] p) (𝓝 0))
    (hshβ : ∀ (q : ℚ≥0) (t₀ : ℝ≥0), t₀ < q → β t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
      F ≤ 𝓝[H \ fillH (β '' Icc 0 (q : ℝ≥0))] (β t₀) → ∀ y : ℝ,
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => Wβ r.toNNReal) (q : ℝ≥0) z) F (𝓝 (y : ℂ)) → 0 < y →
      Tendsto (fun z => vβ q z + u₀ z + k * (QuantumZipper.logDerivFwd (fun r : ℝ => Wβ r.toNNReal) (q : ℝ≥0) z).im)
        F (𝓝 hL))
    (hshα : ∀ (q : ℚ≥0) (t₀ : ℝ≥0), t₀ < q → α t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
      F ≤ 𝓝[H \ fillH (α '' Icc 0 (q : ℝ≥0))] (α t₀) → ∀ y : ℝ,
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => Wα r.toNNReal) (q : ℝ≥0) z) F (𝓝 (y : ℂ)) → y < 0 →
      Tendsto (fun z => vα q z + u₀ z + k * (QuantumZipper.logDerivFwd (fun r : ℝ => Wα r.toNNReal) (q : ℝ≥0) z).im)
        F (𝓝 hR)) :
    OuterSideLimit (Lemma71E.shiftLift c n) vT u₀ k hL hR := by
  intro ξ hξ
  have hCH : C ⊆ H \ (range α ∪ range β) := Prop74B.subset_of_mem_betweenComponents hF.hC
  have hCH' : C ⊆ H \ (range β ∪ range α) := fun z hz => by
    rw [union_comm]; exact hCH hz
  have hsides := hF.subset_sides
  show Tendsto (fun y => vT (c.2.1 y) + u₀ (c.2.1 y) + k * (c.2.2 (c.2.1 y) + 2 * π * n)) (𝓝[H] (ξ : ℂ)) _
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · simp only [hneg, ↓reduceIte]
    obtain ⟨s, hs0, hsα, hland⟩ := hF.land_neg hneg
    refine wall_sideLimit hF.hc hF.hdom hF.hβ hF.hα hCH' hAT vβ (fun y => 0 < y) hcmpβ hshβ (fun q z hz => ?_)
      hs0 hsα hland (fun q hsq U hU => Lemma613.exists_pos_tendsto_of_rightSideOf hF.hβ hWβ hWβ0 htrβ hs0 hsq U
        (hU.trans (nhdsWithin_mono _ fun z hz => (hsides hz).2)))
      fun q hsq => (hN Wβ Wα htrβ htrα ξ s q hsq).1 hneg hland
    have h := sides_subset_H_diff_fwdHull hF.hβ htrβ q (Or.inr (hsides hz).2)
    rwa [SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htrβ (ENNReal.coe_lt_top)] at h
  · simp only [not_lt.2 hpos.le, ↓reduceIte]
    obtain ⟨s, hs0, hsβ, hland⟩ := hF.land_pos hpos
    have hAT' : AT = (range α ∪ range β) ∩ H := by rw [hAT, union_comm]
    refine wall_sideLimit hF.hc hF.hdom hF.hα hF.hβ hCH hAT' vα (fun y => y < 0) hcmpα hshα (fun q z hz => ?_)
      hs0 hsβ hland (fun q hsq U hU => exists_neg_tendsto_of_leftSideOf hF.hα hWα hWα0 htrα hs0 hsq U
        (hU.trans (nhdsWithin_mono _ fun z hz => (hsides hz).1)))
      fun q hsq => (hN Wβ Wα htrβ htrα ξ s q hsq).2 hpos hland
    have h := sides_subset_H_diff_fwdHull hF.hα htrα q (Or.inl (hsides hz).1)
    rwa [SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htrα (ENNReal.coe_lt_top)] at h

end Outer

end InteractingSLE.Sec7.Lemma71N
