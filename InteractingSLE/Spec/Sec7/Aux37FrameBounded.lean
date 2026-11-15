/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FrameWitness

/-!
# Aux. lemma 37's witness frame in the bounded change pocket, from the side germ

Packet PROVE-STRIPSYS40. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200). For a change configuration with `0 < rightLo` (the pocket is bounded away from the flow seed), the
counterflow trace and the reverse visits of the walls, a flow chart, and a rational witness on the right arc
(`cfArcR`) or the left arc (`cfArcL`):

* `rightPar`, `leftPar`: the disc parameter of an arc parameter;
* `IsRightSideGerm`, `IsLeftSideGerm`: the two analytic fields of a witness frame along one approach `F` — the
  counterflow chart's real limit on the traversal side (PFI3) and the branch relation (BR);
* **`isRightWitnessFrame_of_germ`**, **`isLeftWitnessFrame_of_germ`**: the whole witness frame of
  `Aux37Assembly.IsRightWitnessFrame` / `IsLeftWitnessFrame`, with the hulls `m(K_t)` of the trace, from a side germ
  along some approach below the chart approach `map c⁻¹ (𝓝[ℍ] (chart value))` at the witness point. All the other
  fields — the point off the other wall and off the angle change, the hull at `r₀` absent near it, the point and the
  walls near it in the hull at `s₀`, the approach from the pocket and from off the exploration, inside one unchanged
  component — are proved here (`Aux37Frame.witness_fields`).

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap logDerivFwd)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Frame

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry StripPocketPath

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ}

/-- The disc parameter of the right arc at the arc parameter `x`. -/
def rightPar (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (x : ℝ) : ℝ := rightLo R L r + x * (rightHi R L r - rightLo R L r)

/-- The disc parameter of the left arc at the arc parameter `x`. -/
def leftPar (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (x : ℝ) : ℝ := leftLo R L r + x * (leftHi R L r - leftLo R L r)

/-- **The right side germ along `F`** (fields (F5)–(F6) of `Aux37Assembly.IsRightWitnessFrame`): the counterflow chart
`f_{s₀} ∘ m` has a real limit `y` along `F`, off the word's jumps, positive and left of every right force position (the
traversal side (PFI3)), and for every own time `q′ > t₀` the branch relation `Im(L_Ψ − L_f) → 2πk` holds along `F`. -/
def IsRightSideGerm {nL nR : ℕ} (w d : ℝ → ℝ) (s₀ : ℝ≥0) (posL : Fin nL → ℝ) (posR : Fin nR → ℝ) (t₀ : ℝ≥0)
    (F : Filter ℂ) : Prop :=
  (∃ y : ℝ, Tendsto (fun z => fwdMap w s₀ (negInv z)) F (𝓝 (y : ℂ)) ∧ y ∉ forceJumpSet posL posR ∧
      0 < y ∧ ∀ i, y ≤ posR i) ∧
    ∀ q' : ℝ≥0, t₀ < q' → ∃ k : ℤ,
      Tendsto (fun z => (Sec5.GlueImg.logDerivPsi w s₀ z - logDerivFwd d q' z).im) F (𝓝 (2 * π * k))

/-- **The left side germ along `F`** (as `IsRightSideGerm`, with the limit `y < 0` right of every left force
position). -/
def IsLeftSideGerm {nL nR : ℕ} (w d : ℝ → ℝ) (s₀ : ℝ≥0) (posL : Fin nL → ℝ) (posR : Fin nR → ℝ) (t₀ : ℝ≥0)
    (F : Filter ℂ) : Prop :=
  (∃ y : ℝ, Tendsto (fun z => fwdMap w s₀ (negInv z)) F (𝓝 (y : ℂ)) ∧ y ∉ forceJumpSet posL posR ∧
      y < 0 ∧ ∀ i, posL i ≤ y) ∧
    ∀ q' : ℝ≥0, t₀ < q' → ∃ k : ℤ,
      Tendsto (fun z => (Sec5.GlueImg.logDerivPsi w s₀ z - logDerivFwd d q' z).im) F (𝓝 (2 * π * k))

/-! ### The open arcs in the disc and in the counterflow chart -/

section ArcFacts

variable {Ψ : ℂ → ℂ} {c : Chart}

theorem IsFlowChart.mem_right (hF : IsFlowChart R L r Ψ c) {σ : ℝ} (hσ : σ ∈ Ioo (rightLo R L r) (rightHi R L r)) :
    toDisc (realPath R) σ ∈ closure (cayley '' changePocket R L r) \ {closePt R L r} := by
  have h := hF.config
  obtain ⟨hu, hv, -, -, -, -, -, -⟩ := h.changeCorner_props
  refine ⟨frontier_subset_closure ?_, fun he => hσ.2.ne
    (h.isDiscCrosscut_right.inj ⟨hu.1.trans hσ.1.le, hσ.2.le.trans hv.2⟩ hv he)⟩
  rw [frontier_eq h]; exact Or.inl ⟨σ, ⟨hσ.1.le, hσ.2.le⟩, rfl⟩

theorem IsFlowChart.mem_left (hF : IsFlowChart R L r Ψ c) {σ : ℝ} (hσ : σ ∈ Ioo (leftLo R L r) (leftHi R L r)) :
    toDisc (realPath L) σ ∈ closure (cayley '' changePocket R L r) \ {closePt R L r} := by
  have h := hF.config
  obtain ⟨-, -, -, ha, hb, -, -, hLb⟩ := h.changeCorner_props
  refine ⟨frontier_subset_closure ?_, fun he => hσ.2.ne
    (h.isDiscCrosscut_left.inj ⟨ha.1.trans hσ.1.le, hσ.2.le.trans hb.2⟩ hb (he.trans hLb.symm))⟩
  rw [frontier_eq h]; exact Or.inr ⟨σ, ⟨hσ.1.le, hσ.2.le⟩, rfl⟩

/-- The real chart values along an open arc form a continuous injective function of the arc parameter. -/
theorem chart_arc_contInj (hF : IsFlowChart R L r Ψ c) {X : ℝ≥0 → ℂ} {lo hi : ℝ} (hlo : 0 ≤ lo) (hlh : lo < hi)
    (hhi : hi ≤ 1) (hXc : ContinuousOn (toDisc (realPath X)) (Icc 0 1)) (hXi : InjOn (toDisc (realPath X)) (Icc 0 1))
    (hmem : ∀ σ ∈ Ioo lo hi, toDisc (realPath X) σ ∈ closure (cayley '' changePocket R L r) \ {closePt R L r})
    (him : ∀ σ ∈ Ioo lo hi, (Ψ (toDisc (realPath X) σ)).im = 0) :
    ContinuousOn (fun u : ℝ => (Ψ (toDisc (realPath X) (lo + u * (hi - lo)))).re) (Ioo 0 1) ∧
      InjOn (fun u : ℝ => (Ψ (toDisc (realPath X) (lo + u * (hi - lo)))).re) (Ioo 0 1) := by
  have hmap : ∀ u ∈ Ioo (0 : ℝ) 1, lo + u * (hi - lo) ∈ Ioo lo hi := fun u hu => affine_mem_Ioo hlh hu
  have hIcc : ∀ u ∈ Ioo (0 : ℝ) 1, lo + u * (hi - lo) ∈ Icc (0 : ℝ) 1 := fun u hu =>
    ⟨hlo.trans (hmap u hu).1.le, (hmap u hu).2.le.trans hhi⟩
  have haff : Continuous fun u : ℝ => lo + u * (hi - lo) := by fun_prop
  refine ⟨?_, fun u hu u' hu' he => ?_⟩
  · have h1 : ContinuousOn (fun u : ℝ => toDisc (realPath X) (lo + u * (hi - lo))) (Ioo 0 1) :=
      hXc.comp haff.continuousOn hIcc
    exact Complex.continuous_re.comp_continuousOn (hF.unif.cont.comp h1 fun u hu => hmem _ (hmap u hu))
  · have hΨ : Ψ (toDisc (realPath X) (lo + u * (hi - lo))) = Ψ (toDisc (realPath X) (lo + u' * (hi - lo))) :=
      Complex.ext he (by rw [him _ (hmap u hu), him _ (hmap u' hu')])
    have h2 := hXi (hIcc u hu) (hIcc u' hu') (hF.unif.inj (hmem _ (hmap u hu)) (hmem _ (hmap u' hu')) hΨ)
    have h3 : u * (hi - lo) = u' * (hi - lo) := by linarith
    exact mul_right_cancel₀ (sub_pos.2 hlh).ne' h3

/-- Every frontier point in `ℍ` of the counterflow-chart pocket is `m` of a wall point. -/
theorem frontier_cfPocket_mem (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) {W : ℝ → ℝ}
    (hP : Sec6.IsReversePocket W η (cfPocket R L r) (cfArcR R L r) (cfArcL R L r) (cfBeta R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    ∀ y ∈ frontier (cfPocket R L r), y ∈ H → negInv y ∈ (range L ∪ range R) ∩ H := by
  obtain ⟨hu, hv, huv, ha, hb, hab, -, -⟩ := h.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have ha0 := h.leftLo_pos h0
  have key : ∀ (X : ℝ≥0 → ℂ), IsSimpleProper X → ∀ {lo hi : ℝ}, 0 < lo → lo ≤ hi → hi ≤ 1 →
      IsDiscCrosscut (toDisc (realPath X)) → ∀ u ∈ Icc (0 : ℝ) 1,
        cfPt (toDisc (realPath X) (lo + u * (hi - lo))) ∈ H →
          negInv (cfPt (toDisc (realPath X) (lo + u * (hi - lo)))) ∈ range X ∩ H := by
    intro X hX lo hi hlo hlh hhi hcc u hu hy
    have hσ0 : 0 < lo + u * (hi - lo) := by
      have := mul_nonneg hu.1 (sub_nonneg.2 hlh); linarith
    have hσ1 : lo + u * (hi - lo) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hu.2 (sub_nonneg.2 hlh); linarith
    rcases eq_or_lt_of_le hσ1 with he | hlt
    · rw [he, hcc.one, cfPt_one] at hy
      exact absurd (Aux37Assembly.ne_zero_of_mem_H hy) (fun h => h rfl)
    · obtain ⟨e, hpos⟩ := cfPt_toDisc_of_mem hX ⟨hσ0, hlt⟩
      rw [e, negInv_negInv]
      exact ⟨⟨_, rfl⟩, hX.2.2.2.1 _ hpos⟩
  intro y hy hyH
  rw [hP.frontier_eq] at hy
  rcases hy with ⟨u, hu', rfl⟩ | ⟨u, hu', rfl⟩
  · obtain ⟨h1, h2⟩ := key R h.right hu0 huv.le hv.2 h.isDiscCrosscut_right u hu' hyH
    exact ⟨Or.inr h1, h2⟩
  · obtain ⟨h1, h2⟩ := key L h.left ha0 hab.le hb.2 h.isDiscCrosscut_left u hu' hyH
    exact ⟨Or.inl h1, h2⟩

end ArcFacts

/-! ### The witness frames from the side germs -/

section Frames

variable {Ψ : ℂ → ℂ} {c : Chart}

theorem IsFlowChart.mapsTo_inv (hF : IsFlowChart R L r Ψ c) : MapsTo c.2.1 H (changePocket R L r) := fun w hw => by
  have := hF.conf.inv_mem_dom hw
  rw [← SetLike.mem_coe, hF.dom] at this
  exact this

/-- An open-arc wall point is off the other wall (the arc lies in a contact gap). -/
theorem notMem_range_of_gap {X Y : ℝ≥0 → ℂ} (hY : IsSimpleProper Y) {σ : ℝ} (hσ1 : σ < 1) (hσ0 : 0 ≤ σ)
    (hgap : σ ∉ Sec7.pocketContactSet (toDisc (realPath X)) (toDisc (realPath Y))) :
    X (arcTime σ).toNNReal ∉ range Y := by
  rintro ⟨t, ht⟩
  refine hgap ⟨⟨hσ0, hσ1.le⟩, ?_⟩
  have hYH : Y t ∈ Hbar := hY.isProperCurve.2.2.1 t
  have hmem := (hY.isProperArc.cayley_mem_crossRange_iff hYH).2 (by rw [arcRange_realPath]; exact ⟨t, rfl⟩)
  rw [toDisc_eq_cayley hσ1, ← ht]
  exact hmem

/-- **The right witness frame from a right side germ** (bounded pocket; see the module docstring). -/
theorem isRightWitnessFrame_of_germ (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hF : IsFlowChart R L r Ψ c) {r₀ s₀ : ℝ≥0} {v v₁ v₂ : ℝ}
    (hw : Aux37Attach.IsAttachWitness η (cfPocket R L r) (cfArcR R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) r₀ s₀ v v₁ v₂)
    (hB : ∀ b ∈ chgPts R L r, b ∉ Icc v v₂) {x : ℝ} (hx : x ∈ Ico v v₂)
    {nL nR : ℕ} {d : ℝ → ℝ} {posL : Fin nL → ℝ} {posR : Fin nR → ℝ} {F : Filter ℂ} [hFne : F.NeBot]
    (hFG : F ≤ map c.2.1 (𝓝[H] ((Ψ (toDisc (realPath R) (rightPar R L r x))).re : ℂ)))
    (hgerm : IsRightSideGerm W d s₀ posL posR (arcTime (rightPar R L r x)).toNNReal F) :
    Aux37Assembly.IsRightWitnessFrame R L r (negInv '' fwdHull W r₀) (negInv '' fwdHull W s₀)
      ((range L ∪ range R) ∩ H) (negInv '' fwdHull W r₀ ∪ (range L ∪ range R) ∩ H)
      (negInv '' fwdHull W s₀ ∪ (range L ∪ range R) ∩ H) W d s₀ posL posR := by
  have hP := h.isReversePocket_of_counterflow h0 trace hW hW0 hrevR hrevL hvisR
  obtain ⟨-, hv, huv, -, -, -, -, -⟩ := h.changeCorner_props
  have hlo := h.rightLo_pos h0
  have hAX : ∀ u ∈ Ioo (0 : ℝ) 1, negInv (cfArcR R L r u) =
      R (arcTime (rightLo R L r + u * (rightHi R L r - rightLo R L r))).toNNReal := fun u hu => by
    obtain ⟨e, -⟩ := cfPt_toDisc_of_mem h.right
      ⟨hlo.trans (affine_mem_Ioo huv hu).1, (affine_mem_Ioo huv hu).2.trans_le hv.2⟩
    show negInv (cfPt _) = _
    rw [e, negInv_negInv]
  obtain ⟨hfc, hfi⟩ := chart_arc_contInj hF hlo.le huv hv.2 h.isDiscCrosscut_right.cont
    h.isDiscCrosscut_right.inj (fun σ hσ => IsFlowChart.mem_right hF hσ)
    (fun σ hσ => (IsFlowChart.tendsto_right hF hσ).1)
  -- the witness point
  obtain ⟨hτr, hrs, hsσ, havoid, hus, hvv₁, hv₁v₂, hv₂r⟩ := hw
  obtain ⟨hus0, -, -, -, -⟩ := hP.chart (hτr.trans hrs.le) hsσ (Or.inl rfl)
  obtain ⟨-, hur1, -, -, -⟩ := hP.chart hτr (hrs.trans hsσ) (Or.inl rfl)
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hus0.trans (hus.trans_le hx.1), hx.2.trans (hv₂r.trans_le hur1)⟩
  have hσ := affine_mem_Ioo huv hxI
  have hσ1 : rightPar R L r x < 1 := hσ.2.trans_le hv.2
  have hY₀ : negInv (cfArcR R L r x) ∉ range L := by
    rw [hAX x hxI]
    exact notMem_range_of_gap h.left hσ1 (hlo.trans hσ.1).le ((h.changeCorners).1.2.2.2 _ hσ)
  obtain ⟨hF2, hF3a, hF3b, -, hGP, hGE, z, hzE, hcomp, hevc⟩ :=
    witness_fields hP (Or.inl rfl) rfl h.changePocket_subset_H h.right h.left
      (fun z hz => hz.1.symm) (Set.disjoint_left.2 fun z hz hzW => (h.changePocket_subset hz).2 hzW.1.symm)
      (frontier_cfPocket_mem h h0 hP) hlo huv hv.2 hAX hF.conf (IsFlowChart.mapsTo_inv hF) hfc hfi
      (fun u hu => (IsFlowChart.tendsto_right hF (affine_mem_Ioo huv hu)).2.2)
      ⟨hτr, hrs, hsσ, havoid, hus, hvv₁, hv₁v₂, hv₂r⟩ hx hY₀
  rw [hAX x hxI] at hF2 hF3a hF3b hGP hGE hY₀
  refine ⟨(arcTime (rightPar R L r x)).toNNReal, hY₀, fun h1 => ?_, hF2, hF3a, hF3b, F, hFne, hFG.trans hGP,
    hFG.trans hGE, ⟨z, hzE, hcomp, hFG hevc⟩, hgerm.1, hgerm.2⟩
  have ha : arcTime (rightPar R L r x) = 1 := by
    rw [← Real.coe_toNNReal (arcTime (rightPar R L r x)) (arcTime_nonneg ⟨(hlo.trans hσ.1).le, hσ1⟩), h1,
      NNReal.coe_one]
  have hd : discTime 1 = rightPar R L r x := by rw [← ha, discTime_arcTime hσ1]
  refine hB _ (Finset.mem_insert_self _ _) ⟨?_, ?_⟩ <;>
    rw [hd, rightPar, add_sub_cancel_left, mul_div_assoc, div_self (sub_pos.2 huv).ne', mul_one]
  · exact hx.1
  · exact hx.2.le

/-- **The left witness frame from a left side germ** (bounded pocket). -/
theorem isLeftWitnessFrame_of_germ (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hF : IsFlowChart R L r Ψ c) {r₀ s₀ : ℝ≥0} {v v₁ v₂ : ℝ}
    (hw : Aux37Attach.IsAttachWitness η (cfPocket R L r) (cfArcL R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) r₀ s₀ v v₁ v₂)
    (hB : ∀ b ∈ chgPts R L r, b ∉ Icc v v₂) {x : ℝ} (hx : x ∈ Ico v v₂)
    {nL nR : ℕ} {d : ℝ → ℝ} {posL : Fin nL → ℝ} {posR : Fin nR → ℝ} {F : Filter ℂ} [hFne : F.NeBot]
    (hFG : F ≤ map c.2.1 (𝓝[H] ((Ψ (toDisc (realPath L) (leftPar R L r x))).re : ℂ)))
    (hgerm : IsLeftSideGerm W d s₀ posL posR (arcTime (leftPar R L r x)).toNNReal F) :
    Aux37Assembly.IsLeftWitnessFrame R L r (negInv '' fwdHull W r₀) (negInv '' fwdHull W s₀)
      ((range L ∪ range R) ∩ H) (negInv '' fwdHull W r₀ ∪ (range L ∪ range R) ∩ H)
      (negInv '' fwdHull W s₀ ∪ (range L ∪ range R) ∩ H) W d s₀ posL posR := by
  have hP := h.isReversePocket_of_counterflow h0 trace hW hW0 hrevR hrevL hvisR
  obtain ⟨-, -, -, -, hb, hab, -, -⟩ := h.changeCorner_props
  have hlo := h.leftLo_pos h0
  have hAX : ∀ u ∈ Ioo (0 : ℝ) 1, negInv (cfArcL R L r u) =
      L (arcTime (leftLo R L r + u * (leftHi R L r - leftLo R L r))).toNNReal := fun u hu => by
    obtain ⟨e, -⟩ := cfPt_toDisc_of_mem h.left
      ⟨hlo.trans (affine_mem_Ioo hab hu).1, (affine_mem_Ioo hab hu).2.trans_le hb.2⟩
    show negInv (cfPt _) = _
    rw [e, negInv_negInv]
  obtain ⟨hfc, hfi⟩ := chart_arc_contInj hF hlo.le hab hb.2 h.isDiscCrosscut_left.cont
    h.isDiscCrosscut_left.inj (fun σ hσ => IsFlowChart.mem_left hF hσ) (fun σ hσ => (IsFlowChart.tendsto_left hF hσ).1)
  obtain ⟨hτr, hrs, hsσ, havoid, hus, hvv₁, hv₁v₂, hv₂r⟩ := hw
  obtain ⟨hus0, -, -, -, -⟩ := hP.chart (hτr.trans hrs.le) hsσ (Or.inr rfl)
  obtain ⟨-, hur1, -, -, -⟩ := hP.chart hτr (hrs.trans hsσ) (Or.inr rfl)
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hus0.trans (hus.trans_le hx.1), hx.2.trans (hv₂r.trans_le hur1)⟩
  have hσ := affine_mem_Ioo hab hxI
  have hσ1 : leftPar R L r x < 1 := hσ.2.trans_le hb.2
  have hY₀ : negInv (cfArcL R L r x) ∉ range R := by
    rw [hAX x hxI]
    exact notMem_range_of_gap h.right hσ1 (hlo.trans hσ.1).le ((h.changeCorners).2.2.2.1.2.2.2 _ hσ)
  obtain ⟨hF2, hF3a, hF3b, -, hGP, hGE, z, hzE, hcomp, hevc⟩ :=
    witness_fields hP (Or.inr rfl) rfl h.changePocket_subset_H h.left h.right
      (fun z hz => hz.1) (Set.disjoint_left.2 fun z hz hzW => (h.changePocket_subset hz).2 hzW.1.symm)
      (frontier_cfPocket_mem h h0 hP) hlo hab hb.2 hAX hF.conf (IsFlowChart.mapsTo_inv hF) hfc hfi
      (fun u hu => (IsFlowChart.tendsto_left hF (affine_mem_Ioo hab hu)).2.2)
      ⟨hτr, hrs, hsσ, havoid, hus, hvv₁, hv₁v₂, hv₂r⟩ hx hY₀
  rw [hAX x hxI] at hF2 hF3a hF3b hGP hGE hY₀
  refine ⟨(arcTime (leftPar R L r x)).toNNReal, hY₀, fun h1 => ?_, hF2, hF3a, hF3b, F, hFne, hFG.trans hGP,
    hFG.trans hGE, ⟨z, hzE, hcomp, hFG hevc⟩, hgerm.1, hgerm.2⟩
  have ha : arcTime (leftPar R L r x) = r := by
    rw [← Real.coe_toNNReal (arcTime (leftPar R L r x)) (arcTime_nonneg ⟨(hlo.trans hσ.1).le, hσ1⟩), h1]
  have hd : discTime r = leftPar R L r x := by rw [← ha, discTime_arcTime hσ1]
  refine hB _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) ⟨?_, ?_⟩ <;>
    rw [hd, leftPar, add_sub_cancel_left, mul_div_assoc, div_self (sub_pos.2 hab).ne', mul_one]
  · exact hx.1
  · exact hx.2.le

end Frames

end InteractingSLE.Sec7.Aux37Frame
