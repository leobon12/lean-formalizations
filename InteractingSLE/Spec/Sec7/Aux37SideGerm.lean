/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37SideBranch

/-!
# Aux. lemma 37's side germ in the bounded change pocket

Packet PROVE-STRIPSYS42. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200), with ruling R41's fresh-tip replacement (`ig1_ztip_elimination.txt` L185–L196).

* `strictMonoOn_of_pos_tendsto`, `tendsto_arc_zero`: the arc values of the flow chart increase on the right arc and
  decrease on the left arc (they have constant sign and start at `0` at the opening contact);
* `rightImg_mono`: the image of a right force point grows with the point;
* **`side_germ`** (generic): (PFI3) and (BR) together, with the force-position bounds: the counterflow limit `y` along
  the chart approach at `f(v₁)` is off the word's jumps, strictly between the left and right force positions, on the
  traversal side `ε y > 0`, and the branch relation holds for every later own time;
* `isArcChart_right`, `isArcChart_left`: the bounded change pocket's two arcs as `IsArcChart`;
* **`isRightSideGerm_of_witness`**, **`isLeftSideGerm_of_witness`**: the side germs of `Aux37Frame` at a witness
  (point `x = v₁`, approach `F` = the chart approach itself).

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv revChart)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Side

open WangWu Lemma71I PocketCoord PocketJordan Aux119Bdry Lemma71O Aux37Frame StripPocketPath

/-! ### Elementary monotonicity -/

section Mono

/-- A continuous injective positive function on `(0, 1)` tending to `0` at `0⁺` increases strictly. -/
theorem strictMonoOn_of_pos_tendsto {f : ℝ → ℝ} (hfc : ContinuousOn f (Ioo 0 1)) (hfi : InjOn f (Ioo 0 1))
    (hpos : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < f u) (hlim : Tendsto f (𝓝[>] 0) (𝓝 0)) : StrictMonoOn f (Ioo 0 1) := by
  intro u hu u' hu' huu'
  obtain ⟨u'', hu''⟩ := ((hlim.eventually (gt_mem_nhds (hpos u hu))).and
    (Ioo_mem_nhdsGT hu.1)).exists
  have hsub : Icc u'' u' ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨hu''.2.1.trans_le ht.1, ht.2.trans_lt hu'.2⟩
  have h1 : u'' < u := hu''.2.2
  rcases (hfc.mono hsub).strictMonoOn_of_injOn_Icc' (h1.trans huu').le (hfi.mono hsub) with h | h
  · exact h ⟨h1.le, huu'.le⟩ ⟨(h1.trans huu').le, le_rfl⟩ huu'
  · exact absurd (h ⟨le_rfl, (h1.trans huu').le⟩ ⟨h1.le, huu'.le⟩ h1) (not_lt.2 hu''.1.le)

/-- The image of a right force point grows with the point. -/
theorem rightImg_mono {w : ℝ → ℝ} (hw : Continuous w) {x x' t : ℝ} (hxx : x ≤ x') (ht : 0 ≤ t) :
    MartChar.RealFlow.rightImg w x t ≤ MartChar.RealFlow.rightImg w x' t :=
  csInf_le_csInf (MartChar.RealFlow.imgSet_bddBelow hw x ht) (MartChar.RealFlow.imgSet_nonempty hw x' ht)
    fun _ ⟨y, hy, hya, hyg⟩ => ⟨y, hxx.trans_lt hy, hya, hyg⟩

end Mono

/-! ### The generic side germ -/

section Germ

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β A : ℝ → ℂ} {τ σ : ℝ} {P : Set ℂ} {X : ℝ≥0 → ℂ}
  {Wu : Set ℂ} {lo hi : ℝ} {c : Chart} {κ : ℂ → ℂ} {f : ℝ → ℝ} {ε : ℝ}

/-- **(PFI3) and (BR) at a rational witness, with the force-position bounds** (see the module docstring). -/
theorem side_germ (hS : IsArcChart C A P X Wu lo hi c κ f ε) {r₀ s₀ a₀ v v₁ v₂ : ℝ}
    (hV : IsArcVisit W η C A r₀ s₀ a₀ v v₂) (hvv₁ : v < v₁) (hv₁v₂ : v₁ < v₂) {d : ℝ → ℝ}
    (hXtr : IsLoewnerTrace d (realPath X))
    (hd : Continuous d) (hd0 : d 0 = 0) (hXa : IsProperArc (realPath X)) (hPX : Disjoint P (range X))
    {nL nR : ℕ} {posL : Fin nL → ℝ} {posR : Fin nR → ℝ}
    (hposR : ∀ i, MartChar.RealFlow.rightImg W 0 s₀ - W s₀ ≤ posR i)
    (hposL : ∀ i, posL i ≤ -MartChar.RealFlow.rightImg (fun s => -W s) 0 s₀ - W s₀)
    (htq : ∀ q' : ℝ, arcTime (lo + v₁ * (hi - lo)) < q' → ∀ᶠ u in 𝓝 v₁, arcTime (lo + u * (hi - lo)) < q') :
    ∃ y : ℝ, Tendsto (fun z => fwdMap W s₀ (negInv z)) (map c.2.1 (𝓝[H] (f v₁ : ℂ))) (𝓝 (y : ℂ)) ∧
      y ∉ forceJumpSet posL posR ∧ 0 < ε * y ∧ (∀ i, posL i < y) ∧ (∀ i, y < posR i) ∧
      ∀ q' : ℝ, 0 ≤ q' → arcTime (lo + v₁ * (hi - lo)) < q' → ∃ k : ℤ,
        Tendsto (fun z => (Sec5.GlueImg.logDerivPsi W s₀ z - logDerivFwd d q' z).im)
          (map c.2.1 (𝓝[H] (f v₁ : ℂ))) (𝓝 (2 * π * k)) := by
  obtain ⟨y, hy, hεy, hFy⟩ := exists_side_limit hS hV hvv₁ hv₁v₂
  have hy0 : y ≠ 0 := fun h => by rw [h, mul_zero] at hεy; exact lt_irrefl _ hεy
  have hs₀ : 0 ≤ s₀ := hV.nonneg.trans hV.lt.le
  have hAH : A v₁ ∈ H := (hV.unvis_r v₁ ⟨by linarith [hV.a₀_lt], hv₁v₂.le⟩).1
  have hFx : extendFrom H (fwdMapInv W s₀) y ∈ H := by
    rw [← YuanSimpleApprox.trMap_zero_left hV.W_zero, hFy]; exact hAH
  have hlt := WangWu.lt_rightImg_sub_of_extendFrom_mem_H hV.trace hV.continuous_W hV.W_zero hs₀ hFx
  have hgt := WangWu.neg_rightImg_sub_lt_of_extendFrom_mem_H hV.trace hV.continuous_W hV.W_zero hs₀ hFx
  have hR : ∀ i, y < posR i := fun i => hlt.trans_le (hposR i)
  have hL : ∀ i, posL i < y := fun i => (hposL i).trans_lt hgt
  refine ⟨y, by rw [tendsto_map'_iff]; exact hy, ?_, hεy, hL, hR, fun q' hq'0 hq' =>
    exists_branch hS hV hvv₁ hv₁v₂ hXtr hd hd0 hXa hPX hy hy0 hq'0 (htq q' hq')⟩
  rintro (h0 | ⟨i, hi⟩ | ⟨i, hi⟩)
  · exact hy0 h0
  · exact (hL i).ne hi
  · exact (hR i).ne' hi

end Germ

/-! ### The bounded change pocket's arcs -/

section Bounded

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart} {η : ℝ → ℂ}

/-- The flow chart's arc values start at `0` at the opening contact. -/
theorem tendsto_arc_zero (hF : IsFlowChart R L r Ψ c) {X : ℝ≥0 → ℂ}
    (hXc : ContinuousOn (toDisc (realPath X)) (Icc 0 1)) {lo hi : ℝ} (hlo : lo ∈ Icc (0 : ℝ) 1) (hlh : lo < hi)
    (hhi : hi ≤ 1) (h0 : toDisc (realPath X) lo = openPt R L r)
    (hmem : ∀ σ ∈ Ioo lo hi, toDisc (realPath X) σ ∈ closure (cayley '' changePocket R L r) \ {closePt R L r}) :
    Tendsto (fun u => (Ψ (toDisc (realPath X) (lo + u * (hi - lo)))).re) (𝓝[>] 0) (𝓝 0) := by
  have h := hF.config
  set S := closure (cayley '' changePocket R L r) \ {closePt R L r} with hS
  have hopen : openPt R L r ∈ S := ⟨frontier_subset_closure h.openPt_mem_frontier, h.openPt_ne_closePt⟩
  have haff : Tendsto (fun u : ℝ => lo + u * (hi - lo)) (𝓝[>] 0) (𝓝[Icc 0 1] lo) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun u : ℝ => lo + u * (hi - lo)) (𝓝 0) (𝓝 (lo + 0 * (hi - lo))) :=
        (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
      rw [zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with u hu
      have := affine_mem_Ioo hlh hu
      exact ⟨hlo.1.trans this.1.le, this.2.le.trans hhi⟩
  have hg : Tendsto (fun u : ℝ => toDisc (realPath X) (lo + u * (hi - lo))) (𝓝[>] 0) (𝓝[S] (openPt R L r)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← h0]; exact (hXc lo hlo).tendsto.comp haff
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with u hu
      exact hmem _ (affine_mem_Ioo hlh hu)
  have hΨ := ((hF.unif.cont _ hopen).tendsto.comp hg)
  rw [hF.unif.zero] at hΨ
  have := (Complex.continuous_re.tendsto 0).comp hΨ
  simpa only [Function.comp_def, zero_re] using this

/-- The landing points of the flow chart are in the closed pocket, hence off `0` (bounded pocket). -/
theorem land_ne_zero (hF : IsFlowChart R L r Ψ c) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) {q : ℂ}
    (hq : q ∈ Hbar) : land c q ≠ 0 := by
  intro hl
  refine h0 ?_
  rw [← hl]
  have hne : (𝓝[H] q).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hq)
  exact mem_closure_of_tendsto (tendsto_land hF hq)
    (eventually_nhdsWithin_of_forall fun w hw => IsFlowChart.mapsTo_inv hF hw)

/-- **The right arc of the bounded change pocket as an arc chart** (`ε = 1`). -/
theorem isArcChart_right (h : IsChangeConfigInc R L r) (hF : IsFlowChart R L r Ψ c)
    (hland0 : ∀ q ∈ Hbar, q ≠ 0 → land c q ≠ 0) :
    IsArcChart (cfPocket R L r) (cfArcR R L r) (changePocket R L r) R ((range L ∪ range R) ∩ H)
      (rightLo R L r) (rightHi R L r) c (fun z => Ψ (cayley z))
      (fun u => (Ψ (toDisc (realPath R) (rightPar R L r u))).re) 1 := by
  obtain ⟨hu, hv, huv, -, -, -, -, -⟩ := h.changeCorner_props
  have hlo : 0 ≤ rightLo R L r := hu.1
  obtain ⟨hfc, hfi⟩ := chart_arc_contInj hF hlo huv hv.2 h.isDiscCrosscut_right.cont
    h.isDiscCrosscut_right.inj (fun σ hσ => IsFlowChart.mem_right hF hσ)
    (fun σ hσ => (IsFlowChart.tendsto_right hF hσ).1)
  have hmono : StrictMonoOn (fun u => (Ψ (toDisc (realPath R) (rightPar R L r u))).re) (Ioo 0 1) :=
    strictMonoOn_of_pos_tendsto hfc hfi (fun u hu => (IsFlowChart.tendsto_right hF (affine_mem_Ioo huv hu)).2.1)
      (tendsto_arc_zero hF h.isDiscCrosscut_right.cont hu huv hv.2 rfl fun σ hσ => IsFlowChart.mem_right hF hσ)
  refine ⟨rfl, h.changePocket_subset_H,
    Set.disjoint_left.2 fun z hz hzW => (h.changePocket_subset hz).2 hzW.1.symm, fun u hu => ?_, hF.conf,
    IsFlowChart.mapsTo_inv hF, continuousOn_land hF, fun w hw => land_of_mem_H hF hw, fun q hq => read_land hF hq,
    fun q hq => continuousWithinAt_read hF hq, hland0, hfc,
    fun u hu => by rw [one_mul]; exact (IsFlowChart.tendsto_right hF (affine_mem_Ioo huv hu)).2.1, ?_,
    Or.inl rfl, fun u hu => (IsFlowChart.tendsto_right hF (affine_mem_Ioo huv hu)).2.2⟩
  · obtain ⟨e, -⟩ := cfPt_toDisc_of_mem h.right
      ⟨hlo.trans_lt (affine_mem_Ioo huv hu).1, (affine_mem_Ioo huv hu).2.trans_le hv.2⟩
    show negInv (cfPt _) = _
    rw [e, negInv_negInv]
  · simpa only [one_mul] using hmono

/-- **The left arc of the bounded change pocket as an arc chart** (`ε = −1`). -/
theorem isArcChart_left (h : IsChangeConfigInc R L r) (hF : IsFlowChart R L r Ψ c)
    (hland0 : ∀ q ∈ Hbar, q ≠ 0 → land c q ≠ 0) :
    IsArcChart (cfPocket R L r) (cfArcL R L r) (changePocket R L r) L ((range L ∪ range R) ∩ H)
      (leftLo R L r) (leftHi R L r) c (fun z => Ψ (cayley z))
      (fun u => (Ψ (toDisc (realPath L) (leftPar R L r u))).re) (-1) := by
  obtain ⟨-, -, -, ha, hb, hab, hLa, -⟩ := h.changeCorner_props
  have hlo : 0 ≤ leftLo R L r := ha.1
  obtain ⟨hfc, hfi⟩ := chart_arc_contInj hF hlo hab hb.2 h.isDiscCrosscut_left.cont
    h.isDiscCrosscut_left.inj (fun σ hσ => IsFlowChart.mem_left hF hσ)
    (fun σ hσ => (IsFlowChart.tendsto_left hF hσ).1)
  have hmono : StrictMonoOn (fun u => -(Ψ (toDisc (realPath L) (leftPar R L r u))).re) (Ioo 0 1) :=
    strictMonoOn_of_pos_tendsto hfc.neg (fun u hu u' hu' he => hfi hu hu' (neg_injective he))
      (fun u hu => neg_pos.2 (IsFlowChart.tendsto_left hF (affine_mem_Ioo hab hu)).2.1)
      (by
        have := (tendsto_arc_zero (Ψ := Ψ) hF h.isDiscCrosscut_left.cont ha hab hb.2 hLa
          fun σ hσ => IsFlowChart.mem_left hF hσ).neg
        rw [neg_zero] at this
        exact this)
  refine ⟨rfl, h.changePocket_subset_H,
    Set.disjoint_left.2 fun z hz hzW => (h.changePocket_subset hz).2 hzW.1.symm, fun u hu => ?_, hF.conf,
    IsFlowChart.mapsTo_inv hF, continuousOn_land hF, fun w hw => land_of_mem_H hF hw, fun q hq => read_land hF hq,
    fun q hq => continuousWithinAt_read hF hq, hland0, hfc,
    fun u hu => by
      have := (IsFlowChart.tendsto_left hF (affine_mem_Ioo hab hu)).2.1
      simp only [neg_one_mul, neg_pos]
      exact this, ?_,
    Or.inr rfl, fun u hu => (IsFlowChart.tendsto_left hF (affine_mem_Ioo hab hu)).2.2⟩
  · obtain ⟨e, -⟩ := cfPt_toDisc_of_mem h.left
      ⟨hlo.trans_lt (affine_mem_Ioo hab hu).1, (affine_mem_Ioo hab hu).2.trans_le hb.2⟩
    show negInv (cfPt _) = _
    rw [e, negInv_negInv]
  · simpa only [neg_one_mul] using hmono

end Bounded

/-! ### The side germs at a witness of the bounded change pocket -/

section Witness

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart} {η : ℝ → ℂ}

/-- The wall times near an arc parameter stay below every later time. -/
theorem eventually_arcTime_lt {lo hi v₁ q' : ℝ} (hσ : lo + v₁ * (hi - lo) < 1)
    (hq : arcTime (lo + v₁ * (hi - lo)) < q') : ∀ᶠ u in 𝓝 v₁, arcTime (lo + u * (hi - lo)) < q' := by
  have hc : ContinuousAt (fun u : ℝ => arcTime (lo + u * (hi - lo))) v₁ := by
    have h1 : (1 : ℝ) - (lo + v₁ * (hi - lo)) ≠ 0 := by linarith
    have : ContinuousAt (fun u : ℝ => (lo + u * (hi - lo)) / (1 - (lo + u * (hi - lo)))) v₁ :=
      ((continuous_const.add (continuous_id.mul continuous_const)).continuousAt).div
        ((continuous_const.sub (continuous_const.add (continuous_id.mul continuous_const))).continuousAt) h1
    exact this
  exact hc.eventually (gt_mem_nhds hq)

/-- **The right side germ at a witness of the bounded change pocket** (`IsRightSideGerm` along the chart approach at
`x = v₁`). -/
theorem isRightSideGerm_of_witness (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hF : IsFlowChart R L r Ψ c) {s₁ s₂ v v₁ v₂ : ℝ}
    (hw : Aux37Attach.IsAttachWitness η (cfPocket R L r) (cfArcR R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) s₁ s₂ v v₁ v₂)
    {d : ℝ → ℝ} (hRtr : IsLoewnerTrace d (realPath R)) (hd : Continuous d) (hd0 : d 0 = 0)
    {nL nR : ℕ} {posL : Fin nL → ℝ} {posR : Fin nR → ℝ}
    (hposR : ∀ i, MartChar.RealFlow.rightImg W 0 s₂ - W s₂ ≤ posR i)
    (hposL : ∀ i, posL i ≤ -MartChar.RealFlow.rightImg (fun s => -W s) 0 s₂ - W s₂) {s₀ : ℝ≥0}
    (hs₀ : (s₀ : ℝ) = s₂) :
    ∃ x ∈ Ico v v₂, ∃ F : Filter ℂ, F.NeBot ∧
      F ≤ map c.2.1 (𝓝[H] ((Ψ (toDisc (realPath R) (rightPar R L r x))).re : ℂ)) ∧
      IsRightSideGerm W d s₀ posL posR (arcTime (rightPar R L r x)).toNNReal F := by
  have hA := isArcChart_right h hF fun q hq _ => land_ne_zero hF h0 hq
  have hP := h.isReversePocket_of_counterflow h0 trace hW hW0 hrevR hrevL hvisR
  obtain ⟨hV, hvv₁, hv₁v₂⟩ := isArcVisit_of_witness hP (Or.inl rfl) hw
  obtain ⟨-, hv, huv, -, -, -, -, -⟩ := h.changeCorner_props
  have hlo := h.rightLo_pos h0
  have hv₁I : v₁ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hV.pos, hV.a₀_lt], by linarith [hV.lt_one]⟩
  have hσ := affine_mem_Ioo huv hv₁I
  have hσ1 : rightLo R L r + v₁ * (rightHi R L r - rightLo R L r) < 1 := hσ.2.trans_le hv.2
  obtain ⟨y, hy, hyJ, hεy, -, hR, hBR⟩ := side_germ hA hV hvv₁ hv₁v₂ hRtr hd hd0 h.right.isProperArc
    (Set.disjoint_left.2 fun z hz hzR => (h.changePocket_subset hz).2 (Or.inl hzR)) hposR hposL
    fun q' hq' => eventually_arcTime_lt hσ1 hq'
  have hne : (𝓝[H] (((Ψ (toDisc (realPath R) (rightPar R L r v₁))).re : ℝ) : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact IsArcChart.ofReal_mem_Hbar _)
  have harc0 : 0 ≤ arcTime (rightPar R L r v₁) := arcTime_nonneg ⟨(hlo.trans hσ.1).le, hσ1⟩
  refine ⟨v₁, ⟨hvv₁.le, hv₁v₂⟩, _, Filter.map_neBot, le_rfl, ⟨y, ?_, hyJ, by linarith, fun i => (hR i).le⟩,
    fun q' hq' => ?_⟩
  · rw [hs₀]; exact hy
  · have hq'r : arcTime (rightLo R L r + v₁ * (rightHi R L r - rightLo R L r)) < (q' : ℝ) := by
      have := NNReal.coe_lt_coe.2 hq'
      rwa [Real.coe_toNNReal _ harc0] at this
    rw [hs₀]
    exact hBR q' q'.2 hq'r

/-- **The left side germ at a witness of the bounded change pocket** (`IsLeftSideGerm` along the chart approach at
`x = v₁`). -/
theorem isLeftSideGerm_of_witness (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hF : IsFlowChart R L r Ψ c) {s₁ s₂ v v₁ v₂ : ℝ}
    (hw : Aux37Attach.IsAttachWitness η (cfPocket R L r) (cfArcL R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) s₁ s₂ v v₁ v₂)
    {d : ℝ → ℝ} (hLtr : IsLoewnerTrace d (realPath L)) (hd : Continuous d) (hd0 : d 0 = 0)
    {nL nR : ℕ} {posL : Fin nL → ℝ} {posR : Fin nR → ℝ}
    (hposR : ∀ i, MartChar.RealFlow.rightImg W 0 s₂ - W s₂ ≤ posR i)
    (hposL : ∀ i, posL i ≤ -MartChar.RealFlow.rightImg (fun s => -W s) 0 s₂ - W s₂) {s₀ : ℝ≥0}
    (hs₀ : (s₀ : ℝ) = s₂) :
    ∃ x ∈ Ico v v₂, ∃ F : Filter ℂ, F.NeBot ∧
      F ≤ map c.2.1 (𝓝[H] ((Ψ (toDisc (realPath L) (leftPar R L r x))).re : ℂ)) ∧
      IsLeftSideGerm W d s₀ posL posR (arcTime (leftPar R L r x)).toNNReal F := by
  have hA := isArcChart_left h hF fun q hq _ => land_ne_zero hF h0 hq
  have hP := h.isReversePocket_of_counterflow h0 trace hW hW0 hrevR hrevL hvisR
  obtain ⟨hV, hvv₁, hv₁v₂⟩ := isArcVisit_of_witness hP (Or.inr rfl) hw
  obtain ⟨-, -, -, -, hb, hab, -, -⟩ := h.changeCorner_props
  have hlo := h.leftLo_pos h0
  have hv₁I : v₁ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hV.pos, hV.a₀_lt], by linarith [hV.lt_one]⟩
  have hσ := affine_mem_Ioo hab hv₁I
  have hσ1 : leftLo R L r + v₁ * (leftHi R L r - leftLo R L r) < 1 := hσ.2.trans_le hb.2
  obtain ⟨y, hy, hyJ, hεy, hL, -, hBR⟩ := side_germ hA hV hvv₁ hv₁v₂ hLtr hd hd0 h.left.isProperArc
    (Set.disjoint_left.2 fun z hz hzL => (h.changePocket_subset hz).2 (Or.inr hzL)) hposR hposL
    fun q' hq' => eventually_arcTime_lt hσ1 hq'
  have hne : (𝓝[H] (((Ψ (toDisc (realPath L) (leftPar R L r v₁))).re : ℝ) : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact IsArcChart.ofReal_mem_Hbar _)
  have harc0 : 0 ≤ arcTime (leftPar R L r v₁) := arcTime_nonneg ⟨(hlo.trans hσ.1).le, hσ1⟩
  refine ⟨v₁, ⟨hvv₁.le, hv₁v₂⟩, _, Filter.map_neBot, le_rfl, ⟨y, ?_, hyJ, by linarith, fun i => (hL i).le⟩,
    fun q' hq' => ?_⟩
  · rw [hs₀]; exact hy
  · have hq'r : arcTime (leftLo R L r + v₁ * (leftHi R L r - leftLo R L r)) < (q' : ℝ) := by
      have := NNReal.coe_lt_coe.2 hq'
      rwa [Real.coe_toNNReal _ harc0] at this
    rw [hs₀]
    exact hBR q' q'.2 hq'r

end Witness

end InteractingSLE.Sec7.Aux37Side
