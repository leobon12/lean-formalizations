/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37SideInf

/-!
# Aux. lemma 37 in the pocket at the flow seed: the witness frames and `hwitI`

Packet PROVE-STRIPSYS42. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200), the case `rightLo = 0` (the change pocket's closure contains the flow seed; in the counterflow chart its
junction is the counterflow's target `∞`, `σ = ∞`).

* **`isRightWitnessFrame_of_inf`**, **`isLeftWitnessFrame_of_inf`**: a rational witness at infinity
  (`IsAttachWitnessInf` on the arm `cfArcRInf` / `cfArcLInf`, off the angle changes `chgPtsInf`) gives a whole witness
  frame `Aux37Assembly.IsRightWitnessFrame` / `IsLeftWitnessFrame` at the arm point `v₁`: the arm is the arc
  reparametrized by `s = 1/(1 + v)` (`cfArcRInf_eq`), its visit data are `isArcVisit_of_witnessInf`, the frame fields
  come from `witness_fields_visit` and the side germ from `side_germ`.
* **`hwitI_of_flatClock`**: `hwitI` of `StripPocketPath.pocketWordEvolution_of_stripSystem`, exactly in its type, from
  the flat clock (FC) and the consumer's realization data (`hwallsL` with both walls' visits).

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48); `h44` is the walls'
determination input, as in G1.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)
open InteractingSLE.WangWu (negInv)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Side

open WangWu Lemma71I PocketCoord PocketJordan Aux119Bdry Lemma71O Aux37Frame StripPocketPath

section Frames

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart} {η : ℝ → ℂ}

theorem one_div_one_add_mem {v₁ : ℝ} (hv₁ : 0 < v₁) : 1 / (1 + v₁) ∈ Ioo (0 : ℝ) 1 :=
  ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩

/-- **The right witness frame from a witness at infinity** (pocket at the flow seed; see the module docstring). -/
theorem isRightWitnessFrame_of_inf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    {W : ℝ → ℝ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hvisL : IsWallVisited L η) (hF : IsFlowChart R L r Ψ c) {s₁ s₂ v v₁ v₂ : ℝ}
    (hw : Aux37Attach.IsAttachWitnessInf η (cfPocket R L r) (cfArcRInf R L r) (firstHit η (cfArcRInf R L r 0))
      s₁ s₂ v v₁ v₂)
    (hB : ∀ b ∈ chgPtsInf R L r, b ∉ Icc v v₂)
    {d : ℝ → ℝ} (hRtr : IsLoewnerTrace d (realPath R)) (hd : Continuous d) (hd0 : d 0 = 0)
    {nL nR : ℕ} {posL : Fin nL → ℝ} {posR : Fin nR → ℝ}
    (hposR : ∀ i, MartChar.RealFlow.rightImg W 0 s₂ - W s₂ ≤ posR i)
    (hposL : ∀ i, posL i ≤ -MartChar.RealFlow.rightImg (fun s => -W s) 0 s₂ - W s₂) {r₀ s₀ : ℝ≥0}
    (hr₀ : (r₀ : ℝ) = s₁) (hs₀ : (s₀ : ℝ) = s₂) :
    Aux37Assembly.IsRightWitnessFrame R L r (negInv '' fwdHull W r₀) (negInv '' fwdHull W s₀)
      ((range L ∪ range R) ∩ H) (negInv '' fwdHull W r₀ ∪ (range L ∪ range R) ∩ H)
      (negInv '' fwdHull W s₀ ∪ (range L ∪ range R) ∩ H) W d s₀ posL posR := by
  have hP := h.isReversePocketInf_of_counterflow h0 trace hW hW0 hrevR hrevL hvisR hvisL
  obtain ⟨hu, hv, huv, -, -, -, -, -⟩ := h.changeCorner_props
  obtain ⟨hV, h12, h23⟩ := isArcVisit_of_witnessInf hP (Or.inl rfl) (fun v _ => cfArcRInf_eq h0 v) hw
  have hA := isArcChart_right h hF fun q hq hq0 => land_ne_zero_of_rightLo_eq_zero h h0 hF hq hq0
  have hw' := hw
  obtain ⟨-, -, -, hur, hvv₁, hv₁v₂, -⟩ := hw'
  have hv0 : 0 < v := (hP.chart hw.1 (Or.inl rfl)).1.trans_lt hur
  set x := 1 / (1 + v₁) with hxdef
  have hxI : x ∈ Ioo (0 : ℝ) 1 := one_div_one_add_mem (by linarith)
  have hσ := affine_mem_Ioo huv hxI
  have hσ1 : rightPar R L r x < 1 := hσ.2.trans_le hv.2
  have hσ0 : 0 ≤ rightPar R L r x := (hu.1.trans hσ.1.le)
  have hY₀ : negInv (cfArcR R L r x) ∉ range L := by
    rw [hA.hAX x hxI]
    exact notMem_range_of_gap h.left hσ1 hσ0 ((h.changeCorners).1.2.2.2 _ hσ)
  obtain ⟨y, hy, hyJ, hεy, -, hRp, hBR⟩ := side_germ hA hV h12 h23 hRtr hd hd0 h.right.isProperArc
    (Set.disjoint_left.2 fun z hz hzR => (h.changePocket_subset hz).2 (Or.inl hzR)) hposR hposL
    fun q' hq' => eventually_arcTime_lt hσ1 hq'
  obtain ⟨hF2, hF3a, hF3b, -, hGP, hGE, z, hzE, hcomp, hevc⟩ :=
    witness_fields_visit hV hP.isOpen rfl h.changePocket_subset_H h.right h.left (fun z hz => hz.1.symm)
      (Set.disjoint_left.2 fun z hz hzW => (h.changePocket_subset hz).2 hzW.1.symm)
      (frontier_cfPocketInf_mem h h0 hP) hu.1 huv hv.2 hA.hAX hF.conf (IsFlowChart.mapsTo_inv hF) hA.fc hA.injOn_f
      hA.lim ⟨h12, h23⟩ hY₀
  rw [hA.hAX x hxI] at hF2 hF3a hF3b hGP hGE hY₀
  rw [← hr₀] at hF2 hcomp
  rw [← hs₀] at hF3a hF3b hGE hzE hcomp hevc
  have harc0 : 0 ≤ arcTime (rightPar R L r x) := arcTime_nonneg ⟨hσ0, hσ1⟩
  have hne : (𝓝[H] (((Ψ (toDisc (realPath R) (rightPar R L r x))).re : ℝ) : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact IsArcChart.ofReal_mem_Hbar _)
  refine ⟨(arcTime (rightPar R L r x)).toNNReal, hY₀, fun h1 => ?_, hF2, hF3a, hF3b, _, Filter.map_neBot, hGP, hGE,
    ⟨z, hzE, hcomp, hevc⟩, ⟨y, by rw [hs₀]; exact hy, hyJ, by linarith, fun i => (hRp i).le⟩, fun q' hq' => ?_⟩
  · -- the angle change of `α` is off the witness interval
    have ha : arcTime (rightPar R L r x) = 1 := by
      rw [← Real.coe_toNNReal _ harc0, h1, NNReal.coe_one]
    have hd1 : discTime 1 = rightPar R L r x := by rw [← ha, discTime_arcTime hσ1]
    have hrH : 0 < rightHi R L r := by linarith
    have hpar : rightPar R L r x = rightHi R L r / (1 + v₁) := by
      simp only [rightPar, h0, sub_zero, zero_add, hxdef]; ring
    have hmem : rightHi R L r / discTime 1 - 1 = v₁ := by
      rw [hd1, hpar]; field_simp; ring
    exact hB _ (Finset.mem_insert_self _ _) (by rw [hmem]; exact ⟨hvv₁.le, hv₁v₂.le⟩)
  · have hq'r : arcTime (rightLo R L r + x * (rightHi R L r - rightLo R L r)) < (q' : ℝ) := by
      have := NNReal.coe_lt_coe.2 hq'
      rwa [Real.coe_toNNReal _ harc0] at this
    rw [hs₀]
    exact hBR q' q'.2 hq'r

/-- **The left witness frame from a witness at infinity** (as `isRightWitnessFrame_of_inf`, on the arm
`cfArcLInf`, with the angle change of `β^{(q)}` at `L(r)`). -/
theorem isLeftWitnessFrame_of_inf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    {W : ℝ → ℝ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hvisL : IsWallVisited L η) (hF : IsFlowChart R L r Ψ c) {s₁ s₂ v v₁ v₂ : ℝ}
    (hw : Aux37Attach.IsAttachWitnessInf η (cfPocket R L r) (cfArcLInf R L r) (firstHit η (cfArcRInf R L r 0))
      s₁ s₂ v v₁ v₂)
    (hB : ∀ b ∈ chgPtsInf R L r, b ∉ Icc v v₂)
    {d : ℝ → ℝ} (hLtr : IsLoewnerTrace d (realPath L)) (hd : Continuous d) (hd0 : d 0 = 0)
    {nL nR : ℕ} {posL : Fin nL → ℝ} {posR : Fin nR → ℝ}
    (hposR : ∀ i, MartChar.RealFlow.rightImg W 0 s₂ - W s₂ ≤ posR i)
    (hposL : ∀ i, posL i ≤ -MartChar.RealFlow.rightImg (fun s => -W s) 0 s₂ - W s₂) {r₀ s₀ : ℝ≥0}
    (hr₀ : (r₀ : ℝ) = s₁) (hs₀ : (s₀ : ℝ) = s₂) :
    Aux37Assembly.IsLeftWitnessFrame R L r (negInv '' fwdHull W r₀) (negInv '' fwdHull W s₀)
      ((range L ∪ range R) ∩ H) (negInv '' fwdHull W r₀ ∪ (range L ∪ range R) ∩ H)
      (negInv '' fwdHull W s₀ ∪ (range L ∪ range R) ∩ H) W d s₀ posL posR := by
  have hP := h.isReversePocketInf_of_counterflow h0 trace hW hW0 hrevR hrevL hvisR hvisL
  obtain ⟨-, -, -, ha, hb, hab, -, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  obtain ⟨hV, h12, h23⟩ := isArcVisit_of_witnessInf hP (Or.inr rfl) (fun v _ => cfArcLInf_eq h h0 v) hw
  have hA := isArcChart_left h hF fun q hq hq0 => land_ne_zero_of_rightLo_eq_zero h h0 hF hq hq0
  have hw' := hw
  obtain ⟨-, -, -, hur, hvv₁, hv₁v₂, -⟩ := hw'
  have hv0 : 0 < v := (hP.chart hw.1 (Or.inr rfl)).1.trans_lt hur
  set x := 1 / (1 + v₁) with hxdef
  have hxI : x ∈ Ioo (0 : ℝ) 1 := one_div_one_add_mem (by linarith)
  have hσ := affine_mem_Ioo hab hxI
  have hσ1 : leftPar R L r x < 1 := hσ.2.trans_le hb.2
  have hσ0 : 0 ≤ leftPar R L r x := (ha.1.trans hσ.1.le)
  have hY₀ : negInv (cfArcL R L r x) ∉ range R := by
    rw [hA.hAX x hxI]
    exact notMem_range_of_gap h.right hσ1 hσ0 ((h.changeCorners).2.2.2.1.2.2.2 _ hσ)
  obtain ⟨y, hy, hyJ, hεy, hLp, -, hBR⟩ := side_germ hA hV h12 h23 hLtr hd hd0 h.left.isProperArc
    (Set.disjoint_left.2 fun z hz hzL => (h.changePocket_subset hz).2 (Or.inr hzL)) hposR hposL
    fun q' hq' => eventually_arcTime_lt hσ1 hq'
  obtain ⟨hF2, hF3a, hF3b, -, hGP, hGE, z, hzE, hcomp, hevc⟩ :=
    witness_fields_visit hV hP.isOpen rfl h.changePocket_subset_H h.left h.right (fun z hz => hz.1)
      (Set.disjoint_left.2 fun z hz hzW => (h.changePocket_subset hz).2 hzW.1.symm)
      (frontier_cfPocketInf_mem h h0 hP) ha.1 hab hb.2 hA.hAX hF.conf (IsFlowChart.mapsTo_inv hF) hA.fc hA.injOn_f
      hA.lim ⟨h12, h23⟩ hY₀
  rw [hA.hAX x hxI] at hF2 hF3a hF3b hGP hGE hY₀
  rw [← hr₀] at hF2 hcomp
  rw [← hs₀] at hF3a hF3b hGE hzE hcomp hevc
  have harc0 : 0 ≤ arcTime (leftPar R L r x) := arcTime_nonneg ⟨hσ0, hσ1⟩
  have hne : (𝓝[H] (((Ψ (toDisc (realPath L) (leftPar R L r x))).re : ℝ) : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact IsArcChart.ofReal_mem_Hbar _)
  refine ⟨(arcTime (leftPar R L r x)).toNNReal, hY₀, fun h1 => ?_, hF2, hF3a, hF3b, _, Filter.map_neBot, hGP, hGE,
    ⟨z, hzE, hcomp, hevc⟩, ⟨y, by rw [hs₀]; exact hy, hyJ, by linarith, fun i => (hLp i).le⟩, fun q' hq' => ?_⟩
  · -- the angle change of `β^{(q)}` is off the witness interval
    have hae : arcTime (leftPar R L r x) = r := by
      rw [← Real.coe_toNNReal _ harc0, h1]
    have hdr : discTime r = leftPar R L r x := by rw [← hae, discTime_arcTime hσ1]
    have hlH : 0 < leftHi R L r := by linarith
    have hpar : leftPar R L r x = leftHi R L r / (1 + v₁) := by
      simp only [leftPar, ha0, sub_zero, zero_add, hxdef]; ring
    have hmem : leftHi R L r / discTime r - 1 = v₁ := by
      rw [hdr, hpar]; field_simp; ring
    exact hB _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (by rw [hmem]; exact ⟨hvv₁.le, hv₁v₂.le⟩)
  · have hq'r : arcTime (leftLo R L r + x * (leftHi R L r - leftLo R L r)) < (q' : ℝ) := by
      have := NNReal.coe_lt_coe.2 hq'
      rwa [Real.coe_toNNReal _ harc0] at this
    rw [hs₀]
    exact hBR q' q'.2 hq'r

end Frames

/-! ### `hwitI` from the flat clock -/

section HwitI

open MeasureTheory
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)
open scoped ENNReal
open PocketMarks Aux119Nested Aux37Germ StripWall StripSideHeightProb Aux37Assembly LocalSets
open Exist.Staged (IsRegularDriver)

universe u

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **`hwitI` of `StripPocketPath.pocketWordEvolution_of_stripSystem`** (Aux. lemma 37's exclusion of every rational
witness in the change pocket at the flow seed, `rightLo = 0`), exactly in its type, from the flat clock (FC) and the
consumer's realization data (as `hwit_of_flatClock`, with both visits of the left walls in `hwallsL`). Angles:
`θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]`. -/
theorem hwitI_of_flatClock (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {gU : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hgU : ∀ q : ℚ, 0 < q → IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q))
    {gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t))
    {gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    {g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t))
    (hFC : ∀ q : ℚ, 0 < q → FlatClockStatement P univ (stripExpl W' ζ' (Lr q) α) (g q))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hLβ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  intro q hq s₁ s₂ v v₁ v₂
  by_cases hlt : (s₁ : ℝ) < s₂
  swap
  · refine Eventually.of_forall fun ω _ _ hw => hlt ?_
    rcases hw.1 with h1 | h1
    · exact h1.2.1
    · exact h1.2.1
  have hrs : (s₁ : ℝ).toNNReal ≤ (s₂ : ℝ).toNNReal := Real.toNNReal_le_toNNReal hlt.le
  have htrace := ae_isLoewnerTrace_counterflow hS hcumL hcumR hηtr
  have hreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous fun t => W' t ω := by
    filter_upwards [StripPocketPath.ae_counterflow_trace hS hcumL hcumR] with ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.1⟩
  filter_upwards [ae_noFrame_strip h44 hS hcumL hcumR hθ₁ hθ₂ (StripSys.rt q) hregα (hregβ q hq) hu₀ (hvL q hq)
    (hlocL q hq) hvα hlocα (hgU q hq) (hgL q hq) hgR (hg q hq) (hFC q hq) hrs, htrace, hreg, hwalls, hwallsL q hq,
    hβ, hLβ q hq, hav, ae_ownTrace_alpha h44 hS hcumL hcumR hθ₁ hregα hvα,
    ae_ownTrace_beta h44 hS hcumL hcumR hθ₂ (StripSys.rt q) (hregβ q hq) (hvL q hq)]
    with ω hno htrω hregω hwω hwLω hβω hLβω havω hα hL hconf hpos hwit
  obtain ⟨⟨Ψ, c, hF⟩, hCl⟩ := exists_isFlowChart_of_cfAvoid hconf hβω hLβω hwω.2 (hηc ω) havω
  obtain ⟨hnoR, hnoL⟩ := hno Ψ c hF hCl
  have hW0 : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by simpa using htrω.2.2
  have he : ∀ t : ℝ≥0, cfHull W' ζ' t ω = negInv '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    cfHull_eq hregω.1 hregω.2.1 hregω.2.2
  have hs₁0 : (0 : ℝ) ≤ s₁ := by
    rcases hwit.1 with h1 | h1
    · exact (Real.sInf_nonneg fun _ hx => hx.1).trans h1.1
    · exact (Real.sInf_nonneg fun _ hx => hx.1).trans h1.1
  have hs₁ : (((s₁ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₁ := Real.coe_toNNReal _ hs₁0
  have hs₂ : (((s₂ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₂ := Real.coe_toNNReal _ (hs₁0.trans hlt.le)
  rcases hwit.1 with hwR | hwL
  · have hfr := isRightWitnessFrame_of_inf hconf hpos htrω.1 htrω.2.1 hW0 hwω.1 hwLω.1 hwω.2 hwLω.2 hF hwR hwit.2
      hα.1 hα.2.1 hα.2.2
      (fun i => cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1 (hs₁0.trans hlt.le) i)
      (fun i => cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1 (hs₁0.trans hlt.le) i)
      hs₁ hs₂
    refine hnoR ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr
  · have hfr := isLeftWitnessFrame_of_inf hconf hpos htrω.1 htrω.2.1 hW0 hwω.1 hwLω.1 hwω.2 hwLω.2 hF hwL hwit.2
      hL.1 hL.2.1 hL.2.2
      (fun i => cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1 (hs₁0.trans hlt.le) i)
      (fun i => cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1 (hs₁0.trans hlt.le) i)
      hs₁ hs₂
    refine hnoL ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr

end HwitI

end InteractingSLE.Sec7.Aux37Side
