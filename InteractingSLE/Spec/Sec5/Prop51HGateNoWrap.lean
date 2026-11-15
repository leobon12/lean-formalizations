/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HGateSign
import InteractingSLE.Spec.Sec5.Aux61LocLanding
import InteractingSLE.WangWu.MeanIdentArc

/-!
# Proposition 5.1's no-wrap step in the chart `Q`, proved (`Prop51G.FwdNoWrapQStatement`)

Packet PROVE-PROP51H-TOPO2 (ruling R71: Astra's follow-up 4, Part (1), §1.7, the deterministic separation). If no
excursion of the proper flow arc `η` in `D = ℍ ∖ R(K_s)` ends in the eastern part of `∂D` (the rational barriers
`FirstContactNotEast`), the counterflow tip `R(β(s))` is not on the left of `η`.

**Proof (by contradiction, in the counterflow chart `Ψ = revChart w s`).** Suppose the tip is on the left of `η`.

1. Every excursion ends at a negative chart point (`Prop51HTopo.hasWesternExcursionEnds_of_rational`), the chart
   flow set `A = Ψ(η ∩ D)` is bounded (`Prop51HTopo.isBounded_revChart_arcRange_of_mem_leftSideOf`), and each
   excursion completes to a chart crosscut `κ` from `κ.start` to `κ.finish < 0` (`nonempty_excursionChartCut`).
2. The physical side index `windRef z = windNum (flowReferenceLoop η) (cayley (Ψ⁻¹ z))` is `0` at a point `w₀` of the
   half-ball at a free positive gate `x₀ > 0` (`Prop51HTopo.exists_positiveBoundaryGate`; the gate's physical boundary
   point is on `ℝ₊`, on the right of `η`) and `1` at a far point `w₁` (`Ψ⁻¹` tends to the tip at `∞`, which is on the
   left).
3. Along the segment `σ` from `w₀` to `w₁` (compact in `ℍ`, so it meets only finitely many excursions `F`), the
   function `g = windRef − Σ_{κ ∈ F} windNum κ.loop` is locally constant off `A` near every point of `σ`: off `A`
   trivially, and at a crosscut point by the local orientation `ExcursionChartCut.exists_local_const`. Hence
   `g w₀ = g w₁` (`eq_of_locally_const_along`).
4. But `g w₁ = 1` (every loop winds `0` far away) and `g w₀ = 0 − Σ (≥ 0) ≤ 0`
   (`ExcursionChartCut.windNum_loop_nonneg_of_gate`: a loop with a western finishing gate winds `0` or `+1` about the
   free positive gate). Contradiction.

This is §1.7's outermost-excursion separation, with the outermost separator replaced by a count of winding numbers
of the finitely many excursions met by one compact path (no density of exterior times, no separation lemma); the
orientation step is §1.7's "the orientation forces an eastern endpoint": a crosscut separating the gate from the tip
with the gate on its right must end east of the gate.

* **`fwdNoWrapQStatement`**: `Prop51G.FwdNoWrapQStatement`, unconditionally;
* **`prop51QStatement_of_partA_of_noCrosscut'`**: `Cond44Ref.Prop51QStatement` from Zhan's Part A inputs and (E1) in
  crosscut form only (`Aux61Loc.prop51QStatement_of_partA_of_noCrosscut` with the no-wrap topology discharged).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement` or `Theorem13Statement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Prop51HGate

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G Prop51HTopo
open _root_.InteractingSLE.Orientation

/-- A winding number is locally constant off its loop. -/
theorem eventually_windNum_eq {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1) {q : ℂ}
    (hq : q ∉ γ '' Icc 0 1) : ∀ᶠ z in 𝓝 q, windNum γ z = windNum γ q := by
  obtain ⟨r, hr, hrK⟩ := exists_ball_disjoint (isCompact_image_Icc hγ).isClosed hq
  filter_upwards [ball_mem_nhds q hr] with z hz
  refine windNum_eq_of_norm_sub_lt hγ hl (w := q) (w' := z) fun t ht => ?_
  calc ‖q - z‖ = dist z q := by rw [dist_eq_norm, norm_sub_rev]
    _ < r := mem_ball.1 hz
    _ ≤ ‖γ t - q‖ := hrK _ (mem_image_of_mem γ ht)

/-- A value of `g` near `q` on the good set, from constancy near `q` and accumulation of the good set. -/
theorem exists_eventually_eq_of_const {g : ℂ → ℤ} {B U : Set ℂ} {q : ℂ} (hU : U ∈ 𝓝 q)
    (hconst : ∀ z ∈ U, ∀ z' ∈ U, z ∈ B → z' ∈ B → g z = g z') (hfreq : ∃ᶠ z in 𝓝 q, z ∈ B) :
    ∃ v : ℤ, ∀ᶠ z in 𝓝 q, z ∈ B → g z = v := by
  obtain ⟨z₀, hz₀B, hz₀U⟩ := (hfreq.and_eventually hU).exists
  exact ⟨g z₀, Filter.mem_of_superset hU fun z hz hzB => hconst z hz z₀ hz₀U hzB hz₀B⟩

/-- The good set `ℍ ∖ A` accumulates at every point of `ℍ`: near a flow point `Ψ(η(u))` there are images of
points on the left of `η`. -/
theorem frequently_notMem_chartFlowSet {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {q : ℂ} (hqH : q ∈ H) :
    ∃ᶠ z in 𝓝 q, z ∈ H \ chartFlowSet η w s := by
  refine mem_closure_iff_frequently.1 ?_
  by_cases hqA : q ∈ chartFlowSet η w s
  · obtain ⟨p, ⟨⟨u, hu0, rfl⟩, hpD⟩, rfl⟩ := hqA
    have hupos : 0 < u := by
      rcases (mem_Ici.1 hu0).eq_or_lt with he | he
      · have hH := hpD.1
        rw [← he, hη.zero] at hH
        exact absurd rfl (ne_zero_of_mem_H hH)
      · exact he
    have hDo : IsOpen (H \ cfHullQ w s) := isOpen_H_diff_negInv_fwdHull hw hs
    have hcl : η u ∈ closure ((H \ cfHullQ w s) ∩ leftSideOf (arcRange η)) :=
      hDo.inter_closure ⟨hpD, hη.mem_closure_leftSideOf hupos⟩
    have hcont : ContinuousWithinAt (revChart w s) ((H \ cfHullQ w s) ∩ leftSideOf (arcRange η)) (η u) :=
      ((continuousOn_revChart hw hs) _ hpD).mono inter_subset_left
    refine closure_mono ?_ (hcont.mem_closure_image hcl)
    rintro _ ⟨p', ⟨hp'D, hp'L⟩, rfl⟩
    refine ⟨revChart_mem_H hw hs hp'D, ?_⟩
    rintro ⟨p'', ⟨hp''A, hp''D⟩, he⟩
    have := injOn_revChart hw hw0 hs hp''D hp'D he
    exact hp'L.1.2 (this ▸ hp''A)
  · exact subset_closure ⟨hqH, hqA⟩

/-- **The no-wrap step of Proposition 5.1 in the chart `Q`** (spec p. 135 with R45, R50; Astra's follow-up 4,
§1.7): `Prop51G.FwdNoWrapQStatement`, proved. -/
theorem fwdNoWrapQStatement : FwdNoWrapQStatement := by
  intro η w β s hη hw hw0 hβ hs0 hβne hbar hL
  have hs : 0 ≤ s := hs0.le
  have hβs : β s ≠ 0 := hβne s hs0
  have htip : negInv (β s) ∉ arcRange η := hL.1.2
  have hends := hasWesternExcursionEnds_of_rational hη hβ hw hw0 hs hβs htip hbar
  have hbd : IsBounded (chartFlowSet η w s) :=
    isBounded_revChart_arcRange_of_mem_leftSideOf hη hβ hw hw0 hs hL
  obtain ⟨R, hR0, hR⟩ := exists_closure_subset_ball hbd
  set A := chartFlowSet η w s with hAdef
  set U := excursionTimes η w s with hUdef
  -- the gate point `w₀`, on the right of `η`
  obtain ⟨gt⟩ := exists_positiveBoundaryGate hη hβ hw hw0 hs
  have : (𝓝[H] (gt.source : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ mem_Hbar_of_im_eq_zero (by simp))
  obtain ⟨w₀, hw₀R, hw₀H, hw₀b⟩ := ((gt.boundary_limit.eventually
    (Prop411Q.eventually_mem_rightSideOf hη gt.target_pos)).and
    (show ∀ᶠ z in 𝓝[H] (gt.source : ℂ), z ∈ H ∩ ball (gt.source : ℂ) gt.radius from
      inter_mem_nhdsWithin H (ball_mem_nhds _ gt.radius_pos))).exists
  have hw₀A : w₀ ∉ A := fun h =>
    (Set.eq_empty_iff_forall_notMem.1 gt.avoids) w₀ ⟨hw₀b, subset_closure h⟩
  -- the far point `w₁`, on the left of `η`
  let f : ℝ → ℂ := fun y => (y : ℂ) * I
  have hfnorm : ∀ y, ‖f y‖ = |y| := fun y => by
    simp only [f, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  have hfH : ∀ᶠ y in atTop, f y ∈ H := (eventually_gt_atTop 0).mono fun y hy => by
    show (0 : ℝ) < ((y : ℂ) * I).im
    simpa using hy
  have hfn : Tendsto (fun y => ‖f y‖) atTop atTop :=
    tendsto_abs_atTop_atTop.congr fun y => (hfnorm y).symm
  obtain ⟨y, hyL, hyR, hy0⟩ := (((tendsto_revChartInv_tip hβ hw hw0 hs hβs hfH hfn).eventually
    ((Cond44Ref.isOpen_leftSideOf_arcRange hη).mem_nhds hL)).and
    ((eventually_gt_atTop R).and (eventually_gt_atTop 0))).exists
  set w₁ := f y with hw₁def
  have hw₁H : w₁ ∈ H := by
    show (0 : ℝ) < ((y : ℂ) * I).im
    simpa using hy0
  have hw₁n : R ≤ ‖w₁‖ := by rw [hw₁def, hfnorm, abs_of_pos hy0]; exact hyR.le
  have hw₁A : w₁ ∉ A := fun h => by
    have := mem_ball_zero_iff.1 (hR (subset_closure h))
    linarith
  -- the segment from `w₀` to `w₁`
  let σ : ℝ → ℂ := fun t => w₀ + (t : ℂ) * (w₁ - w₀)
  have hσc : Continuous σ := by fun_prop
  have hσ0 : σ 0 = w₀ := by simp [σ]
  have hσ1 : σ 1 = w₁ := by simp [σ]
  have hσH : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ H := by
    intro t ht
    have ha : (0 : ℝ) < w₀.im := hw₀H
    have hb : (0 : ℝ) < w₁.im := hw₁H
    show (0 : ℝ) < (w₀ + (t : ℂ) * (w₁ - w₀)).im
    simp only [add_im, mul_im, ofReal_re, sub_im, ofReal_im, sub_re, zero_mul, add_zero]
    nlinarith [mul_nonneg ht.1 (sub_nonneg.2 (min_le_right w₀.im w₁.im)),
      mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 (min_le_left w₀.im w₁.im)), lt_min ha hb]
  set K := σ '' Icc 0 1 with hKdef
  have hKc : IsCompact K := isCompact_Icc.image hσc
  have hKH : K ⊆ H := by rintro _ ⟨t, ht, rfl⟩; exact hσH t ht
  -- the finitely many excursions met by the segment
  set F := (fun t => connectedComponentIn U t) '' (Ici 0 ∩ η ⁻¹' (revChartInv w s '' K)) with hFdef
  have hF : F.Finite := finite_excursions_meeting_chart_compact hη hw hw0 hs hKc hKH
  have hFmem : ∀ C ∈ F, ∃ u ∈ U, C = connectedComponentIn U u := by
    rintro C ⟨u, ⟨hu0, z, hzK, hzu⟩, rfl⟩
    have hD : η u ∈ H \ cfHullQ w s := hzu ▸ revChartInv_mem hw hw0 hs (hKH hzK)
    refine ⟨u, ⟨?_, hD⟩, rfl⟩
    rcases (mem_Ici.1 hu0).eq_or_lt with he | he
    · have hH := hD.1
      rw [← he, hη.zero] at hH
      exact absurd rfl (ne_zero_of_mem_H hH)
    · exact he
  have : Fintype F := hF.fintype
  have hne : ∀ C : F, Nonempty (ExcursionChartCut η w s C.1) := fun C => by
    obtain ⟨u, hu, hC⟩ := hFmem C.1 C.2
    rw [hC]
    exact nonempty_excursionChartCut hη hβ hw hw0 hs htip hends hu
  let κ : ∀ C : F, ExcursionChartCut η w s C.1 := fun C => Classical.choice (hne C)
  let wr : ℂ → ℤ := fun z => windNum (flowReferenceLoop η) (discRevChart w s z)
  let g : ℂ → ℤ := fun z => wr z - ∑ C : F, windNum (κ C).loop z
  set B := H \ A with hBdef
  -- a crosscut point of the segment
  have hloc : ∀ t ∈ Icc (0 : ℝ) 1, ∃ v : ℤ, ∀ᶠ z in 𝓝 (σ t), z ∈ B → g z = v := by
    intro t ht
    set q := σ t with hqdef
    have hqH := hσH t ht
    have hqK : q ∈ K := ⟨t, ht, rfl⟩
    by_cases hqA : q ∈ A
    · obtain ⟨p, ⟨⟨u₀, hu0, hpu⟩, hpD⟩, hq⟩ := hqA
      subst hpu
      have hu₀U : u₀ ∈ U := by
        refine ⟨?_, hpD⟩
        rcases (mem_Ici.1 hu0).eq_or_lt with he | he
        · have hH := hpD.1
          rw [← he, hη.zero] at hH
          exact absurd rfl (ne_zero_of_mem_H hH)
        · exact he
      have hinvq : revChartInv w s q = η u₀ := by
        rw [← hq]; exact revChartInv_revChart hw hw0 hs hpD
      have hC₀F : connectedComponentIn U u₀ ∈ F := ⟨u₀, ⟨hu0, q, hqK, hinvq⟩, rfl⟩
      set c₀ : F := ⟨connectedComponentIn U u₀, hC₀F⟩ with hc₀def
      obtain ⟨t₀, ht₀, ht₀u⟩ := (κ c₀).time_surj (mem_connectedComponentIn hu₀U)
      have hq₀ : (κ c₀).cut t₀ = q := by rw [(κ c₀).cut_eq t₀ ht₀, ht₀u, hq]
      obtain ⟨ε, hε, hconst⟩ := (κ c₀).exists_local_const hη hw hw0 hs ht₀
      rw [hq₀] at hconst
      have hothers : ∀ c : F, c ≠ c₀ → q ∉ (κ c).loop '' Icc 0 1 := by
        rintro c hc ⟨t', ht', he⟩
        obtain ⟨u', hu', hue⟩ := (κ c).exists_of_loop_mem_H ht' (he ▸ hqH)
        have h1 : revChart w s (η ((κ c).time u')) = revChart w s (η u₀) := by
          rw [← (κ c).cut_eq u' hu', ← hue, he, hq]
        have h2 := injOn_revChart hw hw0 hs ((κ c).eta_time_mem hu') hpD h1
        have h3 : (κ c).time u' = u₀ := hη.inj ((κ c).time_pos hu').le (mem_Ici.1 hu0) h2
        have h4 : u₀ ∈ c.1 := h3 ▸ (κ c).time_mem hu'
        obtain ⟨u'', _, hc''⟩ := hFmem c.1 c.2
        rw [hc''] at h4
        apply hc
        apply Subtype.ext
        change c.1 = connectedComponentIn U u₀
        rw [hc'', connectedComponentIn_eq h4]
      have hev : ∀ᶠ z in 𝓝 q, ∀ c : F, c ≠ c₀ → windNum (κ c).loop z = windNum (κ c).loop q := by
        refine Filter.eventually_all.2 fun c => ?_
        by_cases hc : c = c₀
        · exact Filter.Eventually.of_forall fun _ h => absurd hc h
        · exact (eventually_windNum_eq (κ c).continuousOn_loop (κ c).loop_closed
            (hothers c hc)).mono fun _ hz _ => hz
      refine exists_eventually_eq_of_const (Filter.inter_mem (ball_mem_nhds q hε) hev) ?_
        (frequently_notMem_chartFlowSet hη hw hw0 hs hqH)
      rintro z ⟨hzb, hzc⟩ z' ⟨hz'b, hz'c⟩ hzB hz'B
      have hsplit : ∀ x : ℂ, (∀ c : F, c ≠ c₀ → windNum (κ c).loop x = windNum (κ c).loop q) →
          g x = (wr x - windNum (κ c₀).loop x) - ∑ c ∈ ({c₀}ᶜ : Finset F), windNum (κ c).loop q := by
        intro x hx
        simp only [g]
        rw [Fintype.sum_eq_add_sum_compl c₀]
        rw [Finset.sum_congr rfl fun c hc => hx c (by simpa using hc)]
        ring
      rw [hsplit z hzc, hsplit z' hz'c, hconst z hzb z' hz'b hzB.1 hz'B.1 hzB.2 hz'B.2]
    · -- off the chart flow set
      have hqP : revChartInv w s q ∉ arcRange η := fun h =>
        hqA ⟨revChartInv w s q, ⟨h, revChartInv_mem hw hw0 hs hqH⟩, revChart_revChartInv hw hw0 hs hqH⟩
      have hcontq : ContinuousAt (revChartInv w s) q :=
        (continuousOn_revChartInv hw hw0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hqH)
      have hwr : ∀ᶠ z in 𝓝 q, wr z = wr q := by
        rcases hη.mem_leftSideOf_or_mem_rightSideOf (revChartInv_mem hw hw0 hs hqH).1 hqP with hql | hqr
        · filter_upwards [hcontq.eventually ((Cond44Ref.isOpen_leftSideOf_arcRange hη).mem_nhds hql)]
            with z hz
          exact (windNum_flowReferenceLoop_of_mem_left hη hz).trans
            (windNum_flowReferenceLoop_of_mem_left hη hql).symm
        · filter_upwards [hcontq.eventually ((Cond44Ref.isOpen_rightSideOf_arcRange hη).mem_nhds hqr)]
            with z hz
          exact (windNum_flowReferenceLoop_of_mem_right hη hz).trans
            (windNum_flowReferenceLoop_of_mem_right hη hqr).symm
      have hloops : ∀ᶠ z in 𝓝 q, ∀ c : F, windNum (κ c).loop z = windNum (κ c).loop q := by
        refine Filter.eventually_all.2 fun c => eventually_windNum_eq (κ c).continuousOn_loop
          (κ c).loop_closed ?_
        rintro ⟨t', ht', he⟩
        obtain ⟨u', hu', hue⟩ := (κ c).exists_of_loop_mem_H ht' (he ▸ hqH)
        exact hqA (he ▸ hue ▸ (κ c).cut_mem_chartFlowSet hu')
      refine ⟨g q, (hwr.and hloops).mono fun z hz _ => ?_⟩
      simp only [g, hz.1, hz.2]
  have hdense : ∀ t ∈ Icc (0 : ℝ) 1, ∃ᶠ z in 𝓝 (σ t), z ∈ B := fun t ht =>
    frequently_notMem_chartFlowSet hη hw hw0 hs (hσH t ht)
  have key := eq_of_locally_const_along hσc.continuousOn hloc hdense
    (by rw [hσ0]; exact ⟨hw₀H, hw₀A⟩) (by rw [hσ1]; exact ⟨hw₁H, hw₁A⟩)
  rw [hσ0, hσ1] at key
  -- the two ends
  have hg₁ : g w₁ = 1 := by
    have h1 : wr w₁ = 1 := windNum_flowReferenceLoop_of_mem_left hη hyL
    have h2 : ∑ C : F, windNum (κ C).loop w₁ = 0 :=
      Finset.sum_eq_zero fun C _ => (κ C).windNum_loop_eq_zero_of_norm hR hw₁n
    simp only [g, h1, h2, sub_zero]
  have hg₀ : g w₀ ≤ 0 := by
    have h1 : wr w₀ = 0 := windNum_flowReferenceLoop_of_mem_right hη hw₀R
    have h2 : 0 ≤ ∑ C : F, windNum (κ C).loop w₀ :=
      Finset.sum_nonneg fun C _ => (κ C).windNum_loop_nonneg_of_gate hw hs gt.source_pos gt.radius_pos
        gt.avoids hw₀b hw₀H
    simp only [g, h1]
    linarith
  rw [key, hg₁] at hg₀
  exact absurd hg₀ (by norm_num)

universe u

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs and (E1) alone**: the forward-route assembly
`Aux61Loc.prop51QStatement_of_partA_of_noCrosscut` with the no-wrap topology `FwdNoWrapQStatement` discharged by
`fwdNoWrapQStatement`. The remaining input `hno` is (E1) in crosscut form below the critical gap (PROVE-AUX61-R23). -/
theorem prop51QStatement_of_partA_of_noCrosscut' (hA : PartAInputsSixteenDiv)
    (hno : Aux61Loc.FwdNoEastCrosscutQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    Cond44Ref.Prop51QStatement.{u} :=
  Aux61Loc.prop51QStatement_of_partA_of_noCrosscut hA fwdNoWrapQStatement hno

/-- **Theorem 1.2's input `CfAvoidLeftQ.CfFirstContactQStatement` from Zhan's Part A inputs and (E1) alone**
(`Prop51I.cfFirstContactQStatement_of_partA_of_eastSide` with the no-wrap topology discharged and (E1) in crosscut
form). -/
theorem cfFirstContactQStatement_of_partA_of_noCrosscut' (hA : PartAInputsSixteenDiv)
    (hno : Aux61Loc.FwdNoEastCrosscutQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  Prop51I.cfFirstContactQStatement_of_partA_of_eastSide hA fwdNoWrapQStatement
    (Aux61Loc.fwdPostContactEastSideQOn_of_noCrosscut (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hno)

end InteractingSLE.Sec5.Prop51HGate
