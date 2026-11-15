/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripDetPath
import InteractingSLE.Spec.Sec7.FlowReflectFlow

/-!
# The reflected condition (4.4) for a decreasing angle change

Packet PROVE-STRIPSYS27 (the walls' Lemma 6.2 inputs, for `β^{(r)}`). Specification §7.4, proof of Aux. lemma 130
(`source/spec/p385-432.md` L442–L446, p. 410): "For the decreasing change of `β^{(r)}`, put `δ′ = π/2 − θ₂ ∈ (0, π)`.
Its seed totals are `δ′χ/λ` on the left and `−δ′χ/λ` on the right, so the reflected condition applies."

The reflected condition is (4.4) for the mirror image under `R(z) = −z̄` (`FlowReflect`: the angle-`θ` flow line of `h`
with data `b` is mapped to the angle-`(−θ)` flow line of `−h ∘ R` with data `y ↦ −b(−y)`). This file provides:

* `reflWord`: the mirror image of a boundary word (positions negated, heights negated in reverse order), Borel, with
  `(reflWord c).fn = reflData c.fn` off `reflJumps c.jumps = (reflWord c).jumps`;
* **`isFlowLineDriver_reflect`**: a flow-line driver of angle `θ` is mapped to the flow-line driver `−W` of angle `−θ`
  of the reflected field, with the reflected data;
* `stopWord_fn_of_neg`, `stopWord_fn_of_pos`: the heights of the restarted word (PROVE-STAGEDLAW's `stopWord`) left and
  right of the tip are either the seed values `∓λ − θ₀χ` or original heights on the same side (extracted from
  PROVE-STRIPSYS21's `cond44_flowLine_stopWord`);
* **`cond44_reflWord_stopWord`**: for a **decreasing** change `θ ≤ θ₀ ≤ θ + π` and original heights with
  `c + θχ ≤ −λ` on the left and `c + θχ ≥ λ − πχ` on the right (both implied by Aux. lemma 130's nonnegative cumulative
  values), the mirrored restarted word satisfies (4.4) at angle `−θ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripWall

open Sec4 QuantumZipper Restart Exist Exist.Staged Exist.StagedLaw StripDet
open FlowReflect (reflData reflJumps reflField)

/-! ### The mirror image of a boundary word -/

/-- **The mirror image of a boundary word** under `y ↦ −y`: positions `−p i`, heights `−q (n − k)`. -/
def reflWord (c : BoundaryWord) : BoundaryWord := (c.1, fun i => -c.2.1 i, fun k => -c.2.2 (c.1 - k))

theorem measurable_reflWord : Measurable reflWord := by
  refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).neg
  · refine measurable_pi_iff.2 fun k => ?_
    exact measurable_from_prod_countable_right fun n =>
      ((measurable_pi_apply (n - k)).comp measurable_snd).neg

theorem mem_jumps_reflWord {c : BoundaryWord} {y : ℝ} : y ∈ (reflWord c).jumps ↔ -y ∈ c.jumps := by
  rw [BoundaryWord.mem_jumps, BoundaryWord.mem_jumps]
  constructor
  · rintro ⟨i, hi, he⟩
    have he' : -c.2.1 i = y := he
    exact ⟨i, hi, by rw [← he', neg_neg]⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, by show -c.2.1 i = y; rw [he, neg_neg]⟩

theorem jumps_reflWord (c : BoundaryWord) : (reflWord c).jumps = reflJumps c.jumps := by
  ext y
  rw [mem_jumps_reflWord, FlowReflect.mem_reflJumps]

/-- Off the mirrored jumps, the mirrored word's boundary function is the mirrored data. -/
theorem fn_reflWord {c : BoundaryWord} {y : ℝ} (hy : -y ∉ c.jumps) : (reflWord c).fn y = reflData c.fn y := by
  have hidx : (reflWord c).index y + c.index (-y) = c.1 := by
    have e : (Finset.range c.1).filter (fun i => -c.2.1 i < y) =
        (Finset.range c.1).filter (fun i => ¬ c.2.1 i < -y) := by
      refine Finset.filter_congr fun i hi => ?_
      have hne : c.2.1 i ≠ -y := fun he => hy (BoundaryWord.mem_jumps.2 ⟨i, Finset.mem_range.1 hi, he⟩)
      constructor
      · intro h1 h2
        linarith
      · intro h1
        rcases (not_lt.1 h1).lt_or_eq with h | h
        · linarith
        · exact absurd h.symm hne
    show ((Finset.range c.1).filter (fun i => -c.2.1 i < y)).card +
      ((Finset.range c.1).filter (fun i => c.2.1 i < -y)).card = c.1
    rw [e, add_comm, Finset.card_filter_add_card_filter_not, Finset.card_range]
  show -c.2.2 (c.1 - (reflWord c).index y) = -c.fn (-y)
  rw [show c.1 - (reflWord c).index y = c.index (-y) by omega]
  rfl

/-! ### Flow-line drivers under the reflection -/

/-- The reflection of a flow-line coupling from `x`, in unfolded form (the seed `−x` kept symbolic). -/
theorem exists_reflect_of_coupling {κ θ x : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {h h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {𝓕 : Filtration ℝ≥0 mΩ} {VL : Fin (flowLineNL b J x) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR b J x) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J)
    (htr : ∀ ω, IsTranslateAddConst x (θ * chiC κ) (h ω) (h' ω))
    (hc : IsOptionalHullCoupling κ (flowLineXL b J x) (flowLineXR b J x) (flowLineRhoL κ b J x θ)
      (flowLineRhoR κ b J x θ) P 𝓕 W VL VR B ζ h') :
    ∃ (h'' : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (𝓕' : Filtration ℝ≥0 mΩ)
      (VL' : Fin (flowLineNL (reflData b) (reflJumps J) (-x)) → ℝ≥0 → Ω → ℝ)
      (VR' : Fin (flowLineNR (reflData b) (reflJumps J) (-x)) → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
      (∀ ω, IsTranslateAddConst (-x) (-θ * chiC κ) (reflField (h ω)) (h'' ω)) ∧
      IsOptionalHullCoupling κ (flowLineXL (reflData b) (reflJumps J) (-x))
        (flowLineXR (reflData b) (reflJumps J) (-x)) (flowLineRhoL κ (reflData b) (reflJumps J) (-x) (-θ))
        (flowLineRhoR κ (reflData b) (reflJumps J) (-x) (-θ)) P 𝓕' (-W) VL' VR' B' ζ h'' := by
  have hc' := FlowReflect.IsOptionalHullCoupling.castR (FlowReflect.flowLineNR_reflData hb x)
    (FlowReflect.IsOptionalHullCoupling.castL (FlowReflect.flowLineNL_reflData hb x)
      (FlowReflect.IsOptionalHullCoupling.reflect hc))
  refine ⟨fun ω => reflField (h' ω), 𝓕,
    fun i => fun t ω => -VR (Fin.cast (FlowReflect.flowLineNL_reflData hb x) i) t ω,
    fun i => fun t ω => -VL (Fin.cast (FlowReflect.flowLineNR_reflData hb x) i) t ω, -B, fun ω => ?_, ?_⟩
  · have h1 := FlowReflect.IsTranslateAddConst.reflect (htr ω)
    rwa [← neg_mul] at h1
  · have eXL := funext (FlowReflect.flowLineXL_reflData_apply b J hb x)
    have eXR := funext (FlowReflect.flowLineXR_reflData_apply b J hb x)
    have eRL := funext (FlowReflect.flowLineRhoL_reflData_apply b J hb κ x θ)
    have eRR := funext (FlowReflect.flowLineRhoR_reflData_apply b J hb κ x θ)
    rw [eXL, eXR, eRL, eRR]
    exact hc'

/-- **A flow-line driver under the reflection `R(z) = −z̄`**: if `W` drives the angle-`θ` flow line from `0` of `h`
with data `b`, then `−W` drives the angle-`(−θ)` flow line from `0` of `−h ∘ R` with data `y ↦ −b(−y)`, same
lifetime. -/
theorem isFlowLineDriver_reflect {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hb : IsPiecewiseConstantBoundaryData b J) (hd : IsFlowLineDriver κ b J θ P h W ζ) :
    IsFlowLineDriver κ (reflData b) (reflJumps J) (-θ) P (fun ω => reflField (h ω)) (-W) ζ := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hc⟩ := hd
  have key := exists_reflect_of_coupling (x := 0) hb htr hc
  rw [neg_zero] at key
  exact key

/-- **Mirror congruence**: a flow-line driver for the mirrored data is one for the mirrored word. -/
theorem isFlowLineDriver_reflWord {κ θ : ℝ} {c : BoundaryWord} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hd : IsFlowLineDriver κ (reflData c.fn) (reflJumps c.jumps) θ P h W ζ) :
    IsFlowLineDriver κ (reflWord c).fn (reflWord c).jumps θ P h W ζ := by
  refine (isFlowLineDriver_congr_of_eqOn (reflWord c).isPiecewiseConstantBoundaryData
    (FlowReflect.isPiecewiseConstantBoundaryData_reflData c.isPiecewiseConstantBoundaryData) (reflJumps c.jumps)
    fun y hy => ?_).1 hd
  rw [fn_reflWord (fun h => hy (FlowReflect.mem_reflJumps.2 h))]

/-! ### The heights of the restarted word -/

section StopWord

variable {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ₀ : ℝ) (r : RecData)

include hκ in
/-- **Left of the tip, the restarted word has the seed height `−λ − θ₀χ` or an original left height** (the left half of
PROVE-STRIPSYS21's proof of `cond44_flowLine_stopWord`). -/
theorem stopWord_fn_of_neg {y : ℝ} (hy : y < 0) :
    (stopWord κ (c, θ₀, r)).fn y = -sleLambda κ - θ₀ * chiC κ ∨
      ∃ x, x < 0 ∧ x ∉ c.jumps ∧ (stopWord κ (c, θ₀, r)).fn y = c.fn x := by
  have hlam : Real.pi / Real.sqrt κ = sleLambda κ := rfl
  have hc := c.isPiecewiseConstantBoundaryData
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  set nL := flowLineNL c.fn c.jumps 0 with hnL
  set nR := flowLineNR c.fn c.jumps 0 with hnR
  set pL : ℕ → ℝ := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) with hpL
  set pR : ℕ → ℝ := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) with hpR
  set ρL := (padFL κ θ₀ c.fn c.jumps).2.1 with hρL
  set ρR := (padFL κ θ₀ c.fn c.jumps).2.2 with hρR
  have hsw : stopWord κ (c, θ₀, r) = forceWord κ nL nR pL pR ρL ρR (θ₀ * chiC κ) := rfl
  have hraw : rawPos nL pL pR nL = 0 := by simp [rawPos]
  have hleft : ∀ j, 1 ≤ j → j ≤ nL → ∃ x, x < 0 ∧ x ∉ c.jumps ∧
      -sleLambda κ * (1 + ∑ i ∈ Finset.range j, ρL i) = c.fn x + θ₀ * chiC κ := by
    intro j hj1 hjn
    obtain ⟨x, hx0, hxE, hS⟩ := exists_left_point (strictAnti_flowLineXL c.fn c.jumps) hF.2.1
      (insert 0 c.jumps) hj1 hjn
    have hxJ : x ∉ c.jumps := fun h => hxE (Finset.mem_insert_of_mem h)
    refine ⟨x, hx0, hxJ, ?_⟩
    have e1 := forceBoundaryData_of_neg (κ := κ) (flowLineRhoL κ c.fn c.jumps 0 θ₀) (flowLineRhoR κ c.fn c.jumps 0 θ₀)
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) hx0
    rw [Exist.forceBoundaryData_flowLine_seed hκ hc 0 θ₀ hx0.ne (by rwa [add_zero]), add_zero, hS] at e1
    rw [e1, hρL, ← sum_range_pad hjn]
    rfl
  set m := ((Finset.range (nL + 1 + nR)).filter fun k => cumMax (rawPos nL pL pR) k < y).card with hm
  have hfn : (stopWord κ (c, θ₀, r)).fn y = wordHeight κ nL ρL ρR (θ₀ * chiC κ) m := by rw [hsw]; rfl
  have hmle : m ≤ nL := by
    have hsub : (Finset.range (nL + 1 + nR)).filter (fun k => cumMax (rawPos nL pL pR) k < y) ⊆
        Finset.range nL := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [Finset.mem_range]
      by_contra hkn
      have h1 : rawPos nL pL pR nL ≤ cumMax (rawPos nL pL pR) k :=
        (le_cumMax _ nL).trans (monotone_cumMax _ (not_lt.1 hkn))
      rw [hraw] at h1
      linarith [hk.2]
    calc m ≤ (Finset.range nL).card := Finset.card_le_card hsub
      _ = nL := Finset.card_range nL
  have hwh : wordHeight κ nL ρL ρR (θ₀ * chiC κ) m =
      -sleLambda κ * (1 + ∑ i ∈ Finset.range (nL - m), ρL i) - θ₀ * chiC κ := by
    simp only [wordHeight, hmle, ↓reduceIte, hlam]
  rw [hfn, hwh]
  rcases Nat.eq_zero_or_pos (nL - m) with h0 | hpos
  · left
    rw [h0, Finset.range_zero, Finset.sum_empty]
    ring
  · right
    obtain ⟨x, hx0, hxJ, hx⟩ := hleft (nL - m) hpos (Nat.sub_le _ _)
    exact ⟨x, hx0, hxJ, by rw [hx]; ring⟩

include hκ in
/-- **Right of the tip, the restarted word has the seed height `λ − θ₀χ` or an original right height** (the right half
of PROVE-STRIPSYS21's proof of `cond44_flowLine_stopWord`). -/
theorem stopWord_fn_of_pos {y : ℝ} (hy : 0 < y) :
    (stopWord κ (c, θ₀, r)).fn y = sleLambda κ - θ₀ * chiC κ ∨
      ∃ x, 0 < x ∧ x ∉ c.jumps ∧ (stopWord κ (c, θ₀, r)).fn y = c.fn x := by
  have hlam : Real.pi / Real.sqrt κ = sleLambda κ := rfl
  have hc := c.isPiecewiseConstantBoundaryData
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  set nL := flowLineNL c.fn c.jumps 0 with hnL
  set nR := flowLineNR c.fn c.jumps 0 with hnR
  set pL : ℕ → ℝ := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) with hpL
  set pR : ℕ → ℝ := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) with hpR
  set ρL := (padFL κ θ₀ c.fn c.jumps).2.1 with hρL
  set ρR := (padFL κ θ₀ c.fn c.jumps).2.2 with hρR
  have hsw : stopWord κ (c, θ₀, r) = forceWord κ nL nR pL pR ρL ρR (θ₀ * chiC κ) := rfl
  have hpL0 : ∀ i, pL i ≤ 0 := by
    intro i
    refine markPosL_nonpos (continuous_rdrv r) (StagedLaw.rdrv_zero r) (StagedLaw.rtime_nonneg r) ?_
    show (if hi : i < nL then flowLineXL c.fn c.jumps 0 ⟨i, hi⟩ else 0) ≤ 0
    split_ifs
    · exact hF.2.1 _
    · exact le_rfl
  have hright : ∀ j, 1 ≤ j → j ≤ nR → ∃ x, 0 < x ∧ x ∉ c.jumps ∧
      sleLambda κ * (1 + ∑ i ∈ Finset.range j, ρR i) = c.fn x + θ₀ * chiC κ := by
    intro j hj1 hjn
    obtain ⟨x, hx0, hxE, hS⟩ := exists_right_point (strictMono_flowLineXR c.fn c.jumps) hF.2.2.2
      (insert 0 c.jumps) hj1 hjn
    have hxJ : x ∉ c.jumps := fun h => hxE (Finset.mem_insert_of_mem h)
    refine ⟨x, hx0, hxJ, ?_⟩
    have e1 := forceBoundaryData_of_nonneg (κ := κ) (flowLineRhoL κ c.fn c.jumps 0 θ₀)
      (flowLineRhoR κ c.fn c.jumps 0 θ₀) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) hx0.le
    rw [Exist.forceBoundaryData_flowLine_seed hκ hc 0 θ₀ hx0.ne' (by rwa [add_zero]), add_zero, hS] at e1
    rw [e1, hρR, ← sum_range_pad hjn]
    rfl
  set m := ((Finset.range (nL + 1 + nR)).filter fun k => cumMax (rawPos nL pL pR) k < y).card with hm
  have hfn : (stopWord κ (c, θ₀, r)).fn y = wordHeight κ nL ρL ρR (θ₀ * chiC κ) m := by rw [hsw]; rfl
  have hcum : cumMax (rawPos nL pL pR) nL ≤ 0 := by
    refine cumMax_nonpos fun i hi => ?_
    unfold rawPos
    split_ifs
    · exact hpL0 _
    · exact le_rfl
    · omega
  have hmge : nL + 1 ≤ m := by
    have hsub : Finset.range (nL + 1) ⊆
        (Finset.range (nL + 1 + nR)).filter (fun k => cumMax (rawPos nL pL pR) k < y) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, ((monotone_cumMax _ (by omega : k ≤ nL)).trans hcum).trans_lt hy⟩
    calc nL + 1 = (Finset.range (nL + 1)).card := (Finset.card_range _).symm
      _ ≤ m := Finset.card_le_card hsub
  have hmle : m ≤ nL + 1 + nR := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  have hwh : wordHeight κ nL ρL ρR (θ₀ * chiC κ) m =
      sleLambda κ * (1 + ∑ i ∈ Finset.range (m - nL - 1), ρR i) - θ₀ * chiC κ := by
    have : ¬ m ≤ nL := by omega
    simp only [wordHeight, this, ↓reduceIte, hlam]
  rw [hfn, hwh]
  rcases Nat.eq_zero_or_pos (m - nL - 1) with h0 | hpos
  · left
    rw [h0, Finset.range_zero, Finset.sum_empty]
    ring
  · right
    obtain ⟨x, hx0, hxJ, hx⟩ := hright (m - nL - 1) hpos (by omega)
    exact ⟨x, hx0, hxJ, by rw [hx]; ring⟩

end StopWord

/-- **The reflected condition (4.4) for a decreasing restart** (spec p. 410, "the reflected condition applies"): if the
original word `c` has heights `c + θχ ≤ −λ` left of `0` and `c + θχ ≥ λ − πχ` right of `0`, and `θ ≤ θ₀ ≤ θ + π`, then
the mirror image of the restarted word `stopWord κ (c, θ₀, r)` satisfies (4.4) at angle `−θ`. -/
theorem cond44_reflWord_stopWord {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord) (θ₀ θ : ℝ) (r : RecData)
    (hθ : θ ≤ θ₀) (hθπ : θ₀ ≤ θ + Real.pi)
    (hL : ∀ y : ℝ, y < 0 → y ∉ c.jumps → c.fn y + θ * chiC κ ≤ -sleLambda κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ c.jumps → sleLambda κ - Real.pi * chiC κ ≤ c.fn y + θ * chiC κ) :
    Cond44 κ (flowLineRhoL κ (reflWord (stopWord κ (c, θ₀, r))).fn (reflWord (stopWord κ (c, θ₀, r))).jumps 0 (-θ))
      (flowLineRhoR κ (reflWord (stopWord κ (c, θ₀, r))).fn (reflWord (stopWord κ (c, θ₀, r))).jumps 0 (-θ)) := by
  have hχ := chiC_pos hκ hκ4
  refine cond44_flowLine_of_heights hκ (reflWord (stopWord κ (c, θ₀, r))).isPiecewiseConstantBoundaryData (-θ)
    (fun y hy hyJ => ?_) (fun y hy hyJ => ?_)
  · have hyJ' : -y ∉ (stopWord κ (c, θ₀, r)).jumps := fun h => hyJ (mem_jumps_reflWord.2 h)
    rw [fn_reflWord hyJ']
    simp only [reflData]
    rcases stopWord_fn_of_pos hκ c θ₀ r (neg_pos.2 hy) with h1 | ⟨x, hx0, hxJ, h1⟩
    · rw [h1]
      nlinarith
    · rw [h1]
      have := hR x hx0 hxJ
      linarith
  · have hyJ' : -y ∉ (stopWord κ (c, θ₀, r)).jumps := fun h => hyJ (mem_jumps_reflWord.2 h)
    rw [fn_reflWord hyJ']
    simp only [reflData]
    rcases stopWord_fn_of_neg hκ c θ₀ r (neg_neg_iff_pos.2 hy) with h1 | ⟨x, hx0, hxJ, h1⟩
    · rw [h1]
      nlinarith
    · rw [h1]
      have := hL x hx0 hxJ
      linarith

end StripWall

end Sec7

end InteractingSLE
