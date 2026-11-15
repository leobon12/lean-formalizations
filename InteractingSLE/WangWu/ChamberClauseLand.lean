/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.J5ChartClauseLand
import InteractingSLE.Spec.Sec7.Lemma71TMain

/-!
# (J5) at `κ = 4`: the landing of the chamber chart on the middle line, and the fixed-time chamber clause

Packet PROVE-WW-B28 (Wang–Wu, `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31; Proposition 4.20 on
the middle line, text dump L1701–1745). PROVE-WW-B22 reduced WW-B23's fixed-time chamber clause
`ChamberCond.ChamberClauseStatement` to the middle-line side limits `ChamberCurveSideStatement`, and those to the
lift-free landing of the chamber chart on the middle line (`chamberCurveSideStatement_of_land`). This file proves the
landing on every **seed** three-line space and hence the clause, with no named input:

* `ae_isPocketSeg_three`: on every three-line space with a chamber construction, almost surely the pathwise pocket data
  `Sec7.Lemma71P.IsPocketSeg` of the middle line hold (mirrored from `Sec7.Lemma71P.ae_isPocketSeg`; the order clause of
  the frame is `IsThreeLineSpace.ae_closedLeftSide`);
* `IsSeedThreeSpace.ae_exists_isGeneratingTrace_middle`: the middle seed line almost surely has a generating driver on
  `[0, ∞)` (Proposition 4.18's trace part, `IsMarkedChain.ae_seedLine`);
* **`IsSeedThreeSpace.ae_middleLand`**: at every capacity time, almost surely below the terminal capacity, at every
  chart point of the two middle intervals the inverse chart of the remaining chamber lands on the corresponding side of
  the middle line at a point of the stopped prefix off the facing wall (`MiddleLand`). The proof is the specification's
  `Sec7.Lemma71P.middleLandingStatement_of_midRealOff` without the lift clause, with the deterministic
  `Sec7.Lemma71T.midRealOffStatement` (PROVE-LEMMA71T) and a pathwise inherited branch
  (`Sec7.Lemma71O.exists_isPocketBranch`; the inverse chart does not depend on the branch shift);
* **`chamberCurveSideStatement`** : `ChamberCurveSideStatement` (the proof of `chamberCurveSideStatement_of_land` with
  the landing above);
* **`chamberClauseStatement`** : `ChamberCond.ChamberClauseStatement` (WW-B23's (J5)).

PROVE-WW-B22's named `ChamberLandStatement` quantifies over **every** three-line space; its conclusion asks for a
generating driver of the middle curve, which a three-line space does not provide (a deterministic time change of the
middle curve keeps every clause of `IsThreeLineSpace` but is not capacity-parametrized). It is not used here: the
landing is proved on seed three-line spaces, which is all that `ChamberCurveSideStatement` needs.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.WangWu.SeedThree

open QuantumZipper (H Hbar chiC fwdMap fwdMapInv)
open QuantumZipper.CA (cayley)
open Sec7 MartChar Sec7.Lemma71C Sec7.Lemma71D Sec7.Lemma71E Sec7.Lemma71I Sec7.Lemma71K Sec7.Lemma71L Sec7.Lemma71M
  Sec7.Lemma71N Sec7.Lemma71P Sec7.Lemma71Q Sec6 LocalSets

/-! ### The pathwise pocket data on a three-line space -/

section Seg

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- **Almost surely the pocket data of the middle line hold** on a three-line space (`IsPocketSeg`, with the visit
clock), together with the good event (mirrored from `Sec7.Lemma71P.ae_isPocketSeg`; the frame's order clause is
`IsThreeLineSpace.ae_closedLeftSide`). -/
theorem ae_isPocketSeg_three (hS : IsThreeLineSpace P h u₀ β α γ) (hpc : IsPocketConstruction P β α γ C c γ') :
    ∀ᵐ ω ∂P, PocketGood β α γ C c γ' ω ∧ ∃ (a' b' : ℝ) (Ψ : ℂ → ℂ),
      IsPocketSeg (β ω) (α ω) (γ ω) (C ω) (c ω) Ψ a' b' (γ' ω) (visitClock (γ ω) (closure (cayley '' C ω))) := by
  have hS' := hS
  obtain ⟨-, -, -, hβ62, hα62, hγ62, hae⟩ := hS'
  obtain ⟨-, -, him3, -, -, -, -⟩ := Sec7.Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, hlog, hbetw, hfr, hsegc, -, hmark⟩ := hpc'
  filter_upwards [ae_pocketGood_three hS hpc, hae, hS.ae_closedLeftSide, hbetw, hfr, hmark] with ω hg hω hcl hbω
    hfrω hmω
  obtain ⟨-, hsβ, hsα, hsγ, hord, -, -⟩ := hω
  obtain ⟨a', b', Ψ, hMk, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hseg, hrange⟩ := hmω
  have hF : IsPocketFrame (β ω) (α ω) (C ω) (c ω) Ψ a' b' :=
    ⟨hsβ, hsα, hcl.2.2, hbω, hMk, hconf ω, hdom ω, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hfrω⟩
  have hCo : IsOpen (C ω) := (hC ω).1
  have hCH : C ω ⊆ H := (hC ω).2.2.2
  have hγH : ∀ t, γ ω t ∈ Hbar := fun t => him3 2 ω t
  obtain ⟨hvc, hcay, -, -, -⟩ := hg.visit hCo hCH (hconf ω) (hdom ω) hγH
  obtain ⟨-, hκm, hκ0, -, -, -⟩ := hvc
  have hγα : Disjoint (range (γ ω)) (rightSideOf (range (α ω))) := by
    have h := hord.right_middle
    rwa [Lemma71I.arcRange_realPath, Lemma71I.arcRange_realPath] at h
  exact ⟨hg, a', b', Ψ, ⟨hF, hsγ, hγα, hlog ω, hsegc ω, hseg, hrange, hκm, hκ0, hcay⟩⟩

end Seg

/-! ### The middle seed line is a Loewner trace -/

section Trace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ}

/-- **The middle line of a seed three-line space almost surely has a generating driver on `[0, ∞)`** (the seed line of
height `0` is a generating trace of its driver: Proposition 4.18's trace part, `IsMarkedChain.ae_seedLine`). -/
theorem IsSeedThreeSpace.ae_exists_isGeneratingTrace_middle {rL rR u₁ u₂ : ℝ}
    (hS : IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ) :
    ∀ᵐ ω ∂P, ∃ W : ℝ≥0 → ℝ, IsGeneratingTrace W ⊤ (γ ω) := by
  obtain ⟨hu₁, hu₂, hL, hR, -, -, -, hcoup⟩ := hS
  have hl : 0 < wwLambda := wwLambda_pos
  have hL0 : 0 ≤ rL - 0 / wwLambda := by
    have := div_pos hu₂ hl
    rw [zero_div, sub_zero]; linarith
  have hR0 : 0 ≤ rR + 0 / wwLambda := by
    have := div_neg_of_neg_of_pos hu₁ hl
    rw [zero_div, add_zero]; linarith
  obtain ⟨𝓕γ, Wγ, VLγ, VRγ, Bγ, ζγ, hCγ, hsγ⟩ := hcoup 0 γ (by simp)
  filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL0 hR0) hCγ.1,
    hsγ] with ω hmω hsω
  obtain ⟨-, ⟨η, hη, heq⟩, -⟩ := hmω
  have hγη : γ ω = η := funext fun t => by
    have h1 := congrFun hsω.2 (t : ℝ)
    rw [Lemma71I.realPath_coe, heq] at h1
    simpa only [Real.toNNReal_coe] using h1
  exact ⟨fun t => Wγ t ω, by rw [hγη]; exact hη⟩

end Trace

/-! ### The landing of the chamber chart on the middle line -/

section Land

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- **The lift-free landing of the chamber chart on the middle line**, on every seed three-line space (PROVE-WW-B22's
`ChamberLandStatement` on seed spaces). For every chamber construction with its capacity data, at every capacity time
`t`, almost surely on `{t < capLife}` there is a generating driver `W` of the middle line such that at every chart point
of `(L_t − W_t, 0)` the time-`t` inverse chart of the remaining chamber lands on the left side of `γ` at a point of the
stopped prefix (positive time, before the capacity stop) off the left wall `β`, and at every chart point of
`(0, R_t − W_t)` on the right side at a point off the right wall `α`. The specification's
`Sec7.Lemma71P.middleLandingStatement_of_midRealOff` without the lift clause, with `Sec7.Lemma71T.midRealOffStatement`;
the inherited branch of the frame is chosen pathwise (`Sec7.Lemma71O.exists_isPocketBranch`) — the inverse chart does
not depend on it. -/
theorem IsSeedThreeSpace.ae_middleLand {rL rR u₁ u₂ : ℝ} (hS : IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)}
    {Y : Hist × Hist → ℂ} (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z) (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∃ W : ℝ≥0 → ℝ, IsGeneratingTrace W ⊤ (γ ω) ∧
      (∀ x : ℝ, geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t < x → x < 0 →
        MiddleLand (γ ω) (β ω) (capTime G M Y β α γ t ω)
          (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (leftSideOf (range (γ ω))) (pocketInv (shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s) t) x) ∧
      (∀ x : ℝ, 0 < x → x < geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t →
        MiddleLand (γ ω) (α ω) (capTime G M Y β α γ t ω)
          (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (rightSideOf (range (γ ω))) (pocketInv (shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s) t) x) := by
  have hoff : MidRealOffStatement := Sec7.Lemma71T.midRealOffStatement
  have hT : IsThreeLineSpace P h u₀ β α γ := hS.2.2.2.2.2.2.1
  have hT' := hT
  obtain ⟨-, -, -, hβ62, hα62, hγ62, -⟩ := hT'
  obtain ⟨hc3, -, him3, -, -, -, -⟩ := Sec7.Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, -, -, -, -, -⟩ := hpc'
  filter_upwards [ae_isPocketSeg_three hT hpc, hS.ae_exists_isGeneratingTrace_middle] with ω ⟨hg, a', b', Ψ, hP⟩
    ⟨Wγ, htrγ⟩ htl
  obtain ⟨L, hL, hlift⟩ := hP.log
  obtain ⟨n, hNω⟩ := Sec7.Lemma71O.exists_isPocketBranch hP.frame hL hlift
  set w : ℝ≥0 → ℝ := fun s => segDriver (γ' ω) s with hwdef
  have hCo : IsOpen (C ω) := (hC ω).1
  have hCH : C ω ⊆ H := (hC ω).2.2.2
  have hγH : ∀ t, γ ω t ∈ Hbar := fun t => him3 2 ω t
  obtain ⟨W, hW, hW0, hWe, η, hη, hηe⟩ := exists_loewnerTrace hP.seg htl
  have hTs : IsTSetting (β ω) (α ω) (γ ω) (C ω) (c ω) Ψ a' b' (γ' ω)
      (visitClock (γ ω) (closure (cayley '' C ω))) n W η t := ⟨hP, hNω, htl, hW, hW0, hWe, hη, hηe⟩
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hWt : w t = W t := by
    have := hWe ⟨ht0, le_rfl⟩
    simp only [Ito.rpath, Real.toNNReal_coe] at this
    exact this.symm
  have hR' : RealFlow.rightImg (Ito.rpath w) 0 t = RealFlow.rightImg W 0 t :=
    Lemma71B.rightImg_congr hW ht0 (fun r hr => (hWe hr).symm) 0
  have hL' : RealFlow.rightImg (fun s => -Ito.rpath w s) 0 t = RealFlow.rightImg (fun s => -W s) 0 t :=
    Lemma71B.rightImg_congr hW.neg ht0 (fun r hr => by show -Ito.rpath w r = -W r; rw [hWe hr]) 0
  have hvL : geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t = midL W t := by
    have e : geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω =
        -RealFlow.rightImg (fun s => -Ito.rpath (fun s => segDriver (γ' ω) s) s) 0 t := by
      simp only [geomL, LP.twoSeedXL, neg_zero]
      rfl
    rw [e]
    show -RealFlow.rightImg (fun s => -Ito.rpath w s) 0 t - w t = midL W t
    rw [hL', hWt]
    rfl
  have hvR : geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t = midR W t := by
    have e : geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω =
        RealFlow.rightImg (Ito.rpath fun s => segDriver (γ' ω) s) 0 t := by
      simp only [geomR, LP.twoSeedXR]
      rfl
    rw [e]
    show RealFlow.rightImg (Ito.rpath w) 0 t - w t = midR W t
    rw [hR', hWt]
    rfl
  obtain ⟨-, -, hinv', -⟩ := tChart_facts (hconf ω) hP.seg htl hW hW0 hWe n
  -- the inverse chart does not see the branch shift
  have hinv : ∀ y ∈ H, pocketInv (shiftLift (c ω) 0) w t y = (tChart (c ω) n W t).2.1 y := hinv'
  have hWγc := Sec7.Lemma71O.continuous_of_isGeneratingTrace_top htrγ
  have hWγ0 : Wγ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrγ (by simp)
  have htpos : ∀ x : ℝ, midL W t < x → x < midR W t → x ≠ 0 → 0 < t := by
    intro x hxL hxR hx0
    obtain ⟨-, -, -, u, hu0, hut, -, -⟩ := hTs.exists_land hxL hxR hx0
    rcases eq_zero_or_pos t with h0 | h0
    · exfalso
      have hd := PocketTraversal.isDrivenCurve_of_isSegCurve hP.seg
      rw [h0, NNReal.coe_zero, hd.capInv_of_nonpos le_rfl] at hut
      linarith
    · exact h0
  have hτ' : ∀ x : ℝ, midL W t < x → x < midR W t → x ≠ 0 →
      capTime G M Y β α γ t ω = (hTs.capT : ℝ≥0∞) := by
    intro x hxL hxR hx0
    have hτ := capTime_eq_visit (G := G) (M := M) (Y := Y) hg hCo hCH (hconf ω) (hdom ω) hγH (hc3 2 ω) hP.seg
      (hMiff ω) (hGeq ω) (hYeq ω) (htpos x hxL hxR hx0) htl
    rw [hτ, ← hTs.capT_eq, ENNReal.ofReal_coe_nnreal]
  -- the common part of the two sides
  have hcommon : ∀ x : ℝ, midL W t < x → x < midR W t → x ≠ 0 →
      ∃ σ : ℝ≥0, 0 < σ ∧ σ < hTs.capT ∧ (x < 0 → γ ω σ ∉ range (β ω)) ∧ (0 < x → γ ω σ ∉ range (α ω)) ∧
        Tendsto (pocketInv (shiftLift (c ω) 0) w t) (𝓝[H] (x : ℂ)) (𝓝 (γ ω σ)) ∧
        Tendsto (tChart (c ω) n W t).2.1 (𝓝[H] (x : ℂ)) (𝓝[H \ range (γ ω)] (γ ω σ)) ∧
        (∀ᶠ y in 𝓝[H] (x : ℂ), pocketInv (shiftLift (c ω) 0) w t y ∉
          explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω) ∧
        ∃ y : ℝ, (x < 0 → y < 0) ∧ (0 < x → 0 < y) ∧
          Tendsto (fun z => fwdMap (fun r : ℝ => Wγ r.toNNReal) hTs.capT ((tChart (c ω) n W t).2.1 z))
            (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) := by
    intro x hxL hxR hx0
    obtain ⟨σ, hσ, hTσ, u, hu0, -, hue, hσu⟩ := hTs.exists_land hxL hxR hx0
    obtain ⟨hσ0, hβ', hα'⟩ := hTs.landing_offWall hoff hxL hxR hx0 ⟨u, hu0, hue, hσu⟩
    have hEq : ∀ᶠ y in 𝓝[H] (x : ℂ), pocketInv (shiftLift (c ω) 0) w t y = (tChart (c ω) n W t).2.1 y :=
      eventually_nhdsWithin_of_forall fun y hy => hinv y hy
    obtain ⟨y, hyL, hyR, hy⟩ := hTs.exists_sign_tendsto htrγ hxL hxR hx0
    refine ⟨σ, hσ0, hσ, hβ', hα', hTσ.congr' (hEq.mono fun y hy => hy.symm),
      hTs.tendsto_nhdsWithin_diff_range hσ hTσ, ?_, y, hyL, hyR, hy⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hinv z hz, Three.explored_threeStops, hτ' x hxL hxR hx0]
    have hD := hTs.inv_mem_dom hz
    have hzC := (hTs.mem_of_mem_dom hD).1
    rintro ⟨((h1 | h1) | ⟨v, hv, hve⟩), -⟩
    · exact (hP.frame.subset_sides hzC).2.1.2 h1
    · exact (hP.frame.subset_sides hzC).1.1.2 h1
    · exact hTs.notMem_prefix_of_mem_dom hD ⟨v, ⟨zero_le, by exact_mod_cast hv⟩, hve⟩
  have hcap : ∀ x : ℝ, midL W t < x → x < midR W t → x ≠ 0 → ∀ σ : ℝ≥0, σ < hTs.capT →
      (σ : ℝ≥0∞) < capTime G M Y β α γ t ω := by
    intro x hxL hxR hx0 σ hσ
    rw [hτ' x hxL hxR hx0]
    exact_mod_cast hσ
  refine ⟨Wγ, htrγ, fun x hxL hx0 => ?_, fun x hx0 hxR => ?_⟩
  · rw [hvL] at hxL
    have hxR : x < midR W t := by linarith [midR_nonneg hW ht0]
    obtain ⟨σ, hσ0, hσ, hβ', -, hTσ, hTσ', hA, y, hyL, -, hy⟩ := hcommon x hxL hxR hx0.ne
    have hside : leftSideOf (range (γ ω)) ∈ map (tChart (c ω) n W t).2.1 (𝓝[H] (x : ℂ)) :=
      Lemma71Q.leftSideOf_mem_of_tendsto_neg hP.hγ hWγc hWγ0 htrγ hσ0 hσ hTσ' (hyL hx0)
        ((tendsto_map'_iff).2 hy)
    refine ⟨σ, hσ0, hcap x hxL hxR hx0.ne σ hσ, hβ' hx0, hTσ, ?_⟩
    filter_upwards [hA, Filter.mem_map.1 hside, self_mem_nhdsWithin] with z hzA hzS hz
    refine ⟨?_, hzA⟩
    rw [hinv z hz]; exact hzS
  · rw [hvR] at hxR
    have hxL : midL W t < x := by linarith [midL_nonpos hW ht0]
    obtain ⟨σ, hσ0, hσ, -, hα', hTσ, hTσ', hA, y, -, hyR, hy⟩ := hcommon x hxL hxR hx0.ne'
    have hside : rightSideOf (range (γ ω)) ∈ map (tChart (c ω) n W t).2.1 (𝓝[H] (x : ℂ)) :=
      Lemma71Q.rightSideOf_mem_of_tendsto_pos hP.hγ hWγc hWγ0 htrγ hσ0 hσ hTσ' (hyR hx0)
        ((tendsto_map'_iff).2 hy)
    refine ⟨σ, hσ0, hcap x hxL hxR hx0.ne' σ hσ, hα' hx0, hTσ, ?_⟩
    filter_upwards [hA, Filter.mem_map.1 hside, self_mem_nhdsWithin] with z hzA hzS hz
    refine ⟨?_, hzA⟩
    rw [hinv z hz]; exact hzS

end Land

/-! ### The middle-line side limits and the fixed-time chamber clause -/

section Named

/-- **(CS) at `κ = 4`: the side limits of the active chamber component along the middle line**
(`ChamberCurveSideStatement`, no input). The side heights are `IsSeedThreeSpace.ae_middleSideHeight`, the seed values
`tendsto_meanHarmonic_left/right` (with `λ = π/√4`), the landing `IsSeedThreeSpace.ae_middleLand`, and the assembly
`pocketCurveSide_of_land_four` (the proof of `chamberCurveSideStatement_of_land`, PROVE-WW-B22, with the landing proved
on seed spaces). -/
theorem chamberCurveSideStatement : ChamberCurveSideStatement.{u} := by
  intro Ω _ P _ rL rR u₁ u₂ h u₀ β α γ hS C c γ' hpc G M Y _ _ _ hMiff hGeq hYeq t gL hgL
  have hT : IsThreeLineSpace P h u₀ β α γ := hS.2.2.2.2.2.2.1
  have hland := hS.ae_middleLand hpc hMiff hGeq hYeq t
  have hMS := hS.ae_middleSideHeight hgL
  have hT' := hT
  obtain ⟨-, -, -, -, -, -, hae⟩ := hT'
  have hpc' := hpc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsegc, -⟩ := hpc'
  have hlam : sleLambda 4 = wwLambda := SeedField.sleLambda_four
  filter_upwards [hland, hMS, hae] with ω hlω hMω hω htl vL hvL hvLr
  obtain ⟨W, hWtr, hlL, hlR⟩ := hlω htl
  obtain ⟨-, -, -, hsγ, -⟩ := hω
  have hMω' := hMω W hWtr vL hvL hvLr
  have hWc : Continuous W := continuousOn_univ.1 ((SideHeight.continuousOn_of_isGeneratingTrace hWtr).mono
    fun s _ => show (s : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hW0 : W 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace hWtr (by simp)
  set w : ℝ≥0 → ℝ := fun s => segDriver (γ' ω) s with hwdef
  set vLf : Fin 1 → ℝ≥0 → ℝ := fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω with hvLfdef
  set vRf : Fin 1 → ℝ≥0 → ℝ := fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω with hvRfdef
  have hvL' : vLf 0 t = -RealFlow.rightImg (fun s => -Ito.rpath (fun s => segDriver (γ' ω) s) s) 0 t := by
    simp only [hvLfdef, geomL, LP.twoSeedXL, neg_zero]
    rfl
  have hvR' : vRf 0 t = RealFlow.rightImg (Ito.rpath fun s => segDriver (γ' ω) s) 0 t := by
    simp only [hvRfdef, geomR, LP.twoSeedXR]
    rfl
  obtain ⟨hsL, hsR⟩ := seed_sub_driver (hsegc ω) htl hvL' hvR'
  have e1 : (fun i : Fin 1 => vLf i t - w t) = fun _ => vLf 0 t - segDriver (γ' ω) t := by
    funext i; rw [Subsingleton.elim i 0]
  have e2 : (fun i : Fin 1 => vRf i t - w t) = fun _ => vRf 0 t - segDriver (γ' ω) t := by
    funext i; rw [Subsingleton.elim i 0]
  have hG : pocketG 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2) w vLf vRf t 0 =
      Ito.meanHarmonic 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2)
        (fun _ => vLf 0 t - segDriver (γ' ω) t) (fun _ => vRf 0 t - segDriver (γ' ω) t) := by
    funext y
    unfold Lemma71M.pocketG
    rw [e1, e2, sub_zero]
  have hGL : ∀ x : ℝ, vLf 0 t - segDriver (γ' ω) t < x → x < 0 →
      Tendsto (pocketG 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2) w vLf vRf t 0)
        (𝓝[H] (x : ℂ)) (𝓝 (-wwLambda)) := by
    intro x hxL hx0
    have h1 := tendsto_meanHarmonic_left 4 (fun _ : Fin 1 => u₂ / wwLambda - 2)
      (fun _ : Fin 1 => -u₁ / wwLambda - 2) hxL hx0 hsR
    rw [hlam] at h1
    rw [hG]
    exact h1
  have hGR : ∀ x : ℝ, 0 < x → x < vRf 0 t - segDriver (γ' ω) t →
      Tendsto (pocketG 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2) w vLf vRf t 0)
        (𝓝[H] (x : ℂ)) (𝓝 wwLambda) := by
    intro x hx0 hxR
    have h1 := tendsto_meanHarmonic_right 4 (fun _ : Fin 1 => u₂ / wwLambda - 2)
      (fun _ : Fin 1 => -u₁ / wwLambda - 2) hsL hx0 hxR
    rw [hlam] at h1
    rw [hG]
    exact h1
  exact pocketCurveSide_of_land_four hsγ hWc hW0 hWtr
    (Three.explored_threeStops β α γ (capTime G M Y β α γ t) ω) (Three.explored_threeTop β α γ ω) hMω' hGL hGR
    (pocketLift (shiftLift (c ω) 0) w t) hlL hlR

/-- **(J5) at `κ = 4`: WW-B23's fixed-time chamber clause** (`ChamberCond.ChamberClauseStatement`, no input): on every
seed three-line space, the chamber construction `exists_isPocketConstruction_three` with lift shift `0`, `a = 0`,
`k = χ(4)` satisfies the chart coupling clause of the seed word `(u₂/λ − 2; −u₁/λ − 2)` at every deterministic capacity
time on `{t < capLife}` (`chamberClauseStatement_of_curveSide`, `chamberCurveSideStatement`). -/
theorem chamberClauseStatement : ChamberCond.ChamberClauseStatement.{u} :=
  chamberClauseStatement_of_curveSide chamberCurveSideStatement

end Named

end InteractingSLE.WangWu.SeedThree
