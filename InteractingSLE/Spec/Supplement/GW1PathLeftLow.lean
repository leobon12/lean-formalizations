/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PathKernel
import InteractingSLE.Spec.Sec7.R7OuterReflect

/-!
# GW1's retargeting: the high connector after a completed piece of the left walk

Packet PROVE-GW1-PATH. The left mirror of `GW1PathLow` and of the visit lemma of `GW1PathKernel`:

* `connector_left`: the boundary continuation after a completed piece of the left walk moves left from `q` to the
  first earlier original jump `w` with low inward height; the data are high on `(w, q)` (`λ ≤ b + θχ`);
* `fn_high_of_lOrig`: a word original left of the left record is high on `(v, 0)`, `v = rProf d w < 0`;
* `ae_visit_of_high_neg`: a centred counterflow visits every `v < 0` above which its word is high: by reflection
  (`σ(z) = −z̄`, `R7Outer.isCenteredCounterflowDriver_reflect`, `FlowReflect.IsGFFWithBoundaryData.reflect`) it is
  `ae_visit_of_low` at `−v > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Path

open Exist Exist.StagedLaw Exist.Staged Restart GW1W GW1WalkExit GW1WalkFinish
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

section Connector

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The connector after a completed piece of the left walk followed by another launch** (mirror of
`connector_right`). -/
theorem connector_left (hb : IsPiecewiseConstantBoundaryData b jumps) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (2 * n + 1)).2.2.2.1 (2 * n) ≠ none)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (2 * (n + 1) + 1)).2.2.2.1
      (2 * (n + 1)) ≠ none)
    (hC : ClassifiedExit κ b false (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (2 * n))
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (2 * n + 1)))
    (hang : stAngle (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (2 * n + 1)) = θ) :
    let s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (2 * n + 1)
    let s₂ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (2 * (n + 1))
    stPt s₂ < stPt s₁ ∧
      (∀ x, stPt s₂ < x → x < stPt s₁ → x ∉ jumps → sleLambda κ ≤ b x + θ * chiC κ) ∧
      stChart s₂ = (stChart s₁).recenter (rProf (stChart s₁) (stPt s₂)) ∧
      s₂.2.1 = s₁.2.1 ++ [Icc (stPt s₂) (stPt s₁)] := by
  intro s₁ s₂
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D with hRdef
  have hn : ∀ j, 2 * n < j → j < 2 * (n + 1) → (R (j + 1)).2.2.2.1 j = none := by
    intro j hj1 hj2
    have hj : j = 2 * n + 1 := by omega
    subst hj
    exact GW1RestartPair.noLaunch_walk_odd D n
  obtain ⟨-, hrunk, r, hstk⟩ := run_eq_of_last_launch (by omega) hk hl hn
  change stStatus (R (2 * (n + 1))) = stArcM r at hstk
  have hnd : stStatus s₁ ≠ stDone := by
    intro hd
    have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) s₁ false (Or.inr (Or.inl hd))
    change R (2 * (n + 1)) = _ at hrunk
    rw [this] at hrunk
    rw [hrunk] at hstk
    change stStatus s₁ = _ at hstk
    rw [hd] at hstk
    exact absurd hstk (by simp [stArcM])
  have hOut : OutwardThreshold κ b false s₁ := by
    rcases hC.1 with hd | ⟨-, ho⟩
    · exact absurd hd hnd
    · exact ho
  have hBad : sleLambda κ ≤ leftLim b (stPt s₁) + stAngle s₁ * chiC κ := by
    have h := hC.2 hnd
    simpa only [BadOutwardHeight, Bool.false_eq_true, ite_false] using h
  have heq : ExplState.contStep κ b jumps s₁ none false =
      if hC : (restartSetL κ b jumps s₁).Nonempty then
        ExplState.moveAlong s₁ false ((restartSetL κ b jumps s₁).max' hC) true else ExplState.moveToEnd s₁ false := by
    rcases hOut with h | ⟨h, hR, hL⟩
    · exact contStep_thr_false b jumps s₁ h false
    · exact contStep_thr_none_left b jumps s₁ h hR hL
  change R (2 * (n + 1)) = ExplState.contStep κ b jumps s₁ none false at hrunk
  rw [heq] at hrunk
  split_ifs at hrunk with hCne
  swap
  · exfalso
    rw [hrunk] at hstk
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    exact absurd hstk (by simp [ExplState.moveToEnd, stStatus, stArcM])
  set w := (restartSetL κ b jumps s₁).max' hCne with hw
  have hmem := Finset.mem_filter.1 (Finset.max'_mem _ hCne)
  have hwp : w < stPt s₁ := hmem.2.1
  have hs₂ : s₂ = ExplState.moveAlong s₁ false w true := hrunk
  have hpt₂ : stPt s₂ = w := by rw [hs₂, stPt_moveAlong]
  refine ⟨hpt₂ ▸ hwp, ?_, ?_, ?_⟩
  · intro x hx hxq hxJ
    rw [hpt₂] at hx
    rw [← hang]
    refine le_add_of_connector hb hBad (fun z hz hwz hzq => ?_) hx hxq hxJ
    by_contra hlt
    push Not at hlt
    have hz' : z ∈ restartSetL κ b jumps s₁ := Finset.mem_filter.2 ⟨hz, hzq, hlt⟩
    exact absurd ((restartSetL κ b jumps s₁).le_max' z hz') (not_le.2 hwz)
  · rw [hs₂, stChart_moveAlong, stPt_moveAlong]
    rfl
  · rw [hs₂, stPt_moveAlong]
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    rfl

end Connector

section High

/-- **A word original left of the left record is high on `(rProf w, 0)`** when the original data are high on
`(w, stRecL s)` (deterministic mirror of `fn_low_of_rOrig`). -/
theorem fn_high_of_lOrig {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {β : BoundaryWord} {s : ExplState}
    (hP : LProf s) (hO : LOrig b jumps β s) {w : ℝ} (hw : w < stRecL s)
    (hhigh : ∀ x, w < x → x < stRecL s → x ∉ jumps → sleLambda κ ≤ b x + θ * chiC κ) :
    ∀ y, rProf (stChart s) w < y → y < 0 → y ∉ β.jumps → sleLambda κ ≤ β.fn y + θ * chiC κ := by
  intro y hwy hy hyJ
  obtain ⟨x₀, hx₀, hxy⟩ := hP.exists_eq (neg_pos.2 hy)
  set g := lProf (stChart s) with hg
  have hgr : ∀ x, rProf (stChart s) (-x) = -g x := fun x => by
    rw [hg, GW1W.lProf_eq, neg_neg]
  have hrw : rProf (stChart s) w = -g (-w) := by
    have := hgr (-w)
    rwa [neg_neg] at this
  have hx₀w : x₀ < -w := by
    by_contra hge
    push Not at hge
    rcases hge.eq_or_lt with he | hlt
    · rw [hrw, he, hxy] at hwy
      linarith
    · have hd : -stRecL s < -w := by linarith
      have h1 : g (-w) < g x₀ := hP.2.1.1 hd hx₀ hlt
      rw [hxy] at h1
      rw [hrw] at hwy
      linarith
  have hloc : ∀ᶠ z in 𝓝 (-y), β.fn (-z) = β.fn y := by
    have h1 : ∀ᶠ z in 𝓝 y, β.fn z = β.fn y := β.isPiecewiseConstantBoundaryData y hyJ
    have h2 : Tendsto (fun z : ℝ => -z) (𝓝 (-y)) (𝓝 y) := by
      simpa using (continuous_neg.tendsto (-y))
    exact h2.eventually h1
  have hcont : ContinuousAt g x₀ := hP.2.1.2.1.continuousAt (Ioi_mem_nhds hx₀)
  have hev : ∀ᶠ x in 𝓝 x₀, -stRecL s < x ∧ x < -w ∧ β.fn (-g x) = β.fn y := by
    refine (eventually_gt_nhds hx₀).and ((eventually_lt_nhds hx₀w).and ?_)
    have hloc' : ∀ᶠ z in 𝓝 (g x₀), β.fn (-z) = β.fn y := by rw [hxy]; exact hloc
    exact hcont.eventually hloc'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set T : Set ℝ := {x | -stRecL s < x ∧ -g x ∈ β.jumps} with hTdef
  have hT : T.Finite := by
    have hJn : ((β.jumps.image fun z => -z : Finset ℝ) : Set ℝ).Finite := Finset.finite_toSet _
    refine Set.Finite.of_finite_image (hJn.subset ?_) (hP.2.1.1.injOn.mono fun x hx => hx.1)
    rintro _ ⟨x, hx, rfl⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨-g x, hx.2, neg_neg _⟩
  have hbad : (((jumps.image fun z => -z : Finset ℝ) : Set ℝ) ∪ T).Finite :=
    (Finset.finite_toSet _).union hT
  obtain ⟨x, hxI, hxbad⟩ := ((Set.Ioo_infinite (by linarith : x₀ < x₀ + ε)).sdiff hbad).nonempty
  have hdist : dist x x₀ < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hxI.1, hxI.2]
  obtain ⟨hxR, hxw, hfx⟩ := hball hdist
  have hxJ : -x ∉ jumps := fun h => hxbad (Or.inl (by
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨-x, h, neg_neg x⟩))
  have hmJ : rProf (stChart s) (-x) ∉ β.jumps := by
    rw [hgr]
    exact fun h => hxbad (Or.inr ⟨hxR, h⟩)
  have hxL : -x < stRecL s := by linarith
  have hO' := hO (-x) hxL hxJ hmJ
  rw [hgr] at hO'
  rw [← hfx, hO']
  exact hhigh (-x) (by linarith) hxL hxJ

end High

section Visit

/-- The tip of the reflected counterflow at `−v` is the tip of the counterflow at `v` (algebra of `σ(z) = −z̄`). -/
theorem ofReal_eq_neg_inv_of_reflect {z : ℂ} {v : ℝ} (h : (((-v : ℝ)) : ℂ) = -(LP.reflectC z)⁻¹) :
    (v : ℂ) = -z⁻¹ := by
  have h1 : (starRingEnd ℂ) z = ((((-v : ℝ)) : ℂ))⁻¹ := by
    rw [h]
    simp [LP.reflectC, inv_neg, neg_neg, inv_inv]
  have h2 : z = ((((-v : ℝ)) : ℂ))⁻¹ := by
    have := congrArg (starRingEnd ℂ) h1
    rw [Complex.conj_conj] at this
    rw [this, map_inv₀, Complex.conj_ofReal]
  rw [h2, inv_inv]
  push_cast
  ring

/-- **A centred counterflow visits every `v < 0` above which its word is high** (angle `π/2`): the reflection of
`ae_visit_of_low`. -/
theorem ae_visit_of_high_neg (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {γ : BoundaryWord} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData μ h γ.fn γ.jumps)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ μ h W ζ) (hζ : ∀ᵐ ω ∂μ, ζ ω = ⊤)
    {v : ℝ} (hv0 : v < 0)
    (hhigh : ∀ y, v < y → y < 0 → y ∉ γ.jumps → sleLambda κ ≤ γ.fn y + Real.pi / 2 * chiC κ) :
    ∀ᵐ ω ∂μ, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W t ω) ⊤ := by
  -- the reflected word
  obtain ⟨γ', hγ'⟩ := Restart.BoundaryWord.exists_fn_eq
    (Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData γ.isPiecewiseConstantBoundaryData)
  have hh' : IsGFFWithBoundaryData μ (fun ω => Sec7.FlowReflect.reflField (h ω)) γ'.fn γ'.jumps := by
    have h1 := Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hh
    rw [hγ'.1]
    exact (Restart.isGFFWithBoundaryData_congr μ _
      (S := ((Sec7.FlowReflect.reflJumps γ.jumps : Finset ℝ) : Set ℝ)) fun y hy => hγ'.2 y hy).2 h1
  have hcf' := Sec7.R7Outer.isCenteredCounterflowDriver_reflect hκ hcf
  have hlow : ∀ y, 0 < y → y < -v → y ∉ γ'.jumps →
      γ'.fn y + -(Real.pi / 2) * chiC κ ≤ -sleLambda κ := by
    intro y hy hyv hyJ
    have hyJ' : y ∉ Sec7.FlowReflect.reflJumps γ.jumps := by rwa [← hγ'.1]
    rw [hγ'.2 y hyJ']
    rw [Sec7.FlowReflect.mem_reflJumps] at hyJ'
    have := hhigh (-y) (by linarith) (by linarith) hyJ'
    simp only [Sec7.FlowReflect.reflData]
    linarith
  have hvis := ae_visit_of_low hT13 hT13₀ hκ hκ4 hh' hcf' hζ (neg_pos.2 hv0) hlow
  -- back through the reflection
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hk : 0 < 16 / κ := by positivity
  have htr := GW2aSingle.ae_chosenTrace hT13 hk hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  filter_upwards [hvis, htr, hζ, hdrv] with ω hω hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  have hγr : IsGeneratingTrace (fun t => (-W) t ω) ⊤
      (fun t => LP.reflectC (GW2aSingle.chosenTrace W ζ ω t)) := LP.isGeneratingTrace_reflect hγω.1
  have hWc' : Continuous fun t => (-W) t ω := hWc.neg
  have hW0' : (-W) 0 ω = 0 := by simp only [Pi.neg_apply, hdω.1, neg_zero]
  rw [CounterflowRange.tipSet_infinitySourceChart_top hγr hWc' hW0'] at hω
  rw [CounterflowRange.tipSet_infinitySourceChart_top hγω.1 hWc hdω.1]
  obtain ⟨t, ht0, hte⟩ := hω
  exact ⟨t, fun h0 => ht0 (by rw [h0]; simp [LP.reflectC]), ofReal_eq_neg_inv_of_reflect hte⟩

end Visit

end InteractingSLE.Theorem14.GW1Path
