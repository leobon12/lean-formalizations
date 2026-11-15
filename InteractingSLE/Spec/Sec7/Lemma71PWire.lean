/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71POrient
import InteractingSLE.Spec.Sec7.Lemma71PMain
import InteractingSLE.Spec.Sec7.Lemma71QCurve

/-!
# Lemma 7.1's (CS): PROVE-LEMMA71Q's geometric interface from one deterministic Loewner fact

Packet PROVE-LEMMA71P. PROVE-LEMMA71Q reduced (CS) `Lemma71N.PocketCurveSideStatement` (and Lemma 7.1's
`IsPocketChartData`, `Lemma72E.PocketClauseStatement`, `Lemma72.Lemma71JointStatement`) to its geometric input
`Lemma71Q.MiddleLandingStatement`. This file proves that input from the results of this packet (CS-a, CS-branch, the
side of approach `IsTSetting.exists_sign_tendsto`) and **one named deterministic fact about simple Loewner traces**:

* `MidRealOffStatement`: for a continuous Loewner trace `η` injective on `[0, t]`, the boundary extension `F̄_t` of
  `f_t⁻¹` takes no real value `≤ 0` on the left middle interval `(L_t − W_t, 0)` and no real value `≥ 0` on the right
  middle interval `(0, R_t − W_t)` (the left boundary arc of the hull meets the closed negative half-line only at its
  end `F̄_t(L_t − W_t)`, the right one meets the closed positive half-line only at `F̄_t(R_t − W_t)`).

It gives the two facts of `MiddleLanding` not covered by CS-a/CS-branch/orientation: the landing time is positive,
and the landing point is off the left wall on the left interval (off the right wall on the right interval).

Main result: **`middleLandingStatement_of_midRealOff`**. With `Lemma71Q.pocketCurveSideStatement_of_middleLanding`
this gives (CS) from `MidRealOffStatement` and the §4.2 reference.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71P

open QuantumZipper (H Hbar chiC fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71C Lemma71K Lemma71L Sec6 LocalSets
open MartChar Lemma71M Lemma71E Lemma71D Coupling Lemma71G
open Lemma71N (IsPocketFrame IsPocketBranch)
open Lemma71O (land)

/-- **Named input: the middle boundary arcs of a simple Loewner hull meet the real line only on the far side.** For a
continuous driver `W` (`W 0 = 0`) with a Loewner trace `η` injective on `[0, t]`, the boundary extension `F̄_t` of
`f_t⁻¹` takes no real value `≤ 0` at the chart points of `(L_t − W_t, 0)` and no real value `≥ 0` at those of
`(0, R_t − W_t)`. -/
def MidRealOffStatement : Prop :=
  ∀ (W : ℝ → ℝ) (η : ℝ → ℂ) (t : ℝ), Continuous W → W 0 = 0 → 0 ≤ t → IsLoewnerTrace W η → InjOn η (Icc 0 t) →
    (∀ x : ℝ, midL W t < x → x < 0 →
      ¬ ((extendFrom H (fwdMapInv W t) x).im = 0 ∧ (extendFrom H (fwdMapInv W t) x).re ≤ 0)) ∧
    (∀ x : ℝ, 0 < x → x < midR W t →
      ¬ ((extendFrom H (fwdMapInv W t) x).im = 0 ∧ 0 ≤ (extendFrom H (fwdMapInv W t) x).re))

namespace IsTSetting

variable {β α γ : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {γ' : ℝ → ℂ} {κ : ℝ → ℝ} {n : ℤ}
  {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ≥0}

theorem injOn_η (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) : InjOn η (Icc 0 (t : ℝ)) := fun s hs s' hs' h => by
  rw [hS.hηe s hs.1 hs.2, hS.hηe s' hs'.1 hs'.2] at h
  exact injOn_capInv hS.seg.seg hS.ht hs hs' h

/-- **The landing point at a middle chart point is off the wall on the same side, at a positive time**, given
`MidRealOffStatement`: on the left interval it is off `β`, on the right interval off `α`. -/
theorem landing_offWall (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) (hoff : MidRealOffStatement) {x : ℝ}
    (hxL : midL W t < x) (hxR : x < midR W t) (hx0 : x ≠ 0) {σ : ℝ≥0} (hu : ∃ u : ℝ, 0 ≤ u ∧
      extendFrom H (fwdMapInv W t) x = γ' u ∧ σ = (κ u).toNNReal) :
    0 < σ ∧ (x < 0 → γ σ ∉ range β) ∧ (0 < x → γ σ ∉ range α) := by
  obtain ⟨u, hu0, hue, hσ⟩ := hu
  have hF := hS.seg.frame
  obtain ⟨hoffL, hoffR⟩ := hoff W η t hS.hW hS.hW0 t.coe_nonneg hS.hη hS.injOn_η
  have hnotreal : ¬ ((extendFrom H (fwdMapInv W t) x).im = 0 ∧ (extendFrom H (fwdMapInv W t) x).re = 0) := by
    rcases lt_or_gt_of_ne hx0 with h | h
    · exact fun h' => hoffL x hxL h ⟨h'.1, h'.2.le⟩
    · exact fun h' => hoffR x h hxR ⟨h'.1, h'.2.ge⟩
  have hu0' : 0 < u := by
    refine lt_of_le_of_ne hu0 fun h => hnotreal ?_
    rw [hue, ← h, hS.seg.seg.2.2.2.1]; simp
  have hσ0 : 0 < σ := by
    rw [hσ]
    exact Real.toNNReal_pos.2 (lt_of_le_of_lt hS.seg.hκ0 (hS.seg.hκ self_mem_Ici hu0'.le hu0'))
  have hland : γ σ = land c (extendFrom H (fwdMapInv W t) x) := by rw [hσ, hue, hS.seg.land_seg hu0]
  have hFx := extendFrom_mem_Hbar hS.hη hS.hW hS.hW0 t.coe_nonneg (mem_Hbar_of_im_eq_zero (z := ((x : ℝ) : ℂ))
    (by simp))
  have hC : extendFrom H (fwdMapInv W t) x ∈ H → land c (extendFrom H (fwdMapInv W t) x) ∈ C := fun hH => by
    rw [show land c (extendFrom H (fwdMapInv W t) x) = c.2.1 (extendFrom H (fwdMapInv W t) x) from
      extendFrom_extends hF.hc.1.continuousOn _ hH, ← hF.hdom]
    exact hF.hc.inv_mem_dom hH
  refine ⟨hσ0, fun hneg => ?_, fun hpos => ?_⟩
  · rw [hland]
    rcases (show (0 : ℝ) ≤ (extendFrom H (fwdMapInv W t) x).im from hFx).eq_or_lt with him | hH
    · have hre : 0 < (extendFrom H (fwdMapInv W t) x).re := by
        by_contra hle
        exact hoffL x hxL hneg ⟨him.symm, not_lt.1 hle⟩
      have hreal : extendFrom H (fwdMapInv W t) x = (((extendFrom H (fwdMapInv W t) x).re : ℝ) : ℂ) :=
        eq_ofReal_re_of_im_eq_zero him.symm
      obtain ⟨s', -, hs'β, hs'⟩ := Lemma71O.PocketFrame.land_ofReal_pos hF hre
      rw [hreal, hs']
      exact hs'β
    · exact (hF.subset_sides (hC hH)).2.1.2
  · rw [hland]
    rcases (show (0 : ℝ) ≤ (extendFrom H (fwdMapInv W t) x).im from hFx).eq_or_lt with him | hH
    · have hre : (extendFrom H (fwdMapInv W t) x).re < 0 := by
        by_contra hle
        exact hoffR x hpos hxR ⟨him.symm, not_lt.1 hle⟩
      have hreal : extendFrom H (fwdMapInv W t) x = (((extendFrom H (fwdMapInv W t) x).re : ℝ) : ℂ) :=
        eq_ofReal_re_of_im_eq_zero him.symm
      obtain ⟨s', -, hs'α, hs'⟩ := Lemma71O.PocketFrame.land_ofReal_neg hF hre
      rw [hreal, hs']
      exact hs'α
    · exact (hF.subset_sides (hC hH)).1.1.2

/-- Near a landing point `γ σ` strictly before the capacity stop, the inverse chart of the active component stays
off the complete middle curve. -/
theorem tendsto_nhdsWithin_diff_range (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {x : ℝ} {σ : ℝ≥0}
    (hσ : σ < hS.capT) (hT : Tendsto (tChart c n W t).2.1 (𝓝[H] (x : ℂ)) (𝓝 (γ σ))) :
    Tendsto (tChart c n W t).2.1 (𝓝[H] (x : ℂ)) (𝓝[H \ range γ] (γ σ)) := by
  obtain ⟨ρ, hρ, hball⟩ := Lemma71N.exists_ball_tail hS.seg.hγ hσ
  refine tendsto_nhdsWithin_iff.2 ⟨hT, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hT (ball_mem_nhds _ hρ)] with y hy hyb
  have hD := hS.inv_mem_dom hy
  refine ⟨hS.seg.frame.subset_H (hS.mem_of_mem_dom hD).1, ?_⟩
  rintro ⟨v, hv⟩
  rcases le_or_gt hS.capT v with hle | hlt
  · exact hball v hle (by rw [hv]; exact hyb)
  · exact hS.notMem_prefix_of_mem_dom hD ⟨v, ⟨zero_le, hlt.le⟩, hv⟩

end IsTSetting

/-- **PROVE-LEMMA71Q's geometric input from `MidRealOffStatement`**: `Lemma71Q.MiddleLandingStatement` (CS-a, the side
of approach, the landing off the same-side wall at a positive time, and CS-branch, at every middle chart point). -/
theorem middleLandingStatement_of_midRealOff (hoff : MidRealOffStatement) : Lemma71Q.MiddleLandingStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb Ω _ P _ h u₀ β α γ ζβ ζα ζγ hS C c γ' hpc G M Y hG hM hY hMiff hGeq hYeq
    n hn hN t
  have hS' := hS
  obtain ⟨-, -, -, hβfl, hαfl, hγfl, hβ62, hα62, hγ62, hae⟩ := hS'
  obtain ⟨hc3, -, him3, -, -, -, -⟩ := Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, -, -, -, -, -⟩ := hpc'
  have hζβ : ∀ᵐ ω ∂P, ζβ ω = ⊤ := hae.mono fun ω hω => hω.1
  have hζα : ∀ᵐ ω ∂P, ζα ω = ⊤ := hae.mono fun ω hω => hω.2.1
  have hζγ : ∀ᵐ ω ∂P, ζγ ω = ⊤ := hae.mono fun ω hω => hω.2.2.1
  filter_upwards [ae_isPocketSeg hS hpc, hN, ae_exists_isGeneratingTrace hβfl hζβ,
    ae_exists_isGeneratingTrace hαfl hζα, ae_exists_isGeneratingTrace hγfl hζγ] with ω ⟨hg, a', b', Ψ, hP⟩ hNω
    ⟨Wβ, htrβ⟩ ⟨Wα, htrα⟩ ⟨Wγ, htrγ⟩ htl
  set w : ℝ≥0 → ℝ := fun s => segDriver (γ' ω) s with hwdef
  have hCo : IsOpen (C ω) := (hC ω).1
  have hCH : C ω ⊆ H := (hC ω).2.2.2
  have hγH : ∀ t, γ ω t ∈ Hbar := fun t => him3 2 ω t
  obtain ⟨W, hW, hW0, hWe, η, hη, hηe⟩ := exists_loewnerTrace hP.seg htl
  have hT : IsTSetting (β ω) (α ω) (γ ω) (C ω) (c ω) Ψ a' b' (γ' ω)
      (visitClock (γ ω) (closure (cayley '' C ω))) (n ω) W η t := ⟨hP, hNω, htl, hW, hW0, hWe, hη, hηe⟩
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
  have hmL := midL_nonpos hW ht0
  have hmR := midR_nonneg hW ht0
  obtain ⟨-, -, hinv, -⟩ := tChart_facts (hconf ω) hP.seg htl hW hW0 hWe (n ω)
  have hWγc := Lemma71O.continuous_of_isGeneratingTrace_top htrγ
  have hWγ0 : Wγ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrγ (by simp)
  -- the common part of the two sides
  have hcommon : ∀ x : ℝ, midL W t < x → x < midR W t → x ≠ 0 →
      ∃ σ : ℝ≥0, 0 < σ ∧ σ < hT.capT ∧ (x < 0 → γ ω σ ∉ range (β ω)) ∧ (0 < x → γ ω σ ∉ range (α ω)) ∧
        Tendsto (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t) (𝓝[H] (x : ℂ))
          (𝓝 (γ ω σ)) ∧
        Tendsto (tChart (c ω) (n ω) W t).2.1 (𝓝[H] (x : ℂ)) (𝓝[H \ range (γ ω)] (γ ω σ)) ∧
        (∀ᶠ y in 𝓝[H] (x : ℂ), pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t y ∉
          explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω) ∧
        ∃ y : ℝ, (x < 0 → y < 0) ∧ (0 < x → 0 < y) ∧
          Tendsto (fun z => fwdMap (fun r : ℝ => Wγ r.toNNReal) hT.capT
            (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t z)) (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) := by
    intro x hxL hxR hx0
    obtain ⟨σ, hσ, hTσ, u, hu0, hut, hue, hσu⟩ := hT.exists_land hxL hxR hx0
    obtain ⟨hσ0, hβ', hα'⟩ := hT.landing_offWall hoff hxL hxR hx0 ⟨u, hu0, hue, hσu⟩
    have htpos : 0 < t := by
      rcases eq_zero_or_pos t with h0 | h0
      · exfalso
        have hd := PocketTraversal.isDrivenCurve_of_isSegCurve hP.seg
        rw [h0, NNReal.coe_zero, hd.capInv_of_nonpos le_rfl] at hut
        linarith
      · exact h0
    have hτ := capTime_eq_visit (G := G) (M := M) (Y := Y) hg hCo hCH (hconf ω) (hdom ω) hγH (hc3 2 ω) hP.seg
      (hMiff ω) (hGeq ω) (hYeq ω) htpos htl
    have hτ' : capTime G M Y β α γ t ω = (hT.capT : ℝ≥0∞) := by
      rw [hτ, ← hT.capT_eq, ENNReal.ofReal_coe_nnreal]
    have hEq : ∀ᶠ y in 𝓝[H] (x : ℂ),
        pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t y = (tChart (c ω) (n ω) W t).2.1 y :=
      eventually_nhdsWithin_of_forall fun y hy => hinv y hy
    obtain ⟨y, hyL, hyR, hy⟩ := hT.exists_sign_tendsto htrγ hxL hxR hx0
    refine ⟨σ, hσ0, hσ, hβ', hα', hTσ.congr' (hEq.mono fun y hy => hy.symm),
      hT.tendsto_nhdsWithin_diff_range hσ hTσ, ?_, y, hyL, hyR, hy.congr' (hEq.mono fun z hz => by
        show _ = fwdMap (fun r : ℝ => Wγ r.toNNReal) hT.capT
          (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t z)
        rw [hz])⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hinv z hz, Three.explored_threeStops, hτ']
    have hD := hT.inv_mem_dom hz
    have hzC := (hT.mem_of_mem_dom hD).1
    rintro ⟨((h1 | h1) | ⟨v, hv, hve⟩), -⟩
    · exact (hP.frame.subset_sides hzC).2.1.2 h1
    · exact (hP.frame.subset_sides hzC).1.1.2 h1
    · exact hT.notMem_prefix_of_mem_dom hD ⟨v, ⟨zero_le, by exact_mod_cast hv⟩, hve⟩
  have hcap : ∀ x : ℝ, midL W t < x → x < midR W t → x ≠ 0 → ∀ σ : ℝ≥0, σ < hT.capT →
      (σ : ℝ≥0∞) < capTime G M Y β α γ t ω := by
    intro x hxL hxR hx0 σ hσ
    obtain ⟨-, -, -, u, -, hut, -, -⟩ := hT.exists_land hxL hxR hx0
    have htpos : 0 < t := by
      rcases eq_zero_or_pos t with h0 | h0
      · exfalso
        have hd := PocketTraversal.isDrivenCurve_of_isSegCurve hP.seg
        rw [h0, NNReal.coe_zero, hd.capInv_of_nonpos le_rfl] at hut
        obtain ⟨-, -, -, u', hu', hut', -⟩ := hT.exists_land hxL hxR hx0
        rw [h0, NNReal.coe_zero, hd.capInv_of_nonpos le_rfl] at hut'
        linarith
      · exact h0
    have hτ := capTime_eq_visit (G := G) (M := M) (Y := Y) hg hCo hCH (hconf ω) (hdom ω) hγH (hc3 2 ω) hP.seg
      (hMiff ω) (hGeq ω) (hYeq ω) htpos htl
    rw [hτ, ← hT.capT_eq, ENNReal.ofReal_coe_nnreal]
    exact_mod_cast hσ
  refine ⟨Wγ, htrγ, fun x hxL hx0 => ?_, fun x hx0 hxR => ?_⟩
  · rw [hvL] at hxL
    have hxR : x < midR W t := by linarith
    obtain ⟨σ, hσ0, hσ, hβ', -, hTσ, hTσ', hA, y, hyL, -, hy⟩ := hcommon x hxL hxR hx0.ne
    have hS : leftSideOf (range (γ ω)) ∈ map (tChart (c ω) (n ω) W t).2.1 (𝓝[H] (x : ℂ)) :=
      Lemma71Q.leftSideOf_mem_of_tendsto_neg hP.hγ hWγc hWγ0 htrγ hσ0 hσ hTσ' (hyL hx0)
        ((tendsto_map'_iff).2 (hy.congr' (eventually_nhdsWithin_of_forall fun z hz => by
          simp only [Function.comp_apply]; rw [hinv z hz])))
    refine ⟨σ, hσ0, hcap x hxL hxR hx0.ne σ hσ, hβ' hx0, hTσ, ?_, hT.capT, hσ,
      hT.tendsto_pocketLift_sub htrβ htrα htrγ hxL hxR hx0.ne hTσ hσ le_rfl⟩
    filter_upwards [hA, Filter.mem_map.1 hS, self_mem_nhdsWithin] with z hzA hzS hz
    refine ⟨?_, hzA⟩
    rw [hinv z hz]; exact hzS
  · rw [hvR] at hxR
    have hxL : midL W t < x := by linarith
    obtain ⟨σ, hσ0, hσ, -, hα', hTσ, hTσ', hA, y, -, hyR, hy⟩ := hcommon x hxL hxR hx0.ne'
    have hS : rightSideOf (range (γ ω)) ∈ map (tChart (c ω) (n ω) W t).2.1 (𝓝[H] (x : ℂ)) :=
      Lemma71Q.rightSideOf_mem_of_tendsto_pos hP.hγ hWγc hWγ0 htrγ hσ0 hσ hTσ' (hyR hx0)
        ((tendsto_map'_iff).2 (hy.congr' (eventually_nhdsWithin_of_forall fun z hz => by
          simp only [Function.comp_apply]; rw [hinv z hz])))
    refine ⟨σ, hσ0, hcap x hxL hxR hx0.ne' σ hσ, hα' hx0, hTσ, ?_, hT.capT, hσ,
      hT.tendsto_pocketLift_sub htrβ htrα htrγ hxL hxR hx0.ne' hTσ hσ le_rfl⟩
    filter_upwards [hA, Filter.mem_map.1 hS, self_mem_nhdsWithin] with z hzA hzS hz
    refine ⟨?_, hzA⟩
    rw [hinv z hz]; exact hzS

end InteractingSLE.Sec7.Lemma71P
