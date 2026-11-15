/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfJl
import InteractingSLE.Spec.Supplement.SB2WfJp
import InteractingSLE.Spec.Supplement.G12RemSwallow

/-!
# The junction invariant through a launch, from the walk's invariants and three facts about the piece

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). `jw_launch_full` discharges the hypotheses of `jw_launch`
from round 2's invariants (`OW`, `RProf`, `ROrig` before and after the launch, `LLeft`, `stRecL ≤ 0 ≤ stRecR`) and three
facts about the launched piece in its chart (word `β`, angle `θ`):

* `hseed`: at a positive stop the right seed is admissible (`cumWeightRight (β⁺(0) + θχ) > −2`);
* `hRT`: at a right touch `z > 0` before the stop the piece's right weight is `> −2`;
* `hLT`: a left touch `z < 0` before the stop lies inside an open interval where the word is constant with left weight
  `< κ/2 − 2` (the touch criterion GB7a, and G12 at the marks).

The location of a left touch (`jw_leftLoc`): the chart points strictly between the touch and the tip are in the closed
hull, so not alive, so their left-ray preimages are right of the new left record (`lLeft_launch`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

variable {κ θ ψ u : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The location of a left touch**: left-ray points whose images lie strictly between the touch and the tip are at or
right of the new left record. -/
theorem jw_leftLoc {s : ExplState} (hc : IsRealChart (stChart s)) (hs : LLeft s) (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : IsRegularDriver D) (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) {γ : ℝ → ℂ}
    (hγ : IsLoewnerTraceLT (rdrv (recOf ⊤ D)) (rtime (recOf ⊤ D)) γ)
    (hγc : ContinuousOn γ (Icc 0 (rtime (recOf ⊤ D)))) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (ht₀T : t₀ < rtime (recOf ⊤ D)) (him : (γ t₀).im = 0) (hneg : (γ t₀).re < 0) :
    ∃ δ > 0, ∀ x, ((γ t₀).re < rProf (stChart s) x ∧ rProf (stChart s) x < (γ t₀).re + δ) →
      stRecL (ExplState.launch s k D θ ⊤) ≤ x := by
  set r := recOf ⊤ D with hr
  set W := rdrv r with hWdef
  set T := rtime r with hTdef
  have hW : Continuous W := continuous_rdrv r
  have hW0 : W 0 = 0 := rdrv_zero r
  have hT0 : 0 ≤ T := rtime_nonneg r
  obtain ⟨-, -, hrelL⟩ := lLeft_launch hc hs k θ hreg hgood hfin
  have hL₁ : stRecL (ExplState.launch s k D θ ⊤) ≤ stRecL s := by
    by_contra hlt
    push Not at hlt
    have h1 := (hrelL ((stRecL s + stRecL (ExplState.launch s k D θ ⊤)) / 2) (by linarith)).1
    linarith
  set z := (γ t₀).re with hz
  refine ⟨-z, by linarith, fun x hx => ?_⟩
  by_cases hxL : stRecL s ≤ x
  · exact hL₁.trans hxL
  push Not at hxL
  by_contra hlt
  push Not at hlt
  -- the image is alive at the stop
  obtain ⟨-, ⟨v, hv⟩, -⟩ := hrelL x hlt
  have hcl := Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hW hT0 hv
  set y := rProf (stChart s) x with hy
  have hy0 : y < 0 := by linarith [hx.2]
  have hγ0 : γ 0 = 0 := hγ.1
  have ht₀pos : 0 < t₀ := by
    rcases ht₀.lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 : z = 0 := by rw [hz, ← h, hγ0]; simp
      linarith
  -- but it is in the closed hull
  apply hcl
  by_cases hyA : (y : ℂ) ∈ γ '' Icc 0 t₀
  · obtain ⟨t₁, ht₁, he⟩ := hyA
    have ht₁pos : 0 < t₁ := by
      rcases ht₁.1.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h, hγ0] at he
        have : (y : ℂ) = 0 := he.symm
        have : y = 0 := by exact_mod_cast this
        linarith
    have h1 := Supp7.G12.trace_mem_closure_fwdHull hW hW0 hγ ht₁pos (lt_of_le_of_lt ht₁.2 ht₀T)
    rw [he] at h1
    exact closure_mono (Vo.fwdHull_mono (lt_of_le_of_lt ht₁.2 ht₀T).le) h1
  · have hc₀ : ContinuousOn γ (Icc 0 t₀) := hγc.mono fun q hq => ⟨hq.1, hq.2.trans ht₀T.le⟩
    have hHbar : MapsTo γ (Icc 0 t₀) Hbar := fun q hq =>
      Vo.mem_Hbar_of_trace hW hW0 hγ hγc ⟨hq.1, hq.2.trans ht₀T.le⟩
    have hmem := YuanCharacterisation.mem_closure_fillH_of_lt_of_lt hc₀ hHbar (u₁ := t₀) (u₂ := 0)
      ⟨ht₀, le_rfl⟩ ⟨le_rfl, ht₀⟩ him (by rw [hγ0]; simp) hx.1 (by rw [hγ0]; simpa using hy0) hyA
    rw [← hγ.2.2 t₀ ht₀ ht₀T] at hmem
    exact closure_mono (Vo.fwdHull_mono ht₀T.le) hmem

/-- **The junction invariant through a launch, from the walk's invariants and three facts about the piece.** -/
theorem jw_launch_full (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {β : BoundaryWord} {s : ExplState} (hc : IsRealChart (stChart s)) (hcc : (stChart s).IsConformal)
    (hs : LLeft s) (hL0 : stRecL s ≤ 0) (hR0 : 0 ≤ stRecR s) (hRP : RProf s) (hRO : ROrig b jumps β s)
    (hOW : OW κ θ b jumps β s) (hI : JW κ θ ψ u b β s) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (stChart s).2.1 H) (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) {γ : ℝ → ℂ}
    (hγ : IsLoewnerTraceLT (rdrv (recOf ⊤ D)) (rtime (recOf ⊤ D)) γ)
    (hγc : ContinuousOn γ (Icc 0 (rtime (recOf ⊤ D))))
    (hs₁ : RProf (ExplState.launch s k D θ ⊤)) (hO₁ : ROrig b jumps (stopWord κ (β, θ, recOf ⊤ D))
      (ExplState.launch s k D θ ⊤)) (hOW₁ : OW κ θ b jumps (stopWord κ (β, θ, recOf ⊤ D)) (ExplState.launch s k D θ ⊤))
    (hR0₁ : 0 ≤ stRecR (ExplState.launch s k D θ ⊤))
    (hseed : 0 < rtime (recOf ⊤ D) → -2 < Sec4.cumWeightRight κ (rightLim β.fn 0 + θ * chiC κ))
    (hRT : ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < rtime (recOf ⊤ D) → (γ t₀).im = 0 → 0 < (γ t₀).re →
      -2 < Sec4.cumWeightRight κ (rightLim β.fn (γ t₀).re + θ * chiC κ))
    (hLT : ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < rtime (recOf ⊤ D) → (γ t₀).im = 0 → (γ t₀).re < 0 →
      ∃ a a' v : ℝ, a < (γ t₀).re ∧ (γ t₀).re < a' ∧ (∀ y ∈ Ioo a a', y ∉ β.jumps → β.fn y = v) ∧
        Sec4.cumWeightLeft κ (v + θ * chiC κ) < κ / 2 - 2) :
    JW κ θ ψ u b (stopWord κ (β, θ, recOf ⊤ D)) (ExplState.launch s k D θ ⊤) := by
  set s₁ := ExplState.launch s k D θ ⊤ with hs₁def
  obtain ⟨-, -, hrelL⟩ := lLeft_launch hc hs k θ hreg hgood hfin
  have hL₁ : stRecL s₁ ≤ stRecL s := by
    by_contra hlt
    push Not at hlt
    have h1 := (hrelL ((stRecL s + stRecL s₁) / 2) (by linarith)).1
    linarith
  have hL₁R : stRecL s₁ ≤ stRecR s := (hL₁.trans hL0).trans hR0
  have hfree : ∀ x, stRecR s < x → ContinuousAt (stChart s).1 (x : ℂ) ∧ ChartFree (stChart s) x := by
    obtain ⟨S, -, -, -, hSR, -, hSc, -⟩ := hOW
    exact fun x hx => hSc x (hSR x hx)
  have hfree₁ : ∀ x, stRecR s₁ < x → ContinuousAt (stChart s₁).1 (x : ℂ) ∧ ChartFree (stChart s₁) x := by
    obtain ⟨S, -, -, -, hSR, -, hSc, -⟩ := hOW₁
    exact fun x hx => hSc x (hSR x hx)
  -- the chart after the launch is conformal
  have hcc₁ : (stChart s₁).IsConformal := by
    have hWe : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
    have hch : stChart s₁ = (stChart s).loewner (rdrv (recOf ⊤ D)) (rtime (recOf ⊤ D)) := by
      rw [hWe, rtime_recOf]; exact (launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)).1
    rw [hch]
    exact hcc.loewner (continuous_rdrv _) (rdrv_zero _) (rtime_nonneg _)
  refine jw_launch hκ hc hcc hs hI hgc hgi k hreg hgood hfin hγ hγc ?_ ?_ ?_ ?_
  · -- the new right ray
    intro g₁ hg₁c hg₁i r₁ hr₁ hlow p hp
    obtain ⟨h1, h2⟩ := jw_rightRay hκ hκ4 hθψ hs₁.1 hcc₁ hs₁ hO₁ hfree₁ hg₁c hg₁i hr₁ hlow hp
    refine ⟨?_, fun _ => h2⟩
    have hL₁' : stRecL s₁ ≤ 0 := hL₁.trans hL0
    linarith
  · -- the base
    intro hτ p hp
    exact jw_base hκ hκ4 hθψ hc hcc hRP hRO hfree hgc hgi hL₁R (hseed hτ) p hp
  · -- right touches before the stop
    intro t₀ ht₀ ht₀T him hpos p hp
    have hzr : γ t₀ = (((γ t₀).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hzr] at hp
    exact jw_rightTouch hκ hκ4 hθψ hc hcc hRP hRO hfree hgc hgi hL₁R hpos (hRT t₀ ht₀ ht₀T him hpos) p hp
  · -- left touches before the stop
    intro t₀ ht₀ ht₀T him hneg p hp
    obtain ⟨a, a', v, ha, ha', hcon, hlowv⟩ := hLT t₀ ht₀ ht₀T him hneg
    have hzr : γ t₀ = (((γ t₀).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hzr] at hp
    exact jw_leftTouch hκ hκ4 hθψ hb hcc hOW hc hgc hgi ha ha' hcon hlowv
      (jw_leftLoc hc hs k hreg hgood hfin hγ hγc ht₀ ht₀T him hneg) p hp

end InteractingSLE.Theorem14.SB.Wf
