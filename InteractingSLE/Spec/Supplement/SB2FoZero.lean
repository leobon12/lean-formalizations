/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FoInp
import InteractingSLE.Spec.Supplement.SB2QxPhys

/-!
# D34's left heights through a zero-lifetime stage of B

Worker PROVE-SB2-F3LAW (round 3). When B's piece at a tail stage `ℓ` has lifetime `0` and B launches again at `ℓ + 2`,
the retained hull is unchanged (`Qx.stageSet_succ_succ_eq_of_zero`), the word is unchanged (`Fl.mvLaw_succ_succ_zero`),
and the seed moves from `p = stPt (run ℓ)` to `p' = stPt (run (ℓ + 2)) ≥ p` (NOJUMP's `Nc.realMax_retX_eq` at both
stages) over free points whose heights are admissible (`ae_free_between_seeds`); so `Fm.LeftAdm` passes from the entry
at `p` to the entry at `p'` (`leftAdm_entry_mono`).

* **`ae_leftAdm_zero`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fo

open Restart Exist Exist.Staged Exist.StagedLaw Fm Qw WalkSide

/-- **D34's left heights through a zero-lifetime stage, almost surely**: when B's piece at `ℓ` has lifetime `0` and B
launches again at `ℓ + 2`, the retained hull does not change and the seed moves from `p = stPt (run ℓ)` to the next
restart mark `p'` over an admissible connector; the word (`Fl.mvLaw_succ_succ_zero` keeps it) stays admissible left of
the new entry. -/
theorem ae_leftAdm_zero (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {A₁ A₁' : Ω → Set ℂ} (hA : ∀ᵐ ω ∂P, A₁ ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω)
    (hA' : ∀ᵐ ω ∂P, A₁' ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    {β : Ω → BoundaryWord} :
    ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 →
      LeftAdm κ (β ω) (entry (A₁ ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ))) →
      (∀ x r : ℝ, 0 < r → Disjoint (ball (x : ℂ) r) (A₁ ω) → x ∉ jumps →
        bdryVal (A₁ ω) x ∉ (β ω).jumps → (β ω).fn (bdryVal (A₁ ω) x) = b x) →
      IsHPHull (A₁ ω) ∧ A₁' ω = A₁ ω ∧
      LeftAdm κ (β ω) (entry (A₁' ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 2)))) := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set Er := StagedReg.regFam E w with hEr
  by_cases hℓ : ℓ < w.2.2.length
  swap
  · refine Eventually.of_forall fun ω hω => absurd (SB.Nc.flow_of_launch hω.2).1 hℓ
  by_cases hℓ2 : ℓ + 2 < w.2.2.length
  swap
  · refine Eventually.of_forall fun ω _ hl2 => absurd (SB.Nc.flow_of_launch hl2).1 hℓ2
  filter_upwards [SB.Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft,
    SB.Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ, hA, hA', hrun w hwbc,
    SB.Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k (ℓ + 2) hℓ2,
    Qx.ae_walkChainFacts_regFam h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER,
    ae_free_between_seeds h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA']
    with ω hg hgeo hAω hA'ω hrω hgeo2 hWC hfree hev hl2 hoff h0 hL hread
  have hgω := hg hev.1
  obtain ⟨hXc, -, -, hHP, hfill⟩ := hgeo hev.2
  have hAeq : A₁ ω = fillH (SB.Nc.retX κ b jumps E u l k ℓ ω) := hAω.trans hfill
  have heven := SB.Nc.even_of_launch hev.2
  have hmax := SB.Nc.realMax_retX_eq hgω hev.2 hoff heven
  have hfreeR : FreeRight (A₁ ω) (stPt (ExplState.run κ b jumps w (fun i => E w i ω) ℓ)) := by
    rw [hAeq, ← hmax]; exact freeRight_fillH_realMax hXc
  -- the hull does not change
  have hl' : (ExplState.run κ b jumps w (fun j => Er j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [hrω]; exact hev.2
  obtain ⟨old, q₀, q₁, hS⟩ := Qx.pieceSimpleAt_of_chainFacts hWC hl'
  have h0' : (Er ℓ ω).2 = 0 := by rw [hEr, StagedReg.regFam, StagedReg.regHist_snd]; exact h0
  have hst := Qx.stageSet_succ_succ_eq_of_zero (κ := κ) (b := b) (jumps := jumps) (E := Er) hl' hS h0'
  obtain ⟨-, hlen⟩ := Qx.walk_instr_of_launch hl'
  have hlen2 : ℓ + 2 ≤ w.2.2.length := (SB.Nc.flow_of_launch hl2).1.le.trans' (by omega)
  have hAA : A₁' ω = A₁ ω := by
    rw [hA'ω, hAω]
    unfold Mf.fillVer
    beta_reduce
    rw [WalkInf.stageSet_capSpec_of_le hlen2 ω le_rfl, WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl, hst]
  refine ⟨by rw [hAeq]; exact hHP, hAA, ?_⟩
  rw [hAA]
  have hpp' : stPt (ExplState.run κ b jumps w (fun i => E w i ω) ℓ) ≤
      stPt (ExplState.run κ b jumps w (fun i => E w i ω) (ℓ + 2)) := by
    have hnd : stStatus (ExplState.run κ b jumps w (fun i => E w i ω) ℓ) ≠ GW1Conn.stDone := by
      obtain ⟨⟨c, θ'⟩, hlc⟩ := Option.ne_none_iff_exists'.1 hev.2
      exact WalkIntRunChron.not_done_of_launch w _ hlc
    have hmem : ((stPt (ExplState.run κ b jumps w (fun i => E w i ω) ℓ) : ℝ) : ℂ) ∈
        SB.Nc.retX κ b jumps E u l k (ℓ + 2) ω :=
      Or.inr (WalkIntRunChron.prefixPhysSet_mono w _ (by omega : ℓ ≤ ℓ + 2) (hgω.pinv ℓ hnd).2)
    obtain ⟨hXc2, -, -, -, -⟩ := hgeo2 hl2
    have hmax2 := SB.Nc.realMax_retX_eq hgω hl2 (lt_trans hoff (by omega)) (by omega)
    rw [← hmax2]
    exact SB.Lx.le_realMax_of_mem hXc2 hmem
  refine leftAdm_entry_mono (b := b) (jumps := jumps) (by rw [hAeq]; exact hHP) hfreeR hpp' hL
    (fun x hx hxJ hyJ => ?_) (fun x hx hxp' hxJ => ?_)
  · obtain ⟨r, hr, hd⟩ := hfreeR x hx
    exact hread x r hr hd hxJ hyJ
  · obtain ⟨r, hr, hd⟩ := hfreeR x hx
    exact hfree hev hl2 x hx hxp' ⟨r, hr, by rw [hAA]; exact hd⟩ hxJ

end InteractingSLE.Theorem14.SB.Fo
