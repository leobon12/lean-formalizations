/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FoThr
import InteractingSLE.Spec.Supplement.SB2FoTail
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import InteractingSLE.Spec.Exist.StagedLaw3Path
import InteractingSLE.Spec.Supplement.SB2FmSeed

/-!
# D34's left heights: the step `ℓ → ℓ + 2` of F3's induction

Worker PROVE-SB2-F3LAW (round 3, target 3's `hL`). The invariant "the retained word is admissible left of the entry
of the free ray right of the seed" (`Fm.LeftAdm κ β (Fm.entry A p)`, the input of `Fm.ae_heightClause_of_leftAdm`)
passes through one step of F3's induction:

* `stepHull_recDrv_eq`: the stepped hull only sees the relative driver up to its lifetime;
* **`leftAdm_stepWord_entry`** (one sample, in the step's objects: `Qw.stepWord`, `Qw.stepHull`, `Qw.recDrv`);
* **`leftAdm_entry_mono`** (the zero-lifetime step: same hull and word, the seed moves along admissible free points);
* **`ae_leftAdm_succ_succ`** (almost surely, positive lifetime, tail or root seed `p ≥ stPt (run ℓ)`): from the
  invariant at `ℓ`, the offset bound `x₀ ≤ entry`, the original heights right of the entry, the seed cell, the
  kernel law of the relative chart field, and the step's outputs (`Fo.mvLaw_succ_succ_jointX`); its other inputs are
  `Fo.ae_markPos_zero_driverOf` (right side swallowed), `Fm.ae_seed_freeRight` (free ray at `ℓ + 2`) and
  `Fo.ae_free_between_seeds` (admissible connector).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fo

open Restart Exist Exist.Staged Exist.StagedLaw Fm Qw

/-- The stepped hull only sees the driver up to the lifetime: `recDrv e` and the record's driver agree there. -/
theorem stepHull_recDrv_eq {A : Set ℂ} (x₀ : ℝ) {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver e)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ e))) (hfin : e.2 ≠ ⊤) :
    stepHull A x₀ (Qw.recDrv e) (e.2.toNNReal : ℝ) =
      stepHull A x₀ (rdrv (recOf ⊤ e)) (rtime (recOf ⊤ e)) := by
  have hT : rtime (recOf ⊤ e) = (e.2.toNNReal : ℝ) := by
    rw [rtime_recOf_coe, min_eq_right le_top]
  have hfin' : min ⊤ e.2 ≠ ⊤ := by rwa [min_eq_right le_top]
  rw [hT]
  unfold stepHull
  congr 2
  refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc (Qw.continuous_recDrv hreg hgood) (continuous_rdrv _)
    (NNReal.coe_nonneg _) fun s hs => ?_
  rw [rdrv_recOf_eq hreg hgood hfin' (by rw [hT]; exact hs.2)]
  unfold Qw.recDrv retOf
  show e.1 (min ((s.toNNReal : ℝ≥0) : ℝ≥0∞) (min ⊤ e.2)).toNNReal = e.1 s.toNNReal
  have h1 : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ min ⊤ e.2 := by
    rw [min_eq_right le_top, ← ENNReal.coe_toNNReal hfin]
    exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2
  rw [min_eq_left h1, ENNReal.toNNReal_coe]

/-- **D34's left heights through one step of F3's induction, in the step's own objects (one sample)**: the word of
`Fl.mvLaw_succ_succ` (`Qw.stepWord`) is admissible left of the entry of the stepped hull at the next seed. -/
theorem leftAdm_stepWord_entry {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {x₀ : Ω → ℝ}
    {β₁ : Ω → BoundaryWord} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω} {A : Set ℂ} (hA : IsHPHull A) {p : ℝ}
    (hp : FreeRight A p) (hx₀ : x₀ ω ≤ entry A p) (hL : LeftAdm κ (β₁ ω) (entry A p))
    (hread : ∀ x, p < x → x ∉ jumps → bdryVal A x ∉ (β₁ ω).jumps → (β₁ ω).fn (bdryVal A x) = b x)
    (hreg : IsRegularDriver (e ω)) (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ (e ω)))) (hfin : (e ω).2 ≠ ⊤)
    (h0 : markPos (rdrv (recOf ⊤ (e ω))) (rtime (recOf ⊤ (e ω))) 0 = 0) {p' : ℝ}
    (hp' : FreeRight (stepHull A (x₀ ω) (Qw.recDrv (e ω)) ((e ω).2.toNNReal : ℝ)) p')
    (hlow : ∀ x, p < x → x < p' →
      (∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (stepHull A (x₀ ω) (Qw.recDrv (e ω)) ((e ω).2.toNNReal : ℝ))) →
      x ∉ jumps → b x + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    LeftAdm κ (stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) e ω)
      (entry (stepHull A (x₀ ω) (Qw.recDrv (e ω)) ((e ω).2.toNNReal : ℝ)) p') := by
  rw [stepHull_recDrv_eq (x₀ ω) hreg hgood hfin] at hp' hlow ⊢
  exact leftAdm_entry_step hκ hA hp hx₀ hL hread (recOf ⊤ (e ω)) h0 hp' hlow

/-- **The zero-lifetime step**: the hull and word do not change, the seed moves from `p` to the next restart mark
`p'`; the free points between them are admissible, so admissibility left of the entry moves from `p` to `p'`. -/
theorem leftAdm_entry_mono {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {A : Set ℂ} (hA : IsHPHull A) {p p' : ℝ}
    (hp : FreeRight A p) (hpp' : p ≤ p') {β : BoundaryWord} (hL : LeftAdm κ β (entry A p))
    (hread : ∀ x, p < x → x ∉ jumps → bdryVal A x ∉ β.jumps → β.fn (bdryVal A x) = b x)
    (hlow : ∀ x, p < x → x < p' → x ∉ jumps → b x + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    LeftAdm κ β (entry A p') := by
  classical
  have hp' : FreeRight A p' := fun x hx => hp x (lt_of_le_of_lt hpp' hx)
  set F : Finset ℝ := β.jumps ∪ {entry A p} ∪ jumps.image (bdryVal A) with hF
  have hgen : ∀ y, y < entry A p' → y ∉ F → β.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := by
    intro y hy hyF
    have hyJ : y ∉ β.jumps := fun h => hyF (by simp [hF, h])
    rcases lt_trichotomy y (entry A p) with hlt | heq | hgt
    · exact hL y hlt hyJ
    · exact absurd (by rw [hF, heq]; simp) hyF
    obtain ⟨x, hpx, hbx⟩ := exists_bdryVal_eq hA hp hgt
    have hxp' : x < p' := by
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.1 hge) with h | h
      · obtain ⟨r, hr, hd⟩ := hp x hpx
        have := entry_le_bdryVal_self hA hp' hr (by rw [h]; exact hd)
        rw [show bdryVal A p' = y by rw [h]; exact hbx] at this
        linarith
      · have := entry_le_bdryVal hA hp' h
        rw [hbx] at this
        linarith
    have hxJ : x ∉ jumps := fun h => hyF (by
      rw [hF, ← hbx]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
    rw [← hbx, hread x hpx hxJ (by rw [hbx]; exact hyJ)]
    exact hlow x hpx hxp' hxJ
  intro y hy hyJ
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 (β.isPiecewiseConstantBoundaryData y hyJ)
  obtain ⟨y'', ⟨hy1, hy2⟩, hyF⟩ := ((Set.Ioo_infinite (show y - δ < y by linarith)).sdiff
    F.finite_toSet).nonempty
  have he : β.fn y'' = β.fn y := hδb (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [← he]
  exact hgen y'' (by linarith) hyF

/-- **D34's left heights through the step `ℓ → ℓ + 2` of F3's induction, almost surely** (positive lifetime; tail or
root: `p` is the seed of the stage, at least B's point `stPt (run ℓ)`). The inputs at stage `ℓ` are the invariant
`hL`, the offset bound `hx₀le` (F2b′'s offset is the entry of the free ray, `entryRead_eq_entry`), the original
heights right of the entry (`hread`), the seed cell's seed (`hseedF`) and the kernel law of the relative chart field
(`hlawx`); the step's outputs (`Fo.mvLaw_succ_succ_jointX`): `G₂ ⊆ F`, the finite lifetime, the stepped hull. -/
theorem ae_leftAdm_succ_succ (h12p : Theorem12ParamStatement.{u}) (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    -- stage `ℓ`
    (h𝓜 : 𝓜 ≤ mΩ) {K : Ω → Set ℂ} (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {x₀ : Ω → ℝ} {β₁ : Ω → BoundaryWord} {F : Set Ω}
    (hc : Measurable[𝓜] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
    (hZ : Measurable fun ω => Fl.canonField κ h x₀ hKc hKp ω) (hF : MeasurableSet[𝓜] F)
    (hlawx : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) (Fl.canonField κ h x₀ hKc hKp)
      (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).jumps)
    (hFev : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Ms.stageEvent κ b jumps E u l k ℓ) {p : Ω → ℝ}
    (hp : ∀ᵐ ω ∂P, ω ∈ F → FreeRight (fillH (K ω)) (p ω) ∧
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) ≤ p ω)
    (hx₀le : ∀ᵐ ω ∂P, ω ∈ F → x₀ ω ≤ entry (fillH (K ω)) (p ω))
    (hL : ∀ᵐ ω ∂P, ω ∈ F → LeftAdm κ (β₁ ω) (entry (fillH (K ω)) (p ω)))
    (hread : ∀ᵐ ω ∂P, ω ∈ F → ∀ x, p ω < x → x ∉ jumps → bdryVal (fillH (K ω)) x ∉ (β₁ ω).jumps →
      (β₁ ω).fn (bdryVal (fillH (K ω)) x) = b x)
    (hseedF : ∀ᵐ ω ∂P, ω ∈ F → ¬ ForceWord.ThresholdCondition
      (flowLineRhoL κ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0
        (-(Real.pi / 2)))
      (flowLineRhoR κ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0
        (-(Real.pi / 2))) 0
      (flowLineXL (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0)
      (flowLineXR (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0))
    -- the step's outputs at `ℓ + 2`
    {A₁' : Ω → Set ℂ} (hA' : ∀ᵐ ω ∂P, A₁' ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    {K₂ : Ω → Set ℂ} {G₂ : Set Ω} (hG₂F : G₂ ⊆ F)
    (hζ₂ : ∀ ω ∈ G₂, (driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)).2 ≠ ⊤)
    (hhull₂ : ∀ᵐ ω ∂P, ω ∈ G₂ →
      LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)))) →
      fillH (K₂ ω) = stepHull (fillH (K ω)) (x₀ ω) (Qw.recDrv (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)))
        ((driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)).2.toNNReal : ℝ))
    (hK₂A : ∀ᵐ ω ∂P, ω ∈ G₂ → fillH (K₂ ω) = A₁' ω) :
    ∀ᵐ ω ∂P, ω ∈ G₂ → ω ∈ Ms.stageEvent κ b jumps E u l k (ℓ + 2) →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ + 2 →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) ω).2 →
      LeftAdm κ (stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
        (Fl.maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)) ω)
        (entry (A₁' ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 2)))) := by
  have hE2 := ae_markPos_zero_driverOf h12p h13 hκ (-(Real.pi / 2)) h𝓜 hc hZ hF hlawx
  filter_upwards [hFev, hp, hx₀le, hL, hread, hseedF, hE2, hhull₂, hK₂A,
    ae_seed_freeRight h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k (ℓ + 2) hleft hA',
    ae_free_between_seeds h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA']
    with ω hFevω hpω hx₀ω hLω hreadω hseedω hE2ω hhullω hK₂ω hseed2 hfree2 hωG hev2 hoff2 hpos2
  have hωF : ω ∈ F := hG₂F hωG
  obtain ⟨hpfree, hpst⟩ := hpω hωF
  set D := driverOf h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)
    with hDdef
  have hfin : D.2 ≠ ⊤ := hζ₂ ω hωG
  have hLc : ∀ y, y < 0 → y ∉ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps →
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := by
    have h1 : LeftAdm κ (β₁ ω) (x₀ ω) := fun y hy hyJ => hLω hωF y (lt_of_lt_of_le hy (hx₀ω hωF)) hyJ
    have h2 := leftAdm_shiftW h1 (x₀ ω)
    rw [sub_self] at h2
    exact h2
  obtain ⟨hgood, h0⟩ := hE2ω hωF (hseedω hωF) hLc hfin
  have hA'ω : stepHull (fillH (K ω)) (x₀ ω) (Qw.recDrv D) (D.2.toNNReal : ℝ) = A₁' ω :=
    (hhullω hωG hgood).symm.trans (hK₂ω hωG)
  obtain ⟨-, -, hfreeR⟩ := hseed2 hev2 hoff2 hpos2
  have hlow : ∀ x, p ω < x → x < stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 2)) →
      (∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (stepHull (fillH (K ω)) (x₀ ω) (Qw.recDrv D) (D.2.toNNReal : ℝ))) →
      x ∉ jumps → b x + -(Real.pi / 2) * chiC κ < sleLambda κ := fun x hpx hxp' hfr hxJ =>
    hfree2 (hFevω hωF) hev2.2 x (lt_of_le_of_lt hpst hpx) hxp' (by rwa [← hA'ω]) hxJ
  have hstep := leftAdm_stepWord_entry (e := fun ω => driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)) (ω := ω) hκ
    (Mo.isHPHull_fillH hKc hKp ω) hpfree (hx₀ω hωF) (hLω hωF) (hreadω hωF) (Mz.isRegularDriver_driverOf h12p hκ _ _)
    hgood hfin h0 (by rw [hA'ω]; exact hfreeR) hlow
  rw [hA'ω] at hstep
  have hw : stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
      (Fl.maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)) ω =
      stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
        (fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)) ω := by
    unfold stepWord
    rw [Fl.maskDrv_of_mem hωF]
  rw [hw]
  exact hstep

end InteractingSLE.Theorem14.SB.Fo
