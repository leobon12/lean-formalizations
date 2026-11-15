/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CqFacts
import InteractingSLE.Spec.Supplement.SB2CqHull
import InteractingSLE.Spec.Supplement.SB2CqGood
import InteractingSLE.Spec.Supplement.SB2CjK2
import InteractingSLE.Spec.Supplement.SBS3CanonComp
import InteractingSLE.Spec.Supplement.SB2MzFacts

/-!
# The chain facts at a tail stage, almost surely

Packet PROVE-SB2-CANON, round 5 ((P4) at the tails). **`ae_chainFacts_tail`**: for the objects of the successor
statement `Cz.SB2LowerStageVersionStatement6` at a tail stage `ℓ` (the hull `K` with `fill K = A₁ 0` on the live event
`F`, the entry offset `x₀`, `F`'s characterization, relative versions `S` at announced stops for the canonical chart
`Mo.hullChart (fill K) x₀` and a word `c` with countably many types covering `F`, the clock coverage and the first-stop
bound), K2's outputs (the stopped code matches and the lifetime identity, `Cj.ae_k2_stage`) and the continuity of the
canonical driver up to its lifetime (`ae_continuousOn_driverOf`), almost surely on `F` the chain facts
`Qx.ChainFacts` of the canonical driver hold.

At a sample: NOJUMP's good-sample facts for the retained union (`ae_stageGoodAt_retX`), the sample's own word type
(whose seed cell contains it, `Ci.hseed_of_le_thr`), the versions' hull, alive and reach clauses at all rational B-times
with the line family read as fills (`union_fillVer_eq`) and the canonical curve (`fwdHull_eq_canon_of_hull`) give the
identification (`ident_canon_at`); B's stage chart (`S3.Canon.runChart_package`, `Mz.isNormalized_walkStageChart`) and
B's stage trace (`LuM.isGeneratingTrace_trOf`) give the rest of `chainFacts_at`'s inputs.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms Mf WalkSide Lk
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **The chain facts at a tail stage, almost surely on the live event.** See the module docstring. -/
theorem ae_chainFacts_tail (h12p : Theorem12ParamStatement.{u}) (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    -- the line family
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
    (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω)
    -- the successor statement's objects
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {relLife : Ω → ℝ≥0∞} {F : Set Ω}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω)
    (hent : ∀ᵐ ω ∂P, ω ∈ F → IsRightEntryChart (Nc.retX κ b jumps E u l k ℓ ω)
      (realMax (Nc.retX κ b jumps E u l k ℓ ω))
      ((Mo.hullChart (fillH (Nc.retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω)))
    (hFae : ∀ᵐ ω ∂P, ω ∈ F → (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
    {c : Ω → BoundaryWord} {types : Set WordType} (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ (-(Real.pi / 2)) (c ω) ∈ types)
    (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) c types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      ∃ m, (S.ver m).a t ω < S.V m ω)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ (-(Real.pi / 2)) c F w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W (cellXL κ (-(Real.pi / 2)) c w)
        (cellXR κ (-(Real.pi / 2)) c w) ω)
    -- K2's outputs and the continuity of the canonical driver
    (hK2 : ∀ᵐ ω ∂P, ω ∈ F →
      (∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2))
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
        (fun t => (S.ver m).W t ω) (S.V m ω)) ∧
      (driverCode h12p hκ (-(Real.pi / 2))
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω)
    (hcont : ∀ᵐ ω ∂P, ω ∈ F → ContinuousOn (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).1
      {s | (s : ℝ≥0∞) ≤ (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).2}) :
    ∀ᵐ ω ∂P, ω ∈ F → Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω := by
  -- the a.s. facts, over the countable index sets
  have hgood := ae_stageGoodAt_retX h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hFae hent
  have hseed : ∀ᵐ ω ∂P, ∀ v ∈ types, ω ∈ wordTypeCell κ (-(Real.pi / 2)) c F v →
      ω ∈ seedCell κ (-(Real.pi / 2)) c F v :=
    (ae_ball_iff htypes).2 (Ci.hseed_of_le_thr S hle)
  have hAq : ∀ᵐ ω ∂P, ∀ q : ℚ, A₁ (q : ℝ).toNNReal ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
      A₂ (q : ℝ).toNNReal ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω) ω :=
    ae_all_iff.2 fun q => hA (q : ℝ).toNNReal
  have hhullq : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ q : ℚ, ∀ v ∈ types, ω ∈ seedCell κ (-(Real.pi / 2)) c F v →
      (S.ver m).a (q : ℝ).toNNReal ω < (S.ver m).Λ v ω →
      H \ (A₁ (q : ℝ).toNNReal ω ∪ A₂ (q : ℝ).toNNReal ω) = (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.1 ''
        (H \ fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a (q : ℝ).toNNReal ω).toNNReal) :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun q => (ae_ball_iff htypes).2 fun v hv =>
      (S.ver m).hull v hv (q : ℝ).toNNReal
  have haliveq : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ q : ℚ, ∀ v ∈ types, ω ∈ seedCell κ (-(Real.pi / 2)) c F v →
      (S.ver m).a (q : ℝ).toNNReal ω < (S.ver m).Λ v ω →
      (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun q => (ae_ball_iff htypes).2 fun v hv =>
      (S.ver m).alive v hv (q : ℝ).toNNReal
  have hreachq : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ q : ℚ, ∀ v ∈ types, ω ∈ seedCell κ (-(Real.pi / 2)) c F v →
      (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (S.ver m).Λ v ω →
      ∃ t, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (S.ver m).a t ω :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun q => (ae_ball_iff htypes).2 fun v hv =>
      (S.ver m).reach v hv (q : ℝ).toNNReal
  have hclq : ∀ᵐ ω ∂P, ∀ q : ℚ, ω ∈ F →
      (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      ∃ m, (S.ver m).a (q : ℝ).toNNReal ω < S.V m ω :=
    ae_all_iff.2 fun q => hcl (q : ℝ).toNNReal
  filter_upwards [hgood, hseed, hAq, hA 0, hKF, hFae, hcover, hhullq, haliveq, hreachq, hclq, S.V_sup, hK2, hcont]
    with ω hg hsd hAω hA0 hKω hFω hcov hhω halω hrω hclω hsup hk2 hcω hωF
  obtain ⟨hst, hoff, hpos⟩ := hFω hωF
  have hgω := hg hωF
  -- the sample's own cell
  set v₀ := angleWordType κ (-(Real.pi / 2)) (c ω) with hv₀
  have hv₀T : v₀ ∈ types := hcov hωF
  have hcell : ω ∈ seedCell κ (-(Real.pi / 2)) c F v₀ := hsd v₀ hv₀T ⟨hωF, rfl⟩
  -- the retained union
  have hfill : fillH (K ω) = fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
    rw [hKω hωF, hA0.1]; exact fillVer_first_eq hgω _
  have hL0 : (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≠ 0 := pos_iff_ne_zero.1 hpos
  have hpc := Ne.continuousOn_bPc hgω
  have hdr : IsDrivenCurve (Dv.canonCurve (Nc.retX κ b jumps E u l k ℓ ω) (x₀ ω) (Nc.bPc κ b jumps E ℓ ω)
      (Nc.bLife b jumps E ℓ ω)) := hgω.driven
  -- the identification
  have hΛ : ∀ m, (S.ver m).Λ v₀ ω = S.V m ω := fun m => by rw [S.Λ_eq m v₀]
  obtain ⟨he1, he2⟩ := ident_canon_at hdr hL0 (Wm := fun m t => (S.ver m).W t ω)
    (am := fun m t => (S.ver m).a t ω) (V := fun m => S.V m ω) (relLife := relLife ω)
    (fun m => (S.ver m).W_cont ω) (fun m => (S.ver m).W_zero ω) (fun m => (S.ver m).clock_cont ω)
    (fun m => (S.ver m).clock_zero ω) (hsup hωF)
    (fun m q hq => by
      have hq' : (S.ver m).a (q : ℝ).toNNReal ω < (S.ver m).Λ v₀ ω := by rw [hΛ m]; exact hq
      have hal := halω m q v₀ hv₀T hcell hq'
      have hH := hhω m q v₀ hv₀T hcell hq'
      rw [union_fillVer_eq hgω hal (hAω q).1 (hAω q).2, hfill] at hH
      exact fwdHull_eq_canon_of_hull hgω.retc hgω.hull hL0 hpc hdr hal hH)
    (fun m q hq => halω m q v₀ hv₀T hcell (by rw [hΛ m]; exact hq))
    (fun m q hq => hrω m q v₀ hv₀T hcell (by rw [hΛ m]; exact hq))
    (fun q hq => hclω q hωF hq) (e := Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω)
    (Mz.isRegularDriver_driverOf h12p hκ _ _)
    (fun m => (hk2 hωF).1 m) (hk2 hωF).2
  -- B's stage chart and stage trace
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hst.2
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hl'
  obtain ⟨-, gc, C, hD, -, -, -, -, -, -, hgct, hgC⟩ :=
    S3.Canon.runChart_package (κ := κ) (b := b) (jumps := jumps) _
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) hgω.walk.reg ℓ hnd
  have hPR := LuM.pieceRegular_of_launch hgω.walk.reg hst.2
  have hα := LuM.isGeneratingTrace_trOf hPR
  exact chainFacts_at h12p hκ E u l k ℓ hKc hKp hst.2 hD (Mz.isNormalized_walkStageChart hgω.walk.reg ℓ) hgct hgC
    hgω.retc hgω.hull hfill hL0 hpc hdr hα.2.1
    (fun t ht => LuM.im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht) he1 he2 (hcω hωF)

end InteractingSLE.Theorem14.SB.Cz
