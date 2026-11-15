/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CqRoot
import InteractingSLE.Spec.Supplement.SB2CqIdent
import InteractingSLE.Spec.Supplement.SB2CqRJoint
import InteractingSLE.Spec.Supplement.SB2CqTail
import InteractingSLE.Spec.Supplement.SB2CrAll
import InteractingSLE.Spec.Supplement.SB2NeRoot

/-!
# The chain facts at the relative root, almost surely

Packet PROVE-SB2-CANON, round 5 (`Mz.CanonIdentOn` at `relOff`). **`ae_chainFacts_root`**: for the root objects of
`Cz.SB2LowerRootVersionStatement9` (the hull `K` with `fill K = A₁ 0` on `FB`, the root event `Fr ⊆ FB` inside
`Ne.rootEv`, relative root versions `S` from the tail start `entrR` with clock `0` up to it, the clock coverage and the
first-stop bound, a word `c` with countably many types covering `Fr`), K2's outputs at the root (`Cr.ae_k2_root`'s
conclusion), the continuity of the canonical driver up to its lifetime (`ae_continuousOn_driverOf`), and two facts of
the root construction (named below: the post-entry canonical curve is driven for the statement's offset, and B's head
before `entrR` lies in `fill X ∪ ℝ`), almost surely on `Fr` the chain facts `Qx.ChainFacts` hold.

At a sample: the walk facts (`Nc.ae_walkGood`, `Nc.ae_retGeom`, the regularized runs), the line family read as fills
(`union_fillVer_eq_of`), the head split (`image_Icc_add_split`, `fillH_union_of_subset_fill_real`), the versions'
hull clause at the rational B-times after `entrR` (`fwdHull_eq_canon_of_hull` for the post-entry piece), the clock `0`
at `entrR` (**`eq_zero_at_of_rat`**), the identification from the tail start (`ident_canon_shift`), and
`chainFacts_root_at`.

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

/-- **A continuous clock vanishing at the rational times up to `T` vanishes at every time up to `T`.** -/
theorem eq_zero_at_of_rat {a : ℝ≥0 → ℝ≥0∞} (hac : Continuous a) {T : ℝ≥0∞} {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) ≤ T) (h : ∀ q : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T → a (q : ℝ).toNNReal = 0) :
    a τ = 0 := by
  have hZ : IsClosed {t : ℝ≥0 | a t = 0} := isClosed_eq hac continuous_const
  have hS : {t : ℝ≥0 | ∃ q : ℚ, t = (q : ℝ).toNNReal ∧ t ≤ τ} ⊆ {t : ℝ≥0 | a t = 0} := by
    rintro t ⟨q, rfl, hqτ⟩
    exact h q ((ENNReal.coe_le_coe.2 hqτ).trans hτ)
  refine hZ.closure_subset_iff.2 hS ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases hτ0 : τ = 0
  · refine ⟨0, ⟨0, by simp, by simp [hτ0]⟩, by simp [hτ0, hε]⟩
  have hτpos : (0 : ℝ) < τ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hτ0)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (sub_lt_self (τ : ℝ) hε) hτpos)
  have hq0 : (0 : ℝ) ≤ q := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hq1)
  refine ⟨(q : ℝ).toNNReal, ⟨q, rfl, ?_⟩, ?_⟩
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq2.le
  · rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_lt]
    have := lt_of_le_of_lt (le_max_left _ _) hq1
    constructor <;> linarith

/-- **The chain facts at the relative root, almost surely on the root event.** See the module docstring. -/
theorem ae_chainFacts_root (h12p : Theorem12ParamStatement.{u}) (h12 : Theorem12Statement.{u})
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
    -- the root statement's objects
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {pc : Ω → ℝ≥0 → ℂ} {relLife : Ω → ℝ≥0∞} {FB Fr : Set Ω}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ FB → fillH (K ω) = A₁ 0 ω) (hFrB : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ FB)
    (hFr : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ Ne.rootEv κ b jumps E u l k ℓ)
    {c : Ω → BoundaryWord} {types : Set WordType} (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ (-(Real.pi / 2)) (c ω) ∈ types)
    (S : Cr.RootVersionS κ (-(Real.pi / 2)) P Fr 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) c types pc
      (fun ω => (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal)
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hz0 : ∀ m, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ Fr → (t : ℝ≥0∞) ≤ Nd.entrR κ b jumps E u l k ℓ ω →
      (S.ver m).a t ω = 0)
    (hcl : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ Fr → (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      ∃ m, (S.ver m).a t ω < S.V m ω)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ (-(Real.pi / 2)) c Fr w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W (cellXL κ (-(Real.pi / 2)) c w)
        (cellXR κ (-(Real.pi / 2)) c w) ω)
    -- K2's outputs at the root and the continuity of the canonical driver
    (hK2 : ∀ᵐ ω ∂P, ω ∈ Fr →
      (∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2))
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
        (fun t => (S.ver m).W t ω) (S.V m ω)) ∧
      (driverCode h12p hκ (-(Real.pi / 2))
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω)
    (hcont : ∀ᵐ ω ∂P, ω ∈ Fr → ContinuousOn (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).1
      {s | (s : ℝ≥0∞) ≤ (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).2})
    -- the root construction's two facts
    (hdrv : ∀ᵐ ω ∂P, ω ∈ Fr → IsDrivenCurve (Dv.canonCurve (Nc.retX κ b jumps E u l k ℓ ω) (x₀ ω)
      (fun s => Nc.bPc κ b jumps E ℓ ω ((Nd.entrR κ b jumps E u l k ℓ ω).toNNReal + s))
      (Nc.bLife b jumps E ℓ ω - (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal)))
    (hhd : ∀ᵐ ω ∂P, ω ∈ Fr → Nc.bPc κ b jumps E ℓ ω '' Icc 0 (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal ⊆
      fillH (Nc.retX κ b jumps E u l k ℓ ω) ∪ {z | z.im = 0}) :
    ∀ᵐ ω ∂P, ω ∈ Fr → Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω := by
  obtain ⟨-, -, hrun'⟩ := StagedReg.regFam_spec hb hE hER
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hgood := Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft
  have hgeo := Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ
  have hseed : ∀ᵐ ω ∂P, ∀ v ∈ types, ω ∈ wordTypeCell κ (-(Real.pi / 2)) c Fr v →
      ω ∈ seedCell κ (-(Real.pi / 2)) c Fr v :=
    (ae_ball_iff htypes).2 (Cr.hseed_of_le_thr_root S hle)
  have hAq := ae_all_iff.2 fun q : ℚ => hA (q : ℝ).toNNReal
  have hhullq : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ q : ℚ, ∀ v ∈ types, ω ∈ seedCell κ (-(Real.pi / 2)) c Fr v →
      (S.ver m).a (q : ℝ).toNNReal ω < (S.ver m).Λ v ω →
      H \ (A₁ (q : ℝ).toNNReal ω ∪ A₂ (q : ℝ).toNNReal ω) = (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.1 ''
        (H \ fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a (q : ℝ).toNNReal ω).toNNReal) :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun q => (ae_ball_iff htypes).2 fun v hv =>
      (S.ver m).hull v hv (q : ℝ).toNNReal
  have haliveq : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ q : ℚ, ∀ v ∈ types, ω ∈ seedCell κ (-(Real.pi / 2)) c Fr v →
      (S.ver m).a (q : ℝ).toNNReal ω < (S.ver m).Λ v ω →
      (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun q => (ae_ball_iff htypes).2 fun v hv =>
      (S.ver m).alive v hv (q : ℝ).toNNReal
  have hreachq : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ q : ℚ, ∀ v ∈ types, ω ∈ seedCell κ (-(Real.pi / 2)) c Fr v →
      (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (S.ver m).Λ v ω →
      ∃ t, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (S.ver m).a t ω :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun q => (ae_ball_iff htypes).2 fun v hv =>
      (S.ver m).reach v hv (q : ℝ).toNNReal
  have hclq := ae_all_iff.2 fun q : ℚ => hcl (q : ℝ).toNNReal
  have hz0q := ae_all_iff.2 fun m => ae_all_iff.2 fun q : ℚ => hz0 m (q : ℝ).toNNReal
  filter_upwards [hgood, hgeo, hrun' _ hw, hrun' _ hsu, hseed, hAq, hA 0, hKF, hFrB, hFr, hcover, hhullq, haliveq,
    hreachq, hclq, hz0q, S.V_sup, hK2, hcont, hdrv, hhd]
    with ω hgω hgeω hrw hru hsd hAω hA0 hKω hFrBω hFrω hcov hhω halω hrω hclω hz0ω hsup hk2 hcω hdrω hhdω hωF
  obtain ⟨hst, -, -, hent⟩ := hFrω hωF
  have hg := hgω hst.1
  obtain ⟨hc, hH, -, hhull, -⟩ := hgeω hst.2
  -- the sample's own cell
  set v₀ := angleWordType κ (-(Real.pi / 2)) (c ω) with hv₀
  have hv₀T : v₀ ∈ types := hcov hωF
  have hcell : ω ∈ seedCell κ (-(Real.pi / 2)) c Fr v₀ := hsd v₀ hv₀T ⟨hωF, rfl⟩
  have hΛ : ∀ m, (S.ver m).Λ v₀ ω = S.V m ω := fun m => by rw [S.Λ_eq m v₀]
  -- the entrance time and the retained union
  set τ : ℝ≥0 := (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal with hτdef
  have hτ : (τ : ℝ≥0∞) = Nd.entrR κ b jumps E u l k ℓ ω := ENNReal.coe_toNNReal (ne_top_of_lt hent)
  have hτL : (τ : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := by rw [hτ]; exact hent
  have hfill : fillH (K ω) = fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
    rw [hKω (hFrBω hωF), hA0.1]; exact fillVer_first_eq_of hst.2 hrw hru hc _
  have hL' : (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 - τ ≠ 0 := (tsub_pos_of_lt hτL).ne'
  have hBL : ∀ s : ℝ≥0, ((τ + s : ℝ≥0) : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ↔
      (s : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 - τ :=
    fun s => by rw [ENNReal.coe_add]; exact lt_tsub_iff_left.symm
  have hpc := continuousOn_pcPt_launch hg.reg hst.2
  have hpc' : ContinuousOn (fun s => Nc.bPc κ b jumps E ℓ ω (τ + s))
      {s : ℝ≥0 | (s : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 - τ} :=
    hpc.comp (continuous_const.add continuous_id).continuousOn fun s hs => by
      show ((τ + s : ℝ≥0) : ℝ≥0∞) ≤ _
      rw [ENNReal.coe_add]; exact (ENNReal.le_sub_iff_add_le_left ENNReal.coe_ne_top hτL.le).1 hs
  have hdr := hdrω hωF
  have hhead := hhdω hωF
  -- B's stage chart and stage trace
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hst.2
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hl'
  obtain ⟨-, gc, C, hD, -, -, -, -, -, -, hgct, hgC⟩ :=
    S3.Canon.runChart_package (κ := κ) (b := b) (jumps := jumps) _
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) hg.reg ℓ hnd
  have hbl : ∀ x : ℝ, ∃ y : ℂ, Tendsto (Mn.walkStageChart κ b jumps E ℓ ω).2.1 (𝓝[H] (x : ℂ)) (𝓝 y) := fun x =>
    ⟨gc x, hgct x (by simp [Hbar])⟩
  have hPR := LuM.pieceRegular_of_launch hg.reg hst.2
  have hα := LuM.isGeneratingTrace_trOf hPR
  have hβH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      0 ≤ (LuM.trOf (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) t).im :=
    fun t ht => LuM.im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  have hPH : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      0 ≤ (Nc.bPc κ b jumps E ℓ ω r).im :=
    fun r hr => im_bdVal_nonneg hD hbl (hβH r hr)
  -- the version hull at a rational B-time after the entrance
  have hpost : ∀ m, ∀ q : ℚ, τ < (q : ℝ).toNNReal → (S.ver m).a (q : ℝ).toNNReal ω < S.V m ω →
      fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) (((S.ver m).a (q : ℝ).toNNReal ω).toNNReal : ℝ) =
        fillH (Dv.canonCurve (Nc.retX κ b jumps E u l k ℓ ω) (x₀ ω)
          (fun s => Nc.bPc κ b jumps E ℓ ω (τ + s)) ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 - τ) ''
          Icc 0 (Nc.uOf ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 - τ)
            (((q : ℝ).toNNReal - τ : ℝ≥0) : ℝ))) := by
    intro m q hτq hq
    have hq' : (S.ver m).a (q : ℝ).toNNReal ω < (S.ver m).Λ v₀ ω := by rw [hΛ m]; exact hq
    have hal := halω m q v₀ hv₀T hcell hq'
    have hH' := hhω m q v₀ hv₀T hcell hq'
    rw [union_fillVer_eq_of hst.2 hrw hru hg.reg hc hal (hAω q).1 (hAω q).2, hfill] at hH'
    have hqτ : τ + ((q : ℝ).toNNReal - τ) = (q : ℝ).toNNReal := add_tsub_cancel_of_le hτq.le
    have hsplit : Nc.bPc κ b jumps E ℓ ω '' Icc 0 (q : ℝ).toNNReal = Nc.bPc κ b jumps E ℓ ω '' Icc 0 τ ∪
        (fun s => Nc.bPc κ b jumps E ℓ ω (τ + s)) '' Icc 0 ((q : ℝ).toNNReal - τ) := by
      conv_lhs => rw [← hqτ]
      exact image_Icc_add_split _ τ _
    have ht' : ((((q : ℝ).toNNReal - τ : ℝ≥0)) : ℝ≥0∞) <
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 - τ :=
      (hBL _).1 (by rw [hqτ]; exact hal)
    have hT : IsCompact ((fun s => Nc.bPc κ b jumps E ℓ ω (τ + s)) '' Icc 0 ((q : ℝ).toNNReal - τ)) :=
      isCompact_Icc.image_of_continuousOn (hpc'.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans ht'.le)
    have hTH : ∀ z ∈ Nc.retX κ b jumps E u l k ℓ ω ∪
        (fun s => Nc.bPc κ b jumps E ℓ ω (τ + s)) '' Icc 0 ((q : ℝ).toNNReal - τ), 0 ≤ z.im := by
      rintro z (hz | ⟨r, hr, rfl⟩)
      · exact hH z hz
      · refine hPH _ ?_
        have := (hBL r).2 ((ENNReal.coe_le_coe.2 hr.2).trans_lt ht')
        exact this.le
    rw [hsplit, ← union_assoc, fillH_union_of_subset_fill_real (hc.union hT) hTH hhead] at hH'
    exact fwdHull_eq_canon_of_hull hc hhull hL' hpc' hdr ht' hH'
  obtain ⟨he1, he2⟩ := ident_canon_shift hdr hL' (τ := τ) (Wm := fun m t => (S.ver m).W t ω)
    (am := fun m t => (S.ver m).a t ω) (V := fun m => S.V m ω) (relLife := relLife ω)
    (fun m => (S.ver m).W_cont ω) (fun m => (S.ver m).W_zero ω) (fun m => (S.ver m).clock_cont ω)
    (fun m => (S.ver m).clock_mono ω)
    (fun m => eq_zero_at_of_rat ((S.ver m).clock_cont ω) hτ.le
      fun q hq => hz0ω m q hωF hq)
    (hsup hωF) hpost
    (fun m q hτq hq => by
      have hq' : (S.ver m).a (q : ℝ).toNNReal ω < (S.ver m).Λ v₀ ω := by rw [hΛ m]; exact hq
      exact (hBL _).1 (by rw [add_tsub_cancel_of_le hτq.le]; exact halω m q v₀ hv₀T hcell hq'))
    (fun m q hq => hrω m q v₀ hv₀T hcell (by rw [hΛ m]; exact hq))
    (fun q hτq hq => hclω q hωF (by rw [← add_tsub_cancel_of_le hτq.le]; exact (hBL _).2 hq))
    (e := Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω) (Mz.isRegularDriver_driverOf h12p hκ _ _)
    (fun m => (hk2 hωF).1 m) (hk2 hωF).2
  exact chainFacts_root_at h12p hκ E u l k ℓ hKc hKp hst.2 hD (Mz.isNormalized_walkStageChart hg.reg ℓ) hgct hgC
    hc hhull hH hfill hτL hhead hpc hdr hα.2.1 hβH he1 he2 (hcω hωF)

end InteractingSLE.Theorem14.SB.Cz
