/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuVer2
import InteractingSLE.Spec.Supplement.SB2OmCfg
import InteractingSLE.Spec.Supplement.SB2MiCap
import InteractingSLE.Spec.Supplement.SB2JtRule
import InteractingSLE.Spec.Supplement.SB2LjRule

/-!
# F2b′'s successor: the live event by the intrinsic positive lifetime, and the S2 clause (D28, D31)

Packet PROVE-AUX61-NOJUMP (round 20). **`Na.SB2LowerStageVersionStatement3`** is `Mu.SB2LowerStageVersionStatement2`
(PROVE-SB2-LCMEAN's F2b′) with two changes:

* **D31 (option (R)).** The live event `F` is characterized by the intrinsic positive lifetime of B's piece `ℓ` at
  the tail stages, `F ↔ stageEvent ℓ ∧ relOff < ℓ ∧ 0 < (E walk ℓ ω).2`, instead of `0 < relLife` (an existential
  output, which let `F = ∅` satisfy the old form; `DECISIONS-FABLE-5.md`). The root `ℓ = relOff` goes to the root
  variant.
* **D28 (option (D)).** A fourth clause on the versions: at every B-time `t` with `0 < a t < Λ`, almost surely on the
  seed cell, GEOM2's S2 record `Om.IsStageS2` of the canonical chart in B's (reflected) stage coordinates, with B's
  stage chart `Mi.sb2StageChart … ℓ`, B's stopped driver `Mi.sb2StopDrv … ℓ t` and stop time `Mi.sb2StopTime … ℓ t`
  (the objects of `Mk.ae_isStagePullback_fill_adm` and `Mi.exists_capMean_hind`), the version's driver and clock.
  This is the exact hypothesis `hS2` of `Om.hmean_of_stageS2` (at `ψ = −π/2`).

* **The trace clause at the chart's domain.** `Ms.StageVersionG.trace` asks `ηr (a s) = Φ.1 (pc s)` at every B-time
  `s ∈ [t_L, t]`. At `s = t_L` the trace is `ηr 0 = 0`, so `Φ.1 (pc t_L) = mapOut (fill K) (pc t_L) − x₀` must vanish
  at the piece's start, a real point off `ℍ ∖ fill K`, where `ConformalImage.mapOut` is an opaque `Classical.choose`
  value (`IsMapOut` constrains it only on `ℍ ∖ fill K`). No choice of `pc`, `t_L`, `x₀` avoids this when `L = ∞`, so
  that field cannot be proved. The structures `Na.StageVersionG`, `Na.StageVersionS` below are LCMEAN's with the
  trace clause asked at the times where `pc s` is in the chart's domain (`(Φ ω).dom = ℍ ∖ fill K`); every other field
  is verbatim. No landed consumer uses `trace` (`Mu`, `Mt`, `Om`, `Qw` use `hull`, `safeS/L`, `reach`, `reg`, `ann`,
  `V_sup`, `Λ_le`), so consumers move to the new structures by retyping.

Everything else is verbatim. PROVE-SB2-LCMEAN consumes this statement (D31).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Na

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms

/-! ### The version structures, with the trace clause at the chart's domain -/

section Version

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **One relative version at stage `ℓ` with lifetime `Λ`** (`Ms.StageVersionG` with the trace clause asked only at the
times when the piece is in the chart's domain; the SB2(2) analogue of `Lv.SB2LineVersionG`). Parameters:
the live event `F`, the line filtration `𝓖`, the line sets `A₁`, `A₂ t`, the relative chart family `Φ`, the word `β₁`
and its countable set of types, B's stage-`ℓ` physical piece `pc` (B's time), its tail start `tL` and B's lifetime
`L` of the stage. -/
structure StageVersionG (κ ψ : ℝ) (P : Measure Ω) (F : Set Ω) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ)
    (A₂ : ℝ≥0 → Ω → Set ℂ) (Φ : Ω → Chart) (β₁ : Ω → BoundaryWord) (types : Set WordType)
    (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (L : Ω → ℝ≥0∞) where
  𝓗 : Filtration ℝ≥0 mΩ
  W : ℝ≥0 → Ω → ℝ
  a : ℝ≥0 → Ω → ℝ≥0∞
  Λ : WordType → Ω → ℝ≥0∞
  marks_le : lineFiltC P 𝓖 0 ≤ 𝓗 0
  W_zero : ∀ ω, W 0 ω = 0
  W_cont : ∀ ω, Continuous fun t => W t ω
  W_adapted : StronglyAdapted 𝓗 W
  clock_cont : ∀ ω, Continuous fun t => a t ω
  clock_mono : ∀ ω, Monotone fun t => a t ω
  clock_zero : ∀ ω, a 0 ω = 0
  clock_meas : ∀ t, Measurable[lineFiltC P 𝓖 t] (a t)
  timeChange : ∀ (q : ℝ≥0) (D' : Set Ω), MeasurableSet[𝓗 q] D' → ∀ t,
    MeasurableSet[lineFiltC P 𝓖 t] (D' ∩ {ω | (q : ℝ≥0∞) ≤ a t ω})
  reach : ∀ w ∈ types, ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → (q : ℝ≥0∞) < Λ w ω →
    ∃ t, (q : ℝ≥0∞) ≤ a t ω
  reg : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
    Aux79.IsForceReg W (geomLW W (cellXL κ ψ β₁ w)) (geomRW W (cellXR κ ψ β₁ w)) (Λ w) ω
  safeS : ∀ w ∈ types, ∀ (φ : TestOn upperHalfPlaneOpens) t, MeasurableSet[lineFiltC P 𝓖 t]
    {ω | a t ω < Λ w ω ∧ Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  safeL : ∀ w ∈ types, ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[lineFiltC P 𝓖 t]
    {ω | a t ω < Λ w ω ∧ Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  hull : ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → a t ω < Λ w ω →
    H \ (A₁ t ω ∪ A₂ t ω) = (Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)
  trace : ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → a t ω < Λ w ω →
    ∃ ηr : ℝ → ℂ, IsLoewnerTrace (fun s : ℝ => W s.toNNReal ω) ηr ∧
      ∀ s : ℝ≥0, s ≤ t → tL ω ≤ s → pc ω s ∈ ((Φ ω).dom : Set ℂ) → ηr (a s ω).toReal = (Φ ω).1 (pc ω s)
  alive : ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → a t ω < Λ w ω → (t : ℝ≥0∞) < L ω
  Λ_le : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
    Λ w ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ β₁ w) (cellXR κ ψ β₁ w) ω

/-- **SB2(2)'s relative versions at announced stops** (`Ms.StageVersionS` over `Na.StageVersionG`; the SB2(2) analogue
of `Lv.SB2LineVersionS`, D4/D10): for every
`m` a version `ver m` whose lifetimes are all the stop `V m`; the stop is a record-path rule of a record measurable for
the stage's initial σ-algebra, announced on the live event by finite nondecreasing rules, strictly below the relative
lifetime `relLife`, and the stops increase to `relLife`. -/
structure StageVersionS (κ ψ : ℝ) (P : Measure Ω) (F : Set Ω) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ)
    (A₂ : ℝ≥0 → Ω → Set ℂ) (Φ : Ω → Chart) (β₁ : Ω → BoundaryWord) (types : Set WordType)
    (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (L : Ω → ℝ≥0∞) (relLife : Ω → ℝ≥0∞) where
  ver : ℕ → StageVersionG κ ψ P F 𝓖 A₁ A₂ Φ β₁ types pc tL L
  V : ℕ → Ω → ℝ≥0∞
  record : Ω → RecData
  record_meas : Measurable[lineFiltC P 𝓖 0] record
  ρ : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρs : ℕ → ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρ_meas : ∀ m, Measurable (ρ m)
  ρ_rule : ∀ m, Supp8.GB6.HullId.IsPathRule (ρ m)
  ρs_meas : ∀ m n, Measurable (ρs m n)
  ρs_rule : ∀ m n, Supp8.GB6.HullId.IsPathRule (ρs m n)
  ρs_fin : ∀ m n x, ρs m n x ≠ ⊤
  ρs_mono : ∀ m x, Monotone fun n => ρs m n x
  Λ_eq : ∀ m w, (ver m).Λ w = V m
  V_eq : ∀ m ω, V m ω = ρ m (record ω, fun s => (ver m).W s ω)
  ann : ∀ m, ∀ᵐ ω ∂P, ω ∈ F → (∀ n, ρs m n (record ω, fun s => (ver m).W s ω) < V m ω) ∧
    ⨆ n, ρs m n (record ω, fun s => (ver m).W s ω) = V m ω
  V_lt : ∀ m, ∀ᵐ ω ∂P, ω ∈ F → V m ω < relLife ω
  V_mono : ∀ ω, Monotone fun m => V m ω
  V_sup : ∀ᵐ ω ∂P, ω ∈ F → ⨆ m, V m ω = relLife ω
  W_eq : ∀ m m', m ≤ m' → ∀ᵐ ω ∂P, ω ∈ F → ∀ t : ℝ≥0, (t : ℝ≥0∞) < V m ω →
    (ver m).W t ω = (ver m').W t ω

end Version

/-- **Named statement (F2b′'s successor; PROVE-AUX61-NOJUMP's, decisions D28 and D31).**
`Mu.SB2LowerStageVersionStatement2` with the live event characterized by `0 < (E walk ℓ ω).2` at the tail stages
`relOff < ℓ`, and with the S2 record `Om.IsStageS2` at every B-time of positive clock below the stop, almost surely on
the seed cell. -/
def SB2LowerStageVersionStatement3 : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
    ∀ (ℓ : ℕ) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ) (A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω ∧
        A₂ t ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
            (ℓ + 1)) ω) →
    ∀ (ψ : ℝ) (β₁ : Ω → BoundaryWord) (types : Set WordType),
      Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁ → (∀ ω, (β₁ ω).IsSorted) → types.Countable →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
      (∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
              (H \ A₁ 0 ω)) →
    ∃ (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (relLife : Ω → ℝ≥0∞) (F : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧ (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) ∧
      Measurable[lineFiltC P 𝓖 0] x₀ ∧ MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)) ∧
      ((∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types) →
        ∃ S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
          (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
          (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife,
          (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
            (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
            ∃ m, (S.ver m).a t ω < S.V m ω) ∧
          (∀ m, ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
            S.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver m).W
              (cellXL κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
              (cellXR κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω) ∧
          (∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
            ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w → relLife ω < ⊤ →
              (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
              FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
                (cellXR κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω ≤ relLife ω) ∧
          (∀ m, ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
            ω ∈ seedCell κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
            (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω →
            Om.IsStageS2 (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω)
              (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω) (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
              (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω) (fun s : ℝ => (S.ver m).W s.toNNReal ω)
              ((S.ver m).a t ω).toNNReal))

/-! ### The root variant (LCMEAN's handoff R14.4 item 5, option (A); D31) -/

section Root

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
  (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)

/-- **B's entrance time at the root**: the first time B's piece `ℓ` visits `R = max (A ∩ ℝ)` (`Lk.visitTime`). -/
def rootEntry (ω : Ω) : ℝ≥0 :=
  Lk.visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) (realMax (upperPrefix κ b jumps E u l k ω))

/-- **The capped retained pasts** at a deterministic B-time `r` of stage `ℓ` (the line family of F2b′). -/
abbrev capPast (r : ℝ≥0) : MeasurableSpace Ω :=
  pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
    pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (r : ℝ≥0∞))
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)

end Root

/-- **Named statement (F2b′'s root variant; PROVE-AUX61-NOJUMP's, stated here since LCMEAN has not: R14.4 item 5,
option (A), and D31).** At the root `ℓ = relOff` in the piece-start case (`¬ ArcEntry`), with a tail of positive
length (`τE < ζ_ℓ`, `τE = rootEntry` B's entrance time at `R`): the conclusion of `SB2LowerStageVersionStatement3`
without the S2 clause, for the line family shifted to the entrance time — `𝓖 t` is the σ-algebra of the capped
retained pasts stopped at the random B-time `τE + t` (`s ∈ 𝓖 t ↔ ∀ r, s ∩ {τE + t ≤ r} ∈ capPast r`), and `A₂ t` is B's
piece `ℓ` capped at `τE + t`. The retained word and its mean identity are those at the stage start, as at the tail
stages (the piece's head before `R` lies in the retained fill). -/
def SB2LowerRootVersionStatement3 : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
    ∀ (ℓ : ℕ) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ) (A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ (t : ℝ≥0) (s : Set Ω), MeasurableSet[𝓖 t] s ↔ ∀ r : ℝ≥0,
        MeasurableSet[capPast κ b jumps E u l k ℓ r] (s ∩ {ω | ((rootEntry κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) +
          (t : ℝ≥0∞) ≤ (r : ℝ≥0∞)})) →
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω ∧
        A₂ t ω = fillVer (fun ω => WalkLaw.stageSet κ b jumps
            (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
              (((rootEntry κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) + (t : ℝ≥0∞)))
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω) ω) →
    ∀ (ψ : ℝ) (β₁ : Ω → BoundaryWord) (types : Set WordType),
      Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁ → (∀ ω, (β₁ ω).IsSorted) → types.Countable →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
      (∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
              (H \ A₁ 0 ω)) →
    ∃ (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (relLife : Ω → ℝ≥0∞) (F : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧ (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) ∧
      Measurable[lineFiltC P 𝓖 0] x₀ ∧ MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
        ¬ Lk.ArcEntry κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
        ((rootEntry κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)) ∧
      ((∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types) →
        ∃ S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
          (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
          (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife,
          (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
            (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
            ∃ m, (S.ver m).a t ω < S.V m ω) ∧
          (∀ m, ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
            S.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver m).W
              (cellXL κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
              (cellXR κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω) ∧
          (∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
            ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w → relLife ω < ⊤ →
              (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
              FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
                (cellXR κ ψ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω ≤ relLife ω))

end InteractingSLE.Theorem14.SB.Na
