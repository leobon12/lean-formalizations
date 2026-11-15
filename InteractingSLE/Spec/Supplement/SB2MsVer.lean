/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MsF3
import InteractingSLE.Spec.Supplement.SB2MqIface
import InteractingSLE.Spec.Supplement.SB2DrvLineIfaceR
import InteractingSLE.Spec.Supplement.GB6HullIdRule

/-!
# D5's F2b: SB2(2)'s per-stage relative version at announced stops (for PROVE-AUX61-NOJUMP)

Packet PROVE-SB2-LCMEAN, round 12 (ruling R120, D5 item F2b: "LCMEAN states it now; NOJUMP proves it after SB2(1)'s
version half"). The SB2(2) analogue of SB2(1)'s line version at announced stops (`Lv.SB2LineVersionG`,
`SB2LineVersionS`, decisions D4/D10): per actual stage `ℓ` of the lower walk B, the image of B's piece `ℓ` (from its
tail start) under the canonical relative chart is read as a Loewner chain with a measurable driver, a clock in B's own
time, a time-change filtration, `reach`, force regularity and the safe events, stopped strictly below the relative
lifetime at record-path rules announced by finite ones.

**Objects (all at the `P` level, B's stage `ℓ` fixed).**
* the line family of `Ml.exists_sb2LineFamily_cf`: the line filtration `𝓖 t` (upper past ⊔ lower past capped at B's
  time `t` in stage `ℓ`) and the sets `A₁ t` (retained union before stage `ℓ`) and `A₂ t` (B through stage `ℓ` capped at
  `t`); the version uses the completed filtration `lineFiltC 𝓖 t = mΩ ⊓ aeSigma (𝓖 t) P`;
* the canonical relative chart `Mo.hullChart (fillH (K ω)) (x₀ ω)` for a compact hull `K` with `fill K = A₁ 0` on the
  live event (D5's F2, round 11's `Mo.retHull`; `x₀` places B's stage-`ℓ` launch point at `0`);
* F3's word `β₁` (`Ms.SB2LowerRetainedMeanStatement`), whose types partition the live event into cells.

**The structures.**
* `StageVersionG`: one version with lifetime `Λ` — the fields of `Lv.SB2LineVersionG` with the chain clause replaced
  by the **hull identity** of K2's line form (`BW1Lines.hasSafeMembers_life_of_lineLocal`'s `hBK`):
  `ℍ ∖ (A₁ t ∪ A₂ t) = Φ⁻¹(ℍ ∖ K_{a t})` below `Λ`, together with the **trace clause** (the relative trace at clock time
  `a s` is the chart image of B's piece at `s`) and `alive`;
* `StageVersionS`: versions at announced stops `V m` (D4/D10): record-path rules `ρ m`, announced by finite rules
  `ρs m n`, `V m` strictly below the relative lifetime `relLife` and at most the threshold on every type cell.
* **`SB2LowerStageVersionStatement`** (named statement, PROVE-AUX61-NOJUMP's): in SB2(2)'s setting, at every stage `ℓ`,
  for the line family and F3's word, there are `x₀` and a `StageVersionS` on the live event `F` (stage event, tail
  stage, positive relative lifetime) whose stops increase to the relative lifetime.

The kernel half (mine) turns this, with the line family's locality and F3/`hind₂` means, into K2's (S) and (L) at every
stop (`BW1Lines.hasSafeLaw_life_of_lineKernel`, `hasSafeMembers_life_of_lineLocal`), then into the stopped code match.

R48: no source theorem is assumed; this is a named statement for Theorem 1.4's SB2(2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ms

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf

/-- The completed line filtration `t ↦ mΩ ⊓ aeSigma (𝓖 t) P` (R108's completion, as SB2(1)'s `lineFiltC`). -/
def lineFiltC {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) :
    Filtration ℝ≥0 mΩ :=
  ⟨fun t => mΩ ⊓ aeSigma (𝓖 t) P, fun _ _ hst => inf_le_inf_left _ (WalkLaw.aeSigma_mono (P := P) (𝓖.mono hst)),
    fun _ => inf_le_left⟩

section Version

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **One relative version at stage `ℓ` with lifetime `Λ`** (the SB2(2) analogue of `Lv.SB2LineVersionG`). Parameters:
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
      ∀ s : ℝ≥0, s ≤ t → tL ω ≤ s → ηr (a s ω).toReal = (Φ ω).1 (pc ω s)
  alive : ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → a t ω < Λ w ω → (t : ℝ≥0∞) < L ω
  Λ_le : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
    Λ w ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ β₁ w) (cellXR κ ψ β₁ w) ω

/-- **SB2(2)'s relative versions at announced stops** (the SB2(2) analogue of `Lv.SB2LineVersionS`, D4/D10): for every
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

/-- **Named statement (F2b; PROVE-AUX61-NOJUMP's, ruling R120/D5): SB2(2)'s per-stage relative version at announced
stops.** In SB2(2)'s setting (the premises of `Lf.SB2LowerSetting`), at every stage `ℓ` of the lower walk, for the line
family of `Ml.exists_sb2LineFamily_cf` (filtration `𝓖`, sets `A₁`, `A₂`) and every word `β₁` of F3 with a countable set
of types covering the live event, there are a compact dyadic-hit measurable retained hull `K` with `fill K = A₁ 0` on
the live event (`Mo.retHull`'s form, so that the chart family is conformal at every sample), a chart offset `x₀`
(measurable for the completed initial σ-algebra), B's stage-`ℓ` physical piece `pc` with its tail start `tL`, the
relative lifetime `relLife` (the supremum of the relative capacity of `Φ ∘ pc` after `tL`), and relative versions at
announced stops for the canonical relative chart `Mo.hullChart (fillH (K ω)) (x₀ ω)` on the live event
`F` = stage event ∩ {`ℓ` is a tail stage} ∩ {`0 < relLife`}. -/
def SB2LowerStageVersionStatement : Prop :=
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
    ∃ (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (relLife : Ω → ℝ≥0∞) (F : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧ (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) ∧
      Measurable[lineFiltC P 𝓖 0] x₀ ∧ MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ≤ ℓ ∧ 0 < relLife ω)) ∧
      ((∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (β₁ ω) ∈ types) →
        Nonempty (StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL
          (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife))

end InteractingSLE.Theorem14.SB.Ms
