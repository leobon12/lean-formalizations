/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ChWit
import InteractingSLE.Spec.Supplement.SB2FmBase

/-!
# The root's canonical objects and the root-word identity (D55)

Packet PROVE-SB2-CONDFIN, round 11 (decision D55). The determination of SB2(2)'s relative root
(`Ch.SB2LowerRootDetWStatement`) consumes, at every B-stage `ℓ` (the root sits at `ℓ = relOff`):

* **`PosRootAt ℓ ω`**: the relative root of `ω` is at B's stage `ℓ` and has positive lifetime (B launches at `ℓ`,
  `R` has entered by stage `ℓ`, the offset is `ℓ`, and piece `ℓ` lives past the entrance time `shiftD 0`);
* **`RootCover ℓ G`**: `G` contains almost every positive root at `ℓ`;
* **`RootWordAt G c`** (F3LAW's identity, D55): under the upper kernel at almost every upper launch, the word `c` is
  almost surely on `G` one constant word `w`, and `w` is a data word of the relative field `affField m h'` (the
  data `b'` read with the shift `m`). Literal equality with a chosen word of `(b', J')` cannot be asked: the setting's
  `(b', J')` is any data of the relative field's law, so `J'` may contain points where `b'` does not jump;
* **`BaseLawFor ℓ β₁`**: F3LAW's base law at stage `ℓ` (`Fm.SB2LowerBaseLawMvStatement`'s conclusion) for the word
  `β₁`, for every line family of the stage;
* **`SB2LowerRootIdentStatement`** (CANON's step 3, D51 item 5, in the consumer form): for every base word, canonical
  root objects with the word `shiftW x₀ β₁`, covering the positive roots, with `Mz.CanonIdentOn`;
* **`SB2LowerRootWordStatement`** (for F3LAW, D55): a base word with its base law such that the word read with the
  offset of any such canonical objects satisfies `RootWordAt`;
* `SB2LowerRootCanonStatement`: the two combined (proved from them in `SB2CtRoot`).

R48: no source theorem is assumed; these are named statements for Theorem 1.4's SB2(2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ct

open Restart Exist Exist.Staged Exist.StagedLaw Lu Mx FlowDilate

section Defs

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ) (jumps : Finset ℝ)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0))
  (k : ℕ)

/-- **A positive relative root at B's stage `ℓ`**: B launches at `ℓ`, `R` has entered by stage `ℓ`, the offset is
`ℓ`, and B's piece `ℓ` lives past the entrance time. -/
def PosRootAt (ℓ : ℕ) (ω : Ω) : Prop :=
  (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (Mz.lowerD b jumps E ω)
      (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
  Cf.RootEv κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (Mz.lowerD b jumps E ω) ℓ ∧
    (Mz.lowerD b jumps E ω ℓ).2 - (Lk.shiftD κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (Mz.lowerD b jumps E ω) 0 : ℝ≥0∞) ≠ 0

/-- **`G` covers the positive roots at `ℓ`.** -/
def RootCover (ℓ : ℕ) (G : Set Ω) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k → PosRootAt (κ := κ) b jumps E u l k ℓ ω → ω ∈ G

/-- **The root-word identity for the objects `(G, c)`** (F3LAW's, D55): under the upper kernel at almost every
upper launch, for every relative datum of the setting, `c` is almost surely on `G` a constant word `w`, which is a
data word of the relative field. -/
def RootWordAt (G : Set Ω) (c : Ω → BoundaryWord) : Prop :=
  ∀ᵐ ω₀ ∂P, ∀ (c₀ : Chart) (θ : ℝ),
    (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k = some (c₀, θ) →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens), IsPiecewiseConstantBoundaryData b' J' →
      (∀ ω, IsChartTransport c₀ 1 0 (chiC κ) (h ω) (h' ω)) →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
        h' b' J' →
      ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
      ∃ w : BoundaryWord,
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
          (fun ω => affField m one_pos (h' ω)) w.fn w.jumps ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀), ω ∈ G → c ω = w

/-- **F3LAW's base law at B's stage `ℓ` for the word `β₁`** (`Fm.SB2LowerBaseLawMvStatement`'s conclusion with the
word named): `β₁` is measurable for the upper past, and for every line family of the stage (`𝓖 t` the upper past
with B's past capped at `t` through `ℓ + 1`, `A₁ t` the filled retained union) the retained law holds with word `β₁`
on an event covering `stageEvent ℓ ∩ {ℓ ≤ relOff}`. -/
def BaseLawFor (ℓ : ℕ) (β₁ : Ω → BoundaryWord) : Prop :=
  Measurable[pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k] β₁ ∧
  ∀ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ),
    (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω) →
    ∃ (K : Ω → Set ℂ) (G : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ),
      Fl.MvLaw κ (Ms.lineFiltC P 𝓖 0) P h (A₁ 0) K G Y β₁ M ∧
      ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ G

/-- **The canonical objects of the relative root at B's stage `ℓ`, with the root-word identity.** -/
def RootCanonAt (ℓ : ℕ) : Prop :=
  ∃ (G : Set Ω) (c : Ω → BoundaryWord) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)),
    RootCover (κ := κ) b jumps P E u l k ℓ G ∧ Mz.CanonIdentOn h12p hκ b jumps P h E u l k ℓ G c K x₀ Dr hKc hKp ∧
      RootWordAt (κ := κ) b jumps P h E u l k G c

end Defs

/-- **Named statement (CANON's step 3 at the root, D51 item 5; consumer form).** In SB2(2)'s setting, at every
B-stage `ℓ` and for every base word `β₁` with F3LAW's base law, canonical root objects covering the positive roots at
`ℓ`, with the identification clause `Mz.CanonIdentOn` for the word `shiftW x₀ β₁`. -/
def SB2LowerRootIdentStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k → ∀ (ℓ : ℕ) (β₁ : Ω → BoundaryWord), BaseLawFor (κ := κ) b jumps P h E u l k ℓ β₁ →
        ∃ (G : Set Ω) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
          (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)),
          RootCover (κ := κ) b jumps P E u l k ℓ G ∧
          Mz.CanonIdentOn h12p hκ b jumps P h E u l k ℓ G (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) K x₀ Dr
            hKc hKp

/-- **Named statement (for F3LAW, D55): the base word with the root-word identity.** In SB2(2)'s setting, at every
B-stage `ℓ`, a base word `β₁` with F3LAW's base law such that, for every canonical root object family with the word
`shiftW x₀ β₁` (covering the positive roots at `ℓ`, with `Mz.CanonIdentOn`), that word satisfies `RootWordAt`. -/
def SB2LowerRootWordStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k → ∀ ℓ : ℕ, ∃ β₁ : Ω → BoundaryWord, BaseLawFor (κ := κ) b jumps P h E u l k ℓ β₁ ∧
        ∀ (G : Set Ω) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
          (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)),
          RootCover (κ := κ) b jumps P E u l k ℓ G →
          Mz.CanonIdentOn h12p hκ b jumps P h E u l k ℓ G (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) K x₀ Dr
            hKc hKp →
          RootWordAt (κ := κ) b jumps P h E u l k G (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))

/-- **The canonical root objects with the root-word identity at every B-stage** (the two statements above combined). -/
def SB2LowerRootCanonStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k → ∀ ℓ : ℕ, RootCanonAt h12p hκ b jumps P h E u l k ℓ

/-- **CANON's step 3 and F3LAW's identity give the combined root objects.** -/
theorem sb2LowerRootCanonStatement_of_ident_word (h12p : Theorem12ParamStatement.{u})
    (hI : SB2LowerRootIdentStatement.{u} h12p) (hW : SB2LowerRootWordStatement.{u} h12p) :
    SB2LowerRootCanonStatement.{u} h12p := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ
  obtain ⟨β₁, hbase, hword⟩ := hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ
  obtain ⟨G, K, x₀, Dr, hKc, hKp, hcov, hid⟩ :=
    hI κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ β₁ hbase
  exact ⟨G, _, K, x₀, Dr, hKc, hKp, hcov, hid, hword G K x₀ Dr hKc hKp hcov hid⟩

end InteractingSLE.Theorem14.SB.Ct
