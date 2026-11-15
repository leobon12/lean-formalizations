/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QrHull
import InteractingSLE.Spec.Supplement.SB2MsF3
import InteractingSLE.Spec.Restart.FCLocality

/-!
# D5's F3 at one stage of the lower walk: the retained mean from the retained kernel law

Worker REVIEW-FABLE-T14 (proving phase; orchestrator adjustment: D5's F3, `hind₁` of SB2(2)'s conditional half).

`Ms.SB2LowerRetainedMeanStatement` (`SB2MsF3`) asks, at every stage `ℓ` of the lower walk B, for a word `β₁` whose
mean, read in the canonical hull chart of the retained union `A₁ = fill(A ∪ B_{<ℓ})`, is the local-set mean of `A₁`.
The content of that statement is the **retained kernel law** at stage `ℓ`: conditionally on the completed retained
past, the field read in the canonical hull chart is a free field with the boundary data of `β₁`. This is the invariant
of the stage induction (the two-history analogue of `Exist.StagedLaw.IsStageWitness`); the single-stage law
`Exist.StagedLaw.IsStopLaw` at the stage's lifetime carries it from one stage to the next, once that stage's piece is
identified as a conditional flow line (the conditional half at that stage).

* `marksC`: the completed retained past `mΩ ⊓ aeSigma (Ms.stageMarks …) P`;
* `RetainedLawAt`: the retained kernel law at stage `ℓ` for a version `A₁` and a word `β₁`: a retained hull `K`
  (compact, connected to the real line, dyadic-hit measurable for the completed past, `fill K = A₁` on a good event
  containing the stage event), a chart offset `x₀`, a measurable chart field `Y` and the kernel law of `Y` with a
  word `β`, `β₁` being `β` shifted by `−x₀`;
* **`ae_eqOn_retainedMean_of_retainedLaw`**: at a flow stage `ℓ`, the retained kernel law gives the body of
  `Ms.SB2LowerRetainedMeanStatement` for `(ℓ, τ, A₁, β₁)` and every local-set mean of `A₁`;
* `SB2LowerRetainedLawStatement` (named statement: the retained kernel law at every stage) and
  **`sb2LowerRetainedMeanStatement_of_law`**: it gives `Ms.SB2LowerRetainedMeanStatement`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qr

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Sec4 Supp9B Lx

/-- **The completed retained past at the start of B's stage `ℓ`**: `Ms.stageMarks` completed by the null sets inside
the ambient σ-algebra. -/
abbrev marksC (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) : MeasurableSpace Ω :=
  mΩ ⊓ aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P

theorem marksC_le (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) :
    marksC κ b jumps P E u l k ℓ ≤ mΩ := inf_le_left

/-- **The retained kernel law at B's stage `ℓ`**, for a version `A₁` of the retained union and a word `β₁`: there are
a retained hull `K` — compact and connected to the real line at every sample, observed through its dyadic hits by the
completed retained past — a good event `G` of the completed retained past containing the stage event almost surely,
on which `fill K = A₁`, a chart offset `x₀` measurable for the completed retained past, a word `β`, sorted on `G`,
with `β₁ = β` shifted by `−x₀` on `G`, and a measurable field `Y`, on `G` the field read in the canonical hull chart
`Mo.hullChart (fill K) x₀`, whose regular conditional law given the completed retained past has, on `G`, the boundary
data of `β`. -/
def RetainedLawAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)
    (A₁ : Ω → Set ℂ) (β₁ : Ω → BoundaryWord) : Prop :=
  ∃ (K : Ω → Set ℂ) (G : Set Ω) (x₀ : Ω → ℝ) (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
    @IsDyadicHitMeasurable Ω (marksC κ b jumps P E u l k ℓ) K ∧ (∀ ω, IsCompact (K ω)) ∧
    (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧
    MeasurableSet[marksC κ b jumps P E u l k ℓ] G ∧
    (∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ → ω ∈ G) ∧
    (∀ᵐ ω ∂P, ω ∈ G → fillH (K ω) = A₁ ω) ∧
    Measurable[marksC κ b jumps P E u l k ℓ] x₀ ∧
    (∀ᵐ ω ∂P, ω ∈ G → (β ω).IsSorted ∧ β₁ ω = BoundaryWord.shiftW (-(x₀ ω)) (β ω)) ∧ Measurable Y ∧
    (∀ᵐ ω ∂P, ω ∈ G →
      IsChartTransport (Mo.hullChart (fillH (K ω)) (x₀ ω)) 1 0 (chiC κ) (h ω) (Y ω)) ∧
    ∀ᵐ ω ∂P, ω ∈ G →
      IsGFFWithBoundaryData (condExpKernel P (marksC κ b jumps P E u l k ℓ) ω) Y (β ω).fn (β ω).jumps

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **F3 at a flow stage from the retained kernel law** (the body of `Ms.SB2LowerRetainedMeanStatement`). In SB2(2)'s
setting, at a flow stage `ℓ` of the lower walk, for every cap `τ` and every hitting-measurable version `A₁` of the
line family's retained set `fill(A ∪ B_{<ℓ})`: if the retained kernel law holds for `A₁` and a sorted word `β₁`, then
for every local-set mean `g₁` of `A₁` (centred field), almost surely on the stage event, every harmonic
representative `w₁` of `g₁` off `A₁` satisfies `w₁ + u₀ = (β₁ ω).mean ∘ g_{A₁} − χ(κ) · Im (canonDerivLog A₁)` on
`ℍ ∖ A₁`. -/
theorem ae_eqOn_retainedMean_of_retainedLaw (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    {t : ℝ≥0∞} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), t)))
    (τ : ℝ≥0∞) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A₁ : Ω → Set ℂ} (hA₁ : Measurable[mΩ, hittingSigma] A₁)
    (hA₁e : ∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω)
    {β₁ : Ω → BoundaryWord} (hlaw : RetainedLawAt κ b jumps P h E u l k ℓ A₁ β₁)
    {g₁ : Ω → DistOn upperHalfPlaneOpens} (hg₁ : IsLocalSetMean A₁ (centredField h u₀) P g₁) :
    ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
        EqOn (fun z => w₁ z + u₀ z)
          (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ ω) 0).2.2 z)
          (H \ A₁ ω) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hcap := isStagedHistory_capSpec (τ := τ) hb (hE' _ hw) (hreg' _) hℓ hwℓ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hA1, ho1, -, hloc1⟩ :=
    Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _) hu₀ k ℓ
  have h𝓜₁ : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ≤ mΩ :=
    sup_le (hup.2.1 k) (hcap.2.1 ℓ)
  obtain ⟨B₁, hB₁m, hB₁c, hB₁ae, hB₁loc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜₁⟩
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho1 hA1 hloc1
  obtain ⟨-, hFc, hFloc, -⟩ := fillVer_package hh0 h𝓜₁ hB₁c hB₁m hB₁loc
  have hAF : ∀ᵐ ω ∂P, fillVer B₁ ω = A₁ ω := by
    filter_upwards [hA₁e, hB₁ae] with ω h1 h2
    rw [h1]
    unfold fillVer
    rw [h2]
  have hmark₁ := WalkLaw.isHistoryAvoidanceLocal_congr_ae hAF hFloc
  have hpast : pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
      (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ =
      pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ :=
    pastSigma_capSpec_of_le hℓ.le _ le_rfl
  rw [hpast] at hmark₁
  have hmark₂ : IsHistoryAvoidanceLocal (Ms.stageMarks κ b jumps E u l k ℓ) A₁ (centredField h u₀) P := hmark₁
  have hmark : IsHistoryAvoidanceLocal (marksC κ b jumps P E u l k ℓ) A₁ (centredField h u₀) P :=
    Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma hmark₂
  have hAc : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω) := by
    filter_upwards [hAF] with ω he
    rw [← he]
    exact hFc ω
  have hloc : IsLocalSet A₁ (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hA₁ hAc).out 4 1).2 hmark₂.isAvoidanceLocal
  obtain ⟨K, G, x₀, β, Y, hK, hKc, hKp, hG, hGe, hAK, hx₀, hβ, hY, htr, hl⟩ := hlaw
  have hm := ae_eqOn_hullMean_of_kernelWord (marksC_le κ b jumps P E u l k ℓ) hK hKc hKp hx₀ hh hu₀ hY hG
    (hβ.mono fun ω hω hGω => (hω hGω).1) htr hl hA₁ hloc hmark hAK hg₁
  filter_upwards [hm, hGe, hβ] with ω hmω hGω hβω hs
  rw [(hβω (hGω hs)).2]
  exact hmω (hGω hs)

/-! ### The closed form -/

/-- **Named statement: the retained kernel law of SB2(2)'s lower walk at every stage** — the hypothesis under which
`Ms.SB2LowerRetainedMeanStatement` holds (`sb2LowerRetainedMeanStatement_of_law`). In SB2(2)'s setting (the premises
of `Lf.SB2LowerSetting`), for every stage `ℓ`, every cap `τ` and every hitting-measurable version `A₁` of the line
family's retained set `fill(A ∪ B_{<ℓ})`, there is a sorted boundary word `β₁`, measurable for the completed retained
past, with the retained kernel law `RetainedLawAt`. It is the invariant of the stage induction: at stage `0` it is the
upper walk's stage witness, and stage `ℓ`'s conditional half with the single-stage law at the stage's lifetime
(`Exist.StagedLaw.IsStopLaw`) gives it at the next launching stage. -/
def SB2LowerRetainedLawStatement : Prop :=
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
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
    ∀ (ℓ : ℕ) (τ : ℝ≥0∞) (A₁ : Ω → Set ℂ), Measurable[mΩ, hittingSigma] A₁ →
      (∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω) →
      ∃ β₁ : Ω → BoundaryWord,
        Measurable[aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] β₁ ∧ Measurable β₁ ∧ (∀ ω, (β₁ ω).IsSorted) ∧
        RetainedLawAt κ b jumps P h E u l k ℓ A₁ β₁

/-- **F3 from the retained kernel law** (Theorems 1.2–1.3): `Ms.SB2LowerRetainedMeanStatement`, the form SB2(2)'s
kernel half consumes, holds once the retained kernel law holds at every stage. A stage `ℓ` at which the lower walk
launches at some sample is a flow stage of the walk's program; at any other stage the stage event is empty. -/
theorem sb2LowerRetainedMeanStatement_of_law (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hlaw : SB2LowerRetainedLawStatement.{u}) : Ms.SB2LowerRetainedMeanStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hW' hζ' E hE hER u l k hu hl hlθ hL hleft ℓ τ u₀ hu₀ A₁ hA₁ hA₁e
  obtain ⟨β₁, hβa, hβm, hsort, hL'⟩ :=
    hlaw κ hκ hκ4 b jumps hb P h hh W' ζ' hW' hζ' E hE hER u l k hu hl hlθ hL hleft ℓ τ A₁ hA₁ hA₁e
  refine ⟨β₁, hβa, hβm, hsort, fun g₁ hg₁ => ?_⟩
  by_cases hne : (Ms.stageEvent κ b jumps E u l k ℓ).Nonempty
  · obtain ⟨ω', hω'⟩ := hne
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω'.2
    obtain ⟨hins, -, -⟩ := eq_launch_of_launches _ _ hcθ
    obtain ⟨rfl, -⟩ := WalkLeaf.boundaryWalkSpec_inl hins
    obtain ⟨hℓ, -⟩ := List.getElem?_eq_some_iff.1 hins
    exact ae_eqOn_retainedMean_of_retainedLaw h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hins τ hu₀ hA₁ hA₁e hL' hg₁
  · exact Eventually.of_forall fun ω hω => absurd ⟨ω, hω⟩ hne

end InteractingSLE.Theorem14.SB.Qr
