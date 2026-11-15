/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsCompWire

/-!
# The two orientation inputs from the walk chronology and the walk order of component charts

Packet PROVE-WALK-WORDS. Both remaining named inputs of the walk-chart leaves combine two separate facts:

* **the walk chronology** (`WalkPieceChronologyStatement`, PROVE-T14-WALKINT's area): every complete simple flow
  parametrizing a walk traverses each recorded piece in the piece's own time order;
* for `WalkPieceDirectionStatement` (common points of the two walks): GW4's **contact order**, which is part of
  `WalkPairPathFacts` — `walkPieceDirectionStatement_of_chronology`;
* for `WalkComponentOrientationStatement` (component charts): the **walk order of component charts**
  (`WalkComponentWalkOrderStatement`, Lemma GW3's "incoming orientation", GB13a): along the right walk the landings of a
  component chart move forward along the walk as `x` increases, along the left walk backward —
  `walkComponentOrientationStatement_of_walkOrder`.

So the walk chronology is the only input shared by the two leaves, and the walk order is a statement about the
complete walks alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkWords

open WalkBdry WalkMean WalkNorm

/-- **Named input: the walk chronology.** Almost surely, every complete simple flow parametrizing a boundary walk
traverses each of its recorded pieces in the piece's own time order. Same hypotheses as `WalkPairArcDataStatement`. -/
def WalkPieceChronologyStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkInf.WalkPairPathFacts κ b jumps E ω) →
      (∀ᵐ ω ∂P, WalkPiecesSimple κ b jumps E ω) →
      ∀ᵐ ω ∂P,
        (∀ γ : ℝ≥0 → ℂ, range γ = physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (walkRuns κ b jumps E ω).1 → GB11.IsCompleteSimpleFlow γ →
          ∀ pc ∈ (walkRuns κ b jumps E ω).1.1, ∀ (t t' u u' : ℝ≥0) (z z' : ℂ), (t' : ℝ≥0∞) ≤ pc.2.2 →
            pc.1.tipAt pc.2.1 t z → pc.1.tipAt pc.2.1 t' z' → γ u = z → γ u' = z' → t < t' → u < u') ∧
        (∀ γ : ℝ≥0 → ℂ, range γ = physOf (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (walkRuns κ b jumps E ω).2 → GB11.IsCompleteSimpleFlow γ →
          ∀ pc ∈ (walkRuns κ b jumps E ω).2.1, ∀ (t t' u u' : ℝ≥0) (z z' : ℂ), (t' : ℝ≥0∞) ≤ pc.2.2 →
            pc.1.tipAt pc.2.1 t z → pc.1.tipAt pc.2.1 t' z' → γ u = z → γ u' = z' → t < t' → u < u')

/-- A tip point of a recorded piece lies in the range of a walk parametrization. -/
theorem tipAt_mem_range {spec : ExplSpec} {s : ExplState} {γ : ℝ≥0 → ℂ} (hγ : range γ = physOf spec s)
    {pc : Piece} (hpc : pc ∈ s.1) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pc.2.2) {z : ℂ} (hz : pc.1.tipAt pc.2.1 t z) :
    z ∈ range γ := by
  rw [hγ]
  exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨pc, hpc, t, ht, hz⟩))

/-- **`WalkPieceDirectionStatement` from the walk chronology** and GW4's contact order (`WalkPairPathFacts`). -/
theorem walkPieceDirectionStatement_of_chronology (hch : WalkPieceChronologyStatement.{u}) :
    WalkPieceDirectionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts hsimple
  filter_upwards [hch κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts hsimple, hfacts]
    with ω hω hf pR hpR pL hpL a a' c c' z z' ha ha' hc hc' hzR hzR' hzL hzL' haa'
  obtain ⟨hchR, hchL⟩ := hω
  obtain ⟨⟨γR, hγR, hγR0, hrR⟩, ⟨γL, hγL, hγL0, hrL⟩, hco⟩ := hf
  have hfR : GB11.IsCompleteSimpleFlow γR := ⟨hγR.1, hγR.2.1, hγR0, hγR.2.2.1, hγR.2.2.2⟩
  have hfL : GB11.IsCompleteSimpleFlow γL := ⟨hγL.1, hγL.2.1, hγL0, hγL.2.2.1, hγL.2.2.2⟩
  obtain ⟨u, hu⟩ := tipAt_mem_range hrR hpR ha hzR
  obtain ⟨u', hu'⟩ := tipAt_mem_range hrR hpR ha' hzR'
  obtain ⟨v, hv⟩ := tipAt_mem_range hrL hpL hc hzL
  obtain ⟨v', hv'⟩ := tipAt_mem_range hrL hpL hc' hzL'
  have huu' : u < u' := hchR γR hrR hfR pR hpR a a' u u' z z' ha' hzR hzR' hu hu' haa'
  have hvv' : v < v' := (hco γR γL hrR hrL hfR hfL u u' v v' (hu.trans hv.symm) (hu'.trans hv'.symm)).1 huu'
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · exact hlt
  · subst heq
    have hzz := Chart.tipAt_unique hzL hzL'
    rw [← hzz] at hu'
    exact absurd (hγR.2.1 (hu.trans hu'.symm)) huu'.ne
  · exact absurd (hchL γL hrL hfL pL hpL c' c v' v z' z hc hzL' hzL hv' hv hgt) (not_lt.2 hvv'.le)

/-- **Named input: the walk order of component charts** (Lemma GW3, p. 636: the component chart takes the right arc to
`(0, ∞)` and the left arc to `(−∞, 0)` "in the incoming orientation"; GB13a). Almost surely, for every component chart
of a component between the walks and every complete simple flows parametrizing the two walks, the landings at
`0 < x < x'` are right-walk points at walk parameters `u < u'`, and the landings at `x < x' < 0` are left-walk points
at walk parameters `v > v'`. Same hypotheses as `WalkIntFiber.WalkPhysicalGeometryStatement`. -/
def WalkComponentWalkOrderStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ C ∈ betweenComponents
        (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
        (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2),
        ∀ c : Chart, IsComponentChart
          (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
          (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) C c →
        ∀ γR γL : ℝ≥0 → ℂ,
          range γR = physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 →
          GB11.IsCompleteSimpleFlow γR →
          range γL = physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 →
          GB11.IsCompleteSimpleFlow γL →
          (∀ (x x' : ℝ) (v v' : ℝ≥0), 0 < x → x < x' → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (γR v)) →
            Tendsto c.2.1 (𝓝[H] (x' : ℂ)) (𝓝 (γR v')) → v < v') ∧
          (∀ (x x' : ℝ) (v v' : ℝ≥0), x < x' → x' < 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (γL v)) →
            Tendsto c.2.1 (𝓝[H] (x' : ℂ)) (𝓝 (γL v')) → v' < v)

/-- **`WalkComponentOrientationStatement` from the walk order of component charts and the walk chronology.** -/
theorem walkComponentOrientationStatement_of_walkOrder (hwo : WalkComponentWalkOrderStatement.{u})
    (hch : WalkPieceChronologyStatement.{u}) : WalkComponentOrientationStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hpf : ∀ᵐ ω ∂P, WalkInf.WalkPairPathFacts κ b jumps E ω := hfacts.mono fun _ hω => hω.1
  have hps : ∀ᵐ ω ∂P, WalkPiecesSimple κ b jumps E ω := hfacts.mono fun _ hω => hω.2.1
  filter_upwards [hwo κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts,
    hch κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hpf hps, hpf] with ω hω hchω hf C hC c hc
  obtain ⟨hchR, hchL⟩ := hchω
  obtain ⟨⟨γR, hγR, hγR0, hrR⟩, ⟨γL, hγL, hγL0, hrL⟩, -⟩ := hf
  have hfR : GB11.IsCompleteSimpleFlow γR := ⟨hγR.1, hγR.2.1, hγR0, hγR.2.2.1, hγR.2.2.2⟩
  have hfL : GB11.IsCompleteSimpleFlow γL := ⟨hγL.1, hγL.2.1, hγL0, hγL.2.2.1, hγL.2.2.2⟩
  obtain ⟨hwoR, hwoL⟩ := hω C hC c hc γR γL hrR hfR hrL hfL
  refine ⟨fun pc hpc x x' t t' z z' hx hxx' hz hz' ht ht' hzt hzt' => ?_,
    fun pc hpc x x' t t' z z' hxx' hx' hz hz' ht ht' hzt hzt' => ?_⟩
  · obtain ⟨v, rfl⟩ := tipAt_mem_range hrR hpc ht hzt
    obtain ⟨v', rfl⟩ := tipAt_mem_range hrR hpc ht' hzt'
    have hvv' := hwoR x x' v v' hx hxx' hz hz'
    rcases lt_trichotomy t t' with hlt | heq | hgt
    · exact hlt
    · subst heq
      exact absurd (hγR.2.1 (Chart.tipAt_unique hzt hzt')) hvv'.ne
    · exact absurd (hchR γR hrR hfR pc hpc t' t v' v _ _ ht hzt' hzt rfl rfl hgt) (not_lt.2 hvv'.le)
  · obtain ⟨v, rfl⟩ := tipAt_mem_range hrL hpc ht hzt
    obtain ⟨v', rfl⟩ := tipAt_mem_range hrL hpc ht' hzt'
    have hvv' := hwoL x x' v v' hxx' hx' hz hz'
    rcases lt_trichotomy t' t with hlt | heq | hgt
    · exact hlt
    · subst heq
      exact absurd (hγL.2.1 (Chart.tipAt_unique hzt' hzt)) hvv'.ne
    · exact absurd (hchL γL hrL hfL pc hpc t t' v v' _ _ ht' hzt hzt' rfl rfl hgt) (not_lt.2 hvv'.le)

end InteractingSLE.Theorem14.WalkWords
