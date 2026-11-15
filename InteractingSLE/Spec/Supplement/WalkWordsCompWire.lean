/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsComp
import InteractingSLE.Spec.Supplement.WalkIntFillPrefix
import InteractingSLE.Spec.Supplement.GW3LawEvery

/-!
# The central prefix matches of every component chart, from the boundary orientation

Packet PROVE-WALK-WORDS (`hMatch` of PROVE-T14-WALKINT's terminal theorems, central sides). Under the hypotheses of
`WalkIntFiber.WalkPhysicalGeometryStatement`, almost surely, for every component `C` between the walks and every
component chart `c` of `C`, every real point `x₀ ≠ 0` whose landing `p` is a point of `ℍ` off the piece ends of its
walk and off the other walk has a recorded prefix through `p` with the complete prefix match
`IsPiecePhysicalMatch` (left side of the right walk for `x₀ > 0`, right side of the left walk for `x₀ < 0`), for every
reference hull containing the prefix's hull: `walkCentralMatchStatement_of_orientation`.

The one input is the named **orientation** of component charts, `WalkComponentOrientationStatement` (Lemma GW3, p. 636:
the component's uniformizer takes the right arc to `(0, ∞)` and the left arc to `(−∞, 0)` "in the incoming
orientation"; GB13a): along the right walk the landings of `c` move forward in each recorded piece's own time as `x`
increases, along the left walk backward. Everything else (piece data, launch domains, the prime-end access, the local
walk geometry, the transition) is derived (`exists_isPiecePhysicalMatch_right` / `_left`).
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

/-- **Named input: the orientation of component charts along the two walks** (see the module docstring). -/
def WalkComponentOrientationStatement : Prop :=
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
        (∀ pc ∈ (walkRuns κ b jumps E ω).1.1, ∀ (x x' : ℝ) (t t' : ℝ≥0) (z z' : ℂ), 0 < x → x < x' →
          Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 z) → Tendsto c.2.1 (𝓝[H] (x' : ℂ)) (𝓝 z') →
          (t : ℝ≥0∞) ≤ pc.2.2 → (t' : ℝ≥0∞) ≤ pc.2.2 → pc.1.tipAt pc.2.1 t z → pc.1.tipAt pc.2.1 t' z' →
          t < t') ∧
        (∀ pc ∈ (walkRuns κ b jumps E ω).2.1, ∀ (x x' : ℝ) (t t' : ℝ≥0) (z z' : ℂ), x < x' → x' < 0 →
          Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 z) → Tendsto c.2.1 (𝓝[H] (x' : ℂ)) (𝓝 z') →
          (t : ℝ≥0∞) ≤ pc.2.2 → (t' : ℝ≥0∞) ≤ pc.2.2 → pc.1.tipAt pc.2.1 t z → pc.1.tipAt pc.2.1 t' z' →
          t' < t)

/-- **The central prefix matches** (the proved conclusion; see the module docstring). -/
def WalkCentralMatchStatement : Prop :=
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
        (∀ (x₀ : ℝ) (p : ℂ), 0 < x₀ → Tendsto c.2.1 (𝓝[H] (x₀ : ℂ)) (𝓝 p) → p ∈ H →
          p ∉ pieceEnds (walkRuns κ b jumps E ω).1.1 → p ∉ closure (wsetOf (walkRuns κ b jumps E ω).2) →
          ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0), (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post ∧
            (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧ ∀ {d : Chart} (B : WalkIntCanon.HullModel d)
              (A : WalkIntCanon.HullModel (prefixChart pc τ)), A.hull ⊆ B.hull →
              WalkIntFiber.IsPiecePhysicalMatch (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2 true c B x₀) ∧
        (∀ (x₀ : ℝ) (p : ℂ), x₀ < 0 → Tendsto c.2.1 (𝓝[H] (x₀ : ℂ)) (𝓝 p) → p ∈ H →
          p ∉ pieceEnds (walkRuns κ b jumps E ω).2.1 → p ∉ closure (wsetOf (walkRuns κ b jumps E ω).1) →
          ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0), (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post ∧
            (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧ ∀ {d : Chart} (B : WalkIntCanon.HullModel d)
              (A : WalkIntCanon.HullModel (prefixChart pc τ)), A.hull ⊆ B.hull →
              WalkIntFiber.IsPiecePhysicalMatch (walkRuns κ b jumps E ω).2 (walkRuns κ b jumps E ω).1 false c B x₀)

/-- The points of a final state's physical set off the real line are its ordinary points. -/
theorem mem_ordOf_or_im_eq_zero {spec : ExplSpec} {s : ExplState} {z : ℂ} (hz : z ∈ physOf spec s) :
    z ∈ ordOf s ∨ z.im = 0 := by
  rcases hz with (hz | hz) | hz
  · right; rw [mem_singleton_iff.1 hz]; simp
  · exact Or.inl hz
  · right
    obtain ⟨a, -, ha⟩ := mem_iUnion₂.1 hz
    obtain ⟨x, -, rfl⟩ := ha
    simp

theorem walkCentralMatchStatement_of_orientation (hor : WalkComponentOrientationStatement.{u}) :
    WalkCentralMatchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  filter_upwards [hor κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts, hfacts, hRR, hRL]
    with ω hω hf hωR hωL C hC c hc
  obtain ⟨horR, horL⟩ := hω C hC c hc
  have hCoH : IsOpen C ∧ C ⊆ H := by
    rcases hf.2.2.2 C hC with hJ | hU
    · exact ⟨hJ.1, hJ.2.2.1⟩
    · exact ⟨hU.1, hU.2.1⟩
  have hcc : c.IsConformal := GW3Law.isConformal_of_isComponentChart hc hCoH.1 hCoH.2
  have hcC : MapsTo c.2.1 H C := hc.2.2.1
  obtain ⟨z₀, -, -, -, hCdef⟩ := hC
  have hCsub : C ⊆ H \ (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 ∪
      physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) := by
    rw [hCdef]; exact connectedComponentIn_subset _ _
  have hCR : Disjoint C (wsetOf (walkRuns κ b jumps E ω).1) := Set.disjoint_left.2 fun z hz hzw =>
    (hCsub hz).2 (Or.inl (Or.inl (Or.inr hzw.1)))
  have hCL : Disjoint C (wsetOf (walkRuns κ b jumps E ω).2) := Set.disjoint_left.2 fun z hz hzw =>
    (hCsub hz).2 (Or.inr (Or.inl (Or.inr hzw.1)))
  have hland := hc.2.2.2.2.1
  have hdR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
      (fun k c θ hl => pieceRegular_of_event hωR k c θ hl) (fun k c θ hl => hf.2.1 true k c θ hl) hs
  have hdL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
      (fun k c θ hl => pieceRegular_of_event hωL k c θ hl) (fun k c θ hl => hf.2.1 false k c θ hl) hs
  have hfR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (-(Real.pi / 2)) true
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
      (fun k c θ hl => pieceRegular_of_event hωR k c θ hl) (fun k => hreg _ k ω) hs h0
  have hfL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (Real.pi / 2) false
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
      (fun k c θ hl => pieceRegular_of_event hωL k c θ hl) (fun k => hreg _ k ω) hs h0
  refine ⟨fun x₀ p hx₀ hp hpH hpF hpL => ?_, fun x₀ p hx₀ hp hpH hpF hpR => ?_⟩
  · obtain ⟨p', hp', hpR', -⟩ := hland x₀
    have : (𝓝[H] (x₀ : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x₀ : ℂ)).im by simp)
    have hpp : p' = p := tendsto_nhds_unique hp' hp
    have hpo : p ∈ ordOf (walkRuns κ b jumps E ω).1 := by
      rcases mem_ordOf_or_im_eq_zero (hpp ▸ hpR' hx₀) with h | h
      · exact h
      · exact absurd hpH (by show ¬ 0 < p.im; rw [h]; exact lt_irrefl 0)
    exact exists_isPiecePhysicalMatch_right hdR hfR hCR hcc hcC
      (fun x hx => by
        obtain ⟨z, hz, hzR, -⟩ := hland x
        exact ⟨z, hz, mem_ordOf_or_im_eq_zero (hzR hx)⟩) hx₀ hp hpH hpo hpF hpL horR
  · obtain ⟨p', hp', -, hpL'⟩ := hland x₀
    have : (𝓝[H] (x₀ : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x₀ : ℂ)).im by simp)
    have hpp : p' = p := tendsto_nhds_unique hp' hp
    have hpo : p ∈ ordOf (walkRuns κ b jumps E ω).2 := by
      rcases mem_ordOf_or_im_eq_zero (hpp ▸ hpL' hx₀) with h | h
      · exact h
      · exact absurd hpH (by show ¬ 0 < p.im; rw [h]; exact lt_irrefl 0)
    exact exists_isPiecePhysicalMatch_left hdL hfL hCL hcc hcC
      (fun x hx => by
        obtain ⟨z, hz, -, hzL⟩ := hland x
        exact ⟨z, hz, mem_ordOf_or_im_eq_zero (hzL hx)⟩) hx₀ hp hpH hpo hpF hpR horL

/-! ### The canonical boundary word of a component chart -/

open Classical in
/-- **The canonical word** of a chart `c` of a component between `ordR` and `ordL`: at a positive (negative) real
point, `−Λ` (`Λ`) if the landing is an ordinary point of the right (left) walk, and the original boundary value `b`
at the landing otherwise (`IsComponentBoundaryData`, GW3.1). -/
def componentWord (κ : ℝ) (b : ℝ → ℝ) (ordR ordL : Set ℂ) (inv : ℂ → ℂ) (x : ℝ) : ℝ :=
  if 0 < x then
    (if extendFrom H inv x ∈ ordR then -(sleLambda κ - Real.pi / 2 * QuantumZipper.chiC κ)
      else b (extendFrom H inv x).re)
  else if x < 0 then
    (if extendFrom H inv x ∈ ordL then sleLambda κ - Real.pi / 2 * QuantumZipper.chiC κ
      else b (extendFrom H inv x).re)
  else 0

/-- **The canonical word satisfies (GW3.1) with every jump set.** -/
theorem isComponentBoundaryData_componentWord {κ : ℝ} {b : ℝ → ℝ} {ordR ordL : Set ℂ} {inv : ℂ → ℂ}
    (jumpsC : Finset ℝ) :
    IsComponentBoundaryData κ b ordR ordL inv (componentWord κ b ordR ordL inv) jumpsC := by
  intro x _ p hp
  have hx : ((x : ℂ)) ∈ closure H := by rw [closure_H]; show (0 : ℝ) ≤ ((x : ℂ)).im; simp
  have he : extendFrom H inv x = p := extendFrom_eq hx hp
  refine ⟨fun hx0 => ?_, fun hx0 => ?_⟩
  · simp only [componentWord, hx0, ↓reduceIte]
    rw [he]
  · have hn : ¬ 0 < x := not_lt.2 hx0.le
    simp only [componentWord, hn, hx0, ↓reduceIte]
    rw [he]

/-- **Every word satisfying (GW3.1) is the canonical word off its jumps** (when the chart lands at every real
point): the finite word of `hMatch` is the canonical one, and only its piecewise constancy is a condition. -/
theorem eq_componentWord_of_isComponentBoundaryData {κ : ℝ} {b : ℝ → ℝ} {ordR ordL : Set ℂ} {inv : ℂ → ℂ}
    {bC : ℝ → ℝ} {jumpsC : Finset ℝ} (h : IsComponentBoundaryData κ b ordR ordL inv bC jumpsC)
    (hland : ∀ x : ℝ, ∃ p : ℂ, Tendsto inv (𝓝[H] (x : ℂ)) (𝓝 p)) {x : ℝ} (hx : x ∉ jumpsC) (hx0 : x ≠ 0) :
    bC x = componentWord κ b ordR ordL inv x := by
  obtain ⟨p, hp⟩ := hland x
  have hcd := isComponentBoundaryData_componentWord (κ := κ) (b := b) (ordR := ordR) (ordL := ordL)
    (inv := inv) jumpsC x hx p hp
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [(h x hx p hp).2 hneg, (hcd.2 hneg)]
  · rw [(h x hx p hp).1 hpos, (hcd.1 hpos)]

end InteractingSLE.Theorem14.WalkWords
