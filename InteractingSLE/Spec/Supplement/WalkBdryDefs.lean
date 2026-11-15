/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMeanBdry
import InteractingSLE.Spec.Supplement.WalkPieceProof

/-!
# Theorem 1.4's walk leaves: prefix charts, side points and the three remaining named inputs

Packet PROVE-T14-WALKBDRY. Lemma GW3, proof (`source/spec/p625-671.md` L210–L226, pp. 636–637) and Theorem GW4, proof
(p. 637). The two leaves `WalkMean.WalkUnionBdryStatement` (the union mean's boundary values in a run-determined
component chart) and `WalkPiece.WalkPiecePairRegStatement` (an ordinary piece of `R` and one of `L` share no arc) are
reduced (`WalkBdryAssembly`, `WalkBdryPair`) to three statements isolated here, each in the vocabulary of the
**prefix charts** of the recorded pieces:

* a recorded piece `pc = (c, W, S)` of a run (launch chart, stopped driver, stop) run to an own time `τ < S` has the
  **prefix chart** `prefixChart pc τ = c.loewner W τ` (it sends the prefix's tip to `0`); its explored set is
  `prefixSet pre pc τ` (the earlier pieces `pre` and the prefix, in `ℍ`);
* `IsLeftSidePt pc τ y` (`IsRightSidePt`): `y` is a real point of the **open left (right) side** of the prefix in the
  prefix chart — negative (positive), and a positive distance inside the images of the real points of the launch chart
  still alive at `τ`;
* **`WalkPrefixSideStatement θ right`** (probabilistic, one walk): almost surely, every harmonic representative `v` of
  the walk's own local-set mean, read in a prefix chart (`v + u₀ + χ · lift`), tends at a left (right) side point `y`
  to the side height `−λ − θχ` (`λ − θχ`), when near the landing point `p` of `y` the walk is the prefix
  (Lemma GW3's proof: "On an ordinary selected subarc the incoming own germ is, respectively, `λ − (π/2)χ = Λ` or
  `−λ + (π/2)χ = −Λ`"; the stage law of the piece at the stop `τ` and the nested marked comparison);
* **`WalkNormChartStatement`** (pathwise conformal geometry of the two runs): every component between the walks has a
  **normalized chart** (`IsNormChart`) — a component chart and word, and a finite set off which every real point of the
  chart matches a prefix side point of `R` (positive points) or of `L` (negative points) through a continuous
  transition whose lift difference tends to `0`, or an untouched original real point where the lift tends to `0`
  (Lemma GW3's proof: "The final component uniformizer therefore reflects with positive derivative across this single
  connected interval. Choose its logarithm to have argument zero there. … the zero lifts of the intervening own
  hydrodynamic maps preserve that germ");
* **`WalkPairGeomStatement`** (pathwise geometry of the pair clause): a nondegenerate common continuum of an ordinary
  piece of `R` and one of `L` yields a point where both walks are locally one prefix arc, seen from the **left of both**
  prefixes (the walks traverse it in the same direction: "Every common contact is ordered the same way on the two
  walks"), with a transition whose lift difference tends to a multiple of `2π` (Theorem GW4, proof: "an inherited branch
  change is an integer multiple of `2πχ`").

R48: these serve Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkBdry

open WalkLaw GW3Between LocalSets WalkMean

/-- A recorded piece of a run: its launch chart, its stopped driver and its stop. -/
abbrev Piece : Type := Chart × (ℝ≥0 → ℝ) × ℝ≥0∞

/-! ### Prefix charts and side points -/

/-- The driver of a recorded piece on real times. -/
def pieceDrv (pc : Piece) : ℝ → ℝ := fun r => pc.2.1 r.toNNReal

/-- The chart after the prefix of the piece `pc` run to own time `τ` (it sends the prefix's tip to `0`). -/
def prefixChart (pc : Piece) (τ : ℝ≥0) : Chart := pc.1.loewner (pieceDrv pc) τ

/-- The explored set in `ℍ` after the earlier pieces `pre` and the prefix of `pc` run to own time `τ`. -/
def prefixSet (pre : List Piece) (pc : Piece) (τ : ℝ≥0) : Set ℂ :=
  ((⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) ∪ pc.1.tipSet pc.2.1 τ) ∩ H

/-- `X` is a real point of the launch chart of `pc` not swallowed by own time `τ`. -/
def IsAlivePt (pc : Piece) (τ : ℝ≥0) (X : ℝ) : Prop :=
  ∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (pieceDrv pc) (X : ℂ) τ u

/-- `y` is a point of the open left side of the prefix of `pc` at own time `τ`, in the prefix chart: negative, and a
positive distance right of the images of all alive real points left of the prefix. -/
def IsLeftSidePt (pc : Piece) (τ : ℝ≥0) (y : ℝ) : Prop :=
  y < 0 ∧ ∃ ε > 0, ∀ X : ℝ, IsAlivePt pc τ X → (QuantumZipper.fwdMap (pieceDrv pc) τ X).re < 0 →
    (QuantumZipper.fwdMap (pieceDrv pc) τ X).re + ε < y

/-- `y` is a point of the open right side of the prefix of `pc` at own time `τ`, in the prefix chart. -/
def IsRightSidePt (pc : Piece) (τ : ℝ≥0) (y : ℝ) : Prop :=
  0 < y ∧ ∃ ε > 0, ∀ X : ℝ, IsAlivePt pc τ X → 0 < (QuantumZipper.fwdMap (pieceDrv pc) τ X).re →
    y + ε < (QuantumZipper.fwdMap (pieceDrv pc) τ X).re

/-- The ordinary part of a final state (all its recorded pieces). -/
def ordOf (s : ExplState) : Set ℂ := ⋃ p ∈ s.1, p.1.tipSet p.2.1 p.2.2

/-- The range in `ℍ` of a final state. -/
def wsetOf (s : ExplState) : Set ℂ := ordOf s ∩ H

theorem ordinarySet_eq_ordOf (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.ordinarySet κ b jumps spec D = ordOf (ExplState.run κ b jumps spec D spec.2.2.length) := rfl

/-- The walk's range in `ℍ` is the range in `ℍ` of its final state (root and connectors are real). -/
theorem walkSet_eq_wsetOf (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (w : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    walkSet κ b jumps w E ω = wsetOf (ExplState.run κ b jumps w (fun k => E k ω) w.2.2.length) := by
  ext z
  simp only [walkSet, wsetOf, ordOf, ExplState.physSet, mem_inter_iff, mem_union, mem_singleton_iff,
    mem_iUnion, mem_image, exists_prop]
  constructor
  · rintro ⟨(⟨rfl | h⟩ | ⟨a, -, x, -, rfl⟩), hzH⟩
    · exact absurd hzH (by simp [QuantumZipper.H])
    · exact ⟨h, hzH⟩
    · exact absurd hzH (by simp [QuantumZipper.H])
  · rintro ⟨h, hzH⟩
    exact ⟨Or.inl (Or.inr h), hzH⟩

/-- A prefix set lies in the range of the final state. -/
theorem prefixSet_subset_wsetOf {s : ExplState} {pre post : List Piece} {pc : Piece} (hs : s.1 = pre ++ pc :: post)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) ≤ pc.2.2) : prefixSet pre pc τ ⊆ wsetOf s := by
  rintro z ⟨hz, hzH⟩
  refine ⟨?_, hzH⟩
  simp only [ordOf, mem_iUnion, exists_prop]
  rcases hz with hz | hz
  · simp only [mem_iUnion, exists_prop] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    exact ⟨p, by rw [hs]; exact List.mem_append_left _ hp, hzp⟩
  · refine ⟨pc, by rw [hs]; exact List.mem_append_right _ List.mem_cons_self, ?_⟩
    obtain ⟨t, ht, hlim⟩ := hz
    exact ⟨t, ht.trans hτ, hlim⟩

/-! ### Normalized component charts -/

/-- The side height `Λ = λ − (π/2)χ` of Lemma GW3. -/
def bigLambda (κ : ℝ) : ℝ := sleLambda κ - Real.pi / 2 * QuantumZipper.chiC κ

/-- **Prefix match** at a real point `x` of a chart `c`: the boundary point of `c` at `x` is seen, through a
continuous transition `c'.fwd ∘ c.inv` into a prefix chart `c'` of the run `s`, as a point `y` of the left
(`left = true`) or right side of the prefix; near its landing point `p` the run `s` is the prefix and the other run
`s'` lies inside `s`; and the lift difference tends to `0`. -/
def IsPieceMatch (s s' : ExplState) (left : Bool) (c : Chart) (x : ℝ) : Prop :=
  ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0) (y : ℝ) (p : ℂ) (r : ℝ),
    s.1 = pre ++ pc :: post ∧ (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
    (if left then IsLeftSidePt pc τ y else IsRightSidePt pc τ y) ∧
    Tendsto (prefixChart pc τ).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) ∧ p ∈ wsetOf s ∪ {z : ℂ | z.im = 0} ∧
    0 < r ∧ wsetOf s ∩ ball p r ⊆ prefixSet pre pc τ ∧ wsetOf s' ∩ ball p r ⊆ wsetOf s ∧
    Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) ∧
    (∀ᶠ w in 𝓝[H] (x : ℂ), (prefixChart pc τ).1 (c.2.1 w) ∈ H ∧
      (prefixChart pc τ).2.1 ((prefixChart pc τ).1 (c.2.1 w)) = c.2.1 w) ∧
    Tendsto (fun w => (prefixChart pc τ).2.2 (c.2.1 w) - c.2.2 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 0)

/-- **Real match** at a real point `x` of a chart `c`: the boundary point of `c` at `x` is an original real point `a`
off the jumps of `b`, a positive distance from both ranges, the lift tends to `0` there and the word value is `b a`. -/
def IsRealMatch (sR sL : ExplState) (b : ℝ → ℝ) (jumps : Finset ℝ) (c : Chart) (x bx : ℝ) : Prop :=
  ∃ (a r : ℝ), a ∉ (jumps : Set ℝ) ∧ 0 < r ∧ Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ)) ∧
    Disjoint (ball (a : ℂ) r) (wsetOf sR ∪ wsetOf sL) ∧
    Tendsto (fun w => c.2.2 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 0) ∧ bx = b a

/-- **Normalized chart** of a component `C` between the walks with final states `r`: a component chart with a
piecewise-constant word `(bC, jumpsC)` satisfying (GW3.1), and a finite set off which every positive real point is a
left prefix match with `R` (word `−Λ`) or a real match, and every negative real point a right prefix match with `L`
(word `Λ`) or a real match. -/
def IsNormChart (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (r : ExplState × ExplState) (C : Set ℂ)
    (t : Chart × (ℝ → ℝ) × Finset ℝ) : Prop :=
  IsComponentChart (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2) C t.1 ∧
    IsPiecewiseConstantBoundaryData t.2.1 t.2.2 ∧
    IsComponentBoundaryData κ b (ordOf r.1) (ordOf r.2) t.1.2.1 t.2.1 t.2.2 ∧
    ∃ Eℝ : Set ℝ, Eℝ.Finite ∧ ∀ x : ℝ, x ∉ Eℝ →
      (0 < x → (IsPieceMatch r.1 r.2 true t.1 x ∧ t.2.1 x = -bigLambda κ) ∨
        IsRealMatch r.1 r.2 b jumps t.1 x (t.2.1 x)) ∧
      (x < 0 → (IsPieceMatch r.2 r.1 false t.1 x ∧ t.2.1 x = bigLambda κ) ∨
        IsRealMatch r.1 r.2 b jumps t.1 x (t.2.1 x))

/-! ### The three named inputs -/

/-- **Named input: the side heights of one walk's mean in its prefix charts** (Lemma GW3, proof, p. 636: "On an
ordinary selected subarc the incoming own germ is, respectively, `λ − (π/2)χ = Λ` or `−λ + (π/2)χ = −Λ`. The other
incoming set is separated from every compact proper subarc. The nested marked collar comparison … preserve[s] that
germ"; Lemma GW1, pp. 618–620, the stage word at a stop). For the boundary walk at angle `θ`: almost surely, for every
harmonic representative `v` of the walk's own local-set mean (centred field, any measurable version of the walk), every
recorded piece `pc` and rational own time `τ` before its stop, and every real point `y` of the open left (right) side of
the prefix in the prefix chart `c'` whose landing point `p` (a point of the prefix or a real point) has a neighbourhood
in which the walk is the prefix, `v + u₀ + χ · lift'` read through `c'` tends at `y` to `−λ − θχ` (`λ − θχ`). The
counterflow hypotheses are those of the consumers (they give the walks' proper parametrizations). -/
def WalkPrefixSideStatement (θ : ℝ) (right : Bool) : Prop :=
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
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A →
      (∀ᵐ ω ∂P, A ω = walkSet κ b jumps (boundaryWalkSpec b jumps θ right)
        (E (boundaryWalkSpec b jumps θ right)) ω) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (WholeField.centredField h u₀) P g →
      ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, v z * φ z) →
        ∀ (pre post : List Piece) (pc : Piece),
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
            (fun k => E (boundaryWalkSpec b jumps θ right) k ω)
            (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ pc :: post →
        ∀ τ : ℚ≥0, (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 →
        ∀ (y : ℝ) (p : ℂ), Tendsto (prefixChart pc τ).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) →
          p ∈ prefixSet pre pc τ ∪ {z : ℂ | z.im = 0} →
          (∃ r > 0, walkSet κ b jumps (boundaryWalkSpec b jumps θ right)
            (E (boundaryWalkSpec b jumps θ right)) ω ∩ ball p r ⊆ prefixSet pre pc τ) →
          (IsLeftSidePt pc τ y →
            Tendsto (fun ζ => v ((prefixChart pc τ).2.1 ζ) + u₀ ((prefixChart pc τ).2.1 ζ) +
                QuantumZipper.chiC κ * (prefixChart pc τ).2.2 ((prefixChart pc τ).2.1 ζ))
              (𝓝[H] (y : ℂ)) (𝓝 (-sleLambda κ - θ * QuantumZipper.chiC κ))) ∧
          (IsRightSidePt pc τ y →
            Tendsto (fun ζ => v ((prefixChart pc τ).2.1 ζ) + u₀ ((prefixChart pc τ).2.1 ζ) +
                QuantumZipper.chiC κ * (prefixChart pc τ).2.2 ((prefixChart pc τ).2.1 ζ))
              (𝓝[H] (y : ℂ)) (𝓝 (sleLambda κ - θ * QuantumZipper.chiC κ)))

/-- **Named input: every component between the walks has a normalized chart** (Lemma GW3, proof, p. 636: retained
prefixes of both selected arcs; the hydrodynamic chart of the retained union, in which they are consecutive real
intervals; the component uniformizer reflects with positive derivative across the interval between the two retained
tips; "Choose its logarithm to have argument zero there"; the zero lifts of the intervening own hydrodynamic maps; on an
open selected connector "the exact zero logarithmic lift"; "Increase the retained prefixes. Their component logarithms
agree on one previously fixed compact incident collar, so agree everywhere"). Pathwise conformal geometry of the two
final runs, stated almost surely under the hypotheses of `WalkMean.WalkUnionBdryStatement`. -/
def WalkNormChartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      ∀ᵐ ω ∂P, ∀ C ∈ betweenComponents
          (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
          (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2),
        ∃ t : Chart × (ℝ → ℝ) × Finset ℝ, IsNormChart κ b jumps (walkRuns κ b jumps E ω) C t

/-- **Named input: the local geometry of a common arc of the two walks** (Theorem GW4, proof, p. 637: "Every common
contact is ordered the same way on the two walks … An interior common open subarc is impossible: on the same incident
side the two exact flow germs differ by `πχ`, whereas an inherited branch change is an integer multiple of `2πχ`. Apply
the marked collar comparison on a compact proper ordinary subarc."). Almost surely, if the closures of an ordinary
piece of `R` and one of `L` share a nondegenerate preconnected set, there is a point `p ∈ ℍ` of both ranges near which
both walks are a single prefix arc (the same set), seen from the left of both prefixes at `yR`, `yL` (same traversal
direction), with a continuous transition `c'_L.fwd ∘ c'_R.inv` from `yR` to `yL` and a lift difference tending to a
multiple of `2π`. -/
def WalkPairGeomStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      ∀ᵐ ω ∂P, ∀ pR ∈ (walkRuns κ b jumps E ω).1.1, ∀ pL ∈ (walkRuns κ b jumps E ω).2.1,
        ∀ S ⊆ closure (pR.1.tipSet pR.2.1 pR.2.2) ∩ closure (pL.1.tipSet pL.2.1 pL.2.2),
          IsPreconnected S → ¬ S.Subsingleton →
          ∃ (preR postR preL postL : List Piece) (pcR pcL : Piece) (τR τL : ℚ≥0) (yR yL : ℝ) (p : ℂ)
            (r : ℝ) (n : ℤ),
            (walkRuns κ b jumps E ω).1.1 = preR ++ pcR :: postR ∧ (((τR : ℝ≥0)) : ℝ≥0∞) < pcR.2.2 ∧
            IsLeftSidePt pcR τR yR ∧
            (walkRuns κ b jumps E ω).2.1 = preL ++ pcL :: postL ∧ (((τL : ℝ≥0)) : ℝ≥0∞) < pcL.2.2 ∧
            IsLeftSidePt pcL τL yL ∧
            Tendsto (prefixChart pcR τR).2.1 (𝓝[H] (yR : ℂ)) (𝓝 p) ∧
            Tendsto (prefixChart pcL τL).2.1 (𝓝[H] (yL : ℂ)) (𝓝 p) ∧
            p ∈ wsetOf (walkRuns κ b jumps E ω).1 ∩ wsetOf (walkRuns κ b jumps E ω).2 ∧ 0 < r ∧
            wsetOf (walkRuns κ b jumps E ω).1 ∩ ball p r ⊆ prefixSet preR pcR τR ∧
            wsetOf (walkRuns κ b jumps E ω).2 ∩ ball p r ⊆ prefixSet preL pcL τL ∧
            wsetOf (walkRuns κ b jumps E ω).1 ∩ ball p r = wsetOf (walkRuns κ b jumps E ω).2 ∩ ball p r ∧
            (∀ᶠ ζ in 𝓝[H] (yR : ℂ), (prefixChart pcR τR).2.1 ζ ∈
              H \ (wsetOf (walkRuns κ b jumps E ω).1 ∪ wsetOf (walkRuns κ b jumps E ω).2)) ∧
            Tendsto (fun ζ => (prefixChart pcL τL).1 ((prefixChart pcR τR).2.1 ζ)) (𝓝[H] (yR : ℂ))
              (𝓝 (yL : ℂ)) ∧
            (∀ᶠ ζ in 𝓝[H] (yR : ℂ), (prefixChart pcL τL).1 ((prefixChart pcR τR).2.1 ζ) ∈ H ∧
              (prefixChart pcL τL).2.1 ((prefixChart pcL τL).1 ((prefixChart pcR τR).2.1 ζ)) =
                (prefixChart pcR τR).2.1 ζ) ∧
            Tendsto (fun ζ => (prefixChart pcL τL).2.2 ((prefixChart pcR τR).2.1 ζ) -
                (prefixChart pcR τR).2.2 ((prefixChart pcR τR).2.1 ζ)) (𝓝[H] (yR : ℂ))
              (𝓝 (2 * Real.pi * n))

end InteractingSLE.Theorem14.WalkBdry
