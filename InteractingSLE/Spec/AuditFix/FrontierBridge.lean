/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.FrontierInputs
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_boundaryWalks_frontiers
import InteractingSLE.Frozen.Spec.Chart_id
import InteractingSLE.Frozen.Spec.Chart_tipSet

/-!
# Audit fix: the boundary walks are the outer boundary of the counterflow range (Theorem 1.4)

Packet PROVE-AF-FRONTIER, external audit §3.4 (p. 9): "The frontier export states that the right walk lies in the
counterflow range and that the range has no point strictly to its right, with the reflected left statement. It does
not literally identify a topological frontier set. […] A bridge to a specified notion of outer boundary should be
exported if that terminology is meant as an exact equality. Boundary connectors make a naive frontier identity
delicate."

Paper (arXiv:1201.1496v2): Theorem 1.4, p. 22: "if `η'` is nowhere boundary filling (i.e., `η' ∩ ℝ` has empty
interior), then `ηL` and `ηR` do not hit the continuation threshold before reaching `∞` and are the left and right
boundaries of `η'`"; p. 26: "A similar statement holds on the event that `η'` is boundary filling on one or more
segments of `ℝ`. In this case, `ηL` and `ηR` hit their continuation thresholds before reaching `∞`, but they can be
extended to describe the entire left and right boundaries of `η'` in the manner explained in Figure 7.22"; Figure
7.22, p. 164: "Let `K = KL ∪ KR` be the outer boundary of `η'`, `KL` and `KR` its left and right sides […] this does
not mean that `η'` *traces* a segment of `∂D`".

## The notions

In the setting of the frozen anchor `IsCenteredCounterflowDriver.boundaryWalks_frontiers`, write `K` for the completed
range of `η'` (`counterflowCompletedRange`), `R` and `L` for the physical sets of the right and left boundary walks
(`ExplState.physSet` of `boundaryWalkSpec … (−π/2) true` and `boundaryWalkSpec … (π/2) false`; ordinary pieces, real
connectors and the root `0`), and `ℍ = QuantumZipper.H`.

* The **right complementary region** of the range is `rightSideOf K`: the union of the components of `ℍ \ K` whose
  closure contains a point of `(0, ∞)` off `K`; the **left** one is `leftSideOf K`; their union is the **outer
  region** (the components of `ℍ \ K` reaching the boundary outside the range).
* The **right boundary** of `η'` in `ℍ` is the relative boundary `frontier (rightSideOf K) ∩ ℍ`; the **outer
  boundary** in `ℍ` is `frontier (rightSideOf K ∪ leftSideOf K) ∩ ℍ`.
* **Infinity.** `∞` is not a point of `ℂ`: the walks run from `0` to `∞` (proper curves, `‖γ t‖ → ∞`), the range
  omits its initial point `∞`, and every identity below is between subsets of `ℂ`; adding `∞` to both sides gives
  the identities in the Riemann sphere.
* **Real points and connectors.** The full frontier of `rightSideOf K` in `ℂ` also contains the real intervals that
  bound the right complementary components (points off the range), and a real connector of `R` (a segment of
  `[0, ∞)` filled by `η'`) borders only the region on the *left* of `R`. So `R = frontier (rightSideOf K)` fails
  whenever the right region reaches the boundary, and `R = frontier (rightSideOf K) ∩ K` fails when `η'` fills a
  segment of `[0, ∞)` (the interior points of that connector do not border the right region); it holds in the
  nowhere-boundary-filling case. The exact general identity adds the range's own points on `[0, ∞)`.

## Main results

* `FrontierBridgeStatement`, `frontierBridge_holds` (general piecewise-constant data, almost surely): the walks are
  proper simple curves from `0`; `K` is closed and `K = closure (K ∩ ℍ)`; `rightSideOf K = rightSideOf R` and
  `leftSideOf K = leftSideOf L`; `frontier (rightSideOf K) ∩ ℍ = R ∩ ℍ` and the left mirror; the outer boundary in `ℍ`
  is `(R ∪ L) ∩ ℍ`, inside the topological frontier of `K`; `R ∩ [0, ∞) = K ∩ [0, ∞)`, `L ∩ (−∞, 0] = K ∩ (−∞, 0]`;
  `R = closure (frontier (rightSideOf K) ∩ ℍ) ∪ (K ∩ [0, ∞)) = (frontier (rightSideOf K) ∩ K) ∪ (K ∩ [0, ∞))`,
  and the left mirror.
* `FrontierNowhereFillingStatement`, `frontierNowhereFilling_holds` (the paper's case): almost surely, if `ℝ ∩ K`
  has empty interior, both first pieces have lifetime `⊤`, each walk is its root `0` together with the trace of its
  first piece (the complete flow line `ηR`, resp. `ηL`), `R = frontier (rightSideOf K) ∩ K =
  closure (frontier (rightSideOf K) ∩ ℍ)`, the left mirror, and `R ∪ L = frontier (rightSideOf K ∪ leftSideOf K) ∩ K =
  closure (frontier (rightSideOf K ∪ leftSideOf K) ∩ ℍ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.AuditFix

/-- **Theorem 1.4, frontiers as the outer boundary of the range** (general piecewise-constant boundary data). In the
setting of the frozen anchor `IsCenteredCounterflowDriver.boundaryWalks_frontiers`, almost surely, with `K` the
completed range of `η'` and `R`, `L` the right and left boundary walks (with their real connectors and root):
1. `R` and `L` are ranges of proper simple curves from `0` to `∞` in `closure ℍ`;
2. `K` is closed and is the closure of its points in `ℍ` (the counterflow trace lies in `ℍ` at times arbitrarily close
   to any time; cf. Figure 7.22: `η'` does not *trace* a segment of the boundary);
3. the right complementary region of the range is exactly the region strictly to the right of `R`, and the left one
   exactly the region strictly to the left of `L`;
4. `R ∩ ℍ` (resp. `L ∩ ℍ`) is the relative boundary in `ℍ` of the right (resp. left) complementary region;
5. the relative boundary in `ℍ` of the outer region is `(R ∪ L) ∩ ℍ`, and these points are topological frontier
   points of `K`;
6. `R` contains exactly the points of `K` on `[0, ∞)`, and `L` exactly those on `(−∞, 0]` (filled boundary segments,
   i.e. the real connectors, and isolated boundary contacts);
7. `R = closure (frontier (rightSideOf K) ∩ ℍ) ∪ (K ∩ [0, ∞))` and
   `L = closure (frontier (leftSideOf K) ∩ ℍ) ∪ (K ∩ (−∞, 0])`;
8. `R = (frontier (rightSideOf K) ∩ K) ∪ (K ∩ [0, ∞))` and `L = (frontier (leftSideOf K) ∩ K) ∪ (K ∩ (−∞, 0])`: the
   points of the range on the boundary of its right (left) complementary region lie on `R` (`L`), and the rest of
   `R` (`L`) is the range's points on the closed positive (negative) half-line. -/
def FrontierBridgeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P,
        let K := counterflowCompletedRange (fun t => W' t ω)
        let R := ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
        let L := ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
        ((∃ γ : ℝ≥0 → ℂ, Continuous γ ∧ Function.Injective γ ∧ (∀ t, 0 ≤ (γ t).im) ∧
            Tendsto (fun t => ‖γ t‖) atTop atTop ∧ γ 0 = 0 ∧ range γ = R) ∧
          (∃ γ : ℝ≥0 → ℂ, Continuous γ ∧ Function.Injective γ ∧ (∀ t, 0 ≤ (γ t).im) ∧
            Tendsto (fun t => ‖γ t‖) atTop atTop ∧ γ 0 = 0 ∧ range γ = L)) ∧
        (IsClosed K ∧ closure (K ∩ QuantumZipper.H) = K) ∧
        (rightSideOf K = rightSideOf R ∧ leftSideOf K = leftSideOf L) ∧
        (frontier (rightSideOf K) ∩ QuantumZipper.H = R ∩ QuantumZipper.H ∧
          frontier (leftSideOf K) ∩ QuantumZipper.H = L ∩ QuantumZipper.H) ∧
        (frontier (rightSideOf K ∪ leftSideOf K) ∩ QuantumZipper.H = (R ∪ L) ∩ QuantumZipper.H ∧
          (R ∪ L) ∩ QuantumZipper.H ⊆ frontier K) ∧
        (R ∩ ((↑) : ℝ → ℂ) '' Ici 0 = K ∩ ((↑) : ℝ → ℂ) '' Ici 0 ∧
          L ∩ ((↑) : ℝ → ℂ) '' Iic 0 = K ∩ ((↑) : ℝ → ℂ) '' Iic 0) ∧
        (R = closure (frontier (rightSideOf K) ∩ QuantumZipper.H) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Ici 0) ∧
          L = closure (frontier (leftSideOf K) ∩ QuantumZipper.H) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Iic 0)) ∧
        (R = (frontier (rightSideOf K) ∩ K) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Ici 0) ∧
          L = (frontier (leftSideOf K) ∩ K) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Iic 0))

/-- **Theorem 1.4, the nowhere-boundary-filling case: `ηR` and `ηL` are the right and left boundaries of `η'`**
(p. 22). In the setting of the frozen anchor `IsCenteredCounterflowDriver.boundaryWalks_frontiers`, almost surely, with
`K`, `R`, `L` as in `FrontierBridgeStatement`: if `η'` is nowhere boundary filling (`ℝ ∩ K` has empty interior), then
1. the first ordinary pieces of both walks have lifetime `⊤` (they do not hit the continuation threshold before
   reaching `∞`);
2. each walk is its root `0` together with the trace of its first piece in the identity chart, i.e. the complete
   angle-`−π/2` flow line `ηR` (resp. angle-`π/2` flow line `ηL`) of `h` from `0` (by `IsStagedHistory` at
   instruction `0`, whose retained past `pastSigma … 0` is trivial, the first piece is that flow line of `h` itself);
3. `R` is the set of points of the range on the boundary of its right complementary region, and `L` that for the
   left one;
4. `R` is the closure of the relative boundary in `ℍ` of the right complementary region of the range, and `L` that of
   the left one;
5. `R ∪ L` is the set of points of the range on the boundary of the outer region (the outer boundary of the range),
   and is the closure of the relative boundary in `ℍ` of the outer region. -/
def FrontierNowhereFillingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P,
        let K := counterflowCompletedRange (fun t => W' t ω)
        let R := ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
        let L := ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
        interior (((↑) : ℝ → ℂ) ⁻¹' K) = ∅ →
          ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
            (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) ∧
          (R = {0} ∪ Chart.id.tipSet (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).1 ⊤ ∧
            L = {0} ∪ Chart.id.tipSet (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).1 ⊤) ∧
          (R = frontier (rightSideOf K) ∩ K ∧ L = frontier (leftSideOf K) ∩ K) ∧
          (R = closure (frontier (rightSideOf K) ∩ QuantumZipper.H) ∧
            L = closure (frontier (leftSideOf K) ∩ QuantumZipper.H)) ∧
          (R ∪ L = frontier (rightSideOf K ∪ leftSideOf K) ∩ K ∧
            R ∪ L = closure (frontier (rightSideOf K ∪ leftSideOf K) ∩ QuantumZipper.H))

/-- **`FrontierBridgeStatement` holds**: from the frozen frontier anchor, GW1's proper parametrizations of both walks
(Theorems 1.2–1.3), the walks' real-arc statements, Theorem 1.3 for the counterflow, and the deterministic topology of
`Spec/AuditFix/FrontierTopology.lean`. -/
theorem frontierBridge_holds : FrontierBridgeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hPP := Wire.walkProperRegStatements_of_thm12_thm13 Wire.T14Asm7.h12.{u} Wire.T14Asm7.h13.{u}
    Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀
  have hNR := Theorem14.WalkPiece.rightWalkNegRealRegStatement_of_theorem13 hPP.1 Wire.T14Asm7.h13₀
  filter_upwards [IsCenteredCounterflowDriver.boundaryWalks_frontiers hκ hκ4 b jumps hb hh hcf hζ' E hE hreg,
    hPP.1 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hPP.2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    Frontier.ae_leftWalk_posReal_subsingleton hκ hκ4 hb hh hcf hζ' hE hreg,
    Frontier.ae_isClosed_closure_inter_H hκ hcf hζ'] with ω hfr hPR hPL hNRω hPLω hK
  intro K R L
  obtain ⟨⟨hRK, hfR⟩, ⟨hLK, hfL⟩, -⟩ := hfr
  obtain ⟨γR, hγR, hγR0, hγRr⟩ := hPR
  obtain ⟨γL, hγL, hγL0, hγLr⟩ := hPL
  rw [← hγRr] at hRK hfR hNRω
  rw [← hγLr] at hLK hfL hPLω
  obtain ⟨hs1, hs2, hb1, hb2, ho1, ho2, hr1, hr2, -, -⟩ :=
    Frontier.bridge_core hγR hγR0 hγL hγL0 hK.1 hK.2 hRK hfR hLK hfL
  obtain ⟨hi1, hi2, hj1, hj2⟩ :=
    Frontier.bridge_of_walks hγR hγR0 hγL hγL0 hK.1 hK.2 hRK hfR hLK hfL hNRω hPLω
  have eR : R = range γR := hγRr.symm
  have eL : L = range γL := hγLr.symm
  rw [eR, eL]
  exact ⟨⟨⟨γR, hγR.1, hγR.2.1, hγR.2.2.1, hγR.2.2.2, hγR0, rfl⟩,
      ⟨γL, hγL.1, hγL.2.1, hγL.2.2.1, hγL.2.2.2, hγL0, rfl⟩⟩,
    hK, ⟨hs1, hs2⟩, ⟨hb1, hb2⟩, ⟨ho1, ho2⟩, ⟨hr1, hr2⟩, ⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩

/-- **`FrontierNowhereFillingStatement` holds**: from the frozen frontier anchor (whose third clause gives the
lifetimes), GW1's proper parametrizations, Theorem 1.3 for the counterflow, the walk machine
(`Frontier.physSet_boundaryWalkSpec_of_top`) and the deterministic topology. -/
theorem frontierNowhereFilling_holds : FrontierNowhereFillingStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hPP := Wire.walkProperRegStatements_of_thm12_thm13 Wire.T14Asm7.h12.{u} Wire.T14Asm7.h13.{u}
    Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀
  filter_upwards [IsCenteredCounterflowDriver.boundaryWalks_frontiers hκ hκ4 b jumps hb hh hcf hζ' E hE hreg,
    hPP.1 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hPP.2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    Frontier.ae_isClosed_closure_inter_H hκ hcf hζ'] with ω hfr hPR hPL hK
  intro K R L hint
  obtain ⟨⟨hRK, hfR⟩, ⟨hLK, hfL⟩, hnb⟩ := hfr
  obtain ⟨hR0, hL0⟩ := hnb hint
  have hRtop := Frontier.physSet_boundaryWalkSpec_of_top κ b jumps (-(Real.pi / 2)) true
    (D := fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hR0
  have hLtop := Frontier.physSet_boundaryWalkSpec_of_top κ b jumps (Real.pi / 2) false
    (D := fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hL0
  obtain ⟨γR, hγR, hγR0, hγRr⟩ := hPR
  obtain ⟨γL, hγL, hγL0, hγLr⟩ := hPL
  rw [← hγRr] at hRK hfR
  rw [← hγLr] at hLK hfL
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ :=
    Frontier.bridge_nbf_of_walks hγR hγR0 hγL hγL0 hK.1 hK.2 hRK hfR hLK hfL hint
  refine ⟨⟨hR0, hL0⟩, ⟨hRtop, hLtop⟩, ?_⟩
  have eR : R = range γR := hγRr.symm
  have eL : L = range γL := hγLr.symm
  rw [eR, eL]
  exact ⟨⟨hn1, hn2⟩, ⟨hn3, hn4⟩, ⟨hn5, hn6⟩⟩

end InteractingSLE.AuditFix
