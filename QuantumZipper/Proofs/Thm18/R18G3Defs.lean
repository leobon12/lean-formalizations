import QuantumZipper.Proofs.Thm18.G1ZSplitDefs
import QuantumZipper.Proofs.Thm18.R18Nodes
import QuantumZipper.Proofs.Thm18.G3Reduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3: the split of `R18.G3PaperStmt` (route (b) of D77)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71). Plan: `handoff/R18-PLAN.md` §5.

Route (b) (DECISIONS D77): the independence of the two side surfaces is proved the way G1 proves
that each side is a wedge, for both sides at once.

1. **Joint rerooting** (`G3JointRerootStmt`): unzipping by left quantum length `ℓ` (E6) reroots
   both side surfaces at the same length `ℓ` (F1: the two lengths of `η[0,t]` agree), so the pair
   of local canonical side data has the same law as the pair rerooted at the points at length `ℓ`
   (p. 70: "invariant under unzipping by a fixed quantity of quantum boundary length ... similar
   to the argument used to show Proposition 1.7").
2. **Adding a constant** (`G3JointConstInvStmt`): the pair law does not change when the same
   constant is added to both side fields (the `(γ−2/γ)`-wedge with an independent SLE is
   invariant under adding constants modulo rescaling; proof of Prop. 1.7, pp. 25–26).
3. **Joint Palm average** (`G3JointPalmConstStmt`): averaging 1 over `ℓ ∈ (0,U]` samples the left
   root from quantum length and the right root is its length partner, exactly the pair
   `(x, R(x))` of Figure 1.7 (p. 71).
4. **Wedge coordinates** (`G3JointPalmToWedgeStmt`): the joint Palm-window integral is that of
   the `(γ−2/γ)`-wedge `Y` at `x` and at its length partner `R(x)`, zoomed at level `γ C` through
   the local conformal maps of the independent curve.
5. **Two-point Palm zoom decorrelation** (`G3WedgePalmDecStmt`, the core): as the zoom level
   grows, the zooms of `Y` at `x` and at `R(x)` decorrelate (p. 71: condition on the field off
   `B_ε(x) ∪ B_ε(R(x))`; Proposition 5.5 at each point; the GFF Markov property), stated for
   cylinder events of the zoom data, the form in which Proposition 5.5 is available
   (`G2FixMixStmt`).

Steps 1–4 are copies of the G1 proofs (`R18.g1RerootStmt_of_arc`, `g1SideConstInvStmt_of`,
`g1PalmConstStmt_of`, `g1PalmToWedgeStmt_of`) with pairs of functionals; step 5 is the content of
Sheffield p. 71 and is the only new open node. The wiring (`R18G3Wire.lean`) turns the product
formula for cylinder events into `IndepFun` (`indepFun_of_generating_eq_mul`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm D3Plus

/-! ## Objects -/

/-- The quantum length of the left segment `[b, 0]` of the left side surface. -/
def g3LenL (γ : ℝ) (x : FieldSample) (b : ℝ) : ℝ :=
  (g1SideNu γ true x (g1SideSeg true b)).toReal

/-- The joint Palm-window integral of the two side surfaces with the constant `C` added: the
left root `b` is sampled from the left side boundary measure on the window of length `U`, the
right root is the point of the right side half-line at the same quantum length (Figure 1.7). -/
def g3PalmIntC (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) (U C : ℝ) (R : ℕ)
    (Γ₁ Γ₂ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ b in g1Win γ true (g1SideField γ B Y true ω) U,
    Γ₁ (locFieldFull R (canonical γ (addConst (translate (g1SideField γ B Y true ω) (b : ℂ)) C))) *
    Γ₂ (locFieldFull R (canonical γ (addConst (translate (g1SideField γ B Y false ω)
      (g1SidePt γ false (g1SideField γ B Y false ω)
        (g3LenL γ (g1SideField γ B Y true ω) b) : ℂ)) C)))
    ∂(g1SideNu γ true (g1SideField γ B Y true ω)) ∂P

/-- The length partner `R(x) > 0` of a left boundary point `x < 0` of the wedge field `y`:
`ν_y[0, R(x)] = ν_y[x, 0]` (Sheffield, Figure 1.7 and p. 71). -/
def g3zPartner (γ : ℝ) (y : FieldSample) (x : ℝ) : ℝ :=
  lenRight (qBoundaryMeasure γ y) ((qBoundaryMeasure γ y) (Icc x 0)).toReal

/-- The joint Palm-window integral of the wedge `Y`: Palm point `x` on the left window, its
length partner `R(x)`, zooms at level `L` through the local maps of the curve. -/
def g3zWedgePalmInt (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) (U L : ℝ) (R : ℕ)
    (Γ₁ Γ₂ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ x in g1zWedgeWin γ true (Y ω) U,
    Γ₁ (locFieldFull R (canonical γ
      (zoomFieldVia γ L (Y ω) x (g1zLocMap true (drive (γ ^ 2) B ω) x)))) *
    Γ₂ (locFieldFull R (canonical γ
      (zoomFieldVia γ L (Y ω) (g3zPartner γ (Y ω) x)
        (g1zLocMap false (drive (γ ^ 2) B ω) (g3zPartner γ (Y ω) x)))))
    ∂((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf true)) ∂P

/-! ## The nodes -/

/-- **Step 1 (joint rerooting).** For `ℓ > 0` the pair of local canonical side data has the
same joint integrals of product functionals as the pair rerooted at the points at quantum length
`ℓ` of the two side half-lines. -/
def G3JointRerootStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ R : ℕ, ∀ Γ₁ Γ₂ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞,
      Measurable Γ₁ → Measurable Γ₂ → (∀ y, Γ₁ y ≤ 1) → (∀ y, Γ₂ y ≤ 1) →
      ∫⁻ ω, Γ₁ (locFieldFull R (canonical γ (translate (g1SideField γ B Y true ω)
          (g1SidePt γ true (g1SideField γ B Y true ω) ℓ : ℂ)))) *
        Γ₂ (locFieldFull R (canonical γ (translate (g1SideField γ B Y false ω)
          (g1SidePt γ false (g1SideField γ B Y false ω) ℓ : ℂ)))) ∂P =
      ∫⁻ ω, Γ₁ (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) *
        Γ₂ (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P

/-- **Step 2 (adding a constant to both sides).** -/
def G3JointConstInvStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ C : ℝ,
    ∀ R : ℕ, ∀ Γ₁ Γ₂ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞,
      Measurable Γ₁ → Measurable Γ₂ → (∀ y, Γ₁ y ≤ 1) → (∀ y, Γ₂ y ≤ 1) →
      ∫⁻ ω, Γ₁ (locFieldFull R (canonical γ (addConst (g1SideField γ B Y true ω) C))) *
        Γ₂ (locFieldFull R (canonical γ (addConst (g1SideField γ B Y false ω) C))) ∂P =
      ∫⁻ ω, Γ₁ (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) *
        Γ₂ (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P

/-- **Step 3 (joint Palm average with a constant).** The normalized joint Palm-window integral
is the plain joint expectation of the constant-shifted pair. -/
def G3JointPalmConstStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ U : ℝ, 0 < U → ∀ C : ℝ,
    ∀ R : ℕ, ∀ Γ₁ Γ₂ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞,
      Measurable Γ₁ → Measurable Γ₂ → (∀ y, Γ₁ y ≤ 1) → (∀ y, Γ₂ y ≤ 1) →
      (ENNReal.ofReal U)⁻¹ * g3PalmIntC γ P B Y U C R Γ₁ Γ₂ =
        ∫⁻ ω, Γ₁ (locFieldFull R (canonical γ (addConst (g1SideField γ B Y true ω) C))) *
          Γ₂ (locFieldFull R (canonical γ (addConst (g1SideField γ B Y false ω) C))) ∂P

/-- **Step 4 (change of variables to the wedge boundary, both sides).** -/
def G3JointPalmToWedgeStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ U : ℝ, 0 < U → ∀ C : ℝ,
    ∀ R : ℕ, ∀ Γ₁ Γ₂ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞,
      Measurable Γ₁ → Measurable Γ₂ → (∀ y, Γ₁ y ≤ 1) → (∀ y, Γ₂ y ≤ 1) →
      g3PalmIntC γ P B Y U C R Γ₁ Γ₂ = g3zWedgePalmInt γ P B Y U (γ * C) R Γ₁ Γ₂

/-- The joint Palm-window integral of the wedge for two cylinder events of the full data of the
zooms (`lawData` of the canonical zooms, as in `zoomLaw`/`G2FixMixStmt`). -/
def g3zWedgePalmCyl (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) (U L : ℝ) (s t : Set LawD) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ x in g1zWedgeWin γ true (Y ω) U,
    s.indicator 1 (WedgeMeas.dataFull H (canonical γ
      (zoomFieldVia γ L (Y ω) x (g1zLocMap true (drive (γ ^ 2) B ω) x)))) *
    t.indicator 1 (WedgeMeas.dataFull H (canonical γ
      (zoomFieldVia γ L (Y ω) (g3zPartner γ (Y ω) x)
        (g1zLocMap false (drive (γ ^ 2) B ω) (g3zPartner γ (Y ω) x)))))
    ∂((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf true)) ∂P

/-- **Step 5 (two-point Palm zoom decorrelation; Sheffield p. 71, the core).** For cylinder
events `s, t` of the zoom data and every `ε > 0`, some window `U > 0` makes the normalized joint
Palm-window integral of the zooms of the `(γ−2/γ)`-wedge at `x` and at its length partner `R(x)`
(through the local maps of the independent curve) `ε`-close to the product of its two marginals,
for all large zoom levels. Route: Fubini over the independent curve; the local maps are conformal
near `x`, `R(x)` (G0); conditionally on the field off `B_ε(x) ∪ B_ε(R(x))` the two zooms are
independent (GFF Markov property, `condIndepCE_twoHalfDisc_palm`) and each is asymptotically
independent of the conditioning (conditional Proposition 5.5, `g2FixMixStmt_holds`); the
free-field version of the conclusion is `R18.g3FreeTwoPoint_holds`. -/
def G3WedgePalmDecStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ s ∈ lawCyl, ∀ t ∈ lawCyl, ∀ ε : ℝ≥0∞, 0 < ε → ∃ U : ℝ, 0 < U ∧ ∀ᶠ L in atTop,
      (ENNReal.ofReal U)⁻¹ * g3zWedgePalmCyl γ P B Y U L s t ≤
          ((ENNReal.ofReal U)⁻¹ * g3zWedgePalmCyl γ P B Y U L s univ) *
            ((ENNReal.ofReal U)⁻¹ * g3zWedgePalmCyl γ P B Y U L univ t) + ε ∧
        ((ENNReal.ofReal U)⁻¹ * g3zWedgePalmCyl γ P B Y U L s univ) *
            ((ENNReal.ofReal U)⁻¹ * g3zWedgePalmCyl γ P B Y U L univ t) ≤
          (ENNReal.ofReal U)⁻¹ * g3zWedgePalmCyl γ P B Y U L s t + ε

end R18
end QuantumZipper
