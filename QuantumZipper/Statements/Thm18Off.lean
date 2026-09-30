import QuantumZipper.Statements.Thm18

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8 as Sheffield states it: the fields are compared away from the curve (D74)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (p. 26,
`literature/1012.4797.txt` lines 1005–1030). **User-approved statement alignment D74**
(`DECISIONS.md`, 2026-09-29): "we are trying to faithfully formalize Scott's original paper, so
we should follow what he does. If he compares away from the curve, then so should we."

Sheffield's objects are the **restrictions** `h_{D₁}, h_{D₂}` of `h` to the two components of
`ℍ \ η` (p. 26: "let `h_{D1}` and `h_{D2}` be the restrictions of `h` to these domains";
`Z^LEN_{−t}((D₁,h_{D₁}),(D₂,h_{D₂}))`; "(3) the law of the pair `((D₁,h_{D₁}),(D₂,h_{D₂}))` is
invariant"). The field on `η` itself is never an object of the paper: p. 17 ("both `h` and `η` are
determined by the pair"), §4.1 p. 48 ("we can define `h_t` arbitrarily on the measure zero set
`η([0,t])`"); Berestycki–Powell, arXiv:2404.16642, Thm 8.13 and the remark after it (p. 282),
Def 8.15, Rem 8.30.

`Statements/Thm18.lean` (`theorem1_8`) compares the fields on **every** dyadic circle and test
function (`ConfigEq`, `configLawFull`), including those that cross `η`; there the zipped field's
value is an artefact of the regularized model. This file states the paper's version
`theorem1_8Off`: identical to `theorem1_8` except that

* clauses (1)–(2) compare configurations with `ConfigEqOff` (regularized circle averages at the
  circles whose folded image stays at positive distance from the curve, drivers on `[0,∞)`);
* clause (3) compares the laws `configLawOff`: `configLawFull` with every circle coordinate and
  every test pairing that meets the configuration's curve masked (set to `0`).

The wedge decomposition, the lengths clause, existence/non-degeneracy/uniqueness in (1) are
unchanged. `theorem1_8 → theorem1_8Off` is proved in `Proofs/Thm18/D74Headline.lean`
(`D74.theorem1_8Off_of_theorem1_8`).

**Naming.** `theorem1_8` keeps its name (the stronger regularized full-plane form, used by the
existing proofs) so that the ~1000 modules importing `Statements/Thm18.lean` are not rebuilt;
`theorem1_8Off` is the target that matches the paper.

**The curve.** `curveOf W` is the closure of the trace at nonnegative rational times. When the
trace is continuous on `[0,∞)` and tends to `∞` (Sheffield's `η`, `IsSimpleChord`; Rohde–Schramm)
this is `η([0,∞))` (`Proofs/Thm18/D74Curve.lean`: `curveOf_eq_image`, `ae_curveOf_drive_eq`).
Reading it at rational times only makes the mask a measurable function of the configuration data
(`Proofs/Thm18/D74Mask.lean`, `curveMaskMeas`).

**Why this is exactly Sheffield's statement.** The masked data of a configuration consist of the
driver on `[0,∞)` (hence `η`) and of the pairings of `h` with all test functions supported in
`ℍ \ η` together with the circle averages at circles in `ℍ̄ \ η` (these read the boundary
measure of each `(Dᵢ, h|Dᵢ)`), i.e. `(η, h|_{ℍ\η})` in the canonical embedding: the pair
`((D₁,h_{D₁}),(D₂,h_{D₂}))` of the paper, with a fixed embedding. Nothing on `η` is compared
(not stronger), and every object the paper compares is compared (not weaker).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace QuantumZipper

/-- The curve `η = η([0,∞))` of a driving function `W`: the closure of the forward-flow trace at
nonnegative rational times. For a trace that is continuous on `[0,∞)` and tends to `∞` (the SLE
trace, Rohde–Schramm) this is exactly `trace W '' [0,∞)`. -/
def curveOf (W : ℝ → ℝ) : Set ℂ :=
  closure (Set.range fun q : ℚ≥0 => trace W (q : ℝ))

/-- The circle `∂B(z,r)` stays, after folding into `ℍ̄`, at positive distance from `K`: some open
annulus around it is mapped by `foldH` outside `K`. -/
def CircleOff (K : Set ℂ) (z : ℂ) (r : ℝ) : Prop :=
  ∃ δ > 0, ∀ w : ℂ, |dist w z - r| < δ → foldH w ∉ K

/-- Equality of regularized circle averages at every dyadic circle that avoids `K`: equality of
the fields restricted to the complement of `K`. -/
def RegEqOff (K : Set ℂ) (x y : FieldSample) : Prop :=
  ∀ (k : ℕ) (z : ℂ), CircleOff K z (radius k) → avgReg x k z = avgReg y k z

/-- **Equality of configurations away from the curve** (Sheffield's comparison of the pairs
`((D₁,h_{D₁}),(D₂,h_{D₂}))`): the fields agree off the curve of `c'` and the drivers agree on
`[0,∞)` (so the two curves coincide). -/
def ConfigEqOff (c c' : FieldSample × (ℝ → ℝ)) : Prop :=
  RegEqOff (curveOf c'.2) c.1 c'.1 ∧ ∀ u : ℝ, 0 ≤ u → c.2 u = c'.2 u

open scoped Classical in
/-- The law-relevant data `lawData` of a configuration with everything that meets its curve
masked: the circle coordinates `coordsFull` at folded circles that do not stay off the curve, and
the pairings with test functions whose support meets the curve, are replaced by `0`. -/
def lawDataOff (x : FieldSample × (ℝ → ℝ)) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  (fun i => if CircleOff (curveOf x.2) (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2
      then CoordsFull.coordsFull x.1 i else 0,
    fun ρ => if Disjoint (tsupport ρ.1) (curveOf x.2) then pairRaw x.1 ρ.1 else 0)

/-- **The law of the pair of surfaces cut out by the curve** (Theorem 1.8 (3) as in the paper):
the joint law of the masked data `lawDataOff` and of the driver on `[0,∞)`. -/
def configLawOff {Ω : Type*} [MeasurableSpace Ω] (c : Ω → FieldSample × (ℝ → ℝ))
    (P : Measure Ω) : Measure (((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) :=
  P.map fun ω => (lawDataOff (c ω), fun t : ℝ≥0 => (c ω).2 t)

/-- **Theorem 1.8, zipper stationarity, as in the paper** (compare `theorem1_8_zipperStationarity`,
of which this is the off-curve form): (1) existence, non-degeneracy and uniqueness of the
length-welding driver, and the two round trips up to `ConfigEqOff`; (2) the group property up to
`ConfigEqOff`; (3) invariance of `configLawOff`. -/
def theorem1_8_zipperStationarityOff (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) : Prop :=
  (∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
    (∃ p : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p) ∧
    qBoundaryMeasure γ (Y ω) (Set.Icc (lenWeldPoint γ (Y ω) ℓ) 0) = ENNReal.ofReal ℓ ∧
    (∀ p q : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p → IsLenWeldingDriver γ (Y ω) ℓ q →
      p.1 = q.1 ∧ ∀ s ∈ Set.Icc 0 p.1, p.2 s = q.2 s) ∧
    ConfigEqOff (zipLenDown γ ℓ (zipLenC γ ℓ (wedgeConfig γ B Y ω))) (wedgeConfig γ B Y ω) ∧
    ConfigEqOff (zipLenC γ ℓ (zipLenDown γ ℓ (wedgeConfig γ B Y ω))) (wedgeConfig γ B Y ω)) ∧
  (∀ s t : ℝ, ∀ᵐ ω ∂P,
    ConfigEqOff (zipLenC γ (s + t) (wedgeConfig γ B Y ω))
      (zipLenC γ s (zipLenC γ t (wedgeConfig γ B Y ω)))) ∧
  (∀ t : ℝ, configLawOff (fun ω => zipLenC γ t (wedgeConfig γ B Y ω)) P =
    configLawOff (wedgeConfig γ B Y) P)

/-- **Theorem 1.8** (Sheffield, arXiv:1012.4797, p. 26), in the paper's form (D74): wedge
decomposition, agreement of quantum lengths along `η`, and length-zipper stationarity for the
pair of surfaces cut out by `η` (fields compared away from `η`). -/
def theorem1_8Off : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    IsBrownianReal B P → IsQuantumWedge γ (γ - 2 / γ) Y P → IndepFun (pathOf B) Y P →
    theorem1_8_decomposition γ P B Y ∧ theorem1_8_lengthsAgree γ P B Y ∧
      theorem1_8_zipperStationarityOff γ P B Y

end QuantumZipper
