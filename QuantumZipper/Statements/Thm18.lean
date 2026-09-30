import QuantumZipper.Statements.ConfigLaw
import QuantumZipper.Zipper.LengthZip
import QuantumZipper.LQG.Wedge
import QuantumZipper.SLE.Defs
import QuantumZipper.Loewner.Curves
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Theorem 1.8 (wedge decomposition and length-zipper stationarity)

Sheffield, *Conformal weldings of random surfaces*, Theorem 1.8. Specification only.

Fix `γ ∈ (0,2)`, `κ = γ²`, `Q = Qc γ`. Let `Y` be the canonical description of a
`(γ − 2/γ)`-quantum wedge (`IsQuantumWedge`, with the corrected range `α < Q`, B1) and `η` an
independent chordal SLE_κ from `0` to `∞`, driven by `√κ B`. Let `D₁, D₂` be the left and right
components of `ℍ \ η`. The pair of surfaces is encoded by the configuration `c = (Y, √κ B)`
(A8).

* **Wedge decomposition**: `(D₁, h|D₁)` and `(D₂, h|D₂)`, marked at `0` and `∞`, are independent
  `γ`-quantum wedges; their quantum lengths along `η` agree (A12).
* **Zipper stationarity**: (1) `Z^LEN_t` (`t > 0`) is a.s. uniquely defined via conformal
  welding, as the inverse of `Z^LEN_{−t}` (A13); (2) `Z^LEN_{s+t} = Z^LEN_s Z^LEN_t` a.s.;
  (3) the law of the pair is invariant under `Z^LEN_t`, `t ∈ ℝ`.

`Z^LEN_t` is `zipLenC` (`Zipper/LengthZip.lean`). For `t ≥ 0` it is defined constructively from
the length-welding driver (`lenWeldDriver`), like `zipCapUp`, followed by the canonical
rescaling (1.8). For `t < 0` it is `zipLenDown`. Audit AUDIT-1 §1 and §3 motivate this form and the
independence on `lawData`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper

variable {Ω : Type} [MeasurableSpace Ω]

/-- The configuration `(h, W)` of Theorem 1.8: the wedge field `Y ω` and the SLE_κ driving
function `W = √κ B(·, ω)`, `κ = γ²`. -/
def wedgeConfig (γ : ℝ) (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) (ω : Ω) :
    FieldSample × (ℝ → ℝ) :=
  (Y ω, drive (γ ^ 2) B ω)

/-- The canonical description of the quantum surface `(D, h|D)` marked at `0` and `∞`, where
`D` is the left (`left = true`) or right (`left = false`) component of `ℍ \ η`,
`η = sleTrace (γ²) B ω`: with `ψ = (uniformizer D)⁻¹ : ℍ → D` the conformal map fixing the
marked points (`Function.invFunOn` of the normalized uniformizer `D → ℍ`), the field
`h ∘ ψ + Q log|ψ'|` on `ℍ`, rescaled by (1.8) to unit quantum area in `B₁(0)` (A7). The choice
of `ψ` (unique up to `z ↦ a z`) is irrelevant after `canonical`. -/
def componentSurface (γ : ℝ) (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) (left : Bool) (ω : Ω) :
    FieldSample :=
  let η := sleTrace (γ ^ 2) B ω
  let D := if left then leftComponent η else rightComponent η
  canonical γ (coordChange (Y ω) (Function.invFunOn (uniformizer D) D) (Qc γ))

/-- **Theorem 1.8, wedge decomposition.** The surfaces `(D₁, h|D₁)` and `(D₂, h|D₂)` (canonical
descriptions, `componentSurface`) are `γ`-quantum wedges and are independent. Their laws are
compared through positive-radius circle coordinates and pairings (`IsQuantumWedge`, A16), and
independence is stated for the same law-relevant data (`lawData`), not for the raw samples.
Raw values at other measures are junk for regularized fields and could correlate the two
surfaces for artifact reasons (AUDIT-1 §1). -/
def theorem1_8_decomposition (γ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) : Prop :=
  IsQuantumWedge γ γ (componentSurface γ B Y true) P ∧
    IsQuantumWedge γ γ (componentSurface γ B Y false) P ∧
    IndepFun (lawData (componentSurface γ B Y true)) (lawData (componentSurface γ B Y false)) P

/-- **Theorem 1.8, quantum lengths along `η` agree.** Almost surely, for every capacity time
`t ≥ 0`, the quantum length of `η[0,t]` seen from `D₁` equals the one seen from `D₂`, both
defined by unzipping (`unzipLengths`, A12), and for `t > 0` this common length is positive and
finite (DECISIONS D13: excludes the junk value `qBoundaryMeasure = 0`). -/
def theorem1_8_lengthsAgree (γ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    (unzipLengths γ (wedgeConfig γ B Y ω) t).1 = (unzipLengths γ (wedgeConfig γ B Y ω) t).2 ∧
    (0 < t → 0 < (unzipLengths γ (wedgeConfig γ B Y ω) t).1 ∧
      (unzipLengths γ (wedgeConfig γ B Y ω) t).1 < ⊤)

/-- **Theorem 1.8, zipper stationarity.** `Z^LEN_t` is `zipLenC γ t` (`Zipper/LengthZip.lean`),
and `c = wedgeConfig γ B Y` is the configuration `(h, √κ B)`.

1. For every `ℓ > 0`, almost surely:
   * *existence*: the field `h` has a length-welding driver for quantum length `ℓ`
     (`IsLenWeldingDriver`). This is a pair `(T, W')` whose reverse flow zips up a simple curve
     and welds `[x₋,0]` to `[0,x₊]` by quantum length, where `ν_h[x₋,0] = ℓ`;
   * *non-degeneracy* (DECISIONS D13): the point `x₋ = lenWeldPoint γ h ℓ` indeed has
     `ν_h[x₋,0] = ℓ`, which excludes the junk value `qBoundaryMeasure = 0`;
   * *uniqueness*: any two length-welding drivers have the same time `T` and agree on `[0,T]`.
     Hence `Z^LEN_ℓ c` does not depend on the choice made by `lenWeldDriver`
     (`zipLenUpC_eq_of_unique`);
   * *inverse*: `Z^LEN_{−ℓ} (Z^LEN_ℓ c) = c` and `Z^LEN_ℓ (Z^LEN_{−ℓ} c) = c` up to `ConfigEq`.

   Together these are "the inverse `Z^LEN_ℓ` of `Z^LEN_{−ℓ}` is a.s. uniquely defined, via
   conformal welding" (A13).
2. For all `s, t ∈ ℝ`, a.s. `Z^LEN_{s+t} c = Z^LEN_s (Z^LEN_t c)` up to `ConfigEq` (A20).
3. For every `t ∈ ℝ`, `Z^LEN_t c` and `c` have the same law (`configLawFull`, A16).

Design notes. The round trips are stated for `c` itself, not for canonicalized versions. The
field `h` is a canonical description, so a.s. `scaleParam γ h = 1`. Its raw coordinates in
`lawData` a.s. agree with its regularized evaluations. This a.s. agreement is all that the round
trips need, and it is what `ConfigEq` (via `RegEq`) compares. Both outputs of `zipLenC` are
constructed fields (coordinate changes, whose raw values are regularized evaluations), so (3)
compares raw coordinates directly. The only choice left is that of `lenWeldDriver`, and only
`T` and `W'|[0,T]` are read by `zipLenUpC` (`zipWeldUp_congr`). For `Y ω` these are pinned down
by the uniqueness clause of (1). Round trip (ii) and clause (2) also evaluate `lenWeldDriver` at
other fields (`(zipLenDown γ ℓ c).1`, `(zipLenC γ t c).1`); uniqueness holds there a.s. as well
(removability of the corresponding curves, or transfer through (3), the uniqueness set being
coanalytic and hence universally measurable), but it is not asserted by (1) (AUDIT-2 m1).
Law equality in (3) also asserts that
`ω ↦ Z^LEN_t c ω` is a.e.-measurable (A21). -/
def theorem1_8_zipperStationarity (γ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) : Prop :=
  -- (1) the length-welding inverse `Z^LEN_ℓ` of `Z^LEN_{−ℓ}`, `ℓ > 0`
  (∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
    -- existence of a length-welding driver
    (∃ p : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p) ∧
    -- the length-`ℓ` point has quantum length `ℓ` (DECISIONS D13)
    qBoundaryMeasure γ (Y ω) (Set.Icc (lenWeldPoint γ (Y ω) ℓ) 0) = ENNReal.ofReal ℓ ∧
    -- uniqueness of the time and of the driver on `[0,T]`
    (∀ p q : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p → IsLenWeldingDriver γ (Y ω) ℓ q →
      p.1 = q.1 ∧ ∀ s ∈ Set.Icc 0 p.1, p.2 s = q.2 s) ∧
    -- `Z^LEN_ℓ` and `Z^LEN_{−ℓ}` are mutually inverse
    ConfigEq (zipLenDown γ ℓ (zipLenC γ ℓ (wedgeConfig γ B Y ω))) (wedgeConfig γ B Y ω) ∧
    ConfigEq (zipLenC γ ℓ (zipLenDown γ ℓ (wedgeConfig γ B Y ω))) (wedgeConfig γ B Y ω)) ∧
  -- (2) group property
  (∀ s t : ℝ, ∀ᵐ ω ∂P,
    ConfigEq (zipLenC γ (s + t) (wedgeConfig γ B Y ω))
      (zipLenC γ s (zipLenC γ t (wedgeConfig γ B Y ω)))) ∧
  -- (3) law invariance (circle coordinates + pairings, driver on `[0,∞)`)
  (∀ t : ℝ, configLawFull (fun ω => zipLenC γ t (wedgeConfig γ B Y ω)) P =
    configLawFull (wedgeConfig γ B Y) P)

/-- **Theorem 1.8** (Sheffield). For `γ ∈ (0,2)`, `κ = γ²`, a `(γ − 2/γ)`-quantum wedge `Y`
(canonical description) and an independent Brownian motion `B` (SLE_κ driven by `√κ B`): wedge
decomposition, agreement of quantum lengths along `η`, and length-zipper stationarity. -/
def theorem1_8 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    IsBrownianReal B P → IsQuantumWedge γ (γ - 2 / γ) Y P → IndepFun (pathOf B) Y P →
    theorem1_8_decomposition γ P B Y ∧ theorem1_8_lengthsAgree γ P B Y ∧
      theorem1_8_zipperStationarity γ P B Y

end QuantumZipper
