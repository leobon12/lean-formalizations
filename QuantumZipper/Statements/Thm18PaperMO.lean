import QuantumZipper.Statements.Thm18Paper
import QuantumZipper.Loewner.Forward
import Mathlib.Topology.Instances.NNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, final paper form: the length zipper acts on the pieces for all times (D82/D86/D87)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (PDF p. 26,
`literature/1012.4797.txt` lines 1005–1045). This file is the Statements-layer home of the target
`theorem1_8PaperMO` (decision D91, statement placement only). Every definition below is a verbatim
copy of a definition that the proofs layer introduced for decisions D82 (unzipping acts on the
pieces, `Proofs/Thm18/R18RTDefs.lean`, `R18T6Defs.lean`, `R18PosLaw.lean`, `D74Mask.lean`,
`G1PkgTrace.lean`, `G1PkgPath.lean`, `Zipper/E6UpBasic.lean`), D86 (welding by open-arc lengths,
`RT5ODefs.lean`) and D87 (zipping up acts on the pieces, `RT6MODefs.lean`). The proofs layer keeps its
own copies; `Proofs/Thm18/Thm18PaperMOBridge.lean` proves
`Paper18.theorem1_8PaperMO ↔ R18.theorem1_8PaperMO` (`Paper18.theorem1_8PaperMO_iff_R18`).

## Relation to `theorem1_8Paper` (`Statements/Thm18Paper.lean`)

Hypotheses, the wedge decomposition, the length clause and the three comparisons of the stationarity
clause (`ConfigEqOff`, `configLawOff`) are verbatim `theorem1_8Paper`. Only the maps change:

* `offConfig γ c` reads a configuration off its own curve: the masked data `offData` (circle
  coordinates, test pairings, driver on `[0,∞)`), rebuilt as a field (`readOffField`: at a folded
  circle staying off the curve, its first recorded coordinate), the driver, and the local quantum
  area of that field on `ℍ ∖ η` (`areaOfData`). The curve is read by the path-measurable trace
  `curveSel` (for a continuous driver with `W 0 = 0` it is `curveOf`). This is Sheffield's pair of
  pieces `((D₁,h_{D₁}),(D₂,h_{D₂}))` (p. 17; p. 48: `h` may be defined arbitrarily on `η`).
* `Z^LEN_{−ℓ} = zipLenDownA ∘ offConfig` (`zipLenDownMA`, D82) and
  `Z^LEN_ℓ = zipLenUpOA ∘ offConfig` (`zipLenMO`, D87), where `zipLenUpOA` welds the two boundary
  arcs by their open-arc quantum lengths (`lenWeldDriverO`, D86; Berestycki–Powell
  arXiv:2404.16642 Def 6.41 p. 229).

## Clause (1): global driver versus open-arc driver

Clause (1) asserts existence, non-degeneracy and uniqueness of the length-welding driver of `Y ω`
in the **global** form `IsLenWeldingDriver γ (Y ω) ℓ` (lengths from `qBoundaryMeasure γ (Y ω)` on
closed arcs, as in `theorem1_8Paper`), while the zip maps use the **open-arc** driver
`lenWeldDriverO` of the pieces. The two agree almost surely by the D86 bridge
(`R18.lenWeldDriverO_eq_of`: open-arc lengths equal the global closed-arc masses when the global
boundary limit exists without atoms, and `R18.ae_lenWeldDriverO_offConfig_wedge`: a.s. at the
wedge configuration the open-arc driver of the pieces equals the global one), so clause (1) speaks
about the driver the maps actually use.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Paper18

/-! ## Measurable reading of the driver and of the curve (copies of `G1Pkg`, `D74`) -/

/-- A countable dense set of times (copy of `G1Pkg.denseT`). -/
def denseT : Set ℝ≥0 := (TopologicalSpace.exists_countable_dense ℝ≥0).choose

/-- A sequence in `denseT` tending to `t` (copy of `G1Pkg.apx`). -/
def apx (t : ℝ≥0) : ℕ → ℝ≥0 :=
  (mem_closure_iff_seq_limit.1
    ((TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.2 t : t ∈ closure denseT)).choose

/-- Good paths: uniformly continuous on `denseT ∩ [0,N]` for every `N` (copy of `G1Pkg.PathGood`). -/
def PathGood (a : ℝ≥0 → ℝ) : Prop :=
  ∀ N m : ℕ, ∃ k : ℕ, ∀ x ∈ denseT, ∀ y ∈ denseT, x ≤ N → y ≤ N →
    dist x y < 1 / ((k : ℝ) + 1) → |a x - a y| ≤ 1 / ((m : ℝ) + 1)

/-- The regularized path (copy of `G1Pkg.pathReg`). -/
def pathReg (a : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  {a : ℝ≥0 → ℝ | PathGood a}.indicator (fun a => limUnder atTop fun n => a (apx t n)) a

/-- The recentred regularized path (copy of `G1Pkg.regB`). -/
def regB (t : ℝ≥0) (a : ℝ≥0 → ℝ) : ℝ := pathReg a t - pathReg a 0

/-- Positive rationals (copy of `G1Pkg.PosQ`). -/
abbrev PosQ : Type := {q : ℚ // 0 < q}

/-- The filter of positive rationals tending to `0` (copy of `G1Pkg.posQFilter`). -/
def posQFilter : Filter PosQ := Filter.comap (fun q : PosQ => ((q : ℚ) : ℝ)) (𝓝[>] (0 : ℝ))

/-- The path-measurable version of the trace (copy of `G1Pkg.traceSel`). -/
def traceSel (κ : ℝ) (a : ℝ≥0 → ℝ) (t : ℝ) : ℂ :=
  if 0 ≤ t then limUnder posQFilter
    (fun q : PosQ => fwdMapInv (drive κ regB a) t ((((q : ℚ) : ℝ) : ℂ) * Complex.I)) else 0

/-- The curve read from a path (copy of `D74.curveSel`). -/
def curveSel (a : ℝ≥0 → ℝ) : Set ℂ :=
  closure (Set.range fun q : ℚ≥0 => traceSel 1 a (q : ℝ))

/-! ## The pieces of a configuration (copies of `E6`, `R18`, D82) -/

/-- The target space of the masked data (copy of `E6.FullData`). -/
abbrev FullData : Type := ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)

/-- The masked data of a configuration (copy of `R18.offData`). -/
def offData (x : FieldSample × (ℝ → ℝ)) : FullData :=
  (lawDataOff x, fun t : ℝ≥0 => x.2 t)

/-- The index `i` reads the folded circle `μ`, and that circle stays off the curve of `d`
(copy of `R18.OffIdx`). -/
def OffIdx (d : FullData) (μ : Measure ℂ) (i : ℕ) : Prop :=
  foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 = μ ∧
    CircleOff (curveSel d.2) (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2

open Classical in
/-- The field read from masked data (copy of `R18.readOffField`). -/
def readOffField (d : FullData) : FieldSample := fun μ =>
  if h : ∃ i, OffIdx d μ i then d.1.1 (Nat.find h) else 0

/-- The complement of the curve read from the data, in `ℍ` (copy of `R18.offSet`). -/
def offSet (d : FullData) : Set ℂ := H \ curveSel d.2

/-- The area read from the masked data (copy of `R18.areaOfData`). -/
def areaOfData (γ : ℝ) (d : FullData) : Measure ℂ :=
  qAreaMeasureOn γ (readOffField d) (offSet d)

/-- The driver read from the data (copy of `R18.drvOfData`). -/
def drvOfData (d : FullData) : ℝ → ℝ := fun s => d.2 ⟨max s 0, le_max_right _ _⟩

/-- The configuration read from masked data (copy of `R18.configOfData`). -/
def configOfData (γ : ℝ) (d : FullData) : AreaConfig :=
  ⟨readOffField d, drvOfData d, areaOfData γ d⟩

/-- **The pieces of a configuration** (copy of `R18.offConfig`, D82). -/
def offConfig (γ : ℝ) (c : AreaConfig) : AreaConfig :=
  configOfData γ (offData c.toPair)

/-- **`Z^LEN_{−ℓ}` on the pieces** (copy of `R18.zipLenDownMA`, D82). -/
def zipLenDownMA (γ ℓ : ℝ) (c : AreaConfig) : AreaConfig :=
  zipLenDownA γ ℓ (offConfig γ c)

/-! ## Welding by open-arc lengths (copies of `R18`, D86) -/

/-- The left welding point by open-arc lengths (copy of `R18.lenWeldPointO`). -/
def lenWeldPointO (γ : ℝ) (x : FieldSample) (ℓ : ℝ) : ℝ :=
  sSup {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ openArcLen γ x s 0}

/-- The welding homeomorphism by open-arc lengths (copy of `R18.weldHomRO`). -/
def weldHomRO (γ : ℝ) (x : FieldSample) (s : ℝ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ openArcLen γ x s 0 ≤ openArcLen γ x 0 r}

/-- Length-welding driver with open-arc lengths (copy of `R18.IsLenWeldingDriverO`). -/
def IsLenWeldingDriverO (γ : ℝ) (x : FieldSample) (ℓ : ℝ) (p : ℝ × (ℝ → ℝ)) : Prop :=
  0 ≤ p.1 ∧ Continuous p.2 ∧ p.2 0 = 0 ∧ (p.1 = 0 ∨ IsSimpleCurveHull (revHull p.2 p.1)) ∧
    zeroMinus p.2 p.1 = lenWeldPointO γ x ℓ ∧
    ∀ s ∈ Icc (zeroMinus p.2 p.1) 0, weldingHom p.2 p.1 s = weldHomRO γ x s

/-- The open-arc length-welding driver (copy of `R18.lenWeldDriverO`). -/
def lenWeldDriverO (γ : ℝ) (x : FieldSample) (ℓ : ℝ) : ℝ × (ℝ → ℝ) :=
  Classical.epsilon (IsLenWeldingDriverO γ x ℓ)

/-- `Z^LEN_ℓ`, `ℓ ≥ 0`, welding by open-arc lengths (copy of `R18.zipLenUpOA`, D86). -/
def zipLenUpOA (γ ℓ : ℝ) (c : AreaConfig) : AreaConfig :=
  canonAConfig γ (zipWeldUpA γ (lenWeldDriverO γ c.fld ℓ).1 (lenWeldDriverO γ c.fld ℓ).2 c)

/-! ## The target (copies of `R18`, D87) -/

/-- **The length zipper of D87** (copy of `R18.zipLenMO`): `Z^LEN_ℓ` re-welds the pieces for
`ℓ ≥ 0` and unzips the pieces for `ℓ < 0`. -/
def zipLenMO (γ ℓ : ℝ) : AreaConfig → AreaConfig :=
  if 0 ≤ ℓ then zipLenUpOA γ ℓ ∘ offConfig γ else zipLenDownMA γ (-ℓ)

/-- **Theorem 1.8, zipper stationarity, D87 form** (copy of
`R18.theorem1_8_zipperStationarityPaperMO`). Clause (1) reads the global length-welding driver of
`Y ω`; the maps use the open-arc driver of the pieces; the two agree a.s. (module docstring). -/
def theorem1_8_zipperStationarityPaperMO (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) : Prop :=
  (∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
    (∃ p : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p) ∧
    qBoundaryMeasure γ (Y ω) (Set.Icc (lenWeldPoint γ (Y ω) ℓ) 0) = ENNReal.ofReal ℓ ∧
    (∀ p q : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p → IsLenWeldingDriver γ (Y ω) ℓ q →
      p.1 = q.1 ∧ ∀ s ∈ Set.Icc 0 p.1, p.2 s = q.2 s) ∧
    ConfigEqOff (zipLenDownMA γ ℓ (zipLenMO γ ℓ (wedgeAConfig γ B Y ω))).toPair
      (wedgeAConfig γ B Y ω).toPair ∧
    ConfigEqOff (zipLenMO γ ℓ (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω))).toPair
      (wedgeAConfig γ B Y ω).toPair) ∧
  (∀ s t : ℝ, ∀ᵐ ω ∂P,
    ConfigEqOff (zipLenMO γ (s + t) (wedgeAConfig γ B Y ω)).toPair
      (zipLenMO γ s (zipLenMO γ t (wedgeAConfig γ B Y ω))).toPair) ∧
  (∀ t : ℝ, configLawOff (fun ω => (zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair) P =
    configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P)

/-- **Theorem 1.8** (Sheffield, arXiv:1012.4797, p. 26), final paper form (D74, D75, D76, D82,
D86, D87; placed here by D91): let `γ ∈ (0,2)`, `Y` a `(γ − 2/γ)`-quantum wedge (canonical
description) and `B` a Brownian motion independent of `Y` (the SLE_{γ²} driver `√κ B`). Then the
two sides are independent `γ`-quantum wedges, the quantum lengths along `η` seen from both sides
agree (positive and finite), and the length zipper acting on the pieces satisfies (1) unique
inverse via welding, (2) the group law, (3) invariance of the law of the pair. -/
def theorem1_8PaperMO : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    IsBrownianReal B P → IsQuantumWedge γ (γ - 2 / γ) Y P → IndepFun (pathOf B) Y P →
    theorem1_8_decomposition γ P B Y ∧ theorem1_8_lengthsAgreePaper γ P B Y ∧
      theorem1_8_zipperStationarityPaperMO γ P B Y

end Paper18
end QuantumZipper
