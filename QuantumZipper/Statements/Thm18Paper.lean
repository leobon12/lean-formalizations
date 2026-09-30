import QuantumZipper.Statements.Thm18Off
import QuantumZipper.LQG.Local

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8 as Sheffield states it: configurations carry their quantum area (D76)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (PDF p. 26,
`literature/1012.4797.txt` lines 1005–1045) and the normalization (1.8) (PDF pp. 21–22, lines
797–810). **User-approved statement change D76** (`DECISIONS.md`, 2026-09-29, "Carry the area"),
on top of D74 (fields compared away from the curve, `Statements/Thm18Off.lean`) and D73/D75
(lengths of pieces of `η` read on open arcs).

## What changes with respect to `theorem1_8Off`

Sheffield defines `Z^LEN_{−t}((D₁,h_{D₁}),(D₂,h_{D₂}))` as "rescaling of
`(f^η_{t'}(D₁,h_{D₁}), f^η_{t'}(D₂,h_{D₂}))`, where the rescaling is done via (1.8) with the
parameter `a` chosen so that `B₁(0)` has area one in the **transformed quantum measure**" (p. 26,
lines 1030–1036). The objects are the two pieces; the measure normalized is the area of the pieces
transported by the conformal maps. In `theorem1_8Off` the zips instead recompute the area from the
zipped field (`scaleParam γ` of the zipped field), which reads circles crossing the welded curve.
Here a configuration is `(field, driver, μ)` (`AreaConfig`):

* the Theorem 1.8 configuration is `wedgeAConfig = (Y ω, √κ B, μ_{Y ω})`, `μ_{Y ω} = qAreaMeasure`;
* unzipping by capacity time `t` pushes `μ|_{ℍ∖K_t}` forward by the centered forward map `f_t`
  (`zipCapDownA`), zipping up along `(T, W')` pushes `μ|_ℍ` forward by the reverse flow `revMap W' T`
  (`zipWeldUpA`): the welded surface's area is the sum of the two pieces' areas;
* the rescaling (1.8) uses the carried measure: `a = areaScale μ` (`canonAConfig`), and pushes `μ`
  forward by `z ↦ z/a`;
* unzipping lengths are the open-arc lengths (`openArcLen`, D73/D75; a copy of
  `LocLen.arcLen`, `Proofs/Zipper/LocLenDefs.lean`); the zip-up weld point is `lenWeldDriver`, as in
  `theorem1_8Off` (it reads the boundary measure of the field being zipped, not the curve).

Everything else (wedge decomposition, the clause-(1) existence/non-degeneracy/uniqueness of the
length-welding driver of `Y ω`, the comparisons `ConfigEqOff` and `configLawOff`) is verbatim
`theorem1_8Off`; the comparisons read the `(field, driver)` part (`AreaConfig.toPair`).

## Why this is exactly Sheffield's Theorem 1.8 (and not weaker)

1. *Same objects compared.* Clauses (1)–(3) compare the fields away from the curve and the drivers
   (`ConfigEqOff`, `configLawOff`), exactly as `theorem1_8Off` (D74 fidelity argument there). The
   carried `μ` is not compared: in the paper it is a function of the pieces' fields.
2. *Same maps.* Sheffield's `Z^LEN_{±t}` normalizes by the transformed quantum measure of the pieces.
   That is the carried `μ`: at the start `μ = μ_{Y ω}`; each zip transforms it by the conformal map of
   that zip (Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
   Prop 2.1, `literature/0808.1560.txt` lines 488–495: `μ_{h∘ψ+Q log|ψ'|} = ψ⁻¹_* μ_h`), and the curve
   carries no area (p. 48: `η` has measure zero). Where the old field-based normalization makes
   sense, it agrees with this one (`Proofs/Thm18/R18Basic.lean`: `R18.toPair_canonAConfig`,
   `R18.toPair_zipLenUpA`, `R18.toPair_zipLenDownA`). The facts "the curve has zero quantum area" and
   "area coordinate change in the zip direction" are proved in the proof of `theorem1_8Paper`
   (handoff/R18-PLAN.md), not assumed.
3. *Not weaker.* Hypotheses are those of `theorem1_8`/`theorem1_8Off`; the conclusion keeps every
   clause of Sheffield's theorem (decomposition, lengths along `η` agree, (1) unique inverse via
   welding, (2) group law, (3) law invariance), with the initial area fixed to the true quantum area
   of the wedge, so there is no free data. Lengths: open arcs (D75: the paper's length measure has
   no atoms, so open and closed arcs give the same lengths).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper

/-- A configuration of the paper-form Theorem 1.8 (D76): the field, the driving function of the
curve, and the quantum area measure `μ` of the pair of surfaces cut out by the curve. -/
structure AreaConfig where
  /-- the field `h` (a canonical embedding of the pair of pieces) -/
  fld : FieldSample
  /-- the driving function of the curve `η` -/
  drv : ℝ → ℝ
  /-- the quantum area measure of the pieces (the curve itself carries none) -/
  area : Measure ℂ

/-- The `(field, driver)` part of a configuration, the data compared by Theorem 1.8. -/
def AreaConfig.toPair (c : AreaConfig) : FieldSample × (ℝ → ℝ) := (c.fld, c.drv)

/-- The scale (1.8) read from an area measure: the smallest radius `a` at which `B_a(0) ∩ ℍ` has
`μ`-mass at least `1`. `scaleParam γ x = areaScale (qAreaMeasure γ x)` by definition. -/
def areaScale (μ : Measure ℂ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ 1 ≤ μ (Metric.ball 0 a ∩ H)}

/-- The rescaling (1.8) with the parameter chosen from the carried area (Sheffield p. 26: "`B₁(0)`
has area one in the transformed quantum measure"): with `a = areaScale c.area`, the field becomes
`h(a·) + Q log a`, the driver `s ↦ V(a² s)/a` (Brownian scaling, as `canonConfig`), and the area
is pushed forward by `z ↦ z/a` (a point `w` of the old picture is `w/a` in the new one). -/
def canonAConfig (γ : ℝ) (c : AreaConfig) : AreaConfig :=
  ⟨rescale c.fld (Qc γ) (areaScale c.area),
    fun s => c.drv (areaScale c.area ^ 2 * max s 0) / areaScale c.area,
    c.area.map fun z => ((areaScale c.area : ℂ))⁻¹ * z⟩

/-- Zipping up along the reverse flow `(T, W')` without rescaling (`zipWeldUp`), with the area of
the pieces pushed forward by `revMap W' T : ℍ → ℍ ∖ K_T`. -/
def zipWeldUpA (γ T : ℝ) (W' : ℝ → ℝ) (c : AreaConfig) : AreaConfig :=
  ⟨(zipWeldUp γ T W' c.toPair).1, (zipWeldUp γ T W' c.toPair).2,
    (c.area.restrict H).map (revMap W' T)⟩

/-- Unzipping by capacity time `t` without rescaling (`zipCapDown`), with the area of
`ℍ ∖ K_t` pushed forward by the centered forward map `f_t : ℍ ∖ K_t → ℍ`. -/
def zipCapDownA (γ t : ℝ) (c : AreaConfig) : AreaConfig :=
  ⟨(zipCapDown γ t c.toPair).1, (zipCapDown γ t c.toPair).2,
    (c.area.restrict (H \ fwdHull c.drv t)).map (fwdMap c.drv t)⟩

/-- Open-arc quantum length (D75; Berestycki–Powell arXiv:2404.16642 Def 6.41 on the open
segment): the mass of `(a,b)` for the local boundary measure of `x` on `(a,b)`. Same definition as
`LocLen.arcLen`. -/
def openArcLen (γ : ℝ) (x : FieldSample) (a b : ℝ) : ℝ≥0∞ :=
  qBoundaryMeasureOn γ x (Ioo a b) (Ioo a b)

/-- The quantum lengths of `η[0,t]` seen from `D₁` and `D₂`, "well defined by unzipping"
(p. 26), read on the open arcs `(O⁻_t, 0)` and `(0, O⁺_t)` (same as `LocLen.unzipLengthsArc`). -/
def unzipLengthsOpen (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (t : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  (openArcLen γ (unzippedField γ c t) (sideImages c.2 t).1 0,
    openArcLen γ (unzippedField γ c t) 0 (sideImages c.2 t).2)

/-- The capacity time `t'` at which the length of `η[0,t']` seen from `D₁` first reaches `ℓ`
(same as `LocLen.lenTimeArc`). -/
def lenTimeOpen (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsOpen γ c s).1}

/-- `Z^LEN_{−ℓ}`, `ℓ ≥ 0` (p. 26): unzip up to the length time `t'`, then rescale by (1.8) using
the transported area. -/
def zipLenDownA (γ ℓ : ℝ) (c : AreaConfig) : AreaConfig :=
  canonAConfig γ (zipCapDownA γ (lenTimeOpen γ ℓ c.toPair) c)

/-- `Z^LEN_ℓ`, `ℓ ≥ 0`: zip up along the length-welding driver of the field (`lenWeldDriver`,
Theorem 1.8 (1)), then rescale by (1.8) using the transported area. -/
def zipLenUpA (γ ℓ : ℝ) (c : AreaConfig) : AreaConfig :=
  canonAConfig γ (zipWeldUpA γ (lenWeldDriver γ c.fld ℓ).1 (lenWeldDriver γ c.fld ℓ).2 c)

/-- The length quantum zipper `Z^LEN_ℓ`, `ℓ ∈ ℝ`, on area-carrying configurations. -/
def zipLenA (γ ℓ : ℝ) : AreaConfig → AreaConfig :=
  if 0 ≤ ℓ then zipLenUpA γ ℓ else zipLenDownA γ (-ℓ)

/-- The configuration of Theorem 1.8: the wedge field `Y ω`, the SLE_κ driver `√κ B`
(`κ = γ²`), and the quantum area measure of `Y ω`. -/
def wedgeAConfig (γ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) (ω : Ω) :
    AreaConfig :=
  ⟨Y ω, drive (γ ^ 2) B ω, qAreaMeasure γ (Y ω)⟩

/-- **Theorem 1.8, quantum lengths along `η` agree** (open arcs, D73/D75): a.s., for every
capacity time `t ≥ 0` the lengths of `η[0,t]` seen from `D₁` and `D₂` agree, and for `t > 0` they
are positive and finite. -/
def theorem1_8_lengthsAgreePaper (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    (unzipLengthsOpen γ (wedgeConfig γ B Y ω) t).1 =
        (unzipLengthsOpen γ (wedgeConfig γ B Y ω) t).2 ∧
      (0 < t → 0 < (unzipLengthsOpen γ (wedgeConfig γ B Y ω) t).1 ∧
        (unzipLengthsOpen γ (wedgeConfig γ B Y ω) t).1 < ⊤)

/-- **Theorem 1.8, zipper stationarity** (p. 26), for area-carrying configurations: (1) existence,
non-degeneracy and uniqueness of the length-welding driver of `Y ω`, and the two round trips up to
`ConfigEqOff`; (2) the group property up to `ConfigEqOff`; (3) invariance of `configLawOff`. -/
def theorem1_8_zipperStationarityPaper (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) : Prop :=
  (∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
    (∃ p : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p) ∧
    qBoundaryMeasure γ (Y ω) (Set.Icc (lenWeldPoint γ (Y ω) ℓ) 0) = ENNReal.ofReal ℓ ∧
    (∀ p q : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p → IsLenWeldingDriver γ (Y ω) ℓ q →
      p.1 = q.1 ∧ ∀ s ∈ Set.Icc 0 p.1, p.2 s = q.2 s) ∧
    ConfigEqOff (zipLenDownA γ ℓ (zipLenA γ ℓ (wedgeAConfig γ B Y ω))).toPair
      (wedgeAConfig γ B Y ω).toPair ∧
    ConfigEqOff (zipLenA γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω))).toPair
      (wedgeAConfig γ B Y ω).toPair) ∧
  (∀ s t : ℝ, ∀ᵐ ω ∂P,
    ConfigEqOff (zipLenA γ (s + t) (wedgeAConfig γ B Y ω)).toPair
      (zipLenA γ s (zipLenA γ t (wedgeAConfig γ B Y ω))).toPair) ∧
  (∀ t : ℝ, configLawOff (fun ω => (zipLenA γ t (wedgeAConfig γ B Y ω)).toPair) P =
    configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P)

/-- **Theorem 1.8** (Sheffield, arXiv:1012.4797, p. 26), in the paper's form (D74, D75, D76):
wedge decomposition, agreement of the quantum lengths along `η` (open arcs), and length-zipper
stationarity for the pair of surfaces cut out by `η`, carried with their quantum area. -/
def theorem1_8Paper : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    IsBrownianReal B P → IsQuantumWedge γ (γ - 2 / γ) Y P → IndepFun (pathOf B) Y P →
    theorem1_8_decomposition γ P B Y ∧ theorem1_8_lengthsAgreePaper γ P B Y ∧
      theorem1_8_zipperStationarityPaper γ P B Y

end QuantumZipper
