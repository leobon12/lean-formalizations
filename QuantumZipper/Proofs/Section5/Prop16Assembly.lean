import QuantumZipper.Proofs.Section5.Prop16AssemblyBasic
import QuantumZipper.Proofs.GFF.K3.MixedM5Stmt

/-!
# Proposition 1.6, top-level assembly (PROP16-ASM)

`theorem1_6_of_nodes : … → theorem1_6` assembles Proposition 1.6 (Sheffield, *Conformal weldings
of random surfaces*, arXiv:1012.4797, Prop. 1.6, p. 24, proof p. 25) from

* the **proved** nodes, used directly:
  - D4-a (`Prop16Area.areaConvergesInLawOn_of_tvLocal`, through its instantiation
    `Prop16Area.Meas.prop16_areaConvergesInLawOn_of_inputs'`, which also discharges the
    measurability inputs `hY`, `hmeas` and derives `hgood` from the scale input);
  - the wedge prerequisites (`WedgeFinZero.wedgeFiniteNearZero_holds`,
    `WedgeInf.wedgeInfiniteTotal`, `WedgeMeasND`): coordinate measurability and a.s. area
    measure of the limiting wedge (`Prop16AssemblyBasic`);
  - D1's s-finite kernel `Palm.kerI` (normalization of `prop16Law`);
* and five **not yet proved** nodes, taken as hypotheses with exact statements below. Each
  quantifies over the data of `theorem1_6` (`Prop16Data`) and is stated for the weighted law
  `prop16Q` exactly as `theorem1_6` uses it:
  - `Prop16NuMeasStmt` (D4-MEAS): `ω ↦ ν_{h(ω)}` is a.e.-measurable;
  - `Prop16ZoomAreaStmt`, `Prop16CanonAreaStmt` (local area existence, mixed-field M4-type
    input transported to the Palm law): the zoomed and canonical fields a.s. have a local area
    measure;
  - `Prop16ScaleStmt` (D3⁺(iii) transported through D1/M6/M7): the canonical scale tends to `0`
    in probability, with positivity;
  - `Prop16TVStmt` (D4⁺): TV-local convergence of the canonical fields to a `γ`-quantum wedge.
    **Warning (see `handoff/PROP16-ASM.md`):** for a merely continuous `𝔥₀` this TV form is very
    likely false (Cameron–Martin singularity of non-`H¹` shifts); the paper's convergence is weak.

The statement `theorem1_6` is not modified.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV

/-- The data of Proposition 1.6: exactly the hypotheses of `theorem1_6` (the geometry part is
`K3.Prop16Geometry`, used by the K3 mixed-field nodes). -/
def Prop16Data (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample) : Prop :=
  0 < γ ∧ γ < 2 ∧ K3.Prop16Geometry D c d ∧ a < b ∧ c ≤ a ∧ b ≤ d ∧
    ContinuousOn h0 (D ∪ realSet (Set.Ioo a b)) ∧ IsProbabilityMeasure P ∧
    IsMixedGFF D (realSet (Set.Icc c d)) X P ∧
    0 < ∫⁻ ω, prop16Nu γ h0 a b (X ω) (Set.Icc a b) ∂P ∧
    ∫⁻ ω, prop16Nu γ h0 a b (X ω) (Set.Icc a b) ∂P < ⊤

/-- The weighted law of `(ω, x)` of `theorem1_6`. -/
abbrev prop16Q (γ : ℝ) (h0 : ℂ → ℝ) (a b : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → FieldSample) : Measure (Ω × ℝ) :=
  prop16Law P (fun ω => prop16Nu γ h0 a b (X ω)) a b

/-- **Node D4-MEAS (kernel).** The random boundary measure `ω ↦ ν_{h(ω)}` of Proposition 1.6 is
a.e.-measurable (Giry σ-algebra). Without it `prop16Law` is the junk measure `0`. -/
def Prop16NuMeasStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P

/-- **Node: local area of the zoomed field.** Under the weighted law, for every level `C`, a.s. the
zoomed field `h(· + x) + C/γ` has a local area measure (a vague limit of `areaApprox`) on
`D − x`. -/
def Prop16ZoomAreaStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ C : ℝ, ∀ᵐ p ∂(prop16Q γ h0 a b P X), ∃ m, IsVagueLimitOn (zoomDomain D p.2)
      (areaApprox γ (zoomField γ C (ofFun h0 + X p.1) p.2)) m

/-- **Node: local area of the canonical field.** Under the weighted law, for every level `C`, a.s.
the canonical description of the zoomed field has a local area measure on its domain. -/
def Prop16CanonAreaStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ C : ℝ, ∀ᵐ p ∂(prop16Q γ h0 a b P X), ∃ m,
      IsVagueLimitOn (canonicalDomainOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))
        (areaApprox γ (canonicalOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))) m

/-- **Node: the canonical scale tends to `0`** (D3⁺(iii), transported to the Palm law): for every
`δ > 0`, `Q {¬ (0 < scaleParamOn < δ)} → 0` as `C → ∞`. -/
def Prop16ScaleStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ δ > 0, Tendsto (fun C => prop16Q γ h0 a b P X {p |
      ¬ (0 < scaleParamOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2) ∧
        scaleParamOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2) < δ)})
      atTop (𝓝 0)

end Prop16Asm

end QuantumZipper
