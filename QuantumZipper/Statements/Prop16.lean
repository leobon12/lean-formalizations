import QuantumZipper.LQG.Local
import QuantumZipper.LQG.Wedge
import QuantumZipper.GFF.Defs
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Proposition 1.6 (zooming in at a quantum-typical boundary point)

Sheffield, *Conformal weldings of random surfaces*, Proposition 1.6. Specification only.

Let `D ⊂ ℍ` be a bounded domain with `∂D ∩ ℝ` a segment of positive length, `h̃` a GFF on `D`
with zero boundary conditions on `∂D \ ℝ` and free boundary conditions on `∂D ∩ ℝ`,
`[a,b] ⊆ ∂D ∩ ℝ`, `𝔥₀` continuous on `D` and continuously extendable to `(a,b)`, and
`h = 𝔥₀ + h̃`, with `E[ν_h[a,b]] < ∞`. Sample `h` from `ν_h[a,b] dh` (normalized), then `x` from
`ν_h|_{[a,b]}` (normalized), and let `h* = h(· + x)`. Then as `C → ∞` the doubly marked quantum
surfaces `S_{h* + C/γ}` converge in law to a `γ`-quantum wedge (canonical area measures
converging weakly on bounded subsets of `ℍ`).

Modelling choices:
* `γ ∈ (0,2)` (STATEMENT_SPEC B2: `C/γ` and `Q` are undefined at `γ = 0`).
* Geometry: `D` is a bounded domain in `ℍ`; `∂D ∩ ℝ = [c,d]` with `c < d`; and `D` contains a
  half-disc around every point of `(c,d)`, i.e. `(c,d)` is a genuine free boundary arc of `D`
  (this excludes e.g. slits of `∂D` ending on `(c,d)`). `[a,b] ⊆ [c,d]`, `a < b`.
* `h̃` is `IsMixedGFF D S` with free part `S = ∂D ∩ ℝ = [c,d]`.
* `𝔥₀` is continuous on `D ∪ (a,b)` (its values on `(a,b)` are the continuous extension), and
  enters as the deterministic field `ofFun 𝔥₀`.
* The field is constrained only on `D`, so all LQG measures are the local ones of A17: the
  boundary measure `ν_h = qBoundaryMeasureOn γ h (a,b)` on the open interval `(a,b)` (the only
  part of `∂D ∩ ℝ` where `𝔥₀` is controlled; `ν_h[a,b]` is read as `ν_h(a,b)`, the paper's
  measure being atom-free), and the area measure of the zoomed field on the translated domain
  `D − x`.
* Weighted law of `(h, x)`: the probability measure on `Ω × ℝ`
  `Qw = (E ν_h[a,b])⁻¹ · ∫ δ_ω ⊗ ν_{h(ω)}|_{[a,b]} dP(ω)`, as a `Measure.bind`. Its first marginal
  is `ν_h[a,b] dh` normalized and its conditional law of `x` given `h` is `ν_h|_{[a,b]}`
  normalized. We assume `0 < E ν_h[a,b] < ∞` (positivity holds in reality; it makes the
  normalization meaningful).
* STATEMENT_SPEC B3: `S_{h* + C/γ}` is the canonical description (unit local quantum area in
  `B₁(0)`, `canonicalOn`) of the field `h* + C/γ` living on `D − x`; after rescaling it lives on
  `canonicalDomainOn`, and its area measure is the local one on that domain
  (`AreaConvergesInLawOn`). Test functions have bounded support, and bounded subsets of `ℍ`
  eventually lie inside the rescaled domains. The limit wedge uses the global `qAreaMeasure`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QuantumZipper

/-- The real segment `[c,d]` (or any set of reals) as a subset of `ℂ`. -/
def realSet (S : Set ℝ) : Set ℂ := (fun t : ℝ => (t : ℂ)) '' S

/-- Proposition 1.6's boundary measure `ν_h` of `h = 𝔥₀ + x` on `(a,b)`: the local quantum
boundary length measure (A17) on the open interval `(a,b)`. -/
noncomputable def prop16Nu (γ : ℝ) (h0 : ℂ → ℝ) (a b : ℝ) (x : FieldSample) : Measure ℝ :=
  qBoundaryMeasureOn γ (ofFun h0 + x) (Set.Ioo a b)

/-- The weighted law of `(ω, x)` of Proposition 1.6: `ω` sampled from `ν_h[a,b] dP` and then
`x` from `ν_h|_{[a,b]}`, normalized jointly by `E ν_h[a,b]`. -/
noncomputable def prop16Law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ν : Ω → Measure ℝ) (a b : ℝ) : Measure (Ω × ℝ) :=
  (∫⁻ ω, ν ω (Set.Icc a b) ∂P)⁻¹ •
    P.bind (fun ω => (Measure.dirac ω).prod ((ν ω).restrict (Set.Icc a b)))

/-- The zoomed field `h(· + x) + C/γ` of Proposition 1.6. -/
noncomputable def zoomField (γ C : ℝ) (h : FieldSample) (x : ℝ) : FieldSample :=
  addConst (translate h (x : ℂ)) (C / γ)

/-- The domain `D − x = {z | z + x ∈ D}` on which `h(· + x)` lives. -/
def zoomDomain (D : Set ℂ) (x : ℝ) : Set ℂ := (fun z => z + (x : ℂ)) ⁻¹' D

/-- **Proposition 1.6.** Zooming in at a quantum-typical boundary point: under the weighted law
`prop16Law`, the canonical descriptions of `h(· + x) + C/γ` on `D − x` converge in law, as
`C → ∞`, to a `γ`-quantum wedge, in the sense of local area measures tested against continuous
compactly supported functions (A9, A17, B3). -/
def theorem1_6 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (D : Set ℂ) (c d a b : ℝ), IsOpen D → IsConnected D → Bornology.IsBounded D → D ⊆ H →
    c < d → frontier D ∩ {z : ℂ | z.im = 0} = realSet (Set.Icc c d) →
    (∀ t ∈ Set.Ioo c d, ∃ r > 0, Metric.ball (t : ℂ) r ∩ H ⊆ D) →
    a < b → c ≤ a → b ≤ d →
  ∀ h0 : ℂ → ℝ, ContinuousOn h0 (D ∪ realSet (Set.Ioo a b)) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsMixedGFF D (realSet (Set.Icc c d)) X P →
    0 < ∫⁻ ω, prop16Nu γ h0 a b (X ω) (Set.Icc a b) ∂P →
    ∫⁻ ω, prop16Nu γ h0 a b (X ω) (Set.Icc a b) ∂P < ⊤ →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : Ω' → FieldSample),
      IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ W P' ∧
      AreaConvergesInLawOn γ (prop16Law P (fun ω => prop16Nu γ h0 a b (X ω)) a b)
        (fun C p => canonicalOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))
        (fun C p => canonicalDomainOn γ (zoomField γ C (ofFun h0 + X p.1) p.2)
          (zoomDomain D p.2))
        P' W

end QuantumZipper
