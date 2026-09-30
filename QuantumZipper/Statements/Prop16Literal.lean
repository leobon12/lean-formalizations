import QuantumZipper.Statements.Prop16

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal companion (canonical descriptions on `ℍ`)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Proposition 1.6
(PDF p. 24, `literature/1012.4797.txt` lines 936–957):

> "Then as C → ∞ the random quantum surfaces S_{h*+C/γ} converge in law (w.r.t. the topology of
> convergence of doubly-marked quantum surfaces) to a γ-quantum wedge."

The surface `S_{h*+C/γ}` is described, as in the paper (PDF p. 21, lines 797–807), on `ℍ` with
marked points `0` and `∞`: if `φ_x : D − x → ℍ` is a conformal map with `φ_x(0) = 0`, the
`ℍ`-description of the surface is the coordinate change (1.3)
`(h* + C/γ) ∘ ψ_x + Q log |ψ_x'|`, `ψ_x = φ_x⁻¹ : ℍ → D − x`, and the canonical description
fixes the remaining dilation by (1.8), i.e. by unit quantum area in `B₁(0) ∩ ℍ`.

`theorem1_6` (`Statements/Prop16.lean`) normalizes by (1.8) *in place*, on `D − x`. This file
states the paper's version on `ℍ` as a companion (decision D95); `theorem1_6` is unchanged.

**The second marked point.** The paper does not say which point of `∂(D − x)` is the second
marked point (the preimage of `∞`). It only needs to exist: two choices give maps `φ_x`
differing by an automorphism of `(ℍ, 0)`, and once the second point is fixed the only freedom
left, the automorphisms of `(ℍ, 0, ∞)`, are the dilations, absorbed by (1.8). The statement
therefore quantifies over **every** measurable family `ψ_x` of such inverse maps (any choice of
second marked point, any `x`-dependence). The limit does not depend on the choice because the
canonical scale tends to `0`, and near `0` every `ψ_x` is a dilation to first order.

**Scope.** The chart hypothesis asks, for every `x ∈ (a,b)`, for a conformal map of `ℍ` onto
`D − x`. It can therefore hold only when `D` is simply connected, and for any other `D` this
statement is vacuous. This agrees with the paper, where a doubly marked quantum surface and its
canonical description are defined through a description on `ℍ`. For general `D`, use
`theorem1_6` (normalization in place on `D − x`), which covers every domain the hypotheses allow.

Modelling choices (beyond those of `theorem1_6`, which are kept verbatim):
* The family is given by the inverse maps `ψ x : ℍ → D − x` (so `φ_x = (ψ x)⁻¹`): holomorphic
  and injective on `ℍ` with image `D − x`, for every `x ∈ (a,b)`.
* `φ_x(0) = 0` with positive real derivative is a boundary condition; it is expressed through
  the Schwarz reflection of `ψ x` across the free arc near `0`: on some disc `B(0, r₀ x)`,
  `ψ x` is holomorphic and injective, real on `(−r₀ x, r₀ x)`, `ψ x 0 = 0` and
  `ψ_x'(0) > 0` (the admissible maps `IsG0Map` of the zoom-transfer node G0,
  `Proofs/Thm18/G1G0Stmt.lean`). This localizes the family condition near `0`.
  Joint measurability of `(x, z) ↦ ψ x z` and measurability of `r₀`.
* The zoomed field on `ℍ` is `zoomFieldLit γ C h x ψ = (h(· + x)) ∘ ψ + Q log|ψ'| + C/γ`
  (`coordChange` is (1.3) applied to `h* = h(· + x)`; the constant `C/γ` is added after the
  coordinate change, which as a field is `(h* + C/γ) ∘ ψ + Q log|ψ'|`, the paper's
  `S_{h*+C/γ}` read in the chart; this is the zoom `Thm18Asm.zoomFieldVia` of node G0).
* Its canonical description on `ℍ` is `canonicalOn` (1.8) with the local area measure (A17)
  read on `B(0, r₀ x) ∩ ℍ`, the part of `ℍ` where the reflected map is conformal; after the
  rescaling it lives on `canonicalDomainOn` (which exhausts `ℍ` as the scale tends to `0`).
  Only bounded subsets of `ℍ` are tested (compactly supported test functions), exactly as in
  `theorem1_6`, and the limit wedge uses the global `qAreaMeasure`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QuantumZipper

/-- The zoom of `h` at `x` read in the `ℍ`-coordinates given by `ψ : ℍ → D − x`:
`h(x + ψ(·)) + Q log|ψ'| + C/γ` (coordinate change (1.3) of `h* = h(· + x)`, then `+ C/γ`). -/
noncomputable def zoomFieldLit (γ C : ℝ) (h : FieldSample) (x : ℝ) (ψ : ℂ → ℂ) : FieldSample :=
  addConst (coordChange (translate h (x : ℂ)) ψ (Qc γ)) (C / γ)

/-- `ψ` is (the inverse of) a boundary-normalized conformal map `φ : D − x → ℍ` with
`φ(0) = 0`, `φ'(0) > 0`: `ψ` maps `ℍ` conformally onto `U`, and its Schwarz reflection is
holomorphic and injective on `B(0, r)`, real on `(−r, r)`, with `ψ 0 = 0`, `ψ'(0) > 0`. -/
def IsLitChart (U : Set ℂ) (r : ℝ) (ψ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ ψ H ∧ Set.InjOn ψ H ∧ ψ '' H = U ∧
    0 < r ∧ DifferentiableOn ℂ ψ (Metric.ball 0 r) ∧ Set.InjOn ψ (Metric.ball 0 r) ∧
    (∀ t : ℝ, |t| < r → (ψ t).im = 0) ∧ ψ 0 = 0 ∧ (deriv ψ 0).im = 0 ∧ 0 < (deriv ψ 0).re

/-- **Proposition 1.6, literal form (on `ℍ`).** Same hypotheses as `theorem1_6`; in addition, a
measurable family of charts `ψ x : ℍ → D − x` (inverses of conformal maps `φ_x : D − x → ℍ`
with `φ_x(0) = 0` and `φ_x'(0) > 0`, any second marked point). Under the weighted law
`prop16Law`, the canonical descriptions on `ℍ` of `S_{h* + C/γ}`, i.e. the (1.8)-normalizations
of `(h* + C/γ) ∘ ψ_x + Q log|ψ_x'|`, converge in law as `C → ∞` to a `γ`-quantum wedge, in the
area-measure topology of `theorem1_6` (A9, A17, B3). -/
def theorem1_6_literal : Prop :=
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
  ∀ (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ), Measurable (fun q : ℝ × ℂ => ψ q.1 q.2) → Measurable r₀ →
    (∀ x ∈ Set.Ioo a b, IsLitChart (zoomDomain D x) (r₀ x) (ψ x)) →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : Ω' → FieldSample),
      IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ W P' ∧
      AreaConvergesInLawOn γ (prop16Law P (fun ω => prop16Nu γ h0 a b (X ω)) a b)
        (fun C p => canonicalOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
          (Metric.ball 0 (r₀ p.2) ∩ H))
        (fun C p => canonicalDomainOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
          (Metric.ball 0 (r₀ p.2) ∩ H))
        P' W

end QuantumZipper
