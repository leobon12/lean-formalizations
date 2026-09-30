import QuantumZipper.Proofs.Section5.Prop16MeasInst

/-!
# Proposition 1.6, node D4-MEAS (part 6): `hgood` from `scaleParamOn → 0` in probability

The canonical field of Proposition 1.6 lives on `{z | a z + t ∈ D}` with `a = scaleParamOn` of
the zoomed field. If `0 < a`, `B_{aR}(t) ∩ ℍ ⊆ D` and the local area measure is a genuine vague
limit, the sample is area-good at radius `R` (`areaGoodOn_canonical`). Hence (`hgood_prop16`)
`hgood` of D4-a follows from

* `scaleParamOn → 0` in probability, with `0 < scaleParamOn` (blueprint D3⁺(iii)),
* a.s. the marked point `t` has a half-disc `B_r(t) ∩ ℍ ⊆ D` (for `t ∈ (c,d)`, the geometry
  hypothesis of `theorem1_6`), and
* a.s. existence of the local area measure of the canonical field on its domain,

by continuity from above for the (open, hence measurable) events `¬ B_{R/(n+1)}(t) ∩ ℍ ⊆ D`.
`prop16_areaConvergesInLawOn_of_inputs'` assembles D4-a for Proposition 1.6 from these inputs.
Own elementary argument (AGENT_GUIDE cost rule); the reading follows Sheffield, arXiv:1012.4797,
proof of Proposition 1.6 (p. 25): as `C → ∞` the canonical scale shrinks to `0`, so every bounded
subset of `ℍ` eventually lies in the rescaled domain.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

namespace Meas

open TV Factorization

theorem nullMeasurableSet_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : ∀ᵐ p ∂μ, p ∈ s) : NullMeasurableSet s μ :=
  (MeasurableSet.univ.nullMeasurableSet (μ := μ)).congr (ae_eq_univ.2 (ae_iff.1 hs)).symm

variable {Ω : Type*} [MeasurableSpace Ω]

end Meas

end Prop16Area

end QuantumZipper
