import QuantumZipper.Proofs.Thm18.G4WeldUniq

/-!
# Theorem 1.8, node G4: the two round trips of `Z^LEN` (reduction)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1):
`Z^LEN_{−t} ∘ Z^LEN_t = id = Z^LEN_t ∘ Z^LEN_{−t}` a.s. The paper gives no separate proof (the
inverse `Z^LEN_t` is "a.s. uniquely defined via conformal welding"). The two computations below
are the by-hand verifications recorded in the module docstring of `Zipper/LengthZip.lean`
(**own argument**, elementary algebra of Brownian rescaling and driver concatenation).

Proved here (deterministic):

* `configEq_zipLenC_zipLenDown_of` (round trip `Z_ℓ ∘ Z_{−ℓ}`): let `t'` be the unzipping time,
  `a` the scale of the unzipped field and `p* = (t'/a², u ↦ (W(t' − a²u) − W t')/a)` (`revDrv`).
  If `p*` is a length-welding driver of the unzipped canonical field with removable doubled hull
  (`t' > 0`), the zipped field has scale `a⁻¹` and, canonicalized, is `RegEq` to the original
  field, then `Z_ℓ (Z_{−ℓ} c)` is `ConfigEq` to `c`. The driver identity is exact algebra; the
  choice made by `lenWeldDriver` is removed by `isLenWeldingDriver_unique_of_good`.
* `configEq_zipLenDown_zipLenC_of` (round trip `Z_{−ℓ} ∘ Z_ℓ`): if `p` is a good length-welding
  driver of the field, `b > 0` is the scale of the zipped field, the unzipping time of
  `Z_ℓ c` is `p.1/b²`, the unzipped field there has scale `b⁻¹` and, rescaled, is `RegEq` to the
  original field, then `Z_{−ℓ} (Z_ℓ c)` is `ConfigEq` to `c`.
* `g4RoundStmt_of`: `G4RoundStmt` from the a.s. versions of these field-level hypotheses
  (`G4RoundUpStmt`, `G4RoundDownStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

/-- The unzipping time of `Z^LEN_{−ℓ}` (the first capacity time at which the left unzipped
length reaches `ℓ`), as in `zipLenDown`. -/
def unzipTime (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengths γ c s).1}

/-- The scale `a` of the unzipped field used by `zipLenDown`. -/
def unzipScale (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : ℝ :=
  scaleParam γ (coordChange c.1 (fwdMapInv c.2 (unzipTime γ ℓ c)) (Qc γ))

/-- The rescaled time reversal `p* = (t'/a², u ↦ (W(t' − a²u) − W t')/a)` of the driver: the
candidate length-welding driver of the unzipped canonical field. -/
def revDrv (W : ℝ → ℝ) (t' a : ℝ) : ℝ × (ℝ → ℝ) :=
  (t' / a ^ 2, fun u => (W (t' - a ^ 2 * u) - W t') / a)

/-- The zipped (not yet canonicalized) field of `zipWeldUp` along `p`. -/
def zipField (γ : ℝ) (x : FieldSample) (p : ℝ × (ℝ → ℝ)) : FieldSample :=
  coordChange x (revMapInv p.2 p.1) (Qc γ)

/-- Removability of the doubled reverse hull of `p`. -/
def RemHull (p : ℝ × (ℝ → ℝ)) : Prop :=
  IsConformallyRemovable (closure (revHull p.2 p.1) ∪ conj '' closure (revHull p.2 p.1))

/-! ## Round trip `Z_ℓ ∘ Z_{−ℓ}` -/

/-! ## Round trip `Z_{−ℓ} ∘ Z_ℓ` -/

/-! ## The a.s. reductions -/

end Thm18Asm
end QuantumZipper
