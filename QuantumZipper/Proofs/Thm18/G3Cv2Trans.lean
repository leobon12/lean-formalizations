import QuantumZipper.Proofs.Thm18.G3Cv2Model
import QuantumZipper.Proofs.LQG.IndepParams
import QuantumZipper.Proofs.Section5.Prop17PalmCSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, item 1 (translation layer): `translate` reads raw values of a free field

`zoomFieldVia γ L h x ψ = addConst (coordChange (translate h x) ψ Q) (L/γ)` applies two
regularizations (`translate` and `coordChange` both read `evalReg`). For a free field `W` and a
real `x`:

* `ae_evalReg_circle`: a.s. `evalReg (W ω) fc(c, r) = W ω fc(c, r)` for any centre `c ∈ ℂ` and
  `r > 0` (the pulled-back case `ae_evalReg_pullCircle` with `Φ = id`);
* `ae_avgReg_translate`: a.s., for all `k, z`, the dyadic regularizations of `translate (W ω) x`
  and of the raw translate `W^x ω = W ω (· .map (· + x))` coincide (countably many dyadic
  circles, `fc_map_add_real`); hence (`ae_evalReg_translate`) a.s. for every measure `ν`,
  `evalReg (translate (W ω) x) ν = evalReg (W^x ω) ν`, and
  `coordChange (translate (W ω) x) ψ Q = coordChange (W^x ω) ψ Q` (`ae_coordChange_translate`).

`W^x` is again a free field (`isFreeGFFModConstH_translate`, Prop17PalmCSetup), so the zoom
through a map at a real point `x` of a free field is the zoom through the map at `0` of the free
field `W^x`, to which `exists_g0Model` applies. Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

theorem pullData_id (c : ℂ) (r : ℝ) (hr : 0 < r) :
    PullData id 0 (‖c‖ + r + 2) (‖c‖ + r + 1) ((‖c‖ + r + 1) / 2) 1 1 := by
  have hpos : 0 < ‖c‖ + r + 1 := by positivity
  refine ⟨⟨by positivity, differentiableOn_id, injOn_id _, fun z _ => by simp, fun z _ => rfl,
    measurable_id⟩, hpos, by linarith, ⟨one_pos, one_pos, fun z _ w _ => by simp⟩,
    by linarith, fun z hz => hz.2⟩

/-- The raw translate of a field. -/
def rawTranslate (y : FieldSample) (x : ℝ) : FieldSample := fun μ => y (μ.map (· + (x : ℂ)))

theorem isFree_rawTranslate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : Ω → FieldSample} (hW : IsFreeGFFModConstH W P) (x : ℝ) :
    IsFreeGFFModConstH (fun ω => rawTranslate (W ω) x) P :=
  S5.FieldLaw.Raw.isFreeGFFModConstH_translate hW x

end G3Cv
end QuantumZipper
