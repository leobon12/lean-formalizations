import QuantumZipper.Proofs.Thm18.G3Pl4Asm
import QuantumZipper.Proofs.Thm18.G3Pl4Norm
import QuantumZipper.Proofs.Zipper.CfgBatchLawData
import QuantumZipper.Proofs.Zipper.E5IncField
import QuantumZipper.Proofs.Zipper.LocRichBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): law transfer from the coupled free field to `h_C`

* `lintegral_phiCap_eq_of_coordsLaw`: the capped Palm functional reads a good field only through
  its circle coordinates `coordsFull` (via `avgReg`), so its expectation only depends on the law of
  the circle coordinates.
* `g3pl4_coordsLaw_eq`: for a normalized free field `V` (`V(S) = 0`), `V + (γ − 2/γ)(−log|·|)` and
  `h_C = normField + (−γ log|·|)` have the same law of circle coordinates (both are a normalized
  free field plus the same deterministic function on probability measures; the normalized free
  field law is universal, `E6.fieldLawFull_eq_of_normalized`).
* `g3pl4_lintegral_phiCap_V_eq`: hence `E[Φcap(V + log)] = g3plHonX`.

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

theorem g3pl4_measurable_data {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample}
    (hY : ∀ μ : Measure ℂ, Measurable fun ω => Y ω μ) :
    Measurable fun ω => ((CoordsFull.coordsFull (Y ω), fun ρ : TestFun H => pairRaw (Y ω) ρ.1) :
      (ℕ → ℝ) × (TestFun H → ℝ)) :=
  Measurable.prodMk (measurable_pi_iff.2 fun _ => hY _)
    (measurable_pi_iff.2 fun _ => (D3Plus.measurable_pairRaw_apply _).comp
      (measurable_pi_iff.2 hY))

/-- **The circle law of `V + log` is that of `h_C`.** -/
theorem g3pl4_coordsLaw_eq {γ : ℝ} (hγ : 0 < γ) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {V : Ω' → FieldSample}
    (hV : IsFreeGFFModConstH V P') (hVn : ∀ᵐ ω ∂P', V ω (foldedCircle 0 1) = 0) :
    P'.map (fun ω => CoordsFull.coordsFull (V ω + F2.logSingField (γ ^ 2))) =
      gffBase.P.map (fun ω => CoordsFull.coordsFull (g3pField γ (g3wProf γ) ω)) := by
  have := gffBase.prob
  set X₀ := gffBase.X
  have hX₀m : ∀ μ : Measure ℂ, Measurable fun ω => X₀ ω μ := gffBase.gff.measurable_coord
  set Xn : gffBase.Ω → FieldSample := fun ω => addConst (X₀ ω) (-(X₀ ω refS)) with hXn
  have hXnm : ∀ μ : Measure ℂ, Measurable fun ω => Xn ω μ := fun μ =>
    (hX₀m μ).add ((hX₀m _).neg.mul measurable_const)
  have hXnfree : IsFreeGFFModConstH Xn gffBase.P :=
    E5.isFreeGFFModConstH_of_ae_shift gffBase.gff (fun ω => -(X₀ ω refS)) hXnm
      (fun μ _ => ae_of_all _ fun ω => by simp only [hXn, addConst]; ring)
  have hXnn : ∀ᵐ ω ∂gffBase.P, Xn ω (foldedCircle 0 1) = 0 := ae_of_all _ fun ω => by
    simp only [hXn, addConst, measure_univ, ENNReal.toReal_one, mul_one]
    ring
  have hlaw := E6.fieldLawFull_eq_of_normalized hV hVn hXnfree hXnn
  set k : ℕ → ℝ := fun n => CoordsFull.coordsFull (F2.logSingField (γ ^ 2)) n
  have hg : Measurable fun d : (ℕ → ℝ) × (TestFun H → ℝ) => d.1 + k :=
    measurable_fst.add measurable_const
  have hVm : ∀ μ : Measure ℂ, Measurable fun ω => V ω μ := hV.measurable_coord
  have e := congrArg (fun m : Measure ((ℕ → ℝ) × (TestFun H → ℝ)) => m.map
    fun d => d.1 + k) hlaw
  unfold fieldLawFull at e
  rw [Measure.map_map hg (g3pl4_measurable_data hVm),
    Measure.map_map hg (g3pl4_measurable_data hXnm)] at e
  convert e using 2
  · funext ω n
    simp [CoordsFull.coordsFull, k]
  · funext ω n
    simp only [Function.comp, Pi.add_apply, k, CoordsFull.coordsFull]
    rw [g3pl4_hC_fc γ hγ]
    simp only [hXn, addConst, measure_univ, ENNReal.toReal_one, mul_one]
    ring

end R18
end QuantumZipper
