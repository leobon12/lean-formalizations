import QuantumZipper.Proofs.Zipper.B2Reg
import QuantumZipper.Proofs.Zipper.B2Markov
import QuantumZipper.Proofs.GFF.CoordRegComp

/-!
# B2(b), regularity clauses without hypotheses

`blueprint/E_BRANCH_BLUEPRINT.md` §4, node B2(b), `handoff/E-B2.md` ("Remaining"). The pathwise
reductions `B2.h0f_regEq_of_regular` and `B2.evalReg_h0f_split_of_regular` are combined with the
RC3 composition law for the zipped fields (`CoordRegComp.ae_evalReg_Yf_fc` (R1),
`CoordRegComp.ae_evalReg_Yf_compact` (R2)):

* `ae_evalReg_h0f_compact`: a.s. `evalReg h⁰ ϖ = h⁰ ϖ` ((R2) at `t = 0`, `revMap V 0 = id` on `ℍ`);
* **`b2_coordsFull_eq`**, **`b2_regEq`**: a.s. `coordsFull h⁰ = coordsFull (coordChange Y_t (revMap V t) Q)`, hence `RegEq h⁰ (coordChange Y_t (revMap V t) Q)`;
* **`b2_evalReg_split`**: a.s. `evalReg h⁰ ϖ = evalReg Y_t ϖ_t + q_t`,

for `0 ≤ t ≤ T`, `B` Brownian independent of the free field `X`, `ϖ` a Frostman (`α > 0`)
probability measure carried by a compact subset of `ℍ`.

Sources: Sheffield, arXiv:1012.4797, Theorem 1.2 (p. 14), §5.2 (pp. 57–59); Duplantier–Sheffield,
Invent. Math. 185 (2011), Prop. 3.1 (through RC3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B2

open CharFun UnzipInvariance UnzipFull TwoPoint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [MeasurableSpace Ω] in
/-- At a continuous path, `revMap V 0` fixes a measure carried by `ℍ`. -/
theorem map_revMap_Vr_zero {ω : Ω} (hc : Continuous fun s => B s ω)
    (hT : 0 ≤ T) {μ : Measure ℂ} (hμ : ∀ᵐ z ∂μ, z ∈ H) :
    μ.map (revMap (Vr κ T B ω) 0) = μ := by
  have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have h : revMap (Vr κ T B ω) 0 =ᵐ[μ] id :=
    hμ.mono fun z hz => revMap_zero_eq hV (vrev_zero hT) hz
  rw [Measure.map_congr h, Measure.map_id]

/-- **(R2) at `t = 0`.** A.s. `evalReg h⁰ ϖ = h⁰ ϖ`. -/
theorem ae_evalReg_h0f_compact (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 ≤ T) {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ]
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hϖ : ϖ Kᶜ = 0)
    {α C : ℝ} (hFϖ : IsFrostman ϖ α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, evalReg (h0f κ T B X ω) ϖ = h0f κ T B X ω ϖ := by
  have hϖH : ∀ᵐ z ∂ϖ, z ∈ H := (ae_iff.2 hϖ).mono fun z hz => hKH hz
  filter_upwards [CoordRegComp.ae_evalReg_Yf_compact (κ := κ) hB hX hind le_rfl hT hK hKH hϖ
    hFϖ hα, hB.cont] with ω h hc
  rw [map_revMap_Vr_zero hc hT hϖH] at h
  exact h

/-- **B2(b), coordinate form (unconditional).** For `0 ≤ t ≤ T`, a.s.
`coordsFull h⁰ = coordsFull (coordChange Y_t (revMap V t) Q)`. -/
theorem b2_coordsFull_eq (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P, CoordsFull.coordsFull (h0f κ T B X ω) = CoordsFull.coordsFull
      (coordChange (Yf κ T t B X ω) (revMap (Vr κ T B ω) t) (Qc (Real.sqrt κ))) := by
  filter_upwards [ae_all_iff.2 (CoordRegComp.ae_evalReg_Yf_fc (κ := κ) hB hX hind ht htT),
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hreg hc h0
  funext i
  show h0f κ T B X ω (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
    coordChange (Yf κ T t B X ω) (revMap (Vr κ T B ω) t) (Qc (Real.sqrt κ))
      (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)
  rw [h0f_fc_split hc h0 ht htT _ (fullIndex_radius_pos i)]
  unfold coordChange qt
  rw [hreg i]

/-- **B2(b), `RegEq` clause (unconditional).** For `0 ≤ t ≤ T`, a.s.
`RegEq h⁰ (coordChange Y_t (revMap V t) Q)`. -/
theorem b2_regEq (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P, RegEq (h0f κ T B X ω) (coordChange (Yf κ T t B X ω) (revMap (Vr κ T B ω) t)
      (Qc (Real.sqrt κ))) := by
  filter_upwards [ae_all_iff.2 (CoordRegComp.ae_evalReg_Yf_fc (κ := κ) hB hX hind ht htT),
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hreg hc h0
  exact h0f_regEq_of_regular hc h0 ht htT hreg

/-- **B2(b), regularized split (unconditional).** For `0 ≤ t ≤ T` and a Frostman (`α > 0`)
probability measure `ϖ` carried by a compact `K ⊆ ℍ`, a.s.
`evalReg h⁰ ϖ = evalReg Y_t ϖ_t + q_t`. -/
theorem b2_evalReg_split (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) {ϖ : Measure ℂ}
    [IsProbabilityMeasure ϖ] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hϖ : ϖ Kᶜ = 0)
    {α C : ℝ} (hFϖ : IsFrostman ϖ α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, evalReg (h0f κ T B X ω) ϖ =
      evalReg (Yf κ T t B X ω) (ϖ.map (revMap (Vr κ T B ω) t)) + qt κ (Vr κ T B ω) t ϖ := by
  filter_upwards [ae_evalReg_h0f_compact (κ := κ) hB hX hind (ht.trans htT) hK hKH hϖ hFϖ hα,
    CoordRegComp.ae_evalReg_Yf_compact (κ := κ) hB hX hind ht htT hK hKH hϖ hFϖ hα,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω h1 h2 hc h0
  exact evalReg_h0f_split_of_regular hc h0 ht htT hK hKH hϖ h1 h2

end B2
end QuantumZipper
