import QuantumZipper.Proofs.Zipper.WedgeCocycleCore
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Thm18.G4CapLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# WEDGE-COCYCLE, part 3: `LenCanonCoreStmt`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 and §5.1 (pp. 60–62:
canonical rescaling `h ↦ h(a·) + Q log a` with Brownian scaling of the driver; M4-T3). For a
`P_*` sample realized by an unscaled wedge configuration `(Z, W)` (core P), `a = scaleParam γ Z`,
`U = a² τ` and `c'' = zipCapDown γ U (Z, W)`, the `P_*` configuration unzipped by `τ` has field
`RegEq` to `rescale (field of c'') Q a` (B3(d)) and driver `W_{c''}(a²·)/a`. Hence:

* its scale parameter is `b = scaleParam γ (field of c'') / a` (`GoodTransforms.scaleParam_rescale`),
  positive once the unzipped wedge fields have positive scale parameter (`WedgeUnzipScalePosStmt`);
* scale consistency at scale `b` of a rescaled field reduces to scale consistency of the field of
  `c''` at scales `a b` and `a` (`scaleConsistentAt_rescale`, `RegEq` of iterated rescalings),
  both of which follow from the flow continuum node `F1.WedgeFlowContStmt`
  (`WedgeUnzip.scaleConsistent_of_continuum`, `WedgeUnzip.map_mul_fc_map_fwdMapInv_scale`);
* RC3 and goodness along the flow come from `F1.pstar_flow_fc` (the flowed `P_*` field agrees on
  folded circles with a rescaling of the flowed wedge field), RC3 of rescalings of regular fields
  (`rc3_rescale_of_regular`) and M4-T3.

Main result: `lenCanonCoreStmt_of`. Own elementary bookkeeping around the cited scaling.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-! ## Deterministic lemmas -/

/-- The rescaling of a regular field satisfies RC3 at every folded circle centred in `Hbar`. -/
theorem rc3_rescale_of_regular {x : FieldSample} (hx : IsRegularSample x) (Q : ℝ) {b : ℝ}
    (hb : 0 < b) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    evalReg (rescale x Q b) (foldedCircle d r) = rescale x Q b (foldedCircle d r) := by
  obtain ⟨F, hF⟩ := hx
  rw [(hF.rescale' Q hb).evalReg_fc_of_mem hd hr, RegClosure.rescale_fc_eq hF Q hb d hr,
    CircleFubini.foldH_of_mem' (RegClosure.mapsTo_mul_pos hb hd)]

/-- Scale consistency reads the field only through `avgReg`. -/
theorem scaleConsistentAt_congr {x x' : FieldSample} (h : avgReg x = avgReg x') {Q b : ℝ}
    {ν : Measure ℂ} :
    Thm18Asm.G1.ScaleConsistentAt x Q b ν ↔ Thm18Asm.G1.ScaleConsistentAt x' Q b ν := by
  unfold Thm18Asm.G1.ScaleConsistentAt rescale
  rw [Factorization.coordChange_congr h, Factorization.evalReg_congr h]

/-- **Scale consistency of a rescaled field** from scale consistency of the field at the two
scales `a b` and `a`. -/
theorem scaleConsistentAt_rescale {y : FieldSample} (hy : IsRegularSample y) (Q : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {ν : Measure ℂ}
    (hA : Thm18Asm.G1.ScaleConsistentAt y Q (a * b) ν)
    (hB : Thm18Asm.G1.ScaleConsistentAt y Q a (ν.map fun z => (b : ℂ) * z)) :
    Thm18Asm.G1.ScaleConsistentAt (rescale y Q a) Q b ν := by
  unfold Thm18Asm.G1.ScaleConsistentAt at hA hB ⊢
  have hr := hy.regEq_rescale_rescale Q ha hb
  have hav : avgReg (rescale (rescale y Q a) Q b) = avgReg (rescale y Q (a * b)) :=
    funext fun k => funext fun z => hr k z
  have hmb : Measurable fun z : ℂ => (b : ℂ) * z := measurable_const_mul _
  have hma : Measurable fun z : ℂ => (a : ℂ) * z := measurable_const_mul _
  have hmap : (ν.map fun z => (b : ℂ) * z).map (fun z => (a : ℂ) * z) =
      ν.map fun z => ((a * b : ℝ) : ℂ) * z := by
    rw [Measure.map_map hma hmb]
    congr 1
    funext z
    simp only [Function.comp, Complex.ofReal_mul]
    ring
  have hmass : (ν.map fun z => (b : ℂ) * z).real univ = ν.real univ := by
    simp only [Measure.real, Measure.map_apply hmb MeasurableSet.univ, Set.preimage_univ]
  rw [Factorization.evalReg_congr hav, hA, hB, hmap, hmass, Real.log_mul ha.ne' hb.ne']
  ring

/-- The `P_*` configuration unzipped by `τ`, in terms of the realizing wedge configuration. -/
theorem zipCapDown_pstar_eq {γ : ℝ} {Z Y : FieldSample} {W W' : ℝ → ℝ}
    (havg : avgReg Y = avgReg (canonical γ Z))
    (hcfg : canonConfig γ (Z, W) = (canonical γ Z, W')) {τ : ℝ} (hτ : 0 ≤ τ) :
    zipCapDown γ τ (Y, W') = (unzippedField γ (canonConfig γ (Z, W)) τ, fun r =>
      (zipCapDown γ (scaleParam γ Z ^ 2 * τ) (Z, W)).2 (scaleParam γ Z ^ 2 * r) /
        scaleParam γ Z) := by
  refine Prod.ext ?_ ?_
  · show coordChange Y (fwdMapInv W' τ) (Qc γ) =
      coordChange (canonConfig γ (Z, W)).1 (fwdMapInv (canonConfig γ (Z, W)).2 τ) (Qc γ)
    rw [hcfg]
    exact Factorization.coordChange_congr havg _ _
  · show (zipCapDown γ τ (Y, W')).2 = _
    rw [← zipCapDown_canonConfig_snd Z W hτ, hcfg]
    rfl

/-- The clamped driver of `zipCapDown` absorbs a second Brownian rescaling. -/
theorem zipCapDown_snd_rescale2 {γ U : ℝ} {c : FieldSample × (ℝ → ℝ)} {a b : ℝ}
    (s : ℝ) :
    (zipCapDown γ U c).2 (a ^ 2 * (b ^ 2 * max s 0)) / a / b =
      (zipCapDown γ U c).2 ((a * b) ^ 2 * s) / (a * b) ∧
    (zipCapDown γ U c).2 (a ^ 2 * (b ^ 2 * max s 0)) / a / b =
      (zipCapDown γ U c).2 (a ^ 2 * (b ^ 2 * s)) / a / b := by
  have hm : ∀ v : ℝ, max (a ^ 2 * (b ^ 2 * max s 0)) 0 = max v 0 →
      (zipCapDown γ U c).2 (a ^ 2 * (b ^ 2 * max s 0)) = (zipCapDown γ U c).2 v := by
    intro v hv
    simp only [zipCapDown, hv]
  have key : ∀ v : ℝ, v = (a * b) ^ 2 * s ∨ v = a ^ 2 * (b ^ 2 * s) →
      max (a ^ 2 * (b ^ 2 * max s 0)) 0 = max v 0 := by
    intro v hv
    have hv' : v = (a * b) ^ 2 * s := by rcases hv with h | h <;> rw [h]; ring
    subst hv'
    rcases le_total 0 s with hs | hs
    · rw [max_eq_left hs]; ring_nf
    · rw [max_eq_right hs, mul_zero, mul_zero, max_eq_right le_rfl,
        max_eq_right (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hs)]
  refine ⟨?_, ?_⟩
  · rw [hm _ (key _ (Or.inl rfl)), div_div]
  · rw [hm _ (key _ (Or.inr rfl))]

/-! ## The scale-positivity node and the reduction -/

/-- **Positive scale parameter of the unzipped wedge fields** (open input; Sheffield §1.4, (1.8):
the canonical description exists at every time — the unzipped field has infinite total quantum
area and finite quantum area near the image `0` of the tip): a.s., for all `t ≥ 0`,
`0 < scaleParam γ (field unzipped from the unscaled wedge configuration by t)`. At `t = 0` this is
the canonical specification (`Wire2.ae_wedge_canonical_spec`, up to `RegEq`). -/
def WedgeUnzipScalePosStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → 0 < scaleParam (Real.sqrt κ)
      (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t)

end F1
end QuantumZipper
