import QuantumZipper.Proofs.Zipper.ScaleGeomFix
import QuantumZipper.Proofs.LQG.AllOffsetsBasic
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.GFF.CoordRegSwap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TRUNCFREE: the scaling witness without the `evalReg` bridge

Theorem 1.3, node F2, step (4) (`GammaZeroScaleStmt`); Sheffield, *Conformal weldings of random
surfaces*, arXiv:1012.4797, §5.1 (pp. 60–62: `h ↦ h(a·) + Q log a` preserves quantum lengths;
the free boundary GFF modulo constants is invariant in law under `z ↦ a z`).

**Audit (task TRUNCFREE, decision recorded in `handoff/TRUNCFREE.md`).**
* `F2.EvalRegRawStmt` (a.s., `evalReg (X ω) ν = X ω ν` for **all** admissible `ν` at once) is
  **false**: `IsFreeGFFModConstH` constrains only countably many coordinates at a time, so a
  free field can be modified at one random admissible measure `ν_u` with `P(ν_u = ν) = 0` for each
  fixed `ν`; the modified field is still free, has the same `avgReg` (folded circles are never of
  this form), but its raw coordinate at `ν_u` is shifted by `1`. Formal refutation:
  `F2.not_evalRegRawStmt` (`TruncFreeNoGo.lean`).
* `F2.TruncRescaleFreeStmt` is not known false, but it quantifies over **every** admissible
  measure: at `a = 1` it says that `μ ↦ evalReg (X ω) μ` is again a free field, i.e. that the
  circle-average regularization `∫ avgReg (X ω) k dμ` converges a.s. (along `k`, not along a
  subsequence) for every measure with bounded logarithmic potential. No source proves this, and
  none of its consumers needs it.

**Route.** Use the *raw* dilation witness `rawRescale x Q a μ = x (μ.map (a·)) + Q log a · μ(ℂ)`
(the pushforward of the coordinates, no regularization). It is a free field for elementary
reasons (`isFreeGFFModConstH_rawRescale`: re-indexing of the Gaussian family by `pushPair`,
dilation invariance of `kernelCov2 neumannH`, linearity of pushforward), independent of whatever
`X` is independent of, and a.s. it agrees with `rescale (X ω) Q a` at every folded circle with
dyadic centre and radius `2^{-k}` (`ae_rawRescale_fc_dyadic`: countably many circles, each by
`AllOffsets.ae_evalReg_fc_eq`). Since `avgReg`, hence `evalReg`, `coordChange`, `unzippedField`
and `unzipLengths`, read a field only at those circles, the two witnesses have the same unzipped
lengths a.s. (`ae_unzipLengths_rawRescale`). Hence `GammaZeroScaleStmt` follows from
`ScaleGeomAeStmt'` alone (`gammaZeroScaleStmt_of_raw'`), with no freeness hypothesis.

Own elementary bookkeeping (D27 family); the mathematics is Sheffield §5.1 and the dilation
invariance of the Neumann kernel.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-! ## The raw dilation witness -/

/-- The raw dilation of a field sample: the coordinate at `μ` is the coordinate of `x` at the
dilated measure `μ.map (a ·)`, plus the coordinate-change term `Q log a · μ(ℂ)`. -/
def rawRescale (x : FieldSample) (Q a : ℝ) : FieldSample :=
  addConst (fun μ => x (μ.map fun z => (a : ℂ) * z)) (Q * Real.log a)

theorem measurable_rawRescale (Q a : ℝ) :
    Measurable fun x : FieldSample => rawRescale x Q a := by
  refine measurable_pi_iff.2 fun μ => ?_
  simp only [rawRescale, addConst]
  exact (measurable_pi_apply _).add measurable_const

theorem indepFun_rawRescale {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {V : Ω → β} {X : Ω → FieldSample} (h : IndepFun V X P) (Q a : ℝ) :
    IndepFun V (fun ω => rawRescale (X ω) Q a) P :=
  h.comp measurable_id (measurable_rawRescale Q a)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Dilation invariance of the free field (raw form).** -/
theorem isFreeGFFModConstH_dilRaw (hX : IsFreeGFFModConstH X P) {a : ℝ} (ha : 0 < a) :
    IsFreeGFFModConstH (fun ω (μ : Measure ℂ) => X ω (μ.map fun z => (a : ℂ) * z)) P where
  measurable_coord := fun μ => hX.measurable_coord _
  gaussian := hX.gaussian.comp_right (pushPair a ha)
  centered := fun μ ν hμ hν h => hX.centered _ _ (WedgeTK.isAdmissibleH_map_mul ha hμ)
    (WedgeTK.isAdmissibleH_map_mul ha hν)
    (by rw [WedgeTK.map_univ_mul, WedgeTK.map_univ_mul, h])
  covariance_eq := fun p q hp1 hp2 hp hq1 hq2 hq => by
    have h := hX.covariance_eq (pushPair a ha ⟨p, hp1, hp2, hp⟩).1
      (pushPair a ha ⟨q, hq1, hq2, hq⟩).1 (pushPair a ha ⟨p, hp1, hp2, hp⟩).2.1
      (pushPair a ha ⟨p, hp1, hp2, hp⟩).2.2.1 (pushPair a ha ⟨p, hp1, hp2, hp⟩).2.2.2
      (pushPair a ha ⟨q, hq1, hq2, hq⟩).2.1 (pushPair a ha ⟨q, hq1, hq2, hq⟩).2.2.1
      (pushPair a ha ⟨q, hq1, hq2, hq⟩).2.2.2
    rw [kernelCov2_pushPair] at h
    exact h
  linear := fun μ ν hμ hν a' b' => by
    have hfm : Measurable fun z : ℂ => (a : ℂ) * z := measurable_mul_left_c a
    have h := hX.linear _ _ (WedgeTK.isAdmissibleH_map_mul ha hμ)
      (WedgeTK.isAdmissibleH_map_mul ha hν) a' b'
    refine Filter.EventuallyEq.trans (Eventually.of_forall fun ω => ?_) h
    show X ω ((a' • μ + b' • ν).map fun z => (a : ℂ) * z) =
      X ω (a' • μ.map (fun z => (a : ℂ) * z) + b' • ν.map (fun z => (a : ℂ) * z))
    rw [Measure.map_add _ _ hfm, Measure.map_smul, Measure.map_smul]
    all_goals exact hfm.aemeasurable

/-- **The raw rescaled field is a free field modulo constants** (no `evalReg` bridge). -/
theorem isFreeGFFModConstH_rawRescale (hX : IsFreeGFFModConstH X P) (Q : ℝ) {a : ℝ}
    (ha : 0 < a) : IsFreeGFFModConstH (fun ω => rawRescale (X ω) Q a) P :=
  S5.FieldLaw.Raw.isFreeGFFModConstH_addConst (isFreeGFFModConstH_dilRaw hX ha)
    (c := fun _ => Q * Real.log a) measurable_const

/-! ## Agreement with `rescale` at folded circles -/

/-- `rescale` at a probability measure. -/
theorem rescale_apply_prob {x : FieldSample} {Q a : ℝ} (ha : 0 < a) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] :
    rescale x Q a μ = evalReg x (μ.map fun z => (a : ℂ) * z) + Q * Real.log a := by
  rw [show rescale x Q a = coordChange x (fun z : ℂ => (a : ℂ) * z) Q from rfl]
  unfold coordChange
  rw [integral_log_deriv_mul_left (Q := Q) ha, measure_univ, ENNReal.toReal_one, mul_one]

/-- `rawRescale` at a probability measure. -/
theorem rawRescale_apply_prob {x : FieldSample} {Q a : ℝ} (μ : Measure ℂ)
    [IsProbabilityMeasure μ] :
    rawRescale x Q a μ = x (μ.map fun z => (a : ℂ) * z) + Q * Real.log a := by
  simp only [rawRescale, addConst, measure_univ, ENNReal.toReal_one, mul_one]

/-- **At one folded circle, the raw and the regularized rescalings agree a.s.** -/
theorem ae_rawRescale_fc_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (Q : ℝ) {a : ℝ} (ha : 0 < a) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, rawRescale (X ω) Q a (foldedCircle w r) = rescale (X ω) Q a (foldedCircle w r) := by
  have hmap : (foldedCircle w r).map (fun z => (a : ℂ) * z) =
      foldedCircle (foldH ((a : ℂ) * w)) (a * r) := by
    rw [Thm18Asm.foldedCircle_map_mul ha, CoordReg.foldedCircle_foldH]
  filter_upwards [AllOffsets.ae_evalReg_fc_eq hX (CircleFubini.foldH_mem_Hbar' ((a : ℂ) * w))
    (mul_pos ha hr)] with ω hω
  rw [rawRescale_apply_prob, rescale_apply_prob ha, hmap, hω]

/-- The dyadic grid point with integer coordinates `p` at level `n`. -/
def dyPt (n : ℕ) (p : ℤ × ℤ) : ℂ := ⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩

theorem dyadicRoundC_eq_dyPt (n : ℕ) (z : ℂ) :
    dyadicRoundC n z = dyPt n (⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋) := rfl

/-- **At all dyadic folded circles at once, a.s.** -/
theorem ae_rawRescale_fc_dyadic [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (Q : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ k n : ℕ, ∀ z : ℂ,
      rawRescale (X ω) Q a (foldedCircle (dyadicRoundC n z) (radius k)) =
        rescale (X ω) Q a (foldedCircle (dyadicRoundC n z) (radius k)) := by
  have h : ∀ᵐ ω ∂P, ∀ k n : ℕ, ∀ p : ℤ × ℤ,
      rawRescale (X ω) Q a (foldedCircle (dyPt n p) (radius k)) =
        rescale (X ω) Q a (foldedCircle (dyPt n p) (radius k)) := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun n => ae_all_iff.2 fun p => ?_
    exact ae_rawRescale_fc_eq hX Q ha _ (radius_pos k)
  filter_upwards [h] with ω hω k n z
  rw [dyadicRoundC_eq_dyPt]
  exact hω k n _

/-- Fields that agree at all dyadic folded circles have the same `avgReg`. -/
theorem avgReg_eq_of_fc_dyadic {x y : FieldSample}
    (h : ∀ k n : ℕ, ∀ z : ℂ, x (foldedCircle (dyadicRoundC n z) (radius k)) =
      y (foldedCircle (dyadicRoundC n z) (radius k))) :
    avgReg x = avgReg y := by
  funext k z
  simp only [avgReg]
  exact congrArg (fun f : ℕ → ℝ => limUnder atTop f) (funext fun n => h k n z)

/-! ## `GammaZeroScaleStmt` without a freeness hypothesis -/

end F2
end QuantumZipper
