import QuantumZipper.Proofs.Thm18.G1ZSplitDefs
import QuantumZipper.Proofs.Thm18.G1Rescale
import QuantumZipper.Proofs.LQG.GoodTransforms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (2): from `wedgeRep = canonical zU` to the unscaled wedge, with the curve maps

`wedgeRep γ X A = canonical γ W = rescale W Q b`, with `W = F2.zU γ X A` the unscaled wedge field
(circle-average embedding) and `b = scaleParam γ W`. The dilation moves the boundary measure by
`x ↦ x/b` (`GoodTransforms.qBoundaryMeasure_rescale`) and therefore also the Palm window. The
curve maps stay attached to the points of the dilated field. So the zoom of the dilated field at
`x/b` through a map `f` is the zoom of `W` at `x` through the **target-dilated** map `b · f`:

  `zoomFieldVia L (rescale W Q b) (x/b) f = zoomFieldVia L W x (b f)`

(`zoomFieldVia_rescale_apply`, at one test measure, from the chain rule `(b f)' = b f'` and
`log|b f'| = log b + log|f'|`). Plain zooms (`G3Pl3Dil.zoomLaw_rescale`) do not pass through this
identity.

* `canonical_zoomFieldVia_rescale`: equality of the canonical descriptions, once the three
  regularity identities (evaluation = regularized evaluation) hold at every pushed dyadic folded
  circle (`DilRegAt`, RC3 type, as in `G4RezipDet.rezipDown_fc_apply`).
* `wedgePalm_rescale`: the Palm-window integral of `rescale W Q b` through the maps `g x` (the
  form of `g1zWedgePalmInt`) equals the Palm-window integral of `W` through the maps
  `b · g (x/b)`.

Sheffield, arXiv:1012.4797, §1.6 (quantum surfaces are equivalence classes under
`h ↦ h ∘ ψ + Q log|ψ'|`) and p. 70. Own elementary argument (change of variables and the chain
rule; the pattern of `G4RezipDet` and `G3Pl3Dil.g3plPhi_rescale`).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

open D3Plus

/-- The regularity identities used at the test measure `σ`. -/
def DilRegAt (γ : ℝ) (y : FieldSample) (b x : ℝ) (f : ℂ → ℂ) (σ : Measure ℂ) : Prop :=
  evalReg (translate (rescale y (Qc γ) b) ((x / b : ℝ) : ℂ)) (σ.map f) =
      translate (rescale y (Qc γ) b) ((x / b : ℝ) : ℂ) (σ.map f) ∧
    evalReg (rescale y (Qc γ) b) ((σ.map f).map (· + ((x / b : ℝ) : ℂ))) =
      rescale y (Qc γ) b ((σ.map f).map (· + ((x / b : ℝ) : ℂ))) ∧
    evalReg (translate y (x : ℂ)) (σ.map fun w => (b : ℂ) * f w) =
      translate y (x : ℂ) (σ.map fun w => (b : ℂ) * f w) ∧
    Integrable (fun w => Real.log ‖deriv f w‖) σ ∧ ∀ᵐ w ∂σ, deriv f w ≠ 0

/-- **The zoom of a dilated field through a map, at one test measure.** -/
theorem zoomFieldVia_rescale_apply {γ : ℝ} (y : FieldSample) {b : ℝ} (hb : 0 < b) (L x : ℝ)
    {f : ℂ → ℂ} (hf : Measurable f) (σ : Measure ℂ) [IsFiniteMeasure σ]
    (h : DilRegAt γ y b x f σ) :
    zoomFieldVia γ L (rescale y (Qc γ) b) (x / b) f σ =
      zoomFieldVia γ L y x (fun w => (b : ℂ) * f w) σ := by
  obtain ⟨hR1, hR2, hR3, hint, hne⟩ := h
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  set c : ℂ := ((x / b : ℝ) : ℂ) with hc
  have hmb : Measurable fun z : ℂ => (b : ℂ) * z := measurable_const_mul _
  have hma : Measurable fun z : ℂ => z + c := measurable_add_const _
  have hbf : Measurable fun w => (b : ℂ) * f w := hmb.comp hf
  -- left side
  have eL : zoomFieldVia γ L (rescale y (Qc γ) b) (x / b) f σ =
      (evalReg (translate (rescale y (Qc γ) b) c) (σ.map f) +
        Qc γ * ∫ w, Real.log ‖deriv f w‖ ∂σ) + L / γ * (σ univ).toReal := rfl
  have eT1 : translate (rescale y (Qc γ) b) c (σ.map f) =
      evalReg (rescale y (Qc γ) b) ((σ.map f).map (· + c)) := rfl
  have eR : rescale y (Qc γ) b ((σ.map f).map (· + c)) =
      evalReg y (((σ.map f).map (· + c)).map fun z => (b : ℂ) * z) +
        Qc γ * ∫ z, Real.log ‖deriv (fun z : ℂ => (b : ℂ) * z) z‖ ∂((σ.map f).map (· + c)) := rfl
  have hmass : ((σ.map f).map (· + c)).real univ = σ.real univ := by
    simp only [measureReal_def]
    rw [Measure.map_apply hma MeasurableSet.univ, preimage_univ,
      Measure.map_apply hf MeasurableSet.univ, preimage_univ]
  have hcomp : ((σ.map f).map (· + c)).map (fun z => (b : ℂ) * z) =
      σ.map fun w => (b : ℂ) * f w + (x : ℂ) := by
    rw [Measure.map_map hma hf, Measure.map_map hmb (hma.comp hf)]
    congr 1
    funext w
    simp only [Function.comp, hc]
    push_cast
    field_simp
  -- right side
  have eR' : zoomFieldVia γ L y x (fun w => (b : ℂ) * f w) σ =
      (evalReg (translate y (x : ℂ)) (σ.map fun w => (b : ℂ) * f w) +
        Qc γ * ∫ w, Real.log ‖deriv (fun w => (b : ℂ) * f w) w‖ ∂σ) +
        L / γ * (σ univ).toReal := rfl
  have eT2 : translate y (x : ℂ) (σ.map fun w => (b : ℂ) * f w) =
      evalReg y ((σ.map fun w => (b : ℂ) * f w).map (· + (x : ℂ))) := rfl
  have hcomp2 : (σ.map fun w => (b : ℂ) * f w).map (· + (x : ℂ)) =
      σ.map fun w => (b : ℂ) * f w + (x : ℂ) := by
    rw [Measure.map_map (measurable_add_const _) hbf]; rfl
  have hlog : ∫ w, Real.log ‖deriv (fun w => (b : ℂ) * f w) w‖ ∂σ =
      σ.real univ * Real.log b + ∫ w, Real.log ‖deriv f w‖ ∂σ := by
    rw [deriv_const_mul_field']
    have e : (fun w => Real.log ‖(b : ℂ) * deriv f w‖) =ᵐ[σ]
        fun w => Real.log b + Real.log ‖deriv f w‖ := by
      filter_upwards [hne] with w hw
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le,
        Real.log_mul hb.ne' (norm_ne_zero_iff.2 hw)]
    rw [integral_congr_ae e, integral_add (integrable_const _) hint, integral_const, smul_eq_mul]
  rw [eL, hR1, eT1, hR2, eR, G1.integral_log_deriv_mul' hb, hmass, hcomp, eR', hR3, eT2,
    hcomp2, hlog]
  simp only [measureReal_def]
  ring

/-- The regularity hypotheses at all dyadic folded circles. -/
def DilReg (γ : ℝ) (y : FieldSample) (b x : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ (d : ℂ) (k : ℕ), DilRegAt γ y b x f (foldedCircle d (radius k))

/-- **Canonical descriptions of the zooms of a dilated field through a map.** -/
theorem canonical_zoomFieldVia_rescale {γ : ℝ} (y : FieldSample) {b : ℝ} (hb : 0 < b)
    (L x : ℝ) {f : ℂ → ℂ} (hf : Measurable f) (h : DilReg γ y b x f) :
    canonical γ (zoomFieldVia γ L (rescale y (Qc γ) b) (x / b) f) =
      canonical γ (zoomFieldVia γ L y x (fun w => (b : ℂ) * f w)) := by
  refine Factorization.canonical_congr ?_ γ
  funext k z
  unfold avgReg
  congr 1
  funext n
  exact zoomFieldVia_rescale_apply y hb L x hf _ (h _ k)

theorem preimage_div_half {b : ℝ} (hb : 0 < b) (left : Bool) :
    (fun u : ℝ => u / b) ⁻¹' g1SideHalf left = g1SideHalf left := by
  ext u
  cases left
  · simp only [g1SideHalf, Bool.false_eq_true, ite_false, mem_preimage, mem_Ioi]
    rw [lt_div_iff₀ hb, zero_mul]
  · simp only [g1SideHalf, ite_true, mem_preimage, mem_Iio]
    rw [div_lt_iff₀ hb, zero_mul]

theorem preimage_div_seg {b : ℝ} (hb : 0 < b) (left : Bool) (x : ℝ) :
    (fun u : ℝ => u / b) ⁻¹' g1SideSeg left (x / b) = g1SideSeg left x := by
  ext u
  cases left
  · simp only [g1SideSeg, Bool.false_eq_true, ite_false, mem_preimage, mem_Icc]
    rw [le_div_iff₀ hb, zero_mul, div_le_div_iff_of_pos_right hb]
  · simp only [g1SideSeg, ite_true, mem_preimage, mem_Icc]
    rw [div_le_div_iff_of_pos_right hb, div_le_iff₀ hb, zero_mul]

/-- **The Palm-window integral of a dilated field through the curve maps** (the integrand of
`g1zWedgePalmInt`): the dilated field `rescale y Q b` through the maps `g x` gives the same integral
as `y` through the target-dilated maps `b · g (x/b)`. -/
theorem wedgePalm_rescale {γ : ℝ} (hγ : 0 < γ) {y : FieldSample} (hy : IsLQGGood γ y) {b : ℝ}
    (hb : 0 < b) (left : Bool) (U L : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    (g : ℝ → ℂ → ℂ) (hg : ∀ x, Measurable (g x))
    (hreg : ∀ x ∈ g1SideHalf left, DilReg γ y b x (g (x / b))) :
    ∫⁻ x in g1zWedgeWin γ left (rescale y (Qc γ) b) U,
        Γ (locFieldFull R (canonical γ (zoomFieldVia γ L (rescale y (Qc γ) b) x (g x))))
        ∂((qBoundaryMeasure γ (rescale y (Qc γ) b)).restrict (g1SideHalf left)) =
      ∫⁻ x in g1zWedgeWin γ left y U,
        Γ (locFieldFull R (canonical γ (zoomFieldVia γ L y x (fun w => (b : ℂ) * g (x / b) w))))
        ∂((qBoundaryMeasure γ y).restrict (g1SideHalf left)) := by
  set ν := qBoundaryMeasure γ y with hν
  have hν' : qBoundaryMeasure γ (rescale y (Qc γ) b) = ν.map fun u => u / b :=
    GoodTransforms.qBoundaryMeasure_rescale hy hγ hb
  have hdiv : (fun u : ℝ => u / b) = fun u => u * b⁻¹ := funext fun u => div_eq_mul_inv u b
  have hemb : MeasurableEmbedding fun u : ℝ => u / b := by
    rw [hdiv]; exact (MeasurableEquiv.mulRight₀ b⁻¹ (inv_ne_zero hb.ne')).measurableEmbedding
  have hwin : (fun u : ℝ => u / b) ⁻¹' g1zWedgeWin γ left (rescale y (Qc γ) b) U =
      g1zWedgeWin γ left y U := by
    ext u
    show (u / b ∈ g1SideHalf left ∧ qBoundaryMeasure γ (rescale y (Qc γ) b)
        (g1SideSeg left (u / b)) ≤ ENNReal.ofReal U) ↔
      (u ∈ g1SideHalf left ∧ ν (g1SideSeg left u) ≤ ENNReal.ofReal U)
    rw [hν', hemb.map_apply, preimage_div_seg hb]
    exact and_congr_left' (Set.ext_iff.1 (preimage_div_half hb left) u)
  have hhalf : MeasurableSet (g1SideHalf left) := by
    cases left
    · exact measurableSet_Ioi
    · exact measurableSet_Iio
  rw [hν', hemb.restrict_map, hemb.restrict_map, hemb.lintegral_map, preimage_div_half hb, hwin]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (s := g1SideHalf left)
    (t := g1SideHalf left) subset_rfl (ae_restrict_mem hhalf) |> fun h =>
      (ae_restrict_of_ae (s := g1zWedgeWin γ left y U) h)] with x hx
  rw [canonical_zoomFieldVia_rescale y hb L x (hg _) (hreg x hx)]

end G3Z2b2
end Thm18Asm
end QuantumZipper
