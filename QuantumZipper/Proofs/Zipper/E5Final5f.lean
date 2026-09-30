import QuantumZipper.Proofs.Zipper.E5Final5e
import QuantumZipper.Proofs.Zipper.E5Asm3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-REPR-FINAL, part f: the driver part of the collision correction is `Ξ`-measurable

Task E5-REPR-FINAL (Theorem 1.3, node E5, decision D39); Sheffield, arXiv:1012.4797, §5.4.

`E5IncSwitch.setup_locCorr_switch_reg` (and `E5Final2.zoomModel_lvl`) take as hypothesis `hdrv`:
the driver part `locCorrDrv κ V t ϖ z = −(√κ/2) k_{ϖ_t}(z) − ∫ shiftFun dϖ_t − q_t` of the
collision correction is measurable for the σ-algebra of the conditioning data `Ξ`. On the level
space (`Ξ =` the level point) this file proves it at **any** measurable nonnegative level time
`τ` (`measurable_locCorrDrv_lvl_time`), in particular at the level collision time `T − T_ℓ`
(`hdrv` of `zoomModel_lvl`, `measurable_locCorrDrv_lvl`) and at the clipped germ-free time
`max (T − T_ℓ − u₀) 0` of `E5Final5d` (`measurable_locCorrDrv_lvl_germFree`).

The proofs are those of `E5Asm3` (`measurable_qt_level`, `measurable_kPot_level`,
`measurable_shiftFun_level`) with the level time generalized: joint measurability of the reverse
maps (`E5Final5e.measurable_revMap_level_time`), the derivative as a limit of difference
quotients, and parametric integrals against `ϖ`. Own bookkeeping.
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov B2 E1 E4Grid CoordsFull

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- The reverse map at the level point and a general level time `τ`. -/
def revLt (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (τ : ℝ≥0 × NullMeasurableSpace Ω P → ℝ)
    (z : ℝ≥0 × NullMeasurableSpace Ω P) (u : ℂ) : ℂ :=
  revMap (Vr κ T B (ofCompl P z.2)) (τ z) u

/-- Difference-quotient version of `deriv (revMap V (τ z))`. -/
def derivLt (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (τ : ℝ≥0 × NullMeasurableSpace Ω P → ℝ)
    (p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ) : ℂ :=
  limUnder atTop fun n => (CharFun.hstep n)⁻¹ •
    (revLt κ T B P τ p.1 (p.2 + CharFun.hstep n) - revLt κ T B P τ p.1 p.2)

section Meas

variable {τ : ℝ≥0 × NullMeasurableSpace Ω P → ℝ}

omit [IsProbabilityMeasure P] in
theorem measurable_derivLt (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) : Measurable (derivLt κ T B P τ) := by
  have hR := measurable_revMap_level_time hS hBc hτm hτ0
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  exact ((hR.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub hR).const_smul
    ((CharFun.hstep n)⁻¹ : ℂ)

omit [IsProbabilityMeasure P] in
theorem derivLt_eq (hBc : ∀ ω, Continuous (B · ω)) (hτ0 : ∀ z, 0 ≤ τ z)
    (z : ℝ≥0 × NullMeasurableSpace Ω P) {u : ℂ} (hu : u ∈ H) :
    derivLt κ T B P τ (z, u) = deriv (revMap (Vr κ T B (ofCompl P z.2)) (τ z)) u := by
  have hd := hasDerivAt_revMap _ (continuous_Vr_e5 (κ := κ) (T := T)
    (hBc (ofCompl P z.2))) (hτ0 z) hu
  have ht := hd.tendsto_slope_zero
  have hs : Tendsto CharFun.hstep atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      mem_compl_singleton_iff.2 (Complex.ofReal_ne_zero.2 (by positivity))⟩
    have := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Complex.ofReal_zero] at this
    exact this
  rw [hd.deriv]
  exact (ht.comp hs).limUnder_eq

/-- `q_τ` at the level point and a general level time is measurable. -/
theorem measurable_qt_level_time (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) :
    Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      qt κ (Vr κ T B (ofCompl P z.2)) (τ z) ϖ := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have := hϖ.prob
  have e : (fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      qt κ (Vr κ T B (ofCompl P z.2)) (τ z) ϖ) =
      fun z => Qc (Real.sqrt κ) * ∫ v, Real.log ‖derivLt κ T B P τ (z, v)‖ ∂ϖ := by
    funext z
    simp only [qt]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hϖ.ae_mem_H] with v hv
    rw [derivLt_eq hBc hτ0 z hv]
  rw [e]
  have hm : Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      Real.log ‖derivLt κ T B P τ p‖ :=
    Real.measurable_log.comp (measurable_derivLt hS hBc hτm hτ0).norm
  exact measurable_const.mul (hm.stronglyMeasurable.integral_prod_right').measurable

omit [IsProbabilityMeasure P] in
/-- `k_{ϖ_τ}` at the level point and a general level time is jointly measurable. -/
theorem measurable_kPot_level_time (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) :
    Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      PalmNorm.kPot (varpiT (Vr κ T B (ofCompl P p.1.2)) (τ p.1) ϖ) p.2 := by
  have e : (fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      PalmNorm.kPot (varpiT (Vr κ T B (ofCompl P p.1.2)) (τ p.1) ϖ) p.2) =
      fun p => ∫ w, neumannH p.2 (revLt κ T B P τ p.1 w) ∂ϖ := by
    funext p
    have hm := TwoPoint.measurable_revMap (continuous_Vr_e5 (κ := κ) (T := T)
      (hBc (ofCompl P p.1.2))) (hτ0 p.1)
    simp only [PalmNorm.kPot, varpiT]
    rw [integral_map hm.aemeasurable]
    · rfl
    · exact (measurable_neumannH.comp (measurable_const.prodMk measurable_id) :
        Measurable fun w => neumannH p.2 w).aestronglyMeasurable
  rw [e]
  have := hS.2.2.2.2.2.2.prob
  have hR := measurable_revMap_level_time hS hBc hτm hτ0
  have hF : Measurable fun q : ((ℝ≥0 × NullMeasurableSpace Ω P) × ℂ) × ℂ =>
      neumannH q.1.2 (revLt κ T B P τ q.1.1 q.2) :=
    measurable_neumannH.comp ((measurable_snd.comp measurable_fst).prodMk
      (hR.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

/-- The shift function at the level point and a general level time is jointly measurable. -/
theorem measurable_shiftFun_level_time (hS : E5.Setup κ T P B X ϖ)
    (hBc : ∀ ω, Continuous (B · ω)) (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) :
    Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (Vr κ T B (ofCompl P p.1.2)) (τ p.1) ϖ) 0 p.2 := by
  unfold PalmNorm.shiftFun
  refine ((UnzipInvariance.measurable_h0rev κ).comp measurable_snd).add
    (measurable_const.mul (Measurable.sub ?_ (measurable_kPot_level_time hS hBc hτm hτ0)))
  exact measurable_neumannH.comp (measurable_const.prodMk measurable_snd)

/-- The mean of the shift function against `ϖ_τ` is measurable in the level point. -/
theorem measurable_ofFun_shiftFun_level_time (hS : E5.Setup κ T P B X ϖ)
    (hBc : ∀ ω, Continuous (B · ω)) (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) :
    Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (Vr κ T B (ofCompl P z.2)) (τ z) ϖ) 0)
        (varpiT (Vr κ T B (ofCompl P z.2)) (τ z) ϖ) := by
  have hSF := measurable_shiftFun_level_time hS hBc hτm hτ0
  have hR := measurable_revMap_level_time hS hBc hτm hτ0
  have e : (fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (Vr κ T B (ofCompl P z.2)) (τ z) ϖ) 0)
        (varpiT (Vr κ T B (ofCompl P z.2)) (τ z) ϖ)) =
      fun z => ∫ w, PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (Vr κ T B (ofCompl P z.2)) (τ z) ϖ) 0 (revLt κ T B P τ z w) ∂ϖ := by
    funext z
    have hm := TwoPoint.measurable_revMap (continuous_Vr_e5 (κ := κ) (T := T)
      (hBc (ofCompl P z.2))) (hτ0 z)
    have hSm : Measurable fun u : ℂ => PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (Vr κ T B (ofCompl P z.2)) (τ z) ϖ) 0 u :=
      hSF.comp (measurable_const.prodMk measurable_id)
    exact integral_map hm.aemeasurable hSm.aestronglyMeasurable
  rw [e]
  have := hS.2.2.2.2.2.2.prob
  have hF : Measurable fun q : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (Vr κ T B (ofCompl P q.1.2)) (τ q.1) ϖ) 0 (revLt κ T B P τ q.1 q.2) :=
    hSF.comp (measurable_fst.prodMk hR)
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

/-- **The driver part of the collision correction is measurable in the level point**, at every
point `z` and every measurable nonnegative level time. -/
theorem measurable_locCorrDrv_level_time (hS : E5.Setup κ T P B X ϖ)
    (hBc : ∀ ω, Continuous (B · ω)) (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) (z : ℂ) :
    Measurable fun p : ℝ≥0 × NullMeasurableSpace Ω P =>
      locCorrDrv κ (Vr κ T B (ofCompl P p.2)) (τ p) ϖ z := by
  unfold locCorrDrv
  exact ((measurable_const.mul ((measurable_kPot_level_time hS hBc hτm hτ0).comp
    (measurable_id.prodMk measurable_const))).sub
    (measurable_ofFun_shiftFun_level_time hS hBc hτm hτ0)).sub
    (measurable_qt_level_time hS hBc hτm hτ0)

/-- **`hdrv` on the level space** (`Ξ =` the level point), at a general level time. -/
theorem measurable_locCorrDrv_lvl_time {Ω' : Type} [MeasurableSpace Ω']
    (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) (hτm : Measurable τ)
    (hτ0 : ∀ z, 0 ≤ τ z) (z : ℂ) :
    Measurable[MeasurableSpace.comap (lvlXi : lvl Ω P Ω' → _) inferInstance]
      fun z' : lvl Ω P Ω' => locCorrDrv κ (lvlDrv κ T B P z'.1) (τ z'.1) ϖ z := by
  have hxi : Measurable[MeasurableSpace.comap
      (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P) inferInstance]
      (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P) :=
    measurable_iff_comap_le.2 le_rfl
  exact (measurable_locCorrDrv_level_time hS hBc hτm hτ0 z).comp hxi

end Meas

end E5
end QuantumZipper
