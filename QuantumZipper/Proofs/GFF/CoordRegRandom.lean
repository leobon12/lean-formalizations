import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.Loewner.TwoPointEnergy

/-!
# RC3 (folded circles) for a random unzip map independent of the field

The driver is `Wof κ T hT (g ω)` for a random path `g ω ∈ C([0,T])` independent of `X` (the
setting of `UnzipFull.ae_split_fc_random`). Both sides of the RC3 identity at a fixed folded
circle are jointly measurable in `(path, field)` (`measurable_evalReg_coordChange_fc`,
`measurable_rhs_fc`), and the fixed-driver identity holds for every path, so independence
transfers it (`CharFun.ae_indep`, the pattern of `FrostmanReg.ae_tendsto_evalReg_frostman_random`).
The energy modulus is assumed for every continuous driver, which is the form in which
`TwoPoint.abs_kernelCov2_revMap_foldedCircle_le` is stated.

Source: none — **own elementary proof** (the independence transfer `CharFun.ae_indep`, following
the pattern of `FrostmanReg.ae_tendsto_evalReg_frostman_random`; the fixed-driver input is
`TwoPoint.abs_kernelCov2_revMap_foldedCircle_le`, AUDIT3 §1.3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace CoordReg

open CharFun

variable (κ : ℝ) {T : ℝ} (hT : 0 ≤ T)

/-- `evalReg` at a pushed measure, jointly measurable in `(path, field)` (the proof of
`UnzipFull.measurable_evalReg_push_gen`, copied to avoid depending on a module under
development). -/
theorem measurable_evalReg_push' (μ : Measure ℂ) [SFinite μ] :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      evalReg p.2 (μ.map (revMap (Wof κ T hT p.1) T)) := by
  have heq : ∀ p : C(Icc (0 : ℝ) T, ℝ) × FieldSample,
      evalReg p.2 (μ.map (revMap (Wof κ T hT p.1) T)) =
        limUnder atTop fun k => ∫ z, avgReg p.2 k (Fm κ T hT (p.1, z)) ∂μ := by
    intro p
    unfold evalReg
    congr 1
    funext k
    rw [integral_map (measurable_revMap_Wof κ T hT p.1).aemeasurable
      (show Measurable fun w => avgReg p.2 k w from
        (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
    rfl
  rw [show (fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      evalReg p.2 (μ.map (revMap (Wof κ T hT p.1) T))) = _ from funext heq]
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  have hm : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      avgReg q.1.2 k (Fm κ T hT (q.1.1, q.2)) :=
    (measurable_avgReg k).comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_Fm κ T hT).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'

/-- The `Q`-term of the unzipped field at a folded circle is measurable in the path. -/
theorem measurable_integral_log_deriv_fc (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Measurable fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ u, Real.log ‖deriv (revMap (Wof κ T hT f) T) u‖ ∂foldedCircle c r := by
  have heq : ∀ f : C(Icc (0 : ℝ) T, ℝ),
      ∫ u, Real.log ‖deriv (revMap (Wof κ T hT f) T) u‖ ∂foldedCircle c r =
        ∫ u, Real.log ‖Dm κ T hT (f, u)‖ ∂foldedCircle c r := fun f =>
    integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H c hr).mono fun u hu => by
      show Real.log ‖deriv (revMap (Wof κ T hT f) T) u‖ = Real.log ‖Dm κ T hT (f, u)‖
      rw [Dm_eq κ T hT f hu])
  rw [show (fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ u, Real.log ‖deriv (revMap (Wof κ T hT f) T) u‖ ∂foldedCircle c r) = _ from funext heq]
  exact ((Real.measurable_log.comp (measurable_Dm κ T hT).norm).stronglyMeasurable.integral_prod_right').measurable

/-- Raw values of the unzipped field at a folded circle, jointly in `(path, field)`. -/
theorem measurable_coordChange_fc (G : ℂ → ℝ) (Q : ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      coordChange (ofFun G + p.2) (revMap (Wof κ T hT p.1) T) Q (foldedCircle c r) := by
  have hpair : Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      ((p.1, ofFun G + p.2) : C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
    measurable_fst.prodMk ((measurable_const_add _).comp measurable_snd)
  have h1 := (measurable_evalReg_push' κ hT (foldedCircle c r)).comp hpair
  exact h1.add (((measurable_integral_log_deriv_fc κ hT c hr).comp measurable_fst).const_mul Q)

/-- The regularized average of the unzipped field, jointly measurable in `((path, field), z)`. -/
theorem measurable_avgReg_coordChange (G : ℂ → ℝ) (Q : ℝ) (k : ℕ) :
    Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      avgReg (coordChange (ofFun G + q.1.2) (revMap (Wof κ T hT q.1.1) T) Q) k q.2 := by
  unfold avgReg
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  have hc : (Set.range (dyadicRoundC n)).Countable := by
    refine (Set.countable_range fun p : ℤ × ℤ => CircleCont.lpt n p.1 p.2).mono ?_
    rintro _ ⟨z, rfl⟩
    exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), (CircleCont.dyadicRoundC_eq_lpt n z).symm⟩
  have : Countable (Set.range (dyadicRoundC n)) := hc.to_subtype
  have hdm : Measurable (dyadicRoundC n) := by
    have hrw : dyadicRoundC n = fun z : ℂ =>
        (dyadicRound n z.re : ℂ) + (dyadicRound n z.im : ℂ) * Complex.I := by
      funext z; apply Complex.ext <;> simp [dyadicRoundC]
    have hr : Measurable (dyadicRound n) := by
      unfold dyadicRound
      exact ((measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).div_const ((2 : ℝ) ^ n)).comp
        (Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ n)))
    rw [hrw]
    exact (Complex.continuous_ofReal.measurable.comp (hr.comp Complex.measurable_re)).add
      ((Complex.continuous_ofReal.measurable.comp (hr.comp Complex.measurable_im)).mul_const _)
  intro S hS
  have key : (fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      coordChange (ofFun G + q.1.2) (revMap (Wof κ T hT q.1.1) T) Q
        (foldedCircle (dyadicRoundC n q.2) (radius k))) ⁻¹' S =
      ⋃ d : Set.range (dyadicRoundC n),
        {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
          coordChange (ofFun G + p.2) (revMap (Wof κ T hT p.1) T) Q
            (foldedCircle (d : ℂ) (radius k)) ∈ S} ×ˢ (dyadicRoundC n ⁻¹' {(d : ℂ)}) := by
    ext ⟨p, z⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    constructor
    · intro hmem
      exact ⟨⟨dyadicRoundC n z, Set.mem_range_self z⟩, hmem, rfl⟩
    · rintro ⟨d, hmem, hdz⟩
      rwa [hdz]
  rw [key]
  exact MeasurableSet.iUnion fun d => MeasurableSet.prod
    (measurable_coordChange_fc κ hT G Q (d : ℂ) (radius_pos k) hS)
    (hdm (measurableSet_singleton _))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## Unconditional forms: the energy modulus holds with `β = 1/12` -/

/-- **(E) holds.** The energy modulus of `revMap W T` with exponent `1/12`, for every continuous
driver and `T ≥ 0` (`TwoPoint.abs_kernelCov2_revMap_foldedCircle_le`). -/
theorem energyModulus_holds {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    EnergyModulus W T (1 / 12) := fun _ R hr₀ =>
  TwoPoint.abs_kernelCov2_revMap_foldedCircle_le hW hT (R := R) hr₀

theorem energyModulus_holds_timeRev {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    EnergyModulus (fun s => W (t - s) - W t) t (1 / 12) :=
  energyModulus_holds ((hW.comp (continuous_const.sub continuous_id)).sub continuous_const) ht

/-- **RC2** (unconditional). -/
theorem ae_isRegularSample_coordChange_revMap' {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ}
    (hT : 0 ≤ T) (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (a : ℝ)
    {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) :
    ∀ᵐ ω ∂P, IsRegularSample
      (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap W T) Q) :=
  ae_isRegularSample_coordChange_revMap hW hT hX (by norm_num) (energyModulus_holds hW hT) a hg₁ Q

/-- **RC2 for `h0rev κ`** (unconditional). -/
theorem ae_isRegularSample_coordChange_h0rev' {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ}
    (hT : 0 ≤ T) (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (κ' Q : ℝ) :
    ∀ᵐ ω ∂P, IsRegularSample (coordChange (ofFun (h0rev κ') + X ω) (revMap W T) Q) :=
  ae_isRegularSample_coordChange_h0rev hW hT hX (by norm_num) (energyModulus_holds hW hT) κ' Q

end CoordReg
end QuantumZipper
