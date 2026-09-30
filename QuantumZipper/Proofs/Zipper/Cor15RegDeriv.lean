import QuantumZipper.Proofs.Zipper.Cor15RezipRegMeas
import QuantumZipper.Proofs.Zipper.Cor15RegMeas

/-!
# COR15-HREG (2): a jointly measurable version of the zipped-up pairings

For a driver family `Vp : α → ℝ → ℝ` (continuous, `Vp a 0 = 0`, measurable in `a` pointwise):

* `DInv Vp t`: a jointly measurable version of `deriv (revMapInv (Vp a) t)`, by difference
  quotients (as `CharFun.Dm` for `revMap`); it equals the derivative on the alive set
  `H \ fwdHull (trev (Vp a) t) t`, where `revMapInv = fwdMap ∘ trev` (`revMapInv_eq_fwdMap_trev`)
  is holomorphic (`FwdHolo.hasDerivAt_fwdMap`).
* `CInv`: the candidate `evalReg (fromC c) (μ.map (revMapInv V t)) + Q ∫ log‖DInv‖ dμ`, jointly
  measurable in `(c, a)`, and equal to `coordChange x (revMapInv (Vp a) t) Q μ` for
  `c = coordsFull x` whenever `μ ≪ Leb`, `μ Hᶜ = 0` and the forward hull of `trev (Vp a) t` is
  Lebesgue-null — one condition for all test functions at once.

Own elementary arguments.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun CoordsFull

variable {α : Type*} [MeasurableSpace α] {Vp : α → ℝ → ℝ} {t : ℝ}

/-- A jointly measurable version of `deriv (revMapInv (Vp a) t)`. -/
def DInv (Vp : α → ℝ → ℝ) (t : ℝ) (p : ℂ × α) : ℂ :=
  limUnder atTop fun n =>
    (hstep n)⁻¹ • (revMapInv (Vp p.2) t (p.1 + hstep n) - revMapInv (Vp p.2) t p.1)

theorem measurable_DInv (hVc : ∀ a, Continuous (Vp a)) (hV0 : ∀ a, Vp a 0 = 0)
    (hVm : ∀ s, Measurable fun a => Vp a s) (ht : 0 < t) : Measurable (DInv Vp t) := by
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  have hm := measurable_revMapInv_param hVc hV0 hVm ht
  exact ((hm.comp ((measurable_fst.add_const _).prodMk measurable_snd)).sub hm).const_smul
    ((hstep n)⁻¹ : ℂ)

theorem hasDerivAt_revMapInv {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) (ht : 0 < t)
    {w : ℂ} (hw : w ∈ H \ fwdHull (ArcDriver.trev V t) t) :
    HasDerivAt (revMapInv V t) (Complex.exp (logDerivFwd (ArcDriver.trev V t) t w)) w := by
  have hA := ArcDriver.continuous_trev hV t
  refine (FwdHolo.hasDerivAt_fwdMap hA ht.le hw).congr_of_eventuallyEq ?_
  filter_upwards [(FwdHolo.isOpen_compl_fwdHull hA ht.le).mem_nhds hw] with u hu
  rw [revMapInv_eq_fwdMap_trev hV hV0 ht]
  exact ite_eq_left_of_eq_true _ _ (eq_true hu)

omit [MeasurableSpace α] in
theorem DInv_eq (hVc : ∀ a, Continuous (Vp a)) (hV0 : ∀ a, Vp a 0 = 0) (ht : 0 < t) (a : α)
    {w : ℂ} (hw : w ∈ H \ fwdHull (ArcDriver.trev (Vp a) t) t) :
    DInv Vp t (w, a) = deriv (revMapInv (Vp a) t) w := by
  have hd := hasDerivAt_revMapInv (hVc a) (hV0 a) ht hw
  have hs : Tendsto hstep atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      mem_compl_singleton_iff.2 (Complex.ofReal_ne_zero.2 (by positivity))⟩
    have := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Complex.ofReal_zero] at this
    exact this
  rw [hd.deriv]
  exact (hd.tendsto_slope_zero.comp hs).limUnder_eq

/-- The candidate zipped-up coordinate. -/
def CInv (Vp : α → ℝ → ℝ) (t Q : ℝ) (μ : Measure ℂ) (p : (ℕ → ℝ) × α) : ℝ :=
  evalReg (E1.fromC p.1) (μ.map (revMapInv (Vp p.2) t)) +
    Q * ∫ z, Real.log ‖DInv Vp t (z, p.2)‖ ∂μ

theorem measurable_revMapInv_slice (hR : Measurable fun p : ℂ × α => revMapInv (Vp p.2) t p.1)
    (b : α) : Measurable (revMapInv (Vp b) t) := by
  have h : Measurable fun z : ℂ => ((z, b) : ℂ × α) := by fun_prop
  exact hR.comp h

theorem evalReg_map_revMapInv_eq (hR : Measurable fun p : ℂ × α => revMapInv (Vp p.2) t p.1)
    (μ : Measure ℂ) (y : FieldSample) (b : α) :
    evalReg y (μ.map (revMapInv (Vp b) t)) =
      limUnder atTop fun k => ∫ z, avgReg y k (revMapInv (Vp b) t z) ∂μ := by
  have hA : ∀ k : ℕ, Measurable fun w => avgReg y k w := fun k => by
    have h : Measurable fun w : ℂ => ((y, w) : FieldSample × ℂ) := by fun_prop
    exact (measurable_avgReg k).comp h
  unfold evalReg
  congr 1
  funext k
  exact integral_map (measurable_revMapInv_slice hR b).aemeasurable (hA k).aestronglyMeasurable

theorem measurable_evalReg_revMapInv (hVc : ∀ a, Continuous (Vp a)) (hV0 : ∀ a, Vp a 0 = 0)
    (hVm : ∀ s, Measurable fun a => Vp a s) (ht : 0 < t) (μ : Measure ℂ) [SFinite μ] :
    Measurable fun p : FieldSample × α => evalReg p.1 (μ.map (revMapInv (Vp p.2) t)) := by
  have hR := measurable_revMapInv_param hVc hV0 hVm ht
  simp_rw [evalReg_map_revMapInv_eq hR]
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  have hm : Measurable fun q : (FieldSample × α) × ℂ =>
      avgReg q.1.1 k (revMapInv (Vp q.1.2) t q.2) := by
    have h : Measurable fun q : (FieldSample × α) × ℂ =>
        ((q.1.1, revMapInv (Vp q.1.2) t q.2) : FieldSample × ℂ) :=
      (measurable_fst.comp measurable_fst).prodMk
        (hR.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    exact (measurable_avgReg k).comp h
  exact hm.stronglyMeasurable.integral_prod_right'

theorem measurable_CInv (hVc : ∀ a, Continuous (Vp a)) (hV0 : ∀ a, Vp a 0 = 0)
    (hVm : ∀ s, Measurable fun a => Vp a s) (ht : 0 < t) (Q : ℝ) (μ : Measure ℂ) [SFinite μ] :
    Measurable (CInv Vp t Q μ) := by
  have h1 : Measurable fun p : (ℕ → ℝ) × α =>
      evalReg (E1.fromC p.1) (μ.map (revMapInv (Vp p.2) t)) :=
    (measurable_evalReg_revMapInv hVc hV0 hVm ht μ).comp
      (f := fun p : (ℕ → ℝ) × α => ((E1.fromC p.1, p.2) : FieldSample × α))
      ((measurable_fromC.comp measurable_fst).prodMk measurable_snd)
  have h2 : Measurable fun p : (ℕ → ℝ) × α => ∫ z, Real.log ‖DInv Vp t (z, p.2)‖ ∂μ := by
    have hm : Measurable fun q : ((ℕ → ℝ) × α) × ℂ => Real.log ‖DInv Vp t (q.2, q.1.2)‖ :=
      Real.measurable_log.comp ((measurable_DInv hVc hV0 hVm ht).comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).norm
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  exact h1.add (h2.const_mul Q)

omit [MeasurableSpace α] in
/-- On a Lebesgue-null hull, the zipped-up coordinate is the candidate. -/
theorem coordChange_revMapInv_eq_CInv (hVc : ∀ a, Continuous (Vp a)) (hV0 : ∀ a, Vp a 0 = 0)
    (ht : 0 < t) (Q : ℝ) {μ : Measure ℂ} (hμ : μ ≪ volume) (hμH : μ Hᶜ = 0) (x : FieldSample)
    (a : α) (hnull : volume (fwdHull (ArcDriver.trev (Vp a) t) t) = 0) :
    coordChange x (revMapInv (Vp a) t) Q μ = CInv Vp t Q μ (coordsFull x, a) := by
  rw [coordChange_congr_regEq (regEq_fromC_coordsFull x)]
  unfold coordChange CInv
  congr 2
  refine integral_congr_ae ?_
  have h1 : ∀ᵐ z ∂μ, z ∈ H := ae_iff.2 hμH
  have h2 : ∀ᵐ z ∂μ, z ∉ fwdHull (ArcDriver.trev (Vp a) t) t :=
    hμ (ae_iff.2 (by simpa using hnull) : ∀ᵐ z ∂volume, z ∉ fwdHull (ArcDriver.trev (Vp a) t) t)
  filter_upwards [h1, h2] with z hz1 hz2
  rw [DInv_eq hVc hV0 ht a ⟨hz1, hz2⟩]

omit [MeasurableSpace α] in
theorem pairRaw_revMapInv_eq_CInv (hVc : ∀ a, Continuous (Vp a)) (hV0 : ∀ a, Vp a 0 = 0)
    (ht : 0 < t) (Q : ℝ) (ρ : TestFun H) (x : FieldSample)
    (a : α) (hnull : volume (fwdHull (ArcDriver.trev (Vp a) t) t) = 0) :
    pairRaw (coordChange x (revMapInv (Vp a) t) Q) ρ.1 =
      CInv Vp t Q (tdens ρ.1) (coordsFull x, a) -
        CInv Vp t Q (tdens fun z => -ρ.1 z) (coordsFull x, a) := by
  obtain ⟨h1, h2⟩ := UnzipInvariance.tdens_compl_H ρ
  have e1 := coordChange_revMapInv_eq_CInv hVc hV0 ht Q (μ := tdens ρ.1)
    (withDensity_absolutelyContinuous _ _) h1 x a hnull
  have e2 := coordChange_revMapInv_eq_CInv hVc hV0 ht Q (μ := tdens fun z => -ρ.1 z)
    (withDensity_absolutelyContinuous _ _) h2 x a hnull
  unfold pairRaw
  exact congrArg₂ (· - ·) e1 e2

end Cor15Group
end QuantumZipper
