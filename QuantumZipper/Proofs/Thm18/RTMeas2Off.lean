import QuantumZipper.Proofs.Thm18.RTMeas2Glue
import QuantumZipper.Proofs.Thm18.R18RTMask

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS2, part 2: boundary approximations off the curve, and exactness of the gated readers

* `eventually_restrict_bdryApprox_eq`, `isVagueLimitOnR_congr_off`: fields equal (regularized) off
  a closed `K` have eventually equal boundary approximations on every compact set of reals off `K`,
  hence the same local vague limits on sets of reals off `K` (the argument of
  `R18.qBoundaryMeasureOn_congr_off`, R18RTMaskOff.lean, made local).
* `bdryGate_iff`: on good drivers the gate is the window certificate of the unzipped pieces.
* `lenRdR`: the jointly Borel length reader at real times; on the gate it is the open-arc length
  of the unzipped pieces (`lenRdR_eq`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm18Asm.G4Core CoordsFull

theorem eventually_restrict_bdryApprox_eq {K : Set ℂ} (hK : IsClosed K) {x y : FieldSample}
    (h : RegEqOff K x y) (γ : ℝ) {C : Set ℝ} (hC : IsCompact C) (hCK : ∀ t ∈ C, (t : ℂ) ∉ K) :
    ∀ᶠ k in atTop, (bdryApprox γ x k).restrict C = (bdryApprox γ y k).restrict C := by
  have hS : IsCompact ((fun t : ℝ => (t : ℂ)) '' C) := hC.image Complex.continuous_ofReal
  have hdis : Disjoint ((fun t : ℝ => (t : ℂ)) '' C) K := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hCK t ht
  obtain ⟨r, hr0, hr⟩ := Metric.exists_pos_forall_lt_edist hS hK hdis
  have hd : (0 : ℝ) < r := hr0
  obtain ⟨N, hN⟩ := ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
    (gt_mem_nhds (half_pos hd))).exists_forall_of_atTop
  filter_upwards [Filter.eventually_ge_atTop N] with k hk
  have hfar : ∀ t ∈ C, avgReg x k (t : ℂ) = avgReg y k (t : ℂ) := by
    intro t ht
    refine h k _ (circleOff_of_far (by simp) (fun p hp => ?_) (hN k hk) hd)
    have := hr _ ⟨t, ht, rfl⟩ p hp
    rw [edist_dist] at this
    exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 (by simpa using this))
  have hms : MeasurableSet C := hC.isClosed.measurableSet
  simp only [bdryApprox]
  rw [restrict_withDensity hms, restrict_withDensity hms]
  refine withDensity_congr_ae ((ae_restrict_iff' hms).2 (ae_of_all _ fun t ht => ?_))
  simp only [hfar t ht]

theorem isVagueLimitOnR_congr_off {K : Set ℂ} (hK : IsClosed K) {x y : FieldSample}
    (h : RegEqOff K x y) (γ : ℝ) {I : Set ℝ} (hI : ∀ t ∈ I, (t : ℂ) ∉ K) {ν : Measure ℝ}
    (hx : IsVagueLimitOnR I (bdryApprox γ x) ν) : IsVagueLimitOnR I (bdryApprox γ y) ν := by
  refine ⟨hx.1, hx.2.1, fun f hf hfc hfI => ?_⟩
  refine (tendsto_congr' ?_).1 (hx.2.2 f hf hfc hfI)
  filter_upwards [eventually_restrict_bdryApprox_eq hK h γ hfc (fun t ht => hI t (hfI ht))]
    with k hk
  have hz : ∀ t, t ∉ tsupport f → f t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport ht
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := bdryApprox γ x k) hz,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := bdryApprox γ y k) hz, hk]

/-! ## The gate and the length reader at real times -/

theorem bdryApprox_zfld (γ : ℝ) {d : E6.FullData} (hc : Continuous d.2) (hp : F1.PathGoodAll d.2)
    {t : ℝ} (ht : 0 ≤ t) :
    bdryApprox γ (zfld γ (πd d) t) = bdryApprox γ (unzippedField γ (configOfData γ d).toPair t) :=
  NuMeas.bdryApprox_congr_coordsFull γ (coordsFull_zfld γ hc hp ht)

theorem sideR_πd {d : E6.FullData} (hc : Continuous d.2) (hp : F1.PathGoodAll d.2) {t : ℝ}
    (ht : 0 ≤ t) : sideR (pcode (πd d)).2 t = sideImages (drvOfData d) t := by
  rw [drvOfData_eq_readDrv hc, pcode_πd]
  exact (sideImages_eq_sideR hp ht).symm

theorem bdryGate_iff (γ : ℝ) {d : E6.FullData} (hc : Continuous d.2) (hp : F1.PathGoodAll d.2)
    {t : ℝ} (ht : 0 ≤ t) :
    bdryGate γ (πd d, t) ↔ WinCert (bdryApprox γ (unzippedField γ (configOfData γ d).toPair t))
      (sideImages (drvOfData d) t).1 0 := by
  unfold bdryGate
  rw [bdryApprox_zfld γ hc hp ht, sideR_πd hc hp ht]

/-- The length reader at real times. -/
def lenRdR (γ : ℝ) (x : PX × ℝ) : ℝ≥0∞ :=
  LocLen.arcRd γ (zfld γ x.1 x.2) (sideR (pcode x.1).2 x.2).1 0

theorem measurable_lenRdR (γ : ℝ) : Measurable (lenRdR γ) :=
  LocLen.measurable_arcRd_comp γ (measurable_zfld γ)
    (measurable_sideR.comp ((measurable_snd.comp (measurable_pcode.comp measurable_fst)).prodMk
      measurable_snd)).fst measurable_const

theorem lenRdR_eq (γ : ℝ) {d : E6.FullData} (hc : Continuous d.2) (hp : F1.PathGoodAll d.2)
    {t : ℝ} (ht : 0 ≤ t) (hg : bdryGate γ (πd d, t)) :
    lenRdR γ (πd d, t) = (unzipLengthsOpen γ (configOfData γ d).toPair t).1 := by
  have hb := bdryApprox_zfld γ hc hp ht
  have hs := sideR_πd hc hp ht
  unfold bdryGate at hg
  obtain ⟨ν, hν⟩ := exists_lim_of_winCert hg
  unfold lenRdR
  rw [LocLen.arcRd_eq_arcLen isOpen_Ioo hν subset_rfl, LocLen.arcLen_congr_bdry hb, hs]
  rfl

theorem exists_lim_of_bdryGate (γ : ℝ) {d : E6.FullData} (hc : Continuous d.2)
    (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t) (hg : bdryGate γ (πd d, t)) :
    ∃ ν : Measure ℝ, IsVagueLimitOnR (Ioo (sideImages (drvOfData d) t).1 0)
      (bdryApprox γ (unzippedField γ (configOfData γ d).toPair t)) ν :=
  exists_lim_of_winCert ((bdryGate_iff γ hc hp ht).1 hg)

end RTMeas
end R18
end QuantumZipper
