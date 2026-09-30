import QuantumZipper.Proofs.Zipper.Cor15ZipCoordPushA
import QuantumZipper.Proofs.Zipper.Cor15ZipCoordMain
import QuantumZipper.Proofs.Zipper.Cor15RezipFin2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-ZIPCOORD (4): the convergence form of input (R), `Cor15ZipPushGoodStmt`, proved

Sheffield, arXiv:1012.4797, Corollary 1.5. The proof of `cor15RezipRegStmt`
(`Cor15RezipFin2.lean`: a.s. goodness of the reversed driver `ae_rezip_good`, Fubini over the
independent pair (path, field) `CharFunRhs.ae_indep_ae`) with the jointly measurable event
`finL = finR` replaced by the jointly measurable `CCGoodAt` event, and the fixed-driver theorem
replaced by its convergence form `zc_ae_ccGood_pushed_fc` (`Cor15ZipCoordPushA.lean`; analytic
input Duplantier–Sheffield 2011, Prop. 3.1 via RC3). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun B2

/-- **`CCGoodAt` is a measurable condition** on a parameter, given joint measurability of the
integrands (abstract form of `measurableSet_ccGoodAt`). -/
theorem zc_measurableSet_ccGoodAt_gen {α : Type*} [MeasurableSpace α] {Y : α → FieldSample}
    {ψ : α → ℂ → ℂ} (hF : ∀ k : ℕ, Measurable fun q : α × ℂ => avgReg (Y q.1) k (ψ q.1 q.2))
    (hψ : ∀ b, Measurable (ψ b)) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    MeasurableSet {b | CCGoodAt (Y b) (ψ b) μ} := by
  set F : ℕ → α × ℂ → ℝ := fun k q => avgReg (Y q.1) k (ψ q.1 q.2) with hFd
  have hsl : ∀ b k, Measurable fun w => avgReg (Y b) k w := fun b k =>
    (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
  have hI : ∀ b k, Integrable (fun w => avgReg (Y b) k w) (μ.map (ψ b)) ↔
      Integrable (fun z => F k (b, z)) μ := fun b k =>
    integrable_map_measure (hsl b k).aestronglyMeasurable (hψ b).aemeasurable
  have hE : ∀ b k, ∫ w, avgReg (Y b) k w ∂(μ.map (ψ b)) = ∫ z, F k (b, z) ∂μ := fun b k =>
    integral_map (hψ b).aemeasurable (hsl b k).aestronglyMeasurable
  have e : {b | CCGoodAt (Y b) (ψ b) μ} =
      (⋂ k, {b | Integrable (fun z => F k (b, z)) μ}) ∩
        {b | ∃ L, Tendsto (fun k => ∫ z, F k (b, z) ∂μ) atTop (𝓝 L)} := by
    ext b
    simp only [CCGoodAt, mem_ofPred_eq, mem_inter_iff, mem_iInter, hI, hE]
  rw [e]
  refine (MeasurableSet.iInter fun k => ?_).inter ?_
  · have hj : {b | Integrable (fun z => F k (b, z)) μ} = {b | ∫⁻ z, ‖F k (b, z)‖ₑ ∂μ < ∞} := by
      ext b
      simp only [mem_ofPred_eq]
      exact ⟨fun h => h.2,
        fun h => ⟨((hF k).comp measurable_prodMk_left).aestronglyMeasurable, h⟩⟩
    rw [hj]
    exact measurableSet_lt (hF k).enorm.lintegral_prod_right' measurable_const
  · exact StronglyMeasurable.measurableSet_exists_tendsto fun k =>
      (hF k).stronglyMeasurable.integral_prod_right'

theorem measurable_zcFin (κ : ℝ) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Measurable fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ =>
      avgReg (coordChange (ofFun (h0rev κ) + q.1.2)
        (revMap (Wof κ t ht.le (finRevPath ht.le q.1.1)) t) (Qc (Real.sqrt κ))) k
        (revMapInv (Wof κ t ht.le (finRevPath ht.le q.1.1)) t q.2) := by
  have h1 : Measurable fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ =>
      avgReg (coordChange (ofFun (h0rev κ) + q.1.2) (revMap (Wof κ t ht.le q.1.1) t)
        (Qc (Real.sqrt κ))) k q.2 :=
    CoordReg.measurable_avgReg_coordChange κ ht.le (h0rev κ) (Qc (Real.sqrt κ)) k
  have h2 : Measurable fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ =>
      (((finRevPath ht.le q.1.1, q.1.2),
        revMapInv (Wof κ t ht.le (finRevPath ht.le q.1.1)) t q.2) :
        (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ) := by
    refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
    · exact (measurable_finRevPath ht.le).comp
        (f := fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ => q.1.1)
        (measurable_fst.comp measurable_fst)
    · exact measurable_snd.comp measurable_fst
    · exact (measurable_finInv κ ht).comp
        (f := fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ => (q.1.1, q.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def] using h1.comp h2

/-- The `CCGoodAt` event of the re-zip is jointly measurable in (path, field). -/
theorem zc_measurableSet_ccGood_fin (κ : ℝ) {t : ℝ} (ht : 0 < t) (σ : Measure ℂ)
    [IsFiniteMeasure σ] :
    MeasurableSet {p : C(Icc (0 : ℝ) t, ℝ) × FieldSample | CCGoodAt
      (coordChange (ofFun (h0rev κ) + p.2) (revMap (Wof κ t ht.le (finRevPath ht.le p.1)) t)
        (Qc (Real.sqrt κ))) (revMapInv (Wof κ t ht.le (finRevPath ht.le p.1)) t) σ} :=
  zc_measurableSet_ccGoodAt_gen
    (Y := fun p : C(Icc (0 : ℝ) t, ℝ) × FieldSample => coordChange (ofFun (h0rev κ) + p.2)
      (revMap (Wof κ t ht.le (finRevPath ht.le p.1)) t) (Qc (Real.sqrt κ)))
    (ψ := fun p => revMapInv (Wof κ t ht.le (finRevPath ht.le p.1)) t)
    (measurable_zcFin κ ht) (fun p =>
      measurable_revMapInv (continuous_Wof κ t ht.le (finRevPath ht.le p.1)) ht.le) σ

theorem zc_ae_ccGood_unzip (κ : ℝ) (hκ : 0 < κ) (hκ4 : κ < 4) (t : ℝ) (ht : 0 < t)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (i : ℕ) :
    ∀ᵐ ω ∂P, CCGoodAt (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t)
      (revMapInv (vrev (drive κ B ω) t) t)
      (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) := by
  set σ := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 with hσ
  have hr := UnzipFull.fullIndex_radius_pos i
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := CharFun.exists_good_version hB
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  set g := CharFun.pathC t B₁ hB₁c with hgdef
  have hg : Measurable g := measurable_pathC t hB₁m hB₁c
  have hindg : IndepFun g X P := indepFun_pathC t hind₁ hB₁c
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  obtain ⟨β, hβ, hgood⟩ := ae_rezip_good hB hind hκ hκ4 ht (CoordsFull.fullIndex i).1 hr
  set E : Set (C(Icc (0 : ℝ) t, ℝ) × FieldSample) := {p | CCGoodAt
      (coordChange (ofFun (h0rev κ) + p.2) (revMap (Wof κ t ht.le (finRevPath ht.le p.1)) t)
        (Qc (Real.sqrt κ))) (revMapInv (Wof κ t ht.le (finRevPath ht.le p.1)) t) σ} with hEdef
  have hE : MeasurableSet E := zc_measurableSet_ccGood_fin κ ht σ
  have hrev : ∀ᵐ ω ∂P,
      revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t = revMap (vrev (drive κ B ω) t) t ∧
      EqOn (Wof κ t ht.le (finRevPath ht.le (g ω))) (vrev (drive κ B ω) t) (Icc 0 t) := by
    filter_upwards [hB₁eq] with ω hb
    have heq := finV_pathC_eqOn (κ := κ) ht hB₁c hb
    exact ⟨funext fun z => ReverseFlow.revMap_congr_drive z heq, heq⟩
  have hfib : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, (g ω, X ω') ∈ E := by
    filter_upwards [hgood, hrev] with ω hω hF
    obtain ⟨-, -, hS, hK, ⟨c, hc0, hc⟩, M, hM, C, hC, hHol⟩ := hω
    obtain ⟨hF, hVeq⟩ := hF
    have hK' : σ (H \ revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t '' H) = 0 := by
      rw [hF]; exact hK
    have hσD := ae_mem_revMap_image_fc hr hK'
    have hM' : ∀ r ∈ Icc (0 : ℝ) t, |Wof κ t ht.le (finRevPath ht.le (g ω)) r| ≤ M :=
      fun r hr' => by rw [hVeq hr']; exact hM r hr'
    filter_upwards [zc_ae_ccGood_pushed_fc hX κ (Qc (Real.sqrt κ))
      (continuous_finV κ ht (g ω)) (finV_zero κ ht (g ω)) ht hr hK' (by rw [hF]; exact hS) hM'
      hC hβ (by rw [hF]; exact hHol) hc0 hc] with ω' h
    exact h
  have hmain := CharFunRhs.ae_indep_ae hg hXm hindg hE hfib
  filter_upwards [hmain, hgood, hrev, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hgd hF hc h0
  obtain ⟨hVc, -, -, hK, -⟩ := hgd
  obtain ⟨hF, -⟩ := hF
  have hK' : σ (H \ revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t '' H) = 0 := by
    rw [hF]; exact hK
  have hσD := ae_mem_revMap_image_fc hr hK'
  have h1 : CCGoodAt (coordChange (ofFun (h0rev κ) + X ω)
      (revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t) (Qc (Real.sqrt κ)))
      (revMapInv (Wof κ t ht.le (finRevPath ht.le (g ω))) t) σ := hω
  have hinv : revMapInv (Wof κ t ht.le (finRevPath ht.le (g ω))) t =
      revMapInv (vrev (drive κ B ω) t) t :=
    revMapInv_congr_H fun z _ => congrFun hF z
  rw [hF, hinv] at h1
  have hFF : EqOn (fwdMapInv (drive κ B ω) t) (revMap (vrev (drive κ B ω) t) t) H :=
    fun z hz => fwdMapInv_eq_revMap_vrev (drive_continuous hc) (drive_zero h0) ht.le hz
  exact ccGoodAt_of_avgReg_shift (c := 0)
    (fun j w => by
      show avgReg (coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) t)
        (Qc (Real.sqrt κ))) j w = _
      rw [avgReg_coordChange_congr_H _ hFF, add_zero]) h1

/-- **`Cor15ZipPushGoodStmt` holds** for every genuine setup. -/
theorem cor15ZipPushGood {κ a : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hS : IsGrpSetup P B X) (ha : 0 < a) : Cor15ZipPushGoodStmt κ a P B X :=
  fun i => zc_ae_ccGood_unzip κ hκ hκ4 a ha P B X hS.1 hS.2.1 hS.2.2 i

/-- **COR15-ZIPCOORD: `Cor15ZipCoordReadStmt`** for every genuine setup, from Theorem 1.3. -/
theorem cor15ZipCoordRead' (h13 : theorem1_3) {κ a : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hS : IsGrpSetup P B X) (ha : 0 < a) :
    Cor15ZipCoordReadStmt κ a P B X :=
  cor15ZipCoordRead h13 hκ hκ4 hS ha (cor15ZipPushGood hκ hκ4 hS ha)

end Cor15Group
end QuantumZipper
