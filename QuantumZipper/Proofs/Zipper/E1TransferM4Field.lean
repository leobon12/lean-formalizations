import QuantumZipper.Proofs.Zipper.E1TransferRep3
import QuantumZipper.Proofs.Zipper.E1TransferM4Cert
import QuantumZipper.Proofs.Zipper.E1TransferM4Drive
import QuantumZipper.Proofs.Zipper.E1TransferM4Live

/-!
# M4 (TR-MEAS): the zipped field of E1-TR as a measurable function of (coordinates, driver path)

`handoff/E1-TR.md` (M4b). For coordinates `c : ℕ → ℝ` and a continuous path `w` on `[0,t]`
(driver `Wof 1 t ht w`):

* `mC (c, w) = evalReg (fromC c) ϖ_t + q_t` (the normalizing constant `m`),
* `zC (c, w) = coordChange (fromC c) (revMap (Wof 1 t ht w) t) Q − mC (c, w)` (the field whose boundary
  measure is integrated in `trInt`), `zR = fromC (coordsFull zC)` (same circle values).

Results: `measurable_fromC`, `measurable_mC`, `measurable_coord_zC`, `measurable_zR`,
`measurable_coords_shift`, `bdryApprox_zR`; and the kernel lemma
`measurable_setLIntegral_of_measurable_measure` (a Giry-measurable family of measures, finite on
`s`, integrates a jointly measurable function measurably; finite truncations of the kernel).
Own bookkeeping (measurability plumbing); the reverse flow and its derivative are read through the
jointly measurable `CharFun.Fm`, `CharFun.Dm`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1
namespace M4

open B2 CharFun UnzipInvariance UnzipFull CoordsFull

theorem measurable_fromC : Measurable fromC := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ
  · obtain ⟨j, hj⟩ : ∃ j, ∀ c : ℕ → ℝ, fromC c μ = c j :=
      ⟨_, fun c => by unfold fromC; rw [dif_pos h]⟩
    simp_rw [hj]
    exact measurable_pi_apply j
  · have e : (fun c : ℕ → ℝ => fromC c μ) = fun _ => 0 := by
      funext c; unfold fromC; rw [dif_neg h]
    rw [e]; exact measurable_const

variable (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) (ϖ : Measure ℂ)

/-- The normalizing constant `m` as a function of (coordinates, path). -/
def mC (p : (ℕ → ℝ) × C(Icc (0 : ℝ) t, ℝ)) : ℝ :=
  evalReg (fromC p.1) (varpiT (Wof 1 t ht p.2) t ϖ) + qt κ (Wof 1 t ht p.2) t ϖ

/-- The field of `trInt` as a function of (coordinates, path). -/
def zC (p : (ℕ → ℝ) × C(Icc (0 : ℝ) t, ℝ)) : FieldSample :=
  addConst (coordChange (fromC p.1) (revMap (Wof 1 t ht p.2) t) (Qc (Real.sqrt κ))) (-(mC κ ht ϖ p))

/-- The same field rebuilt from its circle coordinates (a measurable function of `p`). -/
def zR (p : (ℕ → ℝ) × C(Icc (0 : ℝ) t, ℝ)) : FieldSample := fromC (coordsFull (zC κ ht ϖ p))

theorem measurable_logDeriv_int (μ : Measure ℂ) [SFinite μ] (hμ : ∀ᵐ z ∂μ, z ∈ H) :
    Measurable fun w : C(Icc (0 : ℝ) t, ℝ) =>
      ∫ z, Real.log ‖deriv (revMap (Wof 1 t ht w) t) z‖ ∂μ := by
  have e : ∀ w : C(Icc (0 : ℝ) t, ℝ), ∫ z, Real.log ‖deriv (revMap (Wof 1 t ht w) t) z‖ ∂μ =
      ∫ z, Real.log ‖Dm 1 t ht (w, z)‖ ∂μ := fun w =>
    integral_congr_ae (hμ.mono fun z hz => by simp only [Dm_eq 1 t ht w hz])
  simp_rw [e]
  exact (Real.measurable_log.comp (measurable_Dm 1 t ht).norm).stronglyMeasurable
    |>.integral_prod_right'.measurable

theorem measurable_swap_fromC :
    Measurable fun p : (ℕ → ℝ) × C(Icc (0 : ℝ) t, ℝ) => (p.2, fromC p.1) :=
  measurable_snd.prodMk (measurable_fromC.comp measurable_fst)

theorem measurable_evalReg_fromC (μ : Measure ℂ) [SFinite μ] :
    Measurable fun p : (ℕ → ℝ) × C(Icc (0 : ℝ) t, ℝ) =>
      evalReg (fromC p.1) (μ.map (revMap (Wof 1 t ht p.2) t)) := by
  have h := (measurable_evalReg_push_gen 1 t ht μ).comp (measurable_swap_fromC (t := t))
  exact h

theorem measurable_mC [SFinite ϖ] (hϖH : ∀ᵐ z ∂ϖ, z ∈ H) : Measurable (mC κ ht ϖ) := by
  unfold mC varpiT qt
  exact (measurable_evalReg_fromC ht ϖ).add
    (((measurable_logDeriv_int ht ϖ hϖH).comp measurable_snd).const_mul _)

theorem measurable_coord_zC [SFinite ϖ] (hϖH : ∀ᵐ z ∂ϖ, z ∈ H) (i : ℕ) :
    Measurable fun p => coordsFull (zC κ ht ϖ p) i := by
  have hr := fullIndex_radius_pos i
  have hH := TwoPoint.foldedCircle_ae_mem_H (fullIndex i).1 hr
  simp only [zC, coordsFull_addConst]
  simp only [coordsFull, coordChange]
  exact ((measurable_evalReg_fromC ht _).add
    (((measurable_logDeriv_int ht _ hH).comp measurable_snd).const_mul _)).add
    (measurable_mC κ ht ϖ hϖH).neg

theorem measurable_zR [SFinite ϖ] (hϖH : ∀ᵐ z ∂ϖ, z ∈ H) : Measurable (zR κ ht ϖ) :=
  measurable_fromC.comp (measurable_pi_iff.2 (measurable_coord_zC κ ht ϖ hϖH))

theorem measurable_coords_shift [SFinite ϖ] (hϖH : ∀ᵐ z ∂ϖ, z ∈ H) :
    Measurable fun p : (ℕ → ℝ) × C(Icc (0 : ℝ) t, ℝ) =>
      coordsFull (addConst (fromC p.1) (-(mC κ ht ϖ p))) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [coordsFull_addConst]
  exact ((measurable_pi_apply i).comp (measurable_coordsFull.comp
    (measurable_fromC.comp measurable_fst))).add (measurable_mC κ ht ϖ hϖH).neg

theorem bdryApprox_zR (γ : ℝ) (p : (ℕ → ℝ) × C(Icc (0 : ℝ) t, ℝ)) :
    bdryApprox γ (zR κ ht ϖ p) = bdryApprox γ (zC κ ht ϖ p) :=
  Factorization.bdryApprox_congr (avgReg_congr_full (coordsFull_fromC _)) γ

/-! ## Integrating against a measurable family of measures -/

theorem measurable_restrict_family {α : Type*} [MeasurableSpace α] {M : α → Measure ℝ}
    (hM : Measurable M) {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable fun a => (M a).restrict s := by
  refine Measure.measurable_of_measurable_coe _ fun u hu => ?_
  simp only [Measure.restrict_apply hu]
  exact (Measure.measurable_coe (hu.inter hs)).comp hM

open Classical in
/-- The truncated kernels `a ↦ 1{M a s ≤ K} (M a)|_s`. -/
def truncK {α : Type*} [MeasurableSpace α] {M : α → Measure ℝ} (hM : Measurable M)
    {s : Set ℝ} (hs : MeasurableSet s) (K : ℕ) : Kernel α ℝ where
  toFun a := if M a s ≤ K then (M a).restrict s else 0
  measurable' := Measurable.ite (measurableSet_le ((Measure.measurable_coe hs).comp hM)
    measurable_const) (measurable_restrict_family hM hs) measurable_const

instance {α : Type*} [MeasurableSpace α] {M : α → Measure ℝ} (hM : Measurable M)
    {s : Set ℝ} (hs : MeasurableSet s) (K : ℕ) : IsFiniteKernel (truncK hM hs K) := by
  refine ⟨⟨K, ENNReal.natCast_lt_top K, fun a => ?_⟩⟩
  simp only [truncK, Kernel.coe_mk]
  split_ifs with h
  · rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact h
  · simp

theorem measurable_setLIntegral_of_measurable_measure {α : Type*} [MeasurableSpace α]
    {M : α → Measure ℝ} (hM : Measurable M) {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : ∀ a, M a s < ⊤) {f : α × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun a => ∫⁻ x in s, f (a, x) ∂M a := by
  have e : ∀ a, ∫⁻ x in s, f (a, x) ∂M a = ⨆ K : ℕ, ∫⁻ x, f (a, x) ∂truncK hM hs K a := by
    intro a
    refine le_antisymm ?_ (iSup_le fun K => ?_)
    · obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt (hfin a).ne
      refine le_iSup_of_le K (le_of_eq ?_)
      simp only [truncK, Kernel.coe_mk, if_pos hK.le]
    · simp only [truncK, Kernel.coe_mk]
      split_ifs
      · exact le_rfl
      · simp
  simp_rw [e]
  exact Measurable.iSup fun K => hf.lintegral_kernel_prod_right'

end M4
end E1
end QuantumZipper
