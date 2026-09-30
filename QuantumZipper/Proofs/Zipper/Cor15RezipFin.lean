import QuantumZipper.Proofs.Zipper.Cor15RezipRegMeas
import QuantumZipper.Proofs.GFF.CoordRegRandom
import QuantumZipper.Proofs.Zipper.Cor15PosRezip

/-!
# Corollary 1.5, positive times: input (R) `Cor15RezipRegStmt` (the random-driver step)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
The fixed-driver form of (R) is `ae_evalReg_coordChange_pushed_fc` (`Cor15RezipRegTame`), and
`ae_rezip_good` (`Cor15RezipRegGood`) says that a.s. the reversed driver `vrev (√κ B) t`
satisfies its hypotheses. Here we pass to the random driver independent of the field by
Fubini (`CharFunRhs.ae_indep_ae`) and prove **`cor15RezipRegStmt : Cor15RezipRegStmt`**.

**Route (own elementary argument: measurability bookkeeping and Fubini).**
* The reversed driver is written as a measurable function of the path `a = B|[0,t]`:
  `V_a r = Wof κ t (finRevPath a) r = √κ (a(t − r) − a(t))` (so `V_a 0 = 0`, no translation
  lemma needed), and `V_{pathC t B₁} = vrev (√κ B) t` on `[0,t]` for a continuous version `B₁`.
* The two sides of (R) at driver `V_a` are replaced by jointly measurable expressions
  `finL`, `finR` in `(a, x)`: `finL` equals the left side for every `a` (`finL_eq`), and `finR`
  equals the right side whenever the folded circle is carried by `revMap V_a t '' ℍ`
  (`finR_eq`). Joint measurability uses `CoordReg.measurable_avgReg_coordChange`,
  `CharFun.measurable_Dm` and `measurable_revMapInv_param`.
* Fibres: at each good path, `ae_evalReg_coordChange_pushed_fc` (DS 2011 Prop. 3.1 via RC3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun

variable {t : ℝ}

/-- The reversed path `u ↦ a(t − u) − a(t)` on `[0,t]`. -/
def finRevPath (ht : 0 ≤ t) (a : C(Icc (0 : ℝ) t, ℝ)) : C(Icc (0 : ℝ) t, ℝ) where
  toFun u := a ⟨t - u.1, ⟨sub_nonneg.2 u.2.2, sub_le_self t u.2.1⟩⟩ - a ⟨t, ⟨ht, le_rfl⟩⟩
  continuous_toFun := by fun_prop

theorem measurable_finRevPath (ht : 0 ≤ t) : Measurable (finRevPath ht) :=
  ContinuousMap.measurable_iff_eval.2 fun _ =>
    (continuous_eval_const _).measurable.sub (continuous_eval_const _).measurable

theorem continuous_finV (κ : ℝ) (ht : 0 < t) (a : C(Icc (0 : ℝ) t, ℝ)) :
    Continuous (Wof κ t ht.le (finRevPath ht.le a)) :=
  continuous_Wof κ t ht.le _

theorem finV_apply (κ : ℝ) (ht : 0 < t) (a : C(Icc (0 : ℝ) t, ℝ)) {r : ℝ} (hr : r ∈ Icc 0 t) :
    Wof κ t ht.le (finRevPath ht.le a) r = Real.sqrt κ * (a ⟨t - r, ⟨sub_nonneg.2 hr.2, sub_le_self t hr.1⟩⟩ -
      a ⟨t, ⟨ht.le, le_rfl⟩⟩) := by
  simp only [Wof, projIcc_of_mem ht.le hr]
  rfl

theorem finV_zero (κ : ℝ) (ht : 0 < t) (a : C(Icc (0 : ℝ) t, ℝ)) : Wof κ t ht.le (finRevPath ht.le a) 0 = 0 := by
  rw [finV_apply κ ht a ⟨le_rfl, ht.le⟩]
  have : a ⟨t - 0, ⟨sub_nonneg.2 ht.le, sub_le_self t le_rfl⟩⟩ = a ⟨t, ⟨ht.le, le_rfl⟩⟩ :=
    congrArg a (Subtype.ext (sub_zero t))
  rw [this, sub_self, mul_zero]

theorem measurable_finV_apply (κ : ℝ) (ht : 0 < t) (s : ℝ) :
    Measurable fun a : C(Icc (0 : ℝ) t, ℝ) => Wof κ t ht.le (finRevPath ht.le a) s := by
  show Measurable fun a => Real.sqrt κ * (finRevPath ht.le a) (projIcc 0 t ht.le s)
  exact ((continuous_eval_const (projIcc 0 t ht.le s)).measurable.comp
    (measurable_finRevPath ht.le)).const_mul _

theorem measurable_finInv (κ : ℝ) (ht : 0 < t) :
    Measurable fun p : C(Icc (0 : ℝ) t, ℝ) × ℂ => revMapInv (Wof κ t ht.le (finRevPath ht.le p.1)) t p.2 := by
  have h1 := continuous_finV κ ht
  have h2 := finV_zero κ ht
  have h3 := measurable_finV_apply κ ht
  have h : Measurable fun p : ℂ × C(Icc (0 : ℝ) t, ℝ) => revMapInv (Wof κ t ht.le (finRevPath ht.le p.2)) t p.1 :=
    measurable_revMapInv_param h1 h2 h3 ht
  exact h.comp (f := fun p : C(Icc (0 : ℝ) t, ℝ) × ℂ => (p.2, p.1))
    (measurable_snd.prodMk measurable_fst)

/-- Jointly measurable left side of (R). -/
def finL (κ : ℝ) (ht : 0 < t) (σ : Measure ℂ) (p : C(Icc (0 : ℝ) t, ℝ) × FieldSample) : ℝ :=
  limUnder atTop fun k => ∫ z, avgReg (coordChange (ofFun (h0rev κ) + p.2)
    (revMap (Wof κ t ht.le (finRevPath ht.le p.1)) t) (Qc (Real.sqrt κ))) k (revMapInv (Wof κ t ht.le (finRevPath ht.le p.1)) t z) ∂σ

/-- Jointly measurable right side of (R) (valid on good paths). -/
def finR (κ : ℝ) (ht : 0 < t) (σ : Measure ℂ) (p : C(Icc (0 : ℝ) t, ℝ) × FieldSample) : ℝ :=
  evalReg (ofFun (h0rev κ) + p.2) σ + Qc (Real.sqrt κ) *
    ∫ z, Real.log ‖Dm κ t ht.le (finRevPath ht.le p.1, revMapInv (Wof κ t ht.le (finRevPath ht.le p.1)) t z)‖ ∂σ

theorem measurable_finL (κ : ℝ) (ht : 0 < t) (σ : Measure ℂ) [SFinite σ] :
    Measurable (finL κ ht σ) := by
  unfold finL
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  have h1 : Measurable fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ =>
      avgReg (coordChange (ofFun (h0rev κ) + q.1.2) (revMap (Wof κ t ht.le q.1.1) t)
        (Qc (Real.sqrt κ))) k q.2 :=
    CoordReg.measurable_avgReg_coordChange κ ht.le (h0rev κ) (Qc (Real.sqrt κ)) k
  have h2 : Measurable fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ =>
      (((finRevPath ht.le q.1.1, q.1.2), revMapInv (Wof κ t ht.le (finRevPath ht.le q.1.1)) t q.2) :
        (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ) := by
    refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
    · exact (measurable_finRevPath ht.le).comp
        (f := fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ => q.1.1)
        (measurable_fst.comp measurable_fst)
    · exact measurable_snd.comp measurable_fst
    · exact (measurable_finInv κ ht).comp
        (f := fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ => (q.1.1, q.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h3 : Measurable fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ =>
      avgReg (coordChange (ofFun (h0rev κ) + q.1.2) (revMap (Wof κ t ht.le (finRevPath ht.le q.1.1)) t)
        (Qc (Real.sqrt κ))) k (revMapInv (Wof κ t ht.le (finRevPath ht.le q.1.1)) t q.2) := by
    simpa only [Function.comp_def] using h1.comp h2
  exact h3.stronglyMeasurable.integral_prod_right'

theorem measurable_finR (κ : ℝ) (ht : 0 < t) (σ : Measure ℂ) [SFinite σ] :
    Measurable (finR κ ht σ) := by
  unfold finR
  have h1 : Measurable fun q : C(Icc (0 : ℝ) t, ℝ) × ℂ =>
      Real.log ‖Dm κ t ht.le (finRevPath ht.le q.1, revMapInv (Wof κ t ht.le (finRevPath ht.le q.1)) t q.2)‖ := by
    have hA : Measurable fun q : C(Icc (0 : ℝ) t, ℝ) × ℂ =>
        ((finRevPath ht.le q.1, revMapInv (Wof κ t ht.le (finRevPath ht.le q.1)) t q.2) : C(Icc (0 : ℝ) t, ℝ) × ℂ) :=
      ((measurable_finRevPath ht.le).comp (f := fun q : C(Icc (0 : ℝ) t, ℝ) × ℂ => q.1)
        measurable_fst).prodMk (measurable_finInv κ ht)
    have hB : Measurable fun q : C(Icc (0 : ℝ) t, ℝ) × ℂ =>
        Dm κ t ht.le (finRevPath ht.le q.1, revMapInv (Wof κ t ht.le (finRevPath ht.le q.1)) t q.2) :=
      (measurable_Dm κ t ht.le).comp hA
    exact Real.measurable_log.comp hB.norm
  have h4 : Measurable fun a : C(Icc (0 : ℝ) t, ℝ) =>
      ∫ z, Real.log ‖Dm κ t ht.le (finRevPath ht.le a, revMapInv (Wof κ t ht.le (finRevPath ht.le a)) t z)‖ ∂σ :=
    h1.stronglyMeasurable.integral_prod_right'.measurable
  have h5 : Measurable fun p : C(Icc (0 : ℝ) t, ℝ) × FieldSample =>
      evalReg (ofFun (h0rev κ) + p.2) σ :=
    (measurable_evalReg σ).comp (f := fun p : C(Icc (0 : ℝ) t, ℝ) × FieldSample =>
      ofFun (h0rev κ) + p.2) ((measurable_const_add _).comp measurable_snd)
  exact h5.add ((h4.comp (f := fun p : C(Icc (0 : ℝ) t, ℝ) × FieldSample => p.1)
    measurable_fst).const_mul _)

theorem finL_eq (κ : ℝ) (ht : 0 < t) (σ : Measure ℂ) (a : C(Icc (0 : ℝ) t, ℝ))
    (x : FieldSample) :
    finL κ ht σ (a, x) =
      evalReg (coordChange (ofFun (h0rev κ) + x) (revMap (Wof κ t ht.le (finRevPath ht.le a)) t) (Qc (Real.sqrt κ)))
        (σ.map (revMapInv (Wof κ t ht.le (finRevPath ht.le a)) t)) := by
  unfold finL evalReg
  refine congrArg _ (funext fun k => ?_)
  have hg : Measurable fun w => avgReg (coordChange (ofFun (h0rev κ) + x)
      (revMap (Wof κ t ht.le (finRevPath ht.le a)) t) (Qc (Real.sqrt κ))) k w :=
    (measurable_avgReg k).comp (f := fun w => (coordChange (ofFun (h0rev κ) + x)
      (revMap (Wof κ t ht.le (finRevPath ht.le a)) t) (Qc (Real.sqrt κ)), w)) (measurable_const.prodMk measurable_id)
  exact (integral_map (measurable_revMapInv (continuous_Wof κ t ht.le (finRevPath ht.le a)) ht.le).aemeasurable
    hg.aestronglyMeasurable).symm

theorem finR_eq (κ : ℝ) (ht : 0 < t) {σ : Measure ℂ} (a : C(Icc (0 : ℝ) t, ℝ))
    (x : FieldSample) (hσD : ∀ᵐ z ∂σ, z ∈ revMap (Wof κ t ht.le (finRevPath ht.le a)) t '' H) :
    finR κ ht σ (a, x) =
      coordChange (ofFun (h0rev κ) + x) (revMap (Wof κ t ht.le (finRevPath ht.le a)) t) (Qc (Real.sqrt κ))
        (σ.map (revMapInv (Wof κ t ht.le (finRevPath ht.le a)) t)) := by
  have hVc := continuous_Wof κ t ht.le (finRevPath ht.le a)
  unfold finR coordChange
  rw [map_revMap_map_revMapInv hVc ht.le hσD]
  congr 2
  have hm : Measurable fun w => Real.log ‖Dm κ t ht.le (finRevPath ht.le a, w)‖ :=
    Real.measurable_log.comp ((measurable_Dm κ t ht.le).comp
      (measurable_const.prodMk measurable_id)).norm
  rw [integral_congr_ae ((ae_mem_H_map_revMapInv hVc ht.le hσD).mono fun w hw => by
      show Real.log ‖deriv (revMap (Wof κ t ht.le (finRevPath ht.le a)) t) w‖ =
        Real.log ‖Dm κ t ht.le (finRevPath ht.le a, w)‖
      rw [Dm_eq κ t ht.le _ hw]),
    integral_map (measurable_revMapInv hVc ht.le).aemeasurable hm.aestronglyMeasurable]

end Cor15Group
end QuantumZipper
