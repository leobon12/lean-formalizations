import QuantumZipper.Proofs.Zipper.Cor15FieldGoodFix
import QuantumZipper.Proofs.Zipper.Cor15ShiftGood
import QuantumZipper.Proofs.Zipper.Cor15ZipRead
import QuantumZipper.Proofs.Zipper.Cor15LastPair
import QuantumZipper.Proofs.Zipper.Cor15RegDeriv
import QuantumZipper.Proofs.Zipper.Cor15GroupZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-FIELDGOOD2 (1): a measurable good set for the round trip `D_a ∘ U_a` (deterministic part)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
no proof in the paper). Decision D47 (`DECISIONS.md`). Task COR15-FIELDGOOD2.

For a driver reading `Vp : B1E → ℝ → ℝ` (continuous, `Vp e 0 = 0`, pointwise measurable, as in
`exists_readVp`) and `a > 0`, `FG2Set Vp … a Q` is a measurable set of B1-FULL data values such that
(`regEq_roundTrip_of_fg2`) for every configuration `x` with a continuous driver, whose welding
driver on `[0,a]` is `Vp (b1Data x)` and whose data lie in `FG2Set`, the round trip
`D_a (U_a x)` has the regularized field of `x`.

Write `e = b1Data x`, `z = fromC e.1.1` (the field modulo the constant `c = x.1 (σ 0 1)`),
`ψ = revMapInv (Vp e) a`, `φ = revMap (Vp e) a` (as `CharFun.Fm` of a continuous path, so jointly
measurable in `e`). The zipped driver `V` of `U_a x` is continuous (continuous `x.2`, `x.2 0 = 0`),
so `fwdMapInv V a = revMap (vrev V a) a = φ` on `ℍ` (`fwdMapInv_eq_revMap_vrev`). The conditions,
at every dyadic folded circle `μ = σ(d, 2^{-k})`, `d ∈ Dy`:

* `μ` does not charge the hull of `ψ` (so `deriv ψ = DInv` `μ`-a.e.; the zipped raw value at `μ`
  is the measurable candidate `CInv`, collected in `fg2V e`);
* `RegShift z (μ.map ψ)` (the zipped field is `fromC (fg2V e) + c` at the dyadic circles);
* `RegShift (fromC (fg2V e)) (μ.map φ)` and the re-unzip identity
  `evalReg (fromC (fg2V e)) (μ.map φ) + Q ∫ log |φ'| dμ = z μ`.

Then the raw value of `D_a (U_a x)` at `μ` is `z μ + c = x.1 μ`. The conditions do not involve
the additive constant `c`, which the B1 data do not see. **Own elementary argument** (cost rule of
`AGENT_GUIDE.md`; bookkeeping of the change of variables of `rezip_apply` in the other order).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull B2

theorem fg2_regEq_of_dyadic {x y : FieldSample}
    (h : ∀ (n k : ℕ) (w : ℂ), x (foldedCircle (dyadicRoundC n w) (radius k)) =
      y (foldedCircle (dyadicRoundC n w) (radius k))) : RegEq x y := by
  intro k w
  unfold avgReg
  simp only [h]

theorem fg2_exists_index (n k : ℕ) (w : ℂ) :
    ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 =
      foldedCircle (dyadicRoundC n w) (radius k) := by
  obtain ⟨i, hi⟩ := fullIndex_surj n w 1 one_pos k
  refine ⟨i, ?_⟩
  rw [hi, radius_eq_int_div]

theorem fg2_Dy_form {d : ℂ} (hd : d ∈ RegUnif.Dy) (k : ℕ) :
    ∃ n w, foldedCircle d (radius k) = foldedCircle (dyadicRoundC n w) (radius k) := by
  obtain ⟨_, ⟨n, rfl⟩, w, rfl⟩ := hd
  exact ⟨n, w, CoordReg.foldedCircle_foldH _ _⟩

theorem fg2_addConst_prob (y : FieldSample) (c : ℝ) (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    addConst y c μ = y μ + c := by
  simp [addConst, measure_univ]

variable {Vp : B1E → ℝ → ℝ} {a : ℝ}

/-- The reading `Vp e` as a continuous path on `[0,a]`. -/
def fg2Path (Vp : B1E → ℝ → ℝ) (hVc : ∀ e, Continuous (Vp e)) (a : ℝ) (e : B1E) :
    C(Icc (0 : ℝ) a, ℝ) :=
  ⟨fun s => Vp e s, (hVc e).comp continuous_subtype_val⟩

/-- The unzipping map `revMap (Vp e) a`, in the jointly measurable form `CharFun.Fm`. -/
def fg2Phi (Vp : B1E → ℝ → ℝ) (hVc : ∀ e, Continuous (Vp e)) (a : ℝ) (ha : 0 ≤ a) (e : B1E)
    (w : ℂ) : ℂ :=
  CharFun.Fm 1 a ha (fg2Path Vp hVc a e, w)

/-- The candidate raw values of the zipped field (modulo the additive constant). -/
def fg2V (Vp : B1E → ℝ → ℝ) (a Q : ℝ) (e : B1E) : ℕ → ℝ := fun j =>
  CInv Vp a Q (foldedCircle (fullIndex j).1 (fullIndex j).2) (e.1.1, e)

/-- The good-set conditions at one measure `μ`. -/
def FG2At (Vp : B1E → ℝ → ℝ) (hVc : ∀ e, Continuous (Vp e)) (a Q : ℝ) (ha : 0 ≤ a)
    (μ : Measure ℂ) (e : B1E) : Prop :=
  μ (fwdHull (ArcDriver.trev (Vp e) a) a) = 0 ∧
    E1.RegShift (E1.fromC e.1.1) (μ.map (revMapInv (Vp e) a)) ∧
    E1.RegShift (E1.fromC (fg2V Vp a Q e)) (μ.map (fg2Phi Vp hVc a ha e)) ∧
    evalReg (E1.fromC (fg2V Vp a Q e)) (μ.map (fg2Phi Vp hVc a ha e)) +
        Q * ∫ w, Real.log ‖CharFun.Dm 1 a ha (fg2Path Vp hVc a e, w)‖ ∂μ =
      E1.fromC e.1.1 μ

/-- **The measurable good set** of B1-FULL data values. -/
def FG2Set (Vp : B1E → ℝ → ℝ) (hVc : ∀ e, Continuous (Vp e)) (a Q : ℝ) (ha : 0 ≤ a) :
    Set B1E :=
  {e | e.2 0 = 0} ∩
    ⋂ k : ℕ, ⋂ d ∈ RegUnif.Dy, {e | FG2At Vp hVc a Q ha (foldedCircle d (radius k)) e}

/-! ## Measurability -/

theorem measurable_fg2Path (hVc : ∀ e, Continuous (Vp e)) (hVm : ∀ s, Measurable fun e => Vp e s)
    (a : ℝ) : Measurable (fg2Path Vp hVc a) :=
  ContinuousMap.measurable_iff_eval.2 fun s => hVm s

theorem measurable_fg2V (hVc : ∀ e, Continuous (Vp e)) (hV0 : ∀ e, Vp e 0 = 0)
    (hVm : ∀ s, Measurable fun e => Vp e s) (ha : 0 < a) (Q : ℝ) : Measurable (fg2V Vp a Q) :=
  measurable_pi_iff.2 fun _ => (measurable_CInv hVc hV0 hVm ha Q _).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_id)

theorem fg2_measurable_evalReg_param {α : Type*} [MeasurableSpace α] {Y : α → FieldSample}
    (hY : Measurable Y) {f : α → ℂ → ℂ} (hf : Measurable fun p : α × ℂ => f p.1 p.2)
    (μ : Measure ℂ) [SFinite μ] : Measurable fun b => evalReg (Y b) (μ.map (f b)) := by
  have hfa : ∀ b, Measurable (f b) := fun b => hf.comp (measurable_const.prodMk measurable_id)
  have e : ∀ b, evalReg (Y b) (μ.map (f b)) =
      limUnder atTop fun k => ∫ w, avgReg (Y b) k (f b w) ∂μ := by
    intro b
    unfold evalReg
    congr 1
    funext k
    exact integral_map (hfa b).aemeasurable
      (CoordRegComp.measurable_avgReg_right _ k).aestronglyMeasurable
  simp_rw [e]
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  have hm : Measurable fun q : α × ℂ => avgReg (Y q.1) k (f q.1 q.2) :=
    (measurable_avgReg k).comp ((hY.comp measurable_fst).prodMk hf)
  exact hm.stronglyMeasurable.integral_prod_right'

theorem measurableSet_FG2At (hVc : ∀ e, Continuous (Vp e)) (hV0 : ∀ e, Vp e 0 = 0)
    (hVm : ∀ s, Measurable fun e => Vp e s) (ha : 0 < a) (Q : ℝ) (μ : Measure ℂ) [SFinite μ] :
    MeasurableSet {e | FG2At Vp hVc a Q ha.le μ e} := by
  have hg := measurable_fg2Path hVc hVm a
  have hgz : Measurable fun p : B1E × ℂ => ((fg2Path Vp hVc a p.1, p.2) : C(Icc (0 : ℝ) a, ℝ) × ℂ) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hφ : Measurable fun p : B1E × ℂ => fg2Phi Vp hVc a ha.le p.1 p.2 :=
    (CharFun.measurable_Fm 1 a ha.le).comp hgz
  have hψ : Measurable fun p : B1E × ℂ => revMapInv (Vp p.1) a p.2 :=
    (measurable_revMapInv_param hVc hV0 hVm ha).comp measurable_swap
  have hv := measurable_fg2V hVc hV0 hVm ha Q
  have h11 : Measurable fun e : B1E => e.1.1 := measurable_fst.comp measurable_fst
  have hD : Measurable fun e : B1E =>
      ∫ w, Real.log ‖CharFun.Dm 1 a ha.le (fg2Path Vp hVc a e, w)‖ ∂μ := by
    have hm : Measurable fun q : B1E × ℂ =>
        Real.log ‖CharFun.Dm 1 a ha.le (fg2Path Vp hVc a q.1, q.2)‖ :=
      Real.measurable_log.comp ((CharFun.measurable_Dm 1 a ha.le).comp hgz).norm
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  simp only [FG2At, ofPred_and]
  refine (measurableSet_hullNull_meas hVc hVm ha.le μ).inter
    ((measurableSet_regShift_param h11 hψ μ).inter
      ((measurableSet_regShift_param hv hφ μ).inter (measurableSet_eq_fun ?_ ?_)))
  · exact (fg2_measurable_evalReg_param (measurable_fromC.comp hv) hφ μ).add (hD.const_mul Q)
  · exact (measurable_pi_apply μ).comp (measurable_fromC.comp h11)

theorem measurableSet_FG2Set (hVc : ∀ e, Continuous (Vp e)) (hV0 : ∀ e, Vp e 0 = 0)
    (hVm : ∀ s, Measurable fun e => Vp e s) (ha : 0 < a) (Q : ℝ) :
    MeasurableSet (FG2Set Vp hVc a Q ha.le) :=
  (measurableSet_eq_fun ((measurable_pi_apply (0 : ℝ≥0)).comp measurable_snd)
    measurable_const).inter
    (MeasurableSet.iInter fun _ => MeasurableSet.biInter RegUnif.countable_Dy fun _ _ =>
      measurableSet_FG2At hVc hV0 hVm ha Q _)

/-! ## The deterministic round trip on the good set -/

/-- The candidate `fromC (fg2V e)` is the zipped raw value (of `fromC e.1.1`) at a dyadic folded
circle not charging the hull. -/
theorem fromC_fg2V_eq (hVc : ∀ e, Continuous (Vp e)) (hV0 : ∀ e, Vp e 0 = 0) (ha : 0 < a)
    (Q : ℝ) (e : B1E) {μ : Measure ℂ}
    (hμi : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ) (hμH : μ Hᶜ = 0)
    (hnull : μ (fwdHull (ArcDriver.trev (Vp e) a) a) = 0) :
    E1.fromC (fg2V Vp a Q e) μ = coordChange (E1.fromC e.1.1) (revMapInv (Vp e) a) Q μ := by
  classical
  have hs := Nat.find_spec hμi
  rw [E1.fromC, dif_pos hμi]
  unfold fg2V
  rw [hs]
  unfold CInv coordChange
  congr 2
  refine integral_congr_ae ?_
  have h1 : ∀ᵐ z ∂μ, z ∈ H := ae_iff.2 hμH
  have h2 : ∀ᵐ z ∂μ, z ∉ fwdHull (ArcDriver.trev (Vp e) a) a := ae_iff.2 (by simpa using hnull)
  filter_upwards [h1, h2] with z hz1 hz2
  rw [DInv_eq hVc hV0 ha e ⟨hz1, hz2⟩]

/-- **Deterministic round trip on the good set.** -/
theorem regEq_roundTrip_of_fg2 {γ : ℝ} (hVc : ∀ e, Continuous (Vp e)) (hV0 : ∀ e, Vp e 0 = 0)
    (ha : 0 < a) {x : FieldSample × (ℝ → ℝ)} (hxc : Continuous x.2)
    (hW : EqOn (weldDriver γ x.1 a) (Vp (b1Data x)) (Icc 0 a))
    (hG : b1Data x ∈ FG2Set Vp hVc a (Qc γ) ha.le) :
    RegEq (zipCapDown γ a (zipCapUp γ a x)).1 x.1 := by
  set e := b1Data x with he
  set Q := Qc γ with hQ
  set U := Vp e with hU
  set c := x.1 (foldedCircle 0 1) with hc
  set z := E1.fromC e.1.1 with hz
  obtain ⟨hx0, hGk⟩ := hG
  have hGk' : ∀ k : ℕ, ∀ d ∈ RegUnif.Dy, FG2At Vp hVc a Q ha.le (foldedCircle d (radius k)) e :=
    fun k d hd => mem_iInter₂.1 (mem_iInter.1 hGk k) d hd
  -- the field of `x` is `z + c` at the dyadic circles
  have hx1 : ∀ n k w, x.1 (foldedCircle (dyadicRoundC n w) (radius k)) =
      addConst z c (foldedCircle (dyadicRoundC n w) (radius k)) := by
    intro n k w
    rw [fg2_addConst_prob]
    change _ = fieldOf x.1 _ + c
    rw [fieldOf_apply_fc]
    ring
  have hreg1 : RegEq x.1 (addConst z c) := fg2_regEq_of_dyadic hx1
  have hψ : revMapInv (weldDriver γ x.1 a) a = revMapInv U a := revMapInv_congr_drive hW
  -- the zipped field is `fromC (fg2V e) + c` at the dyadic circles
  have hy : ∀ n k w, (zipCapUp γ a x).1 (foldedCircle (dyadicRoundC n w) (radius k)) =
      addConst (E1.fromC (fg2V Vp a Q e)) c (foldedCircle (dyadicRoundC n w) (radius k)) := by
    intro n k w
    obtain ⟨hn, hA3, -, -⟩ := hGk' k _ (RegUnif.foldH_dyadicRoundC_mem_Dy n w)
    rw [CoordReg.foldedCircle_foldH] at hn hA3
    have hμH : foldedCircle (dyadicRoundC n w) (radius k) Hᶜ = 0 :=
      ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k))
    rw [fg2_addConst_prob, fromC_fg2V_eq hVc hV0 ha Q e (fg2_exists_index n k w) hμH hn]
    show coordChange x.1 (revMapInv (weldDriver γ x.1 a) a) Q _ = _
    rw [hψ, coordChange_congr_regEq hreg1]
    have : IsProbabilityMeasure
        ((foldedCircle (dyadicRoundC n w) (radius k)).map (revMapInv U a)) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_revMapInv (hVc e) ha.le).aemeasurable).2
        inferInstance
    unfold coordChange
    rw [E1.evalReg_addConst_of_regShift hA3 c]
    ring
  have hregy : RegEq (zipCapUp γ a x).1 (addConst (E1.fromC (fg2V Vp a Q e)) c) :=
    fg2_regEq_of_dyadic hy
  -- the zipped driver is continuous and reads `U` on `[0,a]`
  have hx00 : x.2 0 = 0 := by simpa [he, b1Data] using hx0
  have hVeq : (zipCapUp γ a x).2 =
      fun s => if s ≤ a then U (a - max s 0) - U a else x.2 (s - a) - U a := by
    funext s
    simp only [zipCapUp]
    split_ifs with hs
    · rw [hW ⟨sub_nonneg.2 (max_le hs ha.le), sub_le_self _ (le_max_right _ _)⟩,
        hW ⟨ha.le, le_rfl⟩]
    · rw [hW ⟨ha.le, le_rfl⟩]
  have hVc' : Continuous (zipCapUp γ a x).2 := by
    rw [hVeq]
    refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
    · exact ((hVc e).comp (continuous_const.sub (continuous_id.max continuous_const))).sub
        continuous_const
    · exact (hxc.comp (continuous_id.sub continuous_const)).sub continuous_const
    · intro s hs
      rw [hs, max_eq_left ha.le, sub_self]
      simp only [hU, hV0, hx00]
  have hV0' : (zipCapUp γ a x).2 0 = 0 := by
    rw [hVeq]
    simp [ha.le]
  have hφ : EqOn (fwdMapInv (zipCapUp γ a x).2 a) (fg2Phi Vp hVc a ha.le e) H := by
    intro w hw
    rw [fwdMapInv_eq_revMap_vrev hVc' hV0' ha.le hw]
    show _ = revMap (CharFun.Wof 1 a ha.le (fg2Path Vp hVc a e)) a w
    refine ReverseFlow.revMap_congr_drive w fun r hr => ?_
    have h1 : a - r ≤ a := by linarith [hr.1]
    rw [vrev_of_mem hr, hVeq]
    simp only [h1, le_refl, ite_true, max_eq_left (sub_nonneg.2 hr.2), max_eq_left ha.le,
      sub_sub_cancel, sub_self]
    simp [CharFun.Wof, fg2Path, projIcc_of_mem ha.le hr, hU, hV0]
  -- the raw values of the round trip
  refine fg2_regEq_of_dyadic fun n k w => ?_
  obtain ⟨-, -, hA6, hA7⟩ := hGk' k _ (RegUnif.foldH_dyadicRoundC_mem_Dy n w)
  rw [CoordReg.foldedCircle_foldH] at hA6 hA7
  show coordChange (zipCapUp γ a x).1 (fwdMapInv (zipCapUp γ a x).2 a) Q _ = x.1 _
  rw [CoordReg.coordChange_fc_congr _ hφ Q _ (radius_pos k), hx1 n k w, fg2_addConst_prob]
  have : IsProbabilityMeasure
      ((foldedCircle (dyadicRoundC n w) (radius k)).map (fg2Phi Vp hVc a ha.le e)) :=
    (Measure.isProbabilityMeasure_map_iff
      (CharFun.measurable_revMap_Wof 1 a ha.le _).aemeasurable).2 inferInstance
  have hint : ∫ u, Real.log ‖deriv (fg2Phi Vp hVc a ha.le e) u‖
      ∂(foldedCircle (dyadicRoundC n w) (radius k)) =
      ∫ u, Real.log ‖CharFun.Dm 1 a ha.le (fg2Path Vp hVc a e, u)‖
        ∂(foldedCircle (dyadicRoundC n w) (radius k)) := by
    refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k)).mono
      fun u hu => ?_)
    dsimp only
    rw [CharFun.Dm_eq 1 a ha.le _ hu]
    rfl
  unfold coordChange
  rw [evalReg_congr_regEq hregy, E1.evalReg_addConst_of_regShift hA6 c, hint, hz, ← hA7]
  ring

end Cor15Group
end QuantumZipper
