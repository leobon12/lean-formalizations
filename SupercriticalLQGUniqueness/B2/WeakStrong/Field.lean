import SupercriticalLQGUniqueness.B2.Strong.Scale
import LQGMetric.Papers.GM.S1.Dilate
import LQGMetric.Papers.GM.S1.WeakStrong

 














set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC DistOn ofCont addFun addConst IsGFFPlusCont affineComp circleAvg restrictTo
  affinePt)

namespace SupercriticalLQGUniqueness.B2.WeakStrong

 
def dilField (Q : ℝ) (b : ℝ) (h : DistC) : DistC :=
  addConst (affineComp b 0 h) (Q * Real.log b)

theorem dilField_eq (Q : ℝ) (b : Set.Ioi (0 : ℝ)) (h : DistC) :
    dilField Q b h = addConst (scaleTranslateDist b 0 h) (Q * Real.log b) := by
  rw [B2.Strong.scaleTranslateDist_eq_affineComp]; rfl

theorem measurable_dilField (Q b : ℝ) : Measurable (dilField Q b) :=
  LQGMetric.DFGPS.L219.measurable_addConst_of (LQGMetric.measurable_affineComp _ _)
    measurable_const

 
theorem isGFFPlusCont_dilField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsGFFPlusCont h P) (Q : ℝ) {b : ℝ} (hb : 0 < b) :
    IsGFFPlusCont (fun ω => dilField Q b (h ω)) P :=
  Uniqueness.Toolkit.LocalEvents.isGFFPlusCont_addConst
    (LQGMetric.GM.isGFFPlusCont_affineComp hh hb 0) measurable_const

theorem addConst_eq (k : DistC) (c : ℝ) : addConst k c = k + ofCont (ContinuousMap.const ℂ c) :=
  rfl

theorem addConst_addConst (k : DistC) (a c : ℝ) : addConst (addConst k a) c = addConst k (a + c) :=
  B2.Strong.addFun_addConst_const k a c

theorem addConst_addFun (k : DistC) (f : C(ℂ, ℝ)) (c : ℝ) :
    addConst (addFun k f) c = addFun (addConst k c) f := by
  simp only [addConst_eq, addFun, add_right_comm]

theorem affineComp_addConst {r : ℝ} (hr : 0 < r) (z : ℂ) (k : DistC) (c : ℝ) :
    affineComp r z (addConst k c) = addConst (affineComp r z k) c := by
  rw [addConst, LQGMetric.GM.affineComp_addFun hr]
  rfl

theorem dilField_dilField (Q : ℝ) {b₁ b₂ : ℝ} (h₁ : 0 < b₁) (h₂ : 0 < b₂) (h : DistC) :
    dilField Q b₁ (dilField Q b₂ h) = dilField Q (b₂ * b₁) h := by
  simp only [dilField]
  rw [affineComp_addConst h₁, LQGMetric.GM.affineComp_comp h₁.ne' h₂.ne', addConst_addConst,
    Real.log_mul h₂.ne' h₁.ne']
  simp only [mul_zero, add_zero, mul_add]

theorem dilField_one (Q : ℝ) (h : DistC) : dilField Q 1 h = h := by
  simp only [dilField, LQGMetric.GM.affineComp_one_zero, Real.log_one, mul_zero,
    B2.Strong.addConst_zero]

theorem affinePt_smul_inv {b : ℝ} (hb : b ≠ 0) (z : ℂ) : affinePt b 0 (b⁻¹ • z) = z := by
  rw [LQGMetric.affinePt_apply, add_zero, Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
    mul_inv_cancel₀ (by exact_mod_cast hb), one_mul]

 
theorem dilField_addFun (Q : ℝ) {b : ℝ} (hb : 0 < b) (h : DistC) (f : C(ℂ, ℝ)) :
    dilField Q b (addFun h f) = addFun (dilField Q b h) (f.comp (affinePt b 0)) := by
  simp only [dilField]
  rw [LQGMetric.GM.affineComp_addFun hb, addConst_addFun]

 
theorem dilField_translate (Q : ℝ) {b : ℝ} (hb : 0 < b) (z : ℂ) (h : DistC) :
    dilField Q b (translateDist z h) = translateDist (b⁻¹ • z) (dilField Q b h) := by
  simp only [dilField]
  rw [SupercriticalLQGUniqueness.translateDist_eq_affineComp_one,
    SupercriticalLQGUniqueness.translateDist_eq_affineComp_one,
    affineComp_addConst one_pos, LQGMetric.GM.affineComp_comp hb.ne' one_ne_zero,
    LQGMetric.GM.affineComp_comp one_ne_zero hb.ne']
  congr 2
  · ring
  · rw [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (by exact_mod_cast hb.ne'), one_mul]
    push_cast
    ring

 
theorem addConst_scaleTranslate_eq (Q : ℝ) (r : Set.Ioi (0 : ℝ)) (z : ℂ) (h : DistC) :
    addConst (scaleTranslateDist r z h) (Q * Real.log r) = dilField Q r (translateDist z h) := by
  simp only [dilField]
  rw [B2.Strong.scaleTranslateDist_eq_affineComp,
    SupercriticalLQGUniqueness.translateDist_eq_affineComp_one,
    LQGMetric.GM.affineComp_comp (ne_of_gt r.2) one_ne_zero]
  congr 2
  · ring
  · push_cast; ring

theorem isGFFPlusCont_translate {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsGFFPlusCont h P) (z : ℂ) : IsGFFPlusCont (fun ω => translateDist z (h ω)) P := by
  simpa only [SupercriticalLQGUniqueness.translateDist_eq_affineComp_one] using
    LQGMetric.GM.isGFFPlusCont_affineComp hh one_pos z

 

theorem restrictTo_add (V : TopologicalSpace.Opens ℂ) (k k' : DistC) :
    restrictTo V (k + k') = restrictTo V k + restrictTo V k' := by
  exact DFunLike.ext _ _ fun φ => rfl

 
abbrev smulOpens (c : ℝ) (U : TopologicalSpace.Opens ℂ) : TopologicalSpace.Opens ℂ :=
  LQGMetric.GM.dilOpens c U

theorem smul_mem_smulOpens {c : ℝ} (hc : c ≠ 0) (U : TopologicalSpace.Opens ℂ) (z : ℂ) :
    c • z ∈ (smulOpens c U : Set ℂ) ↔ z ∈ (U : Set ℂ) := by
  change LQGMetric.affMap c 0 (c • z) ∈ (U : Set ℂ) ↔ _
  simp only [LQGMetric.affMap, neg_zero, add_zero, inv_smul_smul₀ hc]

 
def restrictMap (Q : ℝ) {b : ℝ} (hb : 0 < b) (U : TopologicalSpace.Opens ℂ) (ρ : DistOn U) :
    DistOn (smulOpens b⁻¹ U) :=
  LQGMetric.GM.dilDist b⁻¹ (inv_ne_zero hb.ne') U ρ +
    restrictTo (smulOpens b⁻¹ U) (ofCont (ContinuousMap.const ℂ (Q * Real.log b)))

theorem measurable_restrictMap (Q : ℝ) {b : ℝ} (hb : 0 < b) (U : TopologicalSpace.Opens ℂ) :
    Measurable (restrictMap Q hb U) := by
  rw [LQGMetric.measurable_distOn_iff]
  intro φ
  simp only [restrictMap, add_apply]
  exact ((LQGMetric.measurable_distOn_iff.1 (LQGMetric.GM.measurable_dilDist _ U)) φ).add_const _

 

theorem restrictTo_dilField (Q : ℝ) {b : ℝ} (hb : 0 < b) (U : TopologicalSpace.Opens ℂ)
    (h : DistC) :
    restrictTo (smulOpens b⁻¹ U) (dilField Q b h) = restrictMap Q hb U (restrictTo U h) := by
  have e := LQGMetric.GM.restrictTo_affineComp_inv (inv_ne_zero hb.ne') U h
  rw [inv_inv] at e
  rw [dilField, addConst_eq, restrictTo_add, e]
  rfl

 

theorem dilField_eq_addFun_rescaled (Q : ℝ) (b : Set.Ioi (0 : ℝ)) (h : DistC) :
    dilField Q b h = addFun (B2.Strong.rescaledField h b)
      (ContinuousMap.const ℂ (circleAvg h b 0 + Q * Real.log b)) := by
  rw [B2.Strong.rescaledField, B2.Strong.addFun_addConst_const, dilField]
  congr 1
  ring

theorem isGFFPlusCont_rescaledField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusCont h P) (b : Set.Ioi (0 : ℝ)) :
    IsGFFPlusCont (fun ω => B2.Strong.rescaledField (h ω) b) P :=
  Uniqueness.Toolkit.LocalEvents.isGFFPlusCont_addConst
    (LQGMetric.GM.isGFFPlusCont_affineComp hh b.2 0)
    ((LQGMetric.measurable_circleAvg_left _ _).comp hh.1).neg

 
theorem ae_circleAvg_rescaledField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : LQGMetric.IsWholePlaneGFF h P) (b s : Set.Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, circleAvg (B2.Strong.rescaledField (h ω) b) s 0 =
      circleAvg (h ω) ((b : ℝ) * s) 0 - circleAvg (h ω) b 0 := by
  have hb := b.2
  have hs := s.2
  have hbs : (0 : ℝ) < b * s := mul_pos hb hs
  have hg := hh.affineComp hb 0
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst hg 0 hs,
    LQGMetric.CircleAvg.ae_circleAvg_affineComp hg hs 0,
    LQGMetric.CircleAvg.ae_circleAvg_affineComp hh hbs 0] with ω h1 h2 h3
  rw [B2.Strong.rescaledField, h1, ← h2, LQGMetric.GM.affineComp_comp hs.ne' hb.ne',
    mul_zero, zero_add, h3]
  ring

end SupercriticalLQGUniqueness.B2.WeakStrong
