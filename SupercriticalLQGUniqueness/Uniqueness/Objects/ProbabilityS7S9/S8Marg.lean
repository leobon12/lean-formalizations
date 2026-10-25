import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S8Weyl
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.CMBound
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.RatioMarginal.OneAnnulus
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete
import LQGMetric.Papers.GM.S5.L510C7
import LQGMetric.Papers.GM.S5.Prop43bTrans
import LQGMetric.Papers.GM.S6.GeodSelN
import LQGMetric.Papers.GM.S5.Prop43bInv




 



























set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9

open LQGMetric (DistC TestC)

 

 
theorem enn_mul_lt_top_iff {k : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (a : ℝ≥0∞) :
    k * a < ⊤ ↔ a < ⊤ := by
  constructor
  · intro h
    by_contra ha
    rw [not_lt, top_le_iff] at ha
    rw [ha, ENNReal.mul_top hk0] at h
    exact lt_irrefl _ h
  · intro h
    exact ENNReal.mul_lt_top hkt.lt_top h

 
def supOuter {R : ℝ} (hR : 0 < R) (w : ℂ) : EuclideanAnnulus :=
  ⟨(w, (2 + 1 / 20) * R, (3 - 1 / 20) * R), by positivity, by nlinarith⟩

 
def supInner {R : ℝ} (hR : 0 < R) (w : ℂ) : EuclideanAnnulus :=
  ⟨(w, (1 + 1 / 20) * R, (2 - 1 / 20) * R), by positivity, by nlinarith⟩

 
def SupProxy (κ : ℝ) (d : LSCMetric) {R : ℝ} (hR : 0 < R) (w : ℂ) : Prop :=
  aroundDist d (supOuter hR w) < ⊤ ∧
    aroundDist d (supOuter hR w) ≤ ENNReal.ofReal κ * acrossDist d (supInner hR w) ∧
    0 < acrossDist d (supInner hR w)

 
theorem measurableSet_supProxy {D : DistC → LSCMetric} (hD : Measurable D) (κ : ℝ) {R : ℝ}
    (hR : 0 < R) (w : ℂ) : MeasurableSet {g : DistC | SupProxy κ (D g) hR w} := by
  have ha : Measurable fun g => aroundDist (D g) (supOuter hR w) :=
    (Toolkit.CountableBase.aroundBoundedAnnulus_borel _).comp hD
  have hc : Measurable fun g => acrossDist (D g) (supInner hR w) :=
    (SupercriticalLQGUniqueness.measurable_acrossDist _).comp hD
  have hset : {g : DistC | SupProxy κ (D g) hR w} =
      ({g | aroundDist (D g) (supOuter hR w) < ⊤} ∩
        {g | aroundDist (D g) (supOuter hR w) ≤
          ENNReal.ofReal κ * acrossDist (D g) (supInner hR w)}) ∩
        {g | 0 < acrossDist (D g) (supInner hR w)} := by
    ext g
    simp only [SupProxy, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [hset]
  exact ((measurableSet_lt ha measurable_const).inter
    (measurableSet_le ha (measurable_const.mul hc))).inter (measurableSet_lt measurable_const hc)

 
theorem supProxy_scale_iff (κ : ℝ) (d₁ d₂ : LSCMetric) (k : ℝ≥0∞) (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hscale : ∀ x y : ℂ, d₂ (x, y) = k * d₁ (x, y)) {R : ℝ} (hR : 0 < R) (w : ℂ) :
    SupProxy κ d₂ hR w ↔ SupProxy κ d₁ hR w := by
  unfold SupProxy
  rw [Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale d₁ d₂ k hk0 hkt hscale,
    Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale d₁ d₂ k hk0 hkt hscale]
  have h1 : k * aroundDist d₁ (supOuter hR w) < ⊤ ↔ aroundDist d₁ (supOuter hR w) < ⊤ :=
    enn_mul_lt_top_iff hk0 hkt _
  have h2 : k * aroundDist d₁ (supOuter hR w) ≤
        ENNReal.ofReal κ * (k * acrossDist d₁ (supInner hR w)) ↔
      aroundDist d₁ (supOuter hR w) ≤ ENNReal.ofReal κ * acrossDist d₁ (supInner hR w) := by
    rw [mul_left_comm]
    exact ENNReal.mul_le_mul_iff_right hk0 hkt
  have h3 : 0 < k * acrossDist d₁ (supInner hR w) ↔ 0 < acrossDist d₁ (supInner hR w) := by
    rw [ENNReal.mul_pos_iff]
    exact ⟨fun h => h.2, fun h => ⟨pos_iff_ne_zero.mpr hk0, h⟩⟩
  rw [h1, h2, h3]

 

 
def shapeSupOuter : EuclideanAnnulus := ⟨(0, (41 / 20, 59 / 20)), by norm_num, by norm_num⟩

 
def shapeSupInner : EuclideanAnnulus := ⟨(0, (21 / 20, 39 / 20)), by norm_num, by norm_num⟩

theorem supOuter_eq (R : Ioi (0 : ℝ)) (w : ℂ) :
    Positivity.Witnesses.annulusTranslate (shapeSupOuter.dilate R R.2) w = supOuter R.2 w := by
  apply Subtype.ext
  change ((R : ℝ) • (0 : ℂ) + w, (R : ℝ) * (41 / 20), (R : ℝ) * (59 / 20)) =
    (w, (2 + 1 / 20) * (R : ℝ), (3 - 1 / 20) * (R : ℝ))
  simp only [smul_zero, zero_add, Prod.mk.injEq, true_and]
  constructor <;> ring

theorem supInner_eq (R : Ioi (0 : ℝ)) (w : ℂ) :
    Positivity.Witnesses.annulusTranslate (shapeSupInner.dilate R R.2) w = supInner R.2 w := by
  apply Subtype.ext
  change ((R : ℝ) • (0 : ℂ) + w, (R : ℝ) * (21 / 20), (R : ℝ) * (39 / 20)) =
    (w, (1 + 1 / 20) * (R : ℝ), (2 - 1 / 20) * (R : ℝ))
  simp only [smul_zero, zero_add, Prod.mk.injEq, true_and]
  constructor <;> ring

 

 
def supBumpIn : ContDiffBump (0 : ℂ) := ⟨39 / 20, 41 / 20, by norm_num, by norm_num⟩

 
def supBumpOut : ContDiffBump (0 : ℂ) := ⟨59 / 20, 3, by norm_num, by norm_num⟩

 
def supAnnBump (K : ℝ) : TestC where
  toFun := fun y => K * (supBumpIn y - supBumpOut y)
  contDiff' := contDiff_const.mul (supBumpIn.contDiff.sub supBumpOut.contDiff)
  hasCompactSupport' := (supBumpIn.hasCompactSupport.sub supBumpOut.hasCompactSupport).mul_left
  tsupport_subset' := subset_univ _

theorem supAnnBump_apply (K : ℝ) (y : ℂ) :
    supAnnBump K y = K * (supBumpIn y - supBumpOut y) := rfl

theorem supAnnBump_eq_neg (K : ℝ) {y : ℂ} (h1 : 41 / 20 ≤ ‖y‖) (h2 : ‖y‖ ≤ 59 / 20) :
    supAnnBump K y = -K := by
  rw [supAnnBump_apply]
  have hin : supBumpIn y = 0 := by
    apply Function.notMem_support.mp
    rw [ContDiffBump.support_eq]
    change y ∉ Metric.ball (0 : ℂ) (41 / 20)
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hout : supBumpOut y = 1 := supBumpOut.one_of_mem_closedBall (by
    change y ∈ Metric.closedBall (0 : ℂ) (59 / 20)
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h2)
  rw [hin, hout]
  ring

theorem supAnnBump_eq_zero (K : ℝ) {y : ℂ} (h : ‖y‖ ≤ 39 / 20) : supAnnBump K y = 0 := by
  rw [supAnnBump_apply]
  have hin : supBumpIn y = 1 := supBumpIn.one_of_mem_closedBall (by
    change y ∈ Metric.closedBall (0 : ℂ) (39 / 20)
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h)
  have hout : supBumpOut y = 1 := supBumpOut.one_of_mem_closedBall (by
    change y ∈ Metric.closedBall (0 : ℂ) (59 / 20)
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith)
  rw [hin, hout]
  ring

 
def supBumpAt (K R : ℝ) (w : ℂ) : TestC :=
  LQGMetric.GM.transTest w (LQGMetric.GM.dilT R (supAnnBump K))

theorem supBumpAt_apply (K : ℝ) {R : ℝ} (hR : 0 < R) (w y : ℂ) :
    supBumpAt K R w y = supAnnBump K ((R⁻¹ : ℝ) • (y - w)) := by
  rw [supBumpAt, LQGMetric.GM.transTest_apply, LQGMetric.GM.dilT_apply hR]

theorem gradEnergy_supBumpAt (K : ℝ) {R : ℝ} (hR : 0 < R) (w : ℂ) :
    LQGMetric.gradEnergy (supBumpAt K R w) = LQGMetric.gradEnergy (supAnnBump K) := by
  rw [supBumpAt, LQGMetric.GM.gradEnergy_transTest, LQGMetric.GM.gradEnergy_dilT hR]

theorem norm_smul_inv_sub' {R : ℝ} (hR : 0 < R) (w y : ℂ) :
    ‖(R⁻¹ : ℝ) • (y - w)‖ = dist y w / R := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), dist_eq_norm]
  field_simp

theorem supBumpAt_eq_neg (K : ℝ) {R : ℝ} (hR : 0 < R) (w : ℂ) {y : ℂ}
    (h1 : 41 / 20 * R ≤ dist y w) (h2 : dist y w ≤ 59 / 20 * R) : supBumpAt K R w y = -K := by
  rw [supBumpAt_apply K hR]
  apply supAnnBump_eq_neg <;> rw [norm_smul_inv_sub' hR]
  · rw [le_div_iff₀ hR]; linarith
  · rw [div_le_iff₀ hR]; linarith

theorem supBumpAt_eq_zero (K : ℝ) {R : ℝ} (hR : 0 < R) (w : ℂ) {y : ℂ}
    (h : dist y w ≤ 39 / 20 * R) : supBumpAt K R w y = 0 := by
  rw [supBumpAt_apply K hR]
  apply supAnnBump_eq_zero
  rw [norm_smul_inv_sub' hR, div_le_iff₀ hR]
  linarith

theorem testCont_supBumpAt_apply (K R : ℝ) (w y : ℂ) :
    LQGMetric.testCont (supBumpAt K R w) y = supBumpAt K R w y := rfl

 

 


theorem supProxy_weyl (ξ : ℝ) (d e : LSCMetric) {K R : ℝ} (hR : 0 < R) (w : ℂ)
    (he : ∀ u v : ℂ, e (u, v) = weylScale ξ (LQGMetric.testCont (supBumpAt K R w)) d (u, v))
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), d.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (κ : ℝ) (n M₁ M₂ : ℝ≥0∞) (hn0 : n ≠ 0) (hnt : n ≠ ⊤)
    (hM : ENNReal.ofReal (Real.exp (ξ * -K)) * M₁ ≤ ENNReal.ofReal κ * M₂⁻¹) (hM₁ : M₁ ≠ ⊤)
    (hM₂ : M₂ ≠ ⊤)
    (h1 : n * aroundDist d (supOuter hR w) ≤ M₁) (h2 : M₂⁻¹ ≤ n * acrossDist d (supInner hR w)) :
    SupProxy κ e hR w := by
  have haround : aroundDist e (supOuter hR w) ≤
      ENNReal.ofReal (Real.exp (ξ * -K)) * aroundDist d (supOuter hR w) := by
    have hfA : ∀ y ∈ (supOuter hR w).toSet, LQGMetric.testCont (supBumpAt K R w) y = -K := by
      intro y hy
      have hy' : y ∈ Metric.ball w ((3 - 1 / 20) * R) ∧
          y ∉ closure (Metric.ball w ((2 + 1 / 20) * R)) := hy
      rw [closure_ball w (by positivity), Metric.mem_ball, Metric.mem_closedBall,
        not_le] at hy'
      rw [testCont_supBumpAt_apply]
      exact supBumpAt_eq_neg K hR w (by linarith [hy'.2]) (by linarith [hy'.1])
    exact aroundDist_le_weyl ξ (LQGMetric.testCont (supBumpAt K R w)) d e he (supOuter hR w) (-K)
      hfA
  have hacross : acrossDist d (supInner hR w) ≤ acrossDist e (supInner hR w) := by
    have hf0 : ∀ y : ℂ, (supInner hR w).innerRadius ≤ dist y (supInner hR w).center →
        dist y (supInner hR w).center ≤ (supInner hR w).outerRadius →
        LQGMetric.testCont (supBumpAt K R w) y = 0 := by
      intro y _ hy2
      rw [testCont_supBumpAt_apply]
      have hy2' : dist y w ≤ (2 - 1 / 20) * R := hy2
      exact supBumpAt_eq_zero K hR w (by linarith)
    exact acrossDist_le_weyl ξ (LQGMetric.testCont (supBumpAt K R w)) d e he hcont
      (supInner hR w) hf0
  have hkt : ENNReal.ofReal (Real.exp (ξ * -K)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA : n * aroundDist e (supOuter hR w) ≤ ENNReal.ofReal (Real.exp (ξ * -K)) * M₁ := by
    calc n * aroundDist e (supOuter hR w) ≤
          n * (ENNReal.ofReal (Real.exp (ξ * -K)) * aroundDist d (supOuter hR w)) :=
          mul_le_mul' le_rfl haround
      _ = ENNReal.ofReal (Real.exp (ξ * -K)) * (n * aroundDist d (supOuter hR w)) := by ring
      _ ≤ ENNReal.ofReal (Real.exp (ξ * -K)) * M₁ := mul_le_mul' le_rfl h1
  have hC : M₂⁻¹ ≤ n * acrossDist e (supInner hR w) := h2.trans (mul_le_mul' le_rfl hacross)
  refine ⟨?_, ?_, ?_⟩
  · have hfin : n * aroundDist e (supOuter hR w) < ⊤ :=
      lt_of_le_of_lt hA (ENNReal.mul_lt_top hkt.lt_top hM₁.lt_top)
    exact (enn_mul_lt_top_iff hn0 hnt _).mp hfin
  · rw [← ENNReal.mul_le_mul_iff_right hn0 hnt]
    calc n * aroundDist e (supOuter hR w) ≤ ENNReal.ofReal (Real.exp (ξ * -K)) * M₁ := hA
      _ ≤ ENNReal.ofReal κ * M₂⁻¹ := hM
      _ ≤ ENNReal.ofReal κ * (n * acrossDist e (supInner hR w)) := mul_le_mul' le_rfl hC
      _ = n * (ENNReal.ofReal κ * acrossDist e (supInner hR w)) := by ring
  · have hpos : 0 < n * acrossDist e (supInner hR w) :=
      lt_of_lt_of_le (ENNReal.inv_pos.mpr hM₂) hC
    exact (ENNReal.mul_pos_iff.mp hpos).2

 

 
theorem isGFFPlusCont_addFun' {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : LQGMetric.IsWholePlaneGFF h P) (f : C(ℂ, ℝ)) :
    LQGMetric.IsGFFPlusCont (fun ω => LQGMetric.addFun (h ω) f) P := by
  refine ⟨(LQGMetric.measurable_addFun_left f).comp hh.measurable, fun _ => f,
    measurable_const, ?_⟩
  have hfun : (fun ω => LQGMetric.addFun (h ω) f - LQGMetric.ofCont f) = h := by
    funext ω
    simp only [LQGMetric.addFun, add_sub_cancel_right]
  rw [hfun]
  exact hh

 

theorem ae_supProxy_normPsi_iff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : Ω → DistC) (hg : LQGMetric.IsGFFPlusCont g P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (κ : ℝ) {R : ℝ} (hR : 0 < R) (w : ℂ) :
    ∀ᵐ ω ∂P, (SupProxy κ (D (LQGMetric.GM.normPsi (g ω))) hR w ↔
      SupProxy κ (D (g ω)) hR w) := by
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul P g hg ξ Q D hD
    (fun ω => -(g ω LQGMetric.GM.psiOne))] with ω hω
  exact supProxy_scale_iff κ (D (g ω)) (D (LQGMetric.GM.normPsi (g ω))) _
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
    (fun u v => hω (u, v)) hR w

 
theorem measurable_normAcrossAt' (ξ : Ioi (0 : ℝ)) (Q : ℝ) {D : DistC → LSCMetric}
    (hD : Measurable D) (A : EuclideanAnnulus) (z : ℂ) (r : Ioi (0 : ℝ)) :
    Measurable fun g => TwoScale.RatioMarginal.normAcrossAt ξ Q D g A z r := by
  unfold TwoScale.RatioMarginal.normAcrossAt
  exact (ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (LQGMetric.measurable_circleAvg_left _ _)).neg))).mul
    ((SupercriticalLQGUniqueness.measurable_acrossDist _).comp hD)

theorem measurable_normAroundAt' (ξ : Ioi (0 : ℝ)) (Q : ℝ) {D : DistC → LSCMetric}
    (hD : Measurable D) (A : EuclideanAnnulus) (z : ℂ) (r : Ioi (0 : ℝ)) :
    Measurable fun g => TwoScale.RatioMarginal.normAroundAt ξ Q D g A z r := by
  unfold TwoScale.RatioMarginal.normAroundAt
  exact (ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (LQGMetric.measurable_circleAvg_left _ _)).neg))).mul
    ((Toolkit.CountableBase.aroundBoundedAnnulus_borel _).comp hD)

 


theorem supProxy_marginal (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (κ : ℝ) (hκ : 0 < κ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ (R : ℝ) (hR : 0 < R) (w : ℂ),
        ENNReal.ofReal p₀ ≤ P {ω | SupProxy κ (D (h ω)) hR w} := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  obtain ⟨M₁, hM₁, hV₁⟩ := TwoScale.RatioMarginal.center_ratio_uniform ξ Q D hD shapeSupOuter (7 / 8)
    (by norm_num) (by norm_num)
  obtain ⟨M₂, hM₂, hV₂⟩ := TwoScale.RatioMarginal.center_ratio_uniform ξ Q D hD shapeSupInner (7 / 8)
    (by norm_num) (by norm_num)
  have hM₁0 : 0 < M₁ := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  set K : ℝ := Real.log (M₁ * M₂ / κ) / ξ with hKdef
  have hexpK : Real.exp ((ξ : ℝ) * -K) = κ / (M₁ * M₂) := by
    rw [hKdef, mul_neg, mul_div_cancel₀ _ hξ.ne', Real.exp_neg, Real.exp_log (by positivity),
      inv_div]
  set G : ℝ := LQGMetric.gradEnergy (supAnnBump K) with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    unfold LQGMetric.gradEnergy
    positivity
  refine ⟨(3 / 4) ^ 2 * Real.exp (-G), by positivity, ?_, ?_⟩
  · have : Real.exp (-G) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  intro Ω _ P _ h hh R hR w
  set r : Ioi (0 : ℝ) := ⟨R, hR⟩ with hrdef
  set φ : TestC := supBumpAt K R w with hφdef
  set f : C(ℂ, ℝ) := LQGMetric.testCont φ with hfdef
  have hGFF : LQGMetric.IsGFFPlusCont h P := LQGMetric.GM.detGFFPlusCont hh.1
  
  set G₁ : Set Ω := {ω | ENNReal.ofReal M₁⁻¹ ≤ TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) shapeSupOuter w r ∧
    TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) shapeSupOuter w r ≤ ENNReal.ofReal M₁} with hG₁def
  set G₂ : Set Ω := {ω | ENNReal.ofReal M₂⁻¹ ≤ TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) shapeSupInner w r ∧
    TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) shapeSupInner w r ≤ ENNReal.ofReal M₂} with hG₂def
  have hG₁ : ENNReal.ofReal (7 / 8) ≤ P G₁ := hV₁ P h hh w r
  have hG₂ : ENNReal.ofReal (7 / 8) ≤ P G₂ := hV₂ P h hh w r
  have hG₁m : MeasurableSet G₁ :=
    (measurableSet_le measurable_const
      ((measurable_normAcrossAt' ξ Q hD.measurable shapeSupOuter w r).comp
        hh.1.measurable)).inter
    (measurableSet_le ((measurable_normAroundAt' ξ Q hD.measurable shapeSupOuter w r).comp
      hh.1.measurable) measurable_const)
  have hG₂m : MeasurableSet G₂ :=
    (measurableSet_le measurable_const
      ((measurable_normAcrossAt' ξ Q hD.measurable shapeSupInner w r).comp
        hh.1.measurable)).inter
    (measurableSet_le ((measurable_normAroundAt' ξ Q hD.measurable shapeSupInner w r).comp
      hh.1.measurable) measurable_const)
  
  have hshift : ∀ᵐ ω ∂P, ω ∈ G₁ ∩ G₂ →
      SupProxy κ (D (LQGMetric.addFun (h ω) f)) hR w := by
    filter_upwards [hD.weyl P h hGFF, BiLipschitz.Barrier.ae_curves_continuous hD hQ P h hh] with ω hw hc hω
    have he : ∀ u v : ℂ, D (LQGMetric.addFun (h ω) f) (u, v) =
        weylScale ξ (LQGMetric.testCont (supBumpAt K R w)) (D (h ω)) (u, v) := fun u v =>
      (congrFun (hw f) (u, v)).symm
    set n : ℝ≥0∞ := ENNReal.ofReal ((R : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) R w))) with hndef
    have hn0 : n ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos hR _) (Real.exp_pos _))).ne'
    have h1 : n * aroundDist (D (h ω)) (supOuter hR w) ≤ ENNReal.ofReal M₁ := by
      have h1' := hω.1.2
      unfold TwoScale.RatioMarginal.normAroundAt at h1'
      rw [supOuter_eq r w] at h1'
      exact h1'
    have h2 : (ENNReal.ofReal M₂)⁻¹ ≤ n * acrossDist (D (h ω)) (supInner hR w) := by
      have h2' := hω.2.1
      unfold TwoScale.RatioMarginal.normAcrossAt at h2'
      rw [supInner_eq r w, ENNReal.ofReal_inv_of_pos hM₂0] at h2'
      exact h2'
    have hM : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -K)) * ENNReal.ofReal M₁ ≤
        ENNReal.ofReal κ * (ENNReal.ofReal M₂)⁻¹ := by
      rw [hexpK, ← ENNReal.ofReal_inv_of_pos hM₂0, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hκ.le]
      apply ENNReal.ofReal_le_ofReal
      apply le_of_eq
      field_simp
    exact supProxy_weyl ξ (D (h ω)) (D (LQGMetric.addFun (h ω) f)) hR w he hc.2.1 κ n
      (ENNReal.ofReal M₁) (ENNReal.ofReal M₂) hn0 ENNReal.ofReal_ne_top hM ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top h1 h2
  
  have hcomp : ∀ {S : Set Ω}, MeasurableSet S → ENNReal.ofReal (7 / 8) ≤ P S →
      P Sᶜ ≤ ENNReal.ofReal (1 / 8) := by
    intro S hS hPS
    rw [prob_compl_eq_one_sub hS]
    calc 1 - P S ≤ 1 - ENNReal.ofReal (7 / 8) := tsub_le_tsub_left hPS 1
      _ = ENNReal.ofReal (1 / 8) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
        norm_num
  have hUc : P (G₁ ∩ G₂)ᶜ ≤ ENNReal.ofReal (1 / 4) := by
    rw [compl_inter]
    calc P (G₁ᶜ ∪ G₂ᶜ) ≤ P G₁ᶜ + P G₂ᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) :=
          add_le_add (hcomp hG₁m hG₁) (hcomp hG₂m hG₂)
      _ = ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have hinter : ENNReal.ofReal (3 / 4) ≤ P (G₁ ∩ G₂) := by
    have hsum := measure_add_measure_compl (μ := P) (hG₁m.inter hG₂m)
    rw [measure_univ] at hsum
    have hP : P (G₁ ∩ G₂) = 1 - P (G₁ ∩ G₂)ᶜ :=
      ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hsum
    rw [hP]
    calc ENNReal.ofReal (3 / 4) = 1 - ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
          norm_num
      _ ≤ 1 - P (G₁ ∩ G₂)ᶜ := tsub_le_tsub_left hUc 1
  
  set E : Set DistC := {g | SupProxy κ (D (LQGMetric.GM.normPsi g)) hR w} with hEdef
  have hEm : MeasurableSet E := measurableSet_supProxy
    (hD.measurable.comp LQGMetric.GM.measurable_normPsi) κ hR w
  have hEinv : ∀ (g : DistC) (c : ℝ), LQGMetric.addConst g c ∈ E ↔ g ∈ E := by
    intro g c
    simp only [hEdef, mem_ofPred_eq, LQGMetric.GM.normPsi_addConst]
  obtain ⟨CT, hCT, hCTeq⟩ := LQGMetric.GM.exists_pair0_preimage hEm hEinv
  have hpre0 : P {ω | h ω ∈ E} = LQGMetric.lawPair0 h P CT := by
    rw [LQGMetric.lawPair0, Measure.map_apply (LQGMetric.measurable_pair0_comp hh.1) hCT]
    congr 1
    ext ω
    exact hCTeq (h ω)
  have hpreφ : P {ω | LQGMetric.addFun (h ω) f ∈ E} =
      LQGMetric.lawPair0 (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) P CT := by
    rw [LQGMetric.lawPair0, Measure.map_apply (LQGMetric.measurable_pair0_addFun hh.1 φ) hCT]
    congr 1
    ext ω
    exact hCTeq _
  have hae0 := ae_supProxy_normPsi_iff P h hGFF ξ Q D hD κ hR w
  have haeφ := ae_supProxy_normPsi_iff P (fun ω => LQGMetric.addFun (h ω) f)
    (isGFFPlusCont_addFun' hh.1 f) ξ Q D hD κ hR w
  have hEq0 : {ω | h ω ∈ E} =ᵐ[P] {ω | SupProxy κ (D (h ω)) hR w} := by
    filter_upwards [hae0] with ω hω
    exact propext hω
  have hEqφ : {ω | LQGMetric.addFun (h ω) f ∈ E} =ᵐ[P]
      {ω | SupProxy κ (D (LQGMetric.addFun (h ω) f)) hR w} := by
    filter_upwards [haeφ] with ω hω
    exact propext hω
  
  have hφprob : ENNReal.ofReal (3 / 4) ≤ P {ω | LQGMetric.addFun (h ω) f ∈ E} := by
    rw [measure_congr hEqφ]
    exact hinter.trans (measure_mono_ae (by
      filter_upwards [hshift] with ω hω hG
      exact hω hG))
  
  have hCS := TwoScale.S36.measureReal_lawPair0_addFun_le_sqrt hh.1 φ hCT
  have hGφ : LQGMetric.gradEnergy φ = G := gradEnergy_supBumpAt K hR w
  rw [hGφ] at hCS
  set a : ℝ := (LQGMetric.lawPair0 (fun ω => LQGMetric.addFun (h ω)
    (LQGMetric.testCont φ)) P).real CT with hadef
  set b : ℝ := (LQGMetric.lawPair0 h P).real CT with hbdef
  have ha : 3 / 4 ≤ a := by
    rw [hadef, measureReal_def, ← hpreφ]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hφprob
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hsq : a ^ 2 ≤ b * Real.exp G :=
    (Real.le_sqrt' (by linarith)).mp hCS
  have hb : (3 / 4) ^ 2 * Real.exp (-G) ≤ b := by
    have h34 : (3 / 4 : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
    have hexp : Real.exp (-G) * Real.exp G = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc (3 / 4) ^ 2 * Real.exp (-G) ≤ a ^ 2 * Real.exp (-G) :=
          mul_le_mul_of_nonneg_right h34 (Real.exp_pos _).le
      _ ≤ b * Real.exp G * Real.exp (-G) := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
      _ = b := by rw [mul_assoc, mul_comm (Real.exp G), hexp, mul_one]
  rw [← measure_congr hEq0, hpre0]
  have := TwoScale.S36.isProbabilityMeasure_lawPair0 hh.1
  have hfinal : LQGMetric.lawPair0 h P CT = ENNReal.ofReal b := by
    rw [hbdef, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hfinal]
  exact ENNReal.ofReal_le_ofReal hb


end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9
