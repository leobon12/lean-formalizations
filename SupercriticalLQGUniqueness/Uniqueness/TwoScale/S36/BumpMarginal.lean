import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.BumpDefs




 



















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC TestC)

 
def shapeIn : EuclideanAnnulus := ⟨(0, (1, 2)), by norm_num, by norm_num⟩

def shapeSmall : EuclideanAnnulus := ⟨(0, (11 / 5, 14 / 5)), by norm_num, by norm_num⟩

theorem annIn_eq (s : Ioi (0 : ℝ)) (x : ℂ) :
    Positivity.Witnesses.annulusTranslate (shapeIn.dilate s s.2) x = annIn s.2 x := by
  apply Subtype.ext
  change ((s : ℝ) • (0 : ℂ) + x, (s : ℝ) * 1, (s : ℝ) * 2) = (x, ((s : ℝ), 2 * (s : ℝ)))
  simp only [smul_zero, zero_add, mul_one, mul_comm]

theorem annSmall_eq (s : Ioi (0 : ℝ)) (x : ℂ) :
    Positivity.Witnesses.annulusTranslate (shapeSmall.dilate s s.2) x = annSmall s.2 x := by
  apply Subtype.ext
  change ((s : ℝ) • (0 : ℂ) + x, (s : ℝ) * (11 / 5), (s : ℝ) * (14 / 5)) =
    (x, (11 * (s : ℝ) / 5, 14 * (s : ℝ) / 5))
  simp only [smul_zero, zero_add, Prod.mk.injEq, true_and]
  constructor <;> ring

theorem measurable_ratioEv (D : DistC → LSCMetric) (hD : Measurable D) {s : ℝ} (hs : 0 < s)
    (x : ℂ) : MeasurableSet {g : DistC | RatioEv (D g) hs x} := by
  have ha : Measurable fun g => aroundDist (D g) (annOut hs x) :=
    (measurable_aroundDist_fixed _).comp hD
  have hc : Measurable fun g => acrossDist (D g) (annIn hs x) :=
    (SupercriticalLQGUniqueness.measurable_acrossDist _).comp hD
  have h2 : Measurable fun g => 2 * aroundDist (D g) (annOut hs x) := measurable_const.mul ha
  have hset : {g : DistC | RatioEv (D g) hs x} =
      ({g | aroundDist (D g) (annOut hs x) < ⊤} ∩
        {g | 2 * aroundDist (D g) (annOut hs x) ≤ acrossDist (D g) (annIn hs x)}) ∩
        {g | 0 < acrossDist (D g) (annIn hs x)} := by
    ext g
    simp only [RatioEv, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [hset]
  exact ((measurableSet_lt ha measurable_const).inter (measurableSet_le h2 hc)).inter
    (measurableSet_lt measurable_const hc)

theorem testCont_bumpAt_apply (K s : ℝ) (x y : ℂ) :
    LQGMetric.testCont (bumpAt K s x) y = bumpAt K s x y := rfl

 
theorem ratioEv_weyl (ξ : ℝ) (d e : LSCMetric) {K s : ℝ} (hs : 0 < s) (x : ℂ)
    (he : ∀ u v : ℂ, e (u, v) = weylScale ξ (LQGMetric.testCont (bumpAt K s x)) d (u, v))
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), d.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (n M₁ M₂ : ℝ≥0∞) (hn0 : n ≠ 0) (hnt : n ≠ ⊤)
    (hM : 2 * ENNReal.ofReal (Real.exp (ξ * -K)) * M₁ ≤ M₂⁻¹) (hM₁ : M₁ ≠ ⊤)
    (h1 : n * aroundDist d (annSmall hs x) ≤ M₁) (h2 : M₂⁻¹ ≤ n * acrossDist d (annIn hs x))
    (hM₂ : M₂ ≠ ⊤) :
    RatioEv e hs x := by
  have haround : aroundDist e (annOut hs x) ≤
      ENNReal.ofReal (Real.exp (ξ * -K)) * aroundDist d (annSmall hs x) := by
    have hfA : ∀ y ∈ (annSmall hs x).toSet, LQGMetric.testCont (bumpAt K s x) y = -K := by
      intro y hy
      have hy' : y ∈ Metric.ball x (14 * s / 5) ∧ y ∉ closure (Metric.ball x (11 * s / 5)) := hy
      rw [closure_ball x (by positivity), Metric.mem_ball, Metric.mem_closedBall,
        not_le] at hy'
      rw [testCont_bumpAt_apply]
      exact bumpAt_eq_neg K hs x hy'.2.le hy'.1.le
    exact (around_le_small e hs x).trans
      (aroundDist_le_weyl ξ (LQGMetric.testCont (bumpAt K s x)) d e he (annSmall hs x) (-K) hfA)
  have hacross : acrossDist d (annIn hs x) ≤ acrossDist e (annIn hs x) := by
    have hf0 : ∀ y : ℂ, (annIn hs x).innerRadius ≤ dist y (annIn hs x).center →
        dist y (annIn hs x).center ≤ (annIn hs x).outerRadius →
        LQGMetric.testCont (bumpAt K s x) y = 0 := by
      intro y _ hy2
      rw [testCont_bumpAt_apply]
      exact bumpAt_eq_zero K hs x hy2
    exact acrossDist_le_weyl ξ (LQGMetric.testCont (bumpAt K s x)) d e he hcont (annIn hs x) hf0
  have hkt : ENNReal.ofReal (Real.exp (ξ * -K)) ≠ ⊤ := ENNReal.ofReal_ne_top
  
  have hA : n * aroundDist e (annOut hs x) ≤ ENNReal.ofReal (Real.exp (ξ * -K)) * M₁ := by
    calc n * aroundDist e (annOut hs x) ≤
          n * (ENNReal.ofReal (Real.exp (ξ * -K)) * aroundDist d (annSmall hs x)) :=
          mul_le_mul' le_rfl haround
      _ = ENNReal.ofReal (Real.exp (ξ * -K)) * (n * aroundDist d (annSmall hs x)) := by ring
      _ ≤ ENNReal.ofReal (Real.exp (ξ * -K)) * M₁ := mul_le_mul' le_rfl h1
  have hC : M₂⁻¹ ≤ n * acrossDist e (annIn hs x) := h2.trans (mul_le_mul' le_rfl hacross)
  refine ⟨?_, ?_, ?_⟩
  · 
    have hfin : n * aroundDist e (annOut hs x) < ⊤ :=
      lt_of_le_of_lt hA (ENNReal.mul_lt_top hkt.lt_top hM₁.lt_top)
    exact ((mul_lt_top_iff_of_ne hn0 hnt _).mp hfin)
  · rw [← scale_le_iff hn0 hnt]
    calc n * (2 * aroundDist e (annOut hs x)) = 2 * (n * aroundDist e (annOut hs x)) := by ring
      _ ≤ 2 * (ENNReal.ofReal (Real.exp (ξ * -K)) * M₁) := mul_le_mul' le_rfl hA
      _ = 2 * ENNReal.ofReal (Real.exp (ξ * -K)) * M₁ := by ring
      _ ≤ M₂⁻¹ := hM
      _ ≤ n * acrossDist e (annIn hs x) := hC
  · have hpos : 0 < n * acrossDist e (annIn hs x) :=
      lt_of_lt_of_le (ENNReal.inv_pos.mpr hM₂) hC
    exact (ENNReal.mul_pos_iff.mp hpos).2

 

 
theorem isGFFPlusCont_addFun {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : LQGMetric.IsWholePlaneGFF h P) (f : C(ℂ, ℝ)) :
    LQGMetric.IsGFFPlusCont (fun ω => LQGMetric.addFun (h ω) f) P := by
  refine ⟨(LQGMetric.measurable_addFun_left f).comp hh.measurable, fun _ => f,
    measurable_const, ?_⟩
  have hfun : (fun ω => LQGMetric.addFun (h ω) f - LQGMetric.ofCont f) = h := by
    funext ω
    simp only [LQGMetric.addFun, add_sub_cancel_right]
  rw [hfun]
  exact hh

 

theorem ae_ratioEv_normPsi_iff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : Ω → DistC) (hg : LQGMetric.IsGFFPlusCont g P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    {s : ℝ} (hs : 0 < s) (x : ℂ) :
    ∀ᵐ ω ∂P, (RatioEv (D (LQGMetric.GM.normPsi (g ω))) hs x ↔ RatioEv (D (g ω)) hs x) := by
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul P g hg ξ Q D hD
    (fun ω => -(g ω LQGMetric.GM.psiOne))] with ω hω
  exact ratioEv_scale_iff (D (g ω)) (D (LQGMetric.GM.normPsi (g ω))) _
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
    (fun u v => hω (u, v)) hs x

 

theorem bump_marginal (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ (s : ℝ) (hs : 0 < s) (x : ℂ),
        ENNReal.ofReal p₀ ≤ P {ω | RatioEv (D (h ω)) hs x} := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  obtain ⟨M₁, hM₁, hV₁⟩ := TwoScale.RatioMarginal.center_ratio_uniform ξ Q D hD shapeSmall (7 / 8)
    (by norm_num) (by norm_num)
  obtain ⟨M₂, hM₂, hV₂⟩ := TwoScale.RatioMarginal.center_ratio_uniform ξ Q D hD shapeIn (7 / 8)
    (by norm_num) (by norm_num)
  have hM₁0 : 0 < M₁ := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  set K : ℝ := Real.log (2 * M₁ * M₂) / ξ with hKdef
  have hexpK : Real.exp ((ξ : ℝ) * -K) = (2 * M₁ * M₂)⁻¹ := by
    rw [hKdef, mul_neg, mul_div_cancel₀ _ hξ.ne', Real.exp_neg, Real.exp_log (by positivity)]
  set G : ℝ := LQGMetric.gradEnergy (annBump K) with hGdef
  refine ⟨(3 / 4) ^ 2 * Real.exp (-G), by positivity, ?_⟩
  intro Ω _ P _ h hh s hs x
  set r : Ioi (0 : ℝ) := ⟨s, hs⟩ with hrdef
  set φ : TestC := bumpAt K s x with hφdef
  set f : C(ℂ, ℝ) := LQGMetric.testCont φ with hfdef
  have hGFF : LQGMetric.IsGFFPlusCont h P := LQGMetric.GM.detGFFPlusCont hh.1
  
  set G₁ : Set Ω := {ω | ENNReal.ofReal M₁⁻¹ ≤ TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) shapeSmall x r ∧
    TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) shapeSmall x r ≤ ENNReal.ofReal M₁} with hG₁def
  set G₂ : Set Ω := {ω | ENNReal.ofReal M₂⁻¹ ≤ TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) shapeIn x r ∧
    TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) shapeIn x r ≤ ENNReal.ofReal M₂} with hG₂def
  have hG₁ : ENNReal.ofReal (7 / 8) ≤ P G₁ := hV₁ P h hh x r
  have hG₂ : ENNReal.ofReal (7 / 8) ≤ P G₂ := hV₂ P h hh x r
  have hG₁m : MeasurableSet G₁ :=
    (measurableSet_le measurable_const
      ((measurable_normAcrossAt ξ Q hD.measurable shapeSmall x r).comp hh.1.measurable)).inter
    (measurableSet_le ((measurable_normAroundAt ξ Q hD.measurable shapeSmall x r).comp
      hh.1.measurable) measurable_const)
  have hG₂m : MeasurableSet G₂ :=
    (measurableSet_le measurable_const
      ((measurable_normAcrossAt ξ Q hD.measurable shapeIn x r).comp hh.1.measurable)).inter
    (measurableSet_le ((measurable_normAroundAt ξ Q hD.measurable shapeIn x r).comp
      hh.1.measurable) measurable_const)
  
  have hshift : ∀ᵐ ω ∂P, ω ∈ G₁ ∩ G₂ → RatioEv (D (LQGMetric.addFun (h ω) f)) hs x := by
    filter_upwards [hD.weyl P h hGFF, BiLipschitz.Barrier.ae_curves_continuous hD hQ P h hh] with ω hw hc hω
    have he : ∀ u v : ℂ, D (LQGMetric.addFun (h ω) f) (u, v) =
        weylScale ξ (LQGMetric.testCont (bumpAt K s x)) (D (h ω)) (u, v) := fun u v =>
      (congrFun (hw f) (u, v)).symm
    set n : ℝ≥0∞ := ENNReal.ofReal ((s : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) s x))) with hndef
    have hn0 : n ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos hs _) (Real.exp_pos _))).ne'
    have h1 : n * aroundDist (D (h ω)) (annSmall hs x) ≤ ENNReal.ofReal M₁ := by
      have h1' := hω.1.2
      unfold TwoScale.RatioMarginal.normAroundAt at h1'
      rw [annSmall_eq r x] at h1'
      exact h1'
    have h2 : (ENNReal.ofReal M₂)⁻¹ ≤ n * acrossDist (D (h ω)) (annIn hs x) := by
      have h2' := hω.2.1
      unfold TwoScale.RatioMarginal.normAcrossAt at h2'
      rw [annIn_eq r x, ENNReal.ofReal_inv_of_pos hM₂0] at h2'
      exact h2'
    have hM : 2 * ENNReal.ofReal (Real.exp ((ξ : ℝ) * -K)) * ENNReal.ofReal M₁ ≤
        (ENNReal.ofReal M₂)⁻¹ := by
      rw [hexpK, ← ENNReal.ofReal_inv_of_pos hM₂0,
        show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      apply le_of_eq
      field_simp
    exact ratioEv_weyl ξ (D (h ω)) (D (LQGMetric.addFun (h ω) f)) hs x he hc.2.1 n
      (ENNReal.ofReal M₁) (ENNReal.ofReal M₂) hn0 ENNReal.ofReal_ne_top hM ENNReal.ofReal_ne_top
      h1 h2 ENNReal.ofReal_ne_top
  
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
  
  set E : Set DistC := {g | RatioEv (D (LQGMetric.GM.normPsi g)) hs x} with hEdef
  have hEm : MeasurableSet E := measurable_ratioEv (fun g => D (LQGMetric.GM.normPsi g))
    (hD.measurable.comp LQGMetric.GM.measurable_normPsi) hs x
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
  have hae0 := ae_ratioEv_normPsi_iff P h hGFF ξ Q D hD hs x
  have haeφ := ae_ratioEv_normPsi_iff P (fun ω => LQGMetric.addFun (h ω) f)
    (isGFFPlusCont_addFun hh.1 f) ξ Q D hD hs x
  have hEq0 : {ω | h ω ∈ E} =ᵐ[P] {ω | RatioEv (D (h ω)) hs x} := by
    filter_upwards [hae0] with ω hω
    exact propext hω
  have hEqφ : {ω | LQGMetric.addFun (h ω) f ∈ E} =ᵐ[P]
      {ω | RatioEv (D (LQGMetric.addFun (h ω) f)) hs x} := by
    filter_upwards [haeφ] with ω hω
    exact propext hω
  
  have hφprob : ENNReal.ofReal (3 / 4) ≤ P {ω | LQGMetric.addFun (h ω) f ∈ E} := by
    rw [measure_congr hEqφ]
    exact hinter.trans (measure_mono_ae (by
      filter_upwards [hshift] with ω hω hG
      exact hω hG))
  
  have hCS := measureReal_lawPair0_addFun_le_sqrt hh.1 φ hCT
  have hGφ : LQGMetric.gradEnergy φ = G := gradEnergy_bumpAt K hs x
  rw [hGφ] at hCS
  set a : ℝ := (LQGMetric.lawPair0 (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) P).real CT
    with hadef
  set b : ℝ := (LQGMetric.lawPair0 h P).real CT with hbdef
  have ha : 3 / 4 ≤ a := by
    rw [hadef, measureReal_def, ← hpreφ]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hφprob
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hsq : a ^ 2 ≤ b * Real.exp G :=
    (Real.le_sqrt' (by linarith)).mp hCS
  have hb : (3 / 4) ^ 2 * Real.exp (-G) ≤ b := by
    have h34 : (3 / 4 : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
    have hexp : Real.exp (-G) * Real.exp G = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc (3 / 4) ^ 2 * Real.exp (-G) ≤ a ^ 2 * Real.exp (-G) :=
          mul_le_mul_of_nonneg_right h34 (Real.exp_pos _).le
      _ ≤ b * Real.exp G * Real.exp (-G) := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
      _ = b := by rw [mul_assoc, mul_comm (Real.exp G), hexp, mul_one]
  rw [← measure_congr hEq0, hpre0]
  have := isProbabilityMeasure_lawPair0 hh.1
  have hfinal : LQGMetric.lawPair0 h P CT = ENNReal.ofReal b := by
    rw [hbdef, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hfinal]
  exact ENNReal.ofReal_le_ofReal hb

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
