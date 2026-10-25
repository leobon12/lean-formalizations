import SupercriticalLQGUniqueness.B2.Median.Removable
import SupercriticalLQGUniqueness.B2.Median.GoodLoops
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Good

 


















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Toolkit.CompactPathInfimum

 
def loopAnn (w : ℂ) (t : ℝ) (ht : 0 < t) : EuclideanAnnulus :=
  ⟨(w, (t, 2 * t)), ht, by linarith⟩

 
def crossIn (d : LSCMetric) (w : ℂ) (t : ℝ) : ℝ≥0∞ :=
  compactPathInf d (Uniqueness.Toolkit.AnnulusIteration.closedAnnulus w t (2 * t))
    (sphere w t) (sphere w (2 * t))

 
def LoopGood (C : ℝ) (d : LSCMetric) (w : ℂ) (t : ℝ) (ht : 0 < t) : Prop :=
  aroundDist d (loopAnn w t ht) ≤ ENNReal.ofReal C * crossIn d w t

theorem loopAnn_toSet (w : ℂ) (t : ℝ) (ht : 0 < t) :
    (loopAnn w t ht).toSet = {x | t < dist x w ∧ dist x w < 2 * t} := by
  ext x
  simp only [EuclideanAnnulus.toSet, loopAnn, EuclideanAnnulus.center,
    EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius, mem_diff, mem_ball,
    closure_ball _ ht.ne', mem_closedBall, not_le, mem_setOf_eq]
  tauto

theorem loopAnn_innerBoundary (w : ℂ) (t : ℝ) (ht : 0 < t) :
    (loopAnn w t ht).innerBoundary = sphere w t := rfl

theorem loopAnn_outerBoundary (w : ℂ) (t : ℝ) (ht : 0 < t) :
    (loopAnn w t ht).outerBoundary = sphere w (2 * t) := rfl

theorem isCompact_closedAnnulus' (w : ℂ) (u v : ℝ) :
    IsCompact (Uniqueness.Toolkit.AnnulusIteration.closedAnnulus w u v) := by
  have hb : Bornology.IsBounded (Uniqueness.Toolkit.AnnulusIteration.closedAnnulus w u v) :=
    (isBounded_closedBall (x := w) (r := v)).subset (fun x hx => by
      rw [mem_closedBall, dist_eq_norm]; exact hx.2)
  have hc : IsClosed (Uniqueness.Toolkit.AnnulusIteration.closedAnnulus w u v) :=
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
  exact Metric.isCompact_of_isClosed_isBounded hc hb

theorem measurableSet_loopGood (C : ℝ) (w : ℂ) (t : ℝ) (ht : 0 < t) :
    MeasurableSet {d : LSCMetric | LoopGood C d w t ht} :=
  measurableSet_le (Uniqueness.Toolkit.CountableBase.aroundBoundedAnnulus_borel _)
    (measurable_const.mul (compactPathInf_measurable (isCompact_closedAnnulus' w t (2 * t))
      (isCompact_sphere w t) (isCompact_sphere w (2 * t))))

 
theorem loopGood_iff_of_dist_scale {d e : LSCMetric} (k : ℝ≥0∞) (hk0 : k ≠ 0)
    (hkTop : k ≠ ∞) (hscale : ∀ x y : ℂ, e (x, y) = k * d (x, y)) (C : ℝ) (w : ℂ) (t : ℝ)
    (ht : 0 < t) : LoopGood C e w t ht ↔ LoopGood C d w t ht := by
  unfold LoopGood crossIn
  rw [Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale d e k hk0 hkTop hscale,
    compactPathInf_eq_mul_of_dist_scale d e k hk0 hkTop hscale, mul_left_comm]
  exact ENNReal.mul_le_mul_iff_right hk0 hkTop

 
theorem loopGood_iff_of_intExt_eq {d₁ d₂ : LSCMetric} {U : Set ℂ}
    (hI : ∀ x y, Uniqueness.TwoScale.S36.intExt d₁ U x y = Uniqueness.TwoScale.S36.intExt d₂ U x y)
    (C : ℝ) (w : ℂ) (t : ℝ) (ht : 0 < t)
    (hU : Uniqueness.Toolkit.AnnulusIteration.closedAnnulus w t (2 * t) ⊆ U) :
    LoopGood C d₁ w t ht ↔ LoopGood C d₂ w t ht := by
  have hA : (loopAnn w t ht).toSet ⊆ U := by
    intro x hx
    rw [loopAnn_toSet] at hx
    exact hU ⟨by rw [← dist_eq_norm]; exact hx.1.le, by rw [← dist_eq_norm]; exact hx.2.le⟩
  have ha := Uniqueness.TwoScale.S36.around_transfer hI hA
  have hc : crossIn d₁ w t = crossIn d₂ w t := by
    unfold crossIn
    rw [compactPathInf_eq_internalSetDist, compactPathInf_eq_internalSetDist]
    unfold LSCMetric.internalSetDist
    rw [Uniqueness.TwoScale.S36.internal_transfer hU hI]
  unfold LoopGood
  rw [ha, hc]

 
theorem loopGood_iff_of_translate {D E : LSCMetric} (z : ℂ)
    (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z)) (C : ℝ) (w : ℂ) (t : ℝ) (ht : 0 < t) :
    LoopGood C E w t ht ↔ LoopGood C D (w + z) t ht := by
  have hA : Uniqueness.Positivity.Witnesses.annulusTranslate (loopAnn w t ht) z =
      loopAnn (w + z) t ht := rfl
  have ha := Uniqueness.BiLipschitz.OneScale.aroundDist_translate D E (loopAnn w t ht) z hDE
  rw [hA] at ha
  have himg : ∀ (r : ℝ), (fun x : ℂ => x + z) '' sphere w r = sphere (w + z) r := by
    intro r
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_sphere] at hy ⊢
      rw [dist_add_right]; exact hy
    · intro hx
      refine ⟨x - z, ?_, by ring⟩
      rw [mem_sphere] at hx ⊢
      rw [← dist_add_right (x - z) w z, sub_add_cancel]; exact hx
  have himgA : (fun x : ℂ => x + z) '' Uniqueness.Toolkit.AnnulusIteration.closedAnnulus w t (2 * t)
      = Uniqueness.Toolkit.AnnulusIteration.closedAnnulus (w + z) t (2 * t) := by
    ext x
    simp only [Uniqueness.Toolkit.AnnulusIteration.closedAnnulus, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [add_sub_add_right_eq_sub] using hy
    · intro hx
      refine ⟨x - z, ?_, by ring⟩
      simpa only [show x - z - w = x - (w + z) by ring] using hx
  have hc : crossIn E w t = crossIn D (w + z) t := by
    unfold crossIn
    rw [compactPathInf_translate D E z hDE]
    have e1 := himgA
    have e2 := himg t
    have e3 := himg (2 * t)
    exact congr (congr (congrArg (compactPathInf D) e1) e2) e3
  unfold LoopGood
  rw [ha, hc]

 
theorem acrossDist_le_crossIn (d : LSCMetric) (w : ℂ) (t : ℝ) (ht : 0 < t) :
    acrossDist d (loopAnn w t ht) ≤ crossIn d w t := by
  unfold crossIn compactPathInf
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun _ => le_iInf fun ha => le_iInf fun hb => ?_
  calc acrossDist d (loopAnn w t ht) ≤ d (P a, P b) :=
        iInf₂_le_of_le (P a) ha (iInf₂_le (P b) hb)
    _ ≤ d.len P a b := LSCMetric.edist_le_len d P hP.1

 

theorem exists_loopGood_prob
    (ξ : Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (p : ℝ) (hp : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : ℂ) (t : ℝ) (ht : 0 < t),
      ENNReal.ofReal p ≤ P {ω | LoopGood C (D (h ω)) w t ht} := by
  let A₀ : EuclideanAnnulus := ⟨(0, (1, 2)), by norm_num, by norm_num⟩
  obtain ⟨C, hC, hbad⟩ := exists_around_across_ratio_bound_at_origin P ξ D c hweak h hh A₀
    (1 - p) (by linarith)
  refine ⟨C, hC, ?_⟩
  have hDm : Measurable D := hweak.1
  have hhm : Measurable h := hh.1.measurable
  
  have horigin : ∀ (t : ℝ) (ht : 0 < t),
      ENNReal.ofReal p ≤ P {ω | LoopGood C (D (h ω)) 0 t ht} := by
    intro t ht
    have hdil : A₀.dilate t ht = loopAnn 0 t ht := by
      apply Subtype.ext
      simp [A₀, EuclideanAnnulus.dilate, loopAnn, EuclideanAnnulus.center,
        EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius, mul_comm]
    have hb := hbad ⟨t, ht⟩
    simp only [hdil] at hb
    have hsub : {ω | LoopGood C (D (h ω)) 0 t ht}ᶜ ⊆
        {ω | ENNReal.ofReal C * acrossDist (D (h ω)) (loopAnn 0 t ht) <
          aroundDist (D (h ω)) (loopAnn 0 t ht)} := by
      intro ω hω
      simp only [mem_compl_iff, mem_setOf_eq, LoopGood, not_le] at hω ⊢
      exact lt_of_le_of_lt (mul_le_mul' le_rfl (acrossDist_le_crossIn _ 0 t ht)) hω
    have hmeas : MeasurableSet {ω | LoopGood C (D (h ω)) 0 t ht} :=
      (hDm.comp hhm) (measurableSet_loopGood C 0 t ht)
    have hcompl : P {ω | LoopGood C (D (h ω)) 0 t ht}ᶜ ≤ ENNReal.ofReal (1 - p) :=
      (measure_mono hsub).trans hb
    rw [prob_compl_eq_one_sub hmeas] at hcompl
    by_cases hp0 : p ≤ 0
    · rw [ENNReal.ofReal_of_nonpos hp0]; exact bot_le
    have hle : 1 - ENNReal.ofReal (1 - p) ≤ P {ω | LoopGood C (D (h ω)) 0 t ht} := by
      have := tsub_le_iff_left.mp hcompl
      exact tsub_le_iff_right.mpr this
    refine le_trans ?_ hle
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  
  intro w t ht
  have hcont : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.isGFFPlusCont_of_normalized
      (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh)
  obtain ⟨_, hlen, hloc, hweyl, htrans, hΛ, htight⟩ := hweak
  set κ : Ω → ℝ := fun ω => LQGMetric.circleAvg (h ω) 1 w with hκ
  set h' : Ω → LQGMetric.DistC := fun ω =>
    LQGMetric.addConst (translateDist w (h ω)) (-κ ω) with hh'def
  have hh' : IsNormalizedWholePlaneGFF h' P :=
    Uniqueness.Toolkit.AnnulusIteration.translated_normalized hh.1 w
  have hcont' : LQGMetric.IsGFFPlusCont h' P :=
    LQGMetric.GM.isGFFPlusCont_of_normalized
      (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh')
  have hback : ∀ ω, LQGMetric.addConst (h' ω) (κ ω) = translateDist w (h ω) := by
    intro ω
    simp only [hh'def, LQGMetric.GFFLaw.addConst_addConst, neg_add_cancel,
      LQGMetric.GFFLaw.addConst_zero']
  have hsc := ae_addConst_eq_mul_of_pfe P h' hcont' ξ D c
    ⟨hDm, hlen, hloc, hweyl, htrans, hΛ, htight⟩ κ
  have hequiv : ∀ᵐ ω ∂P, (LoopGood C (D (h ω)) w t ht ↔ LoopGood C (D (h' ω)) 0 t ht) := by
    filter_upwards [htrans P h hcont w, hsc] with ω hT hS
    have h1 := loopGood_iff_of_translate (D := D (h ω)) (E := D (translateDist w (h ω))) w
      (fun x y => hT x y) C 0 t ht
    rw [zero_add] at h1
    rw [← h1, ← hback ω]
    exact loopGood_iff_of_dist_scale _ (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top (fun x y => hS (x, y)) C 0 t ht
  have hS : MeasurableSet {g : LQGMetric.DistC | LoopGood C (D g) 0 t ht} :=
    hDm (measurableSet_loopGood C 0 t ht)
  have hlaw : P.map h' = P.map h := by
    rw [← LQGMetric.GM.normGFFLaw_eq
        (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh'),
      ← LQGMetric.GM.normGFFLaw_eq (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh)]
  have heq : P {ω | LoopGood C (D (h ω)) w t ht} = P {ω | LoopGood C (D (h ω)) 0 t ht} := by
    calc P {ω | LoopGood C (D (h ω)) w t ht} = P {ω | LoopGood C (D (h' ω)) 0 t ht} :=
          measure_congr (hequiv.mono fun ω hω => propext hω)
      _ = (P.map h') {g | LoopGood C (D g) 0 t ht} :=
          (Measure.map_apply hh'.1.measurable hS).symm
      _ = (P.map h) {g | LoopGood C (D g) 0 t ht} := by rw [hlaw]
      _ = P {ω | LoopGood C (D (h ω)) 0 t ht} := Measure.map_apply hhm hS
  rw [heq]
  exact horigin t ht

end SupercriticalLQGUniqueness.B2.Median
