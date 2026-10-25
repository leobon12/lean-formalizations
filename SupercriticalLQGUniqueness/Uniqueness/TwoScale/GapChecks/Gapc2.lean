import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import NV1Evidence
import LQGMetric.Metric.WeylScaling
import LQGMetric.Field.CircleAvgLaw
import LQGMetric.Field.Measurable
import LQGMetric.Papers.GM.S1.Subseq




 













set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

namespace SupercriticalLQGUniqueness

open LQGMetric (DistC IsWholePlaneGFF IsGFFPlusCont addFun addConst ofCont)

namespace Uniqueness.TwoScale.GapChecks

 


 

theorem lsc_eq_of_forall_basisInf {X : Type*} [TopologicalSpace X] {F G : X → ℝ≥0∞}
    (hF : LowerSemicontinuous F) (hG : LowerSemicontinuous G) {B : Set (Set X)}
    (hB : IsTopologicalBasis B) (h : ∀ b ∈ B, ⨅ p ∈ b, F p = ⨅ p ∈ b, G p) : F = G := by
  have key : ∀ {F G : X → ℝ≥0∞}, LowerSemicontinuous F →
      (∀ b ∈ B, ⨅ p ∈ b, F p = ⨅ p ∈ b, G p) → ∀ x, F x ≤ G x := by
    intro F G hF h x
    refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
    obtain ⟨b, hbB, hxb, hbsub⟩ :=
      hB.exists_subset_of_mem_open (show x ∈ F ⁻¹' Ioi t from ht) (hF.isOpen_preimage t)
    calc t ≤ ⨅ p ∈ b, F p := le_iInf₂ fun p hp => (hbsub hp).le
      _ = ⨅ p ∈ b, G p := h b hbB
      _ ≤ G x := iInf₂_le x hxb
  funext x
  exact le_antisymm (key hF h x) (key hG (fun b hb => (h b hb).symm) x)

 
theorem lowerSemicontinuous_ofReal_mul {X : Type*} [TopologicalSpace X] {F : X → ℝ≥0∞}
    (hF : LowerSemicontinuous F) (c : ℝ) :
    LowerSemicontinuous fun p => ENNReal.ofReal c * F p :=
  (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous hF
    fun _ _ hab => by simp only; gcongr

 

theorem scalarEq_iff_forall_basisInf {B : Set (Set (ℂ × ℂ))} (hB : IsTopologicalBasis B)
    (c : ℝ) (hc : 0 < c) (d d' : LSCMetric) :
    (∀ u v : ℂ, d.1 (u, v) = ENNReal.ofReal c * d'.1 (u, v)) ↔
      ∀ b ∈ B, ⨅ p ∈ b, d.1 p = ENNReal.ofReal c * ⨅ p ∈ b, d'.1 p := by
  have hc0 : ENNReal.ofReal c ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hc
  have hmul : ∀ b : Set (ℂ × ℂ), ENNReal.ofReal c * ⨅ p ∈ b, d'.1 p =
      ⨅ p ∈ b, ENNReal.ofReal c * d'.1 p := fun b => by
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    exact iInf_congr fun p => ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top
  constructor
  · intro h b _
    rw [hmul]
    exact iInf_congr fun p => iInf_congr fun _ => h p.1 p.2
  · intro h u v
    have hfun := lsc_eq_of_forall_basisInf d.2.2
      (lowerSemicontinuous_ofReal_mul d'.2.2 c) hB fun b hb => (h b hb).trans (hmul b)
    exact congrFun hfun (u, v)

 
theorem measurableSet_metric_scalarEq (c : ℝ) (hc : 0 < c)
    (D D' : DistC → LSCMetric) (hD : Measurable D) (hD' : Measurable D') :
    MeasurableSet {g : DistC | ∀ u v : ℂ,
      (D g).1 (u, v) = ENNReal.ofReal c * (D' g).1 (u, v)} := by
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis (ℂ × ℂ)
  have hset : {g : DistC | ∀ u v : ℂ, (D g).1 (u, v) = ENNReal.ofReal c * (D' g).1 (u, v)} =
      ⋂ b ∈ B, {g : DistC | ⨅ p ∈ b, (D g).1 p = ENNReal.ofReal c * ⨅ p ∈ b, (D' g).1 p} := by
    ext g
    simp only [mem_ofPred_eq, mem_iInter]
    exact scalarEq_iff_forall_basisInf hB c hc (D g) (D' g)
  rw [hset]
  refine MeasurableSet.biInter hBc fun b hb => ?_
  have hb : IsOpen b := hB.isOpen hb
  exact measurableSet_eq_fun ((LSCMetric.measurable_iInf_of_isOpen hb).comp hD)
    (((LSCMetric.measurable_iInf_of_isOpen hb).comp hD').const_mul _)

 
theorem measurableSet_diagonal_lscMetric :
    MeasurableSet {q : LSCMetric × LSCMetric | q.1 = q.2} := by
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis (ℂ × ℂ)
  have hset : {q : LSCMetric × LSCMetric | q.1 = q.2} =
      ⋂ b ∈ B, {q : LSCMetric × LSCMetric | ⨅ p ∈ b, q.1.1 p = ⨅ p ∈ b, q.2.1 p} := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · rintro h b -
      rw [h]
    · intro h
      exact Subtype.ext (lsc_eq_of_forall_basisInf q.1.2.2 q.2.2.2 hB h)
  rw [hset]
  refine MeasurableSet.biInter hBc fun b hb => ?_
  have hb : IsOpen b := hB.isOpen hb
  exact measurableSet_eq_fun ((LSCMetric.measurable_iInf_of_isOpen hb).comp measurable_fst)
    ((LSCMetric.measurable_iInf_of_isOpen hb).comp measurable_snd)


 


open LQGMetric.MetricGeometry in
 

theorem weylScale_le_mul_of_pointwise (ξ : ℝ) (f : C(ℂ, ℝ)) {k : ℝ} (hk : 0 < k)
    {d d' : LSCMetric} (h : ∀ p : ℂ × ℂ, d.1 p = ENNReal.ofReal k * d'.1 p) (p : ℂ × ℂ) :
    weylScale ξ f d p ≤ ENNReal.ofReal k * weylScale ξ f d' p := by
  have hk0 : ENNReal.ofReal k ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hk
  rw [mul_comm, ← ENNReal.div_le_iff hk0 ENNReal.ofReal_ne_top]
  show _ ≤ ⨅ (P : ℝ → ℂ) (L : ℝ) (_ : d'.IsCurve P 0 L)
      (_ : HasUnitSpeedOn (d'.pt ∘ P) (Icc 0 L)) (_ : P 0 = p.1) (_ : P L = p.2),
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hc => le_iInf fun hu =>
    le_iInf fun h0 => le_iInf fun h1 => ?_
  rw [ENNReal.div_le_iff hk0 ENNReal.ofReal_ne_top, mul_comm]
  have hL : 0 ≤ L := hc.1
  have hFG : ∀ s t, edist ((d.pt ∘ P) s) ((d.pt ∘ P) t) =
      ENNReal.ofReal k * edist ((d'.pt ∘ P) s) ((d'.pt ∘ P) t) := fun s t => h (P s, P t)
  have huQ : HasUnitSpeedOn ((d.pt ∘ P) ∘ fun t => t / k) (Icc 0 (k * L)) :=
    hasUnitSpeedOn_rescale hk hFG hu
  have hcurve : d.IsCurve (fun t => P (t / k)) 0 (k * L) :=
    ⟨mul_nonneg hk.le hL, continuousOn_of_hasUnitSpeedOn huQ⟩
  have h0' : (fun t => P (t / k)) 0 = p.1 := by simp only [zero_div, h0]
  have h1' : (fun t => P (t / k)) (k * L) = p.2 := by
    simp only [mul_div_cancel_left₀ L hk.ne', h1]
  have hle : weylScale ξ f d p ≤
      ∫⁻ s in Icc 0 (k * L), ENNReal.ofReal (Real.exp (ξ * f (P (s / k)))) :=
    iInf_le_of_le (fun t => P (t / k)) <| iInf_le_of_le (k * L) <| iInf_le_of_le hcurve <|
      iInf_le_of_le huQ <| iInf_le_of_le h0' <| iInf_le _ h1'
  refine hle.trans_eq ?_
  have himg : (fun x => k * x) '' Icc 0 L = Icc 0 (k * L) := by
    rw [image_mul_left_Icc hk.le hL, mul_zero]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f' := fun _ => k)
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul k).hasDerivWithinAt)
    (fun x _ y _ hxy => mul_left_cancel₀ hk.ne' hxy)]
  rw [setLIntegral_congr_fun measurableSet_Icc
    (g := fun x => ENNReal.ofReal |k| * ENNReal.ofReal (Real.exp (ξ * f (P x))))
    (fun x _ => by simp [hk.ne'])]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_of_pos hk]

 

theorem weylScale_eq_mul_of_pointwise
    (ξ : ℝ) (f : C(ℂ, ℝ)) (c : ℝ) (hc : 0 < c)
    {d d' : LSCMetric}
    (hdd' : ∀ p : ℂ × ℂ, d.1 p = ENNReal.ofReal c * d'.1 p) :
    ∀ p : ℂ × ℂ,
      weylScale ξ f d p = ENNReal.ofReal c * weylScale ξ f d' p := by
  intro p
  refine le_antisymm (weylScale_le_mul_of_pointwise ξ f hc hdd' p) ?_
  have h2 : weylScale ξ f d' p ≤ ENNReal.ofReal c⁻¹ * weylScale ξ f d p := by
    refine weylScale_le_mul_of_pointwise ξ f (inv_pos.2 hc) (fun q => ?_) p
    rw [hdd' q, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hc).le, inv_mul_cancel₀ hc.ne',
      ENNReal.ofReal_one, one_mul]
  calc ENNReal.ofReal c * weylScale ξ f d' p
      ≤ ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * weylScale ξ f d p) := by gcongr
    _ = weylScale ξ f d p := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
          one_mul]


 

theorem normalizedGFF_ae_metric_scalarEq
    (c : ℝ) (hc : 0 < c) (D D' : DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D')
    {Ω₀ Ω : Type} [MeasurableSpace Ω₀] [MeasurableSpace Ω]
    {P₀ : Measure Ω₀} {P : Measure Ω}
    {H₀ : Ω₀ → DistC} {k : Ω → DistC}
    (hH₀ : IsNormalizedWholePlaneGFF H₀ P₀)
    (hk : IsNormalizedWholePlaneGFF k P)
    (hEq₀ : ∀ᵐ ω ∂P₀, ∀ u v : ℂ,
      (D (H₀ ω)).1 (u, v) = ENNReal.ofReal c * (D' (H₀ ω)).1 (u, v)) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (k ω)).1 (u, v) = ENNReal.ofReal c * (D' (k ω)).1 (u, v) := by
  have hE := measurableSet_metric_scalarEq c hc D D' hD hD'
  have hlaw : P.map k = P₀.map H₀ :=
    LQGMetric.CircleAvg.map_eq_of_isNormalizedWPGFF
      (isNormalizedWholePlaneGFF_iff_old.mp hk) (isNormalizedWholePlaneGFF_iff_old.mp hH₀)
  have h1 : ∀ᵐ g ∂(P₀.map H₀), g ∈ {g : DistC | ∀ u v : ℂ,
      (D g).1 (u, v) = ENNReal.ofReal c * (D' g).1 (u, v)} :=
    (ae_map_iff hH₀.1.measurable.aemeasurable hE).2 hEq₀
  rw [← hlaw] at h1
  exact ae_of_ae_map hk.1.measurable.aemeasurable h1

 

theorem ofCont_add_const_apply (F : C(ℂ, ℝ)) (a : ℝ) (φ : LQGMetric.TestC) :
    ofCont (F + ContinuousMap.const ℂ a) φ = ofCont F φ + (∫ x, φ x) * a := by
  have hφ : Integrable (fun x => φ x) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hφF : Integrable (fun x => φ x * F x) :=
    (φ.continuous.mul F.continuous).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.mul_right)
  rw [LQGMetric.ofCont_apply, LQGMetric.ofCont_apply]
  simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, mul_add]
  rw [integral_add hφF (hφ.mul_const a), integral_mul_const]

theorem exists_normalized_decomposition
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusCont h P) :
    ∃ (k : Ω → DistC) (F' : Ω → C(ℂ, ℝ)),
      IsNormalizedWholePlaneGFF k P ∧ IsGFFPlusCont k P ∧ Measurable F' ∧
        ∀ ω, h ω = addFun (k ω) (F' ω) := by
  obtain ⟨-, F, hF, hg⟩ := hh
  let g : Ω → DistC := fun ω => h ω - ofCont (F ω)
  let a : Ω → ℝ := fun ω => LQGMetric.circleAvg (g ω) 1 0
  have ha : Measurable a := (LQGMetric.measurable_circleAvg_left 1 0).comp hg.measurable
  let k : Ω → DistC := fun ω => addConst (g ω) (-(a ω))
  have hk : IsWholePlaneGFF k P := hg.addConst ha.neg
  refine ⟨k, fun ω => F ω + ContinuousMap.const ℂ (a ω), ?_, ?_, ?_, ?_⟩
  · refine isNormalizedWholePlaneGFF_iff_old.mpr ⟨hk, ?_⟩
    filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero hg] with ω hω
    show LQGMetric.circleAvg (addConst (g ω) (-(a ω))) 1 0 = 0
    rw [hω (-(a ω))]
    exact add_neg_cancel _
  · exact LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hk
  · rw [ContinuousMap.measurable_iff_eval]
    intro x
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    exact ((ContinuousMap.measurable_eval x).comp hF).add ha
  · intro ω
    refine DFunLike.ext _ _ fun φ => ?_
    show h ω φ = (addConst (g ω) (-(a ω)) + ofCont (F ω + ContinuousMap.const ℂ (a ω))) φ
    rw [ContinuousLinearMap.add_apply, LQGMetric.GFFInv.addConst_apply,
      ofCont_add_const_apply]
    show h ω φ = (h ω - ofCont (F ω)) φ + (∫ x, φ x) * -(a ω) +
      (ofCont (F ω) φ + (∫ x, φ x) * a ω)
    rw [ContinuousLinearMap.sub_apply]
    ring

 

 


theorem rootExtension_of_reference
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hR54 : ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (H₀ : Ω₀ → DistC) (c : ℝ),
      IsNormalizedWholePlaneGFF H₀ P₀ ∧ 0 < c ∧
      ∀ᵐ ω ∂P₀, ∀ u v : ℂ,
        (D (H₀ ω)).1 (u, v) = ENNReal.ofReal c * (D' (H₀ ω)).1 (u, v)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) := by
  obtain ⟨Ω₀, mΩ₀, P₀, H₀, c, hH₀, hc, hEq₀⟩ := hR54
  refine ⟨c, hc, fun {Ω} _ P _ h hh => ?_⟩
  obtain ⟨k, F', hkn, hkc, -, hrep⟩ := exists_normalized_decomposition hh
  have hE₀ := normalizedGFF_ae_metric_scalarEq c hc D D' hD.1 hD'.1 hH₀ hkn hEq₀
  have hW := hD.2.2.2.1 P k hkc
  have hW' := hD'.2.2.2.1 P k hkc
  filter_upwards [hE₀, hW, hW'] with ω h0 h1 h2 u v
  rw [hrep ω, ← h1 (F' ω), ← h2 (F' ω)]
  exact weylScale_eq_mul_of_pointwise (ξ : ℝ) (F' ω) c hc (fun p => h0 p.1 p.2) (u, v)

 


theorem rootExtension_of_forall_normalized
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hR54 : ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
      (H₀ : Ω₀ → DistC), IsNormalizedWholePlaneGFF H₀ P₀ →
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂P₀, ∀ u v : ℂ,
        (D (H₀ ω)).1 (u, v) = ENNReal.ofReal c * (D' (H₀ ω)).1 (u, v)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) := by
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, H₀, hH₀⟩ := exists_normalizedGFF
  obtain ⟨c, hc, hEq₀⟩ := hR54 P₀ H₀ hH₀
  exact rootExtension_of_reference ξ Q D D' hD hD' ⟨Ω₀, mΩ₀, P₀, H₀, c, hH₀, hc, hEq₀⟩

 


example
    (hR54 : ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, ∀ D D' : DistC → LSCMetric,
      IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (H₀ : Ω₀ → DistC) (c : ℝ),
        IsNormalizedWholePlaneGFF H₀ P₀ ∧ 0 < c ∧
        ∀ᵐ ω ∂P₀, ∀ u v : ℂ,
          (D (H₀ ω)).1 (u, v) = ENNReal.ofReal c * (D' (H₀ ω)).1 (u, v)) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, ∀ D D' : DistC → LSCMetric,
      IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ u v : ℂ,
            (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) :=
  fun ξ Q D D' hD hD' =>
    rootExtension_of_reference ξ Q D D' hD hD'
      (hR54 ξ Q D D' hD hD')

end Uniqueness.TwoScale.GapChecks

end SupercriticalLQGUniqueness

