import SupercriticalLQGUniqueness.B2.Median.HeightTranslate
import SupercriticalLQGUniqueness.B2.Median.SurgeryPred
import SupercriticalLQGUniqueness.B2.Median.MedianTransfer
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import LQGMetric.Papers.GM.S1.FieldAux

 













set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Toolkit.CompactPathInfimum

 
abbrev RectTriple := (ℚ × ℚ × ℚ × ℚ) × (ℚ × ℚ × ℚ × ℚ) × (ℚ × ℚ × ℚ × ℚ)

theorem ratRect_translate (u₀ : ℝ) (q : ℚ × ℚ × ℚ × ℚ) :
    (fun w : ℂ => w + (⟨0, u₀⟩ : ℂ)) '' ratRect u₀ q = ratRect 0 q := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  · intro hw
    refine ⟨w - ⟨0, u₀⟩, ?_, by ring⟩
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp at h1 h2 h3 h4 ⊢ <;> linarith

theorem measurableSet_continuousAt_upperPathInf {V A B : Set ℂ} (hV : IsCompact V)
    (hA : IsCompact A) (hB : IsCompact B) :
    MeasurableSet {p : LSCMetric × ℝ | ContinuousAt (upperPathInf p.1 V A B) p.2} := by
  have heq : {p : LSCMetric × ℝ | ContinuousAt (upperPathInf p.1 V A B) p.2} =
      {p : LSCMetric × ℝ | ¬ upperLeftEnvelope p.1 V A B p.2 <
        upperRightEnvelope p.1 V A B p.2} := by
    ext p
    simpa only [Set.mem_ofPred_eq, not_not] using
      (upperEnvelope_jump_iff_not_continuousAt p.1 V A B p.2).not.symm
  rw [heq]
  exact (measurableSet_upperEnvelope_jump hV hA hB).compl

theorem measurableSet_continuousAt_lowerPathInf {V A B : Set ℂ} (hV : IsCompact V)
    (hA : IsCompact A) (hB : IsCompact B) :
    MeasurableSet {p : LSCMetric × ℝ | ContinuousAt (lowerPathInf p.1 V A B) p.2} := by
  have heq : {p : LSCMetric × ℝ | ContinuousAt (lowerPathInf p.1 V A B) p.2} =
      {p : LSCMetric × ℝ | ¬ lowerRightEnvelope p.1 V A B p.2 <
        lowerLeftEnvelope p.1 V A B p.2} := by
    ext p
    simpa only [Set.mem_ofPred_eq, not_not] using
      (lowerEnvelope_jump_iff_not_continuousAt p.1 V A B p.2).not.symm
  rw [heq]
  exact (measurableSet_lt (measurable_lowerRightEnvelope hV hA hB)
    (measurable_lowerLeftEnvelope hV hA hB)).compl

 
theorem measurableSet_sideRemovable (u₀ : ℝ) :
    MeasurableSet {d : LSCMetric | SideRemovable d u₀} := by
  have hset : {d : LSCMetric | SideRemovable d u₀} = ⋂ τ : RectTriple,
      ({d : LSCMetric | ContinuousAt (upperPathInf d (ratRect u₀ τ.1) (ratRect u₀ τ.2.1)
          (ratRect u₀ τ.2.2)) 0} ∩
        {d : LSCMetric | ContinuousAt (lowerPathInf d (ratRect u₀ τ.1) (ratRect u₀ τ.2.1)
          (ratRect u₀ τ.2.2)) 1}) := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, SideRemovable]
    exact ⟨fun h τ => h τ.1 τ.2.1 τ.2.2, fun h V E F => h (V, E, F)⟩
  rw [hset]
  refine MeasurableSet.iInter fun τ => MeasurableSet.inter ?_ ?_
  · exact measurable_prodMk_right (measurableSet_continuousAt_upperPathInf
      (isCompact_ratRect u₀ τ.1) (isCompact_ratRect u₀ τ.2.1) (isCompact_ratRect u₀ τ.2.2))
  · exact measurable_prodMk_right (measurableSet_continuousAt_lowerPathInf
      (isCompact_ratRect u₀ τ.1) (isCompact_ratRect u₀ τ.2.1) (isCompact_ratRect u₀ τ.2.2))

 
theorem sideRemovable_of_dist_scale {d e : LSCMetric} (k : ℝ≥0∞) (hk0 : k ≠ 0)
    (hkTop : k ≠ ∞) (hscale : ∀ x y : ℂ, e (x, y) = k * d (x, y)) (u₀ : ℝ)
    (hd : SideRemovable e u₀) : SideRemovable d u₀ := by
  intro V E F
  have hup : upperPathInf e (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F) =
      fun s => k * upperPathInf d (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F) s := by
    funext s
    exact compactPathInf_eq_mul_of_dist_scale d e k hk0 hkTop hscale _ _ _
  have hlo : lowerPathInf e (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F) =
      fun s => k * lowerPathInf d (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F) s := by
    funext s
    exact compactPathInf_eq_mul_of_dist_scale d e k hk0 hkTop hscale _ _ _
  obtain ⟨h1, h2⟩ := hd V E F
  rw [hup] at h1
  rw [hlo] at h2
  have hinv : Continuous fun x : ℝ≥0∞ => k⁻¹ * x :=
    ENNReal.continuous_const_mul (ENNReal.inv_ne_top.mpr hk0)
  constructor
  · have := hinv.continuousAt.comp h1
    simpa only [Function.comp_def, ENNReal.inv_mul_cancel_left hk0 hkTop] using this
  · have := hinv.continuousAt.comp h2
    simpa only [Function.comp_def, ENNReal.inv_mul_cancel_left hk0 hkTop] using this

 


theorem ae_addConst_eq_mul_of_pfe {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    (ξ : Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (κ : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ,
      D (LQGMetric.addConst (h ω) (κ ω)) q =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * κ ω)) * D (h ω) q := by
  obtain ⟨_, hlen, _, hweyl, _, _, _⟩ := hweak
  filter_upwards [hweyl P h hh, hlen P h hh] with ω hw hl
  intro q
  have hqw := congrFun (hw (ContinuousMap.const ℂ (κ ω))) q
  change weylScale (ξ : ℝ) (ContinuousMap.const ℂ (κ ω)) (D (h ω)) q =
    D (LQGMetric.addConst (h ω) (κ ω)) q at hqw
  exact hqw.symm.trans (weylScale_const (ξ : ℝ) (κ ω) (D (h ω)) hl q)

 
theorem exists_ae_sideRemovable
    (ξ : Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ u₀ : ℝ, |u₀| < 1 / 100 ∧ ∀ᵐ ω ∂P, SideRemovable (D (h ω)) u₀ := by
  have hDm : Measurable D := hweak.1
  have hhm : Measurable h := hh.1.measurable
  have hF : Measurable (fun ω => D (h ω)) := hDm.comp hhm
  let μ : Measure LSCMetric := P.map (fun ω => D (h ω))
  haveI : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance
  let Up : RectTriple → LSCMetric → ℝ → ℝ≥0∞ := fun τ d =>
    upperPathInf d (ratRect 0 τ.1) (ratRect 0 τ.2.1) (ratRect 0 τ.2.2)
  let Lo : RectTriple → LSCMetric → ℝ → ℝ≥0∞ := fun τ d =>
    lowerPathInf d (ratRect 0 τ.1) (ratRect 0 τ.2.1) (ratRect 0 τ.2.2)
  
  have hup : ∀ᵐ s : ℝ ∂volume, ∀ᵐ d ∂μ, ∀ τ : RectTriple, ContinuousAt (Up τ d) s := by
    have h1 : ∀ τ : RectTriple, ∀ᵐ s : ℝ ∂volume, ∀ᵐ d ∂μ, ContinuousAt (Up τ d) s :=
      fun τ => ae_height_ae_continuousAt_upperPathInf μ (isCompact_ratRect 0 τ.1)
        (isCompact_ratRect 0 τ.2.1) (isCompact_ratRect 0 τ.2.2)
    filter_upwards [ae_all_iff.mpr h1] with s hs
    exact ae_all_iff.mpr hs
  have hlo : ∀ᵐ s : ℝ ∂volume, ∀ᵐ d ∂μ, ∀ τ : RectTriple, ContinuousAt (Lo τ d) s := by
    have h1 : ∀ τ : RectTriple, ∀ᵐ s : ℝ ∂volume, ∀ᵐ d ∂μ, ContinuousAt (Lo τ d) s :=
      fun τ => ae_height_ae_continuousAt_lowerPathInf μ (isCompact_ratRect 0 τ.1)
        (isCompact_ratRect 0 τ.2.1) (isCompact_ratRect 0 τ.2.2)
    filter_upwards [ae_all_iff.mpr h1] with s hs
    exact ae_all_iff.mpr hs
  have hlo1 : ∀ᵐ u : ℝ ∂volume, ∀ᵐ d ∂μ, ∀ τ : RectTriple, ContinuousAt (Lo τ d) (1 + u) :=
    (measurePreserving_add_left volume (1 : ℝ)).quasiMeasurePreserving.ae hlo
  
  have hres : ∀ᵐ u ∂(volume.restrict (Ioo (-(1 / 100 : ℝ)) (1 / 100))),
      u ∈ Ioo (-(1 / 100 : ℝ)) (1 / 100) ∧
        (∀ᵐ d ∂μ, ∀ τ : RectTriple, ContinuousAt (Up τ d) u) ∧
        (∀ᵐ d ∂μ, ∀ τ : RectTriple, ContinuousAt (Lo τ d) (1 + u)) :=
    (ae_restrict_mem measurableSet_Ioo).and ((ae_restrict_of_ae hup).and (ae_restrict_of_ae hlo1))
  have : (ae (volume.restrict (Ioo (-(1 / 100 : ℝ)) (1 / 100)))).NeBot := by
    rw [ae_neBot, Ne, Measure.restrict_eq_zero, Real.volume_Ioo]
    norm_num
  obtain ⟨u₀, hu₀, hgoodU, hgoodL⟩ := hres.exists
  refine ⟨u₀, abs_lt.mpr ⟨hu₀.1, hu₀.2⟩, ?_⟩
  
  have hcont : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.isGFFPlusCont_of_normalized
      (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh)
  set z : ℂ := ⟨0, u₀⟩ with hz
  have hgoodω : ∀ᵐ ω ∂P, ∀ τ : RectTriple,
      ContinuousAt (Up τ (D (h ω))) u₀ ∧ ContinuousAt (Lo τ (D (h ω))) (1 + u₀) := by
    filter_upwards [ae_of_ae_map hF.aemeasurable hgoodU,
      ae_of_ae_map hF.aemeasurable hgoodL] with ω h1 h2
    exact fun τ => ⟨h1 τ, h2 τ⟩
  obtain ⟨_, _, _, _, htrans, _, _⟩ := hweak
  have htr : ∀ᵐ ω ∂P, SideRemovable (D (translateDist z (h ω))) u₀ := by
    filter_upwards [hgoodω, htrans P h hcont z] with ω hg hT
    intro V E F
    have hzim : z.im = u₀ := rfl
    have hup' : upperPathInf (D (translateDist z (h ω))) (ratRect u₀ V) (ratRect u₀ E)
        (ratRect u₀ F) = fun s => Up (V, E, F) (D (h ω)) (s + u₀) := by
      funext s
      rw [upperPathInf_translate (D (h ω)) (D (translateDist z (h ω))) z
        (fun x y => hT x y), ratRect_translate, ratRect_translate, ratRect_translate, hzim]
    have hlo' : lowerPathInf (D (translateDist z (h ω))) (ratRect u₀ V) (ratRect u₀ E)
        (ratRect u₀ F) = fun s => Lo (V, E, F) (D (h ω)) (s + u₀) := by
      funext s
      rw [lowerPathInf_translate (D (h ω)) (D (translateDist z (h ω))) z
        (fun x y => hT x y), ratRect_translate, ratRect_translate, ratRect_translate, hzim]
    obtain ⟨hgU, hgL⟩ := hg (V, E, F)
    rw [hup', hlo']
    constructor
    · have hc : ContinuousAt (fun s : ℝ => s + u₀) 0 :=
        (continuous_id.add continuous_const).continuousAt
      have hgU' : ContinuousAt (Up (V, E, F) (D (h ω))) ((fun s : ℝ => s + u₀) 0) := by
        show ContinuousAt _ (0 + u₀)
        rw [zero_add]; exact hgU
      exact ContinuousAt.comp (g := Up (V, E, F) (D (h ω))) (f := fun s : ℝ => s + u₀)
        (x := 0) hgU' hc
    · have hc : ContinuousAt (fun s : ℝ => s + u₀) 1 :=
        (continuous_id.add continuous_const).continuousAt
      have hgL' : ContinuousAt (Lo (V, E, F) (D (h ω))) ((fun s : ℝ => s + u₀) 1) := by
        show ContinuousAt _ (1 + u₀)
        exact hgL
      exact ContinuousAt.comp (g := Lo (V, E, F) (D (h ω))) (f := fun s : ℝ => s + u₀)
        (x := 1) hgL' hc
  
  set κ : Ω → ℝ := fun ω => LQGMetric.circleAvg (h ω) 1 z with hκ
  set h' : Ω → LQGMetric.DistC := fun ω =>
    LQGMetric.addConst (translateDist z (h ω)) (-κ ω) with hh'def
  have hh' : IsNormalizedWholePlaneGFF h' P :=
    Uniqueness.Toolkit.AnnulusIteration.translated_normalized hh.1 z
  have hcont' : LQGMetric.IsGFFPlusCont h' P :=
    LQGMetric.GM.isGFFPlusCont_of_normalized
      (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh')
  have hback : ∀ ω, LQGMetric.addConst (h' ω) (κ ω) = translateDist z (h ω) := by
    intro ω
    simp only [hh'def, LQGMetric.GFFLaw.addConst_addConst, neg_add_cancel,
      LQGMetric.GFFLaw.addConst_zero']
  have hsc := ae_addConst_eq_mul_of_pfe P h' hcont' ξ D c
    ⟨hDm, ‹_›, ‹_›, ‹_›, htrans, ‹_›, ‹_›⟩ κ
  have hh'good : ∀ᵐ ω ∂P, h' ω ∈ {g | SideRemovable (D g) u₀} := by
    filter_upwards [htr, hsc] with ω h1 h2
    rw [← hback ω] at h1
    exact sideRemovable_of_dist_scale (ENNReal.ofReal (Real.exp ((ξ : ℝ) * κ ω)))
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
      (fun x y => h2 (x, y)) u₀ h1
  
  have hS : MeasurableSet {g : LQGMetric.DistC | SideRemovable (D g) u₀} :=
    hDm (measurableSet_sideRemovable u₀)
  have hlaw : P.map h' = P.map h := by
    rw [← LQGMetric.GM.normGFFLaw_eq
        (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh'),
      ← LQGMetric.GM.normGFFLaw_eq (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh)]
  have hmap : ∀ᵐ g ∂(P.map h'), g ∈ {g | SideRemovable (D g) u₀} :=
    (ae_map_iff hh'.1.measurable.aemeasurable hS).mpr hh'good
  rw [hlaw] at hmap
  exact (ae_map_iff hhm.aemeasurable hS).mp hmap

end SupercriticalLQGUniqueness.B2.Median
