/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXAdapted

/-! # Continuous adapted paths announce their positive open-set exits -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open Coupling
variable {S : Type u} [mS : MeasurableSpace S] {P : Measure S}
  {𝓖 : Filtration ℝ≥0 mS}

/-- Scalar specialization of the landed killed-state first-entrance theorem. -/
theorem isStoppingTime_scalar_hitBelow [𝓖.IsRightContinuous]
    {X : ℝ≥0 → S → ℝ} {ζ : S → ℝ≥0∞} (ha : AdaptedBefore 𝓖 ζ X)
    (hc : ∀ ω, ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω}) (ε : ℝ) :
    IsStoppingTime 𝓖 (fun ω => hitBelow (X · ω) (ζ ω) ε) := by
  have h := isStoppingTime_hitBelow_state (nL := 0) (nR := 0)
    (VL := fun _ _ _ => 0) (VR := fun _ _ _ => 0) ha
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (G := univ) MeasurableSet.univ
    (fun ω _ => (hc ω).prodMk (continuousOn_const.prodMk continuousOn_const))
    (Φ := fun x => x.1) continuous_fst ε
  simpa only [mem_univ, ↓reduceIte, stateAt] using h

/-- The positive exit of a continuous adapted planar path has finite,
increasing announcing stopping times, by the existing candidate selection. -/
theorem exists_isAnnouncingSeq_exitTime [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    {Z : ℝ≥0 → S → ℂ} (ha : ∀ t, Measurable[𝓖 t] (Z t))
    (hc : ∀ ω, Continuous (Z · ω)) {V : Set ℂ} (hV : IsOpen V)
    (hVc : Vᶜ.Nonempty) (hstart : ∀ ω, Z 0 ω ∈ V) :
    ∃ T : ℕ → S → ℝ≥0,
      IsAnnouncingSeq 𝓖 P (fun ω => InteractingSLE.exitTime V (Z · ω)) T := by
  let e : S → ℝ≥0∞ := fun ω => InteractingSLE.exitTime V (Z · ω)
  let d : ℝ≥0 → S → ℝ := fun t ω => infDist (Z t ω) Vᶜ
  have hes : IsStoppingTime 𝓖 (fun ω => (e ω : WithTop ℝ≥0)) :=
    InteractingSLE.isStoppingTime_exitTime ha hc hV
  have hdc : ∀ ω, Continuous (d · ω) := fun ω => (continuous_infDist_pt _).comp (hc ω)
  have hda : AdaptedBefore 𝓖 e d := MartChar.adaptedBefore_of_stronglyAdapted hes
    (fun t => ((continuous_infDist_pt _).measurable.comp (ha t)).stronglyMeasurable)
  have hpos : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < e ω → 0 < d t ω := by
    intro ω t ht
    exact (hV.isClosed_compl.notMem_iff_infDist_pos hVc).1
      (not_not.2 (InteractingSLE.mem_of_lt_exitTime ht))
  let a : ℕ → ℕ → S → WithTop ℝ≥0 := fun _ k ω =>
    hitBelow (d · ω) (e ω) (1 / ((k : ℝ) + 1))
  have ha' : ∀ p k, IsStoppingTime 𝓖 (a p k) := fun _ k =>
    isStoppingTime_scalar_hitBelow hda (fun ω => (hdc ω).continuousOn) _
  have ham : ∀ p ω, Monotone fun k => a p k ω := fun _ _ k l hkl =>
    hitBelow_anti (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1))
  apply exists_isAnnouncingSeq_of_candidates ha' ham
  · exact ae_of_all _ fun ω p hp k => by
      obtain ⟨M, hM⟩ := hp
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
        (ne_top_of_le_ne_top WithTop.coe_ne_top (hM k))
      exact ⟨t, ht.symm, lt_of_hitBelow_eq ht.symm⟩
  · exact ae_of_all _ fun ω t ht => by
      obtain ⟨K, hK⟩ := eventually_atTop.1
        (eventually_le_hitBelow (hdc ω).continuousOn (hpos ω) ht)
      exact ⟨K, fun _ _ k hk => hK k hk⟩
  · exact ae_of_all _ fun ω he => by
      obtain ⟨t, ht, hout⟩ := InteractingSLE.exists_eq_exitTime hV (hc ω) he
      have htpos : 0 < t := ENNReal.coe_pos.1 (ht ▸ InteractingSLE.exitTime_pos hV (hc ω) (hstart ω))
      have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
      have hd0 : d t ω = 0 := infDist_zero_of_mem hout
      refine ⟨0, ⌈t⌉₊, fun k => ?_⟩
      have hdlim : Tendsto (d · ω) (𝓝[<] t) (𝓝 0) := by
        rw [← hd0]
        exact (hdc ω).tendsto t |>.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ s in 𝓝[<] t, s < t ∧ d s ω < 1 / ((k : ℝ) + 1) := by
        filter_upwards [self_mem_nhdsWithin,
          hdlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))] with s hs hd
        exact ⟨hs, hd⟩
      obtain ⟨s, hs, hds⟩ := hev.exists
      have hse : (s : ℝ≥0∞) < e ω := by
        change (s : ℝ≥0∞) < InteractingSLE.exitTime V (Z · ω)
        rw [ht]
        exact ENNReal.coe_lt_coe.2 hs
      exact (hitBelow_le hse hds).trans (WithTop.coe_le_coe.2 (hs.le.trans (Nat.le_ceil t)))

/-- Announcements are closed under taking the minimum of their lifetimes. -/
theorem isAnnouncingSeq_min {e f : S → ℝ≥0∞} {T U : ℕ → S → ℝ≥0}
    (hT : IsAnnouncingSeq 𝓖 P e T) (hU : IsAnnouncingSeq 𝓖 P f U) :
    IsAnnouncingSeq 𝓖 P (fun ω => min (e ω) (f ω)) (fun n ω => min (T n ω) (U n ω)) := by
  refine ⟨fun n => ?_, fun ω => (hT.2.1 ω).min (hU.2.1 ω), fun n => ?_, ?_⟩
  · simpa only [WithTop.coe_min] using (hT.1 n).min (hU.1 n)
  · filter_upwards [hT.2.2.1 n, hU.2.2.1 n] with ω ht hu
    rw [ENNReal.coe_min]
    exact lt_min ((min_le_left _ _).trans_lt ht) ((min_le_right _ _).trans_lt hu)
  · filter_upwards [hT.2.2.2, hU.2.2.2] with ω ht hu t htf
    obtain ⟨i, hi⟩ := ht t (htf.trans_le (min_le_left _ _))
    obtain ⟨j, hj⟩ := hu t (htf.trans_le (min_le_right _ _))
    exact ⟨max i j, le_min (hi.trans (hT.2.1 ω (le_max_left _ _)))
      (hj.trans (hU.2.1 ω (le_max_right _ _)))⟩

end InteractingSLE.Restart.FlowStopIdentCMI
