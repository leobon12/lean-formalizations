import SupercriticalLQGUniqueness.B2.LscTop.Limits
import SupercriticalLQGUniqueness.B2.WeakStrong.Homothety

 















set_option autoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.LscTop

 

 
def dilate (b : Set.Ioi (0 : ℝ)) (D : LSCMetric) : LSCMetric :=
  B2.WeakStrong.dilateM D b (ne_of_gt b.2)

theorem dilate_apply (b : Set.Ioi (0 : ℝ)) (D : LSCMetric) (p : ℂ × ℂ) :
    dilate b D p = D ((b : ℝ) • p.1, (b : ℝ) • p.2) := rfl

 
def smulMetric (c : Set.Ioi (0 : ℝ)) (D : LSCMetric) : LSCMetric :=
  ⟨fun p => ENNReal.ofReal c * D p,
    ⟨fun x => by simp only [D.isExtMetric.1 x, mul_zero],
      fun x y h => D.isExtMetric.2.1 x y
        ((mul_eq_zero.1 h).resolve_left (ENNReal.ofReal_pos.2 c.2).ne'),
      fun x y => congrArg (ENNReal.ofReal c * ·) (D.isExtMetric.2.2.1 x y),
      fun x y z => by rw [← mul_add]; exact mul_le_mul_right (D.isExtMetric.2.2.2 x y z) _⟩,
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      D.lowerSemicontinuous fun _ _ h => mul_le_mul_right h _⟩

theorem smulMetric_apply (c : Set.Ioi (0 : ℝ)) (D : LSCMetric) (p : ℂ × ℂ) :
    smulMetric c D p = ENNReal.ofReal c * D p := rfl

 

 
theorem tendsto_dilate {b : ℕ → Set.Ioi (0 : ℝ)} {b₀ : Set.Ioi (0 : ℝ)} {G : ℕ → LSCMetric}
    {D : LSCMetric} (hb : Tendsto b atTop (𝓝 b₀)) (hG : Tendsto G atTop (𝓝 D)) :
    Tendsto (fun n => dilate (b n) (G n)) atTop (𝓝 (dilate b₀ D)) := by
  have hb' : Tendsto (fun n => (b n : ℝ)) atTop (𝓝 (b₀ : ℝ)) :=
    (continuous_subtype_val.tendsto b₀).comp hb
  rw [LSCMetric.tendsto_iff] at hG ⊢
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · exact hG.1 (fun n => ((b n : ℝ) • (p n).1, (b n : ℝ) • (p n).2)) _
      ((hb'.smul (continuous_fst.tendsto q |>.comp hp)).prodMk_nhds
        (hb'.smul (continuous_snd.tendsto q |>.comp hp)))
  · obtain ⟨p, hp, hGp⟩ := hG.2 ((b₀ : ℝ) • q.1, (b₀ : ℝ) • q.2)
    have hinv : Tendsto (fun n => (b n : ℝ)⁻¹) atTop (𝓝 (b₀ : ℝ)⁻¹) :=
      hb'.inv₀ (mem_Ioi.1 b₀.2).ne'
    refine ⟨fun n => ((b n : ℝ)⁻¹ • (p n).1, (b n : ℝ)⁻¹ • (p n).2), ?_, ?_⟩
    · have h1 := hinv.smul ((continuous_fst.tendsto _).comp hp)
      have h2 := hinv.smul ((continuous_snd.tendsto _).comp hp)
      simp only [Function.comp_def, inv_smul_smul₀ (mem_Ioi.1 b₀.2).ne'] at h1 h2
      exact h1.prodMk_nhds h2
    · simpa only [dilate_apply, smul_inv_smul₀ (mem_Ioi.1 (b _).2).ne'] using hGp

 
theorem continuous_dilate : Continuous fun x : Set.Ioi (0 : ℝ) × LSCMetric => dilate x.1 x.2 := by
  rw [continuous_iff_seqContinuous]
  intro x y hx
  exact tendsto_dilate ((continuous_fst.tendsto y).comp hx) ((continuous_snd.tendsto y).comp hx)

 
theorem measurable_dilate :
    Measurable fun x : Set.Ioi (0 : ℝ) × LSCMetric => dilate x.1 x.2 := by
  have := borelSpace_LSCMetric
  exact continuous_dilate.measurable

 
theorem tendsto_smulMetric {c : ℕ → Set.Ioi (0 : ℝ)} {c₀ : Set.Ioi (0 : ℝ)} {G : ℕ → LSCMetric}
    {D : LSCMetric} (hc : Tendsto c atTop (𝓝 c₀)) (hG : Tendsto G atTop (𝓝 D)) :
    Tendsto (fun n => smulMetric (c n) (G n)) atTop (𝓝 (smulMetric c₀ D)) := by
  have hc' : Tendsto (fun n => ENNReal.ofReal (c n : ℝ)) atTop (𝓝 (ENNReal.ofReal (c₀ : ℝ))) :=
    ENNReal.tendsto_ofReal ((continuous_subtype_val.tendsto c₀).comp hc)
  have hc0 : ENNReal.ofReal (c₀ : ℝ) ≠ 0 := (ENNReal.ofReal_pos.2 c₀.2).ne'
  rw [LSCMetric.tendsto_iff] at hG ⊢
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · calc smulMetric c₀ D q = ENNReal.ofReal (c₀ : ℝ) * D q := rfl
      _ ≤ liminf (fun n => ENNReal.ofReal (c n : ℝ)) atTop *
          liminf (fun n => G n (p n)) atTop := by
        rw [hc'.liminf_eq]
        exact mul_le_mul_right (hG.1 p q hp) _
      _ ≤ liminf (fun n => smulMetric (c n) (G n) (p n)) atTop := ENNReal.le_liminf_mul
  · obtain ⟨p, hp, hGp⟩ := hG.2 q
    exact ⟨p, hp, ENNReal.Tendsto.mul hc' (Or.inl hc0) hGp (Or.inr ENNReal.ofReal_ne_top)⟩

 
theorem continuous_smulMetric :
    Continuous fun x : Set.Ioi (0 : ℝ) × LSCMetric => smulMetric x.1 x.2 := by
  rw [continuous_iff_seqContinuous]
  intro x y hx
  exact tendsto_smulMetric ((continuous_fst.tendsto y).comp hx)
    ((continuous_snd.tendsto y).comp hx)

 
theorem measurable_smulMetric :
    Measurable fun x : Set.Ioi (0 : ℝ) × LSCMetric => smulMetric x.1 x.2 := by
  have := borelSpace_LSCMetric
  exact continuous_smulMetric.measurable

 

theorem lscTendsto_smulMetric {c : ℕ → Set.Ioi (0 : ℝ)} {c₀ : Set.Ioi (0 : ℝ)}
    {G : ℕ → LSCMetric} {D : LSCMetric} (hc : Tendsto (fun n => (c n : ℝ)) atTop (𝓝 (c₀ : ℝ)))
    (hG : LSCTendsto (fun n => (G n).toLSCFun.1) D.toLSCFun.1) :
    LSCTendsto (fun n => (smulMetric (c n) (G n)).toLSCFun.1) (smulMetric c₀ D).toLSCFun.1 := by
  have hc' : Tendsto c atTop (𝓝 c₀) := tendsto_subtype_rng.2 hc
  have hG' : Tendsto G atTop (𝓝 D) := by
    rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff]
    exact LSCFun.tendsto_of_lscTendsto hG
  have h := tendsto_smulMetric hc' hG'
  rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff] at h
  exact LSCFun.lscTendsto_of_tendsto h

 
theorem continuous_smulMetric_dilate {k : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} (hk : Continuous k)
    (D : LSCMetric) : Continuous fun b => smulMetric (k b) (dilate b D) :=
  continuous_smulMetric.comp (hk.prodMk (continuous_dilate.comp
    (continuous_id.prodMk continuous_const)))

end SupercriticalLQGUniqueness.B2.LscTop
