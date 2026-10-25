import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.AttainedEvent




 





set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events

 

theorem isOpen_continuous_lt_lsc {f g : ℝ → ENNReal}
    (hf : Continuous f) (hg : LowerSemicontinuous g) :
    IsOpen {δ | f δ < g δ} := by
  apply isOpen_iff_mem_nhds.mpr
  intro δ hδ
  change f δ < g δ at hδ
  obtain ⟨m, hfm, hmg⟩ := exists_between hδ
  have h₁ : {x | f x < m} ∈ 𝓝 δ :=
    (isOpen_Iio.preimage hf).mem_nhds hfm
  have h₂ : {x | m < g x} ∈ 𝓝 δ :=
    (hg.isOpen_preimage m).mem_nhds hmg
  exact Filter.mem_of_superset (Filter.inter_mem h₁ h₂) (by
    intro x hx
    change f x < m ∧ m < g x at hx
    exact hx.1.trans hx.2)

 
theorem forall_le_iff_forall_rat {f g : ℝ → ENNReal}
    (hf : Continuous f) (hg : LowerSemicontinuous g) (δ₀ : ℝ) :
    (∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → g δ ≤ f δ) ↔
      (∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ δ₀ → g q ≤ f q) := by
  constructor
  · intro h q hq hqδ
    exact h q hq hqδ
  · intro h δ hδ hδ₀
    by_contra hn
    have hviol : f δ < g δ := lt_of_not_ge hn
    have hO : IsOpen {x | f x < g x} := isOpen_continuous_lt_lsc hf hg
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hO.mem_nhds hviol)
    obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (max_lt hl hδ)
    have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (le_max_right l 0) hqlo
    have hqδ : (q : ℝ) ≤ δ₀ := (hqhi.trans_le hδ₀).le
    have hqO : f q < g q := hsub ⟨lt_of_le_of_lt (le_max_left l 0) hqlo,
      hqhi.trans hu⟩
    exact (not_lt_of_ge (h q hq0 hqδ)) hqO

 
def pointSphereDist (D : LSCMetric) (x : ℂ) (R : ℝ) : ENNReal :=
  spherePairInf D x 0 R

 
theorem pointSphereDist_joint_lsc :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℝ) =>
      pointSphereDist p.1 p.2.1 p.2.2) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hc : Continuous (fun q : LSCMetric × (ℂ × ℝ) => q.2.1) :=
    continuous_fst.comp continuous_snd
  have hR : Continuous (fun q : LSCMetric × (ℂ × ℝ) => q.2.2) :=
    continuous_snd.comp continuous_snd
  exact spherePairInf_seq_liminf hm ((hc.tendsto p).comp hG)
    tendsto_const_nhds ((hR.tendsto p).comp hG)

 
theorem pointSphereDist_joint_measurable :
    Measurable (fun p : LSCMetric × (ℂ × ℝ) =>
      pointSphereDist p.1 p.2.1 p.2.2) :=
  pointSphereDist_joint_lsc.measurable

 

theorem point_loop_forall_iff_rat (D : LSCMetric) (x : ℂ)
    {r θ δ₀ : ℝ} (hθ : 0 < θ) {T : ENNReal} (hT : T ≠ ⊤) :
    (∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      pointSphereDist D x (δ * r) ≤ ENNReal.ofReal (δ ^ θ) * T) ↔
    (∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ δ₀ →
      pointSphereDist D x ((q : ℝ) * r) ≤
        ENNReal.ofReal ((q : ℝ) ^ θ) * T) := by
  have hf : Continuous (fun δ : ℝ => ENNReal.ofReal (δ ^ θ) * T) :=
    (ENNReal.continuous_mul_const hT).comp
      (ENNReal.continuous_ofReal.comp (Real.continuous_rpow_const hθ.le))
  have hg : LowerSemicontinuous (fun δ : ℝ => pointSphereDist D x (δ * r)) := by
    apply (lowerSemicontinuous_iff_seq).2
    intro δs δ hδs
    exact spherePairInf_seq_liminf tendsto_const_nhds tendsto_const_nhds
      tendsto_const_nhds ((continuous_id.mul_const r).tendsto δ |>.comp hδs)
  exact forall_le_iff_forall_rat hf hg δ₀


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
