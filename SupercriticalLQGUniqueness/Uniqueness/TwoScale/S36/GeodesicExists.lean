import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.L34E24




 












set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

 
theorem exists_unit_geodesic (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {x y : ℂ} (hfin : D (x, y) < ⊤) :
    ∃ R : ℝ → ℂ, ContinuousOn R (Icc 0 (D (x, y)).toReal) ∧
      LQGMetric.MetricGeometry.IsGeodesicCurve (D.pt ∘ R) 0 (D (x, y)).toReal ∧
      HasUnitSpeedOn (D.pt ∘ R) (Icc 0 (D (x, y)).toReal) ∧
      R 0 = x ∧ R (D (x, y)).toReal = y := by
  
  have hnear : ∀ n : ℕ, ∃ (γ : ℝ → ℂ) (a b : ℝ), D.IsCurve γ a b ∧ γ a = x ∧ γ b = y ∧
      D.len γ a b ≤ D (x, y) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    hL x y hfin (1 / ((n : ℝ) + 1)) (by positivity)
  choose γ a b hγ hγa hγb hγlen using hnear
  have hlen1 : ∀ n, D.len (γ n) (a n) (b n) ≤ D (x, y) + 1 := by
    intro n
    refine (hγlen n).trans (add_le_add le_rfl ?_)
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hfin1 : D (x, y) + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hfin.ne, ENNReal.one_ne_top⟩
  
  set K₀ : Set ℂ := {w : ℂ | D (x, w) ≤ D (x, y) + 1} with hK₀
  have hK₀b : Bornology.IsBounded K₀ := BiLipschitz.Barrier.isBounded_closedBall_of_barrier D hB hL x _ hfin1
  set K := closure K₀
  have hK : IsCompact K := hK₀b.isCompact_closure
  have htr : ∀ n, γ n '' Icc (a n) (b n) ⊆ K := by
    rintro n _ ⟨t, ht, rfl⟩
    refine subset_closure ?_
    change D (x, γ n t) ≤ D (x, y) + 1
    have h1 := LSCMetric.apply_le_len D (γ n) ht.1
    rw [hγa n] at h1
    have h2 : D.len (γ n) (a n) t ≤ D.len (γ n) (a n) (b n) :=
      eVariationOn.mono _ (Icc_subset_Icc le_rfl ht.2)
    exact h1.trans (h2.trans (hlen1 n))
  have hfinn : ∀ n, D.len (γ n) (a n) (b n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top hfin1 (hlen1 n)
  have hreparam : ∀ n, ∃ ζ : Path (D.pt (γ n (a n))) (D.pt (γ n (b n))),
      LQGMetric.MetricGeometry.pathLength ζ = D.len (γ n) (a n) (b n) ∧
      (∀ t, (ζ t : ℂ) ∈ K) ∧ LipschitzWith (D.len (γ n) (a n) (b n)).toNNReal ζ := fun n =>
    Toolkit.CompactPathInfimum.exists_lipschitz_reparam D (γ n) (hγ n) (hfinn n) (htr n)
  choose ζ hζlen hζK hζlip using hreparam
  set M : ℝ≥0 := (D (x, y) + 1).toNNReal
  let P : ℕ → unitInterval → ℂ := fun n t => (ζ n t : ℂ)
  have hPlip : ∀ n, LipschitzWith M (D.pt ∘ P n) := by
    intro n
    refine (hζlip n).weaken ?_
    exact ENNReal.toNNReal_mono hfin1 (hlen1 n)
  have hconst : Tendsto (fun _ : ℕ => D) atTop (nhds D) := tendsto_const_nhds
  obtain ⟨φ, P₀, hφ, hlim, hP₀K⟩ := Toolkit.CompactPathInfimum.compact_trace_path_subseq hconst hK
    (fun n t => hζK n t) hPlip
  have hP₀lip : LipschitzWith M (D.pt ∘ P₀) :=
    Toolkit.PathInfimum.lipschitz_limit_of_epi (tendsto_const_nhds (x := D)) hlim (fun n => hPlip (φ n))
  set Q : ℝ → ℂ := fun t => P₀ (projIcc 0 1 zero_le_one t)
  have hQcurve : D.IsCurve Q 0 1 :=
    ⟨zero_le_one, (hP₀lip.continuous.comp continuous_projIcc).continuousOn⟩
  have hQ0 : Q 0 = x := by
    change P₀ (projIcc 0 1 zero_le_one 0) = x
    rw [projIcc_left]
    refine tendsto_nhds_unique (hlim.tendsto_at 0) ?_
    refine tendsto_const_nhds.congr fun n => ?_
    rw [(ζ (φ n)).source]
    exact (hγa (φ n)).symm
  have hQ1 : Q 1 = y := by
    change P₀ (projIcc 0 1 zero_le_one 1) = y
    rw [projIcc_right]
    refine tendsto_nhds_unique (hlim.tendsto_at 1) ?_
    refine tendsto_const_nhds.congr fun n => ?_
    rw [(ζ (φ n)).target]
    exact (hγb (φ n)).symm
  
  have hlenφ : ∀ n, D.len (fun t => P (φ n) (projIcc 0 1 zero_le_one t)) 0 1 ≤
      D (x, y) + ENNReal.ofReal (1 / ((φ n : ℝ) + 1)) := by
    intro n
    have he : D.len (fun t => P (φ n) (projIcc 0 1 zero_le_one t)) 0 1 =
        LQGMetric.MetricGeometry.pathLength (ζ (φ n)) := rfl
    rw [he, hζlen]
    exact hγlen (φ n)
  have hliminf := Toolkit.CompactPathInfimum.joint_len_le_liminf hconst (P := fun n t => P (φ n)
    (projIcc 0 1 zero_le_one t)) (P₀ := Q)
    (fun t _ => hlim.tendsto_at (projIcc 0 1 zero_le_one t))
  have hlimit : Tendsto (fun n => D (x, y) + ENNReal.ofReal (1 / ((φ n : ℝ) + 1))) atTop
      (nhds (D (x, y))) := by
    have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((φ n : ℝ) + 1))) atTop (nhds 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.comp
        hφ.tendsto_atTop)
    simpa only [add_zero] using tendsto_const_nhds.add h0
  have hQle : D.len Q 0 1 ≤ D (x, y) := by
    refine hliminf.trans ?_
    rw [← hlimit.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hlenφ)
  have hQge : D (x, y) ≤ D.len Q 0 1 := by
    have h := LSCMetric.apply_le_len D Q zero_le_one
    rwa [hQ0, hQ1] at h
  have hQlen : D.len Q 0 1 = D (x, y) := le_antisymm hQle hQge
  
  have hQfin : LQGMetric.MetricGeometry.curveLength (D.pt ∘ Q) 0 1 ≠ ⊤ := by
    change D.len Q 0 1 ≠ ⊤
    rw [hQlen]
    exact hfin.ne
  have hTeq : (LQGMetric.MetricGeometry.curveLength (D.pt ∘ Q) 0 1).toReal = (D (x, y)).toReal := by
    change (D.len Q 0 1).toReal = _
    rw [hQlen]
  have hunit := LQGMetric.MetricGeometry.hasUnitSpeedOn_lengthParam zero_le_one hQcurve.2 hQfin
  rw [hTeq] at hunit
  have hlip := LQGMetric.MetricGeometry.lipschitzOnWith_lengthParam zero_le_one hQcurve.2 hQfin
  rw [hTeq] at hlip
  let R : ℝ → ℂ := fun τ => @LQGMetric.MetricGeometry.lengthParam D.Space _ (D.pt ∘ Q) 0 1 τ
  have hRD : D.pt ∘ R = LQGMetric.MetricGeometry.lengthParam (D.pt ∘ Q) 0 1 := by
    funext τ
    rfl
  have hT0 : (0 : ℝ) ≤ (D (x, y)).toReal := ENNReal.toReal_nonneg
  have hRcurve : D.IsCurve R 0 (D (x, y)).toReal := ⟨hT0, by rw [hRD]; exact hlip.continuousOn⟩
  have hR0 : R 0 = x := by
    have h := LQGMetric.MetricGeometry.lengthParam_variationOnFromTo hQfin
      (left_mem_Icc.mpr (zero_le_one' ℝ))
    rw [variationOnFromTo.self] at h
    change @LQGMetric.MetricGeometry.lengthParam D.Space _ (D.pt ∘ Q) 0 1 0 = D.pt x
    rw [h]
    exact hQ0
  have hRT : R (D (x, y)).toReal = y := by
    have h := LQGMetric.MetricGeometry.lengthParam_variationOnFromTo hQfin
      (right_mem_Icc.mpr (zero_le_one' ℝ))
    have hσ : variationOnFromTo (D.pt ∘ Q) (Icc 0 1) 0 1 = (D (x, y)).toReal := by
      rw [variationOnFromTo.eq_of_le _ _ zero_le_one, inter_self]
      exact hTeq
    rw [hσ] at h
    change @LQGMetric.MetricGeometry.lengthParam D.Space _ (D.pt ∘ Q) 0 1 (D (x, y)).toReal =
      D.pt y
    rw [h]
    exact hQ1
  refine ⟨R, BiLipschitz.Barrier.continuousOn_of_barrier_of_length D hB hL hRcurve,
    ⟨hT0, hRcurve.2, ?_⟩, by rw [hRD]; exact hunit, hR0, hRT⟩
  have h := hunit (left_mem_Icc.mpr hT0) (right_mem_Icc.mpr hT0)
  rw [inter_eq_left.mpr (Icc_subset_Icc le_rfl le_rfl)] at h
  change eVariationOn (D.pt ∘ R) (Icc 0 (D (x, y)).toReal) = edist (D.pt (R 0)) (D.pt (R _))
  rw [hRD, h, hR0, hRT, NNReal.coe_one, one_mul, sub_zero, ENNReal.ofReal_toReal hfin.ne]
  rfl

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
