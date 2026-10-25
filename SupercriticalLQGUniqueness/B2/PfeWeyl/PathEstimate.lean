import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.WeylLength
import HigherDimLQGMetric.Metric.Reparam

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

private def forget (D : LSCMetric) : D.Space → ℂ := id

 

theorem exists_near_min_weyl_curve (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (z w : ℂ) (hfin : weylScale ξ f D (z, w) ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : ℝ → ℂ) (L : ℝ), D.IsCurve P 0 L ∧
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) ∧ P 0 = z ∧ P L = w ∧
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) <
        weylScale ξ f D (z, w) + ENNReal.ofReal δ := by
  have hlt : weylScale ξ f D (z, w) <
      weylScale ξ f D (z, w) + ENNReal.ofReal δ :=
    ENNReal.lt_add_right hfin (ENNReal.ofReal_pos.mpr hδ).ne'
  simp only [weylScale, iInf_lt_iff] at hlt
  obtain ⟨P, L, hP, hu, h0, h1, hcost⟩ := hlt
  exact ⟨P, L, hP, hu, h0, h1, hcost⟩

 

theorem weylScale_le_subinterval_cost (D : LSCMetric) (ξ : ℝ)
    (f : C(ℂ, ℝ)) (hforget : Continuous (forget D))
    {P : ℝ → ℂ} {L s t : ℝ} (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) (hst : s ≤ t) :
    weylScale ξ f D (P s, P t) ≤
      ∫⁻ τ in Icc s t, ENNReal.ofReal (Real.exp (ξ * f (P τ))) := by
  rw [Uniqueness.Toolkit.WeylLength.weylScale_eq_weylDistOn D ξ f hforget]
  let weight : D.Space → ℝ := fun x => Real.exp (ξ * f (forget D x))
  have hsub : Icc s t ⊆ Icc 0 L := Icc_subset_Icc hs.1 ht.2
  have hc : ContinuousOn (D.pt ∘ P) (Icc s t) := hP.2.mono hsub
  have hu' : HasUnitSpeedOn (D.pt ∘ P) (Icc s t) :=
    LQGMetric.MetricGeometry.hasUnitSpeedOn_mono_Icc hu hs.1 ht.2
  have hw : ContinuousOn (fun τ => weight ((D.pt ∘ P) τ)) (Icc s t) := by
    have hweight : Continuous weight :=
      Real.continuous_exp.comp
        (continuous_const.mul (f.continuous.comp hforget))
    exact hweight.continuousOn.comp hc (fun _ _ => Set.mem_univ _)
  have hbound := HigherDimLQGMetric.weylDistOn_le_of_curve
    (w := weight) (S := Set.univ) hst hc (fun _ _ => Set.mem_univ _)
  rw [HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn hst hu' hw] at hbound
  exact hbound

 

theorem exists_short_step_sampling_with_times (D : LSCMetric) {P : ℝ → ℂ} {L δ : ℝ}
    (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (hδ : 0 < δ) :
    ∃ (N : ℕ) (t : ℕ → ℝ), 0 < N ∧ Monotone t ∧ t 0 = 0 ∧ t N = L ∧
      ∀ j < N, D (P (t j), P (t (j + 1))) < ENNReal.ofReal δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (L / δ)
  have hL : 0 ≤ L := hP.1
  have hquot : 0 ≤ L / δ := div_nonneg hL hδ.le
  have hNpos : 0 < N := by
    exact_mod_cast (lt_of_le_of_lt hquot hN)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hsmall : L / (N : ℝ) < δ := by
    apply (div_lt_iff₀ hNreal).2
    simpa only [mul_comm] using (div_lt_iff₀ hδ).1 hN
  let t : ℕ → ℝ := fun j => (j : ℝ) * (L / (N : ℝ))
  have ht (j : ℕ) (hj : j ≤ N) : t j ∈ Icc 0 L := by
    have hjr : (j : ℝ) ≤ N := by exact_mod_cast hj
    dsimp [t]
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL hNreal.le)
    · have hdiv : (N : ℝ) * (L / (N : ℝ)) = L := by
        field_simp
      exact (mul_le_mul_of_nonneg_right hjr (div_nonneg hL hNreal.le)).trans_eq hdiv
  have htN : t N = L := by
    dsimp [t]
    field_simp
  have htmono : Monotone t := by
    intro i j hij
    dsimp [t]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (div_nonneg hL hNreal.le)
  refine ⟨N, t, hNpos, htmono, ?_, htN, ?_⟩
  · simp [t]
  · intro j hj
    have hj1 : j + 1 ≤ N := Nat.succ_le_of_lt hj
    have hjle : j ≤ N := Nat.le_of_lt hj
    have htime : t j ≤ t (j + 1) := by
      dsimp [t]
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j)
      exact div_nonneg hL hNreal.le
    have hdist : D (P (t j), P (t (j + 1))) ≤
        ENNReal.ofReal (t (j + 1) - t j) := by
      have h := LQGMetric.MetricGeometry.edist_le_curveLength
        (D.pt ∘ P) htime
      rw [LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn
        hu (ht j hjle) (ht (j + 1) hj1)] at h
      exact h
    have hstep : t (j + 1) - t j = L / (N : ℝ) := by
      simp only [t, Nat.cast_add, Nat.cast_one]
      ring
    change D (P (t j), P (t (j + 1))) < ENNReal.ofReal δ
    rw [hstep] at hdist
    exact hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).2 hsmall)

theorem exists_short_step_sampling (D : LSCMetric) {P : ℝ → ℂ} {L δ : ℝ}
    (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (hδ : 0 < δ) :
    ∃ (N : ℕ) (v : ℕ → ℂ), 0 < N ∧ v 0 = P 0 ∧ v N = P L ∧
      ∀ j < N, D (v j, v (j + 1)) < ENNReal.ofReal δ := by
  obtain ⟨N, t, hN, _, ht0, htN, hstep⟩ :=
    exists_short_step_sampling_with_times D hP hu hδ
  exact ⟨N, P ∘ t, hN, by simp [ht0], by simp [htN], hstep⟩

private theorem weighted_chain_eq {X : Type*} [PseudoEMetricSpace X]
    (weight : X → ℝ) (P : ℝ → X) (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      HigherDimLQGMetric.weightedLength weight P (t j) (t (j + 1))) =
      HigherDimLQGMetric.weightedLength weight P (t 0) (t N) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty,
      HigherDimLQGMetric.weightedLength_self]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact HigherDimLQGMetric.weightedLength_add
        (ht (Nat.zero_le N)) (ht (Nat.le_succ N))

 

theorem weyl_chain_le_cost (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (forget D)) {P : ℝ → ℂ} {L : ℝ}
    (hP : D.IsCurve P 0 L) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ) (ht0 : t 0 = 0) (htN : t N = L) :
    (∑ j ∈ Finset.range N, weylScale ξ f D (P (t j), P (t (j + 1)))) ≤
      ∫⁻ τ in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P τ))) := by
  let weight : D.Space → ℝ := fun x => Real.exp (ξ * f (forget D x))
  have hweight : Continuous weight :=
    Real.continuous_exp.comp
      (continuous_const.mul (f.continuous.comp hforget))
  have hcweight : ContinuousOn (fun τ => weight ((D.pt ∘ P) τ)) (Icc 0 L) :=
    hweight.continuousOn.comp hP.2 (fun _ _ => Set.mem_univ _)
  have hpiece (j : ℕ) (hj : j < N) :
      weylScale ξ f D (P (t j), P (t (j + 1))) ≤
        HigherDimLQGMetric.weightedLength weight (D.pt ∘ P) (t j) (t (j + 1)) := by
    have hsub : Icc (t j) (t (j + 1)) ⊆ Icc 0 L :=
      Icc_subset_Icc (ht0 ▸ ht (Nat.zero_le j))
        (htN ▸ ht (Nat.succ_le_of_lt hj))
    rw [Uniqueness.Toolkit.WeylLength.weylScale_eq_weylDistOn D ξ f hforget]
    exact HigherDimLQGMetric.weylDistOn_le_of_curve
      (ht (Nat.le_succ j)) (hP.2.mono hsub) (fun _ _ => Set.mem_univ _)
  calc
    _ ≤ ∑ j ∈ Finset.range N,
          HigherDimLQGMetric.weightedLength weight (D.pt ∘ P) (t j) (t (j + 1)) :=
        Finset.sum_le_sum (fun j hj => hpiece j (Finset.mem_range.mp hj))
    _ = HigherDimLQGMetric.weightedLength weight (D.pt ∘ P) (t 0) (t N) :=
        weighted_chain_eq weight (D.pt ∘ P) t ht N
    _ = ∫⁻ τ in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P τ))) := by
      rw [ht0, htN, HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn
        hP.1 hu hcweight]
      rfl

 

theorem weyl_length_decomp_of_finite (D : LSCMetric) (ξ : ℝ)
    (f : C(ℂ, ℝ)) (hforget : Continuous (forget D))
    (z w : ℂ) (hfin : weylScale ξ f D (z, w) ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (v : ℕ → ℂ), 0 < N ∧ v 0 = z ∧ v N = w ∧
      (∀ j < N, D (v j, v (j + 1)) < ENNReal.ofReal δ) ∧
      (∑ j ∈ Finset.range N, weylScale ξ f D (v j, v (j + 1))) <
        weylScale ξ f D (z, w) + ENNReal.ofReal δ := by
  obtain ⟨P, L, hP, hu, hP0, hPL, hcost⟩ :=
    exists_near_min_weyl_curve D ξ f z w hfin hδ
  obtain ⟨N, t, hN, ht, ht0, htN, hstep⟩ :=
    exists_short_step_sampling_with_times D hP hu hδ
  refine ⟨N, P ∘ t, hN, ?_, ?_, hstep, ?_⟩
  · simp [ht0, hP0]
  · simp [htN, hPL]
  · exact (weyl_chain_le_cost D ξ f hforget hP hu t ht N ht0 htN).trans_lt hcost

end SupercriticalLQGUniqueness.B2.PfeWeyl
