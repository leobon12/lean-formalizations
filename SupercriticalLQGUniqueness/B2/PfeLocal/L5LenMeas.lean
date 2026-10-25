import SupercriticalLQGUniqueness.B2.PfeLocal.L5Shrink
import SupercriticalLQGUniqueness.B2.PfeLocal.PathMeasure
import LQGMetric.Papers.LM.T1_7V1

 

















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric.LM

 
theorem l5_exists_rect_of_compact {a b c d : ℝ} {C : Set ℂ} (hC : IsCompact C)
    (hCS : C ⊆ {z | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}) :
    ∃ q, C ⊆ l5Rect q ∧ l5Rect q ⊆ {z | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d} := by
  rcases C.eq_empty_or_nonempty with hC0 | hne
  · refine ⟨(1, 0, 1, 0), by simp [hC0], fun z hz => ?_⟩
    simp only [l5Rect, mem_setOf_eq] at hz
    push_cast at hz
    linarith [hz.1, hz.2.1]
  obtain ⟨z₁, hz₁, hm₁⟩ := hC.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨z₂, hz₂, hm₂⟩ := hC.exists_isMaxOn hne Complex.continuous_re.continuousOn
  obtain ⟨z₃, hz₃, hm₃⟩ := hC.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨z₄, hz₄, hm₄⟩ := hC.exists_isMaxOn hne Complex.continuous_im.continuousOn
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (hCS hz₁).1
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn (hCS hz₂).2.1
  obtain ⟨q₃, hq₃a, hq₃b⟩ := exists_rat_btwn (hCS hz₃).2.2.1
  obtain ⟨q₄, hq₄a, hq₄b⟩ := exists_rat_btwn (hCS hz₄).2.2.2
  refine ⟨(q₁, q₂, q₃, q₄), fun z hz => ?_, fun z hz => ?_⟩
  · have e1 : z₁.re ≤ z.re := hm₁ hz
    have e2 : z.re ≤ z₂.re := hm₂ hz
    have e3 : z₃.im ≤ z.im := hm₃ hz
    have e4 : z.im ≤ z₄.im := hm₄ hz
    simp only [l5Rect, mem_setOf_eq]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · simp only [l5Rect, mem_setOf_eq] at hz
    exact ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩

theorem l5_square_rect (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) {C : Set ℂ} (hC : IsCompact C)
    (hCS : C ⊆ t17Square ε θ k) : ∃ q, C ⊆ l5Rect q ∧ l5Rect q ⊆ t17Square ε θ k :=
  l5_exists_rect_of_compact hC hCS

 
theorem l5_grid_disjoint_square {ε : ℝ} (hε : 0 < ε) (θ : ℝ × ℝ) (k : ℤ × ℤ) :
    Disjoint (t17Grid ε θ) (t17Square ε θ k) := by
  refine Set.disjoint_left.2 fun x hG hS => ?_
  obtain ⟨s1, s2, s3, s4⟩ := hS
  have key : ∀ (u c : ℝ) (m j : ℤ), u = ε * (m + c) → ε * (j + c) < u → u < ε * (j + 1 + c) →
      False := by
    intro u c m j hu h1 h2
    rw [hu] at h1 h2
    have h1' : (j : ℝ) < m := by
      have := lt_of_mul_lt_mul_left h1 hε.le; linarith
    have h2' : (m : ℝ) < j + 1 := by
      have := lt_of_mul_lt_mul_left h2 hε.le; linarith
    have a1 : j < m := by exact_mod_cast h1'
    have a2 : m < j + 1 := by exact_mod_cast h2'
    omega
  rcases hG with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact key x.re θ.1 m k.1 hm s1 s2
  · exact key x.im θ.2 m k.2 hm s3 s4

theorem l5_measurableSet_preimage {P : ℝ → ℂ} {a b : ℝ} (hP : ContinuousOn P (Icc a b))
    {S : Set ℂ} (hS : MeasurableSet S) : MeasurableSet (P ⁻¹' S ∩ Icc a b) := by
  classical
  set Q : ℝ → ℂ := (Icc a b).piecewise P (fun _ => P a)
  have hQ : Measurable Q := hP.measurable_piecewise continuousOn_const measurableSet_Icc
  have : P ⁻¹' S ∩ Icc a b = Q ⁻¹' S ∩ Icc a b := by
    ext t
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [Q, Set.piecewise_eq_of_mem _ _ _ h2] using h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [Q, Set.piecewise_eq_of_mem _ _ _ h2] using h1, h2⟩
  rw [this]
  exact (hQ hS).inter measurableSet_Icc

theorem l5_measurableSet_grid (ε : ℝ) (θ : ℝ × ℝ) : MeasurableSet (t17Grid ε θ) := by
  unfold t17Grid
  refine MeasurableSet.union ?_ ?_
  · have : {x : ℂ | ∃ k : ℤ, x.re = ε * (k + θ.1)} =
        ⋃ k : ℤ, Complex.re ⁻¹' {ε * (k + θ.1)} := by ext x; simp
    rw [this]
    exact MeasurableSet.iUnion fun k => Complex.measurable_re (measurableSet_singleton _)
  · have : {x : ℂ | ∃ k : ℤ, x.im = ε * (k + θ.2)} =
        ⋃ k : ℤ, Complex.im ⁻¹' {ε * (k + θ.2)} := by ext x; simp
    rw [this]
    exact MeasurableSet.iUnion fun k => Complex.measurable_im (measurableSet_singleton _)

 

theorem l5_len_decomp (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ} (hc : T17Curve (D.pt ∘ P) a b)
    (hPe : ContinuousOn P (Icc a b)) {ε R : ℝ} (hε : 0 < ε) {θ : ℝ × ℝ}
    (hθ1 : θ.1 ∈ Icc (0 : ℝ) 1) (hθ2 : θ.2 ∈ Icc (0 : ℝ) 1)
    (htr : ∀ t ∈ Icc a b, ‖P t‖ ≤ R) :
    D.len P a b = pathLengthIn D P a b (t17Grid ε θ) +
      ∑ k ∈ t17Box ε R, pathLengthIn D P a b (t17Square ε θ k) := by
  have hlen : D.len P a b = t17LenMeas (D.pt ∘ P) a b (Icc a b) := (t17LenMeas_Icc hc).symm
  rw [hlen]
  unfold pathLengthIn
  have hmS : ∀ k, MeasurableSet (P ⁻¹' t17Square ε θ k ∩ Icc a b) := fun k =>
    l5_measurableSet_preimage hPe (t17_isOpen_square ε θ k).measurableSet
  have hmG : MeasurableSet (P ⁻¹' t17Grid ε θ ∩ Icc a b) :=
    l5_measurableSet_preimage hPe (l5_measurableSet_grid ε θ)
  have hU : ∑ k ∈ t17Box ε R, t17LenMeas (D.pt ∘ P) a b (P ⁻¹' t17Square ε θ k ∩ Icc a b) =
      t17LenMeas (D.pt ∘ P) a b (⋃ k ∈ t17Box ε R, P ⁻¹' t17Square ε θ k ∩ Icc a b) :=
    (measure_biUnion_finset (fun i _ j _ hij => Disjoint.mono inter_subset_left
      inter_subset_left ((t17Square_disjoint hε θ hij).preimage P)) fun k _ => hmS k).symm
  have hdisj : Disjoint (P ⁻¹' t17Grid ε θ ∩ Icc a b)
      (⋃ k ∈ t17Box ε R, P ⁻¹' t17Square ε θ k ∩ Icc a b) := by
    rw [Set.disjoint_iUnion₂_right]
    intro k _
    exact Disjoint.mono inter_subset_left inter_subset_left
      ((l5_grid_disjoint_square hε θ k).preimage P)
  have hmU : MeasurableSet (⋃ k ∈ t17Box ε R, P ⁻¹' t17Square ε θ k ∩ Icc a b) :=
    Finset.measurableSet_biUnion _ fun k _ => hmS k
  rw [hU, ← measure_union hdisj hmU]
  congr 1
  ext t
  simp only [mem_union, mem_inter_iff, mem_preimage, mem_iUnion, exists_prop]
  constructor
  · intro ht
    by_cases hG : P t ∈ t17Grid ε θ
    · exact Or.inl ⟨hG, ht⟩
    · exact Or.inr ⟨t17Idx ε θ (P t), t17_idx_mem hε hθ1 hθ2 (htr t ht),
        t17_mem_square hε θ hG, ht⟩
  · rintro (⟨-, ht⟩ | ⟨k, -, -, ht⟩) <;> exact ht

 
theorem l5_pathLengthIn_le_smul {D D' : LSCMetric} (K : ℝ≥0)
    (hle : ∀ x y, D' (x, y) ≤ K * D (x, y)) (P : ℝ → ℂ) {a b : ℝ}
    (hc : T17Curve (D.pt ∘ P) a b) (hc' : T17Curve (D'.pt ∘ P) a b) (S : Set ℂ) :
    pathLengthIn D' P a b S ≤ K * pathLengthIn D P a b S := by
  have h := t17LenMeas_le_smul hc hc' K fun x _ y _ => hle (P x) (P y)
  have := h (P ⁻¹' S ∩ Icc a b)
  simpa only [pathLengthIn, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using this

 
theorem l5_t17Curve_of_le {D D' : LSCMetric} (K : ℝ≥0) (hle : ∀ x y, D' (x, y) ≤ K * D (x, y))
    {P : ℝ → ℂ} {a b : ℝ} (hc : T17Curve (D.pt ∘ P) a b) : T17Curve (D'.pt ∘ P) a b := by
  refine ⟨hc.1, ?_, ?_⟩
  · let ι : D.Space → D'.Space := fun x => x
    have hlip : LipschitzWith K ι := by
      intro x y
      change D' (x, y) ≤ (K : ℝ≥0∞) * D (x, y)
      exact hle x y
    exact hlip.continuous.comp_continuousOn hc.2.1
  · have := t17_eVariationOn_le_mul (g := D.pt ∘ P) (g' := D'.pt ∘ P) (s := Icc a b)
      (c := (K : ℝ≥0∞)) fun x _ y _ => hle (P x) (P y)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hc.2.2) this

theorem l5_lenMeas_singleton {D : LSCMetric} {P : ℝ → ℂ} {a b : ℝ}
    (hc : T17Curve (D.pt ∘ P) a b) {t : ℝ} (ht : t ∈ Icc a b) :
    t17LenMeas (D.pt ∘ P) a b {t} = 0 := by
  have := t17LenMeas_Icc_sub hc ht.1 le_rfl ht.2
  rw [Icc_self] at this
  rw [this]
  exact eVariationOn.subsingleton _ subsingleton_singleton

 
theorem l5_pathLengthIn_eq_of_enc_eq {S : Set ℂ} (hSo : IsOpen S)
    (hS : ∀ C : Set ℂ, IsCompact C → C ⊆ S → ∃ q, C ⊆ l5Rect q ∧ l5Rect q ⊆ S)
    {D D' : LSCMetric} (henc : l5Enc S D = l5Enc S D') (P : ℝ → ℂ) {a b : ℝ}
    (hc : T17Curve (D.pt ∘ P) a b) (hc' : T17Curve (D'.pt ∘ P) a b)
    (hPe : ContinuousOn P (Icc a b)) :
    pathLengthIn D P a b S = pathLengthIn D' P a b S := by
  set O : Set ℝ := Ioo a b ∩ P ⁻¹' S
  have hO : IsOpen O := (hPe.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo hSo
  have hOab : O ⊆ Ioo a b := inter_subset_left
  have heq : ∀ x y, x ≤ y → Icc x y ⊆ O →
      eVariationOn (D.pt ∘ P) (Icc x y) = eVariationOn (D'.pt ∘ P) (Icc x y) := by
    intro x y hxy hxyO
    have hsub : Icc x y ⊆ Icc a b := fun t ht => Ioo_subset_Icc_self (hOab (hxyO ht))
    have hCc : IsCompact (P '' Icc x y) := isCompact_Icc.image_of_continuousOn (hPe.mono hsub)
    have hCS : P '' Icc x y ⊆ S := by
      rintro _ ⟨t, ht, rfl⟩
      exact (hxyO ht).2
    obtain ⟨q, hCq, hqS⟩ := hS _ hCc hCS
    exact l5_len_eq_of_enc_eq henc hqS P ⟨hxy, hc.2.1.mono hsub⟩ ⟨hxy, hc'.2.1.mono hsub⟩
      fun u hu => hCq ⟨u, hu, rfl⟩
  have hOeq := t17LenMeas_eq_on_open hc hc' hO hOab heq
  have hreduce : ∀ (E : LSCMetric), T17Curve (E.pt ∘ P) a b →
      t17LenMeas (E.pt ∘ P) a b (P ⁻¹' S ∩ Icc a b) = t17LenMeas (E.pt ∘ P) a b O := by
    intro E hcE
    apply le_antisymm
    · calc t17LenMeas (E.pt ∘ P) a b (P ⁻¹' S ∩ Icc a b)
          ≤ t17LenMeas (E.pt ∘ P) a b (O ∪ ({a} ∪ {b})) := by
            refine measure_mono fun t ht => ?_
            rcases eq_or_lt_of_le ht.2.1 with h | h
            · exact Or.inr (Or.inl h.symm)
            rcases eq_or_lt_of_le ht.2.2 with h' | h'
            · exact Or.inr (Or.inr h')
            exact Or.inl ⟨⟨h, h'⟩, ht.1⟩
        _ ≤ t17LenMeas (E.pt ∘ P) a b O + (t17LenMeas (E.pt ∘ P) a b {a} +
            t17LenMeas (E.pt ∘ P) a b {b}) :=
            (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
        _ = t17LenMeas (E.pt ∘ P) a b O := by
            rw [l5_lenMeas_singleton hcE ⟨le_rfl, hcE.1⟩,
              l5_lenMeas_singleton hcE ⟨hcE.1, le_rfl⟩, add_zero, add_zero]
    · exact measure_mono fun t ht => ⟨ht.2, Ioo_subset_Icc_self ht.1⟩
  unfold pathLengthIn
  rw [hreduce D hc, hreduce D' hc', hOeq]

 
theorem l5_len_resample {D D'' : LSCMetric} (K : ℝ≥0) (hK : 1 ≤ K)
    (hle : ∀ x y, D'' (x, y) ≤ K * D (x, y)) (P : ℝ → ℂ) {a b : ℝ}
    (hc : T17Curve (D.pt ∘ P) a b) (hPe : ContinuousOn P (Icc a b)) {ε R : ℝ} (hε : 0 < ε)
    {θ : ℝ × ℝ} (hθ1 : θ.1 ∈ Icc (0 : ℝ) 1) (hθ2 : θ.2 ∈ Icc (0 : ℝ) 1)
    (htr : ∀ t ∈ Icc a b, ‖P t‖ ≤ R) (T : Finset (ℤ × ℤ)) (hT : T ⊆ t17Box ε R)
    (henc : ∀ k ∈ t17Box ε R, k ∉ T →
      l5Enc (t17Square ε θ k) D'' = l5Enc (t17Square ε θ k) D) :
    D''.len P a b ≤ D.len P a b + ((K : ℝ≥0∞) - 1) * (pathLengthIn D P a b (t17Grid ε θ) +
      ∑ k ∈ T, pathLengthIn D P a b (t17Square ε θ k)) := by
  have hc'' := l5_t17Curve_of_le K hle hc
  rw [l5_len_decomp D'' P hc'' hPe hε hθ1 hθ2 htr, l5_len_decomp D P hc hPe hε hθ1 hθ2 htr,
    ← Finset.sum_sdiff hT, ← Finset.sum_sdiff hT]
  set A := pathLengthIn D P a b (t17Grid ε θ)
  set B := ∑ k ∈ T, pathLengthIn D P a b (t17Square ε θ k)
  set C := ∑ k ∈ t17Box ε R \ T, pathLengthIn D P a b (t17Square ε θ k)
  have hA : pathLengthIn D'' P a b (t17Grid ε θ) ≤ K * A :=
    l5_pathLengthIn_le_smul K hle P hc hc'' _
  have hB : ∑ k ∈ T, pathLengthIn D'' P a b (t17Square ε θ k) ≤ K * B := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => l5_pathLengthIn_le_smul K hle P hc hc'' _
  have hC : ∑ k ∈ t17Box ε R \ T, pathLengthIn D'' P a b (t17Square ε θ k) = C := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.1 hk
    exact (l5_pathLengthIn_eq_of_enc_eq (t17_isOpen_square ε θ k)
      (fun C hC hCS => l5_square_rect ε θ k hC hCS) (henc k hk1 hk2).symm P hc hc'' hPe).symm
  have hK' : (K : ℝ≥0∞) = 1 + ((K : ℝ≥0∞) - 1) :=
    (add_tsub_cancel_of_le (by exact_mod_cast hK)).symm
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0∞, (K : ℝ≥0∞) = 1 + d := ⟨_, hK'⟩
  have hd' : (K : ℝ≥0∞) - 1 = d := by rw [hd, ENNReal.add_sub_cancel_left ENNReal.one_ne_top]
  calc pathLengthIn D'' P a b (t17Grid ε θ) +
        (∑ k ∈ t17Box ε R \ T, pathLengthIn D'' P a b (t17Square ε θ k) +
          ∑ k ∈ T, pathLengthIn D'' P a b (t17Square ε θ k))
      ≤ K * A + (C + K * B) := by rw [hC]; gcongr
    _ = A + (C + B) + ((K : ℝ≥0∞) - 1) * (A + B) := by
        rw [hd', hd]
        ring

end SupercriticalLQGUniqueness.B2.PfeLocal
