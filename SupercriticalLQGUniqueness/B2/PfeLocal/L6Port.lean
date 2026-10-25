import SupercriticalLQGUniqueness.B2.PfeLocal.L6Cauchy
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

 



















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

 
theorem l6_tendsto_measure_of_ae_eventually {s : ℕ → Set Ω}
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) : Tendsto (fun n => P (s n)) atTop (𝓝 1) := by
  set E : ℕ → Set Ω := fun N => ⋂ n ≥ N, s n with hE
  have hmono : Monotone E := fun a b hab => by
    intro ω hω
    simp only [hE, mem_iInter] at hω ⊢
    exact fun n hn => hω n (hab.trans hn)
  have hU : P (⋃ N, E N) = 1 := by
    have h0 : P (⋃ N, E N)ᶜ = 0 := by
      rw [← ae_iff.symm.trans Iff.rfl] at *
      have : ∀ᵐ ω ∂P, ω ∈ ⋃ N, E N := by
        filter_upwards [h] with ω hω
        obtain ⟨N, hN⟩ := eventually_atTop.1 hω
        exact mem_iUnion.2 ⟨N, mem_iInter₂.2 hN⟩
      exact ae_iff.1 this
    rw [measure_congr (ae_eq_univ.2 h0), measure_univ]
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun N => ?_)
    (fun N => prob_le_one)
  exact measure_mono (biInter_subset_of_mem (le_refl N))

 

theorem l6_measure_closed_eq_one {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T] [HasOuterApproxClosed T] {Z : ℕ → Ω → T}
    (hZ : ∀ n, Measurable (Z n)) {μs : ℕ → ProbabilityMeasure T}
    (hμs : ∀ n, (μs n : Measure T) = P.map (Z n)) {ρ : ProbabilityMeasure T}
    (hlim : Tendsto μs atTop (𝓝 ρ)) {F : Set T} (hF : IsClosed F)
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Z n ω ∈ F) : (ρ : Measure T) F = 1 := by
  have h1 : Tendsto (fun n => (μs n : Measure T) F) atTop (𝓝 1) := by
    have e : (fun n => (μs n : Measure T) F) = fun n => P (Z n ⁻¹' F) := by
      funext n; rw [hμs n, Measure.map_apply (hZ n) hF.measurableSet]
    rw [e]
    exact l6_tendsto_measure_of_ae_eventually hev
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  rw [h1.limsup_eq] at hle
  exact le_antisymm prob_le_one hle

section Product

variable {L Y : Type*} [TopologicalSpace L] [MeasurableSpace L] [TopologicalSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace (L × Y)] [HasOuterApproxClosed (L × Y)]
  {Λ : Ω → L} {Yn : ℕ → Ω → Y} {μs : ℕ → ProbabilityMeasure (L × Y)}
  {ρ : ProbabilityMeasure (L × Y)}

 
theorem l6_ae_of_closed (hZ : ∀ n, Measurable fun ω => (Λ ω, Yn n ω))
    (hμs : ∀ n, (μs n : Measure (L × Y)) = P.map fun ω => (Λ ω, Yn n ω))
    (hlim : Tendsto μs atTop (𝓝 ρ)) {ι : Type*} [Countable ι] {F : ι → Set (L × Y)}
    (hF : ∀ i, IsClosed (F i)) (hev : ∀ i, ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (Λ ω, Yn n ω) ∈ F i) :
    ∀ᵐ p ∂(ρ : Measure (L × Y)), ∀ i, p ∈ F i := by
  rw [ae_all_iff]
  intro i
  have h1 := l6_measure_closed_eq_one hZ hμs hlim (hF i) (hev i)
  have h0 : (ρ : Measure (L × Y)) (F i)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff (hF i).measurableSet]; exact h1
  exact measure_eq_zero_iff_ae_notMem.1 h0 |>.mono fun p hp => by
    by_contra hn; exact hp hn

 
theorem l6_ae_le_of_limsup (hZ : ∀ n, Measurable fun ω => (Λ ω, Yn n ω))
    (hμs : ∀ n, (μs n : Measure (L × Y)) = P.map fun ω => (Λ ω, Yn n ω))
    (hlim : Tendsto μs atTop (𝓝 ρ)) {U : L × Y → ℝ≥0∞} (hU : Continuous U)
    {V : L → ℝ≥0∞} (hV : Continuous V) {C : Set L} (hC : IsOpen C)
    (h : ∀ᵐ ω ∂P, Λ ω ∈ C → limsup (fun n => U (Λ ω, Yn n ω)) atTop ≤ V (Λ ω)) :
    ∀ᵐ p ∂(ρ : Measure (L × Y)), p.1 ∈ C → U p ≤ V p.1 := by
  set F : ℚ → Set (L × Y) := fun q =>
    (Prod.fst ⁻¹' C)ᶜ ∪ {p | ((Real.toNNReal q : ℝ≥0∞)) ≤ V p.1} ∪
      {p | U p ≤ (Real.toNNReal q : ℝ≥0∞)} with hFdef
  have hFc : ∀ q, IsClosed (F q) := fun q =>
    ((hC.preimage continuous_fst).isClosed_compl.union
      (isClosed_le continuous_const (hV.comp continuous_fst))).union
      (isClosed_le hU continuous_const)
  have hev : ∀ q, ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (Λ ω, Yn n ω) ∈ F q := fun q => by
    filter_upwards [h] with ω hω
    by_cases hC' : Λ ω ∈ C
    · by_cases hq : ((Real.toNNReal q : ℝ≥0∞)) ≤ V (Λ ω)
      · exact Eventually.of_forall fun n => Or.inl (Or.inr hq)
      · have hlt : limsup (fun n => U (Λ ω, Yn n ω)) atTop < (Real.toNNReal q : ℝ≥0∞) :=
          (hω hC').trans_lt (lt_of_not_ge hq)
        filter_upwards [eventually_lt_of_limsup_lt hlt] with n hn
        exact Or.inr hn.le
    · exact Eventually.of_forall fun n => Or.inl (Or.inl hC')
  filter_upwards [l6_ae_of_closed hZ hμs hlim hFc hev] with p hp hpC
  by_contra hn
  obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (lt_of_not_ge hn)
  rcases hp q with (hq | hq) | hq
  · exact hq hpC
  · exact absurd h1 (not_lt_of_ge hq)
  · exact absurd h2 (not_lt_of_ge hq)

 
theorem l6_ae_ge_of_liminf (hZ : ∀ n, Measurable fun ω => (Λ ω, Yn n ω))
    (hμs : ∀ n, (μs n : Measure (L × Y)) = P.map fun ω => (Λ ω, Yn n ω))
    (hlim : Tendsto μs atTop (𝓝 ρ)) {U : L × Y → ℝ≥0∞} (hU : Continuous U)
    {V : L → ℝ≥0∞} (hV : Continuous V) {C : Set L} (hC : IsOpen C)
    (h : ∀ᵐ ω ∂P, Λ ω ∈ C → V (Λ ω) ≤ liminf (fun n => U (Λ ω, Yn n ω)) atTop) :
    ∀ᵐ p ∂(ρ : Measure (L × Y)), p.1 ∈ C → V p.1 ≤ U p := by
  set F : ℚ → Set (L × Y) := fun q =>
    (Prod.fst ⁻¹' C)ᶜ ∪ {p | V p.1 ≤ ((Real.toNNReal q : ℝ≥0∞))} ∪
      {p | (Real.toNNReal q : ℝ≥0∞) ≤ U p} with hFdef
  have hFc : ∀ q, IsClosed (F q) := fun q =>
    ((hC.preimage continuous_fst).isClosed_compl.union
      (isClosed_le (hV.comp continuous_fst) continuous_const)).union
      (isClosed_le continuous_const hU)
  have hev : ∀ q, ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (Λ ω, Yn n ω) ∈ F q := fun q => by
    filter_upwards [h] with ω hω
    by_cases hC' : Λ ω ∈ C
    · by_cases hq : V (Λ ω) ≤ ((Real.toNNReal q : ℝ≥0∞))
      · exact Eventually.of_forall fun n => Or.inl (Or.inr hq)
      · have hlt : (Real.toNNReal q : ℝ≥0∞) < liminf (fun n => U (Λ ω, Yn n ω)) atTop :=
          (lt_of_not_ge hq).trans_le (hω hC')
        filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
        exact Or.inr hn.le
    · exact Eventually.of_forall fun n => Or.inl (Or.inl hC')
  filter_upwards [l6_ae_of_closed hZ hμs hlim hFc hev] with p hp hpC
  by_contra hn
  obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (lt_of_not_ge hn)
  rcases hp q with (hq | hq) | hq
  · exact hq hpC
  · exact absurd h2 (not_lt_of_ge hq)
  · exact absurd h1 (not_lt_of_ge hq)

 
theorem l6_ae_eq_zero_of_tendsto (hZ : ∀ n, Measurable fun ω => (Λ ω, Yn n ω))
    (hμs : ∀ n, (μs n : Measure (L × Y)) = P.map fun ω => (Λ ω, Yn n ω))
    (hlim : Tendsto μs atTop (𝓝 ρ)) {F : L × Y → ℝ} (hF : Continuous F)
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => F (Λ ω, Yn n ω)) atTop (𝓝 0)) :
    ∀ᵐ p ∂(ρ : Measure (L × Y)), F p = 0 := by
  set G : ℕ → Set (L × Y) := fun k => {p | |F p| ≤ 1 / ((k : ℝ) + 1)} with hGdef
  have hGc : ∀ k, IsClosed (G k) := fun k => isClosed_le hF.abs continuous_const
  have hev : ∀ k, ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (Λ ω, Yn n ω) ∈ G k := fun k => by
    filter_upwards [h] with ω hω
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h' : Tendsto (fun n => |F (Λ ω, Yn n ω)|) atTop (𝓝 0) := by
      simpa only [abs_zero] using hω.abs
    filter_upwards [h'.eventually (ge_mem_nhds hk)] with n hn
    exact hn
  filter_upwards [l6_ae_of_closed hZ hμs hlim hGc hev] with p hp
  refine abs_eq_zero.1 (le_antisymm ?_ (abs_nonneg _))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have h1 : |F p| ≤ 1 / ((k : ℝ) + 1) := hp k
  linarith

end Product

omit [IsProbabilityMeasure P] in
 
theorem l6_exists_subseq_ae {E : ℕ → Ω → ℝ}
    (h : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤ |E n ω|}) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => E (ψ n) ω) atTop (𝓝 0) := by
  have hT : TendstoInMeasure P E atTop (fun _ => (0 : ℝ)) := by
    intro ε hε
    by_cases hεt : ε = ∞
    · simp only [hεt, top_le_iff, edist_ne_top, ofPred_false, measure_empty]
      exact tendsto_const_nhds
    · have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
      refine (h ε.toReal hpos).congr fun n => ?_
      congr 1; ext ω
      simp only [mem_ofPred_eq, edist_dist, Real.dist_eq, sub_zero]
      exact (ENNReal.le_ofReal_iff_toReal_le hεt (abs_nonneg _)).symm
  obtain ⟨ψ, hψ, hae⟩ := hT.exists_seq_tendsto_ae
  exact ⟨ψ, hψ, hae⟩

omit [IsProbabilityMeasure P] in
 
theorem l6_tendsto_measure_add {E₁ E₂ : ℕ → Ω → ℝ}
    (h₁ : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤ |E₁ n ω|}) atTop (𝓝 0))
    (h₂ : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤ |E₂ n ω|}) atTop (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤ |E₁ n ω + E₂ n ω|}) atTop (𝓝 0) := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by positivity
  have hsum := (h₁ _ hδ2).add (h₂ _ hδ2)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => zero_le)
    (fun n => ?_)
  refine (measure_mono fun ω (hω : δ ≤ |E₁ n ω + E₂ n ω|) => ?_).trans (measure_union_le _ _)
  by_contra hn
  simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hn
  linarith [abs_add_le (E₁ n ω) (E₂ n ω)]

end SupercriticalLQGUniqueness.B2.PfeLocal
