/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibAssembly

/-!
# Identities on the glued space pass to almost every fibre

Packet PROVE-AUX61-FIB, the measure-theoretic transfer needed by pieces (F3) and (F4) of
`planning/handoffs/PROVE-AUX61-ACT.md` ("a 'conditional expectation in a disintegration' lemma: identities given
`σ(Z) ∨ Y⁻¹(σ_nat(stop))` ⇒ identities given the fibre's natural σ-algebra at the stop, for a.e. `x`"), and the
measurability of the code events `L i` of the cover.

* **`setIntegral_rect_eq`**: for a bounded measurable `h` on the code space, the set integral of `h ∘ Y` over a
  rectangle `{Z ∈ B} ∩ {Y ∈ A}` is the integral over `B` (under the law of `Z`) of the fibre set integrals over `A`;
* **`ae_setIntegral_condDistrib_eq_zero`**: if these rectangle integrals vanish for every history event `B`, the fibre
  set integral over `A` vanishes for almost every history value;
* **`ae_forall_setIntegral_condDistrib_eq_zero`**: if they vanish on a countable π-system `𝒜` (and on the whole code
  space), then for almost every history value the fibre set integral vanishes on **every** event of `σ(𝒜)` (Dynkin's
  π-λ theorem, `MeasurableSpace.induction_on_inter`). Applied to `h = (e^{i h(ψ)} − kernel) · 1_{disjoint}` and a
  countable π-system generating the fibre's natural σ-algebra at a stop, this is the passage of (F3)'s glued-space
  kernel identities to the fibres; applied to the projection identities, of (F4)'s member identities;
* **`measurableSet_visit`**: the codes whose path visits a closed set before the lifetime form a measurable set;
  **`measurableSet_visitIoo`**: the same for a real open interval (the code events `L i` of the cover).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Fib

/-! ### Rectangle integrals and the fibres -/

section Disint

variable {X β S : Type*} [MeasurableSpace X] [MeasurableSpace β] [mS : MeasurableSpace S] [StandardBorelSpace S]
  [Nonempty S] {μ : Measure X} [IsFiniteMeasure μ] {Z : X → β} {Y : X → S}

/-- **Rectangle set integrals disintegrate**: `∫_{Z ∈ B, Y ∈ A} h(Y) dμ = ∫_B (∫_A h dP_z) d(Z_* μ)(z)`, with
`P_z = condDistrib Y Z μ z`. -/
theorem setIntegral_rect_eq (hZ : Measurable Z) (hY : Measurable Y) {h : S → ℂ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ s, ‖h s‖ ≤ C) {B : Set β} (hB : MeasurableSet B) {A : Set S} (hA : MeasurableSet A) :
    ∫ x in Z ⁻¹' B ∩ Y ⁻¹' A, h (Y x) ∂μ = ∫ z in B, (∫ s in A, h s ∂(condDistrib Y Z μ z)) ∂(μ.map Z) := by
  have hZY : Measurable fun x => (Z x, Y x) := hZ.prodMk hY
  have e1 : ∫ x in Z ⁻¹' B ∩ Y ⁻¹' A, h (Y x) ∂μ =
      ∫ p in B ×ˢ A, h p.2 ∂(μ.map fun x => (Z x, Y x)) := by
    rw [setIntegral_map (f := fun p : β × S => h p.2) (hB.prod hA) (hh.comp measurable_snd).aestronglyMeasurable
      hZY.aemeasurable]
    rfl
  rw [e1, ← compProd_map_condDistrib hZ.aemeasurable hY.aemeasurable, Measure.setIntegral_compProd hB hA]
  refine Integrable.integrableOn ?_
  exact Integrable.of_bound (hh.comp measurable_snd).aestronglyMeasurable C (ae_of_all _ fun p => hC p.2)

/-- **Vanishing rectangle integrals vanish in almost every fibre.** -/
theorem ae_setIntegral_condDistrib_eq_zero (hZ : Measurable Z) (hY : Measurable Y) {h : S → ℂ} (hh : Measurable h)
    {C : ℝ} (hC : ∀ s, ‖h s‖ ≤ C) {A : Set S} (hA : MeasurableSet A)
    (H : ∀ B : Set β, MeasurableSet B → ∫ x in Z ⁻¹' B ∩ Y ⁻¹' A, h (Y x) ∂μ = 0) :
    ∀ᵐ x ∂μ, ∫ s in A, h s ∂(condDistrib Y Z μ (Z x)) = 0 := by
  set Φ : β → ℂ := fun z => ∫ s in A, h s ∂(condDistrib Y Z μ z) with hΦ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (Classical.arbitrary S))
  have hΦm : StronglyMeasurable Φ := by
    have hf : StronglyMeasurable fun p : β × S => A.indicator h p.2 :=
      ((hh.indicator hA).comp measurable_snd).stronglyMeasurable
    have := hf.integral_condDistrib (X := Z) (Y := Y) (μ := μ)
    convert this using 2 with z
    exact (integral_indicator hA).symm
  have hΦb : ∀ z, ‖Φ z‖ ≤ C := by
    intro z
    refine (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun s _ => hC s).trans ?_
    calc C * (condDistrib Y Z μ z A).toReal ≤ C * 1 :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal zero_le_one
            (by rw [ENNReal.ofReal_one]; exact prob_le_one)) hC0
      _ = C := mul_one C
  have hint : Integrable Φ (μ.map Z) := Integrable.of_bound hΦm.aestronglyMeasurable C (ae_of_all _ hΦb)
  have h0 : Φ =ᵐ[μ.map Z] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun _ _ _ => hint.integrableOn) fun B hB _ => ?_
    rw [← setIntegral_rect_eq hZ hY hh hC hB hA, H B hB]
  exact ae_of_ae_map hZ.aemeasurable h0

/-- **Vanishing on a countable π-system passes to the generated σ-algebra in almost every fibre**: if the rectangle
integrals of `h ∘ Y` vanish over `{Z ∈ B} ∩ {Y ∈ 𝒜 n}` and over `{Z ∈ B}` for every history event `B`, then for almost
every `x` the fibre set integral of `h` vanishes on every event of `σ(𝒜)`. -/
theorem ae_forall_setIntegral_condDistrib_eq_zero (hZ : Measurable Z) (hY : Measurable Y) {h : S → ℂ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ s, ‖h s‖ ≤ C) {𝒜 : ℕ → Set S} (h𝒜 : ∀ n, MeasurableSet (𝒜 n))
    (hpi : IsPiSystem (range 𝒜))
    (H : ∀ n, ∀ B : Set β, MeasurableSet B → ∫ x in Z ⁻¹' B ∩ Y ⁻¹' 𝒜 n, h (Y x) ∂μ = 0)
    (Huniv : ∀ B : Set β, MeasurableSet B → ∫ x in Z ⁻¹' B, h (Y x) ∂μ = 0) :
    ∀ᵐ x ∂μ, ∀ A : Set S, MeasurableSet[MeasurableSpace.generateFrom (range 𝒜)] A →
      ∫ s in A, h s ∂(condDistrib Y Z μ (Z x)) = 0 := by
  have h1 : ∀ᵐ x ∂μ, ∀ n, ∫ s in 𝒜 n, h s ∂(condDistrib Y Z μ (Z x)) = 0 :=
    ae_all_iff.2 fun n => ae_setIntegral_condDistrib_eq_zero hZ hY hh hC (h𝒜 n) (H n)
  have h2 : ∀ᵐ x ∂μ, ∫ s in univ, h s ∂(condDistrib Y Z μ (Z x)) = 0 :=
    ae_setIntegral_condDistrib_eq_zero hZ hY hh hC MeasurableSet.univ fun B hB => by
      simpa only [preimage_univ, inter_univ] using Huniv B hB
  have hle : MeasurableSpace.generateFrom (range 𝒜) ≤ mS :=
    MeasurableSpace.generateFrom_le (by rintro _ ⟨n, rfl⟩; exact h𝒜 n)
  filter_upwards [h1, h2] with x hx hxu
  set ν := condDistrib Y Z μ (Z x) with hν
  have hint : Integrable h ν := Integrable.of_bound hh.aestronglyMeasurable C (ae_of_all _ hC)
  intro A hA
  induction A, hA using MeasurableSpace.induction_on_inter (h_eq := rfl) (h_inter := hpi) with
  | empty => simp
  | basic t ht =>
    obtain ⟨n, rfl⟩ := ht
    exact hx n
  | compl t htm ht =>
    have e := integral_add_compl (hle t htm) hint
    have hall : ∫ s, h s ∂ν = 0 := by rw [← setIntegral_univ]; exact hxu
    rw [ht, zero_add, hall] at e
    exact e
  | iUnion f hd hfm hf =>
    rw [integral_iUnion (fun i => hle _ (hfm i)) hd hint.integrableOn]
    simp [hf]

end Disint

/-! ### Measurable visit events -/

section Visit

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
/-- The countable description of a visit to a closed set: for some horizon `N`, rational times in `[0, min(U, N)]`
approach the set. -/
theorem visit_closed_iff {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} (hc : ∀ x, Continuous (Γ x)) {K : Set ℂ}
    (hK : IsClosed K) (hKne : K.Nonempty) (x : S) :
    (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U x ∧ Γ x t ∈ K) ↔ ∃ N : ℕ, ∀ n : ℕ, ∃ q : ℚ,
      (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U x ∧ (q : ℝ).toNNReal ≤ (N : ℝ≥0) ∧
        infDist (Γ x (q : ℝ).toNNReal) K < 1 / ((n : ℝ) + 1) := by
  constructor
  · rintro ⟨t, htU, hK'⟩
    obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
    refine ⟨N, fun n => ?_⟩
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 (hc x) t _ hn
    obtain ⟨r, hrt, hrδ⟩ : ∃ r : ℚ, (r : ℝ).toNNReal ≤ t ∧ dist (r : ℝ).toNNReal t < δ := by
      rcases eq_or_lt_of_le t.coe_nonneg with h0 | hpos
      · refine ⟨0, by simp, ?_⟩
        have ht0 : t = 0 := by exact_mod_cast h0.symm
        simp [ht0, hδ]
      · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max 0 ((t : ℝ) - δ) < t from
          max_lt hpos (by linarith))
        have hr0 : (0 : ℝ) ≤ r := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hr1)
        refine ⟨r, ?_, ?_⟩
        · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact hr2.le
        · rw [NNReal.dist_eq, Real.coe_toNNReal _ hr0, abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith [le_max_right 0 ((t : ℝ) - δ)]
    refine ⟨r, (ENNReal.coe_le_coe.2 hrt).trans htU, hrt.trans (by exact_mod_cast hN), ?_⟩
    exact lt_of_le_of_lt ((infDist_le_dist_of_mem hK').trans_eq rfl) (hball _ hrδ)
  · rintro ⟨N, hN⟩
    choose q hq using hN
    set τ : ℕ → ℝ≥0 := fun n => ((q n : ℝ)).toNNReal with hτ
    set T : Set ℝ≥0 := Icc 0 (N : ℝ≥0) ∩ {t | (t : ℝ≥0∞) ≤ U x} with hT
    have hTc : IsCompact T :=
      isCompact_Icc.inter_right (isClosed_le ENNReal.continuous_coe continuous_const)
    have hτT : ∀ n, τ n ∈ T := fun n => ⟨⟨zero_le, (hq n).2.1⟩, (hq n).1⟩
    obtain ⟨t, htT, φ, hφ, hlim⟩ := hTc.tendsto_subseq hτT
    refine ⟨t, htT.2, ?_⟩
    have h1 : Tendsto (fun k => Γ x (τ (φ k))) atTop (𝓝 (Γ x t)) := ((hc x).tendsto t).comp hlim
    have h2 : Tendsto (fun k => infDist (Γ x (τ (φ k))) K) atTop (𝓝 0) := by
      have hz0 : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      exact squeeze_zero (fun k => infDist_nonneg) (fun k => (hq (φ k)).2.2.le) hz0
    have h3 : Tendsto (fun k => infDist (Γ x (τ (φ k))) K) atTop (𝓝 (infDist (Γ x t) K)) :=
      ((continuous_infDist_pt K).tendsto _).comp h1
    have hd : infDist (Γ x t) K = 0 := tendsto_nhds_unique h3 h2
    exact (hK.mem_iff_infDist_zero hKne).2 hd

/-- **Visiting a closed set before the lifetime is a measurable event.** -/
theorem measurableSet_visit {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} (hΓm : ∀ t, Measurable fun x => Γ x t)
    (hc : ∀ x, Continuous (Γ x)) (hU : Measurable U) {K : Set ℂ} (hK : IsClosed K) :
    MeasurableSet {x | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U x ∧ Γ x t ∈ K} := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · have e0 : {x | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U x ∧ Γ x t ∈ K} = ∅ := by
      ext x
      simp [hKe]
    rw [e0]
    exact MeasurableSet.empty
  have e : {x | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U x ∧ Γ x t ∈ K} = ⋃ N : ℕ, ⋂ n : ℕ, ⋃ q : ℚ,
      {x | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U x ∧ (q : ℝ).toNNReal ≤ (N : ℝ≥0) ∧
        infDist (Γ x (q : ℝ).toNNReal) K < 1 / ((n : ℝ) + 1)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    exact visit_closed_iff hc hK hKne x
  rw [e]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => ?_
  exact (measurableSet_le measurable_const hU).inter ((MeasurableSet.const _).inter
    (measurableSet_lt ((continuous_infDist_pt K).measurable.comp (hΓm _)) measurable_const))

/-- **Visiting a real open interval before the lifetime is a measurable event.** -/
theorem measurableSet_visitIoo {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} (hΓm : ∀ t, Measurable fun x => Γ x t)
    (hc : ∀ x, Continuous (Γ x)) (hU : Measurable U) (a b : ℝ) :
    MeasurableSet {x | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U x ∧ ∃ y ∈ Ioo a b, Γ x t = (y : ℂ)} := by
  let K : ℕ → Set ℂ := fun m => (fun y : ℝ => (y : ℂ)) '' Icc (a + 1 / ((m : ℝ) + 1)) (b - 1 / ((m : ℝ) + 1))
  have hK : ∀ m, IsClosed (K m) := fun m =>
    (isCompact_Icc.image Complex.continuous_ofReal).isClosed
  have e : {x | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U x ∧ ∃ y ∈ Ioo a b, Γ x t = (y : ℂ)} =
      ⋃ m : ℕ, {x | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U x ∧ Γ x t ∈ K m} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨t, ht, y, ⟨hay, hyb⟩, hy⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < min (y - a) (b - y) from lt_min (by linarith) (by linarith))
      refine ⟨m, t, ht, y, ⟨?_, ?_⟩, hy.symm⟩
      · linarith [min_le_left (y - a) (b - y)]
      · linarith [min_le_right (y - a) (b - y)]
    · rintro ⟨m, t, ht, y, ⟨hay, hyb⟩, hy⟩
      have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      exact ⟨t, ht, y, ⟨by linarith, by linarith⟩, hy.symm⟩
  rw [e]
  exact MeasurableSet.iUnion fun m => measurableSet_visit hΓm hc hU (hK m)

end Visit

end InteractingSLE.Sec5.Aux61Fib
