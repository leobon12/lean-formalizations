import SupercriticalLQGUniqueness.B2.PfeLocal.L6Sandwich
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

 


















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SupercriticalLQGUniqueness.B2.PfeLocal

section Lusin

variable {α E Ω : Type*} [TopologicalSpace α] [NormalSpace α] [MeasurableSpace α] [BorelSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω]

 
def l6Trunc (T : α → E) (M : ℝ) : α → E := fun a => if ‖T a‖ ≤ M then T a else 0

theorem measurable_l6Trunc {T : α → E} (hT : Measurable T) (M : ℝ) : Measurable (l6Trunc T M) :=
  Measurable.ite (measurableSet_le hT.norm measurable_const) hT measurable_const

theorem l6Trunc_norm_le (T : α → E) {M : ℝ} (hM : 0 ≤ M) (a : α) : ‖l6Trunc T M a‖ ≤ M := by
  unfold l6Trunc
  split_ifs with h
  · exact h
  · simpa using hM

 
theorem l6_measure_le_of_map {P : Measure Ω} {μ : Measure α} {Y : Ω → α} (hY : Measurable Y)
    (hlaw : P.map Y = μ) {g : α → ℝ≥0∞} (hg : Measurable g) (c : ℝ≥0∞) :
    P {ω | c ≤ g (Y ω)} = μ {a | c ≤ g a} := by
  rw [← hlaw, Measure.map_apply hY (measurableSet_le measurable_const hg)]
  rfl

theorem l6_tendstoInMeasure_comp {μ : Measure α} [IsProbabilityMeasure μ] [μ.WeaklyRegular]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → α) (Y₀ : Ω → α)
    (hY : ∀ n, Measurable (Y n)) (hY₀ : Measurable Y₀) (hlaw : ∀ n, P.map (Y n) = μ)
    (hlaw₀ : P.map Y₀ = μ) (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y₀ ω)))
    (T : α → E) (hT : Measurable T) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => P {ω | ENNReal.ofReal δ ≤ ‖T (Y n ω) - T (Y₀ ω)‖ₑ}) atTop (𝓝 0) := by
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  
  have hM : Tendsto (fun M : ℕ => μ {a | (M : ℝ) < ‖T a‖}) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun M : ℕ => {a | (M : ℝ) < ‖T a‖})
      (fun M => (measurableSet_lt measurable_const hT.norm).nullMeasurableSet)
      (fun M M' hMM' a (ha : (M' : ℝ) < ‖T a‖) =>
        show (M : ℝ) < ‖T a‖ from lt_of_le_of_lt (by exact_mod_cast hMM') ha)
      ⟨0, measure_ne_top _ _⟩
    have he : ⋂ M : ℕ, {a | (M : ℝ) < ‖T a‖} = ∅ := by
      ext a
      simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨M, hM⟩ := exists_nat_ge ‖T a‖
      exact ⟨M, hM⟩
    rw [he, measure_empty] at h
    exact h
  have hκ8 : 0 < κ / 8 := ENNReal.div_pos hκ.ne' (by norm_num)
  obtain ⟨M, hMsmall⟩ := (hM.eventually (gt_mem_nhds hκ8)).exists
  set TM := l6Trunc T M
  have hTM : Measurable TM := measurable_l6Trunc hT M
  have hTMb : ∀ a, ‖TM a‖ ≤ M := l6Trunc_norm_le T (Nat.cast_nonneg M)
  have hTMLp : MemLp TM 1 μ := MemLp.of_bound hTM.aestronglyMeasurable M
    (Eventually.of_forall hTMb)
  
  set ε : ℝ≥0∞ := ENNReal.ofReal (δ / 3) * (κ / 8)
  have hε : ε ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne'
    (ENNReal.div_pos hκ.ne' (by norm_num)).ne'
  obtain ⟨S, hS, -⟩ := hTMLp.exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top hε
  
  have hdiff : Measurable fun a => ‖TM a - S a‖ₑ :=
    (hTM.sub S.continuous.measurable).enorm
  have hint : ∫⁻ a, ‖TM a - S a‖ₑ ∂μ ≤ ε := by
    rw [eLpNorm_one_eq_lintegral_enorm] at hS
    exact hS
  have hmarkov : μ {a | ENNReal.ofReal (δ / 3) ≤ ‖TM a - S a‖ₑ} ≤ κ / 8 := by
    have h := mul_meas_ge_le_lintegral₀ (μ := μ) hdiff.aemeasurable (ENNReal.ofReal (δ / 3))
    have hpos : ENNReal.ofReal (δ / 3) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    calc μ {a | ENNReal.ofReal (δ / 3) ≤ ‖TM a - S a‖ₑ}
        = (ENNReal.ofReal (δ / 3))⁻¹ * (ENNReal.ofReal (δ / 3) *
            μ {a | ENNReal.ofReal (δ / 3) ≤ ‖TM a - S a‖ₑ}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hpos ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal (δ / 3))⁻¹ * ε := by gcongr; exact h.trans hint
      _ = κ / 8 := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hpos ENNReal.ofReal_ne_top, one_mul]
  have hbad : μ {a | TM a ≠ T a} ≤ κ / 8 := by
    refine (measure_mono fun a ha => ?_).trans hMsmall.le
    by_contra hle
    rw [mem_setOf_eq, not_lt] at hle
    exact ha (by simp only [TM, l6Trunc, if_pos hle])
  
  have hmid : Tendsto (fun n => P {ω | ENNReal.ofReal (δ / 3) ≤ ‖S (Y n ω) - S (Y₀ ω)‖ₑ})
      atTop (𝓝 0) := by
    have hae : ∀ᵐ ω ∂P, Tendsto (fun n => S (Y n ω)) atTop (𝓝 (S (Y₀ ω))) :=
      hconv.mono fun ω hω => (S.continuous.tendsto _).comp hω
    have htm := tendstoInMeasure_of_tendsto_ae
      (fun n => (S.continuous.measurable.comp (hY n)).aestronglyMeasurable) hae
    exact htm (ENNReal.ofReal (δ / 3)) (ENNReal.ofReal_pos.2 (by positivity)) |>.congr fun n => by
      congr 1; ext ω; simp [edist_eq_enorm_sub]
  have hfin := (ENNReal.tendsto_nhds_zero.1 hmid) (κ / 8) hκ8
  filter_upwards [hfin] with n hn
  
  set A := {ω | TM (Y n ω) ≠ T (Y n ω)}
  set B := {ω | TM (Y₀ ω) ≠ T (Y₀ ω)}
  set C₁ := {ω | ENNReal.ofReal (δ / 3) ≤ ‖TM (Y n ω) - S (Y n ω)‖ₑ}
  set C₂ := {ω | ENNReal.ofReal (δ / 3) ≤ ‖S (Y n ω) - S (Y₀ ω)‖ₑ}
  set C₃ := {ω | ENNReal.ofReal (δ / 3) ≤ ‖TM (Y₀ ω) - S (Y₀ ω)‖ₑ}
  have hsub : {ω | ENNReal.ofReal δ ≤ ‖T (Y n ω) - T (Y₀ ω)‖ₑ} ⊆ A ∪ B ∪ C₁ ∪ C₂ ∪ C₃ := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, not_or, A, B, C₁, C₂, C₃, mem_setOf_eq, not_not, not_le] at hnot
    obtain ⟨⟨⟨⟨hA, hB⟩, h1⟩, h2⟩, h3⟩ := hnot
    rw [mem_setOf_eq, ← hA, ← hB] at hω
    have htri : ‖TM (Y n ω) - TM (Y₀ ω)‖ₑ ≤ ‖TM (Y n ω) - S (Y n ω)‖ₑ +
        ‖S (Y n ω) - S (Y₀ ω)‖ₑ + ‖S (Y₀ ω) - TM (Y₀ ω)‖ₑ := by
      have h3 : ‖(TM (Y n ω) - S (Y n ω)) + (S (Y n ω) - S (Y₀ ω)) + (S (Y₀ ω) - TM (Y₀ ω))‖ₑ ≤
          ‖TM (Y n ω) - S (Y n ω)‖ₑ + ‖S (Y n ω) - S (Y₀ ω)‖ₑ + ‖S (Y₀ ω) - TM (Y₀ ω)‖ₑ :=
        enorm_add₃_le
      have e : (TM (Y n ω) - S (Y n ω)) + (S (Y n ω) - S (Y₀ ω)) + (S (Y₀ ω) - TM (Y₀ ω)) =
          TM (Y n ω) - TM (Y₀ ω) := by abel
      rwa [e] at h3
    rw [enorm_sub_rev (S (Y₀ ω))] at htri
    have : ‖TM (Y n ω) - TM (Y₀ ω)‖ₑ < ENNReal.ofReal δ := by
      calc _ ≤ _ := htri
        _ < ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) :=
            ENNReal.add_lt_add (ENNReal.add_lt_add h1 h2) h3
        _ = ENNReal.ofReal δ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            ring_nf
    exact (not_le_of_gt this) hω
  have hmne : MeasurableSet {a | TM a ≠ T a} := (measurableSet_eq_fun hTM hT).compl
  have hA : P A ≤ κ / 8 := by
    have : P A = μ {a | TM a ≠ T a} := by
      rw [← hlaw n, Measure.map_apply (hY n) hmne]
      rfl
    rw [this]; exact hbad
  have hB : P B ≤ κ / 8 := by
    have : P B = μ {a | TM a ≠ T a} := by
      rw [← hlaw₀, Measure.map_apply hY₀ hmne]
      rfl
    rw [this]; exact hbad
  have hC₁ : P C₁ ≤ κ / 8 := by
    rw [l6_measure_le_of_map (hY n) (hlaw n) hdiff]; exact hmarkov
  have hC₃ : P C₃ ≤ κ / 8 := by
    rw [l6_measure_le_of_map hY₀ hlaw₀ hdiff]; exact hmarkov
  calc P {ω | ENNReal.ofReal δ ≤ ‖T (Y n ω) - T (Y₀ ω)‖ₑ}
      ≤ P (A ∪ B ∪ C₁ ∪ C₂ ∪ C₃) := measure_mono hsub
    _ ≤ P A + P B + P C₁ + P C₂ + P C₃ := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ κ / 8 + κ / 8 + κ / 8 + κ / 8 + κ / 8 := by gcongr
    _ ≤ κ / 8 + κ / 8 + κ / 8 + κ / 8 + κ / 8 + (κ / 8 + κ / 8 + κ / 8) := le_self_add
    _ = 8 * (κ / 8) := by ring
    _ = κ := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end Lusin

end SupercriticalLQGUniqueness.B2.PfeLocal
