/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GNextGlued
import InteractingSLE.Spec.Sec5.Aux61GContWindow

/-! # Completing the access before selecting a buffered window -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61GNext
open Aux61GInst Aux61FibData Aux61GCont

/-- Complete a continuous pre-contact path by its given left-time limit.
This construction precedes window selection, so there is no circular use
of a window-dependent exit code to capture the complete segment. -/
theorem exists_continuous_access_completion {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤) {y : ℂ}
    (hendpoint : Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 y)) :
    ∃ γ : ℝ≥0 → ℂ, ContinuousOn γ (Iic (T x).toNNReal) ∧
      EqOn γ (inPath E c ρ T x) (Iio (T x).toNNReal) ∧
      γ 0 = 0 ∧ γ (T x).toNNReal = y ∧
      ∀ u : ℝ≥0, 0 < u → u < (T x).toNNReal → γ u ∈ H := by
  let e := (T x).toNNReal
  have he0 : 0 < e := ENNReal.toNNReal_pos hpos.ne' hfin.ne
  have heT : (e : ℝ≥0∞) = T x := ENNReal.coe_toNNReal hfin.ne
  have hcont : ContinuousOn (inPath E c ρ T x) (Iio e) :=
    (hs.continuousOn_inPath hx).mono fun u hu => by
      rw [← heT]
      exact ENNReal.coe_lt_coe.2 hu
  have hcl : Iic e ⊆ closure (Iio e) := by
    intro u hu
    rcases lt_or_eq_of_le (mem_Iic.1 hu) with hu | rfl
    · exact subset_closure hu
    · exact mem_closure_iff_nhdsWithin_neBot.2 (nhdsLT_neBot_of_exists_lt ⟨0, he0⟩)
  have hlim : ∀ u ∈ Iic e, ∃ z, Tendsto (inPath E c ρ T x) (𝓝[Iio e] u) (𝓝 z) := by
    intro u hu
    rcases lt_or_eq_of_le (mem_Iic.1 hu) with hu | rfl
    · exact ⟨inPath E c ρ T x u, hcont u hu⟩
    · exact ⟨y, hendpoint⟩
  let γ := extendFrom (Iio e) (inPath E c ρ T x)
  have hγ : EqOn γ (inPath E c ρ T x) (Iio e) := extendFrom_extends hcont
  refine ⟨γ, continuousOn_extendFrom hcl hlim, hγ, ?_, ?_, ?_⟩
  · exact (hγ he0).trans (hs.inPath_zero hx hpos)
  · have : (𝓝[<] e).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, he0⟩
    exact hendpoint.limUnder_eq
  · intro u hu0 hue
    rw [hγ hue, hs.inPath_eq_fwd hx hu0 (heT ▸ ENNReal.coe_lt_coe.2 hue)]
    exact (hs.conf x hx).fwd_mem (hs.inside x hx u hu0 (heT ▸ ENNReal.coe_lt_coe.2 hue))

/-- An actual finite nonzero real access limit yields the physical
completed-window capture premises used by the fibre-cover adapter. This
is pointwise geometry; history-measurable localization is a separate step. -/
theorem exists_captured_window_of_access_limit {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤) {y : ℝ} (hy : y ≠ 0)
    (hendpoint : Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)))
    {O : Set ℝ} (hO : IsOpen O) (hO0 : 0 ∈ O) (hOy : y ∈ O) :
    ∃ V U : Set ℂ, IsOpen V ∧ IsOpen U ∧ (0 : ℂ) ∈ V ∧ V ⊆ U ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < T x → inPath E c ρ T x u ∈ V) ∧
      (y : ℂ) ∉ V ∧ IsCompact (closure U) ∧
      (∀ z ∈ closure U, z.im = 0 → z.re ∈ O) ∧
      Aux61FibData.exitTime E c ρ T V x = T x := by
  obtain ⟨γ, hγc, hγeq, hγ0, hγend, hγH⟩ := exists_continuous_access_completion hs hx hpos hfin hendpoint
  obtain ⟨V, U, hVo, hUo, hV0, hVU, -, hbefore, hyV, hUc, hUr⟩ :=
    exists_window_of_completed_segment hγc hγ0 hγH hγend (abs_pos.2 hy) le_rfl hO hO0 hOy
  have hin : ∀ u : ℝ≥0, (u : ℝ≥0∞) < T x → inPath E c ρ T x u ∈ V := by
    intro u hu
    have hue : u < (T x).toNNReal := by
      rw [← ENNReal.coe_toNNReal hfin.ne] at hu
      exact ENNReal.coe_lt_coe.1 hu
    rw [← hγeq hue]
    exact hbefore u hue
  exact ⟨V, U, hVo, hUo, hV0, hVU, hin, hyV, hUc, hUr, exitTime_eq_of_before_mem hs hVo hx hin⟩

end InteractingSLE.Sec5.Aux61GNext
