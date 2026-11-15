/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Asm2Build
import InteractingSLE.Spec.Sec5.Aux61RestartBdryApply

/-! # The source history-cover field from R1's clearance-piece selection

The actual source window event lies in the geometric restart configuration
almost surely, using the transferred good-hitting certificate. Its exact
countable clearance cover then reduces `history_cover` to the selected
records' matching with those pieces. No future capture is made past measurable.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GR1F
open Aux61Asm2 Aux61SlitW Aux61SlitW.SourceSetting Aux61Restart
open LawUnique GlueCond CrossCond.Theta Prop411Q
universe u

/-- The good-hitting certificate holds on the source's actual glued law. -/
theorem ae_source_goodHit (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ, p.2 ∈ goodHitSet := by
  have hg := cfGlueAE_mem_goodHitSetT S.θ S.κ S.κ_pos S.κ_lt_four S.xL S.xR S.ρL S.ρR
    (Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data S.a S.b) {0} 0)
    S.cond44 S.theta_bounds S.P S.own.filt S.own.W S.own.VL S.own.VR S.own.noise S.life S.ownField
    S.own.coupling S.P₂ S.field₂ S.W₂ S.life₂ S.counterflow S.theta_field_law S.kernel S.kernel_law
  rwa [← S.theta_measure] at hg

/-- The source's actual window event has R1's configuration, with no
additional geometric hypothesis on the source setting. -/
theorem ae_source_window_configuration (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → p ∈ restartConfigurationEvent (rationalTime S.s) (rationalTime S.t) S.t
      (fun p : S.Ω × HistorySpace 0 0 => p.2) (fun (p : S.Ω × HistorySpace 0 0) (t : ℝ) => S.path p.1 t.toNNReal)
      (fun t p => S.own.W t p.1) := by
  filter_upwards [S.physical_path, ae_source_goodHit S] with p hp hg hwin
  have hs : ((rationalTime S.s : ℝ≥0) : ℝ) = (S.s : ℝ) :=
    Real.coe_toNNReal _ (by exact_mod_cast S.s_pos.le)
  have hwin' := hwin
  change Aux61Kernel.RestartWindowEvent (cfDrv p.2) (S.s : ℝ)
    (fun t : ℝ => S.path p.1 t.toNNReal) S.t S.windowCode at hwin'
  rw [← hs] at hwin'
  exact mem_restartConfigurationEvent_of_cfDrv_window
    (Real.coe_toNNReal _ (by exact_mod_cast S.t_pos.le)) hp.1.continuous hp.1.2.1 hp.2.1 hp.2.2 hg hwin'

/-- The exact source history-cover field once the chosen record family
matches the already constructed countable R1 clearance pieces. -/
theorem history_cover_of_clearance_selection {S : SourceSetting.{u}}
    (D : R1Restart S) (h : D.HasChart)
    (hselected_of_clearance : ∀ n : ℕ, ∀ p : S.Ω × HistorySpace 0 0,
      p ∈ restartClearancePiece (rationalTime S.s) (rationalTime S.t) S.t
        (fun p : S.Ω × HistorySpace 0 0 => p.2) (fun (p : S.Ω × HistorySpace 0 0) (t : ℝ) => S.path p.1 t.toNNReal)
        (fun t p => S.own.W t p.1) n → ∃ i,
      sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ D.selected i) :
    ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i,
      sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ D.selected i := by
  filter_upwards [ae_source_window_configuration S] with p hp hwin
  have hmem := hp hwin
  rw [restartConfigurationEvent_eq_iUnion_clearancePiece
    (show 0 < (S.t : ℝ) by exact_mod_cast S.t_pos), mem_iUnion] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact hselected_of_clearance n p hn

end InteractingSLE.Sec5.Aux61GR1F
