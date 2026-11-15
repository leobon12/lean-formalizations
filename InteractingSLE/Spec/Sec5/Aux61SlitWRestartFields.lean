/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWAccessFields

/-! # Injectivity of the actual physical restart, including its initial time -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW

/-- A continuous restart agreeing with the physical shift at positive
pre-contact times also agrees at time zero whenever that time is live. -/
theorem restart_eq_shift_of_pos {ρ : ℝ≥0 → ℂ} {η : ℝ → ℂ} {r : ℝ≥0} {T : ℝ≥0∞}
    (hρ : Continuous ρ) (hη : ContinuousOn η (Ici 0))
    (hversion : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T → ρ u = η (r + (u : ℝ))) :
    ∀ u : ℝ≥0, (u : ℝ≥0∞) < T → ρ u = η (r + (u : ℝ)) := by
  have hc : Continuous (fun u : ℝ≥0 => η (r + (u : ℝ))) :=
    hη.comp_continuous (continuous_const.add NNReal.continuous_coe)
      (fun u => add_nonneg r.coe_nonneg u.coe_nonneg)
  intro u huT
  by_cases hu : u = 0
  · subst u
    obtain ⟨ε, hε, hεT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 huT
    have hε0 : (0 : ℝ≥0) < ε := ENNReal.coe_lt_coe.1 hε
    have heq : EqOn ρ (fun u : ℝ≥0 => η (r + (u : ℝ))) (Ioo 0 ε) :=
      fun v hv => hversion v hv.1 ((ENNReal.coe_lt_coe.2 hv.2).trans hεT)
    have hcl := heq.closure hρ hc
    rw [closure_Ioo hε0.ne] at hcl
    exact hcl ⟨le_rfl, hε0.le⟩
  · exact hversion u (pos_iff_ne_zero.2 hu) huT

/-- The physical simple arc supplies restart injectivity before contact.
No injectivity of a chosen version at time zero is an extra assumption. -/
theorem injOn_restart_of_pos_version {ρ : ℝ≥0 → ℂ} {η : ℝ → ℂ} {r : ℝ≥0} {T : ℝ≥0∞}
    (hρ : Continuous ρ) (hη : ContinuousOn η (Ici 0)) (hi : InjOn η (Ici 0))
    (hversion : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T → ρ u = η (r + (u : ℝ))) :
    InjOn ρ {u | (u : ℝ≥0∞) < T} := by
  intro u hu v hv heq
  rw [restart_eq_shift_of_pos hρ hη hversion u hu,
    restart_eq_shift_of_pos hρ hη hversion v hv] at heq
  have he := hi (add_nonneg r.coe_nonneg u.coe_nonneg)
    (add_nonneg r.coe_nonneg v.coe_nonneg) heq
  exact NNReal.coe_injective (add_left_cancel he)

/-- Continuity identifies the actual physical value at a finite positive
contact, even though the version was specified only before contact. -/
theorem restart_eq_shift_at_contact {ρ : ℝ≥0 → ℂ} {η : ℝ → ℂ} {r : ℝ≥0} {T : ℝ≥0∞}
    (hρ : Continuous ρ) (hη : ContinuousOn η (Ici 0)) (hpos : 0 < T) (hfin : T < ⊤)
    (hversion : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T → ρ u = η (r + (u : ℝ))) :
    ρ T.toNNReal = η (r + (T.toNNReal : ℝ)) := by
  have hc : Continuous (fun u : ℝ≥0 => η (r + (u : ℝ))) :=
    hη.comp_continuous (continuous_const.add NNReal.continuous_coe)
      (fun u => add_nonneg r.coe_nonneg u.coe_nonneg)
  have he0 : 0 < T.toNNReal := ENNReal.toNNReal_pos hpos.ne' hfin.ne
  have heq : EqOn ρ (fun u : ℝ≥0 => η (r + (u : ℝ))) (Ioo 0 T.toNNReal) := by
    intro u hu
    apply hversion u hu.1
    rw [← ENNReal.coe_toNNReal hfin.ne]
    exact ENNReal.coe_lt_coe.2 hu.2
  have hcl := heq.closure hρ hc
  rw [closure_Ioo he0.ne] at hcl
  exact hcl ⟨he0.le, le_rfl⟩

/-- A finite contact of a restarted proper interior flow line cannot be
the original real target. This removes a separate endpoint hypothesis. -/
theorem restart_contact_ne_target {ρ : ℝ≥0 → ℂ} {η : ℝ → ℂ} {r : ℝ≥0} {T : ℝ≥0∞}
    (hρ : Continuous ρ) (harc : WangWu.IsProperArc η) (hpos : 0 < T) (hfin : T < ⊤)
    (hversion : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T → ρ u = η (r + (u : ℝ))) :
    ρ T.toNNReal ≠ 1 := by
  rw [restart_eq_shift_at_contact hρ harc.cont hpos hfin hversion]
  have he0 : (0 : ℝ) < T.toNNReal := NNReal.coe_pos.2 (ENNReal.toNNReal_pos hpos.ne' hfin.ne)
  have hH := harc.mem_H _ (add_pos_of_nonneg_of_pos r.coe_nonneg he0)
  intro heq
  rw [heq] at hH
  exact (lt_irrefl (0 : ℝ)) hH

end InteractingSLE.Sec5.Aux61SlitW
