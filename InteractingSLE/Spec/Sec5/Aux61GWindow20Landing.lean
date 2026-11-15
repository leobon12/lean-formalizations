/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptLandAccess
import InteractingSLE.Spec.Sec5.Aux61GWindow20Contact

/-! # The window excursion in the retained counterflow driver

Keep both the interior excursion and its landing, in the same retained
driver as the Borel landing test.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow20
open WangWu Aux61SlitW Aux61Asm2 Aux61Cpt Aux61Cmp GlueCond LawUnique CrossCond.Word49
universe u

/-- The source window supplies a positive counterflow coordinate and the
entire preceding physical excursion, read with the retained driver. -/
theorem ae_retained_window_landing (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ, S.windowEvent p →
    ∃ e x : ℝ, (S.t : ℝ) < e ∧ 0 < x ∧
      (∀ v ∈ Ioo (S.t : ℝ) e,
        S.path p.1 v.toNNReal ∈ H \ negInv '' fwdHull (cfW S p) (rationalTime S.s)) ∧
      Tendsto (fun v : ℝ => revChart (cfW S p) (rationalTime S.s) (S.path p.1 v.toNNReal))
        (𝓝[<] e) (𝓝 (x : ℂ)) ∧
      cfBdry (cfW S p) (rationalTime S.s) x = S.path p.1 e.toNNReal := by
  filter_upwards [S.physical_path, Aux61Asm2.ae_mem_goodCfSet S, ae_cfW_trace S]
    with p hp hg hcf hwin
  obtain ⟨hW, e, he, -⟩ := hwin
  have hexc := he
  obtain ⟨-, -, hte, hin, x, hland⟩ := he
  obtain ⟨hw0, γ, hγ⟩ := hcf
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hw' : Continuous (Prop411Q.cfDrv p.2) := (CfRegQ.reg_of_mem_goodCfSet hg).2.1
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hsq : (rationalTime S.s : ℝ) = (S.s : ℝ) := Aux61R1C.coe_rationalTime S.s_pos.le
  have hmem := Aux61Kernel.WindowExcursion.landing_mem hW hexc hland
  have hx : 0 < x := (Aux61Kernel.junR_nonneg hw' (by exact_mod_cast S.s_pos.le)).trans_lt
    (hW.east.trans hmem.1)
  have hK : Prop51G.cfHullQ (Prop411Q.cfDrv p.2) S.s =
      negInv '' fwdHull (cfW S p) (rationalTime S.s) := by
    rw [← cfHullQ_eq_cfW S hg, cfHullQ_eq_of_mem_goodCfSet hg, hsq]
    rfl
  have hD : ∀ v ∈ Ioo (S.t : ℝ) e,
      S.path p.1 v.toNNReal ∈ H \ negInv '' fwdHull (cfW S p) (rationalTime S.s) := by
    intro v hv
    rw [← hK]
    exact (hin v hv).1
  have hchart : ∀ z : ℂ, revChart (cfW S p) (rationalTime S.s) z =
      revChart (Prop411Q.cfDrv p.2) S.s z := by
    intro z
    have heq := QuantumZipper.CharFunRhs.fwdMap_eq_of_eqOn (eqOn_cfW_cfDrv S hg)
    dsimp only [revChart]
    rw [heq, hsq]
  have hl : Tendsto (fun v : ℝ => revChart (cfW S p) (rationalTime S.s)
      (S.path p.1 v.toNNReal)) (𝓝[<] e) (𝓝 (x : ℂ)) :=
    hland.congr fun v => (hchart _).symm
  exact ⟨e, x, hte, hx, hD, hl, cfBdry_eq_of_landing hp.2.2 hw hw0 hγ hs
    (by exact_mod_cast S.t_pos.le) hte hD hx.ne' hl⟩

end InteractingSLE.Sec5.Aux61GWindow20
