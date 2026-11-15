/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GlueTrace
import InteractingSLE.Spec.Restart.ClockTrace

/-!
# Interior trace times pulled back through a capacity clock

Packet PROVE-T14-GW2ROOT2. The intermediate value theorem and the existing
density of interior generating-trace times supply density in physical time.
No boundary extension of the chart or zero occupation assumption is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE13

open Restart

/-- Every nontrivial physical interval contains a time whose clock image
is an interior time of the relative generating trace. -/
theorem exists_clock_mem_H_between {a : ℝ≥0 → ℝ} {p q : ℝ≥0}
    (hpq : p < q) (hac : ContinuousOn a (Icc p q))
    (hsm : StrictMonoOn a (Icc p q)) (hnn : 0 ≤ a p)
    {w : ℝ≥0 → ℝ} {Γ : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace w ⊤ Γ)
    (hw : Continuous w) (hw0 : w 0 = 0) :
    ∃ r ∈ Ioo p q, Γ (a r).toNNReal ∈ H := by
  have hp : p ∈ Icc p q := ⟨le_rfl, hpq.le⟩
  have hq : q ∈ Icc p q := ⟨hpq.le, le_rfl⟩
  have hapq : a p < a q := hsm hp hq hpq
  have hnq : 0 ≤ a q := hnn.trans hapq.le
  have hab : (a p).toNNReal < (a q).toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hnn, Real.coe_toNNReal _ hnq]
    exact hapq
  obtain ⟨u, hu, huH⟩ := Restart.IsGeneratingTrace.exists_mem_H hΓ hw.continuousOn hw0 hab le_top
  have hu1 : a p < (u : ℝ) := by
    have := NNReal.coe_lt_coe.mpr hu.1
    rwa [Real.coe_toNNReal _ hnn] at this
  have hu2 : (u : ℝ) < a q := by
    have := NNReal.coe_lt_coe.mpr hu.2
    rwa [Real.coe_toNNReal _ hnq] at this
  obtain ⟨r, hr, her⟩ := intermediate_value_Icc hpq.le hac ⟨hu1.le, hu2.le⟩
  have hpr : p < r := lt_of_le_of_ne hr.1 (fun he => by
    have : a p = (u : ℝ) := he.symm ▸ her
    exact hu1.ne this)
  have hrq : r < q := lt_of_le_of_ne hr.2 (fun he => by
    have : a q = (u : ℝ) := he ▸ her
    exact hu2.ne this.symm)
  refine ⟨r, ⟨hpr, hrq⟩, ?_⟩
  simpa only [her, Real.toNNReal_coe] using huH

/-- Before contact, every physical time is a limit of times whose relative
trace tip is in the open upper half-plane. -/
theorem mem_closure_clock_mem_H {a : ℝ≥0 → ℝ} {Tc : ℝ≥0∞}
    (hac : ContinuousOn a {r | (r : ℝ≥0∞) < Tc})
    (hsm : StrictMonoOn a {r | (r : ℝ≥0∞) < Tc})
    (hnn : ∀ r : ℝ≥0, (r : ℝ≥0∞) < Tc → 0 ≤ a r)
    {w : ℝ≥0 → ℝ} {Γ : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace w ⊤ Γ)
    (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < Tc) :
    t ∈ closure {r : ℝ≥0 | (r : ℝ≥0∞) < Tc ∧ Γ (a r).toNNReal ∈ H} := by
  obtain ⟨v, htv, hvT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ht
  have htv' : t < v := ENNReal.coe_lt_coe.mp htv
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  let q : ℝ≥0 := min v (t + (ε / 2).toNNReal)
  have hhalf : 0 < (ε / 2).toNNReal := Real.toNNReal_pos.mpr (half_pos hε)
  have htq : t < q := lt_min htv' (lt_add_of_pos_right t hhalf)
  have hqT : (q : ℝ≥0∞) < Tc :=
    (ENNReal.coe_le_coe.mpr (min_le_left _ _)).trans_lt hvT
  have hsub : Icc t q ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) < Tc} :=
    fun r hr => (ENNReal.coe_le_coe.mpr hr.2).trans_lt hqT
  obtain ⟨r, hr, hrH⟩ := exists_clock_mem_H_between htq (hac.mono hsub)
    (hsm.mono hsub) (hnn t ht) hΓ hw hw0
  refine ⟨r, ⟨hsub ⟨hr.1.le, hr.2.le⟩, hrH⟩, ?_⟩
  rw [dist_comm, NNReal.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hr.1.le))]
  have hrq : (r : ℝ) < (q : ℝ) := NNReal.coe_lt_coe.mpr hr.2
  have hq : (q : ℝ) ≤ (t : ℝ) + ε / 2 := by
    have := NNReal.coe_le_coe.mpr (min_le_right v (t + (ε / 2).toNNReal))
    simpa only [NNReal.coe_add, Real.coe_toNNReal _ (half_pos hε).le] using this
  linarith

end InteractingSLE.Theorem14.GW2TipSystem.RootE13
