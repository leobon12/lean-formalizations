/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwCPiece
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# The physical set of a live switched schedule is the translated joined trace

Packet PROVE-GW2-SWITCH (round 3). If a continuous driver `J` agrees up to time `T` with a driver
that generates a trace `γ` on `[0, ∞)`, the radial tips of `J` at times in `[0, T]` are exactly
`γ([0, T])` (`radialTips_eq_image`). With `Swc.physSet_eq_radialTips` and
`SwC.exists_trace_joinDrv`, the physical set of a live GW2 schedule of regular traced pieces is the
root plus the image of one continuous trace (`physSet_eq_trace_image`): the multi-piece carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Theorem14.GW2TipSystem.SwC

open GW2Schedule Exist Staged StagedLaw Swc

/-- **Radial tips of a driver agreeing with a trace-generating driver are the trace points.** -/
theorem radialTips_eq_image {J : ℝ → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0)
    {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) {T : ℝ} (hT : 0 ≤ T)
    (hag : ∀ t : ℝ≥0, (t : ℝ) ≤ T → W t = J t) :
    radialTips J 0 T = γ '' Icc 0 T.toNNReal := by
  have hWr : Continuous (fun s : ℝ => W s.toNNReal) := hW.comp continuous_real_toNNReal
  have hWr0 : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simp [hW0]
  have hlim : ∀ s : ℝ, 0 ≤ s → s ≤ T →
      Tendsto (fun y : ℝ => fwdMapInv J s ((y : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 (γ s.toNNReal)) := by
    intro s hs0 hsT
    have htip := hγ.tendsto_fwdMapInv_tip hW.continuousOn hW0
      (show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
    rw [Real.coe_toNNReal _ hs0] at htip
    refine (htip.comp tendsto_ofReal_mul_I_nhdsWithin_H).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyH : (y : ℂ) * Complex.I ∈ H := by
      change 0 < ((y : ℂ) * Complex.I).im
      simpa using hy
    refine LP.fwdMapInv_eq_of_eqOn_Icc hWr hJ hWr0 hJ0 hs0 (fun r hr => ?_) hyH
    have hr0 : (0 : ℝ) ≤ r := hr.1
    have h := hag r.toNNReal (by rw [Real.coe_toNNReal _ hr0]; exact hr.2.trans hsT)
    rw [Real.coe_toNNReal _ hr0] at h
    exact h
  ext z
  constructor
  · rintro ⟨s, hs0, hsT, hz⟩
    refine ⟨s.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hsT⟩, ?_⟩
    exact tendsto_nhds_unique (hlim s hs0 hsT) hz
  · rintro ⟨u, hu, rfl⟩
    have huT : (u : ℝ) ≤ T := by
      have h := NNReal.coe_le_coe.2 hu.2
      rwa [Real.coe_toNNReal _ hT] at h
    refine ⟨u, u.2, huT, ?_⟩
    have h := hlim u u.2 huT
    rwa [Real.toNNReal_coe] at h

/-- **The multi-piece carrier**: for a live GW2 flow program whose pieces are regular drivers with
generating traces, the physical set is the root translate of `γ([0, T])` for one generating trace `γ`
on `[0, ∞)` of a continuous driver agreeing with the joined driver up to the total time `T`. -/
theorem physSet_eq_trace_image {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {Δ : ℕ → ℝ≥0∞} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hgw : spec.2.1 = true) {θ : ℕ → ℝ} (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    {n : ℕ} (hn : spec.2.2.length = n + 1) (hs : AllSucc Δ D (n + 1))
    (he : ∀ j < n + 1, IsRegularDriver (D j))
    (hα : ∀ j < n + 1, ∃ α : ℝ≥0 → ℂ, IsGeneratingTrace (D j).1 (D j).2 α)
    (hc : ∀ i < n + 1, Continuous (stopDrv (Δ i) (D i)) ∧ stopDrv (Δ i) (D i) 0 = 0) :
    ∃ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W ∧ W 0 = 0 ∧ IsGeneratingTrace W ⊤ γ ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ joinTime Δ D (n + 1) → W t = joinDrv Δ D (n + 1) t) ∧
      ExplState.physSet κ b jumps spec D =
        (fun z => (spec.1 : ℂ) + z) '' (γ '' Icc 0 (joinTime Δ D (n + 1)).toNNReal) := by
  obtain ⟨W, γ, hW, hW0, hγ, hag⟩ := exists_trace_joinDrv n fun j hj =>
    let ⟨_, hαj⟩ := hα j hj
    hasPieceExt_of_trace (he j hj) hαj (hs j hj)
  refine ⟨W, γ, hW, hW0, hγ, hag, ?_⟩
  have hs' : AllSucc Δ D spec.2.2.length := by rw [hn]; exact hs
  have hc' : ∀ i < spec.2.2.length, Continuous (stopDrv (Δ i) (D i)) ∧
      stopDrv (Δ i) (D i) 0 = 0 := by rw [hn]; exact hc
  rw [physSet_eq_radialTips (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ hs' hc', hn]
  obtain ⟨hJ, hJ0⟩ := continuous_joinDrv hc
  rw [radialTips_eq_image hJ hJ0 hW hW0 hγ (joinTime_nonneg Δ D _) hag]

end InteractingSLE.Theorem14.GW2TipSystem.SwC
