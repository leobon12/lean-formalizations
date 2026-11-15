/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartMobius

/-!
# Möbius images of chains based at a general real point

Packet PROVE-T14-GW2ROOT2. Translation reduces a general initial driver
to the existing normalized Möbius image theorem. At a positive horizon,
the initial point belongs to the closed hull, so clearance from the hull
already excludes a pole at the initial point.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

open ConformalImage ConformalImageFull Sec5.CrossRestart

/-- The initial point of any continuous driver is in every positive closed hull. -/
theorem initial_mem_closure_fwdHull {W : ℝ → ℝ} (hW : Continuous W)
    {T : ℝ} (hT : 0 < T) : (W 0 : ℂ) ∈ closure (fwdHull W T) := by
  have h0 := zero_mem_closure_fwdHull (hW.sub continuous_const) (sub_self (W 0)) hT
  have hK : fwdHull W T = (fun z : ℂ => z + W 0) ''
      fwdHull (fun t => W t - W 0) T := by
    rw [← fwdHull_add_const]
    simp only [sub_add_cancel]
  rw [hK]
  exact image_closure_subset_closure_image (f := fun z : ℂ => z + W 0) (by fun_prop)
    ⟨0, h0, zero_add _⟩

/-- A pole separated from a positive hull is separated from its initial point. -/
theorem mobPole_ne_initial {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {c d r : ℝ} (hr : 0 < r)
    (hd : Disjoint (ball (mobPole c d : ℂ) r) (fwdHull W T)) :
    mobPole c d ≠ W 0 := by
  intro he
  obtain ⟨z, hz, hzr⟩ := Metric.mem_closure_iff.mp
    (initial_mem_closure_fwdHull hW hT) r hr
  exact disjoint_left.mp hd (by simpa only [he, mem_ball, dist_comm] using hzr) hz

/-- The existing Möbius image chain theorem for an arbitrary real initial driver. -/
theorem exists_mobius_chain {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {a b c d : ℝ} (hdet : 0 < a * d - b * c) (hc : c ≠ 0)
    {r : ℝ} (hr : 0 < r)
    (hd : Disjoint (ball (mobPole c d : ℂ) r) (fwdHull W T)) :
    ∃ τ V : ℝ → ℝ, Continuous V ∧
      V 0 = (a * W 0 + b) / (c * W 0 + d) ∧ τ 0 = 0 ∧
      StrictMonoOn τ (Icc 0 T) ∧ ContinuousOn τ (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T,
        τ t = hcapSet (realMobius a b c d '' fwdHull W t) / 2 ∧
        fwdHull V (τ t) = realMobius a b c d '' fwdHull W t := by
  let x := W 0
  let W₀ : ℝ → ℝ := fun t => W t - x
  have hW₀ : Continuous W₀ := hW.sub continuous_const
  have hW₀0 : W₀ 0 = 0 := sub_self _
  have hK : ∀ t, fwdHull W t = (fun z : ℂ => z + x) '' fwdHull W₀ t := by
    intro t
    rw [← fwdHull_add_const]
    simp only [W₀, sub_add_cancel]
  have hdet₀ : 0 < a * (c * x + d) - (a * x + b) * c := by
    nlinarith only [hdet]
  have hp : mobPole c (c * x + d) = mobPole c d - x := by
    unfold mobPole
    field_simp
    ring
  have hp₀ : mobPole c (c * x + d) ≠ 0 := by
    rw [hp, sub_ne_zero]
    exact mobPole_ne_initial hW hT hr hd
  have hd₀ : Disjoint (ball (mobPole c (c * x + d) : ℂ) r) (fwdHull W₀ T) := by
    apply disjoint_left.mpr
    intro z hz hzK
    have hzimage : z + (x : ℂ) ∈ fwdHull W T := by
      rw [hK T]
      exact ⟨z, hzK, rfl⟩
    apply disjoint_left.mp hd ?_ hzimage
    rw [mem_ball, dist_eq_norm] at hz ⊢
    rw [hp, ofReal_sub] at hz
    convert hz using 1
    congr 1
    ring
  obtain ⟨τ, V, _, _, _, hV, hV0, hτ0, hτm, hτc, hmain⟩ :=
    exists_loewner_mobius_image hW₀ hW₀0 hT.le hdet₀ hc hp₀ hr hd₀
  have himg : ∀ t, realMobius a (a * x + b) c (c * x + d) '' fwdHull W₀ t =
      realMobius a b c d '' fwdHull W t := by
    intro t
    rw [hK t, image_image]
    apply image_congr
    intro z _
    simp only [realMobius, ofReal_add, ofReal_mul]
    congr 1 <;> ring
  refine ⟨τ, V, hV, hV0, hτ0, hτm, hτc, fun t ht => ?_⟩
  rw [← himg t]
  exact ⟨(hmain t ht).1, (hmain t ht).2.1⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
