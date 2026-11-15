/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aMeanIdentGeometry

/-!
# Boundary values of the geometric arg sum, including swallowed marks

Packet PROVE-G7A-MEANIDENT. These finite-sum adapters use the landed real-flow
order results. No survival assumption is placed on the marks.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open QuantumZipper (H fwdMap IsForwardSol)

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI
open MartChar.RealFlow

/-- Boundary values of a finite arg sum away from its finitely many marks. -/
theorem tendsto_argSum0 {ι : Type*} [Fintype ι] (p c : ι → ℝ) (c₀ x : ℝ)
    (hx : ∀ j, x ≠ p j) :
    Tendsto (GB7a.argSum0 p c c₀) (𝓝[H] (x : ℂ))
      (𝓝 (c₀ + ∑ j, c j * (if x < p j then Real.pi else 0))) :=
  tendsto_const_nhds.add (tendsto_finsetSum _ fun j _ =>
    tendsto_const_nhds.mul (GB7a.tendsto_arg_sub_real (hx j)))

/-- The geometric marks keep their original side of a non-alive boundary access. -/
theorem geomImage_order_of_seed_bounds {w : ℝ → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) {x p : ℝ} (hL : geomL w t 0 ≤ x) (hR : x ≤ geomR w t 0)
    (hp : p ≠ 0) (hxp : x ≠ geomImage w t p) :
    x < geomImage w t p ↔ 0 < p := by
  by_cases hpn : p < 0
  · rw [geomImage, ite_eq_left hpn]
    have hm := rightImg_mono_index hw.neg ht (show 0 ≤ -p from neg_nonneg.2 hpn.le)
    change rightImg (fun s => -w s) 0 t ≤ rightImg (fun s => -w s) (-p) t at hm
    have hpx : geomL w t p ≤ x := by
      simp only [geomL, neg_zero] at hL ⊢
      linarith
    constructor <;> intro h <;> linarith
  · rw [geomImage, ite_eq_right hpn] at hxp ⊢
    have hpp : 0 < p := lt_of_le_of_ne (not_lt.1 hpn) hp.symm
    have hm := rightImg_mono_index hw ht hpp.le
    have hpx : x ≤ geomR w t p := by simp only [geomR] at hR ⊢; linarith
    exact ⟨fun _ => hpp, fun _ => lt_of_le_of_ne hpx hxp⟩

/-- At a non-alive boundary access the geometric arg sum has the original seed value. -/
theorem tendsto_geomArgSum_of_seed_bounds {ι : Type*} [Fintype ι]
    {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t)
    (p c : ι → ℝ) (c₀ : ℝ) (hp : ∀ j, p j ≠ 0)
    (hseed : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => 0 < p j), c j = 0)
    {x : ℝ} (hL : geomL w t 0 ≤ x) (hR : x ≤ geomR w t 0)
    (hx : ∀ j, x ≠ geomImage w t (p j)) :
    Tendsto (GB7a.argSum0 (fun j => geomImage w t (p j)) c c₀)
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hl := tendsto_argSum0 (fun j => geomImage w t (p j)) c c₀ x hx
  have hv : c₀ + ∑ j, c j * (if x < geomImage w t (p j) then Real.pi else 0) = 0 := by
    simp_rw [geomImage_order_of_seed_bounds hw ht hL hR (hp _) (hx _)]
    rw [Finset.sum_filter, Finset.mul_sum] at hseed
    have hs : ∑ j, c j * (if 0 < p j then Real.pi else 0) =
        ∑ j, Real.pi * (if 0 < p j then c j else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [hs]
    exact hseed
  rw [hv] at hl
  exact hl

/-- At an alive real point the geometric and initial arg sums have the same boundary value. -/
theorem tendsto_geomArgSum_of_alive {ι : Type*} [Fintype ι]
    {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (p c : ι → ℝ) (c₀ : ℝ) {a x : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol w (a : ℂ) t u) (hut : u t = (x : ℂ))
    (hx : ∀ j, x ≠ geomImage w t (p j)) :
    Tendsto (GB7a.argSum0 (fun j => geomImage w t (p j)) c c₀)
      (𝓝[H] (x : ℂ)) (𝓝 (c₀ + ∑ j, c j * (if a < p j then Real.pi else 0))) := by
  have hl := tendsto_argSum0 (fun j => geomImage w t (p j)) c c₀ x hx
  simp_rw [geomImage_order_of_alive hw hw0 ht hu hut (hx _)] at hl
  exact hl

end InteractingSLE.Restart.FlowLocalityGen
