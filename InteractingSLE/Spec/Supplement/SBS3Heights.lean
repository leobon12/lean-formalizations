/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwInv
import InteractingSLE.Spec.Sec7.Aux70

/-!
# Lemma S3: the two possible old-side heights are incompatible with the upper flow

Packet PROVE-T14-S3, specification pp. 579–580. The finite label predicate is
the existing `Lh.SideH`; the comparison of harmonic representatives and
derivative lifts is the existing `Sec7.eq_of_side_limits`.

These are local conditional lemmas. The probabilistic construction of a common
joint collar, with the zero inherited phase, is not asserted here.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.S3

/-- Neither side height of an earlier, strictly smaller angle equals the
exposed left height of the upper flow. The right-side case specializes the
already proved height mismatch of Aux. 70. -/
theorem sideH_ne_upper_left {κ ϑ v : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {l : List (ℝ × ℝ≥0)} (hθ : ∀ p ∈ l, p.1 < ϑ) (hv : Lh.SideH κ l v) :
    v ≠ -sleLambda κ - ϑ * chiC κ := by
  obtain ⟨p, hp, hv | hv⟩ := hv
  · rw [hv]
    exact Sec7.sleLambda_sub_ne hκ hκ4
      ((hθ p hp).trans (lt_add_of_pos_right ϑ Real.pi_pos))
  · rw [hv]
    intro he
    have he' : p.1 * chiC κ = ϑ * chiC κ := by linarith only [he]
    exact (hθ p hp).ne (mul_right_cancel₀ (Sec4.chiC_pos hκ hκ4).ne' he')

/-- S3's contradiction once the protected joint comparison has supplied the
two exact side limits and the zero difference of inherited derivative lifts.
No phase modulo `2π` is substituted for the exact zero phase. -/
theorem false_of_side_limits {κ ϑ v : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {l : List (ℝ × ℝ≥0)} (hθ : ∀ p ∈ l, p.1 < ϑ) (hv : Lh.SideH κ l v)
    {F : Filter ℂ} [F.NeBot] {v₁ v₂ u₀ L₁ L₂ : ℂ → ℝ}
    (hmean : Tendsto (fun z => v₁ z - v₂ z) F (𝓝 0))
    (hphase : Tendsto (fun z => L₁ z - L₂ z) F (𝓝 0))
    (hold : Tendsto (fun z => v₁ z + u₀ z + chiC κ * L₁ z) F (𝓝 v))
    (hupper : Tendsto (fun z => v₂ z + u₀ z + chiC κ * L₂ z) F
      (𝓝 (-sleLambda κ - ϑ * chiC κ))) : False :=
  sideH_ne_upper_left hκ hκ4 hθ hv (Sec7.eq_of_side_limits hmean hphase hold hupper)

end InteractingSLE.Theorem14.SB.S3
