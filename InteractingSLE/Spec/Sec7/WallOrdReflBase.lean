/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfSide
import InteractingSLE.Spec.Sec7.R6FcTrace

/-!
# Local boundary continuity of a Loewner chart at an alive wall point

Packet PROVE-WALL-ORDER, target (3) (`R5Lift.R7OuterRefl`). Ingredients for the forward continuity of a reference chart
`old = c.loewner W t` at a boundary point `z` of the pocket that is not in the closed hull:

* `fwd_mem_compl_of_mem_dom_loewner`: on the Loewner chart's domain the pocket coordinate avoids the hull;
* **`tendsto_loewner_fwd_of_alive`**: if the pocket coordinate `ψ` tends to a real point `X₀ ≠ 0` off the closed hull
  at `z`, the forward chart has a real limit at `z` from its domain (the reflection of `f_t` across the real axis near
  an alive point, `R5Lift.tendsto_fwdMap_of_alive`);
* `mem_closure_of_mem_fillH_of_mem_closure_compl`: a point of a filling that is a limit of its complement lies in the
  closure of the filled set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec7.WallOrd

/-- **On a Loewner chart's domain the pocket coordinate avoids the hull** and the forward chart is `f_t ∘ c`. -/
theorem fwd_mem_compl_of_mem_dom_loewner {c : Chart} (hc : c.IsConformal) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {a : ℂ} (ha : a ∈ (c.loewner W t).dom) :
    c.1 a ∈ H \ fwdHull W t ∧ a ∈ c.dom := by
  have hl := hc.loewner hW hW0 ht
  rw [← SetLike.mem_coe, hl.coe_dom] at ha
  obtain ⟨y, hy, rfl⟩ := ha
  have hb : fwdMapInv W t y ∈ H \ fwdHull W t := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 ht]
    exact mem_image_of_mem _ hy
  refine ⟨?_, hc.inv_mem_dom hb.1⟩
  show c.1 (c.2.1 (fwdMapInv W t y)) ∈ H \ fwdHull W t
  rw [hc.2.2 _ hb.1]
  exact hb

/-- **Forward continuity of a Loewner chart at an alive boundary point**: if the pocket coordinate `ψ = c.1` (on
`C = c.dom`) tends at `z` to a real point `X₀ ≠ 0` off the closed hull `K_t`, the forward chart `f_t ∘ ψ` has a real
limit at `z` from the chart's domain. -/
theorem tendsto_loewner_fwd_of_alive {c : Chart} (hc : c.IsConformal) {C : Set ℂ} (hdomC : (c.dom : Set ℂ) = C)
    {ψ : ℂ → ℂ} (heq : EqOn c.1 ψ C) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} {X₀ : ℝ} (hψz : Tendsto ψ (𝓝[C] z) (𝓝 (X₀ : ℂ))) (hX0 : X₀ ≠ 0)
    (hX : (X₀ : ℂ) ∉ closure (fwdHull W t)) :
    ∃ y : ℝ, Tendsto (c.loewner W t).1 (𝓝[((c.loewner W t).dom : Set ℂ)] z) (𝓝 (y : ℂ)) := by
  have hsub : ((c.loewner W t).dom : Set ℂ) ⊆ C := fun a ha => by
    have := (fwd_mem_compl_of_mem_dom_loewner hc hW hW0 ht ha).2
    rwa [← hdomC]
  have hF : ∀ᶠ a in 𝓝[((c.loewner W t).dom : Set ℂ)] z, ψ a ∈ H \ fwdHull W t :=
    eventually_nhdsWithin_of_forall fun a ha => by
      rw [← heq (hsub ha)]
      exact (fwd_mem_compl_of_mem_dom_loewner hc hW hW0 ht ha).1
  have hFx : Tendsto (fun a => fwdMap W 0 (ψ a)) (𝓝[((c.loewner W t).dom : Set ℂ)] z) (𝓝 (X₀ : ℂ)) := by
    refine (hψz.mono_left (nhdsWithin_mono _ hsub)).congr' ?_
    filter_upwards [hF] with a ha
    rw [Ito.fwdMap_zero_eq_sub W ha.1, hW0, Complex.ofReal_zero, sub_zero]
  have hx : (X₀ : ℂ) ∉ closure (fwdHull (fun r => W (0 + r) - W 0) (t - 0)) := by
    have e : (fun r => W (0 + r) - W 0) = W := funext fun r => by rw [zero_add, hW0, sub_zero]
    rw [e, sub_zero]
    exact hX
  obtain ⟨y, hy, -⟩ := R5Lift.tendsto_fwdMap_of_alive hW (s := 0) (s' := t) le_rfl ht hF hX0 hFx hx
  refine ⟨y, hy.congr' (eventually_nhdsWithin_of_forall fun a ha => ?_)⟩
  show fwdMap W t (ψ a) = fwdMap W t (c.1 a)
  rw [heq (hsub ha)]

/-- **A point of a filling that is a limit of the filling's complement lies in the closure of the filled set.** -/
theorem mem_closure_of_mem_fillH_of_mem_closure_compl {S : Set ℂ} {z : ℂ} (hz : z ∈ fillH S)
    (hzc : z ∈ closure (H \ fillH S)) : z ∈ closure S := by
  by_contra hzS
  have hU : IsOpen (H \ closure S) := QuantumZipper.isOpen_H.sdiff isClosed_closure
  have hzU : z ∈ H \ closure S := ⟨hz.1, hzS⟩
  have hb : Bornology.IsBounded (connectedComponentIn (H \ closure S) z) := hz.2.resolve_left hzS
  have hVo : IsOpen (connectedComponentIn (H \ closure S) z) := hU.connectedComponentIn
  have hV : connectedComponentIn (H \ closure S) z ⊆ fillH S := fun w hw => by
    have hwU := connectedComponentIn_subset _ _ hw
    refine ⟨hwU.1, Or.inr ?_⟩
    rw [← connectedComponentIn_eq hw]
    exact hb
  obtain ⟨w, hwV, hwc⟩ := mem_closure_iff.1 hzc _ hVo (mem_connectedComponentIn hzU)
  exact hwc.2 (hV hwV)

end InteractingSLE.Sec7.WallOrd
