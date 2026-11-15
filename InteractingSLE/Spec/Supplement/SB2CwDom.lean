/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CwStage
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# The stage version of a domain chart is a domain chart (deterministic)

Packet PROVE-SB2-CANON, round 4 ((P4): the domain-chart clause of `Qx.ChainFacts`). **`isDomainChart_stageChartOf`**:
if B's stage chart `cℓ` is a domain chart of `ℍ ∖ fill B` and `Φ` a domain chart of `ℍ ∖ fill Y` with `fill B ⊆ fill Y`,
then `Mx.stageChartOf cℓ Φ` (`Φ ∘ cℓ⁻¹`, lift `Φ`'s lift minus `cℓ`'s, both read at `cℓ⁻¹`) is a domain chart of the
stage-coordinate complement `ℍ ∖ Mn.stageRetained cℓ Y`. The lift is the chain rule `IsDerivLog.comp` with the inverse
lift `−L_cℓ ∘ cℓ⁻¹` (from `cℓ ∘ cℓ⁻¹ = id` on `ℍ`).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Cz

/-- **The inverse of a domain chart has the inverse lift.** -/
theorem isDerivLog_inv {c : Chart} {D : Set ℂ} (hD : IsDomainChart D c) {L : ℂ → ℂ}
    (hL : IsDerivLog c.1 L D) : IsDerivLog c.2.1 (fun w => -L (c.2.1 w)) H := by
  have hHo : IsOpen H := QuantumZipper.isOpen_H
  have hinvd : DifferentiableOn ℂ c.2.1 H := hD.isConformal.1
  refine ⟨((hL.1.comp hinvd fun w hw => hD.inv_mem hw)).neg, fun w hw => ?_⟩
  have hxD : c.2.1 w ∈ D := hD.inv_mem hw
  have hfd : DifferentiableAt ℂ c.1 (c.2.1 w) := hD.differentiableOn_fwd.differentiableAt (hD.isOpen.mem_nhds hxD)
  have hgd : DifferentiableAt ℂ c.2.1 w := hinvd.differentiableAt (hHo.mem_nhds hw)
  have hid : (fun y => c.1 (c.2.1 y)) =ᶠ[𝓝 w] id :=
    Filter.eventually_of_mem (hHo.mem_nhds hw) fun y hy => hD.fwd_inv hy
  have hcomp : deriv c.1 (c.2.1 w) * deriv c.2.1 w = 1 := by
    have h1 := deriv_comp w hfd hgd
    rw [show (c.1 ∘ c.2.1) = fun y => c.1 (c.2.1 y) from rfl, hid.deriv_eq, deriv_id] at h1
    exact h1.symm
  have hne : deriv c.1 (c.2.1 w) ≠ 0 := hD.deriv_ne_zero hxD
  rw [exp_neg, hL.2 _ hxD]
  exact (eq_inv_of_mul_eq_one_right hcomp).symm

/-- **The stage version of a domain chart is a domain chart of the stage-coordinate complement.** -/
theorem isDomainChart_stageChartOf {cℓ Φ : Chart} {B Y : Set ℂ} (hD : IsDomainChart (H \ fillH B) cℓ)
    (hΦ : IsDomainChart (H \ fillH Y) Φ) (hBY : fillH B ⊆ fillH Y) :
    IsDomainChart (H \ Mn.stageRetained cℓ Y) (Mx.stageChartOf cℓ Φ) := by
  have hsub : H \ fillH Y ⊆ H \ fillH B := fun x hx => ⟨hx.1, fun h => hx.2 (hBY h)⟩
  have hHo : IsOpen H := QuantumZipper.isOpen_H
  -- the stage complement is the inverse image of `ℍ ∖ fill Y`
  have hD' : H \ Mn.stageRetained cℓ Y = H ∩ cℓ.2.1 ⁻¹' (H \ fillH Y) := by
    ext v
    constructor
    · rintro ⟨hv, hn⟩
      exact ⟨hv, hD.isConformal.2.1 hv, fun h => hn ⟨hv, h⟩⟩
    · rintro ⟨hv, -, hn⟩
      exact ⟨hv, fun h => hn h.2⟩
  have hD'o : IsOpen (H \ Mn.stageRetained cℓ Y) := by
    rw [hD']; exact hD.isConformal.1.continuousOn.isOpen_inter_preimage hHo hΦ.isOpen
  have hmaps : MapsTo cℓ.2.1 (H \ Mn.stageRetained cℓ Y) (H \ fillH Y) := fun v hv => by
    rw [hD'] at hv; exact hv.2
  refine ⟨⟨?_, fun y hy => hD.fwd_mem (hsub (hΦ.inv_mem hy)), fun y hy => ?_⟩, ?_, ?_⟩
  · exact hD.differentiableOn_fwd.comp hΦ.isConformal.1 fun y hy => hsub (hΦ.inv_mem hy)
  · show Φ.1 (cℓ.2.1 (cℓ.1 (Φ.2.1 y))) = y
    rw [hD.inv_fwd (hsub (hΦ.inv_mem hy)), hΦ.fwd_inv hy]
  · -- the image
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hx := hΦ.inv_mem hy
      refine ⟨hD.fwd_mem (hsub hx), fun hv => ?_⟩
      have h2 : cℓ.2.1 (cℓ.1 (Φ.2.1 y)) ∈ fillH Y := hv.2
      rw [hD.inv_fwd (hsub hx)] at h2
      exact hx.2 h2
    · intro hv
      have hx := hmaps hv
      rw [← hΦ.image_eq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      refine ⟨y, hy, ?_⟩
      show cℓ.1 (Φ.2.1 y) = v
      rw [hyx, hD.fwd_inv hv.1]
  · -- the lift
    obtain ⟨LΦ, hLΦ, hΦl⟩ := hΦ.2.2
    obtain ⟨Lc, hLc, hcl⟩ := hD.2.2
    have hinv := (isDerivLog_inv hD hLc).mono (show H \ Mn.stageRetained cℓ Y ⊆ H from sdiff_subset)
    have hcomp := IsDerivLog.comp hD'o hΦ.isOpen hΦ.differentiableOn_fwd
      (hD.isConformal.1.mono sdiff_subset) hmaps hLΦ hinv
    refine ⟨_, hcomp, fun w hw => ?_⟩
    have hx := hmaps hw
    show Φ.2.2 (cℓ.2.1 w) - cℓ.2.2 (cℓ.2.1 w) = (LΦ (cℓ.2.1 w) + -Lc (cℓ.2.1 w)).im
    rw [hΦl hx, hcl (hsub hx), add_im, neg_im]
    ring

end InteractingSLE.Theorem14.SB.Cz
