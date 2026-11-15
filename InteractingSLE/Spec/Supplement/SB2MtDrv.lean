/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4IdentHull
import InteractingSLE.Spec.Sec6.DrivingCriterion

/-!
# Drivers whose hulls differ by a real translation

Packet PROVE-SB2-LCMEAN, round 12 (identification step of the kernel half). The relative chart of `EL`'s stage, read
in physical coordinates (`Mo.physRelChart c c₁ m`), and the canonical relative chart (`Mo.hullChart (fill K) x₀`) are
normalized charts of the same domain, so they differ by a real translation `d` (`Mo.exists_hullChart_translate`).
The image of B's piece under them, hence the relative hulls, differ by `d`. Since both drivers start at `0`, `d = 0`
and the drivers agree:

* `eq_zero_of_fwdHull_eq_le`: the hulls of two continuous drivers agree at all small positive times up to `S > 0` and
  one starts at `0` — then so does the other (`GW4Ident.eq_zero_of_fwdHull_eq` with a horizon);
* **`eqOn_of_fwdHull_eq_add_const`**: if the hulls of `W₂` are those of `W₁` translated by `d` on `[0, S]`, `S > 0`,
  and both start at `0`, then `d = 0` and `W₁ = W₂` on `[0, S]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace InteractingSLE.Theorem14.SB.Mt

/-- **The hulls up to a horizon determine the starting point of the driver**: if the hulls of continuous `W₁`, `W₂`
agree at all positive times up to `S > 0` and `W₁ 0 = 0`, then `W₂ 0 = 0`. -/
theorem eq_zero_of_fwdHull_eq_le {W₁ W₂ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (hW₁0 : W₁ 0 = 0)
    {S : ℝ} (hS : 0 < S)
    (h : ∀ t : ℝ, 0 < t → t ≤ S → QuantumZipper.fwdHull W₁ t = QuantumZipper.fwdHull W₂ t) : W₂ 0 = 0 := by
  set c := W₂ 0 with hc
  set U : ℝ → ℝ := fun s => W₂ s - c with hU
  have hUc : Continuous U := hW₂.sub continuous_const
  have hU0 : U 0 = 0 := by simp [hU, hc]
  have hWU : (fun s => U s + c) = W₂ := by funext s; simp [hU]
  by_contra hne
  have hpos : 0 < |c| := abs_pos.2 hne
  obtain ⟨δ₁, hδ₁, h₁⟩ := GW4Ident.eventually_fwdHull_subset_closedBall hW₁ hW₁0 (ε := |c| / 4) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := GW4Ident.eventually_fwdHull_subset_closedBall hUc hU0 (ε := |c| / 4) (by positivity)
  set t := min (min δ₁ δ₂) S with ht
  have ht0 : 0 < t := lt_min (lt_min hδ₁ hδ₂) hS
  have htδ₁ : t ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have htδ₂ : t ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨z, hz⟩ := QuantumZipper.RS.fwdHull_nonempty_of_pos hW₁ hW₁0 ht0
  have hz₁ := h₁ t ht0 htδ₁ hz
  have hz₂ : z ∈ QuantumZipper.fwdHull W₂ t := h t ht0 (min_le_right _ _) ▸ hz
  have key := ConformalImageFull.fwdHull_add_const U c t
  rw [hWU] at key
  rw [key] at hz₂
  obtain ⟨v, hv, rfl⟩ := hz₂
  have hv₂ := h₂ t ht0 htδ₂ hv
  rw [mem_closedBall, dist_zero_right] at hz₁ hv₂
  have key' : ‖(c : ℂ)‖ ≤ ‖v + c‖ + ‖v‖ := by
    calc ‖(c : ℂ)‖ = ‖(v + c) - v‖ := by ring_nf
      _ ≤ ‖v + c‖ + ‖v‖ := norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs] at key'
  linarith

/-- **Drivers whose hulls differ by a real translation**: if `W₁`, `W₂` are continuous from `0` and on `[0, S]`,
`S > 0`, the hulls of `W₂` are those of `W₁` translated by `d`, then `d = 0` and `W₁ = W₂` on `[0, S]`. -/
theorem eqOn_of_fwdHull_eq_add_const {W₁ W₂ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₂ : Continuous W₂)
    (hW₁0 : W₁ 0 = 0) (hW₂0 : W₂ 0 = 0) {S : ℝ} (hS : 0 < S) {d : ℝ}
    (h : ∀ s ∈ Icc 0 S, QuantumZipper.fwdHull W₂ s = (fun z : ℂ => z + d) '' QuantumZipper.fwdHull W₁ s) :
    d = 0 ∧ EqOn W₁ W₂ (Icc 0 S) := by
  set U : ℝ → ℝ := fun s => W₁ s + d with hU
  have hUc : Continuous U := hW₁.add continuous_const
  have hUW : ∀ s ∈ Icc 0 S, QuantumZipper.fwdHull W₂ s = QuantumZipper.fwdHull U s := fun s hs => by
    rw [h s hs, hU, ConformalImageFull.fwdHull_add_const W₁ d s]
  have hU0 : U 0 = 0 :=
    eq_zero_of_fwdHull_eq_le hW₂ hUc hW₂0 hS fun t ht htS => hUW t ⟨ht.le, htS⟩
  have hd : d = 0 := by simpa [hU, hW₁0] using hU0
  subst hd
  refine ⟨rfl, ?_⟩
  have hU' : U = W₁ := by funext s; simp [hU]
  rw [hU'] at hUW
  exact Sec6.eqOn_of_fwdHull_eq hW₁ hW₂ hW₁0 hW₂0 hS.le fun s hs => (hUW s hs).symm

end InteractingSLE.Theorem14.SB.Mt
