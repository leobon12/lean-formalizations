/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsModel

/-!
# The prime-end part of a prefix match: a chart landing on a recorded piece

Packet PROVE-WALK-WORDS (the central incident sides of PROVE-T14-WALKINT's finite-word matches,
`IsPiecePhysicalMatch`, and of `WalkNorm.IsPieceMatchLoc`). Let `c` be a conformal chart (e.g. a component chart,
`GW3Law.isConformal_of_isComponentChart`) whose inverse lands, along the real points near `x₀`, on the fresh part of
a recorded piece `pc` read through a global Loewner model `(W, η)` of its driver. If, right of `x₀`, the landings are
**later** points of the piece, the transition into the prefix chart `prefixChart pc τ` is defined on a half-disc at
`x₀`, has real limits on the diameter and tends to the **left** side point `y` (any negative preimage of the landing
point): `exists_prefix_transition_of_later`; if they are **earlier** points, it tends to the **right** side point:
`exists_prefix_transition_of_earlier`. These are exactly the last conjuncts of `IsPiecePhysicalMatch` /
`IsPieceMatchLoc` (with the side point from `WalkNorm.exists_isLeftSidePt_of_cut`).

Proof: `nonempty_sideIdentification_of_later` / `_of_earlier` for the model chart `pc.1.loewner W τ`, transported to
the prefix chart (same forward and inverse maps, `prefixChart_inv_eq_loewner`, `prefixChart_fwd_eq_loewner`), and
`WalkIntBridge.SideIdentification.local_transition`. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.WalkWords

open WalkBdry

section Match

variable {c : Chart} {W : ℝ → ℝ} {η : ℝ → ℂ} {pc : Piece} {T' x₀ y : ℝ} {τ : ℝ≥0} {Λ : ℂ → ℂ}

/-- The forward map of a prefix chart is that of the Loewner stage of the model driver. -/
theorem prefixChart_fwd_eq_loewner (hagree : EqOn (pieceDrv pc) W (Icc 0 T')) (hτ : (τ : ℝ) ≤ T') (z : ℂ) :
    (prefixChart pc τ).1 z = (pc.1.loewner W τ).1 z := by
  change fwdMap (pieceDrv pc) τ (pc.1.1 z) = fwdMap W τ (pc.1.1 z)
  exact Ito.fwdMap_congr_of_eqOn (hagree.mono (Icc_subset_Icc_right hτ))

theorem prefixChart_dom_eq_loewner (hW : Continuous W) (hpc : ContinuousOn (pieceDrv pc) (Icc 0 T'))
    (hagree : EqOn (pieceDrv pc) W (Icc 0 T')) (hτ : (τ : ℝ) < T') :
    ((prefixChart pc τ).dom : Set ℂ) = ((pc.1.loewner W τ).dom : Set ℂ) := by
  have h : (prefixChart pc τ).2.1 = (pc.1.loewner W τ).2.1 :=
    funext (prefixChart_inv_eq_loewner hW hpc hagree hτ)
  change interior ((prefixChart pc τ).2.1 '' H) = interior ((pc.1.loewner W τ).2.1 '' H)
  rw [h]

/-- The local transition from a side identification with the model chart, read in the prefix chart. -/
theorem exists_prefix_transition_of_side (hpc1 : pc.1.IsConformal) (hW : Continuous W) (hW0 : W 0 = 0)
    (hpc : ContinuousOn (pieceDrv pc) (Icc 0 T')) (hagree : EqOn (pieceDrv pc) W (Icc 0 T')) (hτ : (τ : ℝ) < T')
    (G : WalkIntBridge.SideIdentification c (pc.1.loewner W τ) x₀ y) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ w ∈ H ∩ ball (x₀ : ℂ) δ, c.2.1 w ∈ (prefixChart pc τ).dom) ∧
      (∀ z ∈ ball (x₀ : ℂ) δ, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
        Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] z) (𝓝 v)) ∧
      Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] (x₀ : ℂ)) (𝓝 (y : ℂ)) := by
  have hcL : (pc.1.loewner W τ).IsConformal := hpc1.loewner hW hW0 τ.coe_nonneg
  obtain ⟨δ, hδ, hdom, hreal, hT⟩ := G.local_transition hcL
  have hf : (fun w => (prefixChart pc τ).1 (c.2.1 w)) = fun w => (pc.1.loewner W τ).1 (c.2.1 w) :=
    funext fun w => prefixChart_fwd_eq_loewner hagree hτ.le _
  refine ⟨δ, hδ, fun w hw => ?_, ?_, ?_⟩
  · rw [SetLike.mem_coe.symm, prefixChart_dom_eq_loewner hW hpc hagree hτ]
    exact hdom w hw
  · rw [hf]; exact hreal
  · rw [hf]; exact hT

/-- **Left side**: a chart landing on later points of a recorded piece sees the piece's left side point. -/
theorem exists_prefix_transition_of_later (hc : c.IsConformal) (hpc1 : pc.1.IsConformal) (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hpc : ContinuousOn (pieceDrv pc) (Icc 0 T'))
    (hagree : EqOn (pieceDrv pc) W (Icc 0 T')) (hτ : (τ : ℝ) < T') {t : ℝ} (ht : 0 ≤ t) (htτ : t < τ)
    (hinj : InjOn η (Icc 0 (τ : ℝ))) (hH : ∀ s ∈ Icc t (τ : ℝ), η s ∈ H) (hy : y < 0)
    (hFy : extendFrom H (fwdMapInv W τ) y = η t)
    (hland : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (Λ x)))
    (htrace : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ s ∈ Icc 0 (τ : ℝ), η s ∈ H ∧ Λ x = pc.1.2.1 (η s))
    (hdom : ∃ δ > 0, ∀ z ∈ H ∩ ball (x₀ : ℂ) δ, c.2.1 z ∈ (prefixChart pc τ).2.1 '' H)
    (hp : Λ x₀ = pc.1.2.1 (η t))
    (hlater : ∃ ε > 0, ∀ x ∈ Ioo x₀ (x₀ + ε), ∃ s ∈ Ioo t (τ : ℝ), Λ x = pc.1.2.1 (η s)) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ w ∈ H ∩ ball (x₀ : ℂ) δ, c.2.1 w ∈ (prefixChart pc τ).dom) ∧
      (∀ z ∈ ball (x₀ : ℂ) δ, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
        Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] z) (𝓝 v)) ∧
      Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] (x₀ : ℂ)) (𝓝 (y : ℂ)) := by
  have hinv : (prefixChart pc τ).2.1 = (pc.1.loewner W τ).2.1 :=
    funext (prefixChart_inv_eq_loewner hW hpc hagree hτ)
  rw [hinv] at hdom
  obtain ⟨G⟩ := nonempty_sideIdentification_of_later hc hpc1 hη hW hW0 ht htτ hinj hH hy hFy hland htrace hdom hp hlater
  exact exists_prefix_transition_of_side hpc1 hW hW0 hpc hagree hτ G

/-- **Right side**: a chart landing on earlier fresh points of a recorded piece sees the piece's right side point. -/
theorem exists_prefix_transition_of_earlier (hc : c.IsConformal) (hpc1 : pc.1.IsConformal) (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hpc : ContinuousOn (pieceDrv pc) (Icc 0 T'))
    (hagree : EqOn (pieceDrv pc) W (Icc 0 T')) (hτ : (τ : ℝ) < T') {s₀ t : ℝ} (hs₀ : 0 ≤ s₀) (hs₀t : s₀ < t)
    (htτ : t < τ) (hinj : InjOn η (Icc 0 (τ : ℝ))) (hH : ∀ s ∈ Icc t (τ : ℝ), η s ∈ H) (hy : 0 < y)
    (hFy : extendFrom H (fwdMapInv W τ) y = η t)
    (hland : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (Λ x)))
    (htrace : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ s ∈ Icc 0 (τ : ℝ), η s ∈ H ∧ Λ x = pc.1.2.1 (η s))
    (hdom : ∃ δ > 0, ∀ z ∈ H ∩ ball (x₀ : ℂ) δ, c.2.1 z ∈ (prefixChart pc τ).2.1 '' H)
    (hp : Λ x₀ = pc.1.2.1 (η t))
    (hearlier : ∃ ε > 0, ∀ x ∈ Ioo x₀ (x₀ + ε), ∃ s ∈ Ioo s₀ t, η s ∈ H ∧ Λ x = pc.1.2.1 (η s)) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ w ∈ H ∩ ball (x₀ : ℂ) δ, c.2.1 w ∈ (prefixChart pc τ).dom) ∧
      (∀ z ∈ ball (x₀ : ℂ) δ, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
        Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] z) (𝓝 v)) ∧
      Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] (x₀ : ℂ)) (𝓝 (y : ℂ)) := by
  have hinv : (prefixChart pc τ).2.1 = (pc.1.loewner W τ).2.1 :=
    funext (prefixChart_inv_eq_loewner hW hpc hagree hτ)
  rw [hinv] at hdom
  obtain ⟨G⟩ := nonempty_sideIdentification_of_earlier hc hpc1 hη hW hW0 hs₀ hs₀t htτ hinj hH hy hFy hland htrace
    hdom hp hearlier
  exact exists_prefix_transition_of_side hpc1 hW hW0 hpc hagree hτ G

end Match

end InteractingSLE.Theorem14.WalkWords
