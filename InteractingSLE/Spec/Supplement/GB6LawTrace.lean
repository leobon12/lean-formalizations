/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LawChain
import InteractingSLE.Spec.Sec5.CrossRestartTrace

/-!
# Proposition GB6: the counterflow trace in the chart of the flow's own component (fillings)

Packet PROVE-GB6B. Continuation of `GB6LawChain.lean` (GB6's fixed-hull restriction) at the level of traces. A
generating trace describes its hulls through fillings (frozen `IsFilling`). Before the first contact with the flow
prefix, the chart of the flow's own component `Ψ = relMap U σ` carries fillings of counterflow hulls to fillings of the
chart images of their traces:

* **`isFilling_relMap_image`**: if `K'_t` (`t ≤ T`) is the filling of `S`, then `Ψ(K'_t)` is the filling of `Ψ(S ∩ ℍ)`;
* **`exists_loewner_relMap_filling`**: with `τ, W'` of `exists_loewner_relMap`, `K^{W'}_{τ(t)}` is the filling of
  `Ψ(γ([0, t]) ∩ ℍ)` for every counterflow trace `γ` with `K'_t = fill(γ([0, t]))`.

Proof: the factorization `Ψ = M₂ ∘ g_A ∘ M₁` (`exists_relMap_factor`) and the filling transport of
`Sec5.CrossRestart` for each factor (`isFilling_image_realMobius`, `isFilling_image_mapOut`, `isFilling_image_add`).
Only points of `ℍ` matter (`isFilling_inter_H_iff`); they lie in the hull (`inter_H_subset_of_isFilling`), where the
factorization holds pointwise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Supp8

namespace GB6

open ConformalImage ConformalImageFull Sec5.CrossRestart

/-- **Fillings in the chart of the flow's own component.** Before the first contact (closed hulls disjoint on
`[0, T]`), for `t ∈ [0, T]`, if the counterflow hull `K'_t` is the filling of `S`, then its chart image `Ψ(K'_t)` is the
filling of `Ψ(S ∩ ℍ)`. -/
theorem isFilling_relMap_image {W U : ℝ → ℝ} (hW : Continuous W) (hU : Continuous U) (hU0 : U 0 = 0)
    {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) {p : ℂ}
    (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 p))
    (hd : Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull W T)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {S : Set ℂ} (hS : IsFilling (QuantumZipper.fwdHull W t) S) :
    IsFilling (relMap U σ '' QuantumZipper.fwdHull W t) (relMap U σ '' (S ∩ H)) := by
  obtain ⟨x, r₁, A, gA, a', b', c', d', x₁, r₃, hxne, hr₁, hd₁, hA, hgA, hdA', -, hdet', hc', hx₁', -,
    hr₃pos, hclear, hfac⟩ := exists_relMap_factor hW hU hU0 hσ hT htip hd
  set Kt := QuantumZipper.fwdHull W t with hKtdef
  set M₁ := realMobius 1 0 x 1 with hM₁def
  set M₂' := realMobius a' (a' * x₁ + b') c' (c' * x₁ + d') with hM₂'def
  have hKt : IsHPHull Kt := isHPHull_fwdHull hW ht.1
  have hmono : Kt ⊆ QuantumZipper.fwdHull W T := (QuantumZipper.fwdHull_mono (W := W)).1 ht.2
  have hdet₁ : (0 : ℝ) < 1 * 1 - 0 * x := by norm_num
  have hd₁t : Disjoint (ball (mobPole x 1 : ℂ) r₁) Kt := hd₁.mono_right hmono
  -- the three factors
  have h1 := isFilling_image_realMobius hdet₁ hxne hKt hr₁ hd₁t hS
  have hK₁ : IsHPHull (M₁ '' Kt) := isHPHull_image hdet₁ hxne hKt hr₁ hd₁t
  have hdA₁ : Disjoint (closure A) (closure (M₁ '' Kt)) :=
    (Set.disjoint_insert_right.1 hdA').2.mono_right (closure_mono (image_mono hmono))
  have h2 := isFilling_image_mapOut hA hgA hK₁ hdA₁ h1
  have hK₂ : IsHPHull (gA '' (M₁ '' Kt)) := hgA.isHPHull_image_of_disjoint_closure hA hK₁ hdA₁
  have h3 := isFilling_image_add hK₂ (-x₁) h2
  have hK₃ := isHPHull_image_add hK₂ (-x₁)
  have hdet₂ : 0 < a' * (c' * x₁ + d') - (a' * x₁ + b') * c' := by
    have : a' * (c' * x₁ + d') - (a' * x₁ + b') * c' = a' * d' - b' * c' := by ring
    rw [this]
    exact hdet'
  have hpole₂' : ((mobPole c' (c' * x₁ + d') : ℝ) : ℂ) = ((mobPole c' d' : ℝ) : ℂ) - x₁ := by
    have hc'C : (c' : ℂ) ≠ 0 := ofReal_ne_zero.2 hc'
    simp only [mobPole]
    push_cast
    field_simp
    ring
  have hd₃ : Disjoint (ball (mobPole c' (c' * x₁ + d') : ℂ) r₃)
      ((fun z : ℂ => z + ((-x₁ : ℝ) : ℂ)) '' (gA '' (M₁ '' Kt))) := by
    rw [hpole₂', Set.disjoint_left]
    rintro _ hb ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    rw [mem_ball, dist_eq_norm] at hb
    have := hclear w (hmono hw)
    have heq : gA (M₁ w) + ((-x₁ : ℝ) : ℂ) - (((mobPole c' d' : ℝ) : ℂ) - x₁) =
        gA (M₁ w) - mobPole c' d' := by
      push_cast
      ring
    rw [heq] at hb
    linarith
  have h4 := isFilling_image_realMobius hdet₂ hc' hK₃ hr₃pos hd₃ h3
  -- the pointwise identity `Ψ = M₂' ∘ (· − x₁) ∘ g_A ∘ M₁` on the hull, and membership in `ℍ`
  have hKH : ∀ w ∈ QuantumZipper.fwdHull W T, w ∈ H := fun w hw =>
    (isHPHull_fwdHull hW hT).1 hw
  have hRK : ∀ w ∈ QuantumZipper.fwdHull W T, -w⁻¹ ∉ QuantumZipper.fwdHull U σ := fun w hw hA' =>
    Set.disjoint_left.1 hd (subset_closure hA') (subset_closure ⟨w, hw, rfl⟩)
  have hid : ∀ w ∈ Kt, M₂' (gA (M₁ w) + ((-x₁ : ℝ) : ℂ)) = relMap U σ w := by
    intro w hw
    rw [(hfac w (hKH w (hmono hw)) (hRK w (hmono hw))).2]
    simp only [hM₂'def, realMobius]
    push_cast
    congr 1 <;> ring
  have hgH : ∀ w ∈ Kt, M₁ w ∈ H ∧ gA (M₁ w) ∈ H ∧ gA (M₁ w) + ((-x₁ : ℝ) : ℂ) ∈ H := by
    intro w hw
    have h := (hfac w (hKH w (hmono hw)) (hRK w (hmono hw))).1
    have hg : gA (M₁ w) ∈ H := hgA.1.2.mapsTo h
    refine ⟨h.1, hg, ?_⟩
    have hg' : 0 < (gA (M₁ w)).im := hg
    show 0 < (gA (M₁ w) + ((-x₁ : ℝ) : ℂ)).im
    simpa using hg'
  have hSK : S ∩ H ⊆ Kt := inter_H_subset_of_isFilling hS
  convert h4 using 1
  · rw [image_image, image_image, image_image]
    exact (image_congr fun w hw => hid w hw).symm
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwK := hSK hw
      obtain ⟨hM, hg, hgx⟩ := hgH w hwK
      exact ⟨gA (M₁ w) + ((-x₁ : ℝ) : ℂ),
        ⟨⟨gA (M₁ w), ⟨⟨M₁ w, ⟨⟨w, hw, rfl⟩, hM⟩, rfl⟩, hg⟩, rfl⟩, hgx⟩, hid w hwK⟩
    · rintro ⟨_, ⟨⟨_, ⟨⟨_, ⟨⟨w, hw, rfl⟩, -⟩, rfl⟩, -⟩, rfl⟩, -⟩, rfl⟩
      exact ⟨w, hw, (hid w (hSK hw)).symm⟩

/-- **The relative chain at the level of fillings**: with `τ, W'` of `exists_loewner_relMap`, for every counterflow
trace `γ` with `K'_t = fill(γ([0, t]))` on `[0, T]`, the relative hull `K^{W'}_{τ(t)}` is the filling of the chart
image `Ψ(γ([0, t]) ∩ ℍ)`. -/
theorem exists_loewner_relMap_filling {W U : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (hU : Continuous U)
    (hU0 : U 0 = 0) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) {p : ℂ}
    (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 p))
    (hd : Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull W T)))
    {γ : ℝ → ℂ} (hγK : ∀ t ∈ Icc (0 : ℝ) T, IsFilling (QuantumZipper.fwdHull W t) (γ '' Icc 0 t)) :
    ∃ τ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 T) ∧
      ContinuousOn τ (Icc 0 T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, QuantumZipper.fwdHull W' (τ t) = relMap U σ '' QuantumZipper.fwdHull W t) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        IsFilling (QuantumZipper.fwdHull W' (τ t)) (relMap U σ '' (γ '' Icc 0 t ∩ H)) := by
  obtain ⟨τ, W', hW'c, hW'0, hτ0, hτm, hτc, hK⟩ := exists_loewner_relMap hW hW0 hU hU0 hσ hT htip hd
  refine ⟨τ, W', hW'c, hW'0, hτ0, hτm, hτc, hK, fun t ht => ?_⟩
  rw [hK t ht]
  exact isFilling_relMap_image hW hU hU0 hσ hT htip hd ht (hγK t ht)

end GB6

end Supp8

end InteractingSLE
