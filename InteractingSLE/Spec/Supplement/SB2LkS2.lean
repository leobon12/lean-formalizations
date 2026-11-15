/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkTail
import InteractingSLE.Spec.Supplement.SBLemmaS2Lift

/-!
# Lemma S2 reflected: the erasure geometry of SB2(2) in a right entry chart

Packet PROVE-T14-SB2LIFT, the deterministic half of SB2(2)'s erasure (supplement p. 631: "Use S2, reflected for the
second assertion"; "Erase `B` through its unique visit to `R` and lift the remaining tail into `D_A`"). Lemma S2
(`s2HullStatement`, `s2LiftStatement`, proved) is stated for a history on the closed RIGHT side of the proper curve and
a LEFT entry chart at `L = min (A ∩ ℝ)`. SB2(2) has the upper history `A` on the closed LEFT side of the completed lower
walk `β₀` and a RIGHT entry chart at `R = max (A ∩ ℝ)`. The reflection `ρ z = −z̄` exchanges the two:

* `refl_image_hullK`: `ρ (K_A) = K_{ρ A}`;
* **`s2HullRight`**: `R ≥ 0`, `β₀` visits `R` at some `t_R` (`t_R = 0` if `R = 0`), `β₀([0, t_R]) ⊆ K_A`,
  `β₀((t_R, ∞)) ⊆ closure D_A`, and every later interior point of `β₀` off `A` lies in `D_A`;
* **`s2LiftRight`**: given a right entry chart `c` of `D_A` at `R` whose inverse has a continuous finite-fibre
  extension `g` to `ℍ̄`, the tail of `β₀` after `t_R` has a proper lift: a proper curve `γ` from `0` with
  `g ∘ γ = β₀(t_R + ·)` (the lift datum of `Lf.IsTailLiftOf`, once its range is identified with the relative walk).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lf

/-! ### Reflection of hulls -/

/-- The reflection of a real segment. -/
theorem refl_image_ofReal_Icc' (a c : ℝ) :
    refl '' (((↑) : ℝ → ℂ) '' Icc a c) = ((↑) : ℝ → ℂ) '' Icc (-c) (-a) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨-x, ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩, (refl_ofReal x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨((-x : ℝ) : ℂ), ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, rfl⟩, ?_⟩
    rw [refl_ofReal, neg_neg]

/-- **The reflection of the filled hull with its real base** is the filled hull of the reflection. -/
theorem refl_image_hullK (A : Set ℂ) : refl '' hullK A = hullK (refl '' A) := by
  unfold hullK
  rw [image_union, refl_image_ofReal_Icc', realMin_refl_image, realMax_refl_image, refl_eq_reflectC,
    LP.fillH_image_reflectC]

/-- The reflection of a path image. -/
theorem refl_image_path (p : ℝ → ℂ) : refl '' (p '' Icc 0 1) = (fun s => refl (p s)) '' Icc 0 1 :=
  image_image refl p (Icc 0 1)

/-- The reflected complement of the filled hull. -/
theorem refl_image_H_diff_fillH (A : Set ℂ) : refl '' (H \ fillH A) = H \ fillH (refl '' A) := by
  rw [refl_eq_reflectC]; exact (LP.H_diff_fillH_image_reflectC A).symm

/-! ### Lemma S2 reflected -/

/-- **Lemma S2's hull restriction, reflected** (SB2(2)): for a path image `A` from `0` in `ℍ̄` on the closed left of a
proper curve `β₀` from `0`, `R = max (A ∩ ℝ) ≥ 0`, `β₀` visits `R` at some `t_R` (`t_R = 0` if `R = 0`),
`β₀([0, t_R]) ⊆ K_A`, `β₀((t_R, ∞)) ⊆ closure D_A`, and every later interior point of `β₀` off `A` lies in `D_A`. -/
theorem s2HullRight {p : ℝ → ℂ} {β₀ : ℝ≥0 → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedLeftSide β₀) :
    0 ≤ realMax (p '' Icc 0 1) ∧
      ∃ tR : ℝ≥0, β₀ tR = realMax (p '' Icc 0 1) ∧ (realMax (p '' Icc 0 1) = 0 → tR = 0) ∧
        β₀ '' Icc 0 tR ⊆ hullK (p '' Icc 0 1) ∧
        β₀ '' Ioi tR ⊆ closure (H \ fillH (p '' Icc 0 1)) ∧
        ∀ t : ℝ≥0, tR < t → β₀ t ∈ H → β₀ t ∉ p '' Icc 0 1 → β₀ t ∈ H \ fillH (p '' Icc 0 1) := by
  set A := p '' Icc 0 1 with hAdef
  set p' : ℝ → ℂ := fun s => refl (p s) with hp'
  have hA' : p' '' Icc 0 1 = refl '' A := (refl_image_path p).symm
  have hp'c : ContinuousOn p' (Icc 0 1) := continuous_refl.comp_continuousOn hp
  have hp'0 : p' 0 = 0 := by
    show refl (p 0) = 0
    rw [hp0]; simp [Supp9B.refl]
  have hp'H : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p' s).im := fun s hs => by
    show 0 ≤ (refl (p s)).im
    rw [refl_im]; exact hpH s hs
  have hβ' := isProperCurve_reflectCurve hβ
  have hβ'0 : reflectCurve β₀ 0 = 0 := by
    show refl (β₀ 0) = 0
    rw [hβ0]; simp [Supp9B.refl]
  have h0im : (β₀ 0).im = 0 := by rw [hβ0]; rfl
  have hsub : p' '' Icc 0 1 ⊆ closedRightSide (reflectCurve β₀) := by
    rw [hA']
    exact (image_mono hA).trans (refl_image_closedLeftSide_subset hβ.2.2.1 h0im)
  obtain ⟨hmin, tL, htL, htL0, hhull, hcl, hD⟩ := s2HullStatement p' (reflectCurve β₀) hp'c hp'0 hp'H hβ' hβ'0 hsub
  rw [hA', realMin_refl_image] at hmin htL htL0
  rw [hA'] at hhull hcl hD
  have hR : β₀ tL = (realMax A : ℂ) := by
    have h1 : refl (β₀ tL) = ((-realMax A : ℝ) : ℂ) := htL
    have h2 := congrArg Supp9B.refl h1
    rw [refl_refl, refl_ofReal, neg_neg] at h2
    exact h2
  refine ⟨by linarith, tL, hR, fun h => htL0 (by rw [h, neg_zero]), ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    have h1 : reflectCurve β₀ t ∈ hullK (refl '' A) := hhull ⟨t, ht, rfl⟩
    rw [← refl_image_hullK] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    have : w = β₀ t := refl_injective hwe
    exact this ▸ hw
  · rintro _ ⟨t, ht, rfl⟩
    have h1 : reflectCurve β₀ t ∈ closure (H \ fillH (refl '' A)) := hcl ⟨t, ht, rfl⟩
    rw [← refl_image_H_diff_fillH] at h1
    have h2 : Supp9B.refl (reflectCurve β₀ t) ∈ Supp9B.refl '' closure (refl '' (H \ fillH A)) := mem_image_of_mem _ h1
    have h3 := image_closure_subset_closure_image continuous_refl h2
    rw [refl_image_refl_image] at h3
    have h4 : Supp9B.refl (reflectCurve β₀ t) = β₀ t := refl_refl (β₀ t)
    rwa [h4] at h3
  · intro t ht hH hnA
    have hH' : reflectCurve β₀ t ∈ H := refl_mem_H hH
    have hnA' : reflectCurve β₀ t ∉ refl '' A := by
      rintro ⟨w, hw, hwe⟩
      exact hnA (refl_injective hwe ▸ hw)
    have h1 := hD t ht hH' hnA'
    rw [← refl_image_H_diff_fillH] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    have : w = β₀ t := refl_injective hwe
    exact this ▸ hw

/-- **Lemma S2's one-sided lift, reflected** (SB2(2): "the actual completed lower tail has an injective, proper lift"):
in the setting of `s2HullRight`, if the inverse of a right entry chart `c` of `D_A` at `R` has a continuous
finite-fibre extension `g` to `ℍ̄`, the tail of `β₀` after its visit `t_R` to `R` has a proper lift `γ` from `0` with
`g ∘ γ = β₀(t_R + ·)`. -/
theorem s2LiftRight {p : ℝ → ℂ} {β₀ : ℝ≥0 → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedLeftSide β₀) {c : Chart} {g : ℂ → ℂ}
    (hc : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) {tR : ℝ≥0}
    (htR : β₀ tR = realMax (p '' Icc 0 1)) :
    ∃ γ : ℝ≥0 → ℂ, IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s : ℝ≥0, g (γ s) = β₀ (tR + s) := by
  set A := p '' Icc 0 1 with hAdef
  set p' : ℝ → ℂ := fun s => Supp9B.refl (p s) with hp'
  have hA' : p' '' Icc 0 1 = Supp9B.refl '' A := (refl_image_path p).symm
  have hp'c : ContinuousOn p' (Icc 0 1) := continuous_refl.comp_continuousOn hp
  have hp'0 : p' 0 = 0 := by
    show Supp9B.refl (p 0) = 0
    rw [hp0]; simp [Supp9B.refl]
  have hp'H : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p' s).im := fun s hs => by
    show 0 ≤ (Supp9B.refl (p s)).im
    rw [refl_im]; exact hpH s hs
  have hβ' := isProperCurve_reflectCurve hβ
  have hβ'0 : reflectCurve β₀ 0 = 0 := by
    show Supp9B.refl (β₀ 0) = 0
    rw [hβ0]; simp [Supp9B.refl]
  have h0im : (β₀ 0).im = 0 := by rw [hβ0]; rfl
  have hsub : p' '' Icc 0 1 ⊆ closedRightSide (reflectCurve β₀) := by
    rw [hA']
    exact (image_mono hA).trans (refl_image_closedLeftSide_subset hβ.2.2.1 h0im)
  -- the reflected chart is a left entry chart at `−R = min (ρ A ∩ ℝ)`
  have hc' : IsLeftEntryChart (p' '' Icc 0 1) (realMin (p' '' Icc 0 1)) (reflChart c) := by
    rw [hA', realMin_refl_image]
    exact isLeftEntryChart_reflChart hc
  set g' : ℂ → ℂ := fun w => Supp9B.refl (g (Supp9B.refl w)) with hg'
  have hg'c : ContinuousOn g' {z | 0 ≤ z.im} := by
    refine continuous_refl.comp_continuousOn (hgc.comp continuous_refl.continuousOn fun w (hw : 0 ≤ w.im) => ?_)
    show 0 ≤ (Supp9B.refl w).im
    rw [refl_im]; exact hw
  have hg'i : EqOn g' (reflChart c).2.1 H := fun w hw => by
    show Supp9B.refl (g (Supp9B.refl w)) = Supp9B.refl (c.2.1 (Supp9B.refl w))
    rw [hgi (refl_mem_H hw)]
  have hg'f : ∀ z, (g' ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite := fun z => by
    refine ((hgf (Supp9B.refl z)).image Supp9B.refl).subset fun w hw => ?_
    obtain ⟨hwz, hwi⟩ := hw
    refine ⟨Supp9B.refl w, ⟨?_, ?_⟩, refl_refl w⟩
    · show g (Supp9B.refl w) = Supp9B.refl z
      have h1 : Supp9B.refl (g (Supp9B.refl w)) = z := hwz
      rw [← h1, refl_refl]
    · show 0 ≤ (Supp9B.refl w).im
      rw [refl_im]; exact hwi
  have htR' : reflectCurve β₀ tR = realMin (p' '' Icc 0 1) := by
    rw [hA', realMin_refl_image]
    show Supp9B.refl (β₀ tR) = ((-realMax A : ℝ) : ℂ)
    rw [htR, refl_ofReal]
  obtain ⟨γ', hγ', hγ'0, hγ'g⟩ := s2LiftStatement p' (reflectCurve β₀) hp'c hp'0 hp'H hβ' hβ'0 hsub (reflChart c)
    g' hc' hg'c hg'i hg'f tR htR'
  refine ⟨reflectCurve γ', isProperCurve_reflectCurve hγ', ?_, fun s => ?_⟩
  · show Supp9B.refl (γ' 0) = 0
    rw [hγ'0]; simp [Supp9B.refl]
  · have h1 : Supp9B.refl (g (Supp9B.refl (γ' s))) = Supp9B.refl (β₀ (tR + s)) := hγ'g s
    have h2 := congrArg Supp9B.refl h1
    rw [refl_refl, refl_refl] at h2
    exact h2

end InteractingSLE.Theorem14.SB.Lk
