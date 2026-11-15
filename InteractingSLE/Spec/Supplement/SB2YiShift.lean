/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkNormSide
import InteractingSLE.Foundations.Loewner.YuanCorollary13

/-!
# A Loewner trace after a time, read through the Loewner map at that time

Packet PROVE-T14-SB2LIFT (round 33, D51 item 3). For a Loewner trace `η` of `W`, injective on `[0, t]`, and
`0 ≤ τ ≤ t`, the shifted tip `γ = loewnerTip (shiftDrive W τ)` (Yuan's Corollary 1.3,
`IsLoewnerTrace.isLoewnerTrace_shift_and_extendFrom`):

* **`shift_facts`**: `γ` is a Loewner trace of `W(τ + ·) − W(τ)`, lying over `η(τ + ·)`; it is injective on
  `[0, t − τ]`; and at every `u ∈ (0, t − τ]` with `η(τ + u) ∈ ℍ`, `γ u ∈ ℍ` and `f_τ(η(τ + u)) = γ u`
  (`WalkNorm.extendFrom_real_cases`: a real boundary value of `F̄_τ` is real or a trace point before `τ`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.SB.Sx

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The trace after `τ` in the coordinates of `f_τ`.** -/
theorem shift_facts (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {τ t : ℝ} (hτ : 0 ≤ τ)
    (hτt : τ ≤ t) (hinj : InjOn η (Icc 0 t)) :
    IsLoewnerTrace (shiftDrive W τ) (loewnerTip (shiftDrive W τ)) ∧
      (∀ u, 0 ≤ u → extendFrom H (fwdMapInv W τ) (loewnerTip (shiftDrive W τ) u) = η (τ + u)) ∧
      InjOn (loewnerTip (shiftDrive W τ)) (Icc 0 (t - τ)) ∧
      ∀ u, 0 < u → u ≤ t - τ → η (τ + u) ∈ H →
        loewnerTip (shiftDrive W τ) u ∈ H ∧ fwdMap W τ (η (τ + u)) = loewnerTip (shiftDrive W τ) u := by
  obtain ⟨hγ, hγF⟩ := hη.isLoewnerTrace_shift_and_extendFrom hW hW0 hτ
  set γ := loewnerTip (shiftDrive W τ) with hγdef
  refine ⟨hγ, hγF, fun u₁ h₁ u₂ h₂ he => ?_, fun u hu hut hH => ?_⟩
  · have h := hγF u₁ h₁.1
    rw [he, hγF u₂ h₂.1] at h
    have := hinj ⟨by linarith [h₂.1], by linarith [h₂.2]⟩ ⟨by linarith [h₁.1], by linarith [h₁.2]⟩ h
    linarith
  · have hbar : γ u ∈ Hbar := (hη.extendFrom_shift_tip hW hW0 hτ hu.le).1
    have hγH : γ u ∈ H := by
      by_contra hn
      have him : (γ u).im = 0 := le_antisymm (not_lt.1 hn) hbar
      have he : γ u = (((γ u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      have hF := hγF u hu.le
      rcases WalkNorm.extendFrom_real_cases hη hW hW0 hτ (γ u).re with h | ⟨s, hs, hse⟩
      · rw [← he, hF] at h
        have : (0 : ℝ) < (η (τ + u)).im := hH
        rw [h] at this
        exact lt_irrefl _ this
      · rw [← he, hF] at hse
        have := hinj ⟨hs.1, hs.2.trans hτt⟩ ⟨by linarith, by linarith⟩ hse
        linarith [hs.2]
    refine ⟨hγH, ?_⟩
    have hF := hγF u hu.le
    rw [extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 hτ) hγH] at hF
    rw [← hF, QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hτ hγH]

end InteractingSLE.Theorem14.SB.Sx
