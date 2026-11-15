/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLvPinchUse

/-!
# S5's stage geometry: the link at real points

Packet PROVE-T14-SBLEAVES, item (2)(e) of the handoff. SB2(1)'s launch-form link (`Lv.IsRemainderLink`) identifies the
relative curve with the actual upper flow at interior relative points; S5's relative step needs the identity
`g (bR s) = β (tL + s)` at every time. `eqOn_Icc_of_dense_H` extends an identity between continuous curves from the
times at which a third curve is in `ℍ` to the whole interval, when those times are dense (a Loewner trace spends no
open time interval on `ℝ`, `FinRel.interior_real_times_eq_empty`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Lv

/-- **Extension from dense interior times.** Two curves continuous on `[0, T]` (`0 < T`) that agree whenever a third
curve `γ` is in `ℍ` agree on `[0, T]`, provided every open subinterval contains a time with `γ ∈ ℍ`. -/
theorem eqOn_Icc_of_dense_H {f₁ f₂ γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T)
    (h₁ : ContinuousOn f₁ (Icc 0 T)) (h₂ : ContinuousOn f₂ (Icc 0 T))
    (hdense : ∀ a b : ℝ≥0, a < b → b ≤ T → ∃ s ∈ Ioo a b, γ s ∈ H)
    (heq : ∀ s ∈ Icc 0 T, γ s ∈ H → f₁ s = f₂ s) : EqOn f₁ f₂ (Icc 0 T) := by
  refine EqOn.of_subset_closure (s := {s ∈ Icc 0 T | γ s ∈ H}) (fun s hs => heq s hs.1 hs.2) h₁ h₂
    (sep_subset _ _) ?_
  intro s hs
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases lt_or_eq_of_le hs.2 with hsT | rfl
  · set b : ℝ≥0 := min (s + ⟨ε / 2, by positivity⟩) T with hb
    have hsb : s < b := lt_min (lt_add_of_pos_right _ (by exact_mod_cast half_pos hε)) hsT
    obtain ⟨r, hr, hrH⟩ := hdense s b hsb (min_le_right _ _)
    refine ⟨r, ⟨⟨zero_le, hr.2.le.trans (min_le_right _ _)⟩, hrH⟩, ?_⟩
    have h1 : (r : ℝ) < s + ε / 2 := by
      have := hr.2.trans_le (min_le_left _ _); exact_mod_cast this
    have h2 : (s : ℝ) < r := by exact_mod_cast hr.1
    rw [NNReal.dist_eq, abs_lt]; constructor <;> linarith
  · set a : ℝ≥0 := s - ⟨ε / 2, by positivity⟩ with ha
    have has : a < s := tsub_lt_self hT (by exact_mod_cast half_pos hε)
    obtain ⟨r, hr, hrH⟩ := hdense a s has le_rfl
    refine ⟨r, ⟨⟨zero_le, hr.2.le⟩, hrH⟩, ?_⟩
    have h1 : (s : ℝ) - ε / 2 ≤ a := by
      rw [ha]
      have := NNReal.sub_def (r := s) (p := ⟨ε / 2, by positivity⟩)
      rw [this, Real.coe_toNNReal']
      exact le_max_left _ _
    have h2 : (a : ℝ) < r := by exact_mod_cast hr.1
    have h3 : (r : ℝ) < s := by exact_mod_cast hr.2
    rw [NNReal.dist_eq, abs_lt]; constructor <;> linarith

end InteractingSLE.Theorem14.SB.Lv
