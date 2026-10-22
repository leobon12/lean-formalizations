import HigherDimLQGMetric.LfppTight.HighFieldTail
import HigherDimLFPP.Paths.Compare

/-! Local LFPP comparison for the finite band plus its fixed high band. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_internal_coupled_upper {d : ℕ} (ξ c M : ℝ)
    (H Ψ : Rd d → ℝ) (hH : Continuous H) (hΨ : Continuous Ψ)
    (V : Set (Rd d)) (hM : ∀ z ∈ V, |Ψ z| ≤ M) (x y : Rd d) :
    HigherDimLFPP.lfppDistOn ξ (fun z => H z - c + Ψ z) V x y ≤
      Real.exp (ξ * -c) * Real.exp (|ξ| * M) *
        HigherDimLFPP.lfppDistOn ξ H V x y := by
  have hfield : (fun z => H z - c + Ψ z) = fun z => (H z + Ψ z) + -c := by
    funext z
    ring
  rw [hfield, HigherDimLFPP.lfppDistOn_add_const]
  have hle := HigherDimLFPP.lfppDistOn_le_exp_mul
    (ζ := ξ) (φ := fun z => H z + Ψ z) (ψ := H)
    (hH.add hΨ) hH (V := V) (x := x) (y := y) (M := M) (by
      intro z hz
      simpa only [show H z + Ψ z - H z = Ψ z by ring] using hM z hz)
  calc
    Real.exp (ξ * -c) * HigherDimLFPP.lfppDistOn ξ (fun z => H z + Ψ z) V x y ≤
        Real.exp (ξ * -c) *
          (Real.exp (|ξ| * M) * HigherDimLFPP.lfppDistOn ξ H V x y) :=
      mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = _ := by ring

theorem l6a_internal_coupled_lower {d : ℕ} (ξ c M : ℝ)
    (H Ψ : Rd d → ℝ) (hH : Continuous H) (hΨ : Continuous Ψ)
    (V : Set (Rd d)) (hM : ∀ z ∈ V, |Ψ z| ≤ M) (x y : Rd d) :
    Real.exp (ξ * -c) * HigherDimLFPP.lfppDistOn ξ H V x y ≤
      Real.exp (|ξ| * M) *
        HigherDimLFPP.lfppDistOn ξ (fun z => H z - c + Ψ z) V x y := by
  have hfield : (fun z => H z - c + Ψ z) = fun z => (H z + Ψ z) + -c := by
    funext z
    ring
  rw [hfield, HigherDimLFPP.lfppDistOn_add_const]
  have hle := HigherDimLFPP.lfppDistOn_le_exp_mul
    (ζ := ξ) (φ := H) (ψ := fun z => H z + Ψ z)
    hH (hH.add hΨ) (V := V) (x := x) (y := y) (M := M) (by
      intro z hz
      simpa only [show H z - (H z + Ψ z) = -(Ψ z) by ring, abs_neg] using hM z hz)
  calc
    Real.exp (ξ * -c) * HigherDimLFPP.lfppDistOn ξ H V x y ≤
        Real.exp (ξ * -c) *
          (Real.exp (|ξ| * M) * HigherDimLFPP.lfppDistOn ξ (fun z => H z + Ψ z) V x y) :=
      mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = Real.exp (|ξ| * M) *
          (Real.exp (ξ * -c) * HigherDimLFPP.lfppDistOn ξ (fun z => H z + Ψ z) V x y) := by
      ring

end HigherDimLQGMetric
