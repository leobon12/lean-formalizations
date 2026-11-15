/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrVisit

/-!
# A common-time input with seed corners allowed

PROVE-R6-TWO. This is the precise remaining geometric construction,
common to all three two-outer shapes. It is explicitly conditional.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Tr

/-- **Named, unproved common-time geometry.** Astra §§2 and 4 must
construct `SameTimeLeftData` for the actual current charts, on the
non-boundary geometric event intersected with Aux. 136's tip event.
The quantifier over one-chain representations introduces no new null
sets: the asserted event works simultaneously for these representations.
No later-time face, local force-landing patch or non-corner condition
is an input. -/
def HasSameTimeLeftGeometry (V P : Set ℂ) (I : ℝ → Chart) (ℓ : ℝ → ℝ)
    (O : Chart) (t : ℝ) (p : ℂ) (v : ℝ) : Prop :=
  ∀ M : InnerChain V P I p, M.time = t →
    (∀ q ∈ Ico M.time (M.time + M.horizon), ℓ q = WangWu.chartAL M.driver q) →
    ∃ EO : ℂ → ℂ, EqOn EO O.2.1 H ∧ ContinuousOn EO Hbar ∧
      Nonempty (SameTimeLeftData O (I M.time) EO P p v (WangWu.chartAL M.driver M.time))

/-- The geometric input is consumed at the common original time;
the proved window supplies all later real-time faces, with fixed outer
interval and test points, and the actual inner geometric mark. -/
theorem faceAt_near_of_sameTime {V P : Set ℂ} {I : ℝ → Chart} {ℓ : ℝ → ℝ}
    {O : Chart} {t : ℝ} {p : ℂ} {ρL ρR σL σR vL vR : Fin 1 → ℝ}
    (hgeom : HasSameTimeLeftGeometry V P I ℓ O t p (vL 0))
    (M : InnerChain V P I p) (hMt : M.time = t)
    (hmark : ∀ q ∈ Ico M.time (M.time + M.horizon), ℓ q = WangWu.chartAL M.driver q)
    (hO : O.IsConformal) (wR : ℝ → Fin 1 → ℝ) (hρ : ρL 0 = σL 0) :
    ∃ θ > 0, ∃ (J : Set ℝ) (y ξ : ℝ), ∀ q : ℝ, t < q → q < t + θ →
      FaceAt ρL ρR σL σR vL vR (fun _ => ℓ q) (wR q) O (I q) J y ξ := by
  obtain ⟨EO, hEO, hEOc, ⟨F⟩⟩ := hgeom M hMt hmark
  obtain ⟨θ₀, hθ₀, hf⟩ := faceAt_left_near M hO hEO hEOc wR hρ F
  refine ⟨min θ₀ M.horizon, lt_min hθ₀ M.horizon_pos, F.interval, F.shared, F.exposed, fun q hlo hhi => ?_⟩
  have hqt : M.time < q := by rwa [hMt]
  have hqθ : q < M.time + θ₀ := by rw [hMt]; exact hhi.trans_le (add_le_add le_rfl (min_le_left _ _))
  have hqh : q ∈ Ico M.time (M.time + M.horizon) := by
    rw [hMt]
    exact ⟨hlo.le, hhi.trans_le (add_le_add le_rfl (min_le_right _ _))⟩
  rw [hmark q hqh]
  exact hf q hqt hqθ

end InteractingSLE.Sec7.R6Tr
