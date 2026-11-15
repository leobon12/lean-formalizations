/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdLateOrd
import InteractingSLE.Spec.Supplement.AbsMergeFixed

/-!
# Theorem 1.5's leaf 3: no force gap is zero at a fixed time

Packet PROVE-T15-ORDDET5. PROVE-T15-ORDDET4 reduced "the moving tip of a continuation is interior at a deterministic
line" to the named statement `OrdLate.FixedTimeGapStatement κ` (for every integrated `SLE_κ(ρ)` evolution and every
fixed `t > 0`, almost surely on `{t < ζ}` the driver differs from every force point at time `t`). That statement is
PROVE-ABSMERGE's `Theorem14.AbsMerge.ae_forall_ne_of_isIntegratedSLEEvolution` (Lévy's 0–1 law against a fresh
Gaussian increment; it uses only Definition 2.1, so it is safe for every input of Theorems 1.2–1.3, R48).

* **`OrdLate.fixedTimeGapStatement`**: `FixedTimeGapStatement κ` for every `κ > 0`;
* **`OrdLate.ae_mem_H_at`**: the tip of a flow line at a fixed positive time is interior almost surely on
  `{t < ζ}` (`κ ≤ 4`), with no named input;
* **`OrdLate.ae_isOrdinaryRetainedPair_later_snd_at`**, **`OrdLate.ae_isOrdinaryRetainedPair_later_fst_at`**: at a
  deterministic later line, the later pair of a continuation without a new contact is ordinary as soon as both tips are
  active (the "moving tip interior" premise of PROVE-T15-ORDDET4's reductions is discharged).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.RLC.OrdLate

open Supp7

/-- **No force gap is zero at a fixed positive time** (`FixedTimeGapStatement`, PROVE-T15-ORDDET4's named input), for
every `κ > 0`: PROVE-ABSMERGE's `ae_forall_ne_of_isIntegratedSLEEvolution`. -/
theorem fixedTimeGapStatement {κ : ℝ} (hκ : 0 < κ) : FixedTimeGapStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ hE t ht
  exact Theorem14.AbsMerge.ae_forall_ne_of_isIntegratedSLEEvolution hκ hF hE ht

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The tip of a flow line at a fixed positive time is interior** (`κ ≤ 4`), almost surely on `{t < ζ}`:
`ae_mem_H_at_of_fixedTimeGap` with `fixedTimeGapStatement`. -/
theorem ae_mem_H_at {x θ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hfl : IsFlowLine κ b jumps x θ P h η ζ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζ ω → η ω t ∈ QuantumZipper.H :=
  ae_mem_H_at_of_fixedTimeGap (fixedTimeGapStatement hκ) hκ hκ4 hfl t ht

variable {x₁ x₂ θ₁ θ₂ : ℝ} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Ordinary later lines of the second continuation at a deterministic line**: for deterministic `u, r, t`, almost
surely, an ordinary pair `(u, r)` continued along the second path to `r + t < ζ₂` without a new contact with
`η₁[0,u]` is ordinary at `(u, r + t)` as soon as both tips are active there (the moving tip is interior almost
surely, `ae_mem_H_at`; at `t = 0` it is the old tip). -/
theorem ae_isOrdinaryRetainedPair_later_snd_at (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) (u r t : ℝ≥0) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω → (∀ s, r < s → s ≤ r + t → η₂ ω s ∉ η₁ ω '' Icc 0 u) →
      η₁ ω u ∈ closure (activeDomain (η₁ ω) u (η₂ ω) (r + t)) →
      η₂ ω (r + t) ∈ closure (activeDomain (η₁ ω) u (η₂ ω) (r + t)) →
      IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) (r + t) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r + t) with h0 | hpos
  · filter_upwards [ae_isOrdinaryRetainedPair_later_snd hκ hκ4 hb hx hθ hh hη₁ hη₂] with ω hω hord hlt hnc h1 h2
    have hrt : r + t = r := by
      have hr : r = 0 := le_antisymm (by rw [h0]; exact le_add_right le_rfl) zero_le
      rw [← h0, hr]
    exact hω u r t hord hlt hnc (by rw [hrt]; exact hord.2.2.2.1) h1 h2
  · filter_upwards [ae_isOrdinaryRetainedPair_later_snd hκ hκ4 hb hx hθ hh hη₁ hη₂,
      ae_mem_H_at hκ hκ4.le hη₂ (r + t) hpos] with ω hω hH hord hlt hnc h1 h2
    exact hω u r t hord hlt hnc (hH hlt) h1 h2

/-- **Ordinary later lines of the first continuation at a deterministic line** (the mirror of
`ae_isOrdinaryRetainedPair_later_snd_at`). -/
theorem ae_isOrdinaryRetainedPair_later_fst_at (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) (u r t : ℝ≥0) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ((u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → (∀ s, u < s → s ≤ u + t → η₁ ω s ∉ η₂ ω '' Icc 0 r) →
      η₁ ω (u + t) ∈ closure (activeDomain (η₁ ω) (u + t) (η₂ ω) r) →
      η₂ ω r ∈ closure (activeDomain (η₁ ω) (u + t) (η₂ ω) r) →
      IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) (u + t) (η₂ ω) (ζ₂ ω) r := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u + t) with h0 | hpos
  · filter_upwards [ae_isOrdinaryRetainedPair_later_fst hκ hκ4 hb hx hθ hh hη₁ hη₂] with ω hω hord hlt hnc h1 h2
    have hut : u + t = u := by
      have hu : u = 0 := le_antisymm (by rw [h0]; exact le_add_right le_rfl) zero_le
      rw [← h0, hu]
    exact hω u r t hord hlt hnc (by rw [hut]; exact hord.2.2.1) h1 h2
  · filter_upwards [ae_isOrdinaryRetainedPair_later_fst hκ hκ4 hb hx hθ hh hη₁ hη₂,
      ae_mem_H_at hκ hκ4.le hη₁ (u + t) hpos] with ω hω hH hord hlt hnc h1 h2
    exact hω u r t hord hlt hnc (hH hlt) h1 h2

end InteractingSLE.RLC.OrdLate
