/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WmDec
import InteractingSLE.Spec.Supplement.GW2SdhInst

/-!
# GW2's stage word map, part 6: the instance choice with the word map and R62's coefficients

Packet PROVE-GW2-GEOM2 (round 7). The schedule instance (`GW2Sdh.schedInst`, `GW2Sdi.schedInstS`) takes its word map,
record event, coefficients, centring and marks from a `GW2Sdh.SchedChoice`. This file fills the word-map part:

* **`wmChoice`**: `β = schedWordMap κ c′ x s L N hN θa` (the flowed root word at root `x`, read from the augmented stage
  record), `σa = specOffset κ + θa χ`, `kc = χ` (R62's offset, the coefficients of `GW2RdSafeData`), with the record
  event `E₀`, the centring `u₀` and the marks `ℋ` left to the instance's owner;
* **`wmChoice_targets`**: the `hβ` hypothesis of `GW2Sdj.schedInstS_good'` / `GW2Sdi.schedInstS_good`
  (measurable, countably many word types at `κ`, sorted).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Wm

open Restart Exist.StagedLaw GW2JointKernel

/-- **The instance choice with the stage word map** and R62's coefficients `σa = specOffset κ + θa χ`, `kc = χ`. -/
def wmChoice {Ω : Type u} (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ)
    (hN : L.length = N) (θa : ℝ) (E₀ : Set RecData) (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) :
    GW2Sdh.SchedChoice Ω where
  β := schedWordMap κ c' x s L N hN θa
  E₀ := E₀
  σa := specOffset κ + θa * chiC κ
  kc := chiC κ
  u₀ := u₀
  ℋ := ℋ

/-- **The word-map hypothesis `hβ` of the instance's `Good`** for `wmChoice`. -/
theorem wmChoice_targets {Ω : Type u} (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ)
    (hN : L.length = N) (θa : ℝ) (E₀ : Set RecData) (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) :
    Measurable (wmChoice κ c' x s L N hN θa E₀ u₀ ℋ).β ∧
      (range fun y => Supp8.Q3Stop.wordType κ ((wmChoice κ c' x s L N hN θa E₀ u₀ ℋ).β y)).Countable ∧
      ∀ y, ((wmChoice κ c' x s L N hN θa E₀ u₀ ℋ).β y).IsSorted :=
  schedWordMap_targets κ c' x s L N hN θa κ

end InteractingSLE.Theorem14.GW2Wm
