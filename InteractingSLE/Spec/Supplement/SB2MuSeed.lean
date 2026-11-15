/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuLife

/-!
# Seed admissibility on the live event from the cell-wide stop bound

Packet PROVE-SB2-LCMEAN, round 13. K2's seed input `hseed` of `Mu.ae_isStopDrvMatch_of_lines` and
`Mu.ae_canonLife_eq_relLife`: almost surely on every type cell the type's seed is admissible. It follows from F2b′'s
cell-wide bound `V m ≤ thr` (SB2(1)'s `SB2LineVersionS.V_le_thr`) and the announcement of the stops (`0 ≤ ρs < V`, so
`V > 0`): at a threshold seed the threshold time is `0` (`Lv.thr_eq_zero_of_seed`).

* **`hseed_of_le_thr`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Mu

open Restart Exist.StagedLaw Lv Supp8.Q3Stop Ms

variable {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {c : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}

/-- **Seed admissibility on the type cells** from the cell-wide stop bound `V 0 ≤ thr` and the announced stops. -/
theorem hseed_of_le_thr (S : StageVersionS κ ψ P F 𝓖 A₁ A₂ Φ c types pc tL L relLife)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c F w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W (cellXL κ ψ c w) (cellXR κ ψ c w) ω) :
    ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c F w → ω ∈ seedCell κ ψ c F w := by
  intro w hw
  filter_upwards [hle w hw, S.ann 0] with ω h1 hann hω
  refine ⟨hω, fun hs => ?_⟩
  have hxL0 : ∀ ω i, cellXL κ ψ c w ω i ≤ 0 := fun ω => (FCDet.isOrderedForceWord_typeXL (c ω)).2.1
  have hxR0 : ∀ ω j, 0 ≤ cellXR κ ψ c w ω j := fun ω => (FCDet.isOrderedForceWord_typeXL (c ω)).2.2.2
  have hz := thr_eq_zero_of_seed (S.ver 0).W_zero (S.ver 0).W_cont hxL0 hxR0 hs
  have hpos : 0 < S.V 0 ω := lt_of_le_of_lt zero_le ((hann hω.1).1 0)
  have h2 := h1 hω
  rw [hz] at h2
  exact absurd (lt_of_lt_of_le hpos h2) (lt_irrefl _)

end InteractingSLE.Theorem14.SB.Mu
