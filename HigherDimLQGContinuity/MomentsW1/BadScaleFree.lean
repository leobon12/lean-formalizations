import HigherDimLQGContinuity.MomentsW1.BadScaleMeas

/-! # Free sites above the last bad scale -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLQGMetric.DGZ

/-- At every scale after `wnBadScale`, a nearby site is free at both adjacent levels. -/
theorem wnBadScale_free {d : ℕ} (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℕ → Rd d → Ω → ℝ} {ξ R : ℝ} {q : ℝ≥0∞}
    {n k : ℕ} {ω : Ω} (hk : 110 ≤ k) (hkn : k < n)
    (hMk : wnBadScale P H ξ R q n ω ≤ k) (x : Zd d) :
    ∃ y : Zd d, WithinInf ((k : ℤ) ^ 2) x (2 • y) ∧
      FreeSite (wnGood P H ξ R q k n ω) (2 • y) ∧
      FreeSite (wnGood P H ξ R q (k - 1) n ω) y := by
  obtain ⟨_, _, hsmall⟩ := wnBadScale_small hk hkn hMk
  obtain ⟨N₁, hN₁⟩ := wnRegion_bounded (d := d) R (k - 1)
  obtain ⟨N₂, hN₂⟩ := wnRegion_bounded (d := d) R k
  obtain ⟨N₃, hN₃⟩ := wnRough_support_bounded P H ξ R q k n
  let N : ℤ := N₁ + N₂ + N₃ + 1
  have hN : 0 ≤ N := by dsimp [N]; omega
  have hO₁ : ∀ y : Zd d, y ∉ wnGood P H ξ R q (k - 1) n ω →
      WithinInf N y 0 := by
    intro y hy i
    have hclosed : ω ∈ wnClosed P H ξ R q (k - 1) n y := by
      simpa [wnGood] using hy
    have hreg : y ∈ wnRegion R (k - 1) := hclosed.1
    have h := hN₁ y hreg i
    dsimp [N]
    exact h.trans (by omega)
  have hO₂ : ∀ y : Zd d, y ∉ wnGood P H ξ R q k n ω →
      WithinInf N y 0 := by
    intro y hy i
    have hclosed : ω ∈ wnClosed P H ξ R q k n y := by
      simpa [wnGood] using hy
    have hreg : y ∈ wnRegion R k := hclosed.1
    have h := hN₂ y hreg i
    dsimp [N]
    exact h.trans (by omega)
  have hNice : ∀ y : Zd d,
      y ∉ wnNice (wnGood P H ξ R q (k - 1) n ω) (wnGood P H ξ R q k n ω) →
      WithinInf N y 0 := by
    intro y hy i
    have hrough : ω ∈ wnRough P H ξ R q k n y := hy
    have hne : wnRough P H ξ R q k n y ≠ ∅ :=
      Set.nonempty_iff_ne_empty.mp ⟨ω, hrough⟩
    have h := hN₃ y hne i
    dsimp [N]
    exact h.trans (by omega)
  obtain ⟨y, hy, hy₂, hy₁⟩ := wnBadScale_free_of_smallClusters hd hsmall
    hNice hO₁ hO₂ hN x
  refine ⟨y, ?_, hy₂, hy₁⟩
  intro i
  have hD : 2 * wnRoughDiameter k + 3 ≤ k ^ 2 := by
    dsimp [wnRoughDiameter]
    have hk2 : 3 ≤ k ^ 2 := by nlinarith
    omega
  have hD' : 2 * (wnRoughDiameter k : ℤ) + 3 ≤ (k : ℤ) ^ 2 := by
    exact_mod_cast hD
  exact (hy i).trans hD'

end HigherDimLQGContinuity
