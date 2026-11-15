/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC11Prefixes
import InteractingSLE.Spec.Supplement.G7ClockGeom

/-!
# Half capacity and a normalized relative generating trace

Packet PROVE-T14-GW2ROOT2. These adapters use the existing capacity
composition and G7 hull identity. The geometric identification of the
actual prefix images remains an explicit input, distinct from a capacity
increment hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootC11

open Restart

/-- On a bounded attached set, GW2's half capacity is the usual hull capacity. -/
theorem capOf_eq_hcapSet {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hcA : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) :
    capOf A = ConformalImage.hcapSet (fillH A) / 2 := by
  rw [capOf, dite_eq_left ⟨hA, hcA⟩,
    ConformalImage.hcapSet_eq (isHPHull_fillH_of_isPreconnected hA hcA)]
  rfl

/-- Monotonicity applies when both sets satisfy the defining geometric conditions. -/
theorem capOf_mono {A B : Set ℂ} (hAB : A ⊆ B)
    (hA : Bornology.IsBounded A) (hcA : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}))
    (hB : Bornology.IsBounded B) (hcB : IsPreconnected (B ∪ {z : ℂ | z.im ≤ 0})) :
    capOf A ≤ capOf B := by
  rw [capOf, dite_eq_left ⟨hA, hcA⟩, capOf, dite_eq_left ⟨hB, hcB⟩]
  exact div_le_div_of_nonneg_right (hcapFill_mono hAB hA hcA hB hcB) zero_le_two

/-- Scaling a filled trace multiplies its capacity by the square of the scale. -/
theorem hcapSet_fillH_affine {A : Set ℂ} (hA : IsHPHull (fillH A))
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ConformalImage.hcapSet (fillH (affHomeo a ha x '' A)) =
      a ^ 2 * ConformalImage.hcapSet (fillH A) := by
  rw [fillH_image_affHomeo, ConformalImage.hcapSet_eq (hA.image_affHomeo ha),
    ConformalImage.hcapSet_eq hA]
  exact HPHull.hcap_affHomeo ⟨_, hA⟩ ha

/-- Geometry of two actual prefix images, expressed through compact representatives
of their fillings and the path added in the old hydrodynamic chart. No capacity
identity or clock inequality is a field of this predicate. -/
structure IsCapacityExtension (A B K P : Set ℂ) (g φ ψ : ℂ → ℂ)
    (x₀ : ℂ) (Γ : ℝ≥0 → ℂ) (t : ℝ≥0) : Prop where
  bounded_before : Bornology.IsBounded A
  attached_before : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})
  bounded_after : Bornology.IsBounded B
  attached_after : IsPreconnected (B ∪ {z : ℂ | z.im ≤ 0})
  fill_before : fillH A = fillH K
  fill_after : fillH B = fillH P
  compact_after : IsCompact P
  chart : Supp7.IsDomChart K φ ψ
  mapOut : IsMapOut (fillH K) g
  centered : ∀ z, φ z = g z - x₀
  real_shift : x₀.im = 0
  after_subset : P ⊆ K ∪ ψ '' (Γ '' Icc 0 t)
  path_after : ∀ r ∈ Icc 0 t, ψ (Γ r) ∈ P

/-- The geometric map-out identity gives the exact unscaled half-capacity increment. -/
theorem IsCapacityExtension.capOf_eq_add {A B K P : Set ℂ} {g φ ψ : ℂ → ℂ}
    {x₀ : ℂ} {Γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hG : IsCapacityExtension A B K P g φ ψ x₀ Γ t) (hAB : A ⊆ B)
    (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓ0 : (Γ 0).im ≤ 0) :
    capOf B = capOf A + ConformalImage.hcapSet (fillH (Γ '' Icc 0 t)) / 2 := by
  have hKh : IsHPHull (fillH K) := hG.fill_before ▸
    isHPHull_fillH_of_isPreconnected hG.bounded_before hG.attached_before
  have hPh : IsHPHull (fillH P) := hG.fill_after ▸
    isHPHull_fillH_of_isPreconnected hG.bounded_after hG.attached_after
  have hKP : fillH K ⊆ fillH P := by
    rw [← hG.fill_before, ← hG.fill_after]
    exact fillH_mono hAB
  have hadd := hG.chart.hcapSet_fillH_eq_add hG.mapOut hG.centered hG.real_shift
    hKh hPh hG.compact_after hKP hG.after_subset hΓc hΓ0 hG.path_after
  rw [← hG.fill_before, ← hG.fill_after] at hadd
  rw [capOf_eq_hcapSet hG.bounded_before hG.attached_before,
    capOf_eq_hcapSet hG.bounded_after hG.attached_after, hadd]
  ring

/-- A relative trace that generates capacity time after scaling by `a` contributes
exactly its observation time to the capacity normalized by `a²`. -/
theorem IsCapacityExtension.scaled_capOf_eq_add {A B K P : Set ℂ} {g φ ψ : ℂ → ℂ}
    {x₀ : ℂ} {Γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hG : IsCapacityExtension A B K P g φ ψ x₀ Γ t) (hAB : A ⊆ B)
    (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓ0 : (Γ 0).im ≤ 0)
    {a : ℝ} (ha : 0 < a) {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {x : ℝ}
    (hgen : IsGeneratingTrace w T (fun r => (a : ℂ) * Γ r - x))
    (hw : ContinuousOn w {r | (r : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < T) :
    a ^ 2 * capOf B = a ^ 2 * capOf A + t := by
  have htrace := Restart.IsGeneratingTrace.hcapSet_fillH_add hgen hw hw0 ht
  have himg : (fun r => (a : ℂ) * Γ r) '' Icc 0 t =
      affHomeo a ha 0 '' (Γ '' Icc 0 t) := by
    rw [image_image, coe_affHomeo]
    simp only [ofReal_zero, add_zero]
  rw [himg, hcapSet_fillH_affine (isHPHull_fillH_image hΓc hΓ0) ha 0] at htrace
  rw [hG.capOf_eq_add hAB hΓc hΓ0]
  calc
    a ^ 2 * (capOf A + ConformalImage.hcapSet (fillH (Γ '' Icc 0 t)) / 2) =
        a ^ 2 * capOf A +
          (a ^ 2 * ConformalImage.hcapSet (fillH (Γ '' Icc 0 t))) / 2 := by ring
    _ = a ^ 2 * capOf A + t := by rw [htrace]; ring

end InteractingSLE.Theorem14.GW2TipSystem.RootC11
