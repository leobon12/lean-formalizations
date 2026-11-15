/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeEPrefix
import InteractingSLE.Spec.Supplement.GB6ReadDGauge

/-!
# Compact separations: congruence, time change, and GB6's readout (S3)

Packet PROVE-GW2-BUF (S3, ruling R115). GB6's causal separation readout `ReadD.separationRead s t` (rational
fractions of the read-back physical trace and of the counterflow trace) and J31's physical gauge
`RootJ31.separationRead` (rational fractions of the recorded physical trace) are both `compactSeparation`s. They
agree once the read-back trace is the physical trace composed with the inverse clock.

* `compactSeparation_congr`: readers that agree on the prefixes give the same separation;
* `exists_unit_mul`, **`compactSeparation_comp`**: a continuous monotone clock `τ` from `0` changes time:
  `compactSeparation (X ∘ τ) A t s = compactSeparation X A (τ t) s`;
* **`separationRead_eq_compactSeparation`**: GB6's readout is the compact separation of its two readers when they are
  continuous on the prefixes.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.GaugeE Supp8.GB6.ReadD

/-- Readers agreeing on the prefixes give the same compact separation. -/
theorem compactSeparation_congr {X X' A A' : ℝ≥0 → ℂ} {t s : ℝ≥0} (hX : ∀ u ≤ t, X u = X' u)
    (hA : ∀ w ≤ s, A w = A' w) : compactSeparation X A t s = compactSeparation X' A' t s := by
  unfold compactSeparation prefixIntegrand
  congr 1
  funext p
  rw [hX _ (fraction_mul_le t p.1), hA _ (fraction_mul_le s p.2)]

/-- Every point of `[0, t]` is `t` times a point of the unit interval. -/
theorem exists_unit_mul {t u : ℝ≥0} (hu : u ≤ t) : ∃ y : UnitSegment, t * y.val = u := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · refine ⟨⟨0, le_rfl, zero_le⟩, ?_⟩
    rw [← ht] at hu ⊢
    simp only [mul_zero]
    exact (le_antisymm hu zero_le).symm
  · refine ⟨⟨u / t, zero_le, (div_le_one ht).2 hu⟩, ?_⟩
    change t * (u / t) = u
    rw [mul_div_cancel₀ _ ht.ne']

/-- **Time change of a compact separation** under a continuous monotone clock from `0`. -/
theorem compactSeparation_comp {X A : ℝ≥0 → ℂ} {τ : ℝ≥0 → ℝ≥0} {t s : ℝ≥0}
    (hτc : ContinuousOn τ (Icc 0 t)) (hτm : MonotoneOn τ (Icc 0 t)) (hτ0 : τ 0 = 0) :
    compactSeparation (fun u => X (τ u)) A t s = compactSeparation X A (τ t) s := by
  have himg : τ '' Icc 0 t = Icc 0 (τ t) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨zero_le, hτm hz ⟨zero_le, le_rfl⟩ hz.2⟩
    · have h := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t) hτc
      rwa [hτ0] at h
  unfold compactSeparation squareMin prefixIntegrand
  congr 1
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    have hz : τ (t * p.1.val) ∈ Icc 0 (τ t) :=
      himg ▸ ⟨t * p.1.val, ⟨zero_le, fraction_mul_le t p.1⟩, rfl⟩
    obtain ⟨y, hy⟩ := exists_unit_mul hz.2
    exact ⟨(y, p.2), by simp only [hy]⟩
  · rintro ⟨p, rfl⟩
    have hz : τ t * p.1.val ∈ τ '' Icc 0 t := by
      rw [himg]; exact ⟨zero_le, fraction_mul_le (τ t) p.1⟩
    obtain ⟨z, hzt, hze⟩ := hz
    obtain ⟨y, hy⟩ := exists_unit_mul hzt.2
    exact ⟨(y, p.2), by simp only [hy, hze]⟩

/-- **GB6's separation readout is the compact separation of its readers**, when they are continuous on the prefixes. -/
theorem separationRead_eq_compactSeparation (s t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ))
    (hX : ContinuousOn (fun u => physicalTrace s u p) (Iic t))
    (hA : ContinuousOn (fun v => recordTrace v p.1) (Iic s)) :
    ReadD.separationRead s t p =
      compactSeparation (fun u => physicalTrace s u p) (fun v => recordTrace v p.1) t s := by
  have hc : Continuous (prefixIntegrand (fun u => physicalTrace s u p) (fun v => recordTrace v p.1) t s) :=
    continuous_prefixIntegrand hX hA
  have hn := squareMin_nonneg hc (fun _ => separationValue_nonneg _ _)
  unfold ReadD.separationRead
  change (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
    (prefixIntegrand (fun u => physicalTrace s u p) (fun v => recordTrace v p.1) t s
      (Prod.map fractionCast fractionCast q))).toReal = _
  rw [rationalInf_eq_squareMin hc, ENNReal.toReal_ofReal hn]
  rfl

end InteractingSLE.Theorem14.GW2Bh
