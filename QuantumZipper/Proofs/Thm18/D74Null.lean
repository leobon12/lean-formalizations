import QuantumZipper.Proofs.Zipper.Cor15HullNull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D74: the SLE_κ trace has zero area, `0 < κ < 4`

One of the three curve facts used by Sheffield's proof of Theorem 1.8 (arXiv:1012.4797, §4.1,
p. 48: "we can define `h_t` arbitrarily on the measure zero set `η([0,t])`"; Berestycki–Powell,
arXiv:2404.16642, remark after Thm 8.13, p. 282: `η` "has Lebesgue measure zero").

Proof (the Fubini argument named in D74): a fixed `z ∈ ℍ` is a.s. not on the trace
(`Cor15Group.ae_notMem_sleTrace_lt_four`, from the one-point estimate), points below `ℝ` are never
on it (`Thm11Area.ae_im_sleTrace_nonneg`), and `ℝ` is Lebesgue-null; Fubini on `Ω × ℂ` with a
jointly measurable version of the trace (`RS.exists_measurable_sleTrace`). This is the proof of
`Thm11Area.ae_volume_sleTrace_eq_zero` (κ ∈ (4,8), AD-2) with the one-point input for `κ < 4`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace D74

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The SLE_κ trace is Lebesgue-null**, `0 < κ < 4`: a.s. `η[0,∞)` has zero area. -/
theorem ae_volume_sleTrace_eq_zero_lt_four (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) : ∀ᵐ ω ∂P, volume (sleTrace κ B ω '' Ici 0) = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨η, -, hηm, hηc, hηeq⟩ := RS.exists_measurable_sleTrace hB hκ (by linarith)
  set S := {p : Ω × ℂ | p.2 ∈ η p.1 '' Ici 0} with hSdef
  have hS : MeasurableSet S := Thm11Area.measurableSet_mem_image_Ici hηm hηc
  have himg : ∀ᵐ ω ∂P, η ω '' Ici 0 = sleTrace κ B ω '' Ici 0 :=
    hηeq.mono fun ω h => h.image_eq
  have hpt : ∀ z : ℂ, z.im ≠ 0 → P ((fun ω => (ω, z)) ⁻¹' S) = 0 := by
    intro z hz
    have hae : ∀ᵐ ω ∂P, z ∉ η ω '' Ici 0 := by
      rcases lt_or_gt_of_ne hz with hneg | hpos
      · filter_upwards [himg, Thm11Area.ae_im_sleTrace_nonneg hB hκ (by linarith)] with ω hi hnn
        rw [hi]
        rintro ⟨t, ht, rfl⟩
        exact absurd (hnn t ht) (not_le.2 hneg)
      · filter_upwards [himg,
          Cor15Group.ae_notMem_sleTrace_lt_four hB hκ hκ4 (show z ∈ H from hpos)] with ω hi h
        rwa [hi]
    exact measure_mono_null (t := {ω | ¬ z ∉ η ω '' Ici 0}) (fun ω hω => not_not.2 hω)
      (ae_iff.1 hae)
  have hprod : (P.prod volume) S = 0 := by
    rw [Measure.prod_apply_symm hS]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    refine measure_mono_null (fun z hz => ?_) Thm11Area.volume_setOf_im_eq_zero
    by_contra hz'
    exact hz (hpt z hz')
  rw [Measure.prod_apply hS] at hprod
  have hzero := (lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)).1 hprod
  filter_upwards [hzero, himg] with ω h hi
  rw [← hi]
  exact h

end D74
end Thm18Asm
end QuantumZipper
