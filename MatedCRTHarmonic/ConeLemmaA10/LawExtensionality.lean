import LQGMetric.Field.GFFLaw

/-!
# Extensionality of normalized distribution laws from mean-zero pairings

Mean-zero test pairings determine a distribution only modulo an additive constant. This file
uses the existing `LQGMetric.GFFLaw.sigma0` and `LQGMetric.GFFLaw.recenter` factorization to
upgrade equality of their joint laws to equality of laws on `DistC`, when both laws are supported
on the zero set of the same additive-equivariant normalization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.GFFInv

/-- A measurable function of a distribution's mean-zero pairings has the same pushforward under
two measures whose complete mean-zero pairing laws agree. -/
theorem map_eq_of_map_ev0_eq {μ ν : Measure DistC} {β : Type*} [MeasurableSpace β]
    {F : DistC → β} (hF : Measurable[GFFLaw.sigma0] F)
    (hpair : μ.map GFFLaw.ev0 = ν.map GFFLaw.ev0) : μ.map F = ν.map F := by
  have hle : GFFLaw.sigma0 ≤ (inferInstance : MeasurableSpace DistC) := by
    rw [GFFLaw.sigma0, ← measurable_iff_comap_le]
    exact measurable_pi_iff.2 fun φ => measurable_pair φ.1
  have hFm : Measurable F := hF.mono hle le_rfl
  have hev : Measurable GFFLaw.ev0 :=
    measurable_pi_iff.2 fun φ => measurable_pair φ.1
  ext S hS
  obtain ⟨T, hT, hTS⟩ := hF hS
  rw [Measure.map_apply hFm hS, Measure.map_apply hFm hS]
  have hpre : F ⁻¹' S = GFFLaw.ev0 ⁻¹' T := hTS.symm
  rw [hpre, ← Measure.map_apply hev hT, ← Measure.map_apply hev hT, hpair]

/-- Equality of the full laws of two normalized distributions follows from equality of the joint
laws of all mean-zero test pairings. The normalization must be measurable, shift by `c` under
`addConst · c`, and vanish almost everywhere under both measures. -/
theorem measure_eq_of_map_ev0_eq_of_normalized {μ ν : Measure DistC} {ρ : TestC}
    (hρ : ∫ x, ρ x = 1) {N : DistC → ℝ} (hNm : Measurable N)
    (hN : ∀ g c, N (addConst g c) = N g + c)
    (hpair : μ.map GFFLaw.ev0 = ν.map GFFLaw.ev0)
    (hμ : ∀ᵐ g ∂μ, N g = 0) (hν : ∀ᵐ g ∂ν, N g = 0) : μ = ν := by
  let K : DistC → DistC := fun g => addConst g (-(N g))
  let F : DistC → DistC := K ∘ GFFLaw.recenter ρ
  have hK : Measurable K := measurable_distC_iff.2 fun φ => by
    simp only [K, addConst_apply]
    exact (measurable_pair φ).add (hNm.neg.const_mul _)
  have hkey : ∀ g, F g = addConst g (-(N g)) := by
    intro g
    simp only [F, Function.comp_apply, K, GFFLaw.recenter, hN,
      GFFLaw.addConst_addConst]
    congr 1
    ring
  have hFm : Measurable[GFFLaw.sigma0] F :=
    hK.comp (GFFLaw.measurable_recenter_sigma0 hρ)
  have hfix : ∀ g, N g = 0 → F g = g := by
    intro g hg
    rw [hkey, hg, neg_zero, GFFLaw.addConst_zero']
  have hμmap : μ.map F = μ := by
    calc
      μ.map F = μ.map id := Measure.map_congr (by
        filter_upwards [hμ] with g hg
        exact hfix g hg)
      _ = μ := Measure.map_id
  have hνmap : ν.map F = ν := by
    calc
      ν.map F = ν.map id := Measure.map_congr (by
        filter_upwards [hν] with g hg
        exact hfix g hg)
      _ = ν := Measure.map_id
  calc
    μ = μ.map F := hμmap.symm
    _ = ν.map F := map_eq_of_map_ev0_eq hFm hpair
    _ = ν := hνmap

end MatedCRTHarmonic.ConeLemmaA10

