/- Provenance (PROVE-GEO-JORDAN, ruling R21): ported, through an intermediate copy, from an earlier mating-of-trees
formalization; only the module and namespace prefixes were changed (now `InteractingSLE.Foundations.Topology` and
`InteractingSLE.Foundations`), and declaration names are unchanged. -/
import InteractingSLE.Foundations.Topology.Schoenflies.Disc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # The Alexander trick: radial extension of a circle homeomorphism

For `ψ : ℂ → ℂ` continuous, injective on the unit circle and mapping it onto itself, the cone
extension `radialExt ψ z = |z| ψ(z/|z|)` is a continuous, norm-preserving bijection of `ℂ`
extending `ψ` (J. W. Alexander, *On the deformation of an n-cell*, PNAS 9 (1923); the standard
"Alexander trick"). Own elementary proof (no Lean source found; mathlib has no cone extension).
-/

noncomputable section

namespace InteractingSLE.Foundations.Schoenflies

open Metric Set Function Filter Topology

/-- The radial (cone) extension `z ↦ |z| ψ(z/|z|)` of a self-map `ψ` of the unit circle. -/
def radialExt (ψ : ℂ → ℂ) (z : ℂ) : ℂ := ((‖z‖ : ℝ) : ℂ) * ψ (z / ((‖z‖ : ℝ) : ℂ))

theorem div_norm_mem_sphere {z : ℂ} (hz : z ≠ 0) : z / ((‖z‖ : ℝ) : ℂ) ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.mpr hz)]

theorem ofReal_norm_ne_zero {z : ℂ} (hz : z ≠ 0) : ((‖z‖ : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)

variable {ψ : ℂ → ℂ}

theorem norm_radialExt (hm : MapsTo ψ (sphere 0 1) (sphere 0 1)) (z : ℂ) :
    ‖radialExt ψ z‖ = ‖z‖ := by
  by_cases hz : z = 0
  · simp [radialExt, hz]
  · have h1 : ‖ψ (z / ((‖z‖ : ℝ) : ℂ))‖ = 1 := by
      simpa using hm (div_norm_mem_sphere hz)
    rw [radialExt, norm_mul, Complex.norm_real, norm_norm, h1, mul_one]

theorem radialExt_of_mem_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : radialExt ψ z = ψ z := by
  have h1 : ‖z‖ = 1 := by simpa using hz
  simp [radialExt, h1]

theorem continuous_radialExt (hc : ContinuousOn ψ (sphere 0 1))
    (hm : MapsTo ψ (sphere 0 1) (sphere 0 1)) : Continuous (radialExt ψ) := by
  have hn : Continuous fun w : ℂ => ((‖w‖ : ℝ) : ℂ) := Complex.continuous_ofReal.comp continuous_norm
  have hcont : ContinuousOn (fun w => ψ (w / ((‖w‖ : ℝ) : ℂ))) {0}ᶜ :=
    hc.comp (continuousOn_id.div hn.continuousOn fun w hw => ofReal_norm_ne_zero hw)
      fun w hw => div_norm_mem_sphere hw
  refine continuous_iff_continuousAt.mpr fun z => ?_
  by_cases hz : z = 0
  · subst hz
    rw [ContinuousAt, show radialExt ψ 0 = 0 by simp [radialExt],
      tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_radialExt hm]
    simpa using (continuous_norm (E := ℂ)).tendsto 0
  · exact hn.continuousAt.mul (hcont.continuousAt (isOpen_compl_singleton.mem_nhds hz))

theorem injective_radialExt (hm : MapsTo ψ (sphere 0 1) (sphere 0 1))
    (hi : InjOn ψ (sphere 0 1)) : Injective (radialExt ψ) := by
  intro z w h
  have hn : ‖z‖ = ‖w‖ := by rw [← norm_radialExt hm z, h, norm_radialExt hm w]
  by_cases hz : z = 0
  · subst hz
    rw [norm_zero, eq_comm, norm_eq_zero] at hn
    exact hn.symm
  have hw : w ≠ 0 := fun hw => hz (norm_eq_zero.mp (hn.trans (by rw [hw, norm_zero])))
  unfold radialExt at h
  rw [hn] at h
  have := hi (hn ▸ div_norm_mem_sphere hz) (div_norm_mem_sphere hw)
    (mul_left_cancel₀ (ofReal_norm_ne_zero hw) h)
  exact (div_left_inj' (ofReal_norm_ne_zero hw)).mp this

theorem surjective_radialExt (hs : SurjOn ψ (sphere 0 1) (sphere 0 1)) :
    Surjective (radialExt ψ) := by
  intro w
  by_cases hw : w = 0
  · exact ⟨0, by simp [radialExt, hw]⟩
  obtain ⟨u, hu, hψu⟩ := hs (div_norm_mem_sphere hw)
  have hu1 : ‖u‖ = 1 := by simpa using hu
  refine ⟨((‖w‖ : ℝ) : ℂ) * u, ?_⟩
  have hn : ‖((‖w‖ : ℝ) : ℂ) * u‖ = ‖w‖ := by
    rw [norm_mul, Complex.norm_real, norm_norm, hu1, mul_one]
  unfold radialExt
  rw [hn, mul_div_cancel_left₀ u (ofReal_norm_ne_zero hw), hψu,
    mul_div_cancel₀ w (ofReal_norm_ne_zero hw)]

/-- A norm-preserving surjection of `ℂ` preserves every set defined through the norm. -/
theorem image_norm_preimage {F : ℂ → ℂ} (hn : ∀ z, ‖F z‖ = ‖z‖) (hs : Surjective F)
    (S : Set ℝ) : F '' ((fun z : ℂ => ‖z‖) ⁻¹' S) = (fun z : ℂ => ‖z‖) ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [mem_preimage, hn] using hz
  · intro hw
    obtain ⟨z, rfl⟩ := hs w
    exact ⟨z, by simpa [mem_preimage, hn] using hw, rfl⟩

/-- **Alexander trick.** A homeomorphism `ψ` of the unit circle extends to a continuous,
norm-preserving bijection `Ψ` of `ℂ`; in particular `Ψ` maps the open and closed unit discs
and the circle onto themselves. -/
theorem alexander_trick (hc : ContinuousOn ψ (sphere 0 1))
    (hm : MapsTo ψ (sphere 0 1) (sphere 0 1)) (hi : InjOn ψ (sphere 0 1))
    (hs : SurjOn ψ (sphere 0 1) (sphere 0 1)) :
    ∃ Ψ : ℂ → ℂ, Continuous Ψ ∧ Injective Ψ ∧ (∀ z, ‖Ψ z‖ = ‖z‖) ∧
      (∀ z ∈ sphere (0 : ℂ) 1, Ψ z = ψ z) ∧ Ψ '' ball 0 1 = ball 0 1 ∧
      Ψ '' closedBall 0 1 = closedBall 0 1 ∧ Ψ '' sphere 0 1 = sphere 0 1 := by
  have hsu := surjective_radialExt hs
  have hn := norm_radialExt hm
  refine ⟨radialExt ψ, continuous_radialExt hc hm, injective_radialExt hm hi, hn,
    fun z hz => radialExt_of_mem_sphere hz, ?_, ?_, ?_⟩
  · have := image_norm_preimage hn hsu (Iio 1)
    convert this using 2 <;> ext <;> simp
  · have := image_norm_preimage hn hsu (Iic 1)
    convert this using 2 <;> ext <;> simp
  · have := image_norm_preimage hn hsu {1}
    convert this using 2 <;> ext <;> simp

end InteractingSLE.Foundations.Schoenflies
