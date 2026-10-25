import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAnnulusCover
import SupercriticalLQGUniqueness.B2.DG20Lim.CircleMinimizers
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPP

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalized_annulus_cross_le_point_distance
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (z u v : ℂ) (d : ℝ)
    (hu : dist u z < d / 16) (hv : 3 * d / 4 < dist v z)
    (hd : 0 < d) :
    ENNReal.ofReal (a : ℝ)⁻¹ *
      crossLenIn ξ φ (closedBall z d) (sphere z (d / 16))
        (sphere z (3 * d / 4)) ≤
      ENNReal.ofReal ((normalizedContLFPP ξ a φ).1 (u, v)) := by
  have hcross := annulus_cross_le_lfppDOn ξ φ z u v
    (d / 16) (3 * d / 4) d hu (by linarith) (by linarith) hv
  have hscale := mul_le_mul_of_nonneg_left hcross bot_le
    (a := ENNReal.ofReal (a : ℝ)⁻¹)
  convert hscale using 1
  · rfl
  rw [normalizedContLFPP, ContMetric.smulPos_apply,
    lfppContMetric_apply]
  rw [ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr a.property))]
  rw [ENNReal.ofReal_toReal (lfppD_ne_top φ.continuous u v)]

theorem exists_finite_annulus_cross_below_circleDist
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (O P : RatCircle) (q : Set ℂ)
    (d : ℝ) (hd : 0 < d)
    (hcover : ∀ u ∈ O.toSet, ∀ v ∈ P.toSet,
      ∃ z ∈ q, dist u z < d / 16 ∧ 3 * d / 4 < dist v z) :
    ∃ z ∈ q, ENNReal.ofReal (a : ℝ)⁻¹ *
      crossLenIn ξ φ (closedBall z d) (sphere z (d / 16))
        (sphere z (3 * d / 4)) ≤
      finiteCircleCoords (normalizedContLFPP ξ a φ) (O, P) := by
  let D := normalizedContLFPP ξ a φ
  obtain ⟨u, hu, v, hv, hmin⟩ := exists_circleDist_minimizers D O P
  obtain ⟨z, hz, huz, hvz⟩ := hcover u hu v hv
  refine ⟨z, hz, ?_⟩
  have hcross := normalized_annulus_cross_le_point_distance ξ a φ
    z u v d huz hvz hd
  exact hcross.trans (by simpa only [finiteCircleCoords, D] using hmin.le)

 


theorem exists_fixed_finite_cross_cover (O P : RatCircle)
    (hOP : Disjoint O.toSet P.toSet) :
    ∃ (d : ℝ) (q : Set ℂ), 0 < d ∧ d ≤ 1 / 2 ∧ q.Finite ∧ q.Nonempty ∧
      ∀ (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)),
        ∃ z ∈ q, ENNReal.ofReal (a : ℝ)⁻¹ *
          crossLenIn ξ φ (closedBall z d) (sphere z (d / 16))
            (sphere z (3 * d / 4)) ≤
          finiteCircleCoords (normalizedContLFPP ξ a φ) (O, P) := by
  obtain ⟨d, hd, hd2, hSep⟩ := exists_circle_separation_scale O P hOP
  obtain ⟨q, hqFin, -, hcover⟩ :=
    finite_annulus_cover_of_separated_compact
      (isCompact_sphere O.center (O.radius : ℝ)) hd hSep
  obtain ⟨u, hu⟩ : O.toSet.Nonempty :=
    NormedSpace.sphere_nonempty.mpr (Rat.cast_nonneg.mpr O.radius_nonneg)
  obtain ⟨v, hv⟩ : P.toSet.Nonempty :=
    NormedSpace.sphere_nonempty.mpr (Rat.cast_nonneg.mpr P.radius_nonneg)
  obtain ⟨z, hz, -, -⟩ := hcover u hu v hv
  refine ⟨d, q, hd, hd2, hqFin, ⟨z, hz⟩, ?_⟩
  intro ξ a φ
  exact exists_finite_annulus_cross_below_circleDist ξ a φ O P q d hd hcover

end SupercriticalLQGUniqueness.B2.DG20Lim
