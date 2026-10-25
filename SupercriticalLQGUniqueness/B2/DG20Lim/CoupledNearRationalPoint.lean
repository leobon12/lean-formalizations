import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledNearPointTail
import SupercriticalLQGUniqueness.B2.DG20Lim.PointCircleVanishingAE

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private theorem exists_real_pos_ofReal_lt_ennreal
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal θ < δ := by
  by_cases htop : δ = ∞
  · exact ⟨1, by norm_num, by simp [htop]⟩
  have hp : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' htop
  refine ⟨δ.toReal / 2, half_pos hp, ?_⟩
  calc
    ENNReal.ofReal (δ.toReal / 2) < ENNReal.ofReal δ.toReal :=
      (ENNReal.ofReal_lt_ofReal_iff hp).2 (by linarith)
    _ = δ := ENNReal.ofReal_toReal htop

theorem exists_near_rational_point_small_coord_probability_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hYm : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (aemeasurable_normalizedContLFPP_heat_version P h hh
          (ε n) (m (ε n)) (ξ : ℝ) (X (ε n)) (hX (ε n))) ω)))
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (Z : RatCircle) (hZ : Z.radius = 0)
    (δ : ℝ≥0∞) (hδ : 0 < δ) (η : ℝ) (hη : 0 < η) :
    ∃ W : RatCircle, W.radius = 0 ∧ W.center ≠ Z.center ∧
      P' {ω | δ ≤ (Ylim ω).2.1 (Z, W)} ≤ ENNReal.ofReal η := by
  obtain ⟨θ, hθ, hθδ⟩ := exists_real_pos_ofReal_lt_ennreal δ hδ
  obtain ⟨r₀, hr₀, htail⟩ :=
    exists_small_coupled_point_coord_tail_of_inputs
      hS4 hPos ξ Q hQ m hm P P' h hh X hX ε hε Y Ylim
      hYm hLaw hConv Z hZ θ η hθ hη
  obtain ⟨s, hs0, hs⟩ := exists_rat_btwn
    (show (0 : ℝ) < min r₀ 1 from lt_min hr₀ zero_lt_one)
  let r : Ioo (0 : ℝ) 1 :=
    ⟨(s : ℝ), hs0, lt_of_lt_of_le hs (min_le_right _ _)⟩
  let W : RatCircle := RatCircle.point (Z.x + s) Z.y
  have hWcenter : W.center = Z.center + (r : ℂ) := by
    apply Complex.ext
    · simp [W, RatCircle.point, RatCircle.center, r]
    · simp [W, RatCircle.point, RatCircle.center, r]
  have hWne : W.center ≠ Z.center := by
    rw [hWcenter]
    intro he
    have hrzero : (r : ℂ) = 0 := by
      have := add_left_cancel (show Z.center + (r : ℂ) = Z.center + 0 by simpa using he)
      simpa using this
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast r.property.1.ne'
    exact hrne hrzero
  refine ⟨W, rfl, hWne, ?_⟩
  calc
    P' {ω | δ ≤ (Ylim ω).2.1 (Z, W)} ≤
        P' {ω | ENNReal.ofReal θ < (Ylim ω).2.1 (Z, W)} := by
          apply measure_mono
          intro ω hω
          exact hθδ.trans_le hω
    _ ≤ ENNReal.ofReal η :=
      htail r (le_of_lt (lt_of_lt_of_le hs (min_le_left _ _)))
        W rfl hWcenter

end SupercriticalLQGUniqueness.B2.DG20Lim
