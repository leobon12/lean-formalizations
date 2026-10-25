import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryFromLargeCircles
import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledLengthRange
import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledLargeAnnuliOfInputs

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_geometry_on_coupled_limit_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ e, IsLFPPNormalizer ξ e (m e))
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
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
    (hTri : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      ∀ x y z : ℂ,
        R.DfromR x z ≤ R.DfromR x y + R.DfromR y z) :
    ∀ᵐ ω ∂P', ∃ (R : RData)
      (htri : ∀ x y z : ℂ,
        R.DfromR x z ≤ R.DfromR x y + R.DfromR y z),
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      (R.toLSCMetric htri).IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (R.toLSCMetric htri).1 (u, v) < ENNReal.ofReal η →
          dist u v < δ) ∧
      (∀ u v : ℂ, (R.toLSCMetric htri).1 (u, v) < ∞ →
        ∃ (γ : ℝ → ℂ) (a b : ℝ),
          (R.toLSCMetric htri).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
            (R.toLSCMetric htri).len γ a b = (R.toLSCMetric htri).1 (u, v)) := by
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω)
  have hD : ∀ n, AEMeasurable (D n) P := by
    intro n
    exact aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε n) (m (ε n)) (ξ : ℝ) (X (ε n)) (hX (ε n))
  have hLenSource : ∀ n, ∀ᵐ ω ∂P, (D n ω).IsLength := by
    intro n
    exact ae_of_all P (fun ω => isLength_normalizedContLFPP
      (ξ : ℝ) (m (ε n)) (X (ε n) ω))
  have hFinite := ae_finite_length_and_range_of_joint_coord_laws
    P P' h hh.1.measurable D hD hLenSource Y hYm
    (by simpa only [D] using hLaw)
  have hLarge := ae_large_annuli_on_coupled_limit_of_inputs
    hS4 hPerc hPos ξ Q hQ m hm P P' h hh X hX ε hε
    Y Ylim hYm hLaw hConv
  filter_upwards [hTri, hFinite, hLarge, hConv] with
    ω hTriω hFiniteω hLargeω hConvω
  obtain ⟨R, hAcross, hAround, htri⟩ := hTriω
  let E : ℕ → ContMetric := fun n => circleCoordsInv (Y n ω).2.1
  have hlenE : ∀ n, (E n).IsLength := fun n => (hFiniteω n).2
  have hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (E n) O.toSet P.toSet)
        atTop (𝓝 (R.across O P)) := by
    intro O Pcircle
    have hc : Tendsto (fun n => (Y n ω).2.1 (O, Pcircle)) atTop
        (𝓝 ((Ylim ω).2.1 (O, Pcircle))) :=
      ((continuous_apply (O, Pcircle)).comp
        (continuous_fst.comp continuous_snd)).tendsto _ |>.comp hConvω
    change Tendsto (fun n => finiteCircleCoords (E n) (O, Pcircle))
      atTop (𝓝 (R.across O Pcircle))
    rw [show (fun n => finiteCircleCoords (E n) (O, Pcircle)) =
      (fun n => (Y n ω).2.1 (O, Pcircle)) from
      funext fun n => congrFun (hFiniteω n).1 (O, Pcircle), hAcross]
    exact hc
  have hlarge : ∀ N : ℕ, ∃ r : {r : ℚ // 1 < r},
      (N : ℝ) < (r : ℚ) ∧
      ENNReal.ofReal ((N : ℝ) + 1) ≤ R.across
        (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property))
        (centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property)) := by
    intro N
    obtain ⟨r, hrN, hrCost⟩ := hLargeω N
    exact ⟨r, hrN, by simpa only [hAcross] using hrCost⟩
  obtain ⟨hLength, hEuclid, hGeo⟩ :=
    R.geometry_of_large_annuli htri hlarge E hlenE hcircle
  exact ⟨R, htri, hAcross, hAround, hLength, hEuclid, hGeo⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
