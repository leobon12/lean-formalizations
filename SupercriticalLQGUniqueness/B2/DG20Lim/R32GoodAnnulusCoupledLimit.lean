import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalGoodSequence
import SupercriticalLQGUniqueness.B2.DG20Lim.Section51FieldC

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_good_annulus_ratio_on_coupled_limit_of_inputsR32
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
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
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y r : ℚ, ∀ hr : 0 < r,
        P' {ω | ENNReal.ofReal C *
          (Ylim ω).2.1 ((centeredRatAnnulusR32 x y r hr).inner,
            (centeredRatAnnulusR32 x y r hr).outer) <
          (Ylim ω).2.2 (centeredRatAnnulusR32 x y r hr)} ≤
          ENNReal.ofReal η := by
  obtain ⟨C, hC, hSource⟩ :=
    exists_rational_good_ratio_eventually_for_sequence_of_inputsR32
      hS4 hPerc ξ Q hQ m hm P h hh X hX ε hε η hη
  refine ⟨C, hC, ?_⟩
  intro x y r hr
  let A : RatAnnulus := centeredRatAnnulusR32 x y r hr
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω)
  have hD (n : ℕ) : AEMeasurable (D n) P :=
    aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε n) (m (ε n)) (ξ : ℝ) (X (ε n)) (hX (ε n))
  have hLaw' (n : ℕ) : P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω)) := by
    simpa only [D] using hLaw n
  have hCoupled : ∀ᶠ n in atTop,
      P' {ω | ENNReal.ofReal C * (Y n ω).2.1 (A.inner, A.outer) <
        (Y n ω).2.2 A} ≤ ENNReal.ofReal η := by
    filter_upwards [hSource x y r hr] with n hn
    have hi : A.inner = centeredInnerCircleR32 x y r hr := rfl
    have ho : A.outer = centeredOuterCircleR32 x y r hr := rfl
    exact bad_ratio_probability_of_joint_coord_law P P' h hh.1.measurable
      (D n) (hD n) (Y n) (hYm n) (hLaw' n) A
      (ENNReal.ofReal C) (ENNReal.ofReal η) (by
        simpa only [D, A, hi, ho] using hn)
  have hProj : Continuous (fun v : (CoordJ → ℝ) × RatCoords =>
      (v.2.1 (A.inner, A.outer), v.2.2 A)) := by
    exact (((continuous_apply (A.inner, A.outer)).comp
      (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_apply A).comp (continuous_snd.comp continuous_snd)))
  have hPairConv : ∀ᵐ ω ∂P', Tendsto
      (fun n => ((Y n ω).2.1 (A.inner, A.outer), (Y n ω).2.2 A))
      atTop (𝓝 ((Ylim ω).2.1 (A.inner, A.outer), (Ylim ω).2.2 A)) := by
    filter_upwards [hConv] with ω hω
    exact hProj.tendsto (Ylim ω) |>.comp hω
  exact bad_ratio_limit_probability_le P'
    (fun n ω => (Y n ω).2.1 (A.inner, A.outer))
    (fun n ω => (Y n ω).2.2 A)
    (fun ω => (Ylim ω).2.1 (A.inner, A.outer))
    (fun ω => (Ylim ω).2.2 A)
    (ENNReal.ofReal C) (ENNReal.ofReal η)
    ENNReal.ofReal_ne_top hPairConv hCoupled

end SupercriticalLQGUniqueness.B2.DG20Lim
