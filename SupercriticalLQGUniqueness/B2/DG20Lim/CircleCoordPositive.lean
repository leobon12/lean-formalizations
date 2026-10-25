import SupercriticalLQGUniqueness.B2.DG20Lim.CircleTailCoordLaw

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_positive_circle_coord_of_joint_law
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {Ω : Type} {Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hYm : ∀ n, Measurable (Y n))
    (hD : ∀ n, AEMeasurable (fun ω =>
      normalizedContLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)) P)
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ)
          (m (ε (φ n))) (X (ε (φ n)) ω)) (hD n) ω)))
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (O Pcircle : RatCircle) (hOP : Disjoint O.toSet Pcircle.toSet) :
    ∀ᵐ ω ∂P', 0 < (Ylim ω).2.1 (O, Pcircle) := by
  have hφTop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hεsub : Tendsto (fun n => (ε (φ n) : ℝ)) atTop (𝓝 0) :=
    hε.comp hφTop
  let V : ℕ → Ω' → ℝ≥0∞ := fun n ω => (Y n ω).2.1 (O, Pcircle)
  let v : Ω' → ℝ≥0∞ := fun ω => (Ylim ω).2.1 (O, Pcircle)
  have hCoordCont : Continuous
      (fun q : (CoordJ → ℝ) × RatCoords => q.2.1 (O, Pcircle)) :=
    ((continuous_apply (O, Pcircle)).comp continuous_fst).comp continuous_snd
  have hVconv : ∀ᵐ ω ∂P', Tendsto (fun n => V n ω) atTop (𝓝 (v ω)) := by
    filter_upwards [hConv] with ω hω
    exact (hCoordCont.tendsto (Ylim ω)).comp hω
  apply ae_pos_of_uniform_small_lower_tail P' V v hVconv
  intro η hη
  obtain ⟨T, ε₀, hT, hε₀, hTailSource⟩ :=
    dg20_heat_circle_small_lower_of_perc hPerc ξ m hm
      P h hh X hX O Pcircle hOP η hη
  refine ⟨ENNReal.ofReal T⁻¹,
    ENNReal.ofReal_pos.mpr (inv_pos.mpr hT), ?_⟩
  have hsmall : ∀ᶠ n in atTop, (ε (φ n) : ℝ) < min ε₀ 1 :=
    hεsub.eventually (isOpen_Iio.mem_nhds (lt_min hε₀ zero_lt_one))
  filter_upwards [hsmall] with n hn
  let e : Ioo (0 : ℝ) 1 := ⟨(ε (φ n) : ℝ), (ε (φ n)).property,
    lt_of_lt_of_le hn (min_le_right _ _)⟩
  have hTail := hTailSource e (lt_of_lt_of_le hn (min_le_left _ _))
  exact circle_lower_tail_of_joint_coord_law P P' h hh.1.measurable
    (fun ω => normalizedContLFPP (ξ : ℝ)
      (m (ε (φ n))) (X (ε (φ n)) ω)) (hD n)
    (Y n) (hYm n) (hLaw n) O Pcircle _ _
    (by simpa only [e] using hTail)

 

theorem ae_all_positive_circle_coords_of_joint_law
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {Ω : Type} {Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hYm : ∀ n, Measurable (Y n))
    (hD : ∀ n, AEMeasurable (fun ω =>
      normalizedContLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)) P)
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ)
          (m (ε (φ n))) (X (ε (φ n)) ω)) (hD n) ω)))
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) :
    ∀ᵐ ω ∂P', ∀ O Pcircle : RatCircle,
      Disjoint O.toSet Pcircle.toSet →
        0 < (Ylim ω).2.1 (O, Pcircle) := by
  apply ae_all_iff.mpr
  intro O
  apply ae_all_iff.mpr
  intro Pcircle
  by_cases hOP : Disjoint O.toSet Pcircle.toSet
  · filter_upwards [ae_positive_circle_coord_of_joint_law
      hPerc ξ m hm ε hε φ hφ P P' h hh X hX Y Ylim
      hYm hD hLaw hConv O Pcircle hOP] with ω hω
    exact fun _ => hω
  · exact Filter.Eventually.of_forall fun _ h => False.elim (hOP h)

end SupercriticalLQGUniqueness.B2.DG20Lim
