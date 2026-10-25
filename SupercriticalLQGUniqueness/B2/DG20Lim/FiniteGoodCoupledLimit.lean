import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteBadOpen
import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusCoupledLimit

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_finite_good_ratio_on_coupled_limit_of_inputs
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
    (a : ℝ) (ha : 0 < a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (x y r₀ : ℚ) (hr₀ : 0 < r₀)
        (S : Finset ℕ) (hS : S.Nonempty),
        P' {ω | ∀ i ∈ S,
          (ENNReal.ofReal 2 *
            (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) *
            ENNReal.ofReal 2) *
            (Ylim ω).2.1
              ((centeredRatAnnulus x y (ratRad64 r₀ i)
                (ratRad64_pos hr₀ i)).inner,
               (centeredRatAnnulus x y (ratRad64 r₀ i)
                (ratRad64_pos hr₀ i)).outer) <
            (Ylim ω).2.2
              (centeredRatAnnulus x y (ratRad64 r₀ i)
                (ratRad64_pos hr₀ i))} ≤
          ENNReal.ofReal (c * Real.exp (-a * S.card)) := by
  obtain ⟨c, C, hc, hC, hfull⟩ :=
    exists_eventual_full_good_iteration64_of_inputs
      hS4 hPerc ξ Q hQ m hm P h hh X hX ε hε a ha
  refine ⟨c, C, hc, hC, ?_⟩
  intro x y r₀ hr₀ S hS
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ hb
  let η : ℝ := δ
  have hη : 0 < η := by exact_mod_cast hδ
  let A : ℕ → RatAnnulus := fun i =>
    centeredRatAnnulus x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i)
  let C' : ℝ≥0∞ := ENNReal.ofReal 2 *
    (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) * ENNReal.ofReal 2
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω)
  have hD (n : ℕ) : AEMeasurable (D n) P :=
    aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε n) (m (ε n)) (ξ : ℝ) (X (ε n)) (hX (ε n))
  have hLaw' (n : ℕ) : P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω)) := by
    simpa only [D] using hLaw n
  have hSrc : ∀ᶠ n in atTop,
      P {ω | ∀ i ∈ S,
        C' * finiteCircleCoords (D n ω) ((A i).inner, (A i).outer) <
          finiteAroundCoords (D n ω) (A i)} ≤
        ENNReal.ofReal (c * Real.exp (-a * S.card)) + ENNReal.ofReal η := by
    filter_upwards [hfull η hη x y r₀ hr₀ S hS] with n hn
    have hgoodEq (i : ℕ) : fullHeatGoodEvent (X (ε n)) (ξ : ℝ) x y
        (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C' =
        normalizedGoodEvent (X (ε n)) (ξ : ℝ) (m (ε n)) x y
          (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C' :=
      fullHeatGoodEvent_eq_normalizedGoodEvent (X (ε n)) (ξ : ℝ)
        (m (ε n)) x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C'
    have hevent : allGoodFail (fun n i =>
        fullHeatGoodEvent (X (ε n)) (ξ : ℝ) x y
          (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C') S n =
        {ω | ∀ i ∈ S,
          C' * finiteCircleCoords (D n ω) ((A i).inner, (A i).outer) <
            finiteAroundCoords (D n ω) (A i)} := by
      ext ω
      simp only [allGoodFail, mem_setOf_eq, hgoodEq, normalizedGoodEvent,
        not_le, D, A, centeredRatAnnulus]
    rwa [hevent] at hn
  have hCoupled : ∀ᶠ n in atTop,
      P' {ω | ∀ i ∈ S,
        C' * (Y n ω).2.1 ((A i).inner, (A i).outer) <
          (Y n ω).2.2 (A i)} ≤
        ENNReal.ofReal (c * Real.exp (-a * S.card)) + ENNReal.ofReal η := by
    filter_upwards [hSrc] with n hn
    exact finite_bad_ratio_probability_of_joint_coord_law
      P P' h hh.1.measurable (D n) (hD n) (Y n) (hYm n)
      (hLaw' n) A S C' _ hn
  have hC' : C' ≠ ∞ := by
    dsimp [C']
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top <;> exact ENNReal.ofReal_ne_top
        · exact ENNReal.ofReal_ne_top
    · exact ENNReal.ofReal_ne_top
  let bad : Set ((CoordJ → ℝ) × RatCoords) :=
    {v | ∀ i ∈ S, C' * v.2.1 ((A i).inner, (A i).outer) < v.2.2 (A i)}
  have hopen : IsOpen bad := isOpen_finite_bad_ratio A S C' hC'
  have hlim := open_event_limit_probability_le P' Y Ylim bad hopen hConv
    (ENNReal.ofReal (c * Real.exp (-a * S.card)) + ENNReal.ofReal η)
    (by simpa only [bad, mem_setOf_eq] using hCoupled)
  simpa only [bad, mem_setOf_eq, A, C', η, ENNReal.ofReal_coe_nnreal] using hlim

end SupercriticalLQGUniqueness.B2.DG20Lim
