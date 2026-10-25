import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircLimit
import SupercriticalLQGUniqueness.B2.DG20Lim.SkUpgradeOfInputs
import SupercriticalLQGUniqueness.B2.DG20Lim.GoodCircleCoupled
import SupercriticalLQGUniqueness.B2.DG20Lim.AllPointCircleVanishing

 














set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open SupercriticalLQGUniqueness.B2.DG20Lim
open SupercriticalLQGUniqueness.B2.Iface

 
def DG20LimitSkSBCirc : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ ε : ℕ → Set.Ioi (0 : ℝ),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
            (∀ r : ℚ, ∀ hr : 0 < r,
              Tendsto (fun n => (r : ℝ) *
                (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
                  Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                    (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (m (ε (φ n)) : ℝ)) atTop
                (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
            ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
              ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
                (∀ δ, IsHeatSmoothing P h δ (X δ)) →
              ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω') (P' : Measure Ω')
                (_ : IsProbabilityMeasure P') (h' : Ω' → DistC)
                (hN : ℕ → Ω' → DistC)
                (F : ℕ → Ω' → ℂ × ℂ → EReal) (L : Ω' → LSCMetric),
                Measurable L ∧ IsNormalizedWholePlaneGFF h' P' ∧
                (∀ n, P'.map (fun ω => (hN n ω, F n ω)) =
                  P.map (fun ω => (h ω,
                    rescaledLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)))) ∧
                (∀ᵐ ω ∂P', Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω))) ∧
                (∀ n, ∀ᵐ ω ∂P', Continuous (F n ω)) ∧
                (∀ᵐ ω ∂P', LSCTendsto (fun n => F n ω) (L ω).toLSCFun.1) ∧
                (∀ᵐ ω ∂P', ∀ u v : ℂ, IsRationalPoint u → IsRationalPoint v →
                  Tendsto (fun n => F n ω (u, v)) atTop
                    (𝓝 ((L ω).toLSCFun.1 (u, v)))) ∧
                (∀ᵐ ω ∂P', (L ω).IsLengthSpace ∧
                  (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
                    ∀ v : ℂ, (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
                  (∀ u v : ℂ, (L ω).1 (u, v) < ∞ →
                    ∃ (γ : ℝ → ℂ) (a b : ℝ),
                      (L ω).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
                        (L ω).len γ a b = (L ω).1 (u, v))) ∧
                (∀ᵐ ω ∂P', ∀ O O' : RatCircle,
                  Tendsto (fun n => setDistance (fun p => (F n ω p).toENNReal) O.toSet O'.toSet)
                    atTop (𝓝 (setDistance (L ω).1 O.toSet O'.toSet)))

 
theorem dg20LimitSkSBCirc_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (_hRatio : B2.Iface.DG20QuantileRatio)
    (_hRelation : B2.Iface.DG20ExponentRelation)
    (hPositive : B2.Iface.DG20ExponentPositive) : DG20LimitSkSBCirc := by
  intro ξ Q hQ m hm ε hε
  obtain ⟨φ, hφ, c, hc, ρ, hlim, hmarg⟩ :=
    exists_scale_canonical_field_limit hS4 ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ?_⟩
  intro Ω mΩ P hP h hh X hX
  obtain ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, hCoordLaw, hNorm, hPairLaw, hCont, hConv, hFieldTop⟩ :=
    exists_lfpp_joint_field_skorokhod_of_canonical_limit (ξ : ℝ) m
      (fun n => ε (φ n)) ρ hlim hmarg P h hh X hX
  letI : MeasurableSpace Ω' := mΩ'
  letI : StandardBorelSpace Ω' := sbΩ'
  letI : IsProbabilityMeasure P' := hP'
  let ε' : ℕ → Ioi (0 : ℝ) := fun n => ε (φ n)
  have hε' : Tendsto (fun n => (ε' n : ℝ)) atTop (𝓝 0) :=
    hε.comp hφ.tendsto_atTop
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP (ξ : ℝ) (m (ε' n)) (X (ε' n) ω)
  have hD : ∀ n, AEMeasurable (D n) P := by
    intro n
    exact aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε' n) (m (ε' n)) (ξ : ℝ) (X (ε' n)) (hX (ε' n))
  have hLen : ∀ n, ∀ᵐ ω ∂P, (D n ω).IsLength := by
    intro n
    exact ae_of_all P (fun ω => isLength_normalizedContLFPP
      (ξ : ℝ) (m (ε' n)) (X (ε' n) ω))
  have hChain := ae_all_finiteCircle_chain_of_joint_coord_laws
    P P' h hh.1.measurable D hD hLen Y hYm hCoordLaw
  have hAround := ae_all_finiteAround_bounds_of_joint_coord_laws
    P P' h hh.1.measurable D hD hLen Y hYm hCoordLaw
  have hRData0 := ae_rdata_of_section51_coupling
    hPerc ξ m hm ε hε φ hφ P P' h hh X hX
    Y Ylim hYm hCoordLaw hConv hChain hAround
  have hLSC := ae_lscTendsto_of_joint_coord_laws P P' h hh.1.measurable
    D hD hLen Y Ylim hYm hCoordLaw hConv hRData0
  have hLaw' : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ) (m (ε' n)) (X (ε' n) ω))
        (aemeasurable_normalizedContLFPP_heat_version P h hh
          (ε' n) (m (ε' n)) (ξ : ℝ) (X (ε' n)) (hX (ε' n))) ω)) := by
    intro n
    exact hCoordLaw n
  have hConvAE : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)) :=
    ae_of_all P' hConv
  have hRData : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 :=
    hLSC.mono fun _ hω => by
      obtain ⟨R, ha, hb, _⟩ := hω
      exact ⟨R, ha, hb⟩
  have hTri := ae_triangle_on_coupled_limit_of_inputs
    hS4 hPerc ξ Q hQ m hm P P' h hh X hX ε' hε'
    Y Ylim hYm hLaw' hConvAE hRData
  have hAgree := ae_rational_agreement_on_coupled_limit_of_inputs
    hS4 hPerc hPositive ξ Q hQ m hm P P' h hh X hX ε' hε'
    Y Ylim hYm hLaw' hConvAE hRData
  have hGeom := ae_geometry_on_coupled_limit_of_inputs
    hS4 hPerc hPositive ξ Q hQ m hm P P' h hh X hX ε' hε'
    Y Ylim hYm hLaw' hConvAE hTri
  have hFinite := ae_finite_length_and_range_of_joint_coord_laws
    P P' h hh.1.measurable D hD hLen Y hYm
    (by simpa only [D] using hLaw')
  have hRange : ∀ᵐ ω ∂P', ∀ n,
      finiteCircleCoords (circleCoordsInv (Y n ω).2.1) = (Y n ω).2.1 :=
    hFinite.mono fun _ hω n => (hω n).1
  obtain ⟨L, hLm, hLsc, hRat, hGeometry⟩ :=
    exists_measurable_coupled_limit_metric
      P' Y Ylim hYm hConvAE hRange hLSC hAgree hGeom
  
  have hCross := ae_all_coupled_crossing_bounds P P' h hh.1.measurable D hD hLen Y hYm hCoordLaw
  have hInter := ae_all_coupled_inter_zero P P' h hh.1.measurable D hD Y hYm hCoordLaw
  obtain ⟨Cg, hCg, hGood⟩ := exists_nested_good_circles_on_coupled_limit_of_inputs
    hS4 hPerc ξ Q hQ m hm P P' h hh X hX ε' hε' Y Ylim hYm hLaw' hConvAE hRData
  have hVanish := ae_all_coupled_point_circle_vanishing_of_inputs
    hS4 hPositive ξ Q hQ m hm P P' h hh X hX ε' hε' Y Ylim hYm hLaw' hConvAE hRData
  have hCirc : ∀ᵐ ω ∂P', ∀ O O' : RatCircle,
      Tendsto (fun n => setDistance (fun p =>
        (finiteMetricE (circleCoordsInv (Y n ω).2.1) p).toENNReal) O.toSet O'.toSet)
        atTop (𝓝 (setDistance (L ω).1 O.toSet O'.toSet)) := by
    filter_upwards [hLSC, hGood, hVanish, hCross, hInter, hRange, hLsc] with ω hLSCω hGoodω
      hVanω hCrossω hInterω hRangeω hLscω
    obtain ⟨R, hRa, hRb, hRL⟩ := hLSCω
    obtain ⟨R', hR'a, hR'b, hR'good⟩ := hGoodω
    have hRR'a : R'.across = R.across := hR'a.trans hRa.symm
    have hRR'b : R'.around = R.around := hR'b.trans hRb.symm
    set K : ℝ≥0∞ := ENNReal.ofReal 2 * (ENNReal.ofReal 2 * ENNReal.ofReal Cg *
      ENNReal.ofReal 2) * ENNReal.ofReal 2 with hK
    have hKtop : K ≠ ∞ := by
      simp only [hK, ne_eq, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, false_and, and_false,
        or_self, not_false_eq_true]
    have hGoodR : ∀ z : ℂ, ∃ B : ℕ → RatAnnulus,
        (∀ n, (B n).inner.Surrounds z ∧ R.around (B n) ≤ K * R.across (B n).inner (B n).outer) ∧
        (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
        Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0) := by
      intro z
      obtain ⟨B, hB1, hB2, hB3⟩ := hR'good z
      refine ⟨B, fun n => ?_, hB2, hB3⟩
      obtain ⟨h1, h2⟩ := hB1 n
      rw [hRR'a, hRR'b] at h2
      exact ⟨h1, h2⟩
    intro O O'
    have hid := limit_circleCoord_eq_setDistance (hConv ω) hRangeω (L ω) hLscω R hRa hRb hRL
      K hKtop hCrossω hInterω hGoodR hVanω O O'
    have hcoord : ∀ n, setDistance (fun p =>
        (finiteMetricE (circleCoordsInv (Y n ω).2.1) p).toENNReal) O.toSet O'.toSet =
        (Y n ω).2.1 (O, O') := by
      intro n
      have h1 : (fun p => (finiteMetricE (circleCoordsInv (Y n ω).2.1) p).toENNReal) =
          ⇑(finiteLSCMetric (circleCoordsInv (Y n ω).2.1)) := by
        funext p
        simp only [finiteMetricE, EReal.toENNReal_coe, finiteLSCMetric_apply]
      rw [h1, setDistance_finiteLSCMetric]
      exact congrFun (hRangeω n) (O, O')
    simp only [hcoord]
    rw [← hid]
    exact tendsto_circleCoord (hConv ω) O O'
  let h' : Ω' → DistC := fun ω => pairJInv ⊤ (Ylim ω).1
  let hN : ℕ → Ω' → DistC := fun n ω => pairJInv ⊤ (Y n ω).1
  let F : ℕ → Ω' → ℂ × ℂ → EReal := fun n ω =>
    finiteMetricE (circleCoordsInv (Y n ω).2.1)
  exact ⟨Ω', mΩ', sbΩ', P', hP', h', hN, F, L,
    hLm, hNorm, hPairLaw, hFieldTop, fun n => ae_of_all P' (hCont n),
    hLsc, hRat, hGeometry, hCirc⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
