import SupercriticalLQGUniqueness.B2.DG20Lim.InterfaceC
import SupercriticalLQGUniqueness.B2.DG20Lim.Section51FieldC
import SupercriticalLQGUniqueness.B2.DG20Lim.TriangleCoupled
import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledGeometry
import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledRationalAgreement
import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledMeasurableMetric
import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledLengthRange

 


set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem dg20LimitSkC_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (_hRatio : B2.Iface.DG20QuantileRatio)
    (_hRelation : B2.Iface.DG20ExponentRelation)
    (hPositive : B2.Iface.DG20ExponentPositive)
    (_hTop : B2.Iface.LscTop) : DG20LimitSkC := by
  intro ξ Q hQ m hm ε hε
  obtain ⟨φ, hφ, c, hc, hCouple⟩ :=
    exists_section51_skorokhod_with_lsc_and_fieldC_of_inputs
      hS4 hPerc ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ?_⟩
  intro Ω mΩ P hP h hh X hX
  obtain ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, hCoordLaw, hNorm, hPairLaw, hCont,
    hConv, hChain, hAround, hLSC, hField⟩ :=
    hCouple P h hh X hX
  letI : MeasurableSpace Ω' := mΩ'
  letI : StandardBorelSpace Ω' := sbΩ'
  letI : IsProbabilityMeasure P' := hP'
  let ε' : ℕ → Ioi (0 : ℝ) := fun n => ε (φ n)
  have hε' : Tendsto (fun n => (ε' n : ℝ)) atTop (𝓝 0) :=
    hε.comp hφ.tendsto_atTop
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
  have hFinite := ae_finite_length_and_range_of_joint_coord_laws
    P P' h hh.1.measurable D hD hLen Y hYm
    (by simpa only [D] using hLaw')
  have hRange : ∀ᵐ ω ∂P', ∀ n,
      finiteCircleCoords (circleCoordsInv (Y n ω).2.1) = (Y n ω).2.1 :=
    hFinite.mono fun _ hω n => (hω n).1
  obtain ⟨L, hLm, hLsc, hRat, hGeometry⟩ :=
    exists_measurable_coupled_limit_metric
      P' Y Ylim hYm hConvAE hRange hLSC hAgree hGeom
  let h' : Ω' → DistC := fun ω => pairJInv ⊤ (Ylim ω).1
  let hN : ℕ → Ω' → DistC := fun n ω => pairJInv ⊤ (Y n ω).1
  let F : ℕ → Ω' → ℂ × ℂ → EReal := fun n ω =>
    finiteMetricE (circleCoordsInv (Y n ω).2.1)
  refine ⟨Ω', mΩ', sbΩ', P', hP', h', hN, F, L,
    hLm, hNorm, ?_, hField, ?_, ?_, ?_, ?_⟩
  · exact hPairLaw
  · intro n
    exact ae_of_all P' (hCont n)
  · exact hLsc
  · exact hRat
  · exact hGeometry

end SupercriticalLQGUniqueness.B2.DG20Lim
