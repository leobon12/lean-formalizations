import SupercriticalLQGUniqueness.B2.DG20Lim.SkUpgradeUniversal
import SupercriticalLQGUniqueness.B2.DG20Lim.DG20LimitSkCOfInputs
import SupercriticalLQGUniqueness.B2.DG20Lim.InterfaceCBridge
import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsDG20SkSB

 

























set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem dg20LimitSkSB_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (_hRatio : B2.Iface.DG20QuantileRatio)
    (_hRelation : B2.Iface.DG20ExponentRelation)
    (hPositive : B2.Iface.DG20ExponentPositive)
    (_hTop : B2.Iface.LscTop) : B2.PfeAxioms.Inputs.DG20LimitSkSB := by
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
  let h' : Ω' → DistC := fun ω => pairJInv ⊤ (Ylim ω).1
  let hN : ℕ → Ω' → DistC := fun n ω => pairJInv ⊤ (Y n ω).1
  let F : ℕ → Ω' → ℂ × ℂ → EReal := fun n ω =>
    finiteMetricE (circleCoordsInv (Y n ω).2.1)
  exact ⟨Ω', mΩ', sbΩ', P', hP', h', hN, F, L,
    hLm, hNorm, hPairLaw, hFieldTop, fun n => ae_of_all P' (hCont n),
    hLsc, hRat, hGeometry⟩

 
theorem dg20LimitSk_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (hRatio : B2.Iface.DG20QuantileRatio)
    (hRelation : B2.Iface.DG20ExponentRelation)
    (hPositive : B2.Iface.DG20ExponentPositive)
    (hTop : B2.Iface.LscTop) : DG20LimitSk :=
  B2.PfeAxioms.Inputs.dg20LimitSk_of_standardBorel
    (dg20LimitSkSB_of_inputs hS4 hPerc hRatio hRelation hPositive hTop)

 
theorem dg20LimitSkC_of_inputs_via_SkSB
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (hRatio : B2.Iface.DG20QuantileRatio)
    (hRelation : B2.Iface.DG20ExponentRelation)
    (hPositive : B2.Iface.DG20ExponentPositive)
    (hTop : B2.Iface.LscTop) : DG20LimitSkC :=
  dg20LimitSkC_of_standardBorel_topological
    (dg20LimitSkSB_of_inputs hS4 hPerc hRatio hRelation hPositive hTop)

 

theorem ae_pairing_tendsto_of_ae_tendsto {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {hN : ℕ → Ω' → DistC} {h' : Ω' → DistC}
    (hField : ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω))) :
    ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)) :=
  fun φ => hField.mono fun ω hω =>
    ((continuous_eval_const φ).tendsto (h' ω)).comp hω

 

theorem dg20LimitSkSB_hpair (hSB : B2.PfeAxioms.Inputs.DG20LimitSkSB)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ δ, IsHeatSmoothing P h δ (X δ)) →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω')
          (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC),
          IsNormalizedWholePlaneGFF h' P' ∧
          ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)) := by
  obtain ⟨φ, hφ, -, -, hCouple⟩ := hSB ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, ?_⟩
  intro Ω mΩ P hP h hh X hX
  obtain ⟨Ω', M', SB', P', hP', h', hN, F, L,
    -, hh', -, hField, -⟩ := hCouple P h hh X hX
  exact ⟨Ω', M', SB', P', hP', h', hN, hh', ae_pairing_tendsto_of_ae_tendsto hField⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
