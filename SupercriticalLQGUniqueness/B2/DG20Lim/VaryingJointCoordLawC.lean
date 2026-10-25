import SupercriticalLQGUniqueness.B2.PfeAxioms.VaryingJointCoordLaw

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology TopologicalSpace
open LQGMetric
open SupercriticalLQGUniqueness.B2.PfeAxioms

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem joint_coord_limit_law_of_varying_fields_C
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (hN : ℕ → Ω' → DistC)
    (hhN : ∀ n, AEMeasurable (hN n) P')
    (h' : Ω' → DistC) (hh' : Measurable h')
    (G : ℕ → Ω → LSCFun) (hGm : ∀ n, AEMeasurable (G n) P)
    (F : ℕ → Ω' → LSCFun) (hFm : ∀ n, AEMeasurable (F n) P')
    (D : Ω → LSCFun) (hDm : AEMeasurable D P)
    (L : Ω' → LSCFun) (hLm : AEMeasurable L P')
    (hLaw : ∀ n,
      P.map (fun ω => (pairJ (⊤ : Opens ℂ) (h ω), G n ω)) =
      P'.map (fun ω => (pairJ (⊤ : Opens ℂ) (hN n ω), F n ω)))
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (𝓝 (D ω)))
    (hConvField : ∀ᵐ ω ∂P', Tendsto (fun n => pairJ (⊤ : Opens ℂ) (hN n ω))
      atTop (𝓝 (pairJ (⊤ : Opens ℂ) (h' ω))))
    (hConv' : ∀ᵐ ω ∂P', Tendsto (fun n => F n ω) atTop (𝓝 (L ω))) :
    P.map (fun ω => (pairJ (⊤ : Opens ℂ) (h ω), D ω)) =
      P'.map (fun ω => (pairJ (⊤ : Opens ℂ) (h' ω), L ω)) := by
  let j : DistC → CoordJ → ℝ := pairJ (⊤ : Opens ℂ)
  have hjm : Measurable j := measurable_pairJ _
  apply joint_limit_law_eq_of_finite_laws P P'
    (fun n ω => (j (h ω), G n ω))
    (fun n ω => (j (hN n ω), F n ω))
    (fun ω => (j (h ω), D ω))
    (fun ω => (j (h' ω), L ω))
  · intro n
    exact (hjm.comp hh).aemeasurable.prodMk (hGm n)
  · intro n
    exact (hjm.comp_aemeasurable (hhN n)).prodMk (hFm n)
  · exact (hjm.comp hh).aemeasurable.prodMk hDm
  · exact (hjm.comp hh').aemeasurable.prodMk hLm
  · exact hLaw
  · filter_upwards [hConv] with ω hω
    exact tendsto_const_nhds.prodMk_nhds hω
  · filter_upwards [hConvField, hConv'] with ω hω hω'
    exact hω.prodMk_nhds hω'


end SupercriticalLQGUniqueness.B2.DG20Lim
