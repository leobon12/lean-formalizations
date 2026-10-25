import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircCoupling
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2ProdLusin
import SupercriticalLQGUniqueness.B2.PfeLocal.L4Main

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify CoordJ pairJ pairJInv)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem exists_subseq_ae_of_coords_gen {T : Type} [TopologicalSpace T]
    [TopologicalSpace.MetrizableSpace T] [SecondCountableTopology T] [MeasurableSpace T]
    [BorelSpace T]
    (μ : Measure (CoordJ → ℝ)) [IsProbabilityMeasure μ]
    (R : ℕ → (CoordJ → ℝ) → T) (Φ' : (CoordJ → ℝ) → T)
    (hR : ∀ n, Measurable (R n)) (hΦ' : Measurable Φ')
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → CoordJ → ℝ) (Xl : Ω' → CoordJ → ℝ) (hXm : ∀ n, Measurable (X n))
    (hXlm : Measurable Xl) (hXlaw : ∀ n, P'.map (X n) = μ) (hXllaw : P'.map Xl = μ)
    (hXconv : ∀ᵐ ω ∂P', Tendsto (fun n => X n ω) atTop (𝓝 (Xl ω)))
    (hYconv : ∀ᵐ ω ∂P', Tendsto (fun n => R n (X n ω)) atTop (𝓝 (Φ' (Xl ω)))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → CoordJ → ℝ), AEMeasurable h P →
        P.map h = μ → ∀ᵐ ω ∂P, Tendsto (fun k => R (ns k) (h ω)) atTop (𝓝 (Φ' (h ω))) := by
  let _ : MetricSpace T := TopologicalSpace.metrizableSpaceMetric T
  let _ : MetricSpace (CoordJ → ℝ) := TopologicalSpace.metrizableSpaceMetric (CoordJ → ℝ)
  exact PfeWeyl.exists_subseq_ae_of_coupling_lusin.{0, 0, 0, 0} μ R Φ' hR P' X Xl hXm hXlm
    hXlaw hXllaw (fun n ω => R n (X n ω)) (fun n => (hR n).comp (hXm n))
    (fun n => Filter.EventuallyEq.rfl) hXconv hYconv (lusin_uniform_of_measurable μ hΦ')

 
theorem setDistance_normalizedLFPPMetric (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (A B : Set ℂ) :
    setDistance (PfeWeyl.normalizedLFPPMetric ξ a φ).1 A B =
      ENNReal.ofReal ((a : ℝ)⁻¹) * setDistance (lfppDistance ξ φ) A B := by
  have h0 : ENNReal.ofReal ((a : ℝ)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 a.property)).ne'
  have ht : ENNReal.ofReal ((a : ℝ)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold setDistance
  simp only [ENNReal.mul_iInf_of_ne h0 ht]
  refine iInf_congr fun u => iInf_congr fun _ => iInf_congr fun v => iInf_congr fun _ => ?_
  exact PfeWeyl.normalizedLFPPMetric_apply ξ a φ (u, v)

end SupercriticalLQGUniqueness.B2.PfeAxioms
