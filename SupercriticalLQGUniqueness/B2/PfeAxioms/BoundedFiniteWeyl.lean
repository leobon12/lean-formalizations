import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableHeatVersion
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionBdd
import SupercriticalLQGUniqueness.B2.PfeWeyl.NormalizedLFPP
import LQGMetric.LFPP.WeylBounds

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_bounded_shift_finiteLFPP_weyl
    (ξ : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (f : Ω → C(ℂ, ℝ)) (M : ℝ) (hf : ∀ ω z, |f ω z| ≤ M)
    (hb : IsGFFPlusBddCont (fun ω => addFun (h ω) (f ω)) P)
    (X Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hY : ∀ δ, IsHeatSmoothing P
      (fun ω => addFun (h ω) (f ω)) δ (Y δ)) :
    ∀ᵐ ω ∂P, ∀ n p,
      PfeWeyl.normalizedLFPPMetric ξ (m (ε n)) (Y (ε n) ω) p =
        weylScale ξ
          (LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
            (f ω) M (hf ω))
          (PfeWeyl.normalizedLFPPMetric ξ (m (ε n)) (X (ε n) ω)) p := by
  rw [ae_all_iff]
  intro n
  have hXe := ae_heat_smoothing_sequence_eq P h hh ε X hX
  have hYe := ae_heatVersion_eq_heatMollify_bdd hb (ε n) (Y (ε n)) (hY (ε n))
  have hconv := hh.1.ae_tendstoLocallyUniformly_heatMollify
    (ε n : ℝ) (ε n).property.ne'
  filter_upwards [hXe, hYe, hconv] with ω hXω hYω hc p
  have hfield : Y (ε n) ω = X (ε n) ω +
      LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (f ω) M (hf ω) := by
    ext z
    change Y (ε n) ω z = X (ε n) ω z + heatMollify (ε n : ℝ) (ofCont (f ω)) z
    rw [hYω z, hXω n z]
    exact congrFun
      (LFPP.heatMollify_addFun (ε n).property.ne'
        (fun u => (tendstoLocallyUniformlyOn_univ.2 hc.1).tendsto_at (mem_univ u))
        (f ω) M (hf ω)) z
  rw [hfield]
  exact PfeWeyl.normalizedLFPPMetric_add_eq_weylScale ξ (m (ε n))
    (X (ε n) ω)
    (LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (f ω) M (hf ω)) p

end SupercriticalLQGUniqueness.B2.PfeAxioms
