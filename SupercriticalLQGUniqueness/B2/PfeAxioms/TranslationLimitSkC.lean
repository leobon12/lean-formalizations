import SupercriticalLQGUniqueness.B2.PfeAxioms.TranslationLimitNormalized
import SupercriticalLQGUniqueness.B2.PfeAxioms.W3MeasurableShiftSkC
import SupercriticalLQGUniqueness.B2.PfeWeyl.InputsS1
import SupercriticalLQGUniqueness.B2.WeakStrong.Field

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_translation_of_dg20LimitSkC_w3
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (htail : PfeWeyl.NormalizedAcrossTails D)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε D)
    (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      D (translateDist z (h ω)) (u, v) = D (h ω) (u + z, v + z) := by
  let g : Ω → DistC := fun ω =>
    addConst (affineComp 1 z (h ω)) (-circleAvg (h ω) 1 z)
  have hg : IsNormalizedWholePlaneGFF g P :=
    (B2.DG20Pt.dg20_heat_translate_normalized P h hh z 1 one_pos).1
  let Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun δ =>
    (exists_heatVersion hg (δ : ℝ) δ.property).choose
  have hY : ∀ δ, IsHeatSmoothing P g δ (Y δ) := fun δ =>
    (exists_heatVersion hg (δ : ℝ) δ.property).choose_spec.2
  have hc : Measurable (fun ω => circleAvg (h ω) 1 z) :=
    (LQGMetric.measurable_circleAvg_left 1 z).comp hh.1.measurable
  have hW := ae_addConst_eq_scale_of_dg20LimitSkC_w3 hSkC
    ξ Q hQ m hm ε hε D hD P g hg Y hY
    (htail P g hg) (hsmall P g hg Y hY)
    (fun ω => circleAvg (h ω) 1 z) hc
  have hT := ae_recentered_translation_of_subseqLimit
    ξ m ε D hD P h hh X hX z
  filter_upwards [hW, hT] with ω hWω hTω
  intro u v
  let c := circleAvg (h ω) 1 z
  have hfield : addConst (g ω) c = translateDist z (h ω) := by
    simp only [g, c, B2.WeakStrong.addConst_addConst,
      neg_add_cancel, B2.Strong.addConst_zero,
      SupercriticalLQGUniqueness.translateDist_eq_affineComp_one]
  have hprod : ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) *
      ENNReal.ofReal (Real.exp (-(ξ : ℝ) * c)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    have hs : (ξ : ℝ) * c + -(ξ : ℝ) * c = 0 := by ring
    rw [hs]
    simp
  calc
    D (translateDist z (h ω)) (u, v) = D (addConst (g ω) c) (u, v) := by rw [hfield]
    _ = ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) * D (g ω) (u, v) := hWω (u, v)
    _ = ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) *
        (ENNReal.ofReal (Real.exp (-(ξ : ℝ) * c)) *
          D (h ω) (u + z, v + z)) := by rw [hTω (u, v)]
    _ = D (h ω) (u + z, v + z) := by rw [← mul_assoc, hprod, one_mul]

end SupercriticalLQGUniqueness.B2.PfeAxioms
