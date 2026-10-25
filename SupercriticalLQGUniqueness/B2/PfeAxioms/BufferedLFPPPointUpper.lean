import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaLower
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNormalizedUpper

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal
open LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem buffered_internal_le_liminf_lfppDOn
    (ξ : ℝ) (a : ℕ → Set.Ioi (0 : ℝ))
    (φ : ℕ → C(ℂ, ℝ)) (D : LSCMetric)
    (hG : Tendsto (fun n => PfeWeyl.normalizedLFPPMetric ξ (a n) (φ n))
      atTop (𝓝 D))
    {V K U : Set ℂ} (hVK : V ⊆ K) (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : V) :
    D.internal U
      (⟨(x : ℂ), hKU (hVK x.property)⟩,
        ⟨(y : ℂ), hKU (hVK y.property)⟩) ≤
      liminf (fun n => ENNReal.ofReal ((a n : ℝ)⁻¹) *
        lfppDOn ξ (φ n) V x y) atTop := by
  have hlow := buffered_internal_liminf hG hVK hK hKU
    (fun _ => x) (fun _ => y) x y tendsto_const_nhds tendsto_const_nhds
  exact hlow.trans <| Filter.liminf_le_liminf (Eventually.of_forall fun n =>
    normalizedLFPPMetric_internal_le_lfppDOn ξ (a n) (φ n) x y)

end SupercriticalLQGUniqueness.B2.PfeAxioms
