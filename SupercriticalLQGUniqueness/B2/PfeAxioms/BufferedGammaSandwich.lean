import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaAutoRadius
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaLower

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem buffered_gamma_sandwich
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (euclidForget (G n)))
    {W V K Kout U : Set ℂ}
    (hWV : W ⊆ V) (hWK : W ⊆ interior K)
    (hVKout : V ⊆ Kout) (hKout : IsCompact Kout) (hKoutU : Kout ⊆ U)
    (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (hneFront : (frontier V).Nonempty)
    (hdisj : Disjoint K (frontier V))
    (hsmall : SmallAnnulusCosts G D K V)
    (x y : W) {C : ℝ} (hC : 0 < C)
    (hxy : D.internal W (x, y) < ENNReal.ofReal C) :
    ∃ x' y' : ℕ → V,
      Tendsto (fun n => (x' n : ℂ)) atTop (𝓝 (x : ℂ)) ∧
      Tendsto (fun n => (y' n : ℂ)) atTop (𝓝 (y : ℂ)) ∧
      D.internal U
        (⟨(x : ℂ), hKoutU (hVKout (hWV x.property))⟩,
          ⟨(y : ℂ), hKoutU (hVKout (hWV y.property))⟩) ≤
        liminf (fun n => (G n).internal V (x' n, y' n)) atTop ∧
      (∀ᶠ n in atTop, (G n).internal V (x' n, y' n) < ENNReal.ofReal C) := by
  obtain ⟨x', y', hx', hy', hupper⟩ :=
    buffered_inner_internal_upper_of_compact_collar hG hLen hPath hforget
      hWV hWK hV hK hfront hneFront hdisj hsmall x y hC hxy
  have hxC : Tendsto (fun n => (x' n : ℂ)) atTop (𝓝 (x : ℂ)) :=
    (continuous_subtype_val.tendsto _).comp hx'
  have hyC : Tendsto (fun n => (y' n : ℂ)) atTop (𝓝 (y : ℂ)) :=
    (continuous_subtype_val.tendsto _).comp hy'
  refine ⟨x', y', hxC, hyC, ?_, hupper⟩
  exact buffered_internal_liminf hG hVKout hKout hKoutU x' y'
    ⟨(x : ℂ), hWV x.property⟩ ⟨(y : ℂ), hWV y.property⟩ hxC hyC

end SupercriticalLQGUniqueness.B2.PfeAxioms
