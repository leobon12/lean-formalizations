import SupercriticalLQGUniqueness.B2.DG20Lim.CanonicalSubseq
import SupercriticalLQGUniqueness.B2.DG20Lim.RatioFromSection4

 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_scale_canonical_coord_limit
    (hS4 : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c : Ioi (0 : ℝ) → Ioi (0 : ℝ),
        (∀ r : ℚ, ∀ hr : 0 < r,
          Tendsto (fun n => (r : ℝ) *
            (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                (Rat.cast_pos.mpr hr))⟩ : ℝ) /
            (m (ε (φ n)) : ℝ)) atTop
            (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
        ∃ ρ : ProbabilityMeasure ((CoordJ → ℝ) × RatCoords),
          Tendsto (β := ProbabilityMeasure ((CoordJ → ℝ) × RatCoords))
            (fun n => (⟨normGFFLaw.map
                (fun g => (pairJ ⊤ g, canonicalCoordSeq (ξ : ℝ) m ε (φ n) g)),
              (Measure.isProbabilityMeasure_map_iff
                (((measurable_pairJ ⊤).comp measurable_id).prodMk
                  (measurable_canonicalCoordSeq (ξ : ℝ) m ε (φ n))).aemeasurable).2
                  B2.PfeAxioms.normalized_canonical_model.1⟩ :
                ProbabilityMeasure ((CoordJ → ℝ) × RatCoords))) atTop (𝓝 ρ) ∧
          (ρ : Measure ((CoordJ → ℝ) × RatCoords)).map Prod.fst =
            normGFFLaw.map (pairJ ⊤) := by
  obtain ⟨φ₁, hφ₁, c, hc⟩ :=
    exists_scale_subseq_of_section4 hS4 ξ Q hQ m hm ε hε
  obtain ⟨ψ, hψ, ρ, hlim, hmarg⟩ :=
    exists_canonical_joint_coord_limit (ξ : ℝ) m (fun n => ε (φ₁ n))
  let φ : ℕ → ℕ := φ₁ ∘ ψ
  refine ⟨φ, hφ₁.comp hψ, c, ?_, ρ, ?_, hmarg⟩
  · intro r hr
    convert (hc r hr).comp hψ.tendsto_atTop using 1
    funext n
    rfl
  · simpa only [φ, Function.comp_apply, canonicalCoordSeq] using hlim

end SupercriticalLQGUniqueness.B2.DG20Lim
