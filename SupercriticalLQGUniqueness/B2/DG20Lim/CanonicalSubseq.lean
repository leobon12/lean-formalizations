import SupercriticalLQGUniqueness.B2.DG20Lim.CanonicalCoordLaw

 


set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def canonicalCoordSeq (ξ : ℝ)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (n : ℕ) (g : DistC) : RatCoords :=
  canonicalRatCoords ξ (ε n) (m (ε n)) g

theorem measurable_canonicalCoordSeq (ξ : ℝ)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (n : ℕ) :
    Measurable (canonicalCoordSeq ξ m ε n) :=
  measurable_canonicalRatCoords ξ (ε n) (m (ε n))

 

theorem exists_canonical_joint_coord_limit
    (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ ρ : ProbabilityMeasure ((CoordJ → ℝ) × RatCoords),
        Tendsto (β := ProbabilityMeasure ((CoordJ → ℝ) × RatCoords))
          (fun n => (⟨normGFFLaw.map
              (fun g => (pairJ ⊤ g, canonicalCoordSeq ξ m ε (ψ n) g)),
            (Measure.isProbabilityMeasure_map_iff
              (((measurable_pairJ ⊤).comp measurable_id).prodMk
                (measurable_canonicalCoordSeq ξ m ε (ψ n))).aemeasurable).2
                B2.PfeAxioms.normalized_canonical_model.1⟩ :
              ProbabilityMeasure ((CoordJ → ℝ) × RatCoords))) atTop (𝓝 ρ) ∧
        (ρ : Measure ((CoordJ → ℝ) × RatCoords)).map Prod.fst =
          normGFFLaw.map (pairJ ⊤) := by
  letI : IsProbabilityMeasure normGFFLaw :=
    B2.PfeAxioms.normalized_canonical_model.1
  exact exists_joint_coord_limit normGFFLaw (id : DistC → DistC)
    measurable_id (canonicalCoordSeq ξ m ε)
    (measurable_canonicalCoordSeq ξ m ε)

end SupercriticalLQGUniqueness.B2.DG20Lim
