import SupercriticalLQGUniqueness.B2.DG20Lim.ScaleCanonicalSubseq
import SupercriticalLQGUniqueness.B2.DG20Lim.PolishOrder

 

















set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology LQGMetric
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

abbrev FieldCoords : Type := (CoordJ → ℝ) × OrdCoords

 
def fieldCoords (g : DistC) : FieldCoords := (pairJ ⊤ g, ordCoords (pairJ ⊤ g))

theorem measurable_fieldCoords : Measurable fieldCoords :=
  (measurable_pairJ ⊤).prodMk (measurable_ordCoords.comp (measurable_pairJ ⊤))

instance : PolishSpace FieldCoords := inferInstance

theorem isProbabilityMeasure_fieldLaw (ξ : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (n : ℕ) :
    IsProbabilityMeasure (normGFFLaw.map
      (fun g => (fieldCoords g, canonicalCoordSeq ξ m ε n g))) := by
  letI : IsProbabilityMeasure normGFFLaw :=
    B2.PfeAxioms.normalized_canonical_model.1
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fieldCoords.prodMk (measurable_canonicalCoordSeq ξ m ε n)).aemeasurable).2
      inferInstance

 

def fieldLawSeq (ξ : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (n : ℕ) : ProbabilityMeasure (FieldCoords × RatCoords) :=
  ⟨normGFFLaw.map (fun g => (fieldCoords g, canonicalCoordSeq ξ m ε n g)),
    isProbabilityMeasure_fieldLaw ξ m ε n⟩

theorem fieldLawSeq_coe (ξ : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (n : ℕ) :
    (fieldLawSeq ξ m ε n : Measure (FieldCoords × RatCoords)) =
      normGFFLaw.map (fun g => (fieldCoords g, canonicalCoordSeq ξ m ε n g)) := rfl

 

theorem exists_canonical_joint_field_limit
    (ξ : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (ε : ℕ → Ioi (0 : ℝ)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ ρ : ProbabilityMeasure (FieldCoords × RatCoords),
        Tendsto (fun n => fieldLawSeq ξ m ε (ψ n)) atTop (𝓝 ρ) ∧
        (ρ : Measure (FieldCoords × RatCoords)).map Prod.fst =
          normGFFLaw.map fieldCoords := by
  letI : IsProbabilityMeasure normGFFLaw :=
    B2.PfeAxioms.normalized_canonical_model.1
  exact LQGMetric.DFGPS.L217.exists_limit_coupling measurable_fieldCoords
    (measurable_canonicalCoordSeq ξ m ε) (IsTightMeasureSet.of_compactSpace)

 

theorem exists_scale_canonical_field_limit
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
        ∃ ρ : ProbabilityMeasure (FieldCoords × RatCoords),
          Tendsto (fun n => fieldLawSeq (ξ : ℝ) m (fun n => ε (φ n)) n)
            atTop (𝓝 ρ) ∧
          (ρ : Measure (FieldCoords × RatCoords)).map Prod.fst =
            normGFFLaw.map fieldCoords := by
  obtain ⟨φ₁, hφ₁, c, hc⟩ :=
    exists_scale_subseq_of_section4 hS4 ξ Q hQ m hm ε hε
  obtain ⟨ψ, hψ, ρ, hlim, hmarg⟩ :=
    exists_canonical_joint_field_limit (ξ : ℝ) m (fun n => ε (φ₁ n))
  refine ⟨φ₁ ∘ ψ, hφ₁.comp hψ, c, ?_, ρ, hlim, hmarg⟩
  intro r hr
  convert (hc r hr).comp hψ.tendsto_atTop using 1
  funext n
  rfl

end SupercriticalLQGUniqueness.B2.DG20Lim
