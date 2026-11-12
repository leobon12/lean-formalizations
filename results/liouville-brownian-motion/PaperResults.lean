import LBMHigherDim

/-! Main theorems of Bertacco–Gwynne, the cone clock and the additional planar cone identification. -/

#print axioms LBMHigherDim.theoremA
#print axioms LBMHigherDim.theoremB
#print axioms LBMHigherDim.theoremB_kernel
#print axioms LBMHigherDim.theoremC
#print axioms LBMHigherDim.theoremD
#print axioms LBMHigherDim.theoremE
#print axioms LBMHigherDim.coneClock
#print axioms LBMHigherDim.theoremF

#print LBMHigherDim.isProbabilityMeasure_normLGFLaw
#print LBMHigherDim.isNormalizedLGF_normLGFLaw
#print axioms HigherDimLQGMetric.exists_isWholeSpaceLGF
#print axioms LBMHigherDim.isNormalizedLGF_normLGFLaw
#print LBMHigherDim.lbm_a4
#print LBMHigherDim.lbm_a7_canonical

section PlanarWitness

open MeasureTheory HigherDimLQGMetric LBMHigherDim

local instance : IsProbabilityMeasure (normLGFLaw 2) :=
  isProbabilityMeasure_normLGFLaw (d := 2) (by decide)

-- Instantiate the every-start clock and the canonical strong Markov theorem at the actual field law.
#check fun {γ : ℝ} (hγ : Subcritical 2 γ) =>
  lbm_a4 (h := id) hγ (isNormalizedLGF_normLGFLaw (d := 2) (by decide))
#check fun {γ : ℝ} (hγ : Subcritical 2 γ) =>
  lbm_a7_canonical (h := id) hγ (isNormalizedLGF_normLGFLaw (d := 2) (by decide))

end PlanarWitness
