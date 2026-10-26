import SupercriticalLFPPAS.ContractionStep.RadiusSequence
import SupercriticalLFPPAS.Concentration.AnnulusConcentration

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric (DistC addConst circleAvg)
open LQGMetric.Blueprint (fieldSigmaClosed0 countOcc)
open SupercriticalLFPPAS.Core
open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF)

namespace SupercriticalLFPPAS.ContractionStep

/-- At one centre, the probability that none of the selected exponents supplies a root event is
bounded by the annulus concentration estimate. The finite selected set is sorted decreasingly,
then continued by geometric padding after its last member. -/
theorem noGoodSelected_probability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (a b p C ε s t : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1)
    (hp : 0 < p) (hp1 : p < 1) (hC : 0 < C)
    (hconc : ∀ (z : ℂ) (r : ℕ → ℝ) (E : ℕ → Set Ω),
      (∀ k, 1 ≤ k → 0 < r k) →
      (∀ j k, 1 ≤ j → j ≤ k → r k ≤ r j) →
      (∀ k, 1 ≤ k → r (k + 1) / r k ≤ (1 / 4096 : ℝ)) →
      (∀ k, 1 ≤ k → MeasurableSet[
        fieldSigmaClosed0 (fun ω => addConst (h ω) (-circleAvg (h ω) (r k) z))
          {x | r k / 16 ≤ dist x z ∧ dist x z ≤ 32 * r k}] (E k)) →
      (∀ k, 1 ≤ k → ENNReal.ofReal p ≤ P (E k)) →
      ∀ n : ℕ, P {ω | (countOcc E n ω : ℝ) < b * n} ≤
        ENNReal.ofReal (C * Real.exp (-a * n)))
    (E : ℝ → ℝ → ℂ → Set Ω)
    (hEvent : ∀ r, ε ^ t ≤ r → r ≤ ε ^ s → ∀ z,
      MeasurableSet[fieldSigmaClosed0
        (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
        {x | r / 16 ≤ dist x z ∧ dist x z ≤ 32 * r}] (E ε r z) ∧
        ENNReal.ofReal p ≤ P (E ε r z))
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < s) (hst : s < t)
    (Sε : Finset ℤ) (hS : Sε ⊆ Iteration.radiusExponents ε s t)
    (hn : 2 ≤ Sε.card) (z : ℂ) :
    P {ω | ∀ j ∈ Sε, ω ∉ E ε (bandRad j) z} ≤
      ENNReal.ofReal (C * Real.exp (-a * Sε.card)) := by
  classical
  let n := Sε.card
  let rseq : ℕ → ℝ := paddedRadius Sε
  let Eseq : ℕ → Set Ω := fun k => if k ≤ n then E ε (rseq k) z else Set.univ
  have hn2 : 2 ≤ n := hn
  have hncard : n ≤ Sε.card := le_rfl
  have hrpos : ∀ k, 1 ≤ k → 0 < rseq k := by
    intro k hk
    exact paddedRadius_pos Sε k hk
  have hranti : ∀ j k, 1 ≤ j → j ≤ k → rseq k ≤ rseq j := by
    intro j k hj hjk
    exact paddedRadius_antitone Sε hjk
  have hrratio : ∀ k, 1 ≤ k → rseq (k + 1) / rseq k ≤ (1 / 4096 : ℝ) := by
    intro k hk
    simpa [rseq, Iteration.annulusBase] using paddedRadius_ratio_le Sε hk
  have hmeas : ∀ k, 1 ≤ k → MeasurableSet[
      fieldSigmaClosed0 (fun ω => addConst (h ω) (-circleAvg (h ω) (rseq k) z))
        {x | rseq k / 16 ≤ dist x z ∧ dist x z ≤ 32 * rseq k}] (Eseq k) := by
    intro k hk
    by_cases hkn : k ≤ n
    · have hidx : k - 1 < Sε.card := by omega
      have hj : paddedExponent Sε (k - 1) ∈ Sε := paddedExponent_mem hidx
      have hjfull : paddedExponent Sε (k - 1) ∈ Iteration.radiusExponents ε s t := hS hj
      have hcut := (Iteration.radiusExponents_mem_iff_cutoffs hε).1 hjfull
      have hrcut : ε ^ t ≤ rseq k ∧ rseq k ≤ ε ^ s := by
        dsimp [rseq, paddedRadius, Core.bandRad]
        exact ⟨hcut.1.le, hcut.2.le⟩
      have hmeasprob := hEvent (rseq k) hrcut.1 hrcut.2 z
      simpa [Eseq, if_pos hkn] using hmeasprob.1
    · simp [Eseq, hkn]
  have hprob : ∀ k, 1 ≤ k → ENNReal.ofReal p ≤ P (Eseq k) := by
    intro k hk
    by_cases hkn : k ≤ n
    · have hidx : k - 1 < Sε.card := by omega
      have hj : paddedExponent Sε (k - 1) ∈ Sε := paddedExponent_mem hidx
      have hjfull : paddedExponent Sε (k - 1) ∈ Iteration.radiusExponents ε s t := hS hj
      have hcut := (Iteration.radiusExponents_mem_iff_cutoffs hε).1 hjfull
      have hrcut : ε ^ t ≤ rseq k ∧ rseq k ≤ ε ^ s := by
        dsimp [rseq, paddedRadius, Core.bandRad]
        exact ⟨hcut.1.le, hcut.2.le⟩
      have hmeasprob := hEvent (rseq k) hrcut.1 hrcut.2 z
      simpa [Eseq, if_pos hkn] using hmeasprob.2
    · have hpENN : ENNReal.ofReal p ≤ 1 := by
        have h := ENNReal.ofReal_le_ofReal hp1.le
        simpa using h
      simpa [Eseq, hkn, measure_univ] using hpENN
  have htail := hconc z rseq Eseq hrpos hranti hrratio hmeas hprob n
  have hnoevent : {ω | ∀ j ∈ Sε, ω ∉ E ε (bandRad j) z} ⊆
      {ω | (countOcc Eseq n ω : ℝ) < b * n} := by
    intro ω hω
    have hempty : {k ∈ Finset.Icc 1 n | ω ∈ Eseq k} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkIcc, hkE⟩
      have hkRange := Finset.mem_Icc.mp hkIcc
      have hidx : k - 1 < Sε.card := by omega
      have hj : paddedExponent Sε (k - 1) ∈ Sε := paddedExponent_mem hidx
      have hkE' : ω ∈ E ε (bandRad (paddedExponent Sε (k - 1))) z := by
        simpa [Eseq, rseq, paddedRadius, Core.bandRad, if_pos hkRange.2] using hkE
      exact hω _ hj hkE'
    have hzero : countOcc Eseq n ω = 0 := by
      unfold countOcc
      rw [hempty]
      rfl
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn2)
    change (countOcc Eseq n ω : ℝ) < b * n
    rw [hzero]
    simpa using mul_pos hb hnpos
  simpa [n] using (measure_mono hnoevent).trans htail

end SupercriticalLFPPAS.ContractionStep
