import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.PropCardPathwise
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.EventGood




 
set_option autoImplicit false
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC)

 

theorem prop_card_ae
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D)
    (hD' : IsWeakLQGMetric ξ Q D')
    (cP : NNReal) (hcmid0 : 0 ≤ cMid) (hcmid : cMid < (cP : ℝ))
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cP)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) :
    ∃ Ccard : ℕ, 1 < Ccard ∧
      ∀ (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
        (obj : ∀ i : ℤ × ℤ,
          EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
            (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
        (k : ℕ), ∀ᵐ ω ∂P,
      let family : Set (Finset (ℤ × ℤ)) := {Z |
        EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
        EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid (cP : ℝ≥0∞) par pbar
          r b q K₁ K₂ obj Z
          (LQGMetric.addFun (h ω) (LQGMetric.testCont
            (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)))}
      family.Finite ∧ family.ncard ≤ Ccard ^ k := by
  classical
  let A := ((cP : ℝ) - cMid) * par.Cinc
  let B := 1 + (cP : ℝ) * EndSaving.Choices.cSpent ξ par
  have hA : 0 < A := by
    dsimp [A]
    have := par.inc_pos
    positivity
  obtain ⟨M, hMgt⟩ := exists_nat_gt (B / A)
  have hM : B ≤ A * M := by
    have hh := (div_lt_iff₀ hA).mp hMgt
    linarith
  let Ccard : ℕ := 2 ^ ((1601 ^ 2) * (M + 1))
  have hCcard : 1 < Ccard := by
    dsimp [Ccard]
    have hE : 0 < (1601 ^ 2) * (M + 1) := by positivity
    exact one_lt_pow₀ (by omega) (Nat.ne_of_gt hE)
  refine ⟨Ccard, hCcard, ?_⟩
  intro r b q K₁ K₂ obj k
  have hreg : ∀ᵐ ω ∂P, EndSaving.Choices.RegularAt D (ξ : ℝ) (h ω) :=
    EndSaving.Choices.ae_regularAt_self hD P h hh
  have hreg' : ∀ᵐ ω ∂P, EndSaving.Choices.RegularAt D' (ξ : ℝ) (h ω) :=
    EndSaving.Choices.ae_regularAt_self hD' P h hh
  have hregShift : ∀ᵐ ω ∂P, ∀ Z : Finset (ℤ × ℤ),
      EndSaving.Choices.RegularAt D (ξ : ℝ)
        (LQGMetric.addFun (h ω) (LQGMetric.testCont
          (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z))) := by
    apply ae_all_iff.mpr
    intro Z
    exact EndSaving.Choices.ae_regularAt_shift hD P h hh
      (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)
  have hgoodAll : ∀ᵐ ω ∂P, ∀ Z : Finset (ℤ × ℤ), ∀ i ∈ Z,
      EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid (cP : ℝ≥0∞) par pbar
        r b q K₁ K₂ obj Z
        (LQGMetric.addFun (h ω) (LQGMetric.testCont
          (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z))) →
      EndSaving.FiniteEvents.GoodSiteV2 P h D D' ξ Q cMid par pbar
        r b q K₁ K₂ obj i (h ω) := by
    apply ae_all_iff.mpr
    intro Z
    exact event_good_ae P h hh D D' ξ Q cMid (cP : ℝ≥0∞)
      hD par pbar r b q K₁ K₂ obj Z
  filter_upwards [hreg, hreg', hregShift, hgoodAll, hPlus] with
    ω hregω hregω' hregS hgoodS hopt
  dsimp only
  let eligible : Finset (ℤ × ℤ) → Prop := fun Z =>
    EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
    EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid (cP : ℝ≥0∞) par pbar
      r b q K₁ K₂ obj Z
      (LQGMetric.addFun (h ω) (LQGMetric.testCont
        (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)))
  by_cases hsome : ∃ Z : Finset (ℤ × ℤ), eligible Z
  · obtain ⟨Z₀, hZ₀⟩ := hsome
    have hcp : (0 : ℝ≥0∞) < cP := by
      have : (0 : ℝ) < (cP : ℝ) := lt_of_le_of_lt hcmid0 hcmid
      exact_mod_cast this
    have hcomp : ∀ x y : ℂ, D' (h ω) (x, y) ≤
        (cP : ℝ≥0∞) * D (h ω) (x, y) := by
      intro x y
      rw [← hopt]
      exact EndSaving.Choices.allPairs_le_upperOptimal (D (h ω)) (D' (h ω))
        (hopt.symm ▸ hcp) x y
    exact prop_card_pathwise_of_good_link P h D D' ξ Q cMid cP
      hcmid0 hcmid par pbar r b q K₁ K₂ obj Z₀ (h ω)
      hZ₀.1 hregω hregω' (hregS Z₀) hcomp hZ₀.2.2 M k
      (by simpa only [B, A] using hM) hZ₀.2.1
      (fun Z _ hF i hi => hgoodS Z i hi hF)
  · have hempty : ({Z : Finset (ℤ × ℤ) | eligible Z} : Set (Finset (ℤ × ℤ))) = ∅ := by
      ext Z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hZ => hsome ⟨Z, hZ⟩
    change ({Z : Finset (ℤ × ℤ) | eligible Z} : Set (Finset (ℤ × ℤ))).Finite ∧
      ({Z : Finset (ℤ × ℤ) | eligible Z} : Set (Finset (ℤ × ℤ))).ncard ≤ Ccard ^ k
    rw [hempty]
    simp

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
