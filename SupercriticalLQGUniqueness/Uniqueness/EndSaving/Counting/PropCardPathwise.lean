import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.PropCardGeometry
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.OldGeoCountV2




 
set_option autoImplicit false
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC)

 

theorem prop_card_pathwise_of_good_link
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (cP : NNReal) (hcmid0 : 0 ≤ cMid) (hcmid : cMid < (cP : ℝ))
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z₀ : Finset (ℤ × ℤ)) (g : DistC)
    (hcfg₀ : EndSaving.Interfaces.Configuration r b K₁ K₂ Z₀)
    (hreg : EndSaving.Choices.RegularAt D (ξ : ℝ) g)
    (hreg' : EndSaving.Choices.RegularAt D' (ξ : ℝ) g)
    (hregs : EndSaving.Choices.RegularAt D (ξ : ℝ)
      (LQGMetric.addFun g (LQGMetric.testCont
        (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z₀))))
    (hcomp : ∀ x y : ℂ, D' g (x, y) ≤ (cP : ℝ≥0∞) * D g (x, y))
    (hF₀ : EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid (cP : ℝ≥0∞) par pbar
      r b q K₁ K₂ obj Z₀
      (LQGMetric.addFun g (LQGMetric.testCont
        (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z₀))))
    (M k : ℕ)
    (hM : 1 + (cP : ℝ) * EndSaving.Choices.cSpent ξ par ≤
      ((cP : ℝ) - cMid) * par.Cinc * M)
    (hZ₀k : Z₀.card ≤ k)
    (hgood_link : ∀ Z : Finset (ℤ × ℤ),
      EndSaving.Interfaces.Configuration r b K₁ K₂ Z →
      EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid (cP : ℝ≥0∞) par pbar
        r b q K₁ K₂ obj Z
        (LQGMetric.addFun g (LQGMetric.testCont
          (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z))) →
      ∀ i ∈ Z, EndSaving.FiniteEvents.GoodSiteV2 μ h D D' ξ Q cMid par pbar
        r b q K₁ K₂ obj i g) :
    let family : Set (Finset (ℤ × ℤ)) := {Z |
      EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
      EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid (cP : ℝ≥0∞) par pbar
        r b q K₁ K₂ obj Z
        (LQGMetric.addFun g (LQGMetric.testCont
          (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z)))}
    family.Finite ∧ family.ncard ≤ (2 ^ ((1601 ^ 2) * (M + 1))) ^ k := by
  classical
  dsimp only
  let eligible : Finset (ℤ × ℤ) → Prop := fun Z =>
    EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
    EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid (cP : ℝ≥0∞) par pbar
      r b q K₁ K₂ obj Z
      (LQGMetric.addFun g (LQGMetric.testCont
        (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z)))
  let good : ℤ × ℤ → Prop := fun i =>
    EndSaving.FiniteEvents.GoodSiteV2 μ h D D' ξ Q cMid par pbar r b q K₁ K₂ obj i g ∧
    Disjoint (B4 r i) (obstacles b K₁ K₂)
  have hcount : ∀ Z₁ : Finset (ℤ × ℤ),
      (∀ i ∈ Z₁, good i ∧ ∀ a ∈ Z₀, i ∉ neighbors a) →
      (∀ i ∈ Z₁, ∀ j ∈ Z₁, i ≠ j → i ∉ neighbors j) →
      Z₁.card ≤ M * Z₀.card := by
    intro Z₁ hg hs
    have hfar : ∀ i ∈ Z₁, ∀ a ∈ Z₀, i ∉ neighbors a :=
      fun i hi a ha => (hg i hi).2 a ha
    have hcfg : EndSaving.Interfaces.Configuration r b K₁ K₂ (Z₀ ∪ Z₁) :=
      configuration_union_of_separated r b K₁ K₂ Z₀ Z₁ hcfg₀
        (fun i hi => (hg i hi).1.2) hfar hs
    have hdj := disjoint_of_far Z₀ Z₁ hfar
    have hc := EndSaving.Choices.old_geo_count_pathwise μ h D D' ξ Q cMid
      (cP : ℝ≥0∞) par pbar r b q K₁ K₂ obj Z₀ Z₁ hcfg hdj g
      hreg hreg' hregs cP rfl hcmid0 hcmid hcomp hF₀
      (fun i hi => (hg i hi).1.1)
    have hcoeff : 0 < ((cP : ℝ) - cMid) * par.Cinc := by
      have := par.inc_pos
      positivity
    have hmul :
      (1 + (cP : ℝ) * EndSaving.Choices.cSpent ξ par) * Z₀.card ≤
        (((cP : ℝ) - cMid) * par.Cinc * M) * Z₀.card :=
      mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _)
    have hle : (Z₁.card : ℝ) ≤ ((M * Z₀.card : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hle
  have hgood : ∀ Z : Finset (ℤ × ℤ), eligible Z → ∀ i ∈ Z, good i := by
    intro Z hZ i hi
    exact ⟨hgood_link Z hZ.1 hZ.2.2 i hi, hZ.1.2 i hi⟩
  have hbase := uniform_family_count eligible Z₀ neighbors good (1601 ^ 2) M
    self_mem_neighbors neighbors_symm (fun i => by rw [neighbors_card]) hgood hcount
  have hpow : 2 ^ ((1601 ^ 2) * ((M + 1) * Z₀.card)) ≤
      (2 ^ ((1601 ^ 2) * (M + 1))) ^ k := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    nlinarith [Nat.mul_le_mul_left ((1601 ^ 2) * (M + 1)) hZ₀k]
  exact ⟨hbase.1, hbase.2.trans hpow⟩

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
