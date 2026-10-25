import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.RawScaleFamily
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.FiniteGrid




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC)

 
theorem counting_event_le_grid_budget_of_choices
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (R : EndSaving.Interfaces.AdmissibleRadii)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar z r)
    (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (k : ℕ) (c₁ : ℝ) (_hc₁ : 0 < c₁) (B : ℝ≥0∞)
    (hbudget : ∀ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii)
      (q : Set.Ioi (0 : ℝ)),
      (∑' Z : Finset (ℤ × ℤ),
        P {ω | EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
          EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
            r b q K₁ K₂
            (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr)
            Z (h ω)}) ≤ B)
    (G : Set Ω)
    (hchoices : ∀ᵐ ω ∂P, ω ∈ G →
      ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii),
        ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
        ∃ q : Set.Ioi (0 : ℝ), EndSaving.Interfaces.IsDyadicSize (q : ℝ) ∧
          (1 / 2) * ε ^ (2 * (ξ : ℝ) * (Q + 3)) ≤ (q : ℝ) ∧
          (q : ℝ) ≤ ε ^ ((ξ : ℝ) * min (Q - 3) (2 * (Q - 3))) ∧
          ∃ 𝓕 : Finset (Finset (ℤ × ℤ)),
            (∀ Z ∈ 𝓕, Z.card ≤ k ∧ EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus
              par pbar r b q K₁ K₂
              (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr)
              Z (h ω)) ∧
            ε ^ (-(c₁ * k)) ≤ (𝓕.card : ℝ)) :
    P G ≤
      ((windowGrid R ξ Q ε hε b).card : ℝ≥0∞) *
        (B / ENNReal.ofReal (ε ^ (-(c₁ * k)))) := by
  classical
  let J := windowGrid R ξ Q ε hε b
  let κ := {j : Set.Ioi (0 : ℝ) × ℤ // j ∈ J}
  let qOf (j : κ) : Set.Ioi (0 : ℝ) :=
    ⟨(2 : ℝ) ^ j.1.2, zpow_pos (by norm_num : (0 : ℝ) < 2) j.1.2⟩
  have hrOf (j : κ) : (j.1.1 : ℝ) ∈ R.radii := by
    have hj := (Finset.mem_product.mp j.2).1
    have hj' : j.1.1 ∈ windowRadii R ε b := by simpa [J, windowGrid] using hj
    exact hj'.1
  let objOf (j : κ) : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((j.1.1 : ℝ) / 100) i) j.1.1 :=
    fun i => family (LQGMetric.GM.gridPt ((j.1.1 : ℝ) / 100) i)
      j.1.1 (hrOf j)
  have hfam (j : κ) : ∃ A : Finset (ℤ × ℤ) → Set Ω,
      (∀ Z, MeasurableSet (A Z)) ∧
      (∀ᵐ ω ∂P, ∀ Z, (ω ∈ A Z) ↔
        (EndSaving.Interfaces.Configuration j.1.1 b K₁ K₂ Z ∧ Z.card ≤ k ∧
          EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
            j.1.1 b (qOf j) K₁ K₂ (objOf j) Z (h ω))) ∧
      (∑' Z, P (A Z)) ≤ B := by
    exact raw_scale_borel_family P h hh D D' ξ Q cMid cPlus hD hD'
      par pbar j.1.1 b (qOf j) K₁ K₂ hK₁ hK₂ (objOf j) k B
      (hbudget j.1.1 (hrOf j) (qOf j))
  let A : κ → Finset (ℤ × ℤ) → Set Ω := fun j => Classical.choose (hfam j)
  have hA (j : κ) (Z : Finset (ℤ × ℤ)) : MeasurableSet (A j Z) :=
    (Classical.choose_spec (hfam j)).1 Z
  have heq : ∀ᵐ ω ∂P, ∀ j : κ, ∀ Z : Finset (ℤ × ℤ),
      (ω ∈ A j Z) ↔
        (EndSaving.Interfaces.Configuration j.1.1 b K₁ K₂ Z ∧ Z.card ≤ k ∧
          EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
            j.1.1 b (qOf j) K₁ K₂ (objOf j) Z (h ω)) := by
    apply ae_all_iff.mpr
    intro j
    exact (Classical.choose_spec (hfam j)).2.1
  have hsum (j : κ) : (∑' Z, P (A j Z)) ≤ B :=
    (Classical.choose_spec (hfam j)).2.2
  let N := ENNReal.ofReal (ε ^ (-(c₁ * k)))
  have hN0 : N ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hNtop : N ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcover : ∀ᵐ ω ∂P, ω ∈ G →
      ω ∈ ⋃ j ∈ (Finset.univ : Finset κ),
        {ω | N ≤ ∑' Z, (A j Z).indicator (fun _ => (1 : ℝ≥0∞)) ω} := by
    filter_upwards [hchoices, heq] with ω hc he hG
    obtain ⟨r, hr, hrlo, hrhi, q, hqd, hqlo, hqhi, 𝓕, h𝓕, hcard⟩ := hc hG
    obtain ⟨ℓ, hqℓ⟩ := hqd
    have hjrad : r ∈ windowRadii R ε b := ⟨hr, hrlo, hrhi⟩
    have hjdy : ℓ ∈ windowSizes ξ Q ε := by
      apply dyadic_mem_windowSizes hε
      · simpa only [← hqℓ] using hqlo
      · simpa only [← hqℓ] using hqhi
    have hj : (r, ℓ) ∈ J := by
      simp only [J, windowGrid, Finset.mem_product]
      exact ⟨by simpa using hjrad, hjdy⟩
    let j : κ := ⟨(r, ℓ), hj⟩
    have hqeq : qOf j = q := by
      apply Subtype.ext
      exact hqℓ.symm
    have hF : ∀ Z ∈ 𝓕, ω ∈ A j Z := by
      intro Z hZ
      obtain ⟨hzk, hfv⟩ := h𝓕 Z hZ
      apply (he j Z).2
      change EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
        EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar
          r b (qOf j) K₁ K₂ (objOf j) Z (h ω)
      have hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z := hfv.1.2.1
      exact ⟨hconfig, hzk, by simpa only [hqeq, objOf] using hfv⟩
    have hFcount := card_le_tsum_indicator_of_family (A j) ω 𝓕 hF
    have hNcard : N ≤ (𝓕.card : ℝ≥0∞) := by
      exact ENNReal.ofReal_le_ofReal hcard |>.trans_eq (by simp)
    have hcount : N ≤ ∑' Z, (A j Z).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
      hNcard.trans hFcount
    simp only [Set.mem_iUnion]
    exact ⟨j, ⟨by simp, hcount⟩⟩
  have hbound := outer_measure_le_of_ae_finite_grid_budget P
    (Finset.univ : Finset κ) A (by intros; exact hA _ _) B N hN0 hNtop
    (by intros; exact hsum _) G hcover
  change P G ≤ (Fintype.card J : ℝ≥0∞) * (B / N) at hbound
  rw [Fintype.card_coe] at hbound
  simpa only [N, J] using hbound

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
