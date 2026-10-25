import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.WeylTransferV2




 













set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter LQGMetric.MetricGeometry
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
theorem around_bound_field {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ} {pbar : Set.Ioo (0 : ℝ) 1}
    {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (u : DistC) (hu : u ∈ obj.E) (c : ℝ) (hc : IsCircleAverage u r z c) :
    aroundDist (D u) ⟨(z, (3 * (r : ℝ), 4 * (r : ℝ))), by
        have hr0 : (0 : ℝ) < (r : ℝ) := r.property
        show 0 < 3 * (r : ℝ) ∧ 3 * (r : ℝ) < 4 * (r : ℝ)
        constructor <;> linarith⟩ ≤
      ENNReal.ofReal par.Caround * ENNReal.ofReal (scaleN ξ Q r c) := by
  obtain ⟨_, ⟨A, hAz, hAr, hAR, hAroundA⟩, _⟩ := obj.E_bounds u hu c hc
  have hAeq : A = ⟨(z, (3 * (r : ℝ), 4 * (r : ℝ))), by
      have hr0 : (0 : ℝ) < (r : ℝ) := r.property
      show 0 < 3 * (r : ℝ) ∧ 3 * (r : ℝ) < 4 * (r : ℝ)
      constructor <;> linarith⟩ := by
    apply Subtype.ext
    rcases A with ⟨⟨a, ⟨s, t⟩⟩, ha⟩
    change a = z at hAz
    change s = 3 * (r : ℝ) at hAr
    change t = 4 * (r : ℝ) at hAR
    simp only [hAz, hAr, hAR]
  rw [← hAeq]
  exact hAroundA

 

theorem ov_finite_of_event {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ} {pbar : Set.Ioo (0 : ℝ) 1}
    {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (u : DistC) (hu : u ∈ obj.E) (c : ℝ) (hc : IsCircleAverage u r z c)
    (d1 : LSCMetric) (hB : BiLipschitz.Barrier.Barrier d1) (hL : d1.IsLengthSpace) (f : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, D u p = weylScale ξ f d1 p)
    (hfn : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ par.Cmax)
    (hf0 : ∀ x ∈ ball z (4 * (r : ℝ)), x ∉ (obj.V : Set ℂ) → f x = 0)
    (P : ℝ → ℂ) {T : ℝ} (hG : IsGeodesicCurve (d1.pt ∘ P) 0 T)
    (hu' : HasUnitSpeedOn (d1.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 ∉ ball z (4 * (r : ℝ))) (hPT : P T ∉ ball z (4 * (r : ℝ))) :
    ∃ hfin : (ovSet P T (ball z (4 * (r : ℝ))) obj.V).Finite,
      (hfin.toFinset.card : ℝ) * par.Cacross ≤ par.Caround := by
  have hr0 : (0 : ℝ) < r := r.property
  have hξ : (0 : ℝ) ≤ ξ := ξ.property.le
  have hP : ContinuousOn P (Icc 0 T) := EndSaving.Spent.continuousOn_euclid_of_barrier d1 hB hL ⟨hG.1, hG.2.1⟩
  have hV : closure (obj.V : Set ℂ) ⊆ ball z (3 * (r : ℝ)) :=
    fun x hx => mem_ball.mpr (obj.closure_V_annulus hx).2
  set N := scaleN ξ Q r c with hN
  have hNpos : 0 < N := scaleN_pos ξ Q r c
  obtain ⟨hcross, _, _⟩ := obj.E_bounds u hu c hc
  have hcharge : ENNReal.ofReal (par.Cacross * N) ≤
      OptimalConstants.Ratios.setDist (D u) (sphere z (3 * (r : ℝ))) (obj.V : Set ℂ) := by
    rw [ENNReal.ofReal_mul par.across_pos.le]
    exact hcross.trans (setDist_sphere_tube_ge (D u) _ _ _ subset_union_right)
  have h4 : ∀ x : ℂ, x ∉ ball z (4 * (r : ℝ)) → 4 * (r : ℝ) ≤ dist x z := by
    intro x hx; simpa only [mem_ball, not_lt] using hx
  have haround : (EndSaving.Spent.closedContactTimes P (obj.V : Set ℂ) T).Nonempty →
      ENNReal.ofReal (EndSaving.Spent.lastClosedContact P (obj.V : Set ℂ) T -
        EndSaving.Spent.firstClosedContact P (obj.V : Set ℂ) T) ≤ ENNReal.ofReal (par.Caround * N) := by
    intro hne
    rw [ENNReal.ofReal_mul par.around_pos.le]
    exact EndSaving.ChoicesCore.newDist_around_closed_contacts d1 (D u) ξ hξ f hB hL hWeyl hfn P
      (obj.V : Set ℂ) z hr0 hG hu' hV (h4 _ hP0) (h4 _ hPT) hne _ _
      (around_bound_field obj u hu c hc)
  obtain ⟨hfin, hcard⟩ := ovSet_finite_card d1 (D u) ξ ((ξ : ℝ) * par.Cmax)
    (par.Cacross * N) (par.Caround * N) f hWeyl P hG hu' hP z r hr0 obj.V hV hf0
    (fun x => mul_le_mul_of_nonneg_left (hfC x) hξ) hcharge (mul_pos par.across_pos hNpos)
    (mul_le_mul_of_nonneg_right par.around_gt_across.le hNpos.le) haround
  refine ⟨hfin, ?_⟩
  have : (hfin.toFinset.card : ℝ) * par.Cacross * N ≤ par.Caround * N := by
    simpa only [mul_assoc] using hcard
  exact le_of_mul_le_mul_right this hNpos

 
theorem spent_window_field {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ} {pbar : Set.Ioo (0 : ℝ) 1}
    {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (u : DistC) (hu : u ∈ obj.E) (c : ℝ) (hc : IsCircleAverage u r z c)
    (d1 : LSCMetric) (hB : BiLipschitz.Barrier.Barrier d1) (hL : d1.IsLengthSpace) (f : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, D u p = weylScale ξ f d1 p)
    (hfn : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ par.Cmax)
    (P : ℝ → ℂ) {T : ℝ} (hG : IsGeodesicCurve (d1.pt ∘ P) 0 T)
    (hu' : HasUnitSpeedOn (d1.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 ∉ ball z (4 * (r : ℝ))) (hPT : P T ∉ ball z (4 * (r : ℝ)))
    (hne : (EndSaving.Spent.closedContactTimes P (obj.V : Set ℂ) T).Nonempty)
    (B : ℝ) (hNB : scaleN ξ Q r c ≤ 2 * B) :
    (D u).len P (EndSaving.Spent.firstClosedContact P (obj.V : Set ℂ) T)
        (EndSaving.Spent.lastClosedContact P (obj.V : Set ℂ) T) ≤
      ENNReal.ofReal (cSpent ξ par * B) := by
  have hr0 : (0 : ℝ) < r := r.property
  have hξ : (0 : ℝ) ≤ ξ := ξ.property.le
  have hV : closure (obj.V : Set ℂ) ⊆ ball z (3 * (r : ℝ)) :=
    fun x hx => mem_ball.mpr (obj.closure_V_annulus hx).2
  have h4 : ∀ x : ℂ, x ∉ ball z (4 * (r : ℝ)) → 4 * (r : ℝ) ≤ dist x z := by
    intro x hx; simpa only [mem_ball, not_lt] using hx
  have hB0 : 0 ≤ B := by
    have := scaleN_pos ξ Q r c; linarith
  have hcmp : ENNReal.ofReal (scaleN ξ Q r c) ≤ 2 * ENNReal.ofReal B := by
    calc ENNReal.ofReal (scaleN ξ Q r c) ≤ ENNReal.ofReal (2 * B) := ENNReal.ofReal_le_ofReal hNB
      _ = 2 * ENNReal.ofReal B := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hsp := EndSaving.ChoicesCore.newDist_spent_closed_contacts d1 (D u) ξ par.Cmax hξ f hB hL hWeyl hfn hfC
    P (obj.V : Set ℂ) z hr0 hG hu' hV (h4 _ hP0) (h4 _ hPT) hne _ _ _
    (around_bound_field obj u hu c hc) hcmp
  have htarget : (ENNReal.ofReal (Real.exp ((ξ : ℝ) * par.Cmax)) * ENNReal.ofReal par.Caround * 2) *
      ENNReal.ofReal B = ENNReal.ofReal (cSpent ξ par * B) := by
    unfold cSpent
    rw [ENNReal.ofReal_mul (by have := par.around_pos; positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [ENNReal.ofReal_ofNat]
    ring
  rw [← htarget]
  exact le_sup_right.trans hsp

 

theorem shortcut_chain {ι : Type*} [DecidableEq ι] (Dt Df : LSCMetric) (cPlus : NNReal)
    (hcomp : ∀ x y : ℂ, Dt (x, y) ≤ (cPlus : ℝ≥0∞) * Df (x, y))
    (P : ℝ → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (S : Finset ι) (s t : ι → ℝ) (hst : ∀ i ∈ S, s i < t i)
    (hin : ∀ i ∈ S, 0 ≤ s i ∧ t i ≤ T)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (L : ι → ℝ≥0∞) (hseg : ∀ i ∈ S, L i ≤ Df.len P (s i) (t i)) :
    Dt (P 0, P T) + ∑ i ∈ S, (cPlus : ℝ≥0∞) * L i ≤
      (cPlus : ℝ≥0∞) * Df.len P 0 T + ∑ i ∈ S, Dt (P (s i), P (t i)) := by
  have hadd : ∀ x y w : ℝ, x ≤ y → y ≤ w →
      (cPlus : ℝ≥0∞) * Df.len P x w =
        (cPlus : ℝ≥0∞) * Df.len P x y + (cPlus : ℝ≥0∞) * Df.len P y w := by
    intro x y w hxy hyw
    rw [← mul_add]
    congr 1
    unfold LSCMetric.len
    simpa only [Set.univ_inter] using (eVariationOn.Icc_add_Icc (Df.pt ∘ P) hxy hyw (mem_univ y)).symm
  have hchain := chain_bound S s t (fun x y => Dt (P x, P y))
    (fun x y => (cPlus : ℝ≥0∞) * Df.len P x y)
    (by intro x y w _ _; exact Dt.isExtMetric.2.2.2 _ _ _)
    hadd 0 T hT hst hin hdisj (by
      intro x y _ hxy _ _
      calc Dt (P x, P y) ≤ (cPlus : ℝ≥0∞) * Df (P x, P y) := hcomp _ _
        _ ≤ (cPlus : ℝ≥0∞) * Df.len P x y := by
            gcongr
            exact eVariationOn.edist_le (Df.pt ∘ P) (left_mem_Icc.mpr hxy)
              (right_mem_Icc.mpr hxy))
  calc Dt (P 0, P T) + ∑ i ∈ S, (cPlus : ℝ≥0∞) * L i
      ≤ Dt (P 0, P T) + ∑ i ∈ S, (cPlus : ℝ≥0∞) * Df.len P (s i) (t i) := by
        gcongr with i hi
        exact hseg i hi
    _ ≤ _ := hchain


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
