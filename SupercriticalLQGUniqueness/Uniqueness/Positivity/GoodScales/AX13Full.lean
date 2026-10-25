import SupercriticalLQGUniqueness.Uniqueness.Positivity.GoodScales.AX11Full
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids.AX13Numeric
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX12
import LQGMetric.Papers.DFGPS.P4_1StepCross




 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.GoodScales

open LQGMetric (DistC circleAvg)
open SupercriticalLQGUniqueness

 
theorem trace_crossing_from_near_far
    (C : ℝ → ℂ) (a b : ℝ) (z : ℂ) (K k : ℕ) (hk : k ≤ K)
    (hcont : ContinuousOn C (Icc a b))
    (hnear : ∃ t ∈ Icc a b, dist (C t) z ≤ Positivity.Grids.mesh K)
    (hfar : ∃ t ∈ Icc a b,
      (4 / 5 : ℝ) * Positivity.Grids.radius k < dist (C t) z) :
    ∃ σ τ : ℝ, a ≤ σ ∧ σ < τ ∧ τ ≤ b ∧
      ((dist (C σ) z = (11 / 20 : ℝ) * Positivity.Grids.radius k ∧
        dist (C τ) z = (4 / 5 : ℝ) * Positivity.Grids.radius k) ∨
       (dist (C σ) z = (4 / 5 : ℝ) * Positivity.Grids.radius k ∧
        dist (C τ) z = (11 / 20 : ℝ) * Positivity.Grids.radius k)) ∧
      (∀ t ∈ Icc σ τ, C t ∈ Positivity.Grids.closedCrossingAnnulus z k) := by
  obtain ⟨tn, htn, hnear⟩ := hnear
  obtain ⟨tf, htf, hfar⟩ := hfar
  have hinner : dist (C tn) z < (11 / 20 : ℝ) * Positivity.Grids.radius k :=
    lt_of_le_of_lt hnear (Positivity.Grids.near_point_inner K k hk)
  have hrR : (11 / 20 : ℝ) * Positivity.Grids.radius k <
      (4 / 5 : ℝ) * Positivity.Grids.radius k := by
    have hr := Positivity.Grids.radius_pos k
    nlinarith
  by_cases hnf : tn ≤ tf
  · have hsub : Icc tn tf ⊆ Icc a b :=
      Icc_subset_Icc htn.1 htf.2
    obtain ⟨σ, τ, hσ, hστ, hτ, hσr, hτR, hclosed⟩ :=
      crossing_extract hnf (hcont.mono hsub) hrR hinner hfar
    refine ⟨σ, τ, htn.1.trans hσ, hστ, hτ.trans htf.2,
      Or.inl ⟨hσr, hτR⟩, ?_⟩
    intro t ht
    exact hclosed t ht
  · have hfn : tf ≤ tn := le_of_lt (lt_of_not_ge hnf)
    have hsub : Icc tf tn ⊆ Icc a b :=
      Icc_subset_Icc htf.1 htn.2
    obtain ⟨σ, τ, hσ, hστ, hτ, hσR, hτr, hclosed⟩ :=
      crossing_extract_reverse hfn (hcont.mono hsub) hrR hfar hinner
    refine ⟨σ, τ, htf.1.trans hσ, hστ, hτ.trans htn.2,
      Or.inr ⟨hσR, hτr⟩, ?_⟩
    intro t ht
    exact hclosed t ht

theorem witness_inner_ge (i : Fin 12) :
    (1 / 15 : ℝ) ≤ (Positivity.Witnesses.witnessAnnulus i).innerRadius := by
  induction i using Fin.cases with
  | zero => norm_num [Positivity.Witnesses.witnessAnnulus_zero, Positivity.Witnesses.largeAnnulus, EuclideanAnnulus.innerRadius]
  | succ j =>
      change 1 / 15 ≤ (Positivity.Witnesses.witnessAnnulus ⟨j.val + 1, by omega⟩).innerRadius
      rw [Positivity.Witnesses.witnessAnnulus_succ j]
      norm_num [Positivity.Witnesses.smallAnnulus, EuclideanAnnulus.innerRadius]

 
theorem trace_far_point
    (i : Fin 12) (C : ℝ → ℂ) (a b : ℝ) (z : ℂ)
    (K k : ℕ) (hK : 8 ≤ K) (hk : K / 2 ≤ k)
    (hnear : ∃ t ∈ Icc a b, dist (C t) z ≤ Positivity.Grids.mesh K)
    (hdiam : ∃ x ∈ C '' Icc a b, ∃ y ∈ C '' Icc a b,
      2 * (Positivity.Witnesses.witnessAnnulus i).innerRadius ≤ dist x y) :
    ∃ t ∈ Icc a b,
      (4 / 5 : ℝ) * Positivity.Grids.radius k < dist (C t) z := by
  obtain ⟨tn, htn, hnear⟩ := hnear
  obtain ⟨x, hx, y, hy, hxy⟩ := hdiam
  obtain ⟨tx, htx, rfl⟩ := hx
  obtain ⟨ty, hty, rfl⟩ := hy
  rcases Positivity.Grids.far_point_of_opposites hxy with hfar | hfar
  · refine ⟨tx, htx, ?_⟩
    apply Positivity.Grids.opposite_beyond_outer K k hK hk hnear
    exact (witness_inner_ge i).trans hfar
  · refine ⟨ty, hty, ?_⟩
    apply Positivity.Grids.opposite_beyond_outer K k hK hk hnear
    exact (witness_inner_ge i).trans hfar

 
theorem closed_crossing_subset_collar (z : ℂ) (k : ℕ) :
    Positivity.Grids.closedCrossingAnnulus z k ⊆ (collar z (dyadicRadius k) : Set ℂ) := by
  intro w hw
  change (1 / 2 : ℝ) * Positivity.Grids.radius k < ‖w - z‖ ∧
    ‖w - z‖ < (9 / 10 : ℝ) * Positivity.Grids.radius k
  rw [← dist_eq_norm]
  have hr := Positivity.Grids.radius_pos k
  exact ⟨by nlinarith [hw.1], by nlinarith [hw.2]⟩

 
theorem crossing_inner_mem_shape (z : ℂ) (k : ℕ) (w : ℂ)
    (hw : dist w z = (11 / 20 : ℝ) * Positivity.Grids.radius k) :
    w ∈ (shape z (dyadicRadius k)).innerBoundary := by
  change dist w (((dyadicRadius k : ℝ) • 0) + z) =
    (dyadicRadius k : ℝ) * (11 / 20 : ℝ)
  simpa only [smul_zero, zero_add, mul_comm, dyadicRadius, Positivity.Grids.radius] using hw

theorem crossing_outer_mem_shape (z : ℂ) (k : ℕ) (w : ℂ)
    (hw : dist w z = (4 / 5 : ℝ) * Positivity.Grids.radius k) :
    w ∈ (shape z (dyadicRadius k)).outerBoundary := by
  change dist w (((dyadicRadius k : ℝ) • 0) + z) =
    (dyadicRadius k : ℝ) * (4 / 5 : ℝ)
  simpa only [smul_zero, zero_add, mul_comm, dyadicRadius, Positivity.Grids.radius] using hw

 
theorem internal_reverse_le_len (D : LSCMetric) (Y : Set ℂ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (hY : ∀ t ∈ Icc a b, P t ∈ Y) :
    D.internal Y (⟨P b, hY b ⟨hP.1, le_rfl⟩⟩,
      ⟨P a, hY a ⟨le_rfl, hP.1⟩⟩) ≤ D.len P a b := by
  let R : ℝ → ℂ := fun t => P (a + b - t)
  have hmap : MapsTo (fun t : ℝ => a + b - t) (Icc a b) (Icc a b) := by
    intro t ht
    exact ⟨by dsimp; linarith [ht.2], by dsimp; linarith [ht.1]⟩
  have hR : D.IsCurve R a b := by
    refine ⟨hP.1, ?_⟩
    exact hP.2.comp (by fun_prop) hmap
  have hYR : ∀ t ∈ Icc a b, R t ∈ Y :=
    fun t ht => hY _ (hmap ht)
  have hRa : R a = P b := by
    dsimp [R]
    congr 1
    ring
  have hRb : R b = P a := by
    dsimp [R]
    congr 1
    ring
  have hle := D.internal_le_len Y R a b hR hYR
  let pR : (↥Y × ↥Y) :=
    (⟨R a, hYR a ⟨le_rfl, hR.1⟩⟩,
     ⟨R b, hYR b ⟨hR.1, le_rfl⟩⟩)
  let pP : (↥Y × ↥Y) :=
    (⟨P b, hY b ⟨hP.1, le_rfl⟩⟩,
     ⟨P a, hY a ⟨le_rfl, hP.1⟩⟩)
  have hpair : pR = pP := by
    ext <;> simp only [pR, pP, hRa, hRb]
  change D.internal Y pR ≤ D.len R a b at hle
  rw [hpair] at hle
  calc
    D.internal Y pP ≤ D.len R a b := hle
    _ = D.len P a b := by
      simpa only [LSCMetric.len, LQGMetric.MetricGeometry.curveLength, R, Function.comp_def] using
        (LQGMetric.MetricGeometry.curveLength_reverse (D.pt ∘ P) hP.1)

 
theorem crossing_intervals_separated
    {ι : Type*} (k : ι → ℕ) (hk : Function.Injective k)
    (C : ℝ → ℂ) (z : ℂ) (σ τ : ι → ℝ)
    (hseg : ∀ i, σ i < τ i)
    (hclosed : ∀ i, ∀ t ∈ Icc (σ i) (τ i),
      C t ∈ Positivity.Grids.closedCrossingAnnulus z (k i)) :
    ∀ i j : ι, i ≠ j → τ i < σ j ∨ τ j < σ i := by
  intro i j hij
  have hki : k i ≠ k j := fun e => hij (hk e)
  have hdisj : Disjoint (Positivity.Grids.closedCrossingAnnulus z (k i))
      (Positivity.Grids.closedCrossingAnnulus z (k j)) := by
    rcases lt_or_gt_of_ne hki with h | h
    · exact Positivity.Grids.crossing_annuli_disjoint z h
    · exact (Positivity.Grids.crossing_annuli_disjoint z h).symm
  by_cases hleft : τ i < σ j
  · exact Or.inl hleft
  right
  by_contra hright
  have hji : σ j ≤ τ i := le_of_not_gt hleft
  have hij' : σ i ≤ τ j := le_of_not_gt hright
  rcases le_total (σ i) (σ j) with hs | hs
  · have hi : C (σ j) ∈ Positivity.Grids.closedCrossingAnnulus z (k i) :=
      hclosed i (σ j) ⟨hs, hji⟩
    have hj : C (σ j) ∈ Positivity.Grids.closedCrossingAnnulus z (k j) :=
      hclosed j (σ j) ⟨le_rfl, (hseg j).le⟩
    exact (Set.disjoint_left.mp hdisj) hi hj
  · have hi : C (σ i) ∈ Positivity.Grids.closedCrossingAnnulus z (k i) :=
      hclosed i (σ i) ⟨le_rfl, (hseg i).le⟩
    have hj : C (σ i) ∈ Positivity.Grids.closedCrossingAnnulus z (k j) :=
      hclosed j (σ i) ⟨hs, hij'⟩
    exact (Set.disjoint_left.mp hdisj) hi hj

 
theorem paid_crossings_sum_le_len
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (hk : Function.Injective k)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (c : ℝ) (z : ℂ) (u : DistC)
    (C : ℝ → ℂ) (a b : ℝ) (hC : (D u).IsCurve C a b)
    (σ τ : ι → ℝ)
    (hseg : ∀ i, a ≤ σ i ∧ σ i < τ i ∧ τ i ≤ b)
    (hboundary : ∀ i,
      ((dist (C (σ i)) z = (11 / 20 : ℝ) * Positivity.Grids.radius (k i) ∧
        dist (C (τ i)) z = (4 / 5 : ℝ) * Positivity.Grids.radius (k i)) ∨
       (dist (C (σ i)) z = (4 / 5 : ℝ) * Positivity.Grids.radius (k i) ∧
        dist (C (τ i)) z = (11 / 20 : ℝ) * Positivity.Grids.radius (k i))))
    (hclosed : ∀ i, ∀ t ∈ Icc (σ i) (τ i),
      C t ∈ Positivity.Grids.closedCrossingAnnulus z (k i))
    (hpaid : ∀ i, Paid ξ Q D c z (dyadicRadius (k i)) u) :
    (∑ i : ι, ENNReal.ofReal (c *
      Positivity.Grids.radius (k i) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius (k i)) z))) ≤
        (D u).len C a b := by
  have hsep : ∀ i j : ι, i ≠ j → τ i < σ j ∨ τ j < σ i :=
    crossing_intervals_separated k hk C z σ τ (fun i => (hseg i).2.1) hclosed
  have hpiece (i : ι) :
      ENNReal.ofReal (c * Positivity.Grids.radius (k i) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius (k i)) z)) ≤
      (D u).len C (σ i) (τ i) := by
    have htime : Icc (σ i) (τ i) ⊆ Icc a b :=
      Icc_subset_Icc (hseg i).1 (hseg i).2.2
    have hCi : (D u).IsCurve C (σ i) (τ i) :=
      ⟨(hseg i).2.1.le, hC.2.mono htime⟩
    have hY : ∀ t ∈ Icc (σ i) (τ i),
        C t ∈ (collar z (dyadicRadius (k i)) : Set ℂ) :=
      fun t ht => closed_crossing_subset_collar z (k i) (hclosed i t ht)
    rcases hboundary i with ⟨hσ, hτ⟩ | ⟨hσ, hτ⟩
    · have hpay := hpaid i (C (σ i)) (crossing_inner_mem_shape z (k i) _ hσ)
        (C (τ i)) (crossing_outer_mem_shape z (k i) _ hτ)
      have hlen := (D u).internal_le_len (collar z (dyadicRadius (k i)) : Set ℂ)
        C (σ i) (τ i) hCi hY
      exact hpay.trans hlen
    · have hpay := hpaid i (C (τ i)) (crossing_inner_mem_shape z (k i) _ hτ)
        (C (σ i)) (crossing_outer_mem_shape z (k i) _ hσ)
      have hlen := internal_reverse_le_len (D u)
        (collar z (dyadicRadius (k i)) : Set ℂ) C (σ i) (τ i) hCi hY
      exact hpay.trans hlen
  calc
    (∑ i : ι, ENNReal.ofReal (c * Positivity.Grids.radius (k i) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius (k i)) z)))
        ≤ ∑ i : ι, (D u).len C (σ i) (τ i) := Finset.sum_le_sum (fun i _ => hpiece i)
    _ ≤ (D u).len C a b := by
      simpa only [LSCMetric.len, LQGMetric.MetricGeometry.curveLength] using
        (LQGMetric.DFGPS.P41.sum_curveLength_le ((D u).pt ∘ C)
        (Finset.univ : Finset ι) σ τ
        (fun i _ => (hseg i).2.1.le)
        (fun i _ j _ hij => hsep i j hij)
        a b (fun i _ => ⟨(hseg i).1, (hseg i).2.2⟩))

 
theorem trace_paid_scales_sum_le_len
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (c : ℝ) (u : DistC) (i : Fin 12)
    (C : ℝ → ℂ) (a b : ℝ) (hC : (D u).IsCurve C a b)
    (hB : ∀ t ∈ Icc a b, C t ∈ Metric.ball (0 : ℂ) 3)
    (hdiam : ∃ x ∈ C '' Icc a b, ∃ y ∈ C '' Icc a b,
      2 * (Positivity.Witnesses.witnessAnnulus i).innerRadius ≤ dist x y)
    (K : ℕ) (hK : 8 ≤ K) (z : ℂ)
    (hnear : ∃ t ∈ Icc a b, dist (C t) z ≤ Positivity.Grids.mesh K)
    (I : Finset ℕ)
    (hI : ∀ k ∈ I, K / 2 ≤ k ∧ k ≤ K)
    (hpaid : ∀ k ∈ I, Paid ξ Q D c z (dyadicRadius k) u) :
    (∑ k ∈ I, ENNReal.ofReal (c * Positivity.Grids.radius k ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius k) z))) ≤
      (D u).len C a b := by
  classical
  have hbounded : Bornology.IsBounded (C '' Icc a b) := by
    apply (Metric.isBounded_ball (x := (0 : ℂ)) (r := (3 : ℝ))).subset
    rintro w ⟨t, ht, rfl⟩
    exact hB t ht
  have hcont : ContinuousOn C (Icc a b) :=
    (D u).continuousOn_euclidean_of_bounded C hC hbounded
  have hex (j : I) : ∃ σ τ : ℝ, a ≤ σ ∧ σ < τ ∧ τ ≤ b ∧
      ((dist (C σ) z = (11 / 20 : ℝ) * Positivity.Grids.radius j.1 ∧
        dist (C τ) z = (4 / 5 : ℝ) * Positivity.Grids.radius j.1) ∨
       (dist (C σ) z = (4 / 5 : ℝ) * Positivity.Grids.radius j.1 ∧
        dist (C τ) z = (11 / 20 : ℝ) * Positivity.Grids.radius j.1)) ∧
      (∀ t ∈ Icc σ τ, C t ∈ Positivity.Grids.closedCrossingAnnulus z j.1) := by
    have hj := hI j.1 j.2
    exact trace_crossing_from_near_far C a b z K j.1 hj.2 hcont hnear
      (trace_far_point i C a b z K j.1 hK hj.1 hnear hdiam)
  choose σ τ hσ hστ hτ hboundary hclosed using hex
  have hsum := paid_crossings_sum_le_len (fun j : I => j.1)
    (fun _ _ h => Subtype.ext h) ξ Q D c z u C a b hC σ τ
    (fun j => ⟨hσ j, hστ j, hτ j⟩) hboundary hclosed
    (fun j => hpaid j.1 j.2)
  have heq :
      (∑ k ∈ I, ENNReal.ofReal (c * Positivity.Grids.radius k ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius k) z))) =
      ∑ j : I, ENNReal.ofReal (c * Positivity.Grids.radius j.1 ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius j.1) z)) := by
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
  exact heq.trans_le hsum

 
theorem trace_low_of_witness
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : Q ≤ 0)
    (D : DistC → LSCMetric) (c M : ℝ) (hc : 0 < c) (hM : 0 < M)
    (E : ℂ → ℕ → Set DistC) (u : DistC) (i : Fin 12)
    (C : ℝ → ℂ) (a b : ℝ) (hC : (D u).IsCurve C a b)
    (hB : ∀ t ∈ Icc a b, C t ∈ Metric.ball (0 : ℂ) 3)
    (hdiam : ∃ x ∈ C '' Icc a b, ∃ y ∈ C '' Icc a b,
      2 * (Positivity.Witnesses.witnessAnnulus i).innerRadius ≤ dist x y)
    (hlen : (D u).len C a b ≤ ENNReal.ofReal (M + 1))
    (K : ℕ) (hK : 8 ≤ K) (hKeven : K % 2 = 0)
    (hlarge : 4 * (M + 1) / c < ((K / 2 + 1 : ℕ) : ℝ))
    (z : ℂ)
    (hnear : ∃ t ∈ Icc a b, dist (C t) z ≤ Positivity.Grids.mesh K)
    (hgood : (3 / 4 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ) ≤
      (Positivity.Grids.scaleCount K (E z) u : ℝ))
    (hpaid : ∀ k : ℕ, u ∈ E z k → Paid ξ Q D c z (dyadicRadius k) u) :
    (((Finset.Icc (K / 2) K).filter
      (fun k => 0 ≤ circleAvg u (dyadicRadius k) z)).card : ℝ) <
      (1 / 2 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ) := by
  classical
  let I := Finset.Icc (K / 2) K
  let paid := I.filter (fun k => u ∈ E z k ∧
    0 ≤ circleAvg u (dyadicRadius k) z)
  have hI (k : ℕ) (hk : k ∈ paid) : K / 2 ≤ k ∧ k ≤ K :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
  have hcost := trace_paid_scales_sum_le_len ξ Q D c u i C a b hC hB hdiam
    K hK z hnear paid hI
    (fun k hk => hpaid k (Finset.mem_filter.mp hk).2.1)
  have hpaidNum : (paid.card : ℝ) * c ≤ M + 1 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ M + 1)).1
    calc
      ENNReal.ofReal ((paid.card : ℝ) * c) =
          (paid.card : ℝ≥0∞) * ENNReal.ofReal c := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ = ∑ _k ∈ paid, ENNReal.ofReal c := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ paid, ENNReal.ofReal (c * Positivity.Grids.radius k ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius k) z)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Positivity.Grids.paid_cost_ge_c ξ Q hQ c hc k _ (Finset.mem_filter.mp hk).2.2
      _ ≤ ENNReal.ofReal (M + 1) := hcost.trans hlen
  have hcardI : I.card = K / 2 + 1 := by
    simp only [I, Nat.card_Icc]
    omega
  have hgood' : (3 / 4 : ℝ) * I.card ≤
      ((I.filter fun k => u ∈ E z k).card : ℝ) := by
    simpa only [Positivity.Grids.scaleCount, I, hcardI] using hgood
  have hpaid' : (paid.card : ℝ) < (1 / 4 : ℝ) * I.card := by
    rw [hcardI]
    have hn : (0 : ℝ) < ((K / 2 + 1 : ℕ) : ℝ) := by positivity
    have hlarge' : 4 * (M + 1) < ((K / 2 + 1 : ℕ) : ℝ) * c :=
      (div_lt_iff₀ hc).mp hlarge
    nlinarith
  have hlow := Positivity.Grids.low_count_of_good_and_paid I
    (fun k => u ∈ E z k) (fun k => 0 ≤ circleAvg u (dyadicRadius k) z)
    hgood' (by simpa only [paid] using hpaid')
  simpa only [I, hcardI] using hlow

 
theorem trace_all_crossings
    (D : LSCMetric) (i : Fin 12)
    (C : ℝ → ℂ) (a b : ℝ) (hC : D.IsCurve C a b)
    (hB : ∀ t ∈ Icc a b, C t ∈ Metric.ball (0 : ℂ) 3)
    (hdiam : ∃ x ∈ C '' Icc a b, ∃ y ∈ C '' Icc a b,
      2 * (Positivity.Witnesses.witnessAnnulus i).innerRadius ≤ dist x y)
    (K : ℕ) (hK : 8 ≤ K) (z : ℂ)
    (hnear : ∃ t ∈ Icc a b, dist (C t) z ≤ Positivity.Grids.mesh K) :
    ∃ σ τ : {k : ℕ // k ∈ Finset.Icc (K / 2) K} → ℝ,
      (∀ j, a ≤ σ j ∧ σ j < τ j ∧ τ j ≤ b ∧
        ((dist (C (σ j)) z = (11 / 20 : ℝ) * Positivity.Grids.radius j.1 ∧
          dist (C (τ j)) z = (4 / 5 : ℝ) * Positivity.Grids.radius j.1) ∨
         (dist (C (σ j)) z = (4 / 5 : ℝ) * Positivity.Grids.radius j.1 ∧
          dist (C (τ j)) z = (11 / 20 : ℝ) * Positivity.Grids.radius j.1)) ∧
        (∀ t ∈ Icc (σ j) (τ j), C t ∈ Positivity.Grids.closedCrossingAnnulus z j.1)) ∧
      (∀ j l, j ≠ l → τ j < σ l ∨ τ l < σ j) := by
  classical
  have hbounded : Bornology.IsBounded (C '' Icc a b) := by
    apply (Metric.isBounded_ball (x := (0 : ℂ)) (r := (3 : ℝ))).subset
    rintro w ⟨t, ht, rfl⟩
    exact hB t ht
  have hcont : ContinuousOn C (Icc a b) :=
    D.continuousOn_euclidean_of_bounded C hC hbounded
  let I := Finset.Icc (K / 2) K
  have hex (j : I) : ∃ σ τ : ℝ, a ≤ σ ∧ σ < τ ∧ τ ≤ b ∧
      ((dist (C σ) z = (11 / 20 : ℝ) * Positivity.Grids.radius j.1 ∧
        dist (C τ) z = (4 / 5 : ℝ) * Positivity.Grids.radius j.1) ∨
       (dist (C σ) z = (4 / 5 : ℝ) * Positivity.Grids.radius j.1 ∧
        dist (C τ) z = (11 / 20 : ℝ) * Positivity.Grids.radius j.1)) ∧
      (∀ t ∈ Icc σ τ, C t ∈ Positivity.Grids.closedCrossingAnnulus z j.1) := by
    have hj : K / 2 ≤ j.1 ∧ j.1 ≤ K := Finset.mem_Icc.mp j.2
    exact trace_crossing_from_near_far C a b z K j.1 hj.2 hcont hnear
      (trace_far_point i C a b z K j.1 hK hj.1 hnear hdiam)
  choose σ τ hσ hστ hτ hboundary hclosed using hex
  refine ⟨σ, τ, (fun j => ⟨hσ j, hστ j, hτ j, hboundary j, hclosed j⟩), ?_⟩
  exact crossing_intervals_separated (fun j : I => j.1)
    (fun _ _ h => Subtype.ext h) C z σ τ hστ hclosed

 
def gridGood (E : ℂ → ℕ → Set DistC) (K : ℕ) : Set DistC :=
  {u | ∀ z ∈ Positivity.Grids.grid K,
    (3 / 4 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ) ≤ (Positivity.Grids.scaleCount K (E z) u : ℝ)}

 
def paidScales (E : ℂ → ℕ → Set DistC) (u : DistC)
    (z : ℂ) (K : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (K / 2) K).filter
    (fun k => u ∈ E z k ∧ 0 ≤ circleAvg u (dyadicRadius k) z)

 
theorem ax13_trace_to_low
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : Q ≤ 0)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) :
    ∃ (p c₀ c M : ℝ) (E : ℂ → ℕ → Set DistC) (V : Set DistC),
      0 < p ∧ p < 1 ∧ 0 < c₀ ∧ 0 < c ∧ 0 < M ∧
      4 * Real.exp (-2) < (1 : ℝ) ∧
      MeasurableSet V ∧ ENNReal.ofReal (7 / 8 : ℝ) ≤ μ V ∧
      (∀ K : ℕ, K % 2 = 0 →
        μ (gridGood E K)ᶜ ≤ ENNReal.ofReal
          (2 ^ 26 * c₀ * Real.exp (-4) * (4 * Real.exp (-2)) ^ K)) ∧
      (∀ᵐ u ∂μ, u ∈ V → ∀ i : Fin 12,
        ∃ (C : ℝ → ℂ) (a b : ℝ),
          (D u).IsCurve C a b ∧
          (∀ t ∈ Icc a b, C t ∈ (Positivity.Witnesses.witnessAnnulus i).toSet) ∧
          (∀ t ∈ Icc a b, C t ∈ Metric.ball (0 : ℂ) 3) ∧
          Disconnects (C '' Icc a b)
            (Positivity.Witnesses.witnessAnnulus i).innerBoundary
            (Positivity.Witnesses.witnessAnnulus i).outerBoundary ∧
          (D u).len C a b ≤ ENNReal.ofReal (M + 1) ∧
          IsCompact (C '' Icc a b) ∧ IsPathConnected (C '' Icc a b) ∧
          (∃ x ∈ C '' Icc a b, ∃ y ∈ C '' Icc a b,
            2 * (Positivity.Witnesses.witnessAnnulus i).innerRadius ≤ dist x y) ∧
          (∀ (K : ℕ), K % 2 = 0 → 8 ≤ K →
            4 * (M + 1) / c < ((K / 2 + 1 : ℕ) : ℝ) →
            u ∈ gridGood E K → ∀ z ∈ Positivity.Grids.grid K,
            (∃ t ∈ Icc a b, dist (C t) z ≤ Positivity.Grids.mesh K) →
              ∃ σ τ : {k : ℕ // k ∈ Finset.Icc (K / 2) K} → ℝ,
                (∀ j, a ≤ σ j ∧ σ j < τ j ∧ τ j ≤ b ∧
                  ((dist (C (σ j)) z = (11 / 20 : ℝ) * Positivity.Grids.radius j.1 ∧
                    dist (C (τ j)) z = (4 / 5 : ℝ) * Positivity.Grids.radius j.1) ∨
                   (dist (C (σ j)) z = (4 / 5 : ℝ) * Positivity.Grids.radius j.1 ∧
                    dist (C (τ j)) z = (11 / 20 : ℝ) * Positivity.Grids.radius j.1)) ∧
                  (∀ t ∈ Icc (σ j) (τ j),
                    C t ∈ Positivity.Grids.closedCrossingAnnulus z j.1)) ∧
                (∀ j l, j ≠ l → τ j < σ l ∨ τ l < σ j) ∧
                (∑ k ∈ paidScales E u z K,
                  ENNReal.ofReal (c * Positivity.Grids.radius k ^ ((ξ : ℝ) * Q) *
                    Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius k) z))) ≤
                  ENNReal.ofReal (M + 1) ∧
                (((Finset.Icc (K / 2) K).filter
                  (fun k => 0 ≤ circleAvg u (dyadicRadius k) z)).card : ℝ) <
                  (1 / 2 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ))) := by
  classical
  obtain ⟨p, c₀, c, E, hp, hp1, hc₀, hc, hbase, _hstrict, _hprob, hpaid, hgrid⟩ :=
    ax11_grid_iteration μ hμ ξ Q D hD
  obtain ⟨M, V, hM, hVm, hVprob, hVw⟩ :=
    Positivity.Witnesses.ax12_canonical_witnesses μ hμ ξ Q D hD
  refine ⟨p, c₀, c, M, E, V, hp, hp1, hc₀, hc, hM, hbase, hVm, hVprob, ?_, ?_⟩
  · intro K hK
    exact hgrid K hK
  · filter_upwards [hpaid, hVw] with u hu hv hVu i
    obtain ⟨C, a, b, hC, hA, hB, hdisc, hlen, hcompact, hpc, hdiam⟩ := hv hVu i
    refine ⟨C, a, b, hC, hA, hB, hdisc, hlen, hcompact, hpc, hdiam, ?_⟩
    intro K hKeven hK hlarge hU z hz hnear
    obtain ⟨σ, τ, hcross, hsep⟩ :=
      trace_all_crossings (D u) i C a b hC hB hdiam K hK z hnear
    let J := paidScales E u z K
    have hJall (j : J) : j.1 ∈ Finset.Icc (K / 2) K :=
      (Finset.mem_filter.mp j.2).1
    let σJ : J → ℝ := fun j => σ ⟨j.1, hJall j⟩
    let τJ : J → ℝ := fun j => τ ⟨j.1, hJall j⟩
    have hsumJ :
        (∑ j : J, ENNReal.ofReal (c * Positivity.Grids.radius j.1 ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius j.1) z))) ≤
        (D u).len C a b := by
      apply paid_crossings_sum_le_len (fun j : J => j.1)
        (fun _ _ h => Subtype.ext h) ξ Q D c z u C a b hC σJ τJ
      · intro j
        exact ⟨(hcross ⟨j.1, hJall j⟩).1,
          (hcross ⟨j.1, hJall j⟩).2.1,
          (hcross ⟨j.1, hJall j⟩).2.2.1⟩
      · intro j
        exact (hcross ⟨j.1, hJall j⟩).2.2.2.1
      · intro j t ht
        exact (hcross ⟨j.1, hJall j⟩).2.2.2.2 t ht
      · intro j
        exact hu K z hz j.1 (Finset.mem_filter.mp j.2).2.1
    have hsumEq :
        (∑ k ∈ J, ENNReal.ofReal (c * Positivity.Grids.radius k ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius k) z))) =
        ∑ j : J, ENNReal.ofReal (c * Positivity.Grids.radius j.1 ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius j.1) z)) := by
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
    have hsum : (∑ k ∈ J,
        ENNReal.ofReal (c * Positivity.Grids.radius k ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg u (dyadicRadius k) z))) ≤
        ENNReal.ofReal (M + 1) :=
      hsumEq.trans_le (hsumJ.trans hlen)
    have hlow := trace_low_of_witness ξ Q hQ D c M hc hM E u i
      C a b hC hB hdiam hlen K hK hKeven hlarge z hnear (hU z hz)
      (fun k hk => hu K z hz k hk)
    exact ⟨σ, τ, hcross, hsep, hsum, hlow⟩









end SupercriticalLQGUniqueness.Uniqueness.Positivity.GoodScales
