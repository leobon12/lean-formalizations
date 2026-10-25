import SupercriticalLQGUniqueness.B2.PfeWeyl.W2Recovery
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaBridge
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaFiniteEventual

 

















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

open PfeAxioms

 

theorem acrossDist_le_len_of_crossing_rev (E : LSCMetric) (A : EuclideanAnnulus)
    {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hPc : ContinuousOn P (Icc a b))
    (ha : A.outerRadius ≤ dist (P a) A.center)
    (hb : dist (P b) A.center ≤ A.innerRadius) :
    acrossDist E A ≤ E.len P a b := by
  have hf : ContinuousOn (fun u => dist (P u) A.center) (Icc a b) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  obtain ⟨s, t, has, hst, htb, hs, ht, _⟩ :=
    LQGMetric.RectCross.exists_sub_crossing' hab hf
      A.innerRadius_lt_outerRadius.le ha hb
  have hcross : acrossDist E A ≤ E (P t, P s) := by
    unfold acrossDist
    exact iInf_le_of_le (P t) (iInf_le_of_le
      (by simpa only [EuclideanAnnulus.innerBoundary, Metric.mem_sphere] using ht)
      (iInf_le_of_le (P s) (iInf_le_of_le
        (by simpa only [EuclideanAnnulus.outerBoundary, Metric.mem_sphere] using hs)
        le_rfl)))
  have hsym : E (P t, P s) = E (P s, P t) := E.isExtMetric.2.2.1 _ _
  rw [hsym] at hcross
  exact hcross.trans ((LSCMetric.apply_le_len E P hst).trans
    (len_mono_Icc E P has htb))

 


theorem curve_mem_ball_of_len_lt_acrossDist_rev (E : LSCMetric) (A : EuclideanAnnulus)
    {P : ℝ → ℂ} {a b : ℝ} (hPc : ContinuousOn P (Icc a b))
    (hb : dist (P b) A.center ≤ A.innerRadius)
    (hlen : E.len P a b < acrossDist E A) :
    ∀ t ∈ Icc a b, P t ∈ Metric.ball A.center A.outerRadius := by
  intro t ht
  by_contra hout
  have hfar : A.outerRadius ≤ dist (P t) A.center := by
    simpa only [Metric.mem_ball, not_lt] using hout
  have hcross := acrossDist_le_len_of_crossing_rev E A ht.2
    (hPc.mono (Icc_subset_Icc ht.1 le_rfl)) hfar hb
  exact (not_lt_of_ge (hcross.trans (len_mono_Icc E P ht.1 le_rfl))) hlen

 
theorem exists_dedup_chain_idx {α : Type*} (v : ℕ → α) (N : ℕ) :
    ∃ (N' : ℕ) (v' : ℕ → α), N' ≤ N ∧ v' 0 = v 0 ∧ v' N' = v N ∧
      (∀ j < N', v' j ≠ v' (j + 1)) ∧
      (∀ j < N', ∃ i < N, v' j = v i ∧ v' (j + 1) = v (i + 1)) ∧
      (∀ j ≤ N', ∃ i ≤ N, v' j = v i ∧ (0 < j → 0 < i) ∧ (j < N' → i < N)) ∧
      ∀ c : α → α → ℝ≥0∞,
        (∑ j ∈ Finset.range N', c (v' j) (v' (j + 1))) ≤
          ∑ i ∈ Finset.range N, c (v i) (v (i + 1)) := by
  induction N with
  | zero =>
    refine ⟨0, v, le_rfl, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => ?_, fun c => le_rfl⟩
    have hj0 : j = 0 := Nat.le_zero.1 hj
    subst hj0
    exact ⟨0, le_rfl, rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd h (lt_irrefl 0)⟩
  | succ N ih =>
    obtain ⟨N', v', hN', h0, hlast, hdist, hpair, hidx, hsum⟩ := ih
    by_cases heq : v (N + 1) = v N
    · refine ⟨N', v', hN'.trans (Nat.le_succ N), h0, hlast.trans heq.symm, hdist,
        fun j hj => ?_, fun j hj => ?_, fun c => ?_⟩
      · obtain ⟨i, hi, h1, h2⟩ := hpair j hj
        exact ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩
      · obtain ⟨i, hi, h1, h2, h3⟩ := hidx j hj
        exact ⟨i, hi.trans (Nat.le_succ N), h1, h2,
          fun hjN => (h3 hjN).trans (Nat.lt_succ_self N)⟩
      · rw [Finset.sum_range_succ]
        exact (hsum c).trans le_self_add
    · let w : ℕ → α := fun j => if j = N' + 1 then v (N + 1) else v' j
      have hw : ∀ j ≤ N', w j = v' j := fun j hj => by
        simp [w, show j ≠ N' + 1 by omega]
      have hwlast : w (N' + 1) = v (N + 1) := by simp [w]
      refine ⟨N' + 1, w, Nat.succ_le_succ hN', ?_, hwlast, ?_, ?_, ?_, fun c => ?_⟩
      · rw [hw 0 (Nat.zero_le _), h0]
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · rw [hw j hj.le, hw (j + 1) hj]
          exact hdist j hj
        · subst hj
          rw [hw j le_rfl, hwlast, hlast]
          exact fun h => heq h.symm
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · obtain ⟨i, hi, h1, h2⟩ := hpair j hj
          refine ⟨i, Nat.lt_succ_of_lt hi, ?_, ?_⟩
          · rw [hw j hj.le, h1]
          · rw [hw (j + 1) hj, h2]
        · subst hj
          exact ⟨N, Nat.lt_succ_self N, by rw [hw j le_rfl, hlast], hwlast⟩
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_iff.2 hj) with hj' | hj'
        · obtain ⟨i, hi, h1, h2, -⟩ := hidx j (Nat.lt_succ_iff.1 hj')
          exact ⟨i, hi.trans (Nat.le_succ N), by rw [hw j (Nat.lt_succ_iff.1 hj'), h1], h2,
            fun _ => Nat.lt_succ_of_le hi⟩
        · subst hj'
          exact ⟨N + 1, le_rfl, hwlast, fun _ => Nat.succ_pos N,
            fun h => absurd h (lt_irrefl _)⟩
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hrest : (∑ j ∈ Finset.range N', c (w j) (w (j + 1))) =
            ∑ j ∈ Finset.range N', c (v' j) (v' (j + 1)) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          rw [hw j hj'.le, hw (j + 1) hj']
        rw [hrest, hw N' le_rfl, hwlast, hlast]
        exact add_le_add (hsum c) le_rfl

private theorem weightedChain_eq' {X : Type*} [PseudoEMetricSpace X]
    (weight : X → ℝ) (P : ℝ → X) (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      HigherDimLQGMetric.weightedLength weight P (t j) (t (j + 1))) =
      HigherDimLQGMetric.weightedLength weight P (t 0) (t N) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty,
      HigherDimLQGMetric.weightedLength_self]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact HigherDimLQGMetric.weightedLength_add
        (ht (Nat.zero_le N)) (ht (Nat.le_succ N))

 


theorem weighted_chain_le_weyl_cost_sub
    (D : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    {P : ℝ → ℂ} {L : ℝ}
    (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ)
    (ht0 : 0 ≤ t 0) (htN : t N ≤ L) (θ : ℝ)
    (hfield : ∀ j < N, ∀ s ∈ Icc (t j) (t (j + 1)),
      f (P (t j)) - θ ≤ f (P s)) :
    (∑ j ∈ Finset.range N,
        chainWeightMinus ξ f θ (P (t j)) * D (P (t j), P (t (j + 1)))) ≤
      ∫⁻ s in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P s))) := by
  let weight : D.Space → ℝ := fun x => Real.exp (ξ * f (euclidForget D x))
  have hweight : Continuous weight :=
    Real.continuous_exp.comp
      (continuous_const.mul (f.continuous.comp hforget))
  have hcweight : ContinuousOn (fun s => weight ((D.pt ∘ P) s)) (Icc 0 L) :=
    hweight.continuousOn.comp hP.2 (fun _ _ => Set.mem_univ _)
  have hpiece (j : ℕ) (hj : j < N) :
      chainWeightMinus ξ f θ (P (t j)) * D (P (t j), P (t (j + 1))) ≤
        HigherDimLQGMetric.weightedLength weight (D.pt ∘ P)
          (t j) (t (j + 1)) := by
    have htime : t j ≤ t (j + 1) := ht (Nat.le_succ j)
    have hdist : D (P (t j), P (t (j + 1))) ≤
        LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) (t j) (t (j + 1)) :=
      LQGMetric.MetricGeometry.edist_le_curveLength (D.pt ∘ P) htime
    have hlo : ∀ s ∈ Icc (t j) (t (j + 1)),
        Real.exp (ξ * (f (P (t j)) - θ)) ≤ weight ((D.pt ∘ P) s) := by
      intro s hs
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hfield j hj s hs) hξ)
    have hlen := HigherDimLQGMetric.ofReal_mul_curveLength_le_weightedLength
      (w := weight) (P := D.pt ∘ P) htime hlo
    exact (mul_le_mul' le_rfl hdist).trans hlen
  have h0N : t 0 ≤ t N := ht (Nat.zero_le N)
  calc
    _ ≤ ∑ j ∈ Finset.range N,
          HigherDimLQGMetric.weightedLength weight (D.pt ∘ P)
            (t j) (t (j + 1)) :=
      Finset.sum_le_sum (fun j hj => hpiece j (Finset.mem_range.mp hj))
    _ = HigherDimLQGMetric.weightedLength weight (D.pt ∘ P) (t 0) (t N) :=
      weightedChain_eq' weight (D.pt ∘ P) t ht N
    _ ≤ HigherDimLQGMetric.weightedLength weight (D.pt ∘ P) 0 L := by
      rw [← HigherDimLQGMetric.weightedLength_add ht0 (h0N.trans htN),
        ← HigherDimLQGMetric.weightedLength_add h0N htN]
      exact le_self_add.trans le_add_self
    _ = _ := by
      rw [HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn hP.1 hu hcweight]
      rfl

 
theorem isRationalCircle_innerBoundary {A : EuclideanAnnulus}
    (hA : IsRationalDoubleAnnulus A) : B2.Iface.IsRationalCircle A.innerBoundary := by
  obtain ⟨x, y, r, hr, hc, hin, -⟩ := hA
  exact ⟨x, y, r, hr.le, by rw [EuclideanAnnulus.innerBoundary, hc, hin]⟩

end SupercriticalLQGUniqueness.B2.PfeWeyl
