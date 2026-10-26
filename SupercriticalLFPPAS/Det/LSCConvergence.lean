import Mathlib
import SupercriticalLQGUniqueness.Frozen.LSCTendsto

/-! Deterministic consequences of the frozen lower-semicontinuous convergence criterion. -/

set_option autoImplicit false
noncomputable section

namespace SupercriticalLFPPAS

open Filter Topology Set

/-- The infimum of an extended-real function over the open metric ball of radius `η`. -/
noncomputable def d1Near {α : Type*} [PseudoMetricSpace α]
    (g : α → EReal) (η : ℝ) (p : α) : EReal :=
  ⨅ q : α, ⨅ (_ : dist q p < η), g q

/-- Any point in the defining ball bounds the neighborhood infimum from above. -/
theorem d1Near_le_of_dist {α : Type*} [PseudoMetricSpace α]
    (g : α → EReal) {η : ℝ} {p q : α} (h : dist q p < η) :
    d1Near g η p ≤ g q := by
  unfold d1Near
  exact (iInf_le _ q).trans (iInf_le _ h)

/-- The center itself is in every positive-radius neighborhood. -/
theorem d1Near_le_center {α : Type*} [PseudoMetricSpace α]
    (g : α → EReal) {η : ℝ} {p : α} (hη : 0 < η) :
    d1Near g η p ≤ g p := by
  apply d1Near_le_of_dist
  simpa using hη

/-- Insert a convergent subsequence into a sequence, using a fixed value at indices outside
the subsequence. -/
noncomputable def d1SparseSequence {α : Type*}
    (φ : ℕ → ℕ) (x : ℕ → α) (x₀ : α) (n : ℕ) : α := by
  classical
  exact if h : ∃ k, φ k = n then x (Classical.choose h) else x₀

/-- A sequence obtained by sparsely inserting a convergent subsequence still converges to the
same limit, provided the indices are strictly increasing. -/
theorem d1SparseSequence_tendsto {α : Type*} [PseudoMetricSpace α]
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x : ℕ → α) (x₀ : α)
    (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (d1SparseSequence φ x x₀) atTop (𝓝 x₀) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Metric.tendsto_nhds.1 hx ε hε)
  refine Filter.eventually_atTop.2 ⟨φ N, ?_⟩
  intro n hn
  classical
  by_cases h : ∃ k, φ k = n
  · let k := Classical.choose h
    have hkn : φ k = n := Classical.choose_spec h
    have hNk : N ≤ k := by
      by_contra hlt
      have hkN : k < N := Nat.lt_of_not_ge hlt
      have hφkn : φ k < φ N := hφ hkN
      omega
    have hxk : dist (x k) x₀ < ε := hN k hNk
    have hs : d1SparseSequence φ x x₀ n = x k := by
      simp [d1SparseSequence, h, k]
    simpa [hs] using hxk
  · simpa [d1SparseSequence, h] using hε

/-- At one of the selected indices, the sparse sequence has the prescribed value. -/
theorem d1SparseSequence_at {α : Type*} (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (x : ℕ → α) (x₀ : α) (k : ℕ) :
    d1SparseSequence φ x x₀ (φ k) = x k := by
  classical
  unfold d1SparseSequence
  split
  · rename_i h
    have hk : Classical.choose h = k := by
      apply hφ
      exact (Classical.choose_spec h).trans rfl
    simp [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

/-- Local lower control supplied by the liminf half of `LSCTendsto`. -/
theorem d1_local_reverse_near {F : ℕ → ℂ × ℂ → EReal} {f : ℂ × ℂ → EReal}
    (hconv : SupercriticalLQGUniqueness.LSCTendsto F f)
    (hFnonneg : ∀ n p, 0 ≤ F n p) (hfnonneg : ∀ p, 0 ≤ f p)
    (p : ℂ × ℂ) {η ν M : ℝ} (hη : 0 < η) (hν : 0 < ν) :
    ∃ ρ, 0 < ρ ∧ ∃ N, ∀ n ≥ N, ∀ q, dist q p < ρ → F n q ≤ M →
      d1Near f η q ≤ F n q + (ν : EReal) := by
  classical
  by_contra hno
  have hbad : ∀ (k : ℕ) N, ∃ n > N, ∃ q : ℂ × ℂ,
      dist q p < min (η / 2) (1 / (k + 1 : ℝ)) ∧
      F n q ≤ M ∧ ¬ d1Near f η q ≤ F n q + (ν : EReal) := by
    intro k N
    let ρ : ℝ := min (η / 2) (1 / (k + 1 : ℝ))
    have hρ : 0 < ρ := by
      dsimp [ρ]
      positivity
    by_contra h
    push Not at h
    apply hno
    refine ⟨ρ, hρ, N + 1, ?_⟩
    intro n hn q hq hqM
    exact h n (by omega) q hq hqM
  let φ : ℕ → ℕ := Nat.rec (Classical.choose (hbad 0 0))
    (fun k prev => Classical.choose (hbad (k + 1) prev))
  have hφstep : ∀ k, φ k < φ (k + 1) := by
    intro k
    simp only [φ]
    exact (Classical.choose_spec (hbad (k + 1) (φ k))).1
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ hφstep
  have hφbad (k : ℕ) : ∃ q : ℂ × ℂ,
      dist q p < min (η / 2) (1 / (k + 1 : ℝ)) ∧
      F (φ k) q ≤ M ∧ ¬ d1Near f η q ≤ F (φ k) q + (ν : EReal) := by
    induction k with
    | zero =>
        simpa [φ] using (Classical.choose_spec (hbad 0 0)).2
    | succ k ih =>
        simpa [φ] using (Classical.choose_spec (hbad (k + 1) (φ k))).2
  let q : ℕ → ℂ × ℂ := fun k => Classical.choose (hφbad k)
  have hqprops (k : ℕ) :
      dist (q k) p < min (η / 2) (1 / (k + 1 : ℝ)) ∧
      F (φ k) (q k) ≤ M ∧
      ¬ d1Near f η (q k) ≤ F (φ k) (q k) + (ν : EReal) :=
    Classical.choose_spec (hφbad k)
  have hradius : Tendsto (fun k : ℕ => (1 / (k + 1 : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hqTendsto : Tendsto q atTop (𝓝 p) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (Metric.tendsto_nhds.1 hradius ε hε)
    filter_upwards [Filter.eventually_atTop.2 ⟨K, fun k hk => hK k hk⟩] with k hk
    have hkR : 1 / (k + 1 : ℝ) < ε := by
      simpa [Real.dist_eq, abs_of_pos (by positivity : 0 < (k : ℝ) + 1)] using hk
    exact ((hqprops k).1.trans_le (min_le_right _ _)).trans hkR
  have hqSparse : Tendsto (d1SparseSequence φ q p) atTop (𝓝 p) :=
    d1SparseSequence_tendsto φ hφ q p hqTendsto
  have hliminf : f p ≤ liminf (fun n => F n (d1SparseSequence φ q p n)) atTop :=
    hconv.1 (d1SparseSequence φ q p) p hqSparse
  let v : ℕ → EReal := fun n => F n (d1SparseSequence φ q p n)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hvBound : IsBoundedUnder (· ≥ ·) atTop v :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n =>
      hFnonneg n (d1SparseSequence φ q p n))
  by_cases htop : f p = ⊤
  · have hev : ∀ᶠ n in atTop, (M : EReal) < v n := by
      have htoplim : (⊤ : EReal) ≤ liminf v atTop := by simpa [v, htop] using hliminf
      exact eventually_lt_of_lt_liminf ((EReal.coe_lt_top M).trans_le htoplim) hvBound
    have hevSub := hφtop.eventually hev
    obtain ⟨k, hk⟩ := hevSub.exists
    have hvalue : v (φ k) = F (φ k) (q k) := by
      simp [v, d1SparseSequence_at φ hφ.injective q p k]
    have hle : v (φ k) ≤ M := by
      rw [hvalue]
      exact hqprops k |>.2.1
    exact (not_lt_of_ge hle) (by simpa using hk)
  · have hbot : f p ≠ ⊥ := by
      intro h
      have hzero : (0 : EReal) ≤ ⊥ := by simpa [h] using hfnonneg p
      exact (not_le_of_gt (show (⊥ : EReal) < 0 by simp)) hzero
    have hfpEq : ((f p).toReal : EReal) = f p := EReal.coe_toReal htop hbot
    let b : EReal := (((f p).toReal - ν / 2 : ℝ) : EReal)
    have hb : b < f p := by
      calc
        b = (((f p).toReal - ν / 2 : ℝ) : EReal) := rfl
        _ < ((f p).toReal : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
        _ = f p := hfpEq
    have hev : ∀ᶠ n in atTop, b < v n :=
      eventually_lt_of_lt_liminf (lt_of_lt_of_le hb hliminf) hvBound
    have hevSub := hφtop.eventually hev
    have hselected : ∀ k, F (φ k) (q k) < b := by
      intro k
      have hqp : dist p (q k) < η := by
        rw [dist_comm]
        calc
          dist (q k) p < min (η / 2) (1 / (k + 1 : ℝ)) := (hqprops k).1
          _ ≤ η / 2 := min_le_left _ _
          _ < η := by linarith
      have hnear : d1Near f η (q k) ≤ f p := d1Near_le_of_dist f hqp
      have hbadval : F (φ k) (q k) + (ν : EReal) < f p :=
        (lt_of_not_ge (hqprops k).2.2).trans_le hnear
      have hFle := (hqprops k).2.1
      have hFtop : F (φ k) (q k) ≠ ⊤ := by
        intro htopF
        rw [htopF] at hFle
        simp at hFle
      have hFbot : F (φ k) (q k) ≠ ⊥ := by
        intro hbotF
        have hnonneg := hFnonneg (φ k) (q k)
        simp [hbotF] at hnonneg
      have hFEq : ((F (φ k) (q k)).toReal : EReal) = F (φ k) (q k) :=
        EReal.coe_toReal hFtop hFbot
      have hbadReal : (F (φ k) (q k)).toReal + ν < (f p).toReal := by
        apply EReal.coe_lt_coe_iff.mp
        simpa [hFEq, hfpEq, EReal.coe_add] using hbadval
      have hselectedCo : ((F (φ k) (q k)).toReal : EReal) < b := by
        change ((F (φ k) (q k)).toReal : EReal) <
          (((f p).toReal - ν / 2 : ℝ) : EReal)
        apply EReal.coe_lt_coe_iff.mpr
        linarith
      simpa [hFEq, b] using hselectedCo
    obtain ⟨k, hk⟩ := hevSub.exists
    have hvalue : v (φ k) = F (φ k) (q k) := by
      simp [v, d1SparseSequence_at φ hφ.injective q p k]
    rw [hvalue] at hk
    exact (not_lt_of_ge (le_of_lt (hselected k))) hk

/-- Recovery sequences give local upper control of the neighborhood infimum. -/
theorem d1_local_forward_near {F : ℕ → ℂ × ℂ → EReal} {f : ℂ × ℂ → EReal}
    (hconv : SupercriticalLQGUniqueness.LSCTendsto F f)
    (hfnonneg : ∀ p, 0 ≤ f p)
    (p : ℂ × ℂ) {M η ν : ℝ} (hp : f p ≤ M)
    (hη : 0 < η) (hν : 0 < ν) :
    ∃ N, ∀ n ≥ N, ∀ q, dist q p < η / 2 →
      (f p - (ν / 2 : ℝ) : EReal) < f q → f q ≤ M →
      d1Near (F n) η q ≤ f q + (ν : EReal) := by
  classical
  obtain ⟨x, hx, hFx⟩ := hconv.2 p
  have hpTop : f p ≠ ⊤ := by
    intro h
    rw [h] at hp
    exact (not_le_of_gt (EReal.coe_lt_top M)) hp
  have hpBot : f p ≠ ⊥ := by
    intro h
    have hzero : (0 : EReal) ≤ ⊥ := by simpa [h] using hfnonneg p
    exact (not_le_of_gt (show (⊥ : EReal) < 0 by simp)) hzero
  have hpEq : ((f p).toReal : EReal) = f p := EReal.coe_toReal hpTop hpBot
  have hthreshold : f p < f p + ((ν / 2 : ℝ) : EReal) := by
    calc
      f p = ((f p).toReal : EReal) := hpEq.symm
      _ < (((f p).toReal + ν / 2 : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr (by linarith)
      _ = f p + ((ν / 2 : ℝ) : EReal) := by rw [← hpEq]; simp
  have hpoint : ∀ᶠ n in atTop, dist (x n) p < η / 2 :=
    hx.eventually (Metric.ball_mem_nhds p (by positivity))
  have hvalue : ∀ᶠ n in atTop, F n (x n) < f p + ((ν / 2 : ℝ) : EReal) :=
    hFx.eventually (isOpen_Iio.mem_nhds hthreshold)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hpoint.and hvalue)
  refine ⟨N, ?_⟩
  intro n hn q hqp hqLower hqM
  have hdist : dist (x n) q < η := by
    calc
      dist (x n) q ≤ dist (x n) p + dist p q := dist_triangle _ _ _
      _ < η / 2 + η / 2 := add_lt_add (hN n hn).1 (by simpa [dist_comm] using hqp)
      _ = η := by ring
  have hqTop : f q ≠ ⊤ := by
    intro h
    rw [h] at hqM
    exact (not_le_of_gt (EReal.coe_lt_top M)) hqM
  have hqBot : f q ≠ ⊥ := by
    intro h
    have hzero : (0 : EReal) ≤ ⊥ := by simpa [h] using hfnonneg q
    exact (not_le_of_gt (show (⊥ : EReal) < 0 by simp)) hzero
  have hqEq : ((f q).toReal : EReal) = f q := EReal.coe_toReal hqTop hqBot
  have hqLowerCoe : (((f p).toReal - ν / 2 : ℝ) : EReal) < ((f q).toReal : EReal) := by
    calc
      (((f p).toReal - ν / 2 : ℝ) : EReal) = f p - ((ν / 2 : ℝ) : EReal) := by
        rw [← hpEq]
        simp
      _ < f q := hqLower
      _ = ((f q).toReal : EReal) := hqEq.symm
  have hqLowerReal : (f p).toReal - ν / 2 < (f q).toReal :=
    EReal.coe_lt_coe_iff.mp hqLowerCoe
  have hthreshold2 : f p + ((ν / 2 : ℝ) : EReal) < f q + (ν : EReal) := by
    calc
      f p + ((ν / 2 : ℝ) : EReal) = (((f p).toReal + ν / 2 : ℝ) : EReal) := by
        rw [← hpEq]
        simp
      _ < (((f q).toReal + ν : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr (by linarith [hqLowerReal])
      _ = f q + (ν : EReal) := by rw [← EReal.coe_toReal hqTop hqBot]; simp
  exact (calc
    d1Near (F n) η q ≤ F n (x n) := d1Near_le_of_dist (F n) hdist
    _ < f p + ((ν / 2 : ℝ) : EReal) := (hN n hn).2
    _ < f q + (ν : EReal) := hthreshold2).le

/-- A finite nonnegative extended real lies strictly above itself minus a positive real. -/
theorem d1_sub_real_lt_self {z : EReal} {M ν : ℝ}
    (hz : 0 ≤ z) (hzM : z ≤ M) (hν : 0 < ν) :
    z - ((ν / 2 : ℝ) : EReal) < z := by
  have htop : z ≠ ⊤ := by
    intro h
    rw [h] at hzM
    exact (not_le_of_gt (EReal.coe_lt_top M)) hzM
  have hbot : z ≠ ⊥ := by
    intro h
    have hzero : (0 : EReal) ≤ ⊥ := by simpa [h] using hz
    exact (not_le_of_gt (show (⊥ : EReal) < 0 by simp)) hzero
  have hzEq : (z.toReal : EReal) = z := EReal.coe_toReal htop hbot
  calc
    z - ((ν / 2 : ℝ) : EReal) = (((z.toReal - ν / 2 : ℝ) : EReal)) := by
      rw [← hzEq]
      simp
    _ < (z.toReal : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
    _ = z := hzEq

/-- Compact-uniform neighborhood estimates for convergence in the frozen lsc topology.
The max product metric on `ℂ × ℂ` is the metric used by the source. -/
theorem d1_lsc_convergence_neighborhoods
    (F : ℕ → ℂ × ℂ → EReal) (f : ℂ × ℂ → EReal)
    (_hFLsc : ∀ n, LowerSemicontinuous (F n)) (hfLsc : LowerSemicontinuous f)
    (hFnonneg : ∀ n p, 0 ≤ F n p) (hfnonneg : ∀ p, 0 ≤ f p)
    (hconv : SupercriticalLQGUniqueness.LSCTendsto F f)
    (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (M η ν : ℝ) (hη : 0 < η) (hν : 0 < ν) :
    ∀ᶠ n in atTop, ∀ p ∈ K,
      (f p ≤ M → d1Near (F n) η p ≤ f p + (ν : EReal)) ∧
      (F n p ≤ M → d1Near f η p ≤ F n p + (ν : EReal)) := by
  classical
  by_cases hKempty : K = ∅
  · refine Filter.eventually_atTop.2 ⟨0, ?_⟩
    intro n hn p hpK
    simp [hKempty] at hpK
  let revWitness (p : ℂ × ℂ) :=
    d1_local_reverse_near (M := M) hconv hFnonneg hfnonneg p hη hν
  let ρ : (ℂ × ℂ) → ℝ := fun p => Classical.choose (revWitness p)
  have hρ (p : ℂ × ℂ) : 0 < ρ p := (Classical.choose_spec (revWitness p)).1
  let revTail (p : ℂ × ℂ) := (Classical.choose_spec (revWitness p)).2
  let Nrev (p : ℂ × ℂ) : ℕ := Classical.choose (revTail p)
  have hrev (p : ℂ × ℂ) : ∀ n ≥ Nrev p, ∀ q, dist q p < ρ p → F n q ≤ M →
      d1Near f η q ≤ F n q + (ν : EReal) := Classical.choose_spec (revTail p)
  let Nfwd (p : ℂ × ℂ) : ℕ :=
    if h : f p ≤ M then Classical.choose (d1_local_forward_near hconv hfnonneg p h hη hν)
    else 0
  have hfwd (p : ℂ × ℂ) (hp : f p ≤ M) :
      ∀ n ≥ Nfwd p, ∀ q, dist q p < η / 2 →
        (f p - (ν / 2 : ℝ) : EReal) < f q → f q ≤ M →
        d1Near (F n) η q ≤ f q + (ν : EReal) := by
    dsimp [Nfwd]
    rw [dif_pos hp]
    exact Classical.choose_spec (d1_local_forward_near hconv hfnonneg p hp hη hν)
  let U : (ℂ × ℂ) → Set (ℂ × ℂ) := fun p =>
    if hp : f p ≤ M then
      Metric.ball p (min (ρ p) (η / 2)) ∩
        f ⁻¹' Set.Ioi (f p - (ν / 2 : ℝ) : EReal)
    else
      Metric.ball p (ρ p) ∩ f ⁻¹' Set.Ioi (M : EReal)
  have UeqLow (p : ℂ × ℂ) (hp : f p ≤ M) :
      U p = Metric.ball p (min (ρ p) (η / 2)) ∩
        f ⁻¹' Set.Ioi (f p - (ν / 2 : ℝ) : EReal) := by
    simp [U, hp]
  have UeqHigh (p : ℂ × ℂ) (hp : ¬ f p ≤ M) :
      U p = Metric.ball p (ρ p) ∩ f ⁻¹' Set.Ioi (M : EReal) := by
    simp [U, hp]
  have hUopen (p : ℂ × ℂ) : IsOpen (U p) := by
    by_cases hp : f p ≤ M
    · rw [UeqLow p hp]
      exact IsOpen.inter Metric.isOpen_ball (hfLsc.isOpen_preimage (f p - (ν / 2 : ℝ) : EReal))
    · rw [UeqHigh p hp]
      exact IsOpen.inter Metric.isOpen_ball (hfLsc.isOpen_preimage (M : EReal))
  have hUcover : K ⊆ ⋃ p, U p := by
    intro p hpK
    by_cases hp : f p ≤ M
    · apply mem_iUnion.2 ⟨p, ?_⟩
      rw [UeqLow p hp]
      constructor
      · apply Metric.mem_ball.mpr
        have hρ' : 0 < min (ρ p) (η / 2) := lt_min (hρ p) (by linarith)
        simpa using hρ'
      · exact d1_sub_real_lt_self (hfnonneg p) hp hν
    · apply mem_iUnion.2 ⟨p, ?_⟩
      rw [UeqHigh p hp]
      constructor
      · apply Metric.mem_ball.mpr
        simpa using hρ p
      · exact lt_of_not_ge hp
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hUopen hUcover
  let Nall (p : ℂ × ℂ) := max (Nrev p) (Nfwd p)
  let N := S.sup Nall
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn p hpK
  have hpCover : p ∈ ⋃ i ∈ S, U i := hS hpK
  rcases mem_iUnion.1 hpCover with ⟨i, hi⟩
  rcases mem_iUnion.1 hi with ⟨hiS, hpi⟩
  have hNall : Nall i ≤ N := Finset.le_sup hiS
  have hNrev : Nrev i ≤ N := le_trans (le_max_left _ _) hNall
  have hNfwd : Nfwd i ≤ N := le_trans (le_max_right _ _) hNall
  have hrevBound : F n p ≤ M → d1Near f η p ≤ F n p + (ν : EReal) := by
    intro hFn
    apply hrev i n (le_trans hNrev hn) p ?_ hFn
    by_cases hiLow : f i ≤ M
    · rw [UeqLow i hiLow] at hpi
      exact (Metric.mem_ball.mp hpi.1).trans_le (min_le_left _ _)
    · rw [UeqHigh i hiLow] at hpi
      exact Metric.mem_ball.mp hpi.1
  have hfwdBound : f p ≤ M → d1Near (F n) η p ≤ f p + (ν : EReal) := by
    intro hfp
    by_cases hiLow : f i ≤ M
    · rw [UeqLow i hiLow] at hpi
      have hdist : dist p i < η / 2 := by
        exact (Metric.mem_ball.mp hpi.1).trans_le (min_le_right _ _)
      exact hfwd i hiLow n (le_trans hNfwd hn) p hdist hpi.2 hfp
    · rw [UeqHigh i hiLow] at hpi
      exact False.elim ((not_le_of_gt hpi.2) hfp)
  exact ⟨hfwdBound, hrevBound⟩

end SupercriticalLFPPAS
