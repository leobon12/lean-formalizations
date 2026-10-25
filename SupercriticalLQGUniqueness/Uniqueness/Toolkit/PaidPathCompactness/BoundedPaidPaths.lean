import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PaidTraces




 
set_option autoImplicit false
noncomputable section
open Set Filter Topology LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.PaidPathCompactness

 

theorem boundedPaidPaths_compact (D : LSCMetric) {K : Set ℂ}
    (hK : IsCompact K) (P : ℕ → ℝ → ℂ) (a b : ℕ → ℝ)
    (hcurve : ∀ n, D.IsCurve (P n) (a n) (b n))
    (htrace : ∀ n t, t ∈ Icc (a n) (b n) → P n t ∈ K)
    {L : ENNReal} (hL : L ≠ ∞) (hlen : ∀ n, D.len (P n) (a n) (b n) ≤ L)
    {x y : ℂ} (hx : Tendsto (fun n => P n (a n)) atTop (nhds x))
    (hy : Tendsto (fun n => P n (b n)) atTop (nhds y)) :
    ∃ (Q : ℕ → unitInterval → ℂ) (φ : ℕ → ℕ) (Q₀ : C(unitInterval, ℂ)),
      StrictMono φ ∧
      (∀ n, Q n 0 = P n (a n) ∧ Q n 1 = P n (b n) ∧
        (∀ t, Q n t ∈ K) ∧
        D.len (fun t => Q n (projIcc 0 1 zero_le_one t)) 0 1 =
          D.len (P n) (a n) (b n)) ∧
      TendstoUniformly (fun n t => Q (φ n) t) Q₀ atTop ∧
      Q₀ 0 = x ∧ Q₀ 1 = y ∧ (∀ t, Q₀ t ∈ K) ∧
      D.IsCurve (fun t => Q₀ (projIcc 0 1 zero_le_one t)) 0 1 ∧
      D.len (fun t => Q₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ L := by
  have hfin : ∀ n, D.len (P n) (a n) (b n) ≠ ∞ :=
    fun n => ne_top_of_le_ne_top hL (hlen n)
  have htrace' : ∀ n, P n '' Icc (a n) (b n) ⊆ K := by
    intro n z hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact htrace n t ht
  choose γ hγlen hγtrace hγlip using fun n =>
    Toolkit.CompactPathInfimum.exists_lipschitz_reparam D (P n) (hcurve n) (hfin n) (htrace' n)
  let Q : ℕ → unitInterval → ℂ := fun n t => γ n t
  have hQtrace : ∀ n t, Q n t ∈ K := fun n t => hγtrace n t
  have hQlip : ∀ n, LipschitzWith L.toNNReal (D.pt ∘ Q n) := by
    intro n
    have hm : (D.len (P n) (a n) (b n)).toNNReal ≤ L.toNNReal :=
      ENNReal.toNNReal_mono hL (hlen n)
    exact (hγlip n).weaken hm
  have hconst : Tendsto (fun _ : ℕ => D) atTop (nhds D) := tendsto_const_nhds
  obtain ⟨φ, Q₀, hφ, hlim, hK₀⟩ :=
    Toolkit.CompactPathInfimum.compact_trace_path_subseq hconst hK hQtrace hQlip
  have hDlip : LipschitzWith L.toNNReal (D.pt ∘ Q₀) :=
    Toolkit.PathInfimum.lipschitz_limit_of_epi (hconst.comp hφ.tendsto_atTop)
      hlim (fun n => hQlip (φ n))
  have hcurve₀ : D.IsCurve (fun t => Q₀ (projIcc 0 1 zero_le_one t)) 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    exact (hDlip.continuous.comp continuous_projIcc).continuousOn
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => Q (φ n) (projIcc 0 1 zero_le_one t)) atTop
        (nhds (Q₀ (projIcc 0 1 zero_le_one t))) :=
    fun t _ => hlim.tendsto_at (projIcc 0 1 zero_le_one t)
  have hlen₀ : D.len (fun t => Q₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ L := by
    have hliminf := Toolkit.CompactPathInfimum.joint_len_le_liminf
      (G := fun _ : ℕ => D) (D := D) (hconst.comp hφ.tendsto_atTop) hpoint
    refine hliminf.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
    change LQGMetric.MetricGeometry.pathLength (γ (φ n)) ≤ L
    exact (hγlen (φ n)).le.trans (hlen (φ n))
  have hQends (n : ℕ) : Q n 0 = P n (a n) ∧ Q n 1 = P n (b n) := by
    change (γ n 0 : ℂ) = P n (a n) ∧ (γ n 1 : ℂ) = P n (b n)
    exact ⟨(γ n).source, (γ n).target⟩
  have hQlen (n : ℕ) :
      D.len (fun t => Q n (projIcc 0 1 zero_le_one t)) 0 1 =
      D.len (P n) (a n) (b n) := by
    change LQGMetric.MetricGeometry.pathLength (γ n) = D.len (P n) (a n) (b n)
    exact hγlen n
  have hQ₀x : Q₀ 0 = x := by
    have hlimx : Tendsto (fun n => Q (φ n) 0) atTop (nhds x) := by
      have heq : (fun n => Q (φ n) 0) = (fun n => P (φ n) (a (φ n))) :=
        funext fun n => (hQends (φ n)).1
      rw [heq]
      exact hx.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique (hlim.tendsto_at 0) hlimx
  have hQ₀y : Q₀ 1 = y := by
    have hlimy : Tendsto (fun n => Q (φ n) 1) atTop (nhds y) := by
      have heq : (fun n => Q (φ n) 1) = (fun n => P (φ n) (b (φ n))) :=
        funext fun n => (hQends (φ n)).2
      rw [heq]
      exact hy.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique (hlim.tendsto_at 1) hlimy
  exact ⟨Q, φ, Q₀, hφ,
    (fun n => ⟨(hQends n).1, (hQends n).2, hQtrace n, hQlen n⟩),
    hlim, hQ₀x, hQ₀y, hK₀, hcurve₀, hlen₀⟩

 
theorem tracePath_of_points (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) {x y : ℂ}
    (hx : x ∈ P '' Icc a b) (hy : y ∈ P '' Icc a b) :
    ∃ γ : Path (D.pt x) (D.pt y),
      Set.range γ ⊆ D.pt '' (P '' Icc a b) ∧
      pathLength γ ≤ D.len P a b := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rcases le_total s t with hst | hts
  · obtain ⟨γ, hlen, hrange⟩ := exists_path_of_curve hst
      (hP.2.mono (Icc_subset_Icc hs.1 ht.2))
    refine ⟨γ, ?_, ?_⟩
    · intro v hv
      obtain ⟨q, hq, rfl⟩ := hrange hv
      exact ⟨P q, ⟨q, ⟨hs.1.trans hq.1, hq.2.trans ht.2⟩, rfl⟩, rfl⟩
    · rw [hlen]
      exact curveLength_mono (D.pt ∘ P) hs.1 ht.2
  · obtain ⟨γ, hlen, hrange⟩ := exists_path_of_curve hts
      (hP.2.mono (Icc_subset_Icc ht.1 hs.2))
    refine ⟨γ.symm, ?_, ?_⟩
    · rw [γ.symm_range]
      intro v hv
      obtain ⟨q, hq, rfl⟩ := hrange hv
      exact ⟨P q, ⟨q, ⟨ht.1.trans hq.1, hq.2.trans hs.2⟩, rfl⟩, rfl⟩
    · rw [pathLength_symm, hlen]
      exact curveLength_mono (D.pt ∘ P) ht.1 hs.2

 
theorem paidTrace_chain_core_path {ι : Type*} (D : LSCMetric)
    (K : ι → Set ℂ) (P : ι → ℝ → ℂ) (a b : ι → ℝ) (C : Set ℂ)
    (hcurve : ∀ q, D.IsCurve (P q) (a q) (b q))
    (htrace : ∀ q, K q = P q '' Icc (a q) (b q))
    (hC : ∀ q, K q ⊆ C)
    (i : ι) (l : List ι) (j : ι)
    (hchain : (i :: l).IsChain fun u v => (K u ∩ K v).Nonempty)
    (hlast : (i :: l).getLast (List.cons_ne_nil i l) = j)
    {x y : ℂ} (hx : x ∈ K i) (hy : y ∈ K j) :
    ∃ γ : Path (D.pt x) (D.pt y),
      Set.range γ ⊆ D.pt '' C ∧
      pathLength γ ≤ ((i :: l).map fun q => D.len (P q) (a q) (b q)).sum := by
  induction l generalizing i x with
  | nil =>
      have hij : i = j := by simpa using hlast
      rw [← hij] at hy
      rw [htrace i] at hx hy
      obtain ⟨γ, hγC, hγlen⟩ := tracePath_of_points D (P i) (hcurve i) hx hy
      refine ⟨γ, ?_, ?_⟩
      · rw [← htrace i] at hγC
        exact hγC.trans (Set.image_mono (hC i))
      · simpa using hγlen
  | cons k tail ih =>
      obtain ⟨z, hzi, hzk⟩ := (List.isChain_cons_cons.mp hchain).1
      have htail : (k :: tail).IsChain fun u v => (K u ∩ K v).Nonempty :=
        (List.isChain_cons_cons.mp hchain).2
      have hlast' : (k :: tail).getLast (List.cons_ne_nil k tail) = j := by
        simpa using hlast
      have hxi : x ∈ P i '' Icc (a i) (b i) := (htrace i).symm ▸ hx
      have hzi' : z ∈ P i '' Icc (a i) (b i) := (htrace i).symm ▸ hzi
      obtain ⟨γ₁, hγ₁C, hγ₁len⟩ :=
        tracePath_of_points D (P i) (hcurve i) hxi hzi'
      have hγ₁C' : Set.range γ₁ ⊆ D.pt '' C := by
        rw [← htrace i] at hγ₁C
        exact hγ₁C.trans (Set.image_mono (hC i))
      obtain ⟨γ₂, hγ₂C, hγ₂len⟩ := ih k htail hlast' hzk
      refine ⟨γ₁.trans γ₂, ?_, ?_⟩
      · rw [Path.trans_range]
        exact Set.union_subset hγ₁C' hγ₂C
      · rw [pathLength_trans]
        simpa only [List.map_cons, List.sum_cons] using add_le_add hγ₁len hγ₂len

 
theorem paidTrace_chain_path {ι : Type*} [DecidableEq ι]
    (D : LSCMetric) (S₀ : Finset ι) (K : ι → Set ℂ)
    (P : ι → ℝ → ℂ) (a b : ι → ℝ) (c : ι → ℂ)
    (A C : Set ℂ) (hAne : A.Nonempty) (hA : IsPreconnected A)
    (hcov : A ⊆ ⋃ i ∈ S₀, connectedComponentIn (K i)ᶜ (c i))
    (hcurve : ∀ i ∈ S₀, D.IsCurve (P i) (a i) (b i))
    (hEucl : ∀ i ∈ S₀, ContinuousOn (P i) (Icc (a i) (b i)))
    (htrace : ∀ i ∈ S₀, K i = P i '' Icc (a i) (b i))
    (_hfinite : ∀ i ∈ S₀, D.len (P i) (a i) (b i) < ∞)
    (hbounded : ∀ i ∈ S₀,
      Bornology.IsBounded (connectedComponentIn (K i)ᶜ (c i)))
    (hC : ∀ i ∈ S₀, K i ⊆ C) :
    ∃ S ⊆ S₀,
      A ⊆ (⋃ i ∈ S, connectedComponentIn (K i)ᶜ (c i)) ∧
      ∀ i j : {i // i ∈ S}, ∀ x ∈ K i.val, ∀ y ∈ K j.val,
        ∃ γ : Path (D.pt x) (D.pt y),
          Set.range γ ⊆ D.pt '' C ∧
          pathLength γ ≤ ∑ k ∈ S, D.len (P k) (a k) (b k) := by
  classical
  have hc : ∀ i ∈ S₀, IsCompact (K i) := by
    intro i hi
    rw [htrace i hi]
    exact isCompact_Icc.image_of_continuousOn (hEucl i hi)
  have hconn : ∀ i ∈ S₀, IsConnected (K i) := by
    intro i hi
    rw [htrace i hi]
    exact (isConnected_Icc (hcurve i hi).1).image (P i) (hEucl i hi)
  obtain ⟨S, hSS₀, hSA, _, _, hchains⟩ :=
    PlanarSeparation.finiteObstacle_chain S₀ K c A hAne hA hcov hc hconn hbounded
  refine ⟨S, hSS₀, hSA, ?_⟩
  intro i j x hx y hy
  obtain ⟨l, hne, hfirst, hlast, hnodup, hchain⟩ := hchains i j
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons u tail =>
      have hui : u = i := by simpa using hfirst
      subst u
      have hlast' : (i :: tail).getLast (List.cons_ne_nil i tail) = j := by
        simpa using hlast
      have hc' : ∀ q : {i // i ∈ S}, D.IsCurve (P q.val) (a q.val) (b q.val) :=
        fun q => hcurve q.val (hSS₀ q.property)
      have ht' : ∀ q : {i // i ∈ S},
          K q.val = P q.val '' Icc (a q.val) (b q.val) :=
        fun q => htrace q.val (hSS₀ q.property)
      have hC' : ∀ q : {i // i ∈ S}, K q.val ⊆ C :=
        fun q => hC q.val (hSS₀ q.property)
      obtain ⟨γ, hγC, hγlen⟩ := paidTrace_chain_core_path D
        (fun q : {i // i ∈ S} => K q.val)
        (fun q => P q.val) (fun q => a q.val) (fun q => b q.val)
        C hc' ht' hC' i tail j hchain hlast' hx hy
      have hsub : (i :: tail).toFinset ⊆ S.attach := by
        intro q hq
        exact Finset.mem_attach S q
      have hsum : ((i :: tail).map (fun q : {i // i ∈ S} =>
          D.len (P q.val) (a q.val) (b q.val))).sum ≤
          ∑ k ∈ S, D.len (P k) (a k) (b k) := by
        rw [← List.sum_toFinset _ hnodup]
        calc
          _ ≤ ∑ q ∈ S.attach, D.len (P q.val) (a q.val) (b q.val) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (by simp)
          _ = ∑ k ∈ S, D.len (P k) (a k) (b k) := by
            exact Finset.sum_attach S (fun k => D.len (P k) (a k) (b k))
      exact ⟨γ, hγC, hγlen.trans hsum⟩

 
theorem dyadic_left_interval_cover {t : ℝ} (ht : 0 < t) (htHalf : t ≤ 1 / 2) :
    ∃ k : ℕ, (1 / 2 : ℝ) ^ (k + 2) < t ∧
      t < 3 * (1 / 2 : ℝ) ^ (k + 2) := by
  obtain ⟨n, hnlow, hnup⟩ :=
    exists_nat_pow_near_of_lt_one ht (by linarith : t ≤ 1)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  cases n with
  | zero =>
      norm_num at hnlow hnup
      linarith
  | succ k =>
      refine ⟨k, ?_, ?_⟩
      · simpa only [Nat.succ_eq_add_one, add_assoc, Nat.reduceAdd] using hnlow
      · have hp : 0 < (1 / 2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
        have hpow : (1 / 2 : ℝ) ^ (k + 2) =
            (1 / 2 : ℝ) ^ (k + 1) / 2 := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
        rw [hpow]
        nlinarith [hnup]

 
theorem dyadic_twoEnd_interval_cover {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ k : ℕ, ((1 / 2 : ℝ) ^ (k + 2) < t ∧
      t < 3 * (1 / 2 : ℝ) ^ (k + 2)) ∨
      (1 - 3 * (1 / 2 : ℝ) ^ (k + 2) < t ∧
       t < 1 - (1 / 2 : ℝ) ^ (k + 2)) := by
  by_cases hhalf : t ≤ 1 / 2
  · obtain ⟨k, hk⟩ := dyadic_left_interval_cover ht.1 hhalf
    exact ⟨k, Or.inl hk⟩
  · have hleft : 0 < 1 - t := by linarith [ht.2]
    have hright : 1 - t ≤ 1 / 2 := by linarith
    obtain ⟨k, hk⟩ := dyadic_left_interval_cover hleft hright
    refine ⟨k, Or.inr ?_⟩
    constructor <;> linarith [hk.1, hk.2]

 
theorem disjointExcursionIntervals_ordered {P : ℝ → ℂ} {O₁ O₂ : Set ℂ}
    {a₁ b₁ a₂ b₂ : ℝ} (hdisj : Disjoint O₁ O₂)
    (h₁ : ∀ t ∈ Ioo a₁ b₁, P t ∈ O₁)
    (h₂ : ∀ t ∈ Ioo a₂ b₂, P t ∈ O₂)
    (ha₂b₂ : a₂ < b₂) (ha₁a₂ : a₁ < a₂) : b₁ ≤ a₂ := by
  by_contra h
  have ha₂b₁ : a₂ < b₁ := lt_of_not_ge h
  have hmin : a₂ < min b₁ b₂ := lt_min ha₂b₁ ha₂b₂
  obtain ⟨t, ha₂t, htmin⟩ := exists_between hmin
  have ht₁ : t ∈ Ioo a₁ b₁ :=
    ⟨ha₁a₂.trans ha₂t, htmin.trans_le (min_le_left b₁ b₂)⟩
  have ht₂ : t ∈ Ioo a₂ b₂ :=
    ⟨ha₂t, htmin.trans_le (min_le_right b₁ b₂)⟩
  exact Set.disjoint_left.mp hdisj (h₁ t ht₁) (h₂ t ht₂)

 

theorem singleExcursion_splice (D : LSCMetric) {P Q : ℝ → ℂ}
    {T τ σ : ℝ} (h0τ : 0 ≤ τ) (hτσ : τ ≤ σ) (hσT : σ ≤ T)
    (hP : D.IsCurve P 0 T) (hQ : D.IsCurve Q τ σ)
    (hτ : P τ = Q τ) (hσ : Q σ = P σ) :
    let R : ℝ → ℂ := fun t => if t ≤ τ then P t else if t ≤ σ then Q t else P t
    D.IsCurve R 0 T ∧ R 0 = P 0 ∧ R T = P T ∧
      D.len R 0 T = D.len P 0 τ + D.len Q τ σ + D.len P σ T := by
  let S : ℝ → ℂ := fun t => if t ≤ σ then Q t else P t
  let R : ℝ → ℂ := fun t => if t ≤ τ then P t else S t
  have hSτ : S τ = P τ := by simp [S, hτσ, ← hτ]
  have hS : D.IsCurve S τ T := by
    refine ⟨hτσ.trans hσT, ?_⟩
    change ContinuousOn (fun t => if t ≤ σ then D.pt (Q t) else D.pt (P t)) (Icc τ T)
    exact continuousOn_concat hτσ hσT (congrArg D.pt hσ) hQ.2
      (hP.2.mono (Icc_subset_Icc (h0τ.trans hτσ) le_rfl))
  have hR : D.IsCurve R 0 T := by
    refine ⟨h0τ.trans (hτσ.trans hσT), ?_⟩
    change ContinuousOn (fun t => if t ≤ τ then D.pt (P t) else D.pt (S t)) (Icc 0 T)
    exact continuousOn_concat h0τ (hτσ.trans hσT) (congrArg D.pt hSτ.symm)
      (hP.2.mono (Icc_subset_Icc le_rfl (hτσ.trans hσT))) hS.2
  have hlenS : D.len S τ T = D.len Q τ σ + D.len P σ T := by
    change curveLength (fun t => if t ≤ σ then D.pt (Q t) else D.pt (P t)) τ T = _
    exact curveLength_concat hτσ hσT (congrArg D.pt hσ)
  have hlenR : D.len R 0 T = D.len P 0 τ + D.len S τ T := by
    change curveLength (fun t => if t ≤ τ then D.pt (P t) else D.pt (S t)) 0 T = _
    exact curveLength_concat h0τ (hτσ.trans hσT) (congrArg D.pt hSτ.symm)
  dsimp only
  have hdef : (fun t => if t ≤ τ then P t else if t ≤ σ then Q t else P t) = R := rfl
  rw [hdef]
  refine ⟨hR, ?_, ?_, ?_⟩
  · simp [h0τ]
  · by_cases hTτ : T ≤ τ
    · simp [hTτ]
    · by_cases hTσ : T ≤ σ
      · have hTeq : T = σ := le_antisymm hTσ hσT
        subst T
        simp [hTτ, hσ]
      · simp [hTτ, hTσ]
  · rw [hlenR, hlenS, add_assoc]

 
theorem singleExcursion_cost_balance (D : LSCMetric) {P Q : ℝ → ℂ}
    {T τ σ : ℝ} (h0τ : 0 ≤ τ) (hτσ : τ ≤ σ) (hσT : σ ≤ T)
    (hP : D.IsCurve P 0 T) (hQ : D.IsCurve Q τ σ)
    (hτ : P τ = Q τ) (hσ : Q σ = P σ) :
    let R : ℝ → ℂ := fun t => if t ≤ τ then P t else if t ≤ σ then Q t else P t
    D.len R 0 T + D.len P τ σ = D.len P 0 T + D.len Q τ σ := by
  have hsplice := singleExcursion_splice D h0τ hτσ hσT hP hQ hτ hσ
  dsimp only at hsplice ⊢
  have hlenP : D.len P 0 T = D.len P 0 τ + D.len P τ σ + D.len P σ T := by
    change curveLength (D.pt ∘ P) 0 T = _
    rw [← curveLength_add _ h0τ (hτσ.trans hσT)]
    rw [← curveLength_add _ hτσ hσT]
    ac_rfl
  rw [hsplice.2.2.2, hlenP]
  ac_rfl

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.PaidPathCompactness
