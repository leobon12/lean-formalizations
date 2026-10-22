import HigherDimLQGContinuity.MetricVersion.Weyl

/-!
# Metric-valued versions (packet E5): no exceptional degenerate parameter

Part C, `c:lem-opt-nondeg` ((5.10)) and `c:lem-opt-metric`. Let `K ⊆ ℝ^d × ℝ^d` be compact and off the diagonal.
With the invariant good event `E` of `weyl_translates_ae`, for rationals `c < c'` with `[c, c'] ⊆ S_d` put

  `A(c, c') = E ∩ {g : ∃ ξ ∈ [c, c'], ∃ p ∈ K, X(ξ)(g)(p) ≤ 0}`.

It is measurable (on `E` the condition is `∀ n, ∃ q ∈ [c, c'] ∩ ℚ, X(q)(g)(K) < 1/(n+1)`, by continuity in `ξ` and
compactness of `[c, c']` and `K`), and invariant under the rational frame shifts (the Weyl bounds preserve the sign of
`X(ξ)(g)(p)`), so `P(A(c, c')) ∈ {0, 1}` (`measure_zero_or_one_of_frame_invariant`). If every rational window around
some `ξ₀ ∈ S_d` had probability one, a sample in all of them and in the fixed-parameter event `X(ξ₀) = ρ^{ξ₀} > 0`
on `K` would contradict the continuity of `ξ ↦ X(ξ)(g)(K)` at `ξ₀`; hence every `ξ₀` has a null rational window, and
the countably many null windows cover every degenerate parameter (`ae_forall_pos_setDist_version`). Closed balls
around a dense sequence then give positivity at all pairs `x ≠ y` (`ae_forall_pos_version`), and the metric axioms
follow (`ae_forall_isMetricFn_version`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Sections of a jointly measurable family are measurable. -/
theorem mv_measurable_section {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : Measurable (Function.uncurry X))
    (ξ : ℝ) : Measurable (X ξ) :=
  hX.comp (measurable_const.prodMk measurable_id)

/-- **`c:lem-opt-nondeg`** (no exceptional degenerate parameter): for a compact set `K` off the diagonal, almost
surely `X(ξ)(g) > 0` on `K` for every positive subcritical `ξ`. -/
theorem ae_forall_pos_setDist_version (hd : 3 ≤ d) (F : PairingFrame d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X) {K : Set (Rd d × Rd d)}
    (hK : IsCompact K) (hKd : ∀ p ∈ K, p.1 ≠ p.2) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ ξ ∈ subcritSet d, ∀ p ∈ K, 0 < X ξ g p := by
  have hd2 : 2 ≤ d := by omega
  have hspec := normLGFLaw_spec_holds d hd2
  have := hspec.1
  rcases K.eq_empty_or_nonempty with hKe | hne
  · exact Eventually.of_forall fun g ξ _ p hp => by rw [hKe] at hp; exact absurd hp (notMem_empty p)
  have hS : IsOpen (subcritSet d) := mv_isOpen_subcritSet hd2
  obtain ⟨E, hEm, hEae, hinv, hcont, -, hweyl⟩ := weyl_translates_ae hd F hX
  -- the sign of `X(ξ)(g)(p)` is invariant under rational frame shifts on `E`
  have hsign : ∀ g ∈ E, ∀ v : ℕ →₀ ℚ, ∀ ξ ∈ subcritSet d, ∀ p : Rd d × Rd d,
      X ξ (addFun g (mvFrameShift F v)) p ≤ 0 ↔ X ξ g p ≤ 0 := by
    intro g hg v ξ hξ p
    obtain ⟨M, -, hMb⟩ := exists_abs_mvFrameShift_le F v
    obtain ⟨hlo, hhi⟩ := hweyl v M hMb g hg ξ hξ p
    constructor
    · intro h
      by_contra hpos
      push Not at hpos
      have := mul_pos (Real.exp_pos (-(ξ * M))) hpos
      linarith
    · intro h
      have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (ξ * M)).le h
      linarith
  -- the window events
  set A : ℚ → ℚ → Set (DistRd d) := fun c c' =>
    E ∩ {g | ∃ ξ ∈ Icc (c : ℝ) c', ∃ p ∈ K, X ξ g p ≤ 0} with hAdef
  -- measurability
  have hAm : ∀ c c' : ℚ, (c : ℝ) < c' → Icc (c : ℝ) c' ⊆ subcritSet d → MeasurableSet (A c c') := by
    intro c c' hcc hJ
    have hJne : (Icc (c : ℝ) c').Nonempty := nonempty_Icc.2 hcc.le
    have key : A c c' = E ∩ ⋂ n : ℕ, ⋃ q : ℚ,
        {g | (q : ℝ) ∈ Icc (c : ℝ) c' ∧ mvInf K (X q g) < 1 / ((n : ℝ) + 1)} := by
      ext g
      simp only [hAdef, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion]
      refine and_congr_right fun hg => ?_
      have hm : ContinuousOn (fun ξ => mvInf K (X ξ g)) (Icc (c : ℝ) c') :=
        (mv_continuousOn_mvInf (hcont g hg) hK).mono hJ
      constructor
      · rintro ⟨ξ, hξ, p, hp, hpx⟩ n
        have hmξ : mvInf K (X ξ g) < 1 / ((n : ℝ) + 1) :=
          (mvInf_le hK _ hp).trans_lt (hpx.trans_lt (by positivity))
        have hcl := mv_Icc_subset_closure_rat hcc hξ
        have : (𝓝[Icc (c : ℝ) c' ∩ range ((↑) : ℚ → ℝ)] ξ).NeBot :=
          mem_closure_iff_nhdsWithin_neBot.1 hcl
        have ht : Tendsto (fun ξ => mvInf K (X ξ g)) (𝓝[Icc (c : ℝ) c' ∩ range ((↑) : ℚ → ℝ)] ξ)
            (𝓝 (mvInf K (X ξ g))) := (hm ξ hξ).mono inter_subset_left
        obtain ⟨t, ht1, ht2⟩ := ((ht.eventually (gt_mem_nhds hmξ)).and self_mem_nhdsWithin).exists
        obtain ⟨htJ, q, rfl⟩ := ht2
        exact ⟨q, htJ, ht1⟩
      · intro h
        obtain ⟨ξ₀, hξ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hJne hm
        have hle : mvInf K (X ξ₀ g) ≤ 0 := by
          by_contra hpos
          push Not at hpos
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
          obtain ⟨q, hqJ, hq⟩ := h n
          have := hmin hqJ
          simp only [mem_ofPred_eq] at this
          linarith
        obtain ⟨p, hp, hpx⟩ := (mvInf_le_iff hK hne (X ξ₀ g) 0).1 hle
        exact ⟨ξ₀, hξ₀, p, hp, hpx⟩
    rw [key]
    refine hEm.inter (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => ?_)
    exact (MeasurableSet.const _).inter (measurableSet_lt
      ((measurable_mvInf hK).comp (mv_measurable_section hX.1 q)) measurable_const)
  -- invariance
  have hAinv : ∀ c c' : ℚ, Icc (c : ℝ) c' ⊆ subcritSet d →
      ∀ (v : ℕ →₀ ℚ) (g : DistRd d), addFun g (mvFrameShift F v) ∈ A c c' ↔ g ∈ A c c' := by
    intro c c' hJ v g
    simp only [hAdef, mem_inter_iff, mem_ofPred_eq, hinv v g]
    refine and_congr_right fun hg => ?_
    constructor
    · rintro ⟨ξ, hξ, p, hp, hpx⟩
      exact ⟨ξ, hξ, p, hp, (hsign g hg v ξ (hJ hξ) p).1 hpx⟩
    · rintro ⟨ξ, hξ, p, hp, hpx⟩
      exact ⟨ξ, hξ, p, hp, (hsign g hg v ξ (hJ hξ) p).2 hpx⟩
  -- zero–one law for the windows
  have hA01 : ∀ c c' : ℚ, (c : ℝ) < c' → Icc (c : ℝ) c' ⊆ subcritSet d →
      normLGFLaw d (A c c') = 0 ∨ normLGFLaw d (A c c') = 1 := fun c c' hcc hJ =>
    measure_zero_or_one_of_frame_invariant hd2 F (hAm c c' hcc hJ) (hAinv c c' hJ)
  -- the fixed-parameter event
  have hfix : ∀ ξ₀ ∈ subcritSet d, ∀ᵐ g ∂(normLGFLaw d), ∀ p ∈ K, 0 < X ξ₀ g p := by
    intro ξ₀ hξ₀
    obtain ⟨D, hD⟩ := mv_exists_strong hd hξ₀
    filter_upwards [hX.2.1 ξ₀ hξ₀.1 hξ₀.2 D hD] with g hg p hp
    rw [hg]
    have := (rho D g).apply_pos (hKd p hp)
    rwa [Prod.mk.eta] at this
  -- every parameter has a null rational window
  have hnull : ∀ ξ₀ ∈ subcritSet d, ∃ c c' : ℚ, (c : ℝ) < ξ₀ ∧ ξ₀ < c' ∧ Icc (c : ℝ) c' ⊆ subcritSet d ∧
      normLGFLaw d (A c c') = 0 := by
    intro ξ₀ hξ₀
    by_contra hcon
    push Not at hcon
    have hall : ∀ᵐ g ∂(normLGFLaw d), ∀ c c' : ℚ, (c : ℝ) < ξ₀ → ξ₀ < c' →
        Icc (c : ℝ) c' ⊆ subcritSet d → g ∈ A c c' := by
      rw [ae_all_iff]
      intro c
      rw [ae_all_iff]
      intro c'
      by_cases hcond : (c : ℝ) < ξ₀ ∧ ξ₀ < c' ∧ Icc (c : ℝ) c' ⊆ subcritSet d
      · obtain ⟨h1, h2, h3⟩ := hcond
        have hcc : (c : ℝ) < c' := h1.trans h2
        have h01 := hA01 c c' hcc h3
        have hone : normLGFLaw d (A c c') = 1 := h01.resolve_left (hcon c c' h1 h2 h3)
        have hcompl : normLGFLaw d (A c c')ᶜ = 0 := by
          rw [prob_compl_eq_zero_iff (hAm c c' hcc h3)]
          exact hone
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcompl] with g hg
        intro _ _ _
        simpa only [mem_compl_iff, not_not] using hg
      · exact Eventually.of_forall fun g h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcond
    obtain ⟨g, ⟨hgall, hgfix⟩, hgE⟩ := ((hall.and (hfix ξ₀ hξ₀)).and hEae).exists
    -- continuity of `ξ ↦ X(ξ)(g)(K)` at `ξ₀`
    have hm : ContinuousAt (fun ξ => mvInf K (X ξ g)) ξ₀ :=
      (mv_continuousOn_mvInf (hcont g hgE) hK).continuousAt (hS.mem_nhds hξ₀)
    have hpos₀ : 0 < mvInf K (X ξ₀ g) := (lt_mvInf_iff hK hne _ 0).2 hgfix
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hm.eventually (lt_mem_nhds hpos₀))
    obtain ⟨δ', hδ', hδ'S⟩ := Metric.isOpen_iff.1 hS ξ₀ hξ₀
    set δ'' := min δ δ' with hδ''
    have hδ''pos : 0 < δ'' := lt_min hδ hδ'
    obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show ξ₀ - δ'' < ξ₀ by linarith)
    obtain ⟨c', hc'1, hc'2⟩ := exists_rat_btwn (show ξ₀ < ξ₀ + δ'' by linarith)
    have hJball : Icc (c : ℝ) c' ⊆ ball ξ₀ δ'' := by
      intro t ht
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hJS : Icc (c : ℝ) c' ⊆ subcritSet d :=
      hJball.trans ((ball_subset_ball (min_le_right _ _)).trans hδ'S)
    obtain ⟨-, ξ, hξJ, p, hp, hpx⟩ := hgall c c' hc2 hc'1 hJS
    have hξball : dist ξ ξ₀ < δ := lt_of_lt_of_le (hJball hξJ) (min_le_left _ _)
    have h1 : 0 < mvInf K (X ξ g) := hball hξball
    have h2 : mvInf K (X ξ g) ≤ 0 := (mvInf_le hK _ hp).trans hpx
    linarith
  -- the countably many null windows cover every degenerate parameter
  set T : ℚ → ℚ → Set (DistRd d) := fun c c' =>
    {g | ((c : ℝ) < c' ∧ Icc (c : ℝ) c' ⊆ subcritSet d ∧ normLGFLaw d (A c c') = 0) ∧ g ∈ A c c'} with hTdef
  have hT0 : ∀ c c' : ℚ, normLGFLaw d (T c c') = 0 := by
    intro c c'
    by_cases hcond : (c : ℝ) < c' ∧ Icc (c : ℝ) c' ⊆ subcritSet d ∧ normLGFLaw d (A c c') = 0
    · exact measure_mono_null (fun g hg => hg.2) hcond.2.2
    · have : T c c' = ∅ := by
        ext g
        simp only [hTdef, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro h
        exact absurd h hcond
      rw [this, measure_empty]
  have hTnull : normLGFLaw d (⋃ c : ℚ, ⋃ c' : ℚ, T c c') = 0 :=
    measure_iUnion_null fun c => measure_iUnion_null fun c' => hT0 c c'
  filter_upwards [hEae, measure_eq_zero_iff_ae_notMem.1 hTnull] with g hgE hgT ξ hξ p hp
  by_contra hcon
  push Not at hcon
  obtain ⟨c, c', hc1, hc2, hJ, hA0⟩ := hnull ξ hξ
  refine hgT (mem_iUnion.2 ⟨c, mem_iUnion.2 ⟨c', ?_⟩⟩)
  exact ⟨⟨hc1.trans hc2, hJ, hA0⟩, hgE, ξ, ⟨hc1.le, hc2.le⟩, p, hp, hcon⟩

/-- `c:lem-opt-metric`, positivity: almost surely, for every positive subcritical `ξ` and all `x ≠ y`,
`X(ξ)(g)(x, y) > 0` (countably many products of closed balls around a dense sequence). -/
theorem ae_forall_pos_version (hd : 3 ≤ d) (F : PairingFrame d) {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ ξ ∈ subcritSet d, ∀ x y : Rd d, x ≠ y → 0 < X ξ g (x, y) := by
  set σ : ℕ → Rd d := TopologicalSpace.denseSeq (Rd d) with hσ
  set Kb : ℕ → ℕ → ℕ → Set (Rd d × Rd d) := fun n m k =>
    closedBall (σ n) (1 / ((k : ℝ) + 1)) ×ˢ closedBall (σ m) (1 / ((k : ℝ) + 1)) with hKb
  have hall : ∀ᵐ g ∂(normLGFLaw d), ∀ n m k : ℕ, 2 / ((k : ℝ) + 1) < dist (σ n) (σ m) →
      ∀ ξ ∈ subcritSet d, ∀ p ∈ Kb n m k, 0 < X ξ g p := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro k
    by_cases hcond : 2 / ((k : ℝ) + 1) < dist (σ n) (σ m)
    · have hK : IsCompact (Kb n m k) := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
      have hKd : ∀ p ∈ Kb n m k, p.1 ≠ p.2 := by
        rintro ⟨u, w⟩ ⟨hu, hw⟩ huw
        simp only at huw
        subst huw
        have hu' : dist u (σ n) ≤ 1 / ((k : ℝ) + 1) := hu
        have hw' : dist u (σ m) ≤ 1 / ((k : ℝ) + 1) := hw
        have := dist_triangle (σ n) u (σ m)
        have h3 : dist (σ n) u = dist u (σ n) := dist_comm _ _
        have h2 : 2 / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by ring
        linarith
      filter_upwards [ae_forall_pos_setDist_version hd F hX hK hKd] with g hg
      exact fun _ => hg
    · exact Eventually.of_forall fun g h => absurd h hcond
  filter_upwards [hall] with g hg ξ hξ x y hxy
  have hδ : 0 < dist x y := dist_pos.2 hxy
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < dist x y / 4 by positivity)
  have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (Rd d)).exists_dist_lt x hk0
  obtain ⟨m, hm⟩ := (TopologicalSpace.denseRange_denseSeq (Rd d)).exists_dist_lt y hk0
  have hcond : 2 / ((k : ℝ) + 1) < dist (σ n) (σ m) := by
    have h1 := dist_triangle x (σ n) y
    have h2 := dist_triangle (σ n) (σ m) y
    have h3 : dist (σ m) y = dist y (σ m) := dist_comm _ _
    have h4 : 2 / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by ring
    linarith
  have hmem : (x, y) ∈ Kb n m k := by
    refine ⟨?_, ?_⟩
    · show dist x (σ n) ≤ 1 / ((k : ℝ) + 1)
      exact hn.le
    · show dist y (σ m) ≤ 1 / ((k : ℝ) + 1)
      exact hm.le
  exact hg n m k hcond ξ hξ (x, y) hmem

/-- **`c:lem-opt-metric`**: almost surely, `X(ξ)(g)` satisfies the metric axioms for every positive subcritical
`ξ` (symmetry, the triangle inequality and `X(x, x) = 0` are closed conditions in `ξ`, proved at rational `ξ`;
positivity is `ae_forall_pos_version`). -/
theorem ae_forall_isMetricFn_version (hd : 3 ≤ d) (F : PairingFrame d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ ξ ∈ subcritSet d, IsMetricFn (X ξ g) := by
  obtain ⟨E, -, hEae, -, hcont, hrat, -⟩ := weyl_translates_ae hd F hX
  filter_upwards [hEae, ae_forall_pos_version hd F hX] with g hgE hpos ξ hξ
  exact mv_isMetricFn_of_family (mv_isOpen_subcritSet (by omega)) (hcont g hgE) (hrat g hgE) hpos hξ

/-- `c:lem-opt-nondeg` in the set-distance form of Part C: for disjoint nonempty compact `A, B ⊆ ℝ^d`, almost surely
`X(ξ)(g)(A, B) = inf_{A × B} X(ξ)(g) > 0` for every positive subcritical `ξ`. -/
theorem ae_forall_pos_mvInf_version (hd : 3 ≤ d) (F : PairingFrame d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X) {A B : Set (Rd d)} (hA : IsCompact A)
    (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : Disjoint A B) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ ξ ∈ subcritSet d, 0 < mvInf (A ×ˢ B) (X ξ g) := by
  have hK : IsCompact (A ×ˢ B) := hA.prod hB
  have hKd : ∀ p ∈ A ×ˢ B, p.1 ≠ p.2 := fun p hp h => hAB.ne_of_mem hp.1 hp.2 h
  filter_upwards [ae_forall_pos_setDist_version hd F hX hK hKd] with g hg ξ hξ
  exact (lt_mvInf_iff hK (hAne.prod hBne) _ 0).2 (hg ξ hξ)

end HigherDimLQGContinuity
