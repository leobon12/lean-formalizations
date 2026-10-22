import HigherDimLQGContinuity.Endpoint.Events
import HigherDimLQGContinuity.Endpoint.Chain
import HigherDimLQGContinuity.Param.Interval
import HigherDimLQGMetric.Frozen.Theorem12

/-!
# The Euclidean endpoint (packet E3), part 6: `endpoint_of`

Blueprint Part C `c:thm-endpoint` ((5.8)); NA4 Details (a) A6. For `d ≥ 3`, from `Prop37Shape d`,
`MarginalEuclidStmt d` and any family `X` with `PosVersionStmt d X`:

  for `normLGFLaw d`-a.e. `g`, `X ξ g → euclidDistC d` in `C(ℝ^d × ℝ^d, ℝ)` as `ξ → 0` within the positive
  subcritical set (`EndpointStmt d X`).

Quantitatively (`endpt_key`, `endpt_ae_blocks`): for a.e. `g` and every integer `R ≥ 1` there is `k₁` with
`|X ξ g (x, y) - |x - y|| ≤ 4(1 + 2R) √(2^{-k})` for `ξ ∈ [2^{-k}, 2^{1-k}]`, `k ≥ k₁`, `x, y ∈ B̄_R`; hence
(`endpoint_rate_of`, the quantitative clause of `c:thm-endpoint` with `4` in place of `2e`) there is `ξ_R(g) > 0` with
`supd_R(X ξ g, eu) ≤ 4(1 + 2R)√ξ` for `ξ ∈ (0, ξ_R(g)]`.

Proof: a subcritical `ξ̄₀` with `(0, ξ̄₀] ⊆ S_d` (`exists_Ioo_subset_subcritSet`); strong assignments at every
positive subcritical parameter (`theorem12` of [8], `endpt_exists_strong`); for each radius, the constants of
`Prop37Shape` at `ξ̄₀` and of `MarginalEuclidStmt` at `(R, 4(L+2), 3/4)` and `(1, 4, 3/4)`; for large `k` the bad
event of block `k` has probability `≤ K 2^{-k}` (`measure_endBad_le`); Borel–Cantelli
(`ae_eventually_notMem`); on the complement, the version event at the countably many nodes
(`PosVersionStmt` (ii)), and the continuity event (`PosVersionStmt` (iii)), `supd_profile_le_of_not_endBad`
controls every block; `endpt_tendsto_of_blocks` concludes. Only `PosVersionStmt`'s three clauses are used: the
nonnegativity at the nodes comes from the version clause (`ContMetric.nonneg`).
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

/-- A strong assignment at every positive subcritical parameter (`theorem12` of [8]; the values off `S_d` are junk). -/
theorem endpt_exists_strong (hd : 3 ≤ d) :
    ∃ Dt : ℝ → DistRd d → ContMetric d,
      ∀ t ∈ subcritSet d, IsStrongExpMetric d t (distExp d t) (Dt t) := by
  obtain ⟨ξ₀, hξ₀⟩ := subcritSet_nonempty (d := d) (by omega)
  have hex : ∀ t : ℝ, ∃ D : DistRd d → ContMetric d,
      t ∈ subcritSet d → IsStrongExpMetric d t (distExp d t) D := by
    intro t
    by_cases ht : t ∈ subcritSet d
    · obtain ⟨D, hD, -⟩ := (theorem12 d t hd ht.1 ht.2).1
      exact ⟨D, fun _ => hD⟩
    · obtain ⟨D, -, -⟩ := (theorem12 d ξ₀ hd hξ₀.1 hξ₀.2).1
      exact ⟨D, fun h => absurd h ht⟩
  choose Dt hDt using hex
  exact ⟨Dt, hDt⟩

/-- **The bad event of a block is rare** (`c:lem-end-base`, `c:lem-end-bridge`, `c:lem-end-fine` together):
under the per-block conditions (all true for large `k`), `P(Bad(k)) ≤ (2 C₁ 2^{3(L+2)} + 2) 2^{-k}`. -/
theorem measure_endBad_le {Dt : ℝ → DistRd d → ContMetric d}
    {ξb ps c' R B M C c C₁ C₂ : ℝ} (h37 : EndP37 d ξb ps c' R B M C c) (hC : 1 ≤ C) (hc : 0 < c)
    (hc' : 0 < c') (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : 2 * endA k ≤ ξb)
    (hDt : ∀ t ∈ Icc (endA k) (2 * endA k), IsStrongExpMetric d t (distExp d t) (Dt t))
    (hm1 : ∀ t ∈ Icc (endA k) (2 * endA k),
      ∫⁻ g, supDistLU d R (rho (Dt t) g).1 (euclidDistC d) ^ ((4 * (endLexp B M + 2) : ℕ) : ℝ)
          ∂(normLGFLaw d) ≤
        ENNReal.ofReal (C₁ * t ^ ((3 / 4 : ℝ) * ((4 * (endLexp B M + 2) : ℕ) : ℝ))))
    (hm2 : ∀ t ∈ Icc (endA k) (2 * endA k),
      ∫⁻ g, supDistLU d 1 (rho (Dt t) g).1 (euclidDistC d) ^ (4 : ℝ) ∂(pinLaw d 10) ≤
        ENNReal.ofReal (C₂ * t ^ ((3 / 4 : ℝ) * 4)))
    (hseed : 16 ^ 5 * C₂ * endA k / c' ^ 4 ≤ ps)
    (hbdepth : C * (endEps k / 8) ^ (-M) * Real.log (C / (endEps k / 8)) ≤
      c * (endEps k / 8) / endA (k + endLexp B M * k))
    (hbfail : ((2 : ℝ) ^ endLevel (endDexp B M) k 0 + 1) *
        (C * (endEps k / 8) ^ (-M) * Real.exp (-(c * (endEps k / 8) ^ M *
          (c * (endEps k / 8) / endA (k + endLexp B M * k))))) ≤ (1 / 2) ^ k)
    (hcond : ∀ j : ℕ,
      endA (k + endLevel (endDexp B M) k j) ≤
          Real.exp (-(C * endA k ^ (-B) * endDelta k j ^ (-B))) ∧
      C * endDelta k j ^ (-M) * Real.log (C / endDelta k j) ≤
        c * endDelta k j / endA (k + endLevel (endDexp B M) k j) ∧
      ((2 : ℝ) ^ endLevel (endDexp B M) k (j + 1) + 1) *
        (C * endDelta k j ^ (-M) * Real.exp (-(c * endDelta k j ^ M *
          (c * endDelta k j / endA (k + endLevel (endDexp B M) k j))))) ≤ (1 / 2) ^ (k + j + 1)) :
    normLGFLaw d (endBad Dt R (endLexp B M) (endDexp B M) k) ≤
      ENNReal.ofReal ((2 * C₁ * 2 ^ (3 * (endLexp B M + 2)) + 2) * (1 / 2) ^ k) := by
  set L := endLexp B M
  set D := endDexp B M
  have hC0 : 0 ≤ C := by linarith
  have hA := endA_pos k
  -- base
  have hbase : normLGFLaw d (endBase Dt R L k) ≤
      ENNReal.ofReal (2 * C₁ * 2 ^ (3 * (L + 2)) * (1 / 2) ^ k) := by
    refine (measure_endBase_le hC₁ (fun m hm => (hDt _ (endNode_mem hm)).measurable)
      (fun m hm => hm1 _ (endNode_mem hm))).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : endA k ^ 2 ≤ (1 / 2) ^ k := by
      have := endA_le_one k
      calc endA k ^ 2 ≤ endA k := by nlinarith
        _ = (1 / 2) ^ k := rfl
    gcongr
  -- bridge
  have hseed' : ∀ s ∈ Icc (endA k) (2 * endA k), ∀ t ∈ Icc (endA k) (2 * endA k),
      pinLaw d 10 {g | ENNReal.ofReal (c' * (endEps k / 8)) <
        supDistLU d 1 (rho (Dt s) g).1 (rho (Dt t) g).1} ≤ ENNReal.ofReal ps := fun s hs t ht =>
    (end_seed_block (hDt s hs).measurable (hDt t ht).measurable hc' hC₂ hs ht (hm2 s hs)
      (hm2 t ht)).trans (ENNReal.ofReal_le_ofReal hseed)
  have hbridge := measure_endBridge_le (R := R) (L := L) (D := D) h37 hC0 hc hk1 hk hDt hseed'
    hbdepth hbfail
  -- fine
  have hfine := measure_endFine_le (R := R) h37 hC0 hc hk hDt hcond
  calc normLGFLaw d (endBad Dt R L D k)
      ≤ normLGFLaw d (endBase Dt R L k) + normLGFLaw d (endBridge Dt R L D k) +
          normLGFLaw d (endFine Dt R D k) := by
        unfold endBad
        exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (2 * C₁ * 2 ^ (3 * (L + 2)) * (1 / 2) ^ k) + ENNReal.ofReal ((1 / 2) ^ k) +
          ENNReal.ofReal ((1 / 2) ^ k) := add_le_add (add_le_add hbase hbridge) hfine
    _ = ENNReal.ofReal ((2 * C₁ * 2 ^ (3 * (L + 2)) + 2) * (1 / 2) ^ k) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem endpt_not_mem_of_not_mem_biUnion {α : Type*} {N : ℕ} {E : ℕ → Set α} {g : α}
    (h : g ∉ ⋃ m ∈ Finset.range (N + 1), E m) : ∀ m ≤ N, g ∉ E m := fun m hm hg =>
  h (mem_iUnion₂.2 ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hm), hg⟩)

/-- **The endpoint at one radius** (`c:thm-endpoint`, quantitative form): for a.e. `g` there is `k₁` with
`|X ξ g (x, y) - |x - y|| ≤ 4(1 + 2R) ε_k` for every block `k ≥ k₁`, `ξ ∈ [a_k, 2a_k]` and `x, y ∈ B̄_R`. -/
theorem endpt_key (hd : 3 ≤ d) (hP : Prop37Shape d) (hL : MarginalEuclidStmt d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X)
    {Dt : ℝ → DistRd d → ContMetric d}
    (hDt : ∀ t ∈ subcritSet d, IsStrongExpMetric d t (distExp d t) (Dt t))
    {ξb : ℝ} (hξbS : ξb ∈ subcritSet d) (hsub : ∀ t, 0 < t → t ≤ ξb → t ∈ subcritSet d)
    (R : ℕ) (hR : 1 ≤ R) :
    ∀ᵐ g ∂(normLGFLaw d), ∃ k₁ : ℕ, ∀ k ≥ k₁, ∀ ξ ∈ Icc (endA k) (2 * endA k),
      ∀ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
        |X ξ g p - euclidDistC d p| ≤ 4 * (1 + 2 * R) * endEps k := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  -- the constants of `Prop37Shape` at `ξ̄₀` and radius `R`
  obtain ⟨ps, c', hps, -, hc', h37R⟩ := endpt_p37_of hP hξbS.1 hξbS.2
  obtain ⟨B, M, C, c, -, -, hc, -, hC, h37⟩ := h37R R hR'
  set L := endLexp B M with hLdef
  set D := endDexp B M with hDdef
  -- Lemma 5.1 at `(R, 4(L+2), 3/4)` and at `(1, 4, 3/4)`
  obtain ⟨ξ₁, C₁, hξ₁, hC₁, hm1⟩ := hL R hR' ((4 * (L + 2) : ℕ) : ℝ)
    (by push_cast; linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]) (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨ξ₂, C₂, hξ₂, hC₂, hm2⟩ := hL 1 le_rfl 4 (by norm_num) (3 / 4) (by norm_num) (by norm_num)
  -- thresholds
  obtain ⟨N₁, hN₁⟩ := endpt_fine_G (B := B) (M := M) (by linarith : (0 : ℝ) < C)
  obtain ⟨N₂, hN₂⟩ := endpt_fine_depth (B := B) (M := M) hC hc
  obtain ⟨N₃, hN₃⟩ := endpt_fine_fail (B := B) (M := M) hC hc
  obtain ⟨k₄, hk₄⟩ := endpt_bridge_depth (B := B) (M := M) hC hc
  obtain ⟨k₅, hk₅⟩ := endpt_bridge_fail (B := B) (M := M) hC hc
  have hev1 : ∀ᶠ k in atTop, 16 ^ 5 * C₂ * endA k / c' ^ 4 ≤ ps := by
    have h0 : Tendsto (fun k => 16 ^ 5 * C₂ * endA k / c' ^ 4) atTop (𝓝 0) := by
      have := (tendsto_endA.const_mul (16 ^ 5 * C₂)).div_const (c' ^ 4)
      simpa only [mul_zero, zero_div] using this
    exact h0.eventually (ge_mem_nhds hps)
  have hev2 : ∀ᶠ k in atTop, 2 * endA k ≤ min ξb (min ξ₁ ξ₂) := by
    have h0 : Tendsto (fun k => 2 * endA k) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_endA.const_mul 2
    exact h0.eventually (ge_mem_nhds (lt_min hξbS.1 (lt_min hξ₁ hξ₂)))
  obtain ⟨k₀, hk₀⟩ := (hev1.and (hev2.and ((eventually_ge_atTop (max (max 2 N₁) (max N₂ N₃))).and
    (eventually_ge_atTop (max k₄ k₅))))).exists_forall_of_atTop
  -- the bad events are rare beyond `k₀`
  set K := 2 * C₁ * 2 ^ (3 * (L + 2)) + 2 with hKdef
  have hK : 0 ≤ K := by positivity
  have hblock : ∀ k ≥ k₀, Icc (endA k) (2 * endA k) ⊆ subcritSet d := by
    intro k hk t ht
    have h2 := (hk₀ k hk).2.1
    exact hsub t ((endA_pos k).trans_le ht.1) (ht.2.trans (h2.trans (min_le_left _ _)))
  have hbad : ∀ k ≥ k₀, normLGFLaw d (endBad Dt R L D k) ≤ ENNReal.ofReal (K * (1 / 2) ^ k) := by
    intro k hk
    obtain ⟨hs, hr, hN, hk45⟩ := hk₀ k hk
    have hk2 : 2 ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
    have hkN₁ : N₁ ≤ k := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
    have hkN₂ : N₂ ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
    have hkN₃ : N₃ ≤ k := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
    have hDtk : ∀ t ∈ Icc (endA k) (2 * endA k), IsStrongExpMetric d t (distExp d t) (Dt t) :=
      fun t ht => hDt t (hblock k hk ht)
    have hpos : ∀ t ∈ Icc (endA k) (2 * endA k), 0 < t := fun t ht => (endA_pos k).trans_le ht.1
    have hm1' : ∀ t ∈ Icc (endA k) (2 * endA k),
        ∫⁻ g, supDistLU d R (rho (Dt t) g).1 (euclidDistC d) ^ ((4 * (L + 2) : ℕ) : ℝ)
            ∂(normLGFLaw d) ≤
          ENNReal.ofReal (C₁ * t ^ ((3 / 4 : ℝ) * ((4 * (L + 2) : ℕ) : ℝ))) := by
      intro t ht
      have h := hm1 t ⟨hpos t ht, ht.2.trans (hr.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
        (Dt t) (hDtk t ht) 1 (Or.inl rfl)
      rwa [pinLaw_one (by omega)] at h
    have hm2' : ∀ t ∈ Icc (endA k) (2 * endA k),
        ∫⁻ g, supDistLU d 1 (rho (Dt t) g).1 (euclidDistC d) ^ (4 : ℝ) ∂(pinLaw d 10) ≤
          ENNReal.ofReal (C₂ * t ^ ((3 / 4 : ℝ) * 4)) := fun t ht =>
      hm2 t ⟨hpos t ht, ht.2.trans (hr.trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
        (Dt t) (hDtk t ht) 10 (Or.inr rfl)
    exact measure_endBad_le h37 hC hc hc' hC₁ hC₂ (by omega) (hr.trans (min_le_left _ _)) hDtk hm1' hm2'
      hs (hk₄ k (le_trans (le_max_left _ _) hk45)) (hk₅ k (le_trans (le_max_right _ _) hk45))
      fun j => ⟨hN₁ k j (by omega), hN₂ k j (by omega), hN₃ k j (by omega)⟩
  -- Borel–Cantelli
  have hsummable : Summable fun k : ℕ => K * (1 / 2 : ℝ) ^ (k + k₀) := by
    simp_rw [pow_add]
    exact (summable_geometric_two.mul_right _).mul_left K
  have hsum : ∑' k : ℕ, normLGFLaw d (endBad Dt R L D (k + k₀)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun k => hbad (k + k₀) (by omega))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsummable]
    exact ENNReal.ofReal_ne_top
  have hBC := ae_eventually_notMem hsum
  -- the version event at the nodes
  have hver : ∀ᵐ g ∂(normLGFLaw d), ∀ k q m : ℕ, endNode k q m ∈ subcritSet d →
      X (endNode k q m) g = (rho (Dt (endNode k q m)) g).1 := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro q
    rw [ae_all_iff]
    intro m
    by_cases ht : endNode k q m ∈ subcritSet d
    · filter_upwards [hX.2.1 _ ht.1 ht.2 (Dt _) (hDt _ ht)] with g hg _ using hg
    · exact Eventually.of_forall fun g h => absurd h ht
  filter_upwards [hBC, hver, hX.2.2] with g hg hverg hcont
  obtain ⟨k', hk'⟩ := eventually_atTop.1 hg
  refine ⟨k' + k₀, fun k hk => ?_⟩
  have hk0 : k₀ ≤ k := by omega
  have hnb : g ∉ endBad Dt R L D k := by
    have := hk' (k - k₀) (by omega)
    rwa [Nat.sub_add_cancel hk0] at this
  have hk2 : 2 ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (hk₀ k hk0).2.2.1)
  have hnode : ∀ q m : ℕ, m ≤ 2 ^ q → X (endNode k q m) g = (rho (Dt (endNode k q m)) g).1 :=
    fun q m hm => hverg k q m (hblock k hk0 (endNode_mem hm))
  simp only [endBad, mem_union, not_or] at hnb
  obtain ⟨⟨hnbase, hnbridge⟩, hnfine⟩ := hnb
  have hD1 : 1 ≤ D := one_le_endDexp B M
  refine supd_profile_le_of_not_endBad (F := fun ξ => X ξ g) (qb := L * k) (q := endLevel D k)
    (endEps_pos k).le (endEps_le_half hk2) (fun j => le_trans (by omega) (le_endLevel hD1 k j))
    ((hcont.mono fun t ht => hblock k hk0 ht)) ?_ ?_ ?_ ?_
  · intro j m hm p
    rw [hnode _ _ hm]
    exact ContMetric.nonneg _ p.1 p.2
  · intro m hm
    have h := endpt_not_mem_of_not_mem_biUnion hnbase m hm
    simp only [mem_ofPred_eq, not_lt] at h
    rw [hnode _ _ hm]
    exact h
  · intro m hm
    have h := endpt_not_mem_of_not_mem_biUnion hnbridge m hm
    simp only [mem_ofPred_eq, not_lt] at h
    rw [hnode _ _ (endPar_le hm), hnode _ _ hm]
    exact h
  · intro j m hm
    have h0 : g ∉ ⋃ m ∈ Finset.range (2 ^ endLevel D k (j + 1) + 1),
        {g | ENNReal.ofReal (endDelta k j) <
          supDistLU d R
            (logProfile (rho (Dt (endNode k (endLevel D k j)
              (endPar (endLevel D k (j + 1)) (endLevel D k j) m))) g).1)
            (logProfile (rho (Dt (endNode k (endLevel D k (j + 1)) m)) g).1)} := fun hmem =>
      hnfine (mem_iUnion.2 ⟨j, hmem⟩)
    have h := endpt_not_mem_of_not_mem_biUnion h0 m hm
    simp only [mem_ofPred_eq, not_lt] at h
    rw [hnode _ _ (endPar_le hm), hnode _ _ hm]
    exact h

/-- The block bounds of `endpt_key`, almost surely simultaneously for every radius. -/
theorem endpt_ae_blocks {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d) (hL : MarginalEuclidStmt d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ R : ℕ, 1 ≤ R → ∃ k₁ : ℕ, ∀ k ≥ k₁,
      ∀ ξ ∈ Icc (endA k) (2 * endA k), ∀ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
        |X ξ g p - euclidDistC d p| ≤ 4 * (1 + 2 * R) * endEps k := by
  obtain ⟨ξ₀, hξ₀, hsub⟩ := exists_Ioo_subset_subcritSet (d := d) (by omega)
  obtain ⟨Dt, hDt⟩ := endpt_exists_strong hd
  have hξb : ξ₀ / 2 ∈ subcritSet d := hsub ⟨by positivity, by linarith⟩
  have hsub' : ∀ t, 0 < t → t ≤ ξ₀ / 2 → t ∈ subcritSet d := fun t ht0 ht => hsub ⟨ht0, by linarith⟩
  rw [ae_all_iff]
  intro R
  by_cases hR : 1 ≤ R
  · filter_upwards [endpt_key hd hP hL hX hDt hξb hsub' R hR] with g hg _ using hg
  · exact Eventually.of_forall fun g h => absurd h hR

/-- **The Euclidean endpoint (5.8)** (Part C `c:thm-endpoint`; NA4 A6). -/
theorem endpoint_of {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d) (hL : MarginalEuclidStmt d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X) : EndpointStmt d X := by
  filter_upwards [endpt_ae_blocks hd hP hL hX] with g hg
  exact endpt_tendsto_of_blocks (fun ξ hξ => hξ.1) fun R hR => ⟨_, hg R hR⟩

/-- **The rate of the endpoint** (the quantitative clause of `c:thm-endpoint`, with the constant `4(1 + 2R)` in place
of `2e(1 + 2R)`): for a.e. `g` and every integer `R ≥ 1` there is `ξ_R(g) > 0` with
`supd_R(X ξ g, eu) ≤ 4(1 + 2R)√ξ` for every `ξ ∈ (0, ξ_R(g)]`. -/
theorem endpoint_rate_of {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d) (hL : MarginalEuclidStmt d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ R : ℕ, 1 ≤ R → ∃ ξR : ℝ, 0 < ξR ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξR,
      supDistLU d R (X ξ g) (euclidDistC d) ≤ ENNReal.ofReal (4 * (1 + 2 * R) * Real.sqrt ξ) := by
  filter_upwards [endpt_ae_blocks hd hP hL hX] with g hg
  intro R hR
  obtain ⟨k₁, hk₁⟩ := hg R hR
  exact endpt_rate_of_blocks (by positivity) hk₁

end HigherDimLQGContinuity
