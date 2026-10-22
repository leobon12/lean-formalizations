import HigherDimLQGMetric.Trap.StableLemmas

/-!
# Stability of (ii) along sequences ([S] Lemma 4.2, MA1 A17 "Stability (ii)")

Packet S3. `trap_stable_ii_seq` is the sequential argument of MA1 A17: coordinate pairs
`p k = (ζ'_k, ζ̃'_k)` of a family with uniform lower modulus and uniform local realization
(MA1 A4 (P1)–(P2)) converge to the base pair `(ζ, ζ̃)` uniformly on `closure A`; `Q k` are
`(w·ζ'_k)`-minimizers between collector points with `ζ'_k(Q k 0, Q k 1) ≥ b`. Then some `Q k`
already has a marked shortcut (ratio `c'`, weighted length `≥ c`, inside `A`). Steps:

1. confinement (C): the `Q k` lie in `Y₀` (measured with `ζ`);
2. constant weighted speed `L_k` on `[0, 1]` (`trap_coord_weighted_param`);
3. a subsequence with converging endpoints; Lemma 2.5′(b) (M2a `lemma25b`, with (H) from (C))
   gives a uniform limit `Q` which is a `(w·ζ)`-minimizer, and `ζ(x, y) ≥ b ≥ b/2`;
4. (ii) for the base configuration gives `u ≤ v` with `∫_{Q|[u,v]} w ds_ζ ≥ 2c` and a shortcut `S`
   in `Y′` of ratio `≤ ĉ`;
5. lower semicontinuity (M2a `coordinate_weightedLength_le_liminf`) bounds the `ζ'_k`-weighted
   length of `Q k|[u,v]` from below, Lemma 2.4 (`trap_uniform_recovery`) recovers `S` for `ζ̃'_k`,
   and uniform local realization (P2) gives short connections from `Q k(u)`, `Q k(v)` to
   `Q(u)`, `Q(v)`; the strict margin `(c' - ĉ) ∫_{Q|[u,v]} w ds_ζ` absorbs all errors.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- `ofReal m * a ≤ ofReal X` with `m > 0`, `X ≥ 0` gives `a ≤ ofReal (X / m)`. -/
theorem trap_le_ofReal_div {m X : ℝ} {a : ℝ≥0∞} (hm : 0 < m) (hX : 0 ≤ X)
    (h : ENNReal.ofReal m * a ≤ ENNReal.ofReal X) : a ≤ ENNReal.ofReal (X / m) := by
  rcases eq_or_ne a ⊤ with htop | hfin
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hm).ne'] at h
    exact absurd h (not_le.2 ENNReal.ofReal_lt_top)
  · rw [← ENNReal.ofReal_toReal hfin] at h ⊢
    rw [← ENNReal.ofReal_mul hm.le, ENNReal.ofReal_le_ofReal_iff hX] at h
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ hm]
    linarith

/-- Uniform closeness `≤ 1/(k+1)` along an index `ix n ≥ n` gives uniform convergence. -/
theorem trap_tendstoUniformlyOn_of_close {X : Type*} {F : ℕ → X × X → ℝ} {f : X × X → ℝ}
    {C : Set X} (hclose : ∀ k, ∀ x ∈ C, ∀ y ∈ C, |F k (x, y) - f (x, y)| ≤ 1 / (k + 1))
    {ix : ℕ → ℕ} (hix : ∀ n, n ≤ ix n) :
    TendstoUniformlyOn (fun n => F (ix n)) f atTop (C ×ˢ C) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine Filter.eventually_atTop.2 ⟨N, fun n hn q hq => ?_⟩
  have h1 := hclose (ix n) q.1 hq.1 q.2 hq.2
  have h2 : (1 : ℝ) / ((ix n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) ≤ ix n := by exact_mod_cast hn.trans (hix n)
    linarith
  rw [Real.dist_eq, abs_sub_comm]
  exact h1.trans_lt (h2.trans_lt hN)

/-- **Stability of (ii) along a sequence** (MA1 A17): if coordinate pairs `p k` of the family
converge to the base pair uniformly on `closure A` (closeness `≤ 1/(k+1)`), keep a collar `2 a_col`,
and `Q k` are `(w·(p k).1)`-minimizers between collector points at `(p k).1`-distance `≥ b`, then
some `Q k` has a subcurve of weighted length `≥ c` with a shortcut of ratio `≤ c'` inside `A`. -/
theorem trap_stable_ii_seq {X : Type*} [MetricSpace X]
    (Fam : Set ((X × X → ℝ) × (X × X → ℝ)))
    (hFam : ∀ p ∈ Fam, IsCoordinate p.1 ∧ IsCoordinate p.2)
    (hFmod : ∀ L : Set X, IsCompact L → ∀ χ : ℝ, 0 < χ → ∃ m : ℝ, 0 < m ∧
      ∀ p ∈ Fam, ∀ u ∈ L, ∀ v ∈ L, (p.1 (u, v) < m → dist u v < χ) ∧
        (p.2 (u, v) < m → dist u v < χ))
    (hFloc : ∀ K₀ O : Set X, IsCompact K₀ → IsOpen O → K₀ ⊆ O → IsCompact (closure O) →
      ∃ a : ℝ, 0 < a ∧ ∀ p ∈ Fam, ∀ x ∈ K₀, ∀ y ∈ K₀,
        (p.1 (x, y) < a → ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
          curveLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v)))
            (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (p.1 (x, y))) ∧
        (p.2 (x, y) < a → ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
          curveLengthWith (fun u v => ENNReal.ofReal (p.2 (u, v)))
            (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (p.2 (x, y))))
    {ζ ζt : X × X → ℝ} (hζ : IsCoordinate ζ) (hbase : (ζ, ζt) ∈ Fam)
    {A V : Set X} (hA : IsOpen A) (hAc : IsCompact (closure A)) (hV : IsOpen V)
    (hVA : closure V ⊆ A)
    {w : X → ℝ} (hwc : Continuous w) (hwpos : ∀ x, 0 < w x) (hw1 : ∀ x, w x ≤ 1)
    (hwV : ∀ x, x ∉ V → w x = 1)
    {acol b ε₀ c ĉ c' : ℝ}
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, 4 * acol ≤ ζ (x, y))
    (hb : 0 < b) (hε₀ : 0 < ε₀) (hε₀col : ε₀ < acol / 12) (hc : 0 < c) (hĉ0 : 0 ≤ ĉ)
    (hĉc' : ĉ < c')
    (hY₀ : ∀ x ∈ closure V, ∀ y ∈ closure V,
      weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w
        (coordTrapSet hζ.metric A V (acol / 2)) x y < ENNReal.ofReal (3 * ε₀))
    (hbaseii : ∀ Q : ℝ → X, ContinuousOn Q (Icc 0 1) → Q 0 ∈ closure V → Q 1 ∈ closure V →
      weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Q 0 1 =
        weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w univ (Q 0) (Q 1) →
      b / 2 ≤ ζ (Q 0, Q 1) →
      ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
        ENNReal.ofReal (2 * c) ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Q u v ∧
        ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧
          MapsTo S (Icc 0 1) (coordTrapSet hζ.metric A V acol) ∧
          weightedLengthWith (fun u v => ENNReal.ofReal (ζt (u, v))) w S 0 1 ≤
            ENNReal.ofReal ĉ * weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Q u v)
    (p : ℕ → (X × X → ℝ) × (X × X → ℝ)) (hpF : ∀ k, p k ∈ Fam)
    (hpclose : ∀ k, ∀ x ∈ closure A, ∀ y ∈ closure A,
      |(p k).1 (x, y) - ζ (x, y)| ≤ 1 / (k + 1) ∧ |(p k).2 (x, y) - ζt (x, y)| ≤ 1 / (k + 1))
    (hpclose8 : ∀ k, ∀ x ∈ closure A, ∀ y ∈ closure A, |(p k).1 (x, y) - ζ (x, y)| ≤ acol / 8)
    (hpcol : ∀ k, ∀ x ∈ closure V, ∀ y ∈ frontier A, 2 * acol ≤ (p k).1 (x, y))
    (Q : ℕ → ℝ → X) (hQc : ∀ k, ContinuousOn (Q k) (Icc 0 1)) (hQ0 : ∀ k, Q k 0 ∈ closure V)
    (hQ1 : ∀ k, Q k 1 ∈ closure V)
    (hQmin : ∀ k, weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w (Q k) 0 1 =
      weylDistOnWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w univ (Q k 0) (Q k 1))
    (hQcost : ∀ k, weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w (Q k) 0 1 <
      ENNReal.ofReal (3 * ε₀))
    (hQb : ∀ k, b ≤ (p k).1 (Q k 0, Q k 1)) :
    ∃ k, ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
      ENNReal.ofReal c ≤ weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w (Q k) u v ∧
      ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧ S 0 = Q k u ∧ S 1 = Q k v ∧ MapsTo S (Icc 0 1) A ∧
        weightedLengthWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w S 0 1 ≤
          ENNReal.ofReal c' *
            weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w (Q k) u v := by
  have hacol : 0 < acol := by linarith
  have hρ : ∀ k, IsCoordinate (p k).1 := fun k => (hFam _ (hpF k)).1
  have hρt : ∀ k, IsCoordinate (p k).2 := fun k => (hFam _ (hpF k)).2
  have hζt : IsCoordinate ζt := (hFam _ hbase).2
  -- the confinement sets
  set Y₀ := coordTrapSet hζ.metric A V (acol / 2) with hY₀_def
  set Y' := coordTrapSet hζ.metric A V acol with hY'_def
  set O₁ := coordTrapOpen hζ.metric A V (3 * acol / 4) with hO₁_def
  set O₂ := coordTrapOpen hζ.metric A V (3 * acol / 2) with hO₂_def
  have hVne : (closure V).Nonempty := ⟨Q 0 0, hQ0 0⟩
  have hVc : IsCompact (closure V) :=
    hAc.of_isClosed_subset isClosed_closure (hVA.trans subset_closure)
  have hY₀c : IsCompact Y₀ := hζ.isCompact_coordTrapSet hAc
  have hY'c : IsCompact Y' := hζ.isCompact_coordTrapSet hAc
  have hY₀O₁ : Y₀ ⊆ O₁ :=
    coordTrapSet_subset_coordTrapOpen hζ.metric hA hVne hcol (by linarith) (by linarith)
  have hO₁Y' : closure O₁ ⊆ Y' :=
    hζ.closure_coordTrapOpen_subset.trans (coordTrapSet_mono hζ.metric (by linarith))
  have hO₁c : IsCompact (closure O₁) := hY'c.of_isClosed_subset isClosed_closure hO₁Y'
  have hY'O₂ : Y' ⊆ O₂ :=
    coordTrapSet_subset_coordTrapOpen hζ.metric hA hVne hcol (by linarith) (by linarith)
  have hO₂A : closure O₂ ⊆ A :=
    hζ.closure_coordTrapOpen_subset.trans (coordTrapSet_subset hζ.metric hA hVne hcol (by linarith))
  have hO₂c : IsCompact (closure O₂) :=
    hAc.of_isClosed_subset isClosed_closure (hO₂A.trans subset_closure)
  have hO₂cA : closure O₂ ⊆ closure A := hO₂A.trans subset_closure
  have hVY₀ : closure V ⊆ Y₀ := closure_subset_coordTrapSet hζ.metric hVA (by linarith)
  have hY₀Y' : Y₀ ⊆ Y' := coordTrapSet_mono hζ.metric (by linarith)
  have hY'cA : Y' ⊆ closure A := fun x hx => hx.1
  have hVcA : closure V ⊆ closure A := hVA.trans subset_closure
  -- the weight is bounded below on `closure A`
  obtain ⟨mw, hmw, hmwle⟩ : ∃ mw : ℝ, 0 < mw ∧ ∀ x ∈ closure A, mw ≤ w x := by
    rcases (closure A).eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun x hx => by rw [hemp] at hx; exact absurd hx (notMem_empty x)⟩
    obtain ⟨z, hz, hmin⟩ := hAc.exists_isMinOn hne hwc.continuousOn
    exact ⟨w z, hwpos z, fun x hx => hmin hx⟩
  -- Step 1: the minimizers stay in `Y₀`
  have hcol3 : ∀ k, ∀ x ∈ closure V, ∀ y ∈ frontier A, 3 * ε₀ ≤ (p k).1 (x, y) :=
    fun k x hx y hy => le_trans (by linarith) (hpcol k x hx y hy)
  have hQY₀ : ∀ k, MapsTo (Q k) (Icc 0 1) Y₀ := by
    intro k
    have h := (trap_coord_mapsTo (hρ k) hζ hA hV hVA hwV (hcol3 k) (hpclose8 k) (hQc k) (hQ0 k)
      (hQcost k)).2
    exact h.mono_right (coordTrapSet_mono hζ.metric (by linarith))
  -- Step 2: the costs are positive
  have hWpos : ∀ k, 0 < (weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w
      (Q k) 0 1).toReal := by
    intro k
    have hfin := ne_top_of_lt (hQcost k)
    have h1 := ofReal_mul_curveLengthWith_le_weightedLengthWith
      (δ := fun u v => ENNReal.ofReal ((p k).1 (u, v))) (w := w) (P := Q k) zero_le_one
      (fun t ht => hmwle _ (hY'cA (hY₀Y' (hQY₀ k ht))))
    have h2 : ENNReal.ofReal ((p k).1 (Q k 0, Q k 1)) ≤
        curveLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) (Q k) 0 1 :=
      le_curveLengthWith (δ := fun u v => ENNReal.ofReal ((p k).1 (u, v))) zero_le_one
    have h3 : ENNReal.ofReal (mw * b) ≤
        weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w (Q k) 0 1 := by
      calc ENNReal.ofReal (mw * b) = ENNReal.ofReal mw * ENNReal.ofReal b :=
            ENNReal.ofReal_mul hmw.le
        _ ≤ ENNReal.ofReal mw * ENNReal.ofReal ((p k).1 (Q k 0, Q k 1)) :=
            mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hQb k))
        _ ≤ _ := (mul_le_mul' le_rfl h2).trans h1
    have h4 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h3
    exact (mul_pos hmw hb).trans_le h4
  -- Step 3: constant weighted speed
  have hparam := fun k => trap_coord_weighted_param (hρ k) hwc hwpos (hQc k)
    (ne_top_of_lt (hQcost k)) (hWpos k)
  choose Qh hQhc hQh0 hQh1 hQhS hQhparam hQhcorr using hparam
  have hQhY₀ : ∀ k, MapsTo (Qh k) (Icc 0 1) Y₀ := by
    intro k t ht
    obtain ⟨r, hr, hrQ⟩ := hQhS k ht
    rw [← hrQ]
    exact hQY₀ k hr
  -- Step 4: endpoints converge along a subsequence
  obtain ⟨⟨x, y⟩, hxyV, ψ, hψ, hψlim⟩ := (hVc.prod hVc).tendsto_subseq
    (x := fun k => (Q k 0, Q k 1)) (fun k => ⟨hQ0 k, hQ1 k⟩)
  have hx : x ∈ closure V := hxyV.1
  have hy : y ∈ closure V := hxyV.2
  have hxn : Tendsto (fun n => Q (ψ n) 0) atTop (𝓝 x) :=
    ((continuous_fst.tendsto _).comp hψlim)
  have hyn : Tendsto (fun n => Q (ψ n) 1) atTop (𝓝 y) :=
    ((continuous_snd.tendsto _).comp hψlim)
  have hψid : ∀ n, n ≤ ψ n := hψ.id_le
  have hconvA : TendstoUniformlyOn (fun n => (p (ψ n)).1) ζ atTop (closure A ×ˢ closure A) :=
    trap_tendstoUniformlyOn_of_close (fun k x hx y hy => (hpclose k x hx y hy).1) hψid
  -- Step 5: Lemma 2.5′(b) gives a limiting minimizer
  obtain ⟨δloc₁, hδloc₁, hloc₁⟩ :=
    hFloc Y₀ O₁ hY₀c (hζ.isOpen_coordTrapOpen hA) hY₀O₁ hO₁c
  have hmodY' : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      (∀ n, ∀ u ∈ Y', ∀ v ∈ Y', (p (ψ n)).1 (u, v) < b → dist u v < χ) ∧
      (∀ u ∈ Y', ∀ v ∈ Y', ζ (u, v) < b → dist u v < χ) := by
    intro χ hχ
    obtain ⟨m, hm, hmm⟩ := hFmod Y' hY'c χ hχ
    exact ⟨m, hm, fun n u hu v hv => (hmm _ (hpF (ψ n)) u hu v hv).1,
      fun u hu v hv => (hmm _ hbase u hu v hv).1⟩
  have hY₀eq : ∀ S : Set X, Y₀ ⊆ S → ∀ a ∈ closure V, ∀ b ∈ closure V,
      weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w S a b =
        weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Y₀ a b :=
    fun S hS a ha b hb => trap_coord_weyl_eq hζ hA hV hVA hwV hcol hε₀ (by linarith) hS ha
      (hY₀ a ha b hb)
  have hH : ∀ a ∈ closure V, ∀ b ∈ closure V,
      weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Y' a b =
        weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Y₀ a b :=
    hY₀eq Y' hY₀Y'
  have hfin : ∀ a ∈ closure V, ∀ b ∈ closure V,
      weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Y' a b ≠ ⊤ :=
    fun a ha b hb => by rw [hH a ha b hb]; exact ne_top_of_lt (hY₀ a ha b hb)
  set P : ℕ → I →ᵇ X := fun n => trapCurveBCF (Qh (ψ n)) (hQhc (ψ n)) with hP_def
  have hPY : ∀ n t, P n t ∈ Y' := fun n t => hY₀Y' (hQhY₀ (ψ n) t.2)
  have hPext : ∀ n, EqOn (Set.IccExtend zero_le_one (P n)) (Qh (ψ n)) (Icc 0 1) :=
    fun n => trapCurveBCF_extend _ _
  have hP0 : ∀ n, P n 0 = Q (ψ n) 0 := fun n => hQh0 (ψ n)
  have hP1 : ∀ n, P n 1 = Q (ψ n) 1 := fun n => hQh1 (ψ n)
  have hspeed : ∀ n : ℕ, ∀ s t : I, (s : ℝ) ≤ t →
      weightedLengthWith (fun u v => ENNReal.ofReal ((p (ψ n)).1 (u, v))) w
        (Set.IccExtend zero_le_one (P n)) s t ≤
      weightedLengthWith (fun u v => ENNReal.ofReal ((p (ψ n)).1 (u, v))) w
        (Set.IccExtend zero_le_one (P n)) 0 1 * ENNReal.ofReal ((t : ℝ) - s) := by
    intro n s t hst
    rw [weightedLengthWith_congr_path ((hPext n).mono (Icc_subset_Icc s.2.1 t.2.2)),
      weightedLengthWith_congr_path (hPext n), hQhparam _ _ _ s.2.1 hst t.2.2,
      hQhparam _ 0 1 le_rfl zero_le_one le_rfl, sub_zero, mul_one,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  have hcost' : ∀ n, weightedLengthWith (fun u v => ENNReal.ofReal ((p (ψ n)).1 (u, v))) w
      (Set.IccExtend zero_le_one (P n)) 0 1 ≤
      weylDistOnWith (fun u v => ENNReal.ofReal ((p (ψ n)).1 (u, v))) w Y'
        (Q (ψ n) 0) (Q (ψ n) 1) + ENNReal.ofReal ((fun _ : ℕ => (0 : ℝ)) n) := by
    intro n
    rw [weightedLengthWith_congr_path (hPext n), hQhparam _ 0 1 le_rfl zero_le_one le_rfl,
      sub_zero, mul_one, ENNReal.ofReal_toReal (ne_top_of_lt (hQcost (ψ n))),
      ENNReal.ofReal_zero, add_zero, hQmin]
    exact weylDistOnWith_anti_set _ _ (subset_univ _) _ _
  obtain ⟨Qs, hQsY', hQs0, hQs1, hQsmin, φ, hφ, hφlim⟩ :=
    lemma25b (fun n => (p (ψ n)).1) ζ (fun n => hρ (ψ n)) hζ w hVc hY'c hVY₀
      (hY₀O₁.trans subset_closure) hO₁Y' hO₁c hwc.continuousOn (fun z _ => hwpos z)
      (hconvA.mono (prod_mono hY'cA hY'cA)) hmodY' hδloc₁
      (fun n a ha b hb hab => (hloc₁ _ (hpF (ψ n)) a ha b hb).1 hab)
      (fun a ha b hb hab => (hloc₁ _ hbase a ha b hb).1 hab) hH hfin
      (fun n => Q (ψ n) 0) (fun n => Q (ψ n) 1) x y (fun n => ⟨hQ0 _, hQ1 _⟩) hx hy hxn hyn
      P hPY hP0 hP1 hspeed (fun _ => 0) tendsto_const_nhds hcost'
  -- Step 6: the limit is a `(w·ζ)`-minimizer over the whole space, at `ζ`-distance `≥ b`
  set Qt : ℝ → X := Set.IccExtend zero_le_one Qs with hQt_def
  have hQtc : ContinuousOn Qt (Icc 0 1) :=
    (continuous_IccExtend_iff.mpr Qs.continuous).continuousOn
  have hQtI : ∀ t : I, Qt t = Qs t := fun t => by
    rw [hQt_def, Set.IccExtend_of_mem _ _ t.2]
  have hQt0 : Qt 0 = x := by rw [← hQs0]; exact hQtI 0
  have hQt1 : Qt 1 = y := by rw [← hQs1]; exact hQtI 1
  have hQtY' : MapsTo Qt (Icc 0 1) Y' := fun t ht => by
    rw [hQt_def, Set.IccExtend_of_mem _ _ ht]
    exact hQsY' _
  have hQtmin : weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Qt 0 1 =
      weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w univ (Qt 0) (Qt 1) := by
    rw [hQt0, hQt1, hY₀eq univ (subset_univ _) x hx y hy, ← hH x hx y hy, ← hQsmin]
  have hxyb : b ≤ ζ (x, y) := by
    have hlim := coordinate_moving_pair_tendsto (fun n => (p (ψ n)).1) ζ hζ hconvA
      (fun n => Q (ψ n) 0) (fun n => Q (ψ n) 1) x y hxn hyn (hVcA hx) (hVcA hy)
      (fun n => ⟨hVcA (hQ0 _), hVcA (hQ1 _)⟩)
    exact ge_of_tendsto' hlim fun n => hQb (ψ n)
  -- Step 7: (ii) for the base configuration at the limit
  obtain ⟨u, v, hu, huv, hv, hcost2c, S, hSc, hS0, hS1, hSY', hSb⟩ :=
    hbaseii Qt hQtc (hQt0 ▸ hx) (hQt1 ▸ hy) hQtmin
      (by rw [hQt0, hQt1]; linarith)
  have hQtfin : weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Qt 0 1 ≠ ⊤ := by
    rw [hQtmin, hQt0, hQt1, hY₀eq univ (subset_univ _) x hx y hy]
    exact ne_top_of_lt (hY₀ x hx y hy)
  obtain ⟨G, hGeq⟩ : ∃ G : ℝ≥0∞,
      weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Qt u v = G := ⟨_, rfl⟩
  rw [hGeq] at hcost2c hSb
  have hGfin : G ≠ ⊤ :=
    hGeq ▸ ne_top_of_le_ne_top hQtfin (trap_weightedLengthWith_mono_interval hu huv hv)
  have hG2c : 2 * c ≤ G.toReal := (ENNReal.ofReal_le_iff_le_toReal hGfin).1 hcost2c
  obtain ⟨Gr, hGr_def⟩ : ∃ Gr : ℝ, G.toReal = Gr := ⟨_, rfl⟩
  rw [hGr_def] at hG2c
  have hGofReal : G = ENNReal.ofReal Gr := by rw [← hGr_def, ENNReal.ofReal_toReal hGfin]
  have hGr : 0 < Gr := by linarith
  have hc'pos : 0 < c' := lt_of_le_of_lt hĉ0 hĉc'
  set Δ := (c' - ĉ) * Gr with hΔ_def
  have hΔ : 0 < Δ := mul_pos (by linarith) hGr
  set η'' := min c (Δ / (4 * c')) with hη''_def
  have hη'' : 0 < η'' := lt_min hc (by positivity)
  have hη''c : η'' ≤ c := min_le_left _ _
  have hη''Δ : c' * η'' ≤ Δ / 4 := by
    have h := min_le_right c (Δ / (4 * c'))
    calc c' * η'' ≤ c' * (Δ / (4 * c')) := mul_le_mul_of_nonneg_left h hc'pos.le
      _ = Δ / 4 := by field_simp
  -- Step 8: lower semicontinuity of the weighted length on `[u, v]`
  have hlsc := coordinate_weightedLength_le_liminf hY'c zero_le_one hζ.continuous.continuousOn
    (hconvA.mono (prod_mono hY'cA hY'cA)) P Qs φ hφ hPY hQsY' hφlim w hwc.continuousOn hu huv hv
  have hlsc' : G ≤ liminf (fun n => weightedLengthWith
      (fun u v => ENNReal.ofReal ((p (ψ (φ n))).1 (u, v))) w (Qh (ψ (φ n))) u v) atTop := by
    have hlsc0 : weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Qt u v ≤ _ := hlsc
    rw [hGeq] at hlsc0
    refine hlsc0.trans (le_of_eq ?_)
    congr 1
    funext n
    exact weightedLengthWith_congr_path ((hPext (φ n)).mono (Icc_subset_Icc hu hv))
  have hev1 : ∀ᶠ n in atTop, ENNReal.ofReal (Gr - η'') < weightedLengthWith
      (fun u v => ENNReal.ofReal ((p (ψ (φ n))).1 (u, v))) w (Qh (ψ (φ n))) u v := by
    have hlt : ENNReal.ofReal (Gr - η'') < liminf (fun n => weightedLengthWith
        (fun u v => ENNReal.ofReal ((p (ψ (φ n))).1 (u, v))) w (Qh (ψ (φ n))) u v) atTop := by
      refine lt_of_lt_of_le ?_ hlsc'
      rw [hGofReal]
      exact (ENNReal.ofReal_lt_ofReal_iff hGr).2 (by linarith)
    exact eventually_lt_of_lt_liminf hlt
  -- Step 9: recovery of the shortcut for the comparison coordinates
  have hSlen : curveLengthWith (fun u v => ENNReal.ofReal (ζt (u, v))) S 0 1 ≤
      ENNReal.ofReal (ĉ * Gr / mw) := by
    apply trap_le_ofReal_div hmw (by positivity)
    calc ENNReal.ofReal mw * curveLengthWith (fun u v => ENNReal.ofReal (ζt (u, v))) S 0 1
        ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ζt (u, v))) w S 0 1 :=
          ofReal_mul_curveLengthWith_le_weightedLengthWith zero_le_one
            (fun t ht => hmwle _ (hY'cA (hSY' ht)))
      _ ≤ ENNReal.ofReal ĉ * G := hSb
      _ = ENNReal.ofReal (ĉ * Gr) := by
          rw [hGofReal, ENNReal.ofReal_mul hĉ0]
  set Fam₂ : Set (X × X → ℝ) := Prod.snd '' Fam with hFam₂_def
  have hFam₂ : ∀ ρ' ∈ Fam₂, IsCoordinate ρ' := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hFam q hq).2
  have hζtF₂ : ζt ∈ Fam₂ := ⟨_, hbase, rfl⟩
  have hmod₂ : ∀ χ : ℝ, 0 < χ → ∃ m : ℝ, 0 < m ∧
      ∀ ρ' ∈ Fam₂, ∀ u ∈ closure O₂, ∀ v ∈ closure O₂, ρ' (u, v) < m → dist u v < χ := by
    intro χ hχ
    obtain ⟨m, hm, hmm⟩ := hFmod (closure O₂) hO₂c χ hχ
    refine ⟨m, hm, ?_⟩
    rintro _ ⟨q, hq, rfl⟩ u hu v hv huv
    exact (hmm q hq u hu v hv).2 huv
  obtain ⟨a₂, ha₂, hloc₂⟩ :=
    hFloc Y' O₂ hY'c (hζ.isOpen_coordTrapOpen hA) hY'O₂ hO₂c
  have hloc₂' : ∃ δloc : ℝ, 0 < δloc ∧ ∀ ρ' ∈ Fam₂, ∀ x ∈ Y', ∀ y ∈ Y', ρ' (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O₂) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ' (x, y)) := by
    refine ⟨a₂, ha₂, ?_⟩
    rintro _ ⟨q, hq, rfl⟩ x hx y hy hxy
    exact (hloc₂ q hq x hx y hy).2 hxy
  obtain ⟨eS, heS, hrecS⟩ := trap_uniform_recovery Fam₂ hFam₂ hζtF₂ hY'O₂ hO₂c
    hwc.continuousOn (fun z _ => (hwpos z).le) hmod₂ hloc₂' (L₀ := ĉ * Gr / mw)
    (η := Δ / 4) (by positivity) (by positivity)
  have hev2 : ∀ᶠ n in atTop, 1 / ((ψ (φ n) : ℝ) + 1) ≤ eS := by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt heS
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hle : (N : ℝ) ≤ ψ (φ n) := by exact_mod_cast hn.trans ((hφ.id_le n).trans (hψid _))
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans hN.le
  -- Step 10: short connections at the two ends
  have hconvAt : TendstoUniformlyOn (fun n => (p (ψ (φ n))).2) ζt atTop
      (closure A ×ˢ closure A) :=
    trap_tendstoUniformlyOn_of_close (fun k x hx y hy => (hpclose k x hx y hy).2)
      (fun n => (hφ.id_le n).trans (hψid _))
  have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu, huv.trans hv⟩
  have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨hu.trans huv, hv⟩
  have hptconv : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => Qh (ψ (φ n)) t) atTop (𝓝 (Qt t)) := by
    intro t ht
    have h := hφlim.tendsto_at (⟨t, ht⟩ : I)
    rw [hQt_def, Set.IccExtend_of_mem _ _ ht]
    exact h
  have hQhA : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, Qh k t ∈ closure A :=
    fun k t ht => hY'cA (hY₀Y' (hQhY₀ k ht))
  have hev3 : ∀ᶠ n in atTop, (p (ψ (φ n))).2 (Qh (ψ (φ n)) u, Qt u) < min a₂ (Δ / 8) := by
    have hlim := coordinate_moving_pair_tendsto (fun n => (p (ψ (φ n))).2) ζt hζt hconvAt
      (fun n => Qh (ψ (φ n)) u) (fun _ => Qt u) (Qt u) (Qt u) (hptconv u huI)
      tendsto_const_nhds (hY'cA (hQtY' huI)) (hY'cA (hQtY' huI))
      (fun n => ⟨hQhA _ u huI, hY'cA (hQtY' huI)⟩)
    rw [hζt.metric.self_eq_zero] at hlim
    exact hlim.eventually (gt_mem_nhds (lt_min ha₂ (by positivity)))
  have hev4 : ∀ᶠ n in atTop, (p (ψ (φ n))).2 (Qt v, Qh (ψ (φ n)) v) < min a₂ (Δ / 8) := by
    have hlim := coordinate_moving_pair_tendsto (fun n => (p (ψ (φ n))).2) ζt hζt hconvAt
      (fun _ => Qt v) (fun n => Qh (ψ (φ n)) v) (Qt v) (Qt v) tendsto_const_nhds
      (hptconv v hvI) (hY'cA (hQtY' hvI)) (hY'cA (hQtY' hvI))
      (fun n => ⟨hY'cA (hQtY' hvI), hQhA _ v hvI⟩)
    rw [hζt.metric.self_eq_zero] at hlim
    exact hlim.eventually (gt_mem_nhds (lt_min ha₂ (by positivity)))
  -- Step 11: one large index
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
  set k := ψ (φ n) with hk_def
  have hu'Y : Qh k u ∈ Y' := hY₀Y' (hQhY₀ k huI)
  have hv'Y : Qh k v ∈ Y' := hY₀Y' (hQhY₀ k hvI)
  have hQtuY : Qt u ∈ Y' := hQtY' huI
  have hQtvY : Qt v ∈ Y' := hQtY' hvI
  -- short realized connections cost at most their length
  have hconn : ∀ (R : I →ᵇ X) (a b : X), (∀ t, R t ∈ closure O₂) → R 0 = a → R 1 = b →
      curveLengthWith (fun u v => ENNReal.ofReal ((p k).2 (u, v)))
        (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal ((p k).2 (a, b)) →
      weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂) a b ≤
        ENNReal.ofReal ((p k).2 (a, b)) := by
    intro R a b hRO hR0 hR1 hRlen
    have hRc : ContinuousOn (Set.IccExtend zero_le_one R) (Icc 0 1) :=
      (continuous_IccExtend_iff.mpr R.continuous).continuousOn
    calc weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂) a b
        ≤ weightedLengthWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w
            (Set.IccExtend zero_le_one R) 0 1 :=
          weylDistOnWith_le hRc
            (by rw [Set.IccExtend_of_mem _ _ ⟨le_rfl, zero_le_one⟩]; exact hR0)
            (by rw [Set.IccExtend_of_mem _ _ ⟨zero_le_one, le_rfl⟩]; exact hR1)
            (fun t ht => by rw [Set.IccExtend_of_mem _ _ ht]; exact hRO _)
      _ ≤ ENNReal.ofReal 1 * curveLengthWith (fun u v => ENNReal.ofReal ((p k).2 (u, v)))
            (Set.IccExtend zero_le_one R) 0 1 :=
          weightedLengthWith_le_ofReal_mul_curveLengthWith fun t _ => hw1 _
      _ = ENNReal.ofReal ((p k).2 (a, b)) := by rw [hRlen, ENNReal.ofReal_one, one_mul]
  obtain ⟨Ru, hRuO, hRu0, hRu1, hRulen⟩ :=
    (hloc₂ _ (hpF k) _ hu'Y _ hQtuY).2 (hn3.trans_le (min_le_left _ _))
  obtain ⟨Rv, hRvO, hRv0, hRv1, hRvlen⟩ :=
    (hloc₂ _ (hpF k) _ hQtvY _ hv'Y).2 (hn4.trans_le (min_le_left _ _))
  have hcu := (hconn Ru _ _ hRuO hRu0 hRu1 hRulen).trans
    (ENNReal.ofReal_le_ofReal (hn3.le.trans (min_le_right _ _)))
  have hcv := (hconn Rv _ _ hRvO hRv0 hRv1 hRvlen).trans
    (ENNReal.ofReal_le_ofReal (hn4.le.trans (min_le_right _ _)))
  -- the recovered shortcut
  have hcloseS : ∀ u' ∈ closure O₂, ∀ v' ∈ closure O₂, |ζt (u', v') - (p k).2 (u', v')| ≤ eS := by
    intro u' hu' v' hv'
    have h := (hpclose k u' (hO₂cA hu') v' (hO₂cA hv')).2
    rw [abs_sub_comm]
    exact h.trans hn2
  have hrec := hrecS (p k).2 ⟨p k, hpF k, rfl⟩ hcloseS S hSc hSY' hSlen
  rw [hS0, hS1] at hrec
  have hSwl : weightedLengthWith (fun u v => ENNReal.ofReal (ζt (u, v))) w S 0 1 ≤
      ENNReal.ofReal (ĉ * Gr) := by
    rw [ENNReal.ofReal_mul hĉ0, ← hGofReal]
    exact hSb
  have htri : ∀ a b' d : X,
      weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂) a d ≤
        weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂) a b' +
        weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂) b' d :=
    fun a b' d => weylDistOnWith_triangle _
      (fun x y z => ofReal_metric_triangle (hρt k).metric x y z) w (closure O₂) a b' d
  have hΔeq : Δ = c' * Gr - ĉ * Gr := by rw [hΔ_def]; ring
  have hgap : 0 < Gr - η'' := by linarith
  have htot : weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂)
      (Qh k u) (Qh k v) < ENNReal.ofReal c' *
        weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w (Qh k) u v := by
    calc weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂)
          (Qh k u) (Qh k v)
        ≤ weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂)
            (Qh k u) (Qt u) +
          weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂)
            (Qt u) (Qt v) +
          weylDistOnWith (fun u v => ENNReal.ofReal ((p k).2 (u, v))) w (closure O₂)
            (Qt v) (Qh k v) :=
          (htri _ (Qt v) _).trans (add_le_add (htri _ _ _) le_rfl)
      _ ≤ ENNReal.ofReal (Δ / 8) + (ENNReal.ofReal (ĉ * Gr) + ENNReal.ofReal (Δ / 4)) +
            ENNReal.ofReal (Δ / 8) := by
          gcongr
          exact hrec.trans (add_le_add hSwl le_rfl)
      _ = ENNReal.ofReal (Δ / 8 + (ĉ * Gr + Δ / 4) + Δ / 8) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
      _ < ENNReal.ofReal (c' * (Gr - η'')) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos hc'pos hgap)]
          rw [mul_sub]
          linarith
      _ = ENNReal.ofReal c' * ENNReal.ofReal (Gr - η'') := ENNReal.ofReal_mul hc'pos.le
      _ ≤ ENNReal.ofReal c' *
            weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w (Qh k) u v :=
          mul_le_mul' le_rfl hn1.le
  obtain ⟨Sk, hSkc, hSk0, hSk1, hSkO, hSkwl⟩ := exists_weighted_competitor_with htot
  have hcostc : ENNReal.ofReal c ≤
      weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w (Qh k) u v :=
    (ENNReal.ofReal_le_ofReal (by linarith : c ≤ Gr - η'')).trans hn1.le
  -- Step 12: back to the original parametrization
  obtain ⟨u', v', hu', huv', hv', hQu, hQv, hwleq⟩ := hQhcorr k u v hu huv hv
  refine ⟨k, u', v', hu', huv', hv', ?_, Sk, hSkc, ?_, ?_, hSkO.mono_right hO₂A, ?_⟩
  · rw [hwleq]
    exact hcostc
  · rw [hSk0, hQu]
  · rw [hSk1, hQv]
  · rw [hwleq]
    exact hSkwl.le

end HigherDimLQGMetric
