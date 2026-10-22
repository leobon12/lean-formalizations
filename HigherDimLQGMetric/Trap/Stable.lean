import HigherDimLQGMetric.Trap.StableII

/-!
# Stability of the trap on a relative neighbourhood ([S] Lemma 4.2, MA1 A17 "Stability")

Packet S3. Coordinate form. `Fam` is a family of coordinate pairs `(ζ', ζ̃')` on a metric space `X`
(the `U`-coordinates of the configurations of a compact family `C(β)`) with the properties
(P1) (a common lower modulus on every compact set) and (P2) (a common local realization threshold
for every compact `K₀ ⊆ O` with `closure O` compact) of MA1 A4, uniformly over the family; the
base pair `(ζ, ζ̃)` belongs to `Fam`. Given the conclusions (i) and (ii) of the trap for the base
pair (`trap_base`, transported), `trap_stable` produces `ε > 0` such that every pair of `Fam`
uniformly `ε`-close to `(ζ, ζ̃)` on `closure A` satisfies

* (i) `(w·ζ')_A(x, y) < 3ε₀` for `x, y ∈ closure V`;
* (ii) every `(w·ζ')`-minimizer (over all curves of `X`) between collector points at
  `ζ'`-distance `≥ b` has a subcurve of weighted length `≥ c` whose endpoints are joined inside `A`
  by a curve of `(w·ζ̃')`-length `≤ c'` times that length;
* (iii) `ζ'(closure V, frontier A) > 2 a_col`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- Three chained pieces bound a confined weighted distance (any distance function with the
triangle inequality). -/
theorem trap_weylDistOnWith_le_three {X : Type*} [MetricSpace X] {E : X → X → ℝ≥0∞}
    (hE : ∀ p q r, E p r ≤ E p q + E q r) {w : X → ℝ} {S : Set X}
    {P₁ P₂ P₃ : ℝ → X} (h12 : P₁ 1 = P₂ 0) (h23 : P₂ 1 = P₃ 0) :
    weylDistOnWith E w S (P₁ 0) (P₃ 1) ≤
      weylDistOnWith E w S (P₁ 0) (P₁ 1) + weylDistOnWith E w S (P₂ 0) (P₂ 1) +
        weylDistOnWith E w S (P₃ 0) (P₃ 1) := by
  calc weylDistOnWith E w S (P₁ 0) (P₃ 1)
      ≤ weylDistOnWith E w S (P₁ 0) (P₂ 1) + weylDistOnWith E w S (P₂ 1) (P₃ 1) :=
        weylDistOnWith_triangle E hE w S _ _ _
    _ ≤ (weylDistOnWith E w S (P₁ 0) (P₁ 1) + weylDistOnWith E w S (P₁ 1) (P₂ 1)) +
          weylDistOnWith E w S (P₂ 1) (P₃ 1) :=
        add_le_add (weylDistOnWith_triangle E hE w S _ _ _) le_rfl
    _ = _ := by rw [h12, h23]

/-- **Stability of the trap** ([S] Lemma 4.2′, MA1 A17), coordinate form. -/
theorem trap_stable {X : Type*} [MetricSpace X]
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
    (hVA : closure V ⊆ A) (hVne : (closure V).Nonempty)
    {w : X → ℝ} (hwc : Continuous w) (hwpos : ∀ x, 0 < w x) (hw1 : ∀ x, w x ≤ 1)
    (hwV : ∀ x, x ∉ V → w x = 1)
    {acol b ε₀ c ĉ c' ηs L₀ : ℝ}
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, 4 * acol ≤ ζ (x, y))
    (hb : 0 < b) (hε₀ : 0 < ε₀) (hε₀col : ε₀ < acol / 12) (hc : 0 < c) (hĉ0 : 0 ≤ ĉ)
    (hĉc' : ĉ < c') (hηs : 0 < ηs) (hηsε : ηs ≤ ε₀) (hL₀ : 0 ≤ L₀)
    (hpieces : ∀ x ∈ closure V, ∀ y ∈ closure V, ∃ P₁ P₂ P₃ : ℝ → X,
      (ContinuousOn P₁ (Icc 0 1) ∧ MapsTo P₁ (Icc 0 1) (coordTrapSet hζ.metric A V (acol / 2)) ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) P₁ 0 1 ≤ ENNReal.ofReal L₀) ∧
      (ContinuousOn P₂ (Icc 0 1) ∧ MapsTo P₂ (Icc 0 1) (coordTrapSet hζ.metric A V (acol / 2)) ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) P₂ 0 1 ≤ ENNReal.ofReal L₀) ∧
      (ContinuousOn P₃ (Icc 0 1) ∧ MapsTo P₃ (Icc 0 1) (coordTrapSet hζ.metric A V (acol / 2)) ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) P₃ 0 1 ≤ ENNReal.ofReal L₀) ∧
      P₁ 0 = x ∧ P₁ 1 = P₂ 0 ∧ P₂ 1 = P₃ 0 ∧ P₃ 1 = y ∧
      weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₁ 0 1 +
        weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₂ 0 1 +
        weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₃ 0 1 ≤
          ENNReal.ofReal (3 * ε₀ - 2 * ηs))
    (hbaseii : ∀ Q : ℝ → X, ContinuousOn Q (Icc 0 1) → Q 0 ∈ closure V → Q 1 ∈ closure V →
      weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Q 0 1 =
        weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w univ (Q 0) (Q 1) →
      b / 2 ≤ ζ (Q 0, Q 1) →
      ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
        ENNReal.ofReal (2 * c) ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Q u v ∧
        ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧
          MapsTo S (Icc 0 1) (coordTrapSet hζ.metric A V acol) ∧
          weightedLengthWith (fun u v => ENNReal.ofReal (ζt (u, v))) w S 0 1 ≤
            ENNReal.ofReal ĉ * weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Q u v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ Fam,
      (∀ x ∈ closure A, ∀ y ∈ closure A,
        |p.1 (x, y) - ζ (x, y)| < ε ∧ |p.2 (x, y) - ζt (x, y)| < ε) →
      (∀ x ∈ closure V, ∀ y ∈ closure V,
        weylDistOnWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w A x y <
          ENNReal.ofReal (3 * ε₀)) ∧
      (∀ Q : ℝ → X, ContinuousOn Q (Icc 0 1) → Q 0 ∈ closure V → Q 1 ∈ closure V →
        weightedLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w Q 0 1 =
          weylDistOnWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w univ (Q 0) (Q 1) →
        b ≤ p.1 (Q 0, Q 1) →
        ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
          ENNReal.ofReal c ≤ weightedLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w Q u v ∧
          ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧ MapsTo S (Icc 0 1) A ∧
            weightedLengthWith (fun u v => ENNReal.ofReal (p.2 (u, v))) w S 0 1 ≤
              ENNReal.ofReal c' *
                weightedLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w Q u v) ∧
      (∀ x ∈ closure V, ∀ y ∈ frontier A, 2 * acol < p.1 (x, y)) := by
  have hacol : 0 < acol := by linarith
  -- the sets for the recovery of the competitors of (i)
  set Y₀ := coordTrapSet hζ.metric A V (acol / 2) with hY₀_def
  set O₁ := coordTrapOpen hζ.metric A V (3 * acol / 4) with hO₁_def
  have hY₀O₁ : Y₀ ⊆ O₁ :=
    coordTrapSet_subset_coordTrapOpen hζ.metric hA hVne hcol (by linarith) (by linarith)
  have hO₁A : closure O₁ ⊆ A :=
    hζ.closure_coordTrapOpen_subset.trans (coordTrapSet_subset hζ.metric hA hVne hcol (by linarith))
  have hO₁cA : closure O₁ ⊆ closure A := hO₁A.trans subset_closure
  have hO₁c : IsCompact (closure O₁) :=
    hAc.of_isClosed_subset isClosed_closure hO₁cA
  have hY₀c : IsCompact Y₀ := hζ.isCompact_coordTrapSet hAc
  have hVcA : closure V ⊆ closure A := hVA.trans subset_closure
  -- uniform recovery for the first coordinates
  set Fam₁ : Set (X × X → ℝ) := Prod.fst '' Fam with hFam₁_def
  have hFam₁ : ∀ ρ' ∈ Fam₁, IsCoordinate ρ' := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hFam q hq).1
  have hζF₁ : ζ ∈ Fam₁ := ⟨_, hbase, rfl⟩
  have hmod₁ : ∀ χ : ℝ, 0 < χ → ∃ m : ℝ, 0 < m ∧
      ∀ ρ' ∈ Fam₁, ∀ u ∈ closure O₁, ∀ v ∈ closure O₁, ρ' (u, v) < m → dist u v < χ := by
    intro χ hχ
    obtain ⟨m, hm, hmm⟩ := hFmod (closure O₁) hO₁c χ hχ
    refine ⟨m, hm, ?_⟩
    rintro _ ⟨q, hq, rfl⟩ u hu v hv huv
    exact (hmm q hq u hu v hv).1 huv
  obtain ⟨a₁, ha₁, hloc₁⟩ := hFloc Y₀ O₁ hY₀c (hζ.isOpen_coordTrapOpen hA) hY₀O₁ hO₁c
  have hloc₁' : ∃ δloc : ℝ, 0 < δloc ∧ ∀ ρ' ∈ Fam₁, ∀ x ∈ Y₀, ∀ y ∈ Y₀, ρ' (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O₁) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ' (x, y)) := by
    refine ⟨a₁, ha₁, ?_⟩
    rintro _ ⟨q, hq, rfl⟩ x hx y hy hxy
    exact (hloc₁ q hq x hx y hy).1 hxy
  obtain ⟨e₁, he₁, hrec₁⟩ := trap_uniform_recovery Fam₁ hFam₁ hζF₁ hY₀O₁ hO₁c
    hwc.continuousOn (fun z _ => (hwpos z).le) hmod₁ hloc₁' hL₀ (η := ηs / 3) (by positivity)
  set ε₁ := min (acol / 8) e₁ with hε₁_def
  have hε₁ : 0 < ε₁ := lt_min (by positivity) he₁
  -- (i) and (iii) for every pair `ε₁`-close to the base pair
  have hi : ∀ p ∈ Fam, (∀ x ∈ closure A, ∀ y ∈ closure A, |p.1 (x, y) - ζ (x, y)| < ε₁) →
      ∀ x ∈ closure V, ∀ y ∈ closure V,
        weylDistOnWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w A x y <
          ENNReal.ofReal (3 * ε₀) := by
    intro p hp hclose x hx y hy
    have hρ := (hFam p hp).1
    have hclose₁ : ∀ u ∈ closure O₁, ∀ v ∈ closure O₁, |ζ (u, v) - p.1 (u, v)| ≤ e₁ := by
      intro u hu v hv
      rw [abs_sub_comm]
      exact (hclose u (hO₁cA hu) v (hO₁cA hv)).le.trans (min_le_right _ _)
    obtain ⟨P₁, P₂, P₃, ⟨h1c, h1Y, h1L⟩, ⟨h2c, h2Y, h2L⟩, ⟨h3c, h3Y, h3L⟩, h10, h12, h23, h31,
      hsum⟩ := hpieces x hx y hy
    have hr1 := hrec₁ p.1 ⟨p, hp, rfl⟩ hclose₁ P₁ h1c h1Y h1L
    have hr2 := hrec₁ p.1 ⟨p, hp, rfl⟩ hclose₁ P₂ h2c h2Y h2L
    have hr3 := hrec₁ p.1 ⟨p, hp, rfl⟩ hclose₁ P₃ h3c h3Y h3L
    have hthree := trap_weylDistOnWith_le_three
      (E := fun u v => ENNReal.ofReal (p.1 (u, v))) (fun a b' d => ofReal_metric_triangle
        hρ.metric a b' d) (w := w) (S := closure O₁) h12 h23
    rw [h10, h31] at hthree
    rw [h10] at hr1
    rw [h31] at hr3
    calc weylDistOnWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w A x y
        ≤ weylDistOnWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w (closure O₁) x y :=
          weylDistOnWith_anti_set _ _ hO₁A x y
      _ ≤ (weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₁ 0 1 +
            ENNReal.ofReal (ηs / 3)) +
          (weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₂ 0 1 +
            ENNReal.ofReal (ηs / 3)) +
          (weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₃ 0 1 +
            ENNReal.ofReal (ηs / 3)) := hthree.trans (add_le_add (add_le_add hr1 hr2) hr3)
      _ = (weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₁ 0 1 +
            weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₂ 0 1 +
            weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₃ 0 1) +
          (ENNReal.ofReal (ηs / 3) + ENNReal.ofReal (ηs / 3) + ENNReal.ofReal (ηs / 3)) := by
          ring
      _ ≤ ENNReal.ofReal (3 * ε₀ - 2 * ηs) + ENNReal.ofReal ηs := by
          gcongr
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact le_of_eq (congrArg ENNReal.ofReal (by ring))
      _ = ENNReal.ofReal (3 * ε₀ - ηs) := by
          rw [← ENNReal.ofReal_add (by linarith) hηs.le]
          congr 1
          ring
      _ < ENNReal.ofReal (3 * ε₀) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
          (by linarith)
  have hiii : ∀ p ∈ Fam, (∀ x ∈ closure A, ∀ y ∈ closure A, |p.1 (x, y) - ζ (x, y)| < ε₁) →
      ∀ x ∈ closure V, ∀ y ∈ frontier A, 2 * acol < p.1 (x, y) := by
    intro p _ hclose x hx y hy
    have h := hclose x (hVcA hx) y (frontier_subset_closure hy)
    have h8 : ε₁ ≤ acol / 8 := min_le_left _ _
    have := hcol x hx y hy
    linarith [(abs_lt.1 h).1]
  -- (ii) by contradiction along a sequence
  have hY₀dist : ∀ x ∈ closure V, ∀ y ∈ closure V,
      weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Y₀ x y <
        ENNReal.ofReal (3 * ε₀) := by
    intro x hx y hy
    obtain ⟨P₁, P₂, P₃, ⟨h1c, h1Y, -⟩, ⟨h2c, h2Y, -⟩, ⟨h3c, h3Y, -⟩, h10, h12, h23, h31,
      hsum⟩ := hpieces x hx y hy
    have hthree := trap_weylDistOnWith_le_three
      (E := fun u v => ENNReal.ofReal (ζ (u, v))) (fun a b' d => ofReal_metric_triangle
        hζ.metric a b' d) (w := w) (S := Y₀) h12 h23
    rw [h10, h31] at hthree
    have hb1 := weylDistOnWith_le (E := fun u v => ENNReal.ofReal (ζ (u, v))) (w := w) h1c rfl rfl h1Y
    have hb2 := weylDistOnWith_le (E := fun u v => ENNReal.ofReal (ζ (u, v))) (w := w) h2c rfl rfl h2Y
    have hb3 := weylDistOnWith_le (E := fun u v => ENNReal.ofReal (ζ (u, v))) (w := w) h3c rfl rfl h3Y
    rw [h10] at hb1
    rw [h31] at hb3
    refine (hthree.trans ((add_le_add (add_le_add hb1 hb2) hb3).trans hsum)).trans_lt ?_
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  have hii : ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ p ∈ Fam,
      (∀ x ∈ closure A, ∀ y ∈ closure A,
        |p.1 (x, y) - ζ (x, y)| < ε₂ ∧ |p.2 (x, y) - ζt (x, y)| < ε₂) →
      ∀ Q : ℝ → X, ContinuousOn Q (Icc 0 1) → Q 0 ∈ closure V → Q 1 ∈ closure V →
        weightedLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w Q 0 1 =
          weylDistOnWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w univ (Q 0) (Q 1) →
        b ≤ p.1 (Q 0, Q 1) →
        ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
          ENNReal.ofReal c ≤ weightedLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w Q u v ∧
          ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧ MapsTo S (Icc 0 1) A ∧
            weightedLengthWith (fun u v => ENNReal.ofReal (p.2 (u, v))) w S 0 1 ≤
              ENNReal.ofReal c' *
                weightedLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v))) w Q u v := by
    by_contra hneg
    push Not at hneg
    have hseq := fun k : ℕ => hneg (min ε₁ (1 / ((k : ℝ) + 1))) (lt_min hε₁ (by positivity))
    choose p hpF hpclose Q hQc hQ0 hQ1 hQmin hQb hQfail using hseq
    have hpclose1 : ∀ k, ∀ x ∈ closure A, ∀ y ∈ closure A,
        |(p k).1 (x, y) - ζ (x, y)| ≤ 1 / (k + 1) ∧ |(p k).2 (x, y) - ζt (x, y)| ≤ 1 / (k + 1) :=
      fun k x hx y hy => ⟨((hpclose k x hx y hy).1.trans_le (min_le_right _ _)).le,
        ((hpclose k x hx y hy).2.trans_le (min_le_right _ _)).le⟩
    have hpcloseε : ∀ k, ∀ x ∈ closure A, ∀ y ∈ closure A, |(p k).1 (x, y) - ζ (x, y)| < ε₁ :=
      fun k x hx y hy => (hpclose k x hx y hy).1.trans_le (min_le_left _ _)
    have hpclose8 : ∀ k, ∀ x ∈ closure A, ∀ y ∈ closure A,
        |(p k).1 (x, y) - ζ (x, y)| ≤ acol / 8 :=
      fun k x hx y hy => (hpcloseε k x hx y hy).le.trans (min_le_left _ _)
    have hpcol : ∀ k, ∀ x ∈ closure V, ∀ y ∈ frontier A, 2 * acol ≤ (p k).1 (x, y) :=
      fun k x hx y hy => (hiii (p k) (hpF k) (hpcloseε k) x hx y hy).le
    have hQcost : ∀ k, weightedLengthWith (fun u v => ENNReal.ofReal ((p k).1 (u, v))) w
        (Q k) 0 1 < ENNReal.ofReal (3 * ε₀) := by
      intro k
      rw [hQmin k]
      exact (weylDistOnWith_anti_set _ _ (subset_univ A) _ _).trans_lt
        (hi (p k) (hpF k) (hpcloseε k) _ (hQ0 k) _ (hQ1 k))
    obtain ⟨k, u, v, hu, huv, hv, hcost, S, hSc, hS0, hS1, hSA, hSb⟩ :=
      trap_stable_ii_seq Fam hFam hFmod hFloc hζ hbase hA hAc hV hVA hwc hwpos hw1 hwV hcol hb
        hε₀ hε₀col hc hĉ0 hĉc' hY₀dist hbaseii p hpF hpclose1 hpclose8 hpcol Q hQc hQ0 hQ1
        hQmin hQcost hQb
    exact absurd hSb (not_le.2 (hQfail k u v hu huv hv hcost S hSc hS0 hS1 hSA))
  obtain ⟨ε₂, hε₂, hii'⟩ := hii
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun p hp hclose => ?_⟩
  have hclose₁ : ∀ x ∈ closure A, ∀ y ∈ closure A, |p.1 (x, y) - ζ (x, y)| < ε₁ :=
    fun x hx y hy => (hclose x hx y hy).1.trans_le (min_le_left _ _)
  have hclose₂ : ∀ x ∈ closure A, ∀ y ∈ closure A,
      |p.1 (x, y) - ζ (x, y)| < ε₂ ∧ |p.2 (x, y) - ζt (x, y)| < ε₂ :=
    fun x hx y hy => ⟨(hclose x hx y hy).1.trans_le (min_le_right _ _),
      (hclose x hx y hy).2.trans_le (min_le_right _ _)⟩
  exact ⟨hi p hp hclose₁, hii' p hp hclose₂, hiii p hp hclose₁⟩

end HigherDimLQGMetric
