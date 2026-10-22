import HigherDimLQGMetric.Trap.Smooth

/-!
# [S] Lemma 4.2′: the smooth trap and its stability (MA1 A17)

Packet S3. `lemma42_trap` is [S] Lemma 4.2 in the corrected form of MA1 A17 / blueprint
`lem:4-2`, assembled from

* the smooth construction `f_n = f₀ + (M_n - f₀) φ_n` (`trap_smooth_family`) with tubes measured
  in the base coordinate `ζ`;
* the base case in metric form (`trap_base`: one index `N`, (i) and (ii) for `ξ₀`, through S1c's
  collapse/shortcut lemmas in the metric space `MetricFunSpace ζ _`);
* the transport between that metric space and the coordinate form on the subtype `U`
  (`Trap/Transport.lean`);
* stability on a relative neighbourhood (`trap_stable`), through M2a's Lemmas CC, 2.4, 2.5′.

The configuration neighbourhood is in the abstract coordinate form of M2a (packet S3): a family of
coordinate pairs with (P1)–(P2) uniformly, and closeness to the base pair uniformly on the fixed
compact `Ā_{1,3}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

section Subtype

variable {d : ℕ} {U : Set (Rd d)}

theorem trap_closure_preimage_val {S : Set (Rd d)} (hSU : S ⊆ U) :
    closure ((Subtype.val : U → Rd d) ⁻¹' S) = Subtype.val ⁻¹' closure S := by
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Subtype.image_preimage_coe, inter_eq_right.2 hSU]

theorem trap_frontier_preimage_val {S : Set (Rd d)} (hS : IsOpen S) (hSU : closure S ⊆ U) :
    frontier ((Subtype.val : U → Rd d) ⁻¹' S) = Subtype.val ⁻¹' frontier S := by
  rw [(hS.preimage continuous_subtype_val).frontier_eq, hS.frontier_eq,
    trap_closure_preimage_val (subset_closure.trans hSU), preimage_sdiff]

theorem trap_isCompact_preimage_val {S : Set (Rd d)} (hS : IsCompact S) (hSU : S ⊆ U) :
    IsCompact ((Subtype.val : U → Rd d) ⁻¹' S) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
    inter_eq_right.2 hSU]
  exact hS

theorem trap_closure_ann_subset : closure (ann (0 : Rd d) 1 3) ⊆ annCl 0 1 3 :=
  closure_minimal (ann_subset_annCl _ _ _) (isClosed_annCl _ _ _)

theorem trap_isCompact_annCl : IsCompact (annCl (0 : Rd d) 1 3) := by
  refine (isCompact_closedBall (0 : Rd d) 3).of_isClosed_subset (isClosed_annCl _ _ _) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hx.2

/-- The source's domain `U = A_{1/2,5}` contains `Ā_{1,3}` (hypothesis `hAU` of `lemma42_trap`). -/
theorem trap_annCl_subset_ann_half_five : annCl (0 : Rd d) 1 3 ⊆ ann 0 (1 / 2) 5 :=
  fun _ hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

end Subtype

/-- **[S] Lemma 4.2′** (MA1 A17): the smooth trap and its stability.

Carrier: the open set `U ⊇ Ā_{1,3}` of `ℝ^d` (in the source `U = A_{1/2,5}`), as a subtype.
`Fam` is a family of coordinate pairs `(ζ', ζ̃')` on `U` (the `U`-coordinates of the
configurations of a compact family `C(β)`) with the properties (P1) (common lower modulus on
compact sets) and (P2) (common local realization threshold for `K₀ ⊆ O ⋐ U`) of MA1 A4; the base
pair `(ζ, ζ̃)` belongs to `Fam` and satisfies `ζ̃ ≤ C ζ` (A4 (P3)). The graph `K` and the marked
arcs `σ i` live in the metric space `MetricFunSpace ζ _` of `ζ` and satisfy the hypotheses of
S1c's `lemma32_shortcut` (finite rectifiable graph; marked arcs in `K` with `ζ`-endpoint distance
`≥ a₁` and `ζ̃`-length ratio `≤ c₀`; forcing `TrapForcing` at threshold `b/4` for every horizon),
with `K ⊆ V` (A17 (H2), from Lemma 4.1′). (H1) is the collar `ζ(V̄, ∂A_{1,3}) ≥ 4 a_col` with
`ε₀ < min (e^{-ξ} b/200, a_col/12)`; (H3) the access curves; (H4) `c₀ < c'`.

Conclusion: a smooth `f ≥ 0` with compact support in `A_{1,3}`, positive exactly on `V`, and
constants `c > 0`, `ĉ ∈ (c₀, c')`, `η_* > 0` such that, with `w := e^{-ξ f}`,
(i) and (ii) hold for the base pair with `3ε₀ - η_*`, threshold `b/2`, length `2c`, ratio `ĉ`, and
there is `ε > 0` such that every pair of `Fam` uniformly `ε`-close to `(ζ, ζ̃)` on `Ā_{1,3}`
satisfies (i) `(w·ζ')_{A_{1,3}} < 3ε₀` on `V̄ × V̄`, (ii) the trap with threshold `b`, length `c`,
ratio `c'` and shortcuts in `A_{1,3}`, (iii) `ζ'(V̄, ∂A_{1,3}) > 2 a_col`. -/
theorem lemma42_trap {d : ℕ} {ξ : ℝ} (hξ : 0 < ξ)
    {U : Set (Rd d)} (hU : IsOpen U) (hAU : annCl (0 : Rd d) 1 3 ⊆ U)
    {V : Set (Rd d)} (hV : IsOpen V) (hVA : closure V ⊆ ann (0 : Rd d) 1 3)
    (Fam : Set ((U × U → ℝ) × (U × U → ℝ)))
    (hFam : ∀ p ∈ Fam, IsCoordinate p.1 ∧ IsCoordinate p.2)
    (hFmod : ∀ L : Set U, IsCompact L → ∀ χ : ℝ, 0 < χ → ∃ m : ℝ, 0 < m ∧
      ∀ p ∈ Fam, ∀ u ∈ L, ∀ v ∈ L, (p.1 (u, v) < m → dist u v < χ) ∧
        (p.2 (u, v) < m → dist u v < χ))
    (hFloc : ∀ K₀ O : Set U, IsCompact K₀ → IsOpen O → K₀ ⊆ O → IsCompact (closure O) →
      ∃ a : ℝ, 0 < a ∧ ∀ p ∈ Fam, ∀ x ∈ K₀, ∀ y ∈ K₀,
        (p.1 (x, y) < a → ∃ R : I →ᵇ U, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
          curveLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v)))
            (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (p.1 (x, y))) ∧
        (p.2 (x, y) < a → ∃ R : I →ᵇ U, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
          curveLengthWith (fun u v => ENNReal.ofReal (p.2 (u, v)))
            (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (p.2 (x, y))))
    {ζ ζt : U × U → ℝ} (hζ : IsCoordinate ζ) (hbase : (ζ, ζt) ∈ Fam)
    {Cst : ℝ} (hCst : 0 < Cst) (hζtζ : ∀ x y : U, ζt (x, y) ≤ Cst * ζ (x, y))
    {acol b ε₀ : ℝ}
    (hcol : ∀ x y : U, (x : Rd d) ∈ closure V → (y : Rd d) ∈ frontier (ann (0 : Rd d) 1 3) →
      4 * acol ≤ ζ (x, y))
    (hb : 0 < b) (hε₀ : 0 < ε₀) (hε₀b : ε₀ < Real.exp (-ξ) * b / 200)
    (hε₀col : ε₀ < acol / 12)
    {ι : Type*} [Fintype ι]
    (K : Set (MetricFunSpace ζ hζ.metric)) (hK : IsFiniteRectGraph K)
    (hKV : ∀ q ∈ K, ((LQGMetric.metricFunSpaceVal ζ hζ.metric q : U) : Rd d) ∈ V)
    (arc : ι → ℝ → MetricFunSpace ζ hζ.metric) (harcc : ∀ i, ContinuousOn (arc i) (Icc 0 1))
    (harcK : ∀ i, MapsTo (arc i) (Icc 0 1) K)
    {c₀ c' a₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₀c' : c₀ < c') (ha₁ : 0 < a₁)
    (harclen : ∀ i, curveLengthWith (fun q q' => ENNReal.ofReal
        (ζt (LQGMetric.metricFunSpaceVal ζ hζ.metric q, LQGMetric.metricFunSpaceVal ζ hζ.metric q')))
        (arc i) 0 1 ≤ ENNReal.ofReal c₀ * edist (arc i 0) (arc i 1))
    (harcsep : ∀ i, a₁ ≤ dist (arc i 0) (arc i 1))
    (hforce : ∀ (T : ℝ) (hT : 0 ≤ T), TrapForcing K arc (b / 4) T hT)
    (haccess : ∀ x : U, (x : Rd d) ∈ closure V → ∃ P : ℝ → U, ContinuousOn P (Icc 0 1) ∧
      P 0 = x ∧ MetricFunSpace.pt ζ hζ.metric (P 1) ∈ K ∧
      curveLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) P 0 1 ≤ ENNReal.ofReal ε₀) :
    ∃ f : Rd d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ann (0 : Rd d) 1 3 ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, 0 < f x ↔ x ∈ V) ∧
    ∃ c ĉ ηs : ℝ, 0 < c ∧ c₀ < ĉ ∧ ĉ < c' ∧ 0 < ηs ∧
      -- (i) for the base pair, with `3ε₀ - η_*`
      (∀ x y : U, (x : Rd d) ∈ closure V → (y : Rd d) ∈ closure V →
        weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v)))
          (fun z : U => Real.exp (-(ξ * f z))) {z : U | (z : Rd d) ∈ ann 0 1 3} x y <
          ENNReal.ofReal (3 * ε₀ - ηs)) ∧
      -- (ii) for the base pair, with threshold `b/2`, length `2c`, ratio `ĉ`
      (∀ Q : ℝ → U, ContinuousOn Q (Icc 0 1) → (Q 0 : Rd d) ∈ closure V →
        (Q 1 : Rd d) ∈ closure V →
        weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v)))
            (fun z : U => Real.exp (-(ξ * f z))) Q 0 1 =
          weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v)))
            (fun z : U => Real.exp (-(ξ * f z))) univ (Q 0) (Q 1) →
        b / 2 ≤ ζ (Q 0, Q 1) →
        ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
          ENNReal.ofReal (2 * c) ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v)))
            (fun z : U => Real.exp (-(ξ * f z))) Q u v ∧
          ∃ S : ℝ → U, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧
            MapsTo S (Icc 0 1) {z : U | (z : Rd d) ∈ ann 0 1 3} ∧
            weightedLengthWith (fun u v => ENNReal.ofReal (ζt (u, v)))
                (fun z : U => Real.exp (-(ξ * f z))) S 0 1 ≤
              ENNReal.ofReal ĉ * weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v)))
                (fun z : U => Real.exp (-(ξ * f z))) Q u v) ∧
      -- stability on a relative neighbourhood
      ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ Fam,
        (∀ x y : U, (x : Rd d) ∈ annCl (0 : Rd d) 1 3 → (y : Rd d) ∈ annCl (0 : Rd d) 1 3 →
          |p.1 (x, y) - ζ (x, y)| < ε ∧ |p.2 (x, y) - ζt (x, y)| < ε) →
        -- (i)
        (∀ x y : U, (x : Rd d) ∈ closure V → (y : Rd d) ∈ closure V →
          weylDistOnWith (fun u v => ENNReal.ofReal (p.1 (u, v)))
            (fun z : U => Real.exp (-(ξ * f z))) {z : U | (z : Rd d) ∈ ann 0 1 3} x y <
            ENNReal.ofReal (3 * ε₀)) ∧
        -- (ii)
        (∀ Q : ℝ → U, ContinuousOn Q (Icc 0 1) → (Q 0 : Rd d) ∈ closure V →
          (Q 1 : Rd d) ∈ closure V →
          weightedLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v)))
              (fun z : U => Real.exp (-(ξ * f z))) Q 0 1 =
            weylDistOnWith (fun u v => ENNReal.ofReal (p.1 (u, v)))
              (fun z : U => Real.exp (-(ξ * f z))) univ (Q 0) (Q 1) →
          b ≤ p.1 (Q 0, Q 1) →
          ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
            ENNReal.ofReal c ≤ weightedLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v)))
              (fun z : U => Real.exp (-(ξ * f z))) Q u v ∧
            ∃ S : ℝ → U, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧
              MapsTo S (Icc 0 1) {z : U | (z : Rd d) ∈ ann 0 1 3} ∧
              weightedLengthWith (fun u v => ENNReal.ofReal (p.2 (u, v)))
                  (fun z : U => Real.exp (-(ξ * f z))) S 0 1 ≤
                ENNReal.ofReal c' * weightedLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v)))
                  (fun z : U => Real.exp (-(ξ * f z))) Q u v) ∧
        -- (iii)
        (∀ x y : U, (x : Rd d) ∈ closure V → (y : Rd d) ∈ frontier (ann (0 : Rd d) 1 3) →
          2 * acol < p.1 (x, y)) := by
  -- notation and the sets in the subtype `U`
  set pt := MetricFunSpace.pt ζ hζ.metric with hpt_def
  set val := LQGMetric.metricFunSpaceVal ζ hζ.metric with hval_def
  set AX : Set U := Subtype.val ⁻¹' ann (0 : Rd d) 1 3 with hAX_def
  set VX : Set U := Subtype.val ⁻¹' V with hVX_def
  have hannU : ann (0 : Rd d) 1 3 ⊆ U := (ann_subset_annCl _ _ _).trans hAU
  have hclannU : closure (ann (0 : Rd d) 1 3) ⊆ U := trap_closure_ann_subset.trans hAU
  have hVU : V ⊆ U := subset_closure.trans (hVA.trans hannU)
  have hAXo : IsOpen AX := (isOpen_ann _ _ _).preimage continuous_subtype_val
  have hVXo : IsOpen VX := hV.preimage continuous_subtype_val
  have hclAX : closure AX = Subtype.val ⁻¹' closure (ann (0 : Rd d) 1 3) :=
    trap_closure_preimage_val hannU
  have hclVX : closure VX = Subtype.val ⁻¹' closure V := trap_closure_preimage_val hVU
  have hfrAX : frontier AX = Subtype.val ⁻¹' frontier (ann (0 : Rd d) 1 3) :=
    trap_frontier_preimage_val (isOpen_ann _ _ _) hclannU
  have hVXAX : closure VX ⊆ AX := by
    rw [hclVX]
    exact fun x hx => hVA hx
  have hAXc : IsCompact (closure AX) := by
    rw [hclAX]
    exact trap_isCompact_preimage_val
      (trap_isCompact_annCl.of_isClosed_subset isClosed_closure trap_closure_ann_subset) hclannU
  have hclAXann : ∀ x ∈ closure AX, (x : Rd d) ∈ annCl (0 : Rd d) 1 3 := by
    intro x hx
    rw [hclAX] at hx
    exact trap_closure_ann_subset hx
  have hcolX : ∀ x ∈ closure VX, ∀ y ∈ frontier AX, 4 * acol ≤ ζ (x, y) := by
    intro x hx y hy
    rw [hclVX] at hx
    rw [hfrAX] at hy
    exact hcol x y hx hy
  have hacol : 0 < acol := by linarith
  -- the metric space of `ζ`
  set AZ : Set (MetricFunSpace ζ hζ.metric) := pt '' AX with hAZ_def
  set VZ : Set (MetricFunSpace ζ hζ.metric) := pt '' VX with hVZ_def
  have hAZo : IsOpen AZ := hζ.trap_isOpen_image hAXo
  have hVZo : IsOpen VZ := hζ.trap_isOpen_image hVXo
  have hclAZ : closure AZ = pt '' closure AX := (hζ.trap_image_closure AX).symm
  have hclVZ : closure VZ = pt '' closure VX := (hζ.trap_image_closure VX).symm
  have hfrAZ : frontier AZ = pt '' frontier AX := (hζ.trap_image_frontier AX).symm
  have hAZc : IsCompact (closure AZ) := by
    rw [hclAZ]
    exact hζ.trap_isCompact_image hAXc
  have hVZAZ : closure VZ ⊆ AZ := by
    rw [hclVZ]
    exact image_mono hVXAX
  have hKVZ : K ⊆ VZ := fun q hq => ⟨val q, hKV q hq, rfl⟩
  have hcolZ : ∀ x ∈ closure VZ, ∀ y ∈ frontier AZ, 4 * acol ≤ dist x y := by
    intro x hx y hy
    rw [hclVZ] at hx
    rw [hfrAZ] at hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hcolX x' hx' y' hy'
  -- the comparison coordinate on the metric space of `ζ`
  have hζt : IsCoordinate ζt := (hFam _ hbase).2
  set E : MetricFunSpace ζ hζ.metric → MetricFunSpace ζ hζ.metric → ℝ≥0∞ :=
    fun q q' => ENNReal.ofReal (ζt (val q, val q')) with hE_def
  have hEtri : ∀ p q r, E p r ≤ E p q + E q r :=
    fun p q r => ofReal_metric_triangle hζt.metric (val p) (val q) (val r)
  have hEsymm : ∀ p q, E p q = E q p := fun p q => by
    simp only [hE_def]
    rw [hζt.metric.symm]
  have hEM : ∀ p q, E p q ≤ ENNReal.ofReal Cst * edist p q := by
    intro p q
    rw [edist_dist, ← ENNReal.ofReal_mul hCst.le]
    exact ENNReal.ofReal_le_ofReal (hζtζ (val p) (val q))
  -- access curves and local realization in the metric space of `ζ`
  have haccessZ : ∀ x ∈ closure VZ, ∃ P : ℝ → MetricFunSpace ζ hζ.metric,
      ContinuousOn P (Icc 0 1) ∧ P 0 = x ∧ P 1 ∈ K ∧ curveLength P 0 1 ≤ ENNReal.ofReal ε₀ := by
    intro x hx
    rw [hclVZ] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [hclVX] at hx'
    obtain ⟨P, hPc, hP0, hP1, hPlen⟩ := haccess x' hx'
    refine ⟨pt ∘ P, hζ.trap_continuousOn_pt hPc, by simp [hP0], hP1, ?_⟩
    rw [← curveLengthWith_metricFunSpace hζ.metric]
    exact hPlen
  set K₀ := coordTrapSet hζ.metric AX VX acol with hK₀_def
  have hVXne : (closure VX).Nonempty := by
    obtain ⟨q, hq⟩ := trap_graph_nonempty hK
    exact ⟨val q, subset_closure (hKV q hq)⟩
  have hK₀c : IsCompact K₀ := hζ.isCompact_coordTrapSet hAXc
  have hK₀AX : K₀ ⊆ AX := coordTrapSet_subset hζ.metric hAXo hVXne hcolX (by linarith)
  have hrealZ : ∃ a : ℝ, 0 < a ∧ ∀ p ∈ trapSet AZ VZ acol, ∀ q ∈ trapSet AZ VZ acol,
      dist p q < a → ∃ R : ℝ → MetricFunSpace ζ hζ.metric, ContinuousOn R (Icc 0 1) ∧
        R 0 = p ∧ R 1 = q ∧ MapsTo R (Icc 0 1) (closure AZ) ∧ curveLength R 0 1 = edist p q := by
    obtain ⟨a, ha, hloc⟩ := hFloc K₀ AX hK₀c hAXo hK₀AX hAXc
    refine ⟨a, ha, ?_⟩
    intro p hp q hq hpq
    rw [hAZ_def, hVZ_def, ← hζ.pt_image_coordTrapSet] at hp hq
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨R, hRA, hR0, hR1, hRlen⟩ := (hloc _ hbase p' hp' q' hq').1 hpq
    have hRc : ContinuousOn (Set.IccExtend zero_le_one R) (Icc 0 1) :=
      (continuous_IccExtend_iff.mpr R.continuous).continuousOn
    refine ⟨pt ∘ Set.IccExtend zero_le_one R, hζ.trap_continuousOn_pt hRc, ?_, ?_, ?_, ?_⟩
    · show pt (Set.IccExtend zero_le_one R 0) = pt p'
      rw [Set.IccExtend_of_mem _ _ ⟨le_rfl, zero_le_one⟩]
      exact congrArg pt hR0
    · show pt (Set.IccExtend zero_le_one R 1) = pt q'
      rw [Set.IccExtend_of_mem _ _ ⟨zero_le_one, le_rfl⟩]
      exact congrArg pt hR1
    · intro t ht
      rw [hclAZ]
      refine ⟨Set.IccExtend zero_le_one R t, ?_, rfl⟩
      rw [Set.IccExtend_of_mem _ _ ht]
      exact hRA _
    · rw [← curveLengthWith_metricFunSpace hζ.metric, hRlen, trap_edist_pt]
  -- the graph in `ℝ^d`, the tube radius and the sequences `λ_n`, `η_n`
  have hKc : IsCompact K := hK.isCompact
  have hKne : K.Nonempty := trap_graph_nonempty hK
  obtain ⟨εV, hεV, hεVsub⟩ := hKc.exists_thickening_subset_open hVZo hKVZ
  set Kd : Set (Rd d) := (fun q => ((val q : U) : Rd d)) '' K with hKd_def
  have hKdc : IsCompact Kd := hKc.image (continuous_subtype_val.comp hζ.val_continuous)
  set lam : ℕ → ℝ := fun n => Real.exp (-ξ) / ((n : ℝ) + 2) with hlam_def
  have hlam0 : ∀ n, 0 < lam n := fun n => div_pos (Real.exp_pos _) (by positivity)
  have hlamξ : ∀ n, lam n ≤ Real.exp (-ξ) := fun n =>
    div_le_self (Real.exp_pos _).le (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hlam : Tendsto lam atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    exact h.const_div_atTop _ |>.congr fun n => rfl
  set eta : ℕ → ℝ := fun n => min (εV / 2) (lam n ^ 2) with heta_def
  have heta0 : ∀ n, 0 < eta n := fun n => lt_min (by positivity) (pow_pos (hlam0 n) 2)
  have heta : Tendsto (fun n => eta n / lam n) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (div_pos (heta0 n) (hlam0 n)).le) (fun n => ?_) hlam
    rw [div_le_iff₀ (hlam0 n)]
    calc eta n ≤ lam n ^ 2 := min_le_right _ _
      _ = lam n * lam n := sq _
  -- the tubes `T n` around the graph, inside `V`
  set T : ℕ → Set (Rd d) := fun n => Subtype.val '' {x : U | Metric.infDist (pt x) K < eta n}
    with hT_def
  have hTo : ∀ n, IsOpen (T n) := fun n => hU.isOpenMap_subtype_val _
    (isOpen_lt ((Metric.continuous_infDist_pt K).comp hζ.pt_continuous) continuous_const)
  have hKT : ∀ n, Kd ⊆ T n := by
    rintro n _ ⟨q, hq, rfl⟩
    refine ⟨val q, ?_, rfl⟩
    show Metric.infDist q K < eta n
    rw [Metric.infDist_zero_of_mem hq]
    exact heta0 n
  have hTV : ∀ n, T n ⊆ V := by
    rintro n _ ⟨x, hx, rfl⟩
    have hthick : pt x ∈ Metric.thickening εV K :=
      (Metric.mem_thickening_iff_infDist_lt hKne).2
        (lt_of_lt_of_le hx ((min_le_left _ _).trans (by linarith)))
    obtain ⟨x', hx', hxx'⟩ := hεVsub hthick
    have : x' = x := hxx'
    rw [← this]
    exact hx'
  have hTiff : ∀ n (q : MetricFunSpace ζ hζ.metric),
      ((val q : U) : Rd d) ∈ T n → Metric.infDist q K < eta n := by
    rintro n q ⟨x, hx, hxq⟩
    have : x = val q := Subtype.ext hxq
    rw [this] at hx
    exact hx
  obtain ⟨f, hf⟩ := trap_smooth_family hξ hV hKdc.isClosed T hTo hKT hTV lam hlam0 hlamξ
  -- the weights on the metric space of `ζ`
  set wZ : ℕ → MetricFunSpace ζ hζ.metric → ℝ :=
    fun n q => Real.exp (-(ξ * f n ((val q : U) : Rd d))) with hwZ_def
  have hwZc : ∀ n, Continuous (wZ n) := fun n => Real.continuous_exp.comp
    ((continuous_const.mul ((hf n).1.continuous.comp
      (continuous_subtype_val.comp hζ.val_continuous))).neg)
  have hwZ1 : ∀ n q, lam n ≤ wZ n q ∧ wZ n q ≤ 1 := fun n q => (hf n).2.2.2.2.1 _
  have hwZK : ∀ n, ∀ q ∈ K, wZ n q = lam n := fun n q hq =>
    (hf n).2.2.2.2.2.1 _ ⟨q, hq, rfl⟩
  have hwZoff : ∀ n q, eta n ≤ Metric.infDist q K → Real.exp (-ξ) ≤ wZ n q := by
    intro n q hq
    apply (hf n).2.2.2.2.2.2
    intro hmem
    exact absurd (hTiff n q hmem) (not_lt.2 hq)
  have hwZV : ∀ n q, q ∉ VZ → wZ n q = 1 := by
    intro n q hq
    have hnot : ((val q : U) : Rd d) ∉ V := fun h => hq ⟨val q, h, rfl⟩
    show Real.exp (-(ξ * f n ((val q : U) : Rd d))) = 1
    rw [(hf n).2.2.2.1 _ hnot, mul_zero, neg_zero, Real.exp_zero]
  -- the base configuration (metric form)
  obtain ⟨N, c, ĉ, ηs, L₀, hc, hc₀ĉ, hĉc', hηs, hηsε, hL₀, hpiecesZ, hiiZ⟩ :=
    trap_base hAZo hAZc hVZo hVZAZ hK hKVZ (Real.exp_pos (-ξ)) hcolZ hb hε₀ hε₀b hε₀col
      haccessZ hrealZ E hEtri hEsymm hCst hEM arc harcc harcK hc₀ hc₀c' ha₁ harclen harcsep
      hforce hlam0 hlam heta0 heta wZ hwZc hwZ1 hwZK hwZoff hwZV
  -- the weight on `U`
  set w : U → ℝ := fun z => Real.exp (-(ξ * f N z)) with hw_def
  have hwc : Continuous w :=
    Real.continuous_exp.comp ((continuous_const.mul ((hf N).1.continuous.comp
      continuous_subtype_val)).neg)
  have hwpos : ∀ z, 0 < w z := fun z => Real.exp_pos _
  have hw1 : ∀ z, w z ≤ 1 := fun z => ((hf N).2.2.2.2.1 _).2
  have hwV : ∀ z, z ∉ VX → w z = 1 := by
    intro z hz
    show Real.exp (-(ξ * f N z)) = 1
    rw [(hf N).2.2.2.1 _ hz, mul_zero, neg_zero, Real.exp_zero]
  have hwlX : ∀ (P : ℝ → U) (a b : ℝ),
      weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P a b =
        weightedLength (wZ N) (pt ∘ P) a b :=
    fun P a b => weightedLengthWith_metricFunSpace hζ.metric w P a b
  have hmapsX : ∀ (r : ℝ) (P : ℝ → MetricFunSpace ζ hζ.metric),
      MapsTo P (Icc 0 1) (trapSet AZ VZ r) →
      MapsTo (val ∘ P) (Icc 0 1) (coordTrapSet hζ.metric AX VX r) := by
    intro r P hP t ht
    have h := hP ht
    rw [hAZ_def, hVZ_def, ← hζ.pt_image_coordTrapSet] at h
    obtain ⟨z, hz, hzP⟩ := h
    show val (P t) ∈ _
    rw [← hzP]
    exact hz
  -- (i) for the base configuration: the pieces in coordinate form
  have hpiecesX : ∀ x ∈ closure VX, ∀ y ∈ closure VX, ∃ P₁ P₂ P₃ : ℝ → U,
      (ContinuousOn P₁ (Icc 0 1) ∧ MapsTo P₁ (Icc 0 1) (coordTrapSet hζ.metric AX VX (acol / 2)) ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) P₁ 0 1 ≤ ENNReal.ofReal L₀) ∧
      (ContinuousOn P₂ (Icc 0 1) ∧ MapsTo P₂ (Icc 0 1) (coordTrapSet hζ.metric AX VX (acol / 2)) ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) P₂ 0 1 ≤ ENNReal.ofReal L₀) ∧
      (ContinuousOn P₃ (Icc 0 1) ∧ MapsTo P₃ (Icc 0 1) (coordTrapSet hζ.metric AX VX (acol / 2)) ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) P₃ 0 1 ≤ ENNReal.ofReal L₀) ∧
      P₁ 0 = x ∧ P₁ 1 = P₂ 0 ∧ P₂ 1 = P₃ 0 ∧ P₃ 1 = y ∧
      weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₁ 0 1 +
        weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₂ 0 1 +
        weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P₃ 0 1 ≤
          ENNReal.ofReal (3 * ε₀ - 2 * ηs) := by
    intro x hx y hy
    have hxZ : pt x ∈ closure VZ := by rw [hclVZ]; exact mem_image_of_mem pt hx
    have hyZ : pt y ∈ closure VZ := by rw [hclVZ]; exact mem_image_of_mem pt hy
    obtain ⟨P₁, P₂, P₃, ⟨h1c, h1Y, h1L⟩, ⟨h2c, h2Y, h2L⟩, ⟨h3c, h3Y, h3L⟩, h10, h12, h23, h31,
      hsum⟩ := hpiecesZ (pt x) hxZ (pt y) hyZ
    refine ⟨val ∘ P₁, val ∘ P₂, val ∘ P₃,
      ⟨hζ.trap_continuousOn_val h1c, hmapsX _ _ h1Y, ?_⟩,
      ⟨hζ.trap_continuousOn_val h2c, hmapsX _ _ h2Y, ?_⟩,
      ⟨hζ.trap_continuousOn_val h3c, hmapsX _ _ h3Y, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [curveLengthWith_metricFunSpace hζ.metric]
      exact h1L
    · rw [curveLengthWith_metricFunSpace hζ.metric]
      exact h2L
    · rw [curveLengthWith_metricFunSpace hζ.metric]
      exact h3L
    · show val (P₁ 0) = x
      rw [h10]
      rfl
    · show val (P₁ 1) = val (P₂ 0)
      rw [h12]
    · show val (P₂ 1) = val (P₃ 0)
      rw [h23]
    · show val (P₃ 1) = y
      rw [h31]
      rfl
    · rw [hwlX, hwlX, hwlX]
      exact hsum
  -- (ii) for the base configuration in coordinate form
  have hbaseiiX : ∀ Q : ℝ → U, ContinuousOn Q (Icc 0 1) → Q 0 ∈ closure VX →
      Q 1 ∈ closure VX →
      weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Q 0 1 =
        weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w univ (Q 0) (Q 1) →
      b / 2 ≤ ζ (Q 0, Q 1) →
      ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
        ENNReal.ofReal (2 * c) ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Q u v ∧
        ∃ S : ℝ → U, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧
          MapsTo S (Icc 0 1) (coordTrapSet hζ.metric AX VX acol) ∧
          weightedLengthWith (fun u v => ENNReal.ofReal (ζt (u, v))) w S 0 1 ≤
            ENNReal.ofReal ĉ * weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w Q u v := by
    intro Q hQc hQ0 hQ1 hmin hsep
    have hQ0Z : (pt ∘ Q) 0 ∈ closure VZ := by rw [hclVZ]; exact mem_image_of_mem pt hQ0
    have hQ1Z : (pt ∘ Q) 1 ∈ closure VZ := by rw [hclVZ]; exact mem_image_of_mem pt hQ1
    have hminZ : weightedLength (wZ N) (pt ∘ Q) 0 1 =
        weylDistOn (wZ N) univ ((pt ∘ Q) 0) ((pt ∘ Q) 1) := by
      have h := hmin
      rw [hwlX, trap_weylDistOnWith_eq hζ, preimage_univ] at h
      exact h
    obtain ⟨u, v, hu, huv, hv, hcost, S, hSc, hS0, hS1, hSY, hSb⟩ :=
      hiiZ (pt ∘ Q) (hζ.trap_continuousOn_pt hQc) hQ0Z hQ1Z hminZ hsep
    refine ⟨u, v, hu, huv, hv, ?_, val ∘ S, hζ.trap_continuousOn_val hSc, ?_, ?_,
      hmapsX _ _ hSY, ?_⟩
    · rw [hwlX]
      exact hcost
    · show val (S 0) = Q u
      rw [hS0]
      rfl
    · show val (S 1) = Q v
      rw [hS1]
      rfl
    · rw [hwlX]
      exact hSb
  -- stability (coordinate form)
  obtain ⟨ε, hε, hstab⟩ := trap_stable Fam hFam hFmod hFloc hζ hbase hAXo hAXc hVXo hVXAX hVXne
    hwc hwpos hw1 hwV hcolX hb hε₀ hε₀col hc (hc₀.trans hc₀ĉ.le) hĉc' hηs hηsε hL₀ hpiecesX
    hbaseiiX
  -- the trap function
  have hfN := hf N
  have hsupp : Function.support (f N) = V := by
    ext x
    rw [Function.mem_support]
    constructor
    · intro hx
      exact (hfN.2.2.1 x).1 (lt_of_le_of_ne (hfN.2.1 x) (Ne.symm hx))
    · intro hx
      exact ((hfN.2.2.1 x).2 hx).ne'
  have htsupp : tsupport (f N) ⊆ ann (0 : Rd d) 1 3 := by
    rw [tsupport, hsupp]
    exact hVA
  have hcpt : HasCompactSupport (f N) :=
    trap_isCompact_annCl.of_isClosed_subset isClosed_closure
      (htsupp.trans (ann_subset_annCl _ _ _))
  have hAXset : AX = {z : U | (z : Rd d) ∈ ann 0 1 3} := rfl
  have hVXmem : ∀ x : U, (x : Rd d) ∈ closure V → x ∈ closure VX := fun x hx => by
    rw [hclVX]
    exact hx
  have hK₀AX' : coordTrapSet hζ.metric AX VX acol ⊆ AX := hK₀AX
  refine ⟨f N, hfN.1, hcpt, htsupp, hfN.2.1, hfN.2.2.1, c, ĉ, ηs, hc, hc₀ĉ, hĉc', hηs, ?_, ?_, ?_⟩
  · -- (i) for the base configuration
    intro x y hx hy
    obtain ⟨P₁, P₂, P₃, ⟨h1c, h1Y, -⟩, ⟨h2c, h2Y, -⟩, ⟨h3c, h3Y, -⟩, h10, h12, h23, h31, hsum⟩ :=
      hpiecesX x (hVXmem x hx) y (hVXmem y hy)
    have hY₀AX : coordTrapSet hζ.metric AX VX (acol / 2) ⊆ AX :=
      coordTrapSet_subset hζ.metric hAXo hVXne hcolX (by linarith)
    have hthree := trap_weylDistOnWith_le_three
      (E := fun u v => ENNReal.ofReal (ζ (u, v))) (fun a b' e => ofReal_metric_triangle
        hζ.metric a b' e) (w := w) (S := AX) h12 h23
    have hb1 := weylDistOnWith_le (E := fun u v => ENNReal.ofReal (ζ (u, v))) (w := w) h1c rfl rfl
      (h1Y.mono_right hY₀AX)
    have hb2 := weylDistOnWith_le (E := fun u v => ENNReal.ofReal (ζ (u, v))) (w := w) h2c rfl rfl
      (h2Y.mono_right hY₀AX)
    have hb3 := weylDistOnWith_le (E := fun u v => ENNReal.ofReal (ζ (u, v))) (w := w) h3c rfl rfl
      (h3Y.mono_right hY₀AX)
    rw [h10, h31] at hthree
    rw [h10] at hb1
    rw [h31] at hb3
    refine (hthree.trans ((add_le_add (add_le_add hb1 hb2) hb3).trans hsum)).trans_lt ?_
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  · -- (ii) for the base configuration
    intro Q hQc hQ0 hQ1 hmin hsep
    obtain ⟨u, v, hu, huv, hv, hcost, S, hSc, hS0, hS1, hSY, hSb⟩ :=
      hbaseiiX Q hQc (hVXmem _ hQ0) (hVXmem _ hQ1) hmin hsep
    exact ⟨u, v, hu, huv, hv, hcost, S, hSc, hS0, hS1, hSY.mono_right hK₀AX', hSb⟩
  · -- stability
    refine ⟨ε, hε, fun p hp hclose => ?_⟩
    have hclose' : ∀ x ∈ closure AX, ∀ y ∈ closure AX,
        |p.1 (x, y) - ζ (x, y)| < ε ∧ |p.2 (x, y) - ζt (x, y)| < ε :=
      fun x hx y hy => hclose x y (hclAXann x hx) (hclAXann y hy)
    obtain ⟨hpi, hpii, hpiii⟩ := hstab p hp hclose'
    refine ⟨fun x y hx hy => hpi x (hVXmem x hx) y (hVXmem y hy), ?_, ?_⟩
    · intro Q hQc hQ0 hQ1 hmin hsep
      exact hpii Q hQc (hVXmem _ hQ0) (hVXmem _ hQ1) hmin hsep
    · intro x y hx hy
      refine hpiii x (hVXmem x hx) y ?_
      rw [hfrAX]
      exact hy

end HigherDimLQGMetric
