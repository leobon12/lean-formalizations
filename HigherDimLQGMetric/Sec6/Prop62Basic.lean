import HigherDimLQGMetric.Config.TightAssembly
import HigherDimLQGMetric.Trap.Lemma42

/-!
# [S] Proposition 6.2, probability part: the compact family as a trap family

Packet S6b. Source: MA3 Details (a) **D-6.2** (*Interface from MA1*, (LC), (L4.2)), blueprint Part A
§6 (`prop:62`, construction steps (1)–(3), (7)).

The outer coordinate pairs of M2b's compact family `C(β)` form the family `Fam` of S3's
`lemma42_trap`:

* `s6bFam`: the pairs `(ζ, ζ̃) = (q.1, q.2.1)` for `q ∈ C(β)`;
* `s6bFam_coord`, `s6bFam_mod`, `s6bFam_loc`: its hypotheses `hFam`, `hFmod`, `hFloc`
  (M2b's P1, the lower moduli of `B(β)`, P2);
* `s6bCore`: `Ā_{1,3}` as a compact subset of the outer configuration annulus, with an index of the
  compact exhaustion containing it (`s6b_exists_core_index`);
* `s6b_lower_core`, `s6b_upper`: the uniform lower bound and the uniform upper modulus of `B(β)` on
  that piece of the exhaustion (they give the collar, the star diameters and the access bound (18)
  deterministically on `C(β)`, BW1 erratum E6.6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter Topology BoundedContinuousFunction unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ### The compact core `Ā_{1,3}` -/

/-- `Ā_{1,3}` as a subset of the outer configuration annulus. -/
def s6bCore (d : ℕ) : Set (configOuter d) := Subtype.val ⁻¹' annCl (0 : Rd d) 1 3

theorem s6b_isCompact_annCl (a b : ℝ) : IsCompact (annCl (0 : Rd d) a b) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_annCl _ _ _) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Rd d)) (r := b)).subset ?_
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right, annCl, sub_zero] using hx.2

theorem s6bCore_isCompact : IsCompact (s6bCore d) :=
  trap_isCompact_preimage_val (s6b_isCompact_annCl 1 3) trap_annCl_subset_ann_half_five

theorem s6b_exists_core_index : ∃ m : ℕ, s6bCore d ⊆ configOuterExhaust d m :=
  (configOuterExhaust d).exists_superset_of_isCompact s6bCore_isCompact

/-! ### The family of outer coordinate pairs -/

/-- The outer coordinate pairs `(ζ, ζ̃)` of the compact family `C(β)`. -/
def s6bFam (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d) :
    Set ((configOuter d × configOuter d → ℝ) × (configOuter d × configOuter d → ℝ)) :=
  (fun q : ConfigC d =>
    (((q.1 : C(configOuter d × configOuter d, ℝ)) : configOuter d × configOuter d → ℝ),
      ((q.2.1 : C(configOuter d × configOuter d, ℝ)) : configOuter d × configOuter d → ℝ))) ''
    configCompactFamily hd c C β

theorem s6b_mem_fam (hd : 2 ≤ d) {c C : ℝ} {β : ConfigBounds d} {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) :
    ((q.1 : configOuter d × configOuter d → ℝ), (q.2.1 : configOuter d × configOuter d → ℝ)) ∈
      s6bFam hd c C β :=
  ⟨q, hq, rfl⟩

theorem s6bFam_coord (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d) :
    ∀ p ∈ s6bFam hd c C β, IsCoordinate p.1 ∧ IsCoordinate p.2 := by
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨(configCompactFamily_outer_P1 hd c C β hq).1,
    (configCompactFamily_outer_tilde_P1 hd c C β hq).1⟩

/-- `hFmod`: one inverse modulus for both coordinates of all pairs of `Fam`, on every compact set. -/
theorem s6bFam_mod (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d) :
    ∀ L : Set (configOuter d), IsCompact L → ∀ χ : ℝ, 0 < χ → ∃ m : ℝ, 0 < m ∧
      ∀ p ∈ s6bFam hd c C β, ∀ u ∈ L, ∀ v ∈ L,
        (p.1 (u, v) < m → dist u v < χ) ∧ (p.2 (u, v) < m → dist u v < χ) := by
  intro L hL χ hχ
  obtain ⟨n, hn⟩ := (configOuterExhaust d).exists_superset_of_isCompact hL
  refine ⟨β.outer.lower n χ, β.outer.lower_pos n χ hχ, ?_⟩
  rintro _ ⟨q, hq, rfl⟩ u hu v hv
  have hB := configCompactFamily_subset_bound hd c C β hq
  have key : ∀ f ∈ configBoundOne (configOuterExhaust d) β.outer,
      f (u, v) < β.outer.lower n χ → dist u v < χ := by
    intro f hf hsmall
    by_contra hlarge
    have hle := (β.outer.lower_mono n (le_of_not_gt hlarge)).trans
      ((hf.1 n (u, v) (hn hu) (hn hv)).1)
    exact (not_lt_of_ge hle) hsmall
  exact ⟨key _ hB.1, key _ hB.2.1⟩

/-- A positive Euclidean gap between a compact set and the frontier of an open superset. -/
theorem s6b_exists_sep {X : Type*} [MetricSpace X] {K O : Set X} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, ∀ z ∈ frontier O, η ≤ dist x z := by
  obtain ⟨η, hη, hsub⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨η, hη, fun x hx z hz => ?_⟩
  by_contra hlt
  have hzO : z ∈ O := hsub (Metric.mem_thickening_iff.2 ⟨x, hx, by
    rw [dist_comm]; exact lt_of_not_ge hlt⟩)
  have := hz.2
  rw [hO.interior_eq] at this
  exact this hzO

/-- `hFloc`: one local realization threshold for both coordinates of all pairs of `Fam`. -/
theorem s6bFam_loc (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d) :
    ∀ K₀ O : Set (configOuter d), IsCompact K₀ → IsOpen O → K₀ ⊆ O → IsCompact (closure O) →
      ∃ a : ℝ, 0 < a ∧ ∀ p ∈ s6bFam hd c C β, ∀ x ∈ K₀, ∀ y ∈ K₀,
        (p.1 (x, y) < a → ∃ R : I →ᵇ configOuter d, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧
          R 1 = y ∧ curveLengthWith (fun u v => ENNReal.ofReal (p.1 (u, v)))
            (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (p.1 (x, y))) ∧
        (p.2 (x, y) < a → ∃ R : I →ᵇ configOuter d, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧
          R 1 = y ∧ curveLengthWith (fun u v => ENNReal.ofReal (p.2 (u, v)))
            (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (p.2 (x, y))) := by
  intro K₀ O hK₀ hO hKO hOc
  obtain ⟨η, hη, hsep⟩ := s6b_exists_sep hK₀ hO hKO
  obtain ⟨a₁, ha₁, H₁⟩ := configCompactFamily_outer_P2 hd c C β hKO hO hOc η hη hsep
  obtain ⟨a₂, ha₂, H₂⟩ := configCompactFamily_outer_tilde_P2 hd c C β hKO hO hOc η hη hsep
  refine ⟨min (a₁ / 4) (a₂ / 4), lt_min (by positivity) (by positivity), ?_⟩
  rintro _ ⟨q, hq, rfl⟩ x hx y hy
  exact ⟨fun h => H₁ q hq x hx y hy (h.trans_le (min_le_left _ _)),
    fun h => H₂ q hq x hx y hy (h.trans_le (min_le_right _ _))⟩

/-! ### Bounds of `B(β)` on the core -/

theorem s6b_lower_core {β : ConfigBounds d} {q : ConfigC d} (hq : q ∈ configBoundSet β)
    {m : ℕ} (hm : s6bCore d ⊆ configOuterExhaust d m) {x y : configOuter d}
    (hx : x ∈ s6bCore d) (hy : y ∈ s6bCore d) :
    β.outer.lower m (dist x y) ≤ q.1 (x, y) ∧ β.outer.lower m (dist x y) ≤ q.2.1 (x, y) :=
  ⟨(hq.1.1 m (x, y) (hm hx) (hm hy)).1, (hq.2.1.1 m (x, y) (hm hx) (hm hy)).1⟩

/-- The upper modulus of `B(β)`: `ζ(x, y) ≤ ω_m(|x - y|)` on the piece `K_m` (coordinates of `C(β)`
vanish on the diagonal). -/
theorem s6b_upper (hd : 2 ≤ d) {c C : ℝ} {β : ConfigBounds d} {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) {m : ℕ} {x y : configOuter d}
    (hx : x ∈ configOuterExhaust d m) (hy : y ∈ configOuterExhaust d m) :
    q.1 (x, y) ≤ β.outer.modulus m (dist x y) ∧ q.2.1 (x, y) ≤ β.outer.modulus m (dist x y) := by
  have hB := configCompactFamily_subset_bound hd c C β hq
  have hc1 := (configCompactFamily_outer_P1 hd c C β hq).1
  have hc2 := (configCompactFamily_outer_tilde_P1 hd c C β hq).1
  have hdist : dist (x, y) (x, x) ≤ dist x y := by
    rw [Prod.dist_eq, dist_self, dist_comm y x]
    exact max_le dist_nonneg le_rfl
  have h1 := hB.1.2 m (x, y) (x, x) hx hy hx hx (dist x y) dist_nonneg hdist
  have h2 := hB.2.1.2 m (x, y) (x, x) hx hy hx hx (dist x y) dist_nonneg hdist
  rw [hc1.metric.self_eq_zero x, Real.dist_eq, sub_zero] at h1
  rw [hc2.metric.self_eq_zero x, Real.dist_eq, sub_zero] at h2
  exact ⟨(le_abs_self _).trans h1, (le_abs_self _).trans h2⟩

end HigherDimLQGMetric
