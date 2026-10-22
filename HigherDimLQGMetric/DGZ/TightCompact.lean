import HigherDimLQGMetric.DGZ.TightInternal
import HigherDimLQGMetric.DGZ.TightCompactSet
import HigherDimLQGMetric.DGZ.FunctionalsMeas
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# DGZ Proposition 6.3: tightness of the normalized internal metrics (packet L5a)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Prop 6.3 (TeX l. 2910–2916, p. 57);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, D-6.1–6.3 (Prop 6.3: "the Hölder bound
gives, for every ball, the modulus condition … hence tightness … by the local criterion"); blueprint
Part C, Prop `r2:prop:63` ("for every `q ∈ [q₂, 1)`, every open connected `U` (including `U = ℝ^d`)
and every `m ≥ 0`, the laws of `D_{m,n}(·,·;U)/a^{(q)}_n` on `C(U × U, ℝ)` are tight, uniformly
over dyadic realizations").

* `exists_holderMetricSet_measure_compl_le` / `isTightMeasureSet_of_holderBounds`: the local
  tightness criterion on `C(X × X, ℝ)` (`X` a metric space with an exhaustion `K j`): laws carried
  by functions vanishing on the diagonal with the triangle inequality, with uniform-in-the-law local
  Hölder bounds on each `K j`, are tight; more precisely, for every `ε` there are constants
  `M j ≥ 0` such that all laws give mass `≤ ε` to the complement of the compact set of
  `holderMetricSet K M β`.
* `exists_isCompact_isPreconnected_superset`: a compact subset of an open connected `U ⊆ ℝ^d` lies
  in a compact preconnected subset of `U` (balls around a finite cover joined by paths).
* `internalMetricC ξ φ U a`: `a⁻¹ D(·,·; U)` as an element of `C(U × U, ℝ)`;
  `measurable_internalMetricC`, `internalMetricC_apply`.
* **`isTightMeasureSet_internalMetricC_sub`** (`h_{m,n} = h_n - h_m`, every `m`),
  **`isTightMeasureSet_internalMetricC`** (`h_n`) and **`isTightMeasureSet_normMetricC`** (the
  whole-space metric, MA7's `normMetricC`), all normalized by `a^{(q)}_n`, `q ∈ [q₂, 1)`, together
  with the structured forms `exists_internalMetricC_holderMetricSet_sub`, … that exhibit the compact
  sets (needed by packet L5b to show that limit laws are carried by locally Hölder pseudo-metrics).

The limit statements of Prop 6.3 (limits are pseudo-metrics, locally Hölder) follow from the
structured forms by the portmanteau theorem, because `holderMetricSet K M β` is closed; they are
left to packet L5b together with the zero-one law (D-6.9).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

/-! ### The local tightness criterion -/

section Criterion

variable {X : Type*} [MetricSpace X] {K : ℕ → Set X} {β : ℝ}

/-- The pseudo-metric conditions define a closed subset of `C(X × X, ℝ)`. -/
lemma tc_isClosed_metricCond :
    IsClosed {f : C(X × X, ℝ) | (∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z)} := by
  have e : {f : C(X × X, ℝ) | (∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z)} =
      (⋂ x, {f : C(X × X, ℝ) | f (x, x) = 0}) ∩
        ⋂ x, ⋂ y, ⋂ z, {f : C(X × X, ℝ) | f (x, z) ≤ f (x, y) + f (y, z)} := by
    ext f; simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [e]
  exact (isClosed_iInter fun x => isClosed_eq (continuous_eval_const _)
      continuous_const).inter (isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_iInter fun z => isClosed_le (continuous_eval_const _)
          ((continuous_eval_const _).add (continuous_eval_const _)))

/-- The local Hölder condition on `K j` defines a closed subset of `C(X × X, ℝ)`. -/
lemma tc_isClosed_holderCond (S : Set X) (M : ℝ) :
    IsClosed {f : C(X × X, ℝ) | ∀ x ∈ S, ∀ y ∈ S, f (x, y) ≤ M * dist x y ^ β} := by
  have e : {f : C(X × X, ℝ) | ∀ x ∈ S, ∀ y ∈ S, f (x, y) ≤ M * dist x y ^ β} =
      ⋂ x ∈ S, ⋂ y ∈ S, {f : C(X × X, ℝ) | f (x, y) ≤ M * dist x y ^ β} := by
    ext f; simp only [mem_iInter, mem_ofPred_eq]
  rw [e]
  exact isClosed_biInter fun x _ => isClosed_biInter fun y _ =>
    isClosed_le (continuous_eval_const _) continuous_const

/-- **Local tightness criterion, structured form**: if all laws of `S` are carried by functions
vanishing on the diagonal with the triangle inequality, and for every `j` and `θ > 0` there is
`M ≥ 0` with `μ[¬(f ≤ M dist^β on K j × K j)] ≤ θ` for all `μ ∈ S`, then for every `ε > 0` there
are `M j ≥ 0` with `μ({f | f ∈ holderMetricSet K M β}ᶜ) ≤ ε` for all `μ ∈ S`. -/
theorem exists_holderMetricSet_measure_compl_le {S : Set (Measure C(X × X, ℝ))}
    (hmet : ∀ μ ∈ S, μ {f : C(X × X, ℝ) |
      ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} = 0)
    (hloc : ∀ (j : ℕ) (θ : ℝ), 0 < θ → ∃ Mj : ℝ, 0 ≤ Mj ∧ ∀ μ ∈ S,
      μ {f : C(X × X, ℝ) | ¬ ∀ x ∈ K j, ∀ y ∈ K j, f (x, y) ≤ Mj * dist x y ^ β} ≤
        ENNReal.ofReal θ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧ ∀ μ ∈ S,
      μ {f : C(X × X, ℝ) | ⇑f ∈ holderMetricSet K M β}ᶜ ≤ ε := by
  obtain ⟨e, he, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    rcases eq_top_or_lt_top ε with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h.ne, by rw [ENNReal.ofReal_toReal h.ne]⟩
  choose M hM0 hMb using fun j => hloc j (e / 2 / 2 ^ j) (by positivity)
  refine ⟨M, hM0, fun μ hμ => ?_⟩
  have hsub : {f : C(X × X, ℝ) | ⇑f ∈ holderMetricSet K M β}ᶜ ⊆
      {f : C(X × X, ℝ) | ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} ∪
        ⋃ j, {f : C(X × X, ℝ) | ¬ ∀ x ∈ K j, ∀ y ∈ K j, f (x, y) ≤ M j * dist x y ^ β} := by
    intro f hf
    by_cases hm : (∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z)
    · right
      simp only [mem_iUnion, mem_ofPred_eq]
      by_contra hc
      push Not at hc
      exact hf ⟨hm.1, hm.2, fun j x hx y hy => hc j x hx y hy⟩
    · left; exact hm
  have hsum : ∑' j, ENNReal.ofReal (e / 2 / 2 ^ j) = ENNReal.ofReal e := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (summable_geometric_two' e),
      tsum_geometric_two']
  calc μ {f : C(X × X, ℝ) | ⇑f ∈ holderMetricSet K M β}ᶜ
      ≤ μ ({f : C(X × X, ℝ) |
          ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} ∪
        ⋃ j, {f : C(X × X, ℝ) | ¬ ∀ x ∈ K j, ∀ y ∈ K j, f (x, y) ≤ M j * dist x y ^ β}) :=
        measure_mono hsub
    _ ≤ 0 + ∑' j, ENNReal.ofReal (e / 2 / 2 ^ j) :=
        (measure_union_le _ _).trans (add_le_add (hmet μ hμ).le
          ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => hMb j μ hμ)))
    _ ≤ ε := by rw [zero_add, hsum]; exact heε

/-- **Local tightness criterion** (the direction used by DGZ Prop 6.3; generalizes
`LQGMetric.LFPP.isTightMeasureSet_of_modulus` to non-compact `X`). -/
theorem isTightMeasureSet_of_holderBounds (hKmono : Monotone K) (hKnhds : ∀ x, ∃ j, K j ∈ 𝓝 x)
    (hβ : 0 < β) {S : Set (Measure C(X × X, ℝ))}
    (hmet : ∀ μ ∈ S, μ {f : C(X × X, ℝ) |
      ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} = 0)
    (hloc : ∀ (j : ℕ) (θ : ℝ), 0 < θ → ∃ Mj : ℝ, 0 ≤ Mj ∧ ∀ μ ∈ S,
      μ {f : C(X × X, ℝ) | ¬ ∀ x ∈ K j, ∀ y ∈ K j, f (x, y) ≤ Mj * dist x y ^ β} ≤
        ENNReal.ofReal θ) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨M, hM0, hMb⟩ := exists_holderMetricSet_measure_compl_le hmet hloc hε
  exact ⟨_, isCompact_holderMetricSet hKmono hKnhds hβ hM0, hMb⟩

end Criterion

variable {d : ℕ}

/-! ### Compact preconnected supersets -/

/-- **Compact connected hulls**: a compact subset `K` of an open connected `U ⊆ ℝ^d` lies in a
compact preconnected `T ⊆ U` (finitely many closed balls covering `K`, joined to a base point of `U`
by paths in `U`). -/
theorem exists_isCompact_isPreconnected_superset {U K : Set (Rd d)} (hU : IsOpen U)
    (hUc : IsConnected U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ T : Set (Rd d), IsCompact T ∧ IsPreconnected T ∧ K ⊆ T ∧ T ⊆ U := by
  have hUp : IsPathConnected U := hU.isConnected_iff_isPathConnected.1 hUc
  obtain ⟨x₀, hx₀⟩ := hUc.nonempty
  have hball : ∀ k ∈ K, ∃ r : ℝ, 0 < r ∧ closedBall k r ⊆ U := fun k hk =>
    nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (hKU hk))
  choose! rad hrad hradU using hball
  obtain ⟨F, hFK, hcov⟩ := hK.elim_nhds_subcover (fun k => ball k (rad k))
    fun k hk => ball_mem_nhds k (hrad k hk)
  have hpath : ∀ k : F, ∃ γ : Path x₀ (k : Rd d), ∀ t, γ t ∈ U := fun k =>
    hUp.joinedIn x₀ hx₀ k (hKU (hFK k k.2))
  choose γ hγ using hpath
  set piece : F → Set (Rd d) := fun k => range (γ k) ∪ closedBall (k : Rd d) (rad k) with hpiece
  refine ⟨⋃ k, piece k, isCompact_iUnion fun k =>
    (isCompact_range (γ k).continuous).union (isCompact_closedBall _ _), ?_, ?_, ?_⟩
  · refine isPreconnected_iUnion ⟨x₀, mem_iInter.2 fun k => Or.inl ⟨0, (γ k).source⟩⟩ fun k => ?_
    exact (isPreconnected_range (γ k).continuous).union (k : Rd d) ⟨1, (γ k).target⟩
      (mem_closedBall_self (hrad k (hFK k k.2)).le) (convex_closedBall _ _).isPreconnected
  · intro z hz
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (hcov hz)
    exact mem_iUnion.2 ⟨⟨k, hk⟩, Or.inr (ball_subset_closedBall hzk)⟩
  · intro z hz
    obtain ⟨k, hzk⟩ := mem_iUnion.1 hz
    rcases hzk with ⟨t, rfl⟩ | hzk
    · exact hγ k t
    · exact hradU k (hFK k k.2) hzk

/-! ### An exhaustion of an open set by compacts -/

/-- `K_j(U) = B̄(0, j) ∖ thickening_{1/(j+1)}(Uᶜ)`, an increasing exhaustion of `U` by compacts. -/
def tcExhaust (U : Set (Rd d)) (j : ℕ) : Set (Rd d) :=
  closedBall (0 : Rd d) j ∩ (thickening (1 / ((j : ℝ) + 1)) Uᶜ)ᶜ

lemma tcExhaust_isCompact (U : Set (Rd d)) (j : ℕ) : IsCompact (tcExhaust U j) :=
  (isCompact_closedBall 0 _).inter_right isOpen_thickening.isClosed_compl

lemma tcExhaust_subset (U : Set (Rd d)) (j : ℕ) : tcExhaust U j ⊆ U := by
  intro y hy
  by_contra hyU
  exact hy.2 (self_subset_thickening (by positivity) _ hyU)

lemma tcExhaust_mono (U : Set (Rd d)) : Monotone (tcExhaust U) := by
  intro i j hij y hy
  refine ⟨closedBall_subset_closedBall (by exact_mod_cast hij) hy.1, fun hth => hy.2 ?_⟩
  refine thickening_mono ?_ _ hth
  have : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
  exact one_div_le_one_div_of_le (by positivity) this

lemma tcExhaust_mem_nhds {U : Set (Rd d)} (hU : IsOpen U) {x : Rd d} (hx : x ∈ U) :
    ∃ j, tcExhaust U j ∈ 𝓝 x := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨j₁, hj₁⟩ := exists_nat_ge (‖x‖ + 1)
  obtain ⟨j₂, hj₂⟩ := exists_nat_one_div_lt (half_pos hr)
  refine ⟨max j₁ j₂, mem_of_superset (ball_mem_nhds x (lt_min one_pos (half_pos hr))) ?_⟩
  intro y hy
  have hy1 : dist y x < 1 := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : dist y x < r / 2 := lt_of_lt_of_le hy (min_le_right _ _)
  refine ⟨?_, fun hth => ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    have : ‖y‖ ≤ ‖x‖ + dist y x := by
      rw [dist_eq_norm]; linarith [norm_le_norm_add_norm_sub' y x]
    have h1 : ((j₁ : ℕ) : ℝ) ≤ ((max j₁ j₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    linarith
  · obtain ⟨w, hw, hyw⟩ := mem_thickening_iff.1 hth
    have hj₂le : (j₂ : ℝ) + 1 ≤ ((max j₁ j₂ : ℕ) : ℝ) + 1 := by
      have : (j₂ : ℝ) ≤ ((max j₁ j₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right j₁ j₂
      linarith
    have h1 : 1 / (((max j₁ j₂ : ℕ) : ℝ) + 1) ≤ 1 / ((j₂ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hj₂le
    have hxw : dist w x < r := by
      calc dist w x ≤ dist w y + dist y x := dist_triangle _ _ _
        _ < r / 2 + r / 2 := by rw [dist_comm] at hyw; linarith
        _ = r := by ring
    exact hw (hrU hxw)

/-! ### The internal metric as a random element of `C(U × U, ℝ)` -/

open Classical in
/-- `a⁻¹ D(·, ·; U)` of the field `φ` as an element of `C(U × U, ℝ)` (junk `0` if it is not
continuous; for continuous `φ` and open preconnected `U` it is, `internalMetricC_apply`). -/
def internalMetricC (ξ : ℝ) (φ : Rd d → ℝ) (U : Set (Rd d)) (a : ℝ) : C(U × U, ℝ) :=
  if h : Continuous (fun p : U × U => a⁻¹ * lfppDistOn ξ φ U p.1 p.2) then ⟨_, h⟩ else 0

/-- Continuity of `(x, y) ↦ a⁻¹ D(x, y; U)` on `U × U` (L3b1's `continuousOn_lfppDistOn`). -/
lemma continuous_internalMetric {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) {U : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsPreconnected U) (a : ℝ) :
    Continuous (fun p : U × U => a⁻¹ * lfppDistOn ξ φ U p.1 p.2) := by
  have h := continuousOn_lfppDistOn hU hUc hφ ξ
  have h2 : Continuous (fun p : U × U => lfppDistOn ξ φ U (p.1 : Rd d) (p.2 : Rd d)) :=
    h.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) fun p => ⟨p.1.2, p.2.2⟩
  exact continuous_const.mul h2

lemma internalMetricC_apply {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) {U : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsPreconnected U) (a : ℝ) (p : U × U) :
    internalMetricC ξ φ U a p = a⁻¹ * lfppDistOn ξ φ U p.1 p.2 := by
  have hc := continuous_internalMetric (ξ := ξ) hφ hU hUc a
  unfold internalMetricC
  split_ifs
  rfl

/-- **Measurability**: for a continuous, measurable random field, `ω ↦ internalMetricC` is
measurable for the Borel σ-algebra of the compact-open topology. -/
theorem measurable_internalMetricC {Ω : Type*} [MeasurableSpace Ω] {H : Rd d → Ω → ℝ}
    (hc : ∀ ω, Continuous fun z => H z ω) (hm : ∀ z, Measurable (H z)) (ξ : ℝ) {U : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsPreconnected U) (a : ℝ) :
    Measurable fun ω => internalMetricC ξ (fun z => H z ω) U a := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  refine ContinuousMap.measurable_iff_eval.2 fun p => ?_
  have heq : (fun ω => internalMetricC ξ (fun z => H z ω) U a p) =
      fun ω => a⁻¹ * lfppDistOn ξ (fun z => H z ω) U p.1 p.2 :=
    funext fun ω => internalMetricC_apply (hc ω) hU hUc a p
  rw [heq]
  exact (measurable_lfppDistOn hc hm hU ξ _ _).const_mul _

/-! ### DGZ Proposition 6.3 on an open connected `U` -/

/-- The exhaustion of `U` seen inside the subtype `U`. -/
def tcExhaustU (U : Set (Rd d)) (j : ℕ) : Set U := ((↑) : U → Rd d) ⁻¹' tcExhaust U j

lemma tcExhaustU_mono (U : Set (Rd d)) : Monotone (tcExhaustU U) := fun _ _ hij _ hx =>
  tcExhaust_mono U hij hx

lemma tcExhaustU_mem_nhds {U : Set (Rd d)} (hU : IsOpen U) (x : U) :
    ∃ j, tcExhaustU U j ∈ 𝓝 x := by
  obtain ⟨j, hj⟩ := tcExhaust_mem_nhds hU x.2
  exact ⟨j, continuous_subtype_val.continuousAt.preimage_mem_nhds hj⟩

/-- **DGZ Prop 6.3, structured form, for `h_{m,n} = h_n - h_m`** (blueprint `r2:prop:63`): under
`Cor52Shape` and `DGZHyp`, for every `β ∈ (0, ξ(Q - √(2d)))` there is `q₂ ∈ (0, 1)` such that for
`q ∈ [q₂, 1)`, every open connected `U`, every `m` and `ε > 0` there are constants `M j ≥ 0` with:
the law of `a^{(q)}_n⁻¹ D(h_n - h_m)(·,·; U)` on `C(U × U, ℝ)` gives mass `≤ ε` to the complement
of the compact set of pseudo-metric-like functions with the local `β`-Hölder bounds `M j` on the
exhaustion `tcExhaustU U j`, for every dyadic realization and every `n`. -/
theorem exists_internalMetricC_holderMetricSet_sub {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hC52 : Cor52Shape d κ ξ Q) (h : DGZHyp d κ ξ Q) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < ξ * (Q - Real.sqrt (2 * d))) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ U : Set (Rd d), IsOpen U → IsConnected U → ∀ (m : ℕ) {ε : ℝ≥0∞}, 0 < ε →
        ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
            (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
              P.map (fun ω => internalMetricC ξ (fun z => H n z ω - H m z ω) U (aQ P H ξ n q))
                {f : C(U × U, ℝ) | ⇑f ∈ holderMetricSet (tcExhaustU U) M β}ᶜ ≤ ε := by
  have hd0 : 0 < d := by have := h.dim; omega
  obtain ⟨q₂, hq₂0, hq₂1, hint⟩ := holder_internal_sub hC52 h hβ0 hβ
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 U hU hUc m ε hε => ?_⟩
  have hq0 : 0 < q := hq₂0.trans_le hq₂q
  have hUp : IsPreconnected U := hUc.isPreconnected
  -- compact preconnected hulls of the exhaustion
  have hT : ∀ j : ℕ, ∃ T : Set (Rd d), IsCompact T ∧ IsPreconnected T ∧ tcExhaust U j ⊆ T ∧
      T ⊆ U := fun j => exists_isCompact_isPreconnected_superset hU hUc
        (tcExhaust_isCompact U j) (tcExhaust_subset U j)
  choose T hTc hTp hKT hTU using hT
  -- the family of laws
  set S : Set (Measure C(U × U, ℝ)) := {μ | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H ∧ ∃ n : ℕ,
      μ = P.map (fun ω => internalMetricC ξ (fun z => H n z ω - H m z ω) U (aQ P H ξ n q))}
    with hS
  have hmet : ∀ μ ∈ S, μ {f : C(U × U, ℝ) |
      ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} = 0 := by
    rintro μ ⟨Ω, _, P, W, H, hH, n, rfl⟩
    have hφc : ∀ ω, Continuous fun z => H n z ω - H m z ω := fun ω =>
      ((hH.band n).continuous ω).sub ((hH.band m).continuous ω)
    have hFm := measurable_internalMetricC (H := fun z ω => H n z ω - H m z ω) hφc
      (fun z => ((hH.band n).measurable z).sub ((hH.band m).measurable z)) ξ hU hUp
      (aQ P H ξ n q)
    have hmeasA : MeasurableSet {f : C(U × U, ℝ) |
        ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} :=
      tc_isClosed_metricCond.isOpen_compl.measurableSet
    rw [Measure.map_apply hFm hmeasA]
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    apply hω
    have ha0 : 0 ≤ (aQ P H ξ n q)⁻¹ := (inv_pos.2 (tight_aQ_pos hd0 hH ξ n hq0 hq1)).le
    refine ⟨fun x => ?_, fun x y z => ?_⟩
    · rw [internalMetricC_apply (hφc ω) hU hUp, lfppDistOn_self, mul_zero]
    · rw [internalMetricC_apply (hφc ω) hU hUp, internalMetricC_apply (hφc ω) hU hUp,
        internalMetricC_apply (hφc ω) hU hUp, ← mul_add]
      exact mul_le_mul_of_nonneg_left (lfppDistOn_triangle_of_isPreconnected hU hUp (hφc ω)
        x.2 y.2 z.2) ha0
  have hloc : ∀ (j : ℕ) (θ : ℝ), 0 < θ → ∃ Mj : ℝ, 0 ≤ Mj ∧ ∀ μ ∈ S,
      μ {f : C(U × U, ℝ) | ¬ ∀ x ∈ tcExhaustU U j, ∀ y ∈ tcExhaustU U j,
        f (x, y) ≤ Mj * dist x y ^ β} ≤ ENNReal.ofReal θ := by
    intro j θ hθ
    obtain ⟨Mj, hMj, hMjb⟩ := hint q hq₂q hq1 U (T j) hU (hTc j) (hTp j) (hTU j) m θ hθ
    refine ⟨Mj, hMj.le, ?_⟩
    rintro μ ⟨Ω, _, P, W, H, hH, n, rfl⟩
    have hφc : ∀ ω, Continuous fun z => H n z ω - H m z ω := fun ω =>
      ((hH.band n).continuous ω).sub ((hH.band m).continuous ω)
    have hFm := measurable_internalMetricC (H := fun z ω => H n z ω - H m z ω) hφc
      (fun z => ((hH.band n).measurable z).sub ((hH.band m).measurable z)) ξ hU hUp
      (aQ P H ξ n q)
    have hclosed : IsClosed {f : C(U × U, ℝ) | ∀ x ∈ tcExhaustU U j, ∀ y ∈ tcExhaustU U j,
        f (x, y) ≤ Mj * dist x y ^ β} := tc_isClosed_holderCond _ _
    have hmeasB : MeasurableSet {f : C(U × U, ℝ) | ¬ ∀ x ∈ tcExhaustU U j,
        ∀ y ∈ tcExhaustU U j, f (x, y) ≤ Mj * dist x y ^ β} := hclosed.isOpen_compl.measurableSet
    rw [Measure.map_apply hFm hmeasB]
    refine le_trans (measure_mono fun ω hω => ?_) (hMjb Ω P W H hH n)
    simp only [mem_preimage, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨x, hx, y, hy, hlt⟩ := hω
    have ha0 := tight_aQ_pos hd0 hH ξ n hq0 hq1
    rw [internalMetricC_apply (hφc ω) hU hUp, Subtype.dist_eq, dist_eq_norm] at hlt
    refine ⟨x, hKT j hx, y, hKT j hy, ?_⟩
    have := (lt_inv_mul_iff₀ ha0).1 hlt
    linarith
  exact exists_holderMetricSet_measure_compl_le hmet hloc hε |>.imp fun M hM =>
    ⟨hM.1, fun Ω _ P W H hH n => hM.2 _ ⟨Ω, _, P, W, H, hH, n, rfl⟩⟩

/-- **DGZ Proposition 6.3 for `h_{m,n} = h_n - h_m`** (blueprint `r2:prop:63`): there is
`q₂ ∈ (0, 1)` such that for `q ∈ [q₂, 1)`, every open connected `U` and every `m`, the laws of
`a^{(q)}_n⁻¹ D(h_n - h_m)(·,·; U)` on `C(U × U, ℝ)`, over all dyadic realizations and all `n`, are
tight. -/
theorem isTightMeasureSet_internalMetricC_sub {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hC52 : Cor52Shape d κ ξ Q) (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ U : Set (Rd d), IsOpen U → IsConnected U → ∀ m : ℕ,
        IsTightMeasureSet {μ : Measure C(U × U, ℝ) | ∃ (Ω : Type) (_ : MeasurableSpace Ω)
          (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
            IsDyadicRealization κ P W H ∧ ∃ n : ℕ,
              μ = P.map (fun ω => internalMetricC ξ (fun z => H n z ω - H m z ω) U
                (aQ P H ξ n q))} := by
  have hξ := h.xi_pos
  have hg : 0 < ξ * (Q - Real.sqrt (2 * d)) := mul_pos hξ (by linarith [h.subcritical])
  obtain ⟨q₂, hq₂0, hq₂1, hstr⟩ := exists_internalMetricC_holderMetricSet_sub hC52 h
    (β := ξ * (Q - Real.sqrt (2 * d)) / 2) (by positivity) (by linarith)
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 U hU hUc m => ?_⟩
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨M, hM0, hMb⟩ := hstr q hq₂q hq1 U hU hUc m hε
  refine ⟨_, isCompact_holderMetricSet (β := ξ * (Q - Real.sqrt (2 * d)) / 2)
    (tcExhaustU_mono U) (tcExhaustU_mem_nhds hU) (by positivity) hM0, ?_⟩
  rintro μ ⟨Ω, _, P, W, H, hH, n, rfl⟩
  exact hMb Ω P W H hH n

/-- **DGZ Proposition 6.3 for `h_n`** (`m = 0` in the blueprint's convention `h_{0,n} = h_n`): the
laws of `a^{(q)}_n⁻¹ D_n(·,·; U)` on `C(U × U, ℝ)` are tight. (The field `h_n` and `h_n - h_0` have
the same law since `h_0 = H_{1,1}` vanishes a.s.) -/
theorem isTightMeasureSet_internalMetricC {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hC52 : Cor52Shape d κ ξ Q) (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ U : Set (Rd d), IsOpen U → IsConnected U →
        IsTightMeasureSet {μ : Measure C(U × U, ℝ) | ∃ (Ω : Type) (_ : MeasurableSpace Ω)
          (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
            IsDyadicRealization κ P W H ∧ ∃ n : ℕ,
              μ = P.map (fun ω => internalMetricC ξ (fun z => H n z ω) U (aQ P H ξ n q))} := by
  obtain ⟨q₂, hq₂0, hq₂1, htight⟩ := isTightMeasureSet_internalMetricC_sub hC52 h
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 U hU hUc => ?_⟩
  refine (htight q hq₂q hq1 U hU hUc 0).subset ?_
  rintro μ ⟨Ω, _, P, W, H, hH, n, rfl⟩
  refine ⟨Ω, _, P, W, H, hH, n, Measure.map_congr ?_⟩
  have h0 := ae_forall_eq_zero_of_isBandVersion_self h.kernel hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  filter_upwards [h0] with ω hω
  have e : (fun z => H n z ω - H 0 z ω) = fun z => H n z ω := funext fun z => by
    rw [hω z, sub_zero]
  simp only [e]

/-! ### DGZ Proposition 6.3 for the whole-space metric (`normMetricC`) -/

lemma normMetricC_apply {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) (a : ℝ)
    (p : Rd d × Rd d) : normMetricC ξ φ a p = a⁻¹ * lfppMetric ξ φ p.1 p.2 := by
  have hc : Continuous (fun p : Rd d × Rd d => a⁻¹ * lfppMetric ξ φ p.1 p.2) :=
    continuous_const.mul (continuous_lfppMetric hφ ξ)
  unfold normMetricC
  split_ifs
  rfl

/-- **Measurability of `normMetricC`** (L3b1's `measurable_continuousMap_of_eq_lfppMetric`). -/
theorem measurable_normMetricC {Ω : Type*} [MeasurableSpace Ω] {H : Rd d → Ω → ℝ}
    (hc : ∀ ω, Continuous fun z => H z ω) (hm : ∀ z, Measurable (H z)) (ξ a : ℝ) :
    Measurable fun ω => normMetricC ξ (fun z => H z ω) a :=
  measurable_continuousMap_of_eq_lfppMetric hc hm ξ a⁻¹ fun ω p => normMetricC_apply (hc ω) a p

lemma tc_closedBall_mono : Monotone fun j : ℕ => closedBall (0 : Rd d) j := fun _ _ hij =>
  closedBall_subset_closedBall (by exact_mod_cast hij)

lemma tc_closedBall_mem_nhds (x : Rd d) : ∃ j : ℕ, closedBall (0 : Rd d) j ∈ 𝓝 x := by
  obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
  exact ⟨j, closedBall_mem_nhds_of_mem (by rw [mem_ball, dist_zero_right]; exact hj)⟩

/-- **DGZ Prop 6.3, structured form, for the whole-space metric**: for `β ∈ (0, ξ(Q - √(2d)))`
there is `q₂ ∈ (0, 1)` such that for `q ∈ [q₂, 1)` and `ε > 0` there are `M j ≥ 0` with: the law of
`normMetricC ξ h_n a^{(q)}_n` (`= a^{(q)}_n⁻¹ D_n` on `C(ℝ^d × ℝ^d, ℝ)`) gives mass `≤ ε` to the
complement of the compact set of pseudo-metric-like functions with the `β`-Hölder bounds `M j` on
`B̄(0, j)`, for every dyadic realization and every `n`. -/
theorem exists_normMetricC_holderMetricSet {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hC52 : Cor52Shape d κ ξ Q) (h : DGZHyp d κ ξ Q) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < ξ * (Q - Real.sqrt (2 * d))) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 → ∀ {ε : ℝ≥0∞}, 0 < ε →
      ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
            P.map (fun ω => normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))
              {f : C(Rd d × Rd d, ℝ) |
                ⇑f ∈ holderMetricSet (fun j : ℕ => closedBall (0 : Rd d) j) M β}ᶜ ≤ ε := by
  have hd0 : 0 < d := by have := h.dim; omega
  obtain ⟨q₂, hq₂0, hq₂1, hint⟩ := holder_internal hC52 h hβ0 hβ
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 ε hε => ?_⟩
  have hq0 : 0 < q := hq₂0.trans_le hq₂q
  set S : Set (Measure C(Rd d × Rd d, ℝ)) := {μ | ∃ (Ω : Type) (_ : MeasurableSpace Ω)
    (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H ∧
      ∃ n : ℕ, μ = P.map (fun ω => normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))} with hS
  have hmet : ∀ μ ∈ S, μ {f : C(Rd d × Rd d, ℝ) |
      ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} = 0 := by
    rintro μ ⟨Ω, _, P, W, H, hH, n, rfl⟩
    have hFm := measurable_normMetricC (H := H n) (hH.band n).continuous (hH.band n).measurable
      ξ (aQ P H ξ n q)
    have hmeasA : MeasurableSet {f : C(Rd d × Rd d, ℝ) |
        ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} :=
      tc_isClosed_metricCond.isOpen_compl.measurableSet
    rw [Measure.map_apply hFm hmeasA]
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    apply hω
    have hφ := (hH.band n).continuous ω
    have ha0 : 0 ≤ (aQ P H ξ n q)⁻¹ := (inv_pos.2 (tight_aQ_pos hd0 hH ξ n hq0 hq1)).le
    refine ⟨fun x => ?_, fun x y z => ?_⟩
    · rw [normMetricC_apply hφ, lfppMetric_self, mul_zero]
    · rw [normMetricC_apply hφ, normMetricC_apply hφ, normMetricC_apply hφ, ← mul_add]
      exact mul_le_mul_of_nonneg_left (lfppMetric_triangle hφ x y z) ha0
  have hloc : ∀ (j : ℕ) (θ : ℝ), 0 < θ → ∃ Mj : ℝ, 0 ≤ Mj ∧ ∀ μ ∈ S,
      μ {f : C(Rd d × Rd d, ℝ) | ¬ ∀ x ∈ closedBall (0 : Rd d) j, ∀ y ∈ closedBall (0 : Rd d) j,
        f (x, y) ≤ Mj * dist x y ^ β} ≤ ENNReal.ofReal θ := by
    intro j θ hθ
    obtain ⟨Mj, hMj, hMjb⟩ := hint q hq₂q hq1 univ (closedBall (0 : Rd d) j) isOpen_univ
      (isCompact_closedBall _ _) (convex_closedBall _ _).isPreconnected (subset_univ _) θ hθ
    refine ⟨Mj, hMj.le, ?_⟩
    rintro μ ⟨Ω, _, P, W, H, hH, n, rfl⟩
    have hFm := measurable_normMetricC (H := H n) (hH.band n).continuous (hH.band n).measurable
      ξ (aQ P H ξ n q)
    have hmeasB : MeasurableSet {f : C(Rd d × Rd d, ℝ) | ¬ ∀ x ∈ closedBall (0 : Rd d) j,
        ∀ y ∈ closedBall (0 : Rd d) j, f (x, y) ≤ Mj * dist x y ^ β} :=
      (tc_isClosed_holderCond _ _).isOpen_compl.measurableSet
    rw [Measure.map_apply hFm hmeasB]
    refine le_trans (measure_mono fun ω hω => ?_) (hMjb Ω P W H hH n)
    simp only [mem_preimage, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨x, hx, y, hy, hlt⟩ := hω
    have ha0 := tight_aQ_pos hd0 hH ξ n hq0 hq1
    rw [normMetricC_apply ((hH.band n).continuous ω), dist_eq_norm] at hlt
    refine ⟨x, hx, y, hy, ?_⟩
    have := (lt_inv_mul_iff₀ ha0).1 hlt
    show Mj * aQ P H ξ n q * ‖x - y‖ ^ β < lfppMetric ξ (fun z => H n z ω) x y
    linarith
  exact exists_holderMetricSet_measure_compl_le hmet hloc hε |>.imp fun M hM =>
    ⟨hM.1, fun Ω _ P W H hH n => hM.2 _ ⟨Ω, _, P, W, H, hH, n, rfl⟩⟩

/-- **DGZ Proposition 6.3 for the whole-space metric** (blueprint `r2:prop:63` with `U = ℝ^d`):
there is `q₂ ∈ (0, 1)` such that for `q ∈ [q₂, 1)` the laws of `normMetricC ξ h_n a^{(q)}_n` on
`C(ℝ^d × ℝ^d, ℝ)`, over all dyadic realizations and all `n`, are tight. -/
theorem isTightMeasureSet_normMetricC {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hC52 : Cor52Shape d κ ξ Q) (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      IsTightMeasureSet {μ : Measure C(Rd d × Rd d, ℝ) | ∃ (Ω : Type) (_ : MeasurableSpace Ω)
        (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
          IsDyadicRealization κ P W H ∧ ∃ n : ℕ,
            μ = P.map (fun ω => normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))} := by
  have hξ := h.xi_pos
  have hg : 0 < ξ * (Q - Real.sqrt (2 * d)) := mul_pos hξ (by linarith [h.subcritical])
  obtain ⟨q₂, hq₂0, hq₂1, hstr⟩ := exists_normMetricC_holderMetricSet hC52 h
    (β := ξ * (Q - Real.sqrt (2 * d)) / 2) (by positivity) (by linarith)
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 => ?_⟩
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨M, hM0, hMb⟩ := hstr q hq₂q hq1 hε
  refine ⟨_, isCompact_holderMetricSet (β := ξ * (Q - Real.sqrt (2 * d)) / 2)
    tc_closedBall_mono tc_closedBall_mem_nhds (by positivity) hM0, ?_⟩
  rintro μ ⟨Ω, _, P, W, H, hH, n, rfl⟩
  exact hMb Ω P W H hH n

end DGZ

end HigherDimLQGMetric
