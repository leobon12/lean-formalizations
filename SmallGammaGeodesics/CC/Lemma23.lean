import SmallGammaGeodesics.CC.Lemma23Close
import SmallGammaGeodesics.CC.LawEqCont
import SmallGammaGeodesics.CC.LusinRestrict
import SmallGammaGeodesics.CC.UniversalLocality
import SmallGammaGeodesics.CC.LocalityConf
import SmallGammaGeodesics.CC.ConfMetric
import LQGMetric.Field.GFFLaw
import LQGMetric.Field.RandomDistVersion
import LQGMetric.Metric.InternalC

/-!
# [3] Lemma 2.3*: small-scale closeness in probability on the NIC spaces (track CC, packet CC6a, T2)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D9** (replaces [3] Lemmas
2.3–2.5 of Gwynne–Miller arXiv:1905.00384); rulings G19–G26 (G25: `restrictPair`).

Fix `R > 0`, `B = B_{R/2}(0)`, a test function `ρ` supported in `B̄_{R/2}` with `∫ ρ = 1`, a compact
`K₁ ⊆ B` and `δ > 0`. Let `(Ω n, P n, h n, h̄ n, K n)` be near-identity couplings on `B_R`
(`IsNICCoupling`, CC4) for `ε_n`-near-identity diffeomorphisms `Φ_n` (`IsNearIdDiffeo`,
`‖Φ_n − id‖ ≤ ε_n`), with `E sup_{B̄_{R/2}} |K n − K n(0)| ≤ ε_n → 0`, and let `K̃ n ω` be
continuous with `|K̃ n − K n| ≤ ε_n` on `B` (e.g. D9's extension of `K n` from `B̄_{3R/4}`, for
which the difference is `0`). Put `𝐌_n = D_{h̄ n + K̃ n}(·,·; B)` (the coupled metric of
`h n ∘ Φ_n⁻¹`) and `𝐌'_n = D_{h n}(·,·; B)`. **Lemma 2.3*** (`lemma23_seq`):
`P_n(∃ u, v ∈ K₁, |𝐌_n(u, v) − 𝐌'_n(u, v)| > δ e^{ξ ⟨h n, ρ⟩}) → 0`.

Proof (D9):
1. *Normalize*: `ĝ = h − ⟨h, ρ⟩`, `ĝ̄ = h̄ − ⟨h̄, ρ⟩` (`GFFLaw.recenter`) are whole-plane GFFs whose
   coordinate vectors `coordVec` (the `pairJ B` coordinates of the restriction to `B`, reindexed by
   `ℕ`) have one law `μ` for all `n` (`map_coordVec_eq`, from `GFFLaw.map_comp_eq_of_sigma0`).
2. *Closeness*: the coordinates differ by `⟨h̄ n, e₀⟩ − ⟨h n, e₀⟩` with `e₀ = e − (∫ e) ρ` mean
   zero, which tends to `0` in probability (`tendsto_prob_pairing`, `CC/Lemma23Close.lean`).
3. *One functional*: universal locality (CC2) for the countable family `{ĝ̄ n, ĝ n}` gives one
   measurable `F` with `D_{ĝ}(·,·;B) = F(ĝ|_B)` a.s.; `d y = F(pairJInv B (y ∘ s⁻¹))` is the same
   functional in coordinates (`pairJInv_coordVec`).
4. *LawEqCont* (CC5, `lawEqCont_restrictPair`) with `F̂ = restrictPair d K₁` (ruling G25):
   `sup_{K₁²} |D_{ĝ̄ n} − D_{ĝ n}|(·,·;B) → 0` in probability, and the sup norms of `F̂(Y n)` are
   tight because they all have the law of `‖F̂‖` under `μ`.
5. *Back to the metrics*: by Weyl scaling, `𝐌_n ∈ e^{ξ⟨h n, ρ⟩} [e^{−t_n}, e^{t_n}] D_{ĝ̄ n}(·,·;B)`
   with `t_n = |ξ| (|⟨h̄ n, ρ⟩ − ⟨h n, ρ⟩ + K n(0)| + sup |K n − K n(0)| + ε_n) → 0` in probability,
   and `𝐌'_n = e^{ξ⟨h n, ρ⟩} D_{ĝ n}(·,·;B)`; the elementary inequality `lemma23_core_bound`
   concludes.

`lemma23_seq_small` is the version with `ε n ≤ 1/32` for all `n`; `lemma23_seq` removes it by
shifting the sequence; `lemma23_uniform` is the uniform (ε–δ) form, obtained from `lemma23_seq` by
contradiction along sequences (the argument of D10, done once). The zoom specializations are in
`CC/Lemma23Zoom.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## 1. Coordinates of the recentred field on an open set -/

/-- **The coordinate vector** (CC0 D9 step 2): the `pairJ O` coordinates of the restriction to `O`
of
the recentred field `x − ⟨x, ρ⟩`, reindexed by `s : ℕ → CoordJ`. -/
def coordVec (ρ : TestC) (O : TopologicalSpace.Opens ℂ) (s : ℕ → CoordJ) (x : DistC) : ℕ → ℝ :=
  fun k => GFFLaw.recenter ρ x (combC O (s k))

theorem coordVec_apply (ρ : TestC) (O : TopologicalSpace.Opens ℂ) (s : ℕ → CoordJ) (x : DistC)
    (k : ℕ) :
    coordVec ρ O s x k = x (combC O (s k) - (∫ y, combC O (s k) y) • ρ) :=
  GFFLaw.recenter_apply ρ x _

/-- the coordinates depend only on the field modulo additive constants (`σ₀`-measurability) -/
theorem measurable_coordVec_sigma0 {ρ : TestC} (hρ : ∫ x, ρ x = 1) (O : TopologicalSpace.Opens ℂ)
    (s : ℕ → CoordJ) : Measurable[GFFLaw.sigma0] (coordVec ρ O s) :=
  (@measurable_pi_iff DistC ℕ (fun _ => ℝ) GFFLaw.sigma0 _ (coordVec ρ O s)).2 fun k =>
    (GFFInv.measurable_pair (combC O (s k))).comp (GFFLaw.measurable_recenter_sigma0 hρ)

theorem measurable_coordVec (ρ : TestC) (O : TopologicalSpace.Opens ℂ) (s : ℕ → CoordJ) :
    Measurable (coordVec ρ O s) :=
  measurable_pi_iff.2 fun k => by
    simp only [coordVec_apply]
    exact GFFInv.measurable_pair _

/-- **One law for all whole-plane GFFs** (D9 step 1). -/
theorem map_coordVec_eq {ρ : TestC} (hρ : ∫ x, ρ x = 1) (O : TopologicalSpace.Opens ℂ)
    (s : ℕ → CoordJ) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsWholePlaneGFF h P)
    (hh' : IsWholePlaneGFF h' P') : P.map (coordVec ρ O s ∘ h) = P'.map (coordVec ρ O s ∘ h') :=
  GFFLaw.map_comp_eq_of_sigma0 (measurable_coordVec_sigma0 hρ O s) hh hh'

/-- From the coordinates back to the restriction: `pairJInv O (y ∘ s⁻¹)` is the restriction of the
recentred field. -/
theorem pairJInv_coordVec {ρ : TestC} {O : TopologicalSpace.Opens ℂ} {s : ℕ → CoordJ}
    (hs : Function.Surjective s) (x : DistC) :
    pairJInv O (fun c => coordVec ρ O s x (Function.surjInv hs c)) =
      restrictTo O (GFFLaw.recenter ρ x) := by
  have e : (fun c => coordVec ρ O s x (Function.surjInv hs c)) =
      pairJ O (restrictTo O (GFFLaw.recenter ρ x)) := by
    funext c
    show GFFLaw.recenter ρ x (combC O (s (Function.surjInv hs c))) = _
    rw [Function.surjInv_eq hs c]
    rfl
  rw [e, pairJInv_pairJ]

/-! ## 2. Internal metrics of length metrics on balls -/

/-- the internal metric of a length metric on a ball is finite and continuous there -/
theorem internal_ball_lt_top {X : ContMetric} (hX : X.IsLength) {r : ℝ} {u v : ℂ}
    (hu : u ∈ ball (0 : ℂ) r) (hv : v ∈ ball (0 : ℂ) r) : X.internal (ball 0 r) u v < ⊤ := by
  refine lt_top_of_mem_connectedComponentIn (d := X.internal (ball 0 r)) isOpen_ball
    (X.continuousOn_internal hX isOpen_ball)
    (fun z hz => MetricGeometry.internalEDist_self ⟨z, hz, rfl⟩)
    (fun z w => MetricGeometry.internalEDist_comm _ _ _)
    (fun x y z => MetricGeometry.internalEDist_triangle _ _ _ _) hu ?_
  exact (convex_ball (0 : ℂ) r).isPreconnected.subset_connectedComponentIn hu subset_rfl hv

/-! ## 3. The deterministic core of D9 step 6 -/

/-- **The elementary inequality behind D9 step 6.** Let `a = aR`, `b = bR` (finite), with
`|aR − bR| ≤ Δ`, `aR ≤ A`, `E e^{−t} a ≤ M ≤ E e^{t} a`, `M' = E b` and `Δ + (e^t − 1) A ≤ δ`. Then
`M ≤ M' + δE` and `M' ≤ M + δE`. -/
theorem lemma23_core_bound {M M' a b : ℝ≥0∞} {aR bR Δ A t δ E : ℝ}
    (ha : a = ENNReal.ofReal aR) (hb : b = ENNReal.ofReal bR) (haR : 0 ≤ aR) (hbR : 0 ≤ bR)
    (hab : |aR - bR| ≤ Δ) (hA : aR ≤ A) (ht : 0 ≤ t) (hE : 0 < E)
    (hM1 : ENNReal.ofReal (E * Real.exp (-t)) * a ≤ M)
    (hM2 : M ≤ ENNReal.ofReal (E * Real.exp t) * a) (hM' : M' = ENNReal.ofReal E * b)
    (hsmall : Δ + (Real.exp t - 1) * A ≤ δ) :
    M ≤ M' + ENNReal.ofReal (δ * E) ∧ M' ≤ M + ENNReal.ofReal (δ * E) := by
  have hx1 : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hy0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hxy : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hy1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hab' := abs_le.1 hab
  have hA0 : 0 ≤ A := haR.trans hA
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans hab
  have hxA : 0 ≤ (Real.exp t - 1) * A := mul_nonneg (by linarith) hA0
  have hδ0 : 0 ≤ δ := by linarith
  -- (e^t − 1) aR ≤ (e^t − 1) A
  have h1 : (Real.exp t - 1) * aR ≤ (Real.exp t - 1) * A :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  -- (1 − e^{−t}) aR ≤ (e^t − 1) aR
  have h2 : (1 - Real.exp (-t)) * aR ≤ (Real.exp t - 1) * aR := by
    refine mul_le_mul_of_nonneg_right ?_ haR
    nlinarith
  rw [ha] at hM1 hM2
  rw [hb] at hM'
  rw [← ENNReal.ofReal_mul (mul_nonneg hE.le hy0.le)] at hM1
  rw [← ENNReal.ofReal_mul (mul_nonneg hE.le (Real.exp_pos _).le)] at hM2
  rw [← ENNReal.ofReal_mul hE.le] at hM'
  constructor
  · rw [hM', ← ENNReal.ofReal_add (mul_nonneg hE.le hbR) (mul_nonneg hδ0 hE.le)]
    refine hM2.trans (ENNReal.ofReal_le_ofReal ?_)
    have : Real.exp t * aR ≤ bR + δ := by nlinarith
    calc E * Real.exp t * aR = E * (Real.exp t * aR) := by ring
      _ ≤ E * (bR + δ) := mul_le_mul_of_nonneg_left this hE.le
      _ = E * bR + δ * E := by ring
  · rw [hM']
    refine le_trans ?_ (add_le_add hM1 (le_refl _))
    rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hE.le hy0.le) haR) (mul_nonneg hδ0 hE.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : bR ≤ Real.exp (-t) * aR + δ := by nlinarith
    calc E * bR ≤ E * (Real.exp (-t) * aR + δ) := mul_le_mul_of_nonneg_left this hE.le
      _ = E * Real.exp (-t) * aR + δ * E := by ring

/-- **D9 step 6, pointwise** (deterministic): for one sample. `Xb = D_{ĝ̄}`, `X = D_{ĝ}` are length
metrics; `d y`, `d y'` agree with their internal metrics on `B = B_r(0) ⊇ K₁`; `Mf` (the coupled
metric) is within the factors `E e^{±t}` of `Xb(·,·;B)` and `M'f = E X(·,·;B)`. If
`dist (F̂ y) (F̂ y') + (e^t − 1) ‖F̂ y‖ ≤ δ` with `F̂ = restrictPair d K₁`, then `Mf` and `M'f`
differ by at
most `δ E` on `K₁ × K₁`. -/
theorem lemma23_pointwise {X Xb : ContMetric} (hX : X.IsLength) (hXb : Xb.IsLength) {r : ℝ}
    {K₁ : Set ℂ} [CompactSpace K₁] (hK₁ : K₁ ⊆ ball 0 r) {d : (ℕ → ℝ) → ℂ → ℂ → ℝ≥0∞}
    {y y' : ℕ → ℝ}
    (hdy : ∀ z ∈ ball (0 : ℂ) r, ∀ w ∈ ball (0 : ℂ) r, d y z w = Xb.internal (ball 0 r) z w)
    (hdy' : ∀ z ∈ ball (0 : ℂ) r, ∀ w ∈ ball (0 : ℂ) r, d y' z w = X.internal (ball 0 r) z w)
    {Mf M'f : ℂ → ℂ → ℝ≥0∞} {E t δ : ℝ} (hE : 0 < E) (ht : 0 ≤ t)
    (hM1 : ∀ u ∈ K₁, ∀ v ∈ K₁,
      ENNReal.ofReal (E * Real.exp (-t)) * Xb.internal (ball 0 r) u v ≤ Mf u v)
    (hM2 : ∀ u ∈ K₁, ∀ v ∈ K₁,
      Mf u v ≤ ENNReal.ofReal (E * Real.exp t) * Xb.internal (ball 0 r) u v)
    (hM' : ∀ u ∈ K₁, ∀ v ∈ K₁, M'f u v = ENNReal.ofReal E * X.internal (ball 0 r) u v)
    (hsmall : dist (restrictPair d K₁ y) (restrictPair d K₁ y') +
      (Real.exp t - 1) * ‖restrictPair d K₁ y‖ ≤ δ) :
    ∀ u ∈ K₁, ∀ v ∈ K₁,
      Mf u v ≤ M'f u v + ENNReal.ofReal (δ * E) ∧ M'f u v ≤ Mf u v + ENNReal.ofReal (δ * E) := by
  -- finiteness and continuity of `d y`, `d y'` on `K₁ × K₁`
  have hfin : ∀ (Z : ContMetric), Z.IsLength → ∀ (y₀ : ℕ → ℝ),
      (∀ z ∈ ball (0 : ℂ) r, ∀ w ∈ ball (0 : ℂ) r, d y₀ z w = Z.internal (ball 0 r) z w) →
      (∀ u ∈ K₁, ∀ v ∈ K₁, d y₀ u v ≠ ⊤) ∧
        ContinuousOn (fun p : ℂ × ℂ => d y₀ p.1 p.2) (K₁ ×ˢ K₁) := by
    intro Z hZ y₀ hy₀
    refine ⟨fun u hu v hv => ?_, ?_⟩
    · rw [hy₀ u (hK₁ hu) v (hK₁ hv)]
      exact (internal_ball_lt_top hZ (hK₁ hu) (hK₁ hv)).ne
    · refine ((Z.continuousOn_internal hZ isOpen_ball).mono (prod_mono hK₁ hK₁)).congr ?_
      intro p hp
      exact hy₀ p.1 (hK₁ hp.1) p.2 (hK₁ hp.2)
  obtain ⟨hfy, hcy⟩ := hfin Xb hXb y hdy
  obtain ⟨hfy', hcy'⟩ := hfin X hX y' hdy'
  intro u hu v hv
  have hab := abs_sub_le_dist_restrictPair hfy hcy hfy' hcy' hu hv
  have happ := restrictPair_apply hfy hcy (⟨u, hu⟩, ⟨v, hv⟩)
  have hA : (d y u v).toReal ≤ ‖restrictPair d K₁ y‖ := by
    have := ContinuousMap.norm_coe_le_norm (restrictPair d K₁ y) (⟨u, hu⟩, ⟨v, hv⟩)
    rw [happ, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  rw [hdy u (hK₁ hu) v (hK₁ hv), hdy' u (hK₁ hu) v (hK₁ hv)] at hab
  rw [hdy u (hK₁ hu) v (hK₁ hv)] at hA
  have hau : Xb.internal (ball 0 r) u v ≠ ⊤ := (internal_ball_lt_top hXb (hK₁ hu) (hK₁ hv)).ne
  have hbu : X.internal (ball 0 r) u v ≠ ⊤ := (internal_ball_lt_top hX (hK₁ hu) (hK₁ hv)).ne
  exact lemma23_core_bound (ENNReal.ofReal_toReal hau).symm (ENNReal.ofReal_toReal hbu).symm
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hab hA ht hE (hM1 u hu v hv) (hM2 u hu v hv)
    (hM' u hu v hv) hsmall

/-! ## 4. Lemma 2.3* along a sequence of near-identity couplings -/

section Main

variable {γ : ℝ} {D : DistC → ContMetric}

/-- **[3] Lemma 2.3*, with `ε n ≤ 1/32`** (the version with the near-identity transports defined for
every `n`; `lemma23_seq` removes the restriction). Let `D` be a strong γ-LQG metric, `R > 0`, `ρ` a
test function supported in `B̄_{R/2}` with `∫ ρ = 1`, `K₁ ⊆ B_{R/2}` compact and `δ > 0`. Let
`(Ω n, P n, h n, h̄ n, K n)` be near-identity couplings on `B_R` (`IsNICCoupling`) of `Φ n`, where
`Φ n` is an `ε n`-near-identity diffeomorphism with inverse `Ψ n` (`IsNearIdDiffeo`,
`‖Φ n − id‖ ≤ ε n`, `ε n ≤ 1/32`), `E sup_{B̄_{R/2}} |K n − K n(0)| ≤ ε n` and `ε n → 0`; and let
`K̃ n ω` be continuous with `|K̃ n ω − K n ω| ≤ ε n` on `B_{R/2}`. Then the probability that
`𝐌_n = D_{h̄ n + K̃ n}(·,·; B_{R/2})` and `𝐌'_n = D_{h n}(·,·; B_{R/2})` differ by more than
`δ e^{ξ ⟨h n, ρ⟩}` somewhere on `K₁ × K₁` tends to `0`. -/
theorem lemma23_seq_small (hD : IsStrongLQGMetric γ D) {R : ℝ} (hR : 0 < R) {ρ : TestC}
    (hρs : tsupport (ρ : ℂ → ℝ) ⊆ closedBall 0 (R / 2)) (hρ1 : ∫ x, ρ x = 1)
    {K₁ : Set ℂ} (hK₁ : IsCompact K₁) (hK₁B : K₁ ⊆ ball 0 (R / 2))
    {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {Φ Ψ : ℕ → ℂ → ℂ} {B ε : ℕ → ℝ}
    {h hbar : ∀ n, Ω n → DistC} {K : ∀ n, Ω n → ℂ → ℝ} {Kt : ∀ n, Ω n → C(ℂ, ℝ)}
    (hc : ∀ n, IsNICCoupling (P n) (Φ n) (ball 0 R) (B n) (h n) (hbar n) (K n))
    (hΦ : ∀ n, IsNearIdDiffeo (Φ n) (Ψ n) (ball 0 R) (ε n))
    (hΦsub : ∀ n x, ‖Φ n x - x‖ ≤ ε n) (hε32 : ∀ n, ε n ≤ 1 / 32)
    (hε : Tendsto ε atTop (𝓝 0))
    (hsup : ∀ n, ∫⁻ ω, supDev (K n ω) (R / 2) ∂(P n) ≤ ENNReal.ofReal (ε n))
    (hKt : ∀ n ω, ∀ x ∈ ball (0 : ℂ) (R / 2), |Kt n ω x - K n ω x| ≤ ε n)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P n {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
      (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v ≤
          (D (h n ω)).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (xiGamma γ * h n ω ρ)) ∧
      (D (h n ω)).internal (ball 0 (R / 2)) u v ≤
          (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (xiGamma γ * h n ω ρ))}) atTop (𝓝 0) := by
  have : CompactSpace K₁ := isCompact_iff_compactSpace.mp hK₁
  obtain ⟨s, hs⟩ := exists_surjective_nat CoordJ
  set O : TopologicalSpace.Opens ℂ := Blueprint.ballO 0 (R / 2) with hOdef
  have hOset : (O : Set ℂ) = ball 0 (R / 2) := rfl
  set ξ : ℝ := xiGamma γ with hξ
  have hε0 : ∀ n, 0 ≤ ε n := fun n => (norm_nonneg _).trans ((hΦ n).deriv_close 0)
  -- the recentred fields `ĝ̄ = h̄ − ⟨h̄, ρ⟩`, `ĝ = h − ⟨h, ρ⟩`
  set gb : ∀ n, Ω n → DistC := fun n ω => GFFLaw.recenter ρ (hbar n ω) with hgbdef
  set g : ∀ n, Ω n → DistC := fun n ω => GFFLaw.recenter ρ (h n ω) with hgdef
  have hgb : ∀ n, IsWholePlaneGFF (gb n) (P n) := fun n =>
    (hc n).isWholePlaneGFF_bar.addConst
      ((GFFInv.measurable_pair ρ).comp (hc n).isWholePlaneGFF_bar.measurable).neg
  have hg : ∀ n, IsWholePlaneGFF (g n) (P n) := fun n =>
    (hc n).isWholePlaneGFF.addConst
      ((GFFInv.measurable_pair ρ).comp (hc n).isWholePlaneGFF.measurable).neg
  -- one locality functional for all of them (universal locality, D9 step 4)
  obtain ⟨F, hFm, hF⟩ := universalLocality hD O (ℕ × Bool) (fun i => Ω i.1) (fun i => P i.1)
    (fun i => cond i.2 (gb i.1) (g i.1)) (fun i => by
      rcases i with ⟨n, b⟩
      cases b
      · exact isGFFPlusCont_of_wp (hg n)
      · exact isGFFPlusCont_of_wp (hgb n))
  have hFb : ∀ n, ∀ᵐ ω ∂(P n), ∀ z ∈ O, ∀ w ∈ O,
      (D (gb n ω)).internal O z w = F (restrictTo O (gb n ω)) z w := fun n => hF (n, true)
  have hFg : ∀ n, ∀ᵐ ω ∂(P n), ∀ z ∈ O, ∀ w ∈ O,
      (D (g n ω)).internal O z w = F (restrictTo O (g n ω)) z w := fun n => hF (n, false)
  -- the functional in coordinates
  set d : (ℕ → ℝ) → ℂ → ℂ → ℝ≥0∞ :=
    fun y => F (pairJInv O (fun c => y (Function.surjInv hs c))) with hddef
  have hd : ∀ u v, Measurable fun y => d y u v := by
    intro u v
    have h1 : Measurable fun y : ℕ → ℝ => (fun c => y (Function.surjInv hs c)) :=
      measurable_pi_iff.2 fun c => measurable_pi_apply _
    exact (measurable_pi_apply v).comp ((measurable_pi_apply u).comp
      (hFm.comp ((measurable_pairJInv O).comp h1)))
  have hdY : ∀ x : DistC, d (coordVec ρ O s x) = F (restrictTo O (GFFLaw.recenter ρ x)) :=
    fun x => by simp only [hddef]; rw [pairJInv_coordVec hs x]
  -- the coordinate vectors and their common law `μ` (D9 steps 1–2)
  set Y : ∀ n, Ω n → ℕ → ℝ := fun n => coordVec ρ O s ∘ hbar n with hYdef
  set Y' : ∀ n, Ω n → ℕ → ℝ := fun n => coordVec ρ O s ∘ h n with hY'def
  have hY : ∀ n, Measurable (Y n) := fun n =>
    (measurable_coordVec ρ O s).comp (hc n).isWholePlaneGFF_bar.measurable
  have hY' : ∀ n, Measurable (Y' n) := fun n =>
    (measurable_coordVec ρ O s).comp (hc n).isWholePlaneGFF.measurable
  set μ : Measure (ℕ → ℝ) := (P 0).map (Y' 0) with hμdef
  have : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  have hlawY : ∀ n, (P n).map (Y n) = μ := fun n =>
    map_coordVec_eq hρ1 O s (hc n).isWholePlaneGFF_bar (hc 0).isWholePlaneGFF
  have hlawY' : ∀ n, (P n).map (Y' n) = μ := fun n =>
    map_coordVec_eq hρ1 O s (hc n).isWholePlaneGFF (hc 0).isWholePlaneGFF
  -- coordinatewise closeness (D9 step 3)
  have hconv : ∀ k : ℕ, ∀ η : ℝ, 0 < η →
      Tendsto (fun n => P n {ω | η ≤ |Y n ω k - Y' n ω k|}) atTop (𝓝 0) := by
    intro k η hη
    set e : TestC := combC O (s k) with hedef
    set e₀ : TestC := e - (∫ y, e y) • ρ with he₀def
    have he₀ : tsupport (e₀ : ℂ → ℝ) ⊆ closedBall 0 (R / 2) := by
      refine tsupport_subset_of_eq_zero isClosed_closedBall fun x hx => ?_
      have h1 : e x = 0 := image_eq_zero_of_notMem_tsupport fun hxe =>
        hx (ball_subset_closedBall (tsupport_combC_subset O (s k) hxe))
      have h2 : ρ x = 0 := image_eq_zero_of_notMem_tsupport fun hxρ => hx (hρs hxρ)
      show e x - (∫ y, e y) * ρ x = 0
      rw [h1, h2]
      ring
    have he₀int : ∫ x, e₀ x = 0 := GFFLaw.integral_sub_smul hρ1 e
    refine Tendsto.congr (fun n => ?_) (tendsto_prob_pairing hR hc hΦ hΦsub hε32 hε hsup he₀ hη)
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, he₀int, zero_mul, add_zero, hYdef, hY'def, Function.comp_apply,
      coordVec_apply]
    exact Iff.rfl
  -- LawEqCont with the restriction functional (D9 step 5)
  have hΔ : Tendsto (fun n => P n {ω | δ / 2 ≤
      dist (restrictPair d K₁ (Y n ω)) (restrictPair d K₁ (Y' n ω))}) atTop (𝓝 0) :=
    lawEqCont_restrictPair hd K₁ μ Ω P Y Y' hY hY' hlawY hlawY' hconv (by positivity)
  -- tightness of the sup norms: one law `μ`
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  set SA : ℝ → Set (ℕ → ℝ) := fun M => {y | M ≤ ‖restrictPair d K₁ y‖} with hSAdef
  have hSAm : ∀ M, MeasurableSet (SA M) := fun M =>
    measurableSet_le measurable_const (measurable_restrictPair hd).norm
  have hSAlim : Tendsto (fun m : ℕ => μ (SA m)) atTop (𝓝 0) := by
    have hanti : Antitone (fun m : ℕ => SA m) := fun m m' hmm' y hy =>
      show ((m : ℕ) : ℝ) ≤ ‖restrictPair d K₁ y‖ from le_trans (Nat.cast_le.2 hmm') hy
    have h0 : (⋂ m : ℕ, SA m) = ∅ := by
      ext y
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨m, hm⟩ := exists_nat_gt ‖restrictPair d K₁ y‖
      exact ⟨m, not_le.2 hm⟩
    have := tendsto_measure_iInter_atTop (μ := μ) (fun m : ℕ => (hSAm m).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rwa [h0, measure_empty] at this
  obtain ⟨m, hm⟩ := (hSAlim.eventually (gt_mem_nhds (ENNReal.half_pos hη.ne'))).exists
  set M₀ : ℝ := (m : ℝ) + 1 with hM₀def
  have hM₀ : 0 < M₀ := by positivity
  have hSA : ∀ n, P n {ω | M₀ ≤ ‖restrictPair d K₁ (Y n ω)‖} < η / 2 := fun n => by
    have e : {ω | M₀ ≤ ‖restrictPair d K₁ (Y n ω)‖} = Y n ⁻¹' SA M₀ := rfl
    rw [e, ← Measure.map_apply (hY n) (hSAm M₀), hlawY n]
    refine lt_of_le_of_lt (measure_mono fun y hy => ?_) hm
    show ((m : ℕ) : ℝ) ≤ ‖restrictPair d K₁ y‖
    exact le_trans (show (m : ℝ) ≤ M₀ by rw [hM₀def]; linarith) hy
  -- the thresholds
  set τ₀ : ℝ := Real.log (1 + δ / (2 * M₀)) with hτ₀def
  have hδM : 0 < δ / (2 * M₀) := by positivity
  have hτ₀ : 0 < τ₀ := Real.log_pos (by linarith)
  have hexpτ₀ : Real.exp τ₀ - 1 = δ / (2 * M₀) := by
    rw [hτ₀def, Real.exp_log (by linarith)]
    ring
  set τ₁ : ℝ := τ₀ / (3 * (|ξ| + 1)) with hτ₁def
  have hτ₁ : 0 < τ₁ := by positivity
  -- the three events which tend to `0`
  have hZ := tendsto_prob_pairing hR hc hΦ hΦsub hε32 hε hsup hρs hτ₁
  have hσ := tendsto_prob_supDev (fun n => (measurable_supDev (by positivity) (by linarith)
      (hc n).measurable fun ω => ((hc n).harmonic ω).continuousOn).aemeasurable) hsup hε hτ₁
  have hsum := (hΔ.add hZ).add hσ
  rw [add_zero, add_zero] at hsum
  have h3τ : 3 * τ₁ * (|ξ| + 1) = τ₀ := by
    rw [hτ₁def]
    field_simp
  have hev2 : ∀ᶠ n in atTop, ε n < τ₁ := hε.eventually (gt_mem_nhds hτ₁)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hsum (η / 2) (ENNReal.half_pos hη.ne'), hev2]
    with n hn1 hn2
  have hgbc := isGFFPlusCont_of_wp (hgb n)
  have hgc := isGFFPlusCont_of_wp (hg n)
  -- the bad event lies a.s. in the union of the four small events (D9 step 6)
  have hincl : {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
      (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v ≤
          (D (h n ω)).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (ξ * h n ω ρ)) ∧
      (D (h n ω)).internal (ball 0 (R / 2)) u v ≤
          (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (ξ * h n ω ρ))} ≤ᵐ[P n]
      ((({ω | δ / 2 ≤ dist (restrictPair d K₁ (Y n ω)) (restrictPair d K₁ (Y' n ω))} ∪
        {ω | τ₁ ≤ |hbar n ω ρ - h n ω ρ + (∫ x, ρ x) * K n ω 0|}) ∪
        {ω | ENNReal.ofReal τ₁ ≤ supDev (K n ω) (R / 2)}) ∪
        {ω | M₀ ≤ ‖restrictPair d K₁ (Y n ω)‖}) := by
    filter_upwards [hFb n, hFg n, hD.length (P n) (gb n) hgbc, hD.length (P n) (g n) hgc,
      ae_internal_addFun_eq_weylScaleOn hD hgbc, hD.ae_internal_addFun_of_eq_const hgc]
      with ω hFbω hFgω hlb hlg hweyl hconst hbad
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hnot
    apply hbad
    set Z : ℝ := hbar n ω ρ - h n ω ρ + (∫ x, ρ x) * K n ω 0 with hZdef
    set σ : ℝ := (supDev (K n ω) (R / 2)).toReal with hσdef
    set t : ℝ := |ξ| * (|Z| + σ + ε n) with htdef
    set E : ℝ := Real.exp (ξ * h n ω ρ) with hEdef
    have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
    have hσt : σ < τ₁ := ENNReal.toReal_lt_of_lt_ofReal h3
    have ht0 : 0 ≤ t := mul_nonneg (abs_nonneg _) (by linarith [abs_nonneg Z, hε0 n])
    have htτ : t ≤ τ₀ := by
      have hs3 : |Z| + σ + ε n ≤ 3 * τ₁ := by linarith
      calc t ≤ |ξ| * (3 * τ₁) := mul_le_mul_of_nonneg_left hs3 (abs_nonneg _)
        _ ≤ (|ξ| + 1) * (3 * τ₁) := by nlinarith
        _ = τ₀ := by rw [← h3τ]; ring
    have hKc : ContinuousOn (K n ω) (closedBall 0 (R / 2)) :=
      ((hc n).harmonic ω).continuousOn.mono (closedBall_subset_ball (by linarith))
    have hfb : ∀ x ∈ ball (0 : ℂ) (R / 2),
        |ξ * (Kt n ω + ContinuousMap.const ℂ (hbar n ω ρ)) x - ξ * h n ω ρ| ≤ t := by
      intro x hx
      have e1 : (Kt n ω + ContinuousMap.const ℂ (hbar n ω ρ)) x - h n ω ρ =
          Z + (K n ω x - K n ω 0) + (Kt n ω x - K n ω x) := by
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, hZdef, hρ1]
        ring
      have b1 : |K n ω x - K n ω 0| ≤ σ :=
        abs_sub_le_toReal_supDev hKc (ball_subset_closedBall hx)
      have b2 := hKt n ω x hx
      rw [← mul_sub, abs_mul, e1]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |Z + (K n ω x - K n ω 0) + (Kt n ω x - K n ω x)|
          ≤ |Z + (K n ω x - K n ω 0)| + |Kt n ω x - K n ω x| := abs_add_le _ _
        _ ≤ |Z| + |K n ω x - K n ω 0| + |Kt n ω x - K n ω x| := by
            gcongr; exact abs_add_le _ _
        _ ≤ |Z| + σ + ε n := by gcongr
    have hfield1 : addFun (hbar n ω) (Kt n ω) =
        addFun (gb n ω) (Kt n ω + ContinuousMap.const ℂ (hbar n ω ρ)) := by
      show addFun (hbar n ω) (Kt n ω) = addFun (addConst (hbar n ω) (-(hbar n ω ρ))) _
      rw [addFun_addConst_eq_addFun]
      congr 1
      ext x
      simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
      ring
    have hfield2 : h n ω = addFun (g n ω) (ContinuousMap.const ℂ (h n ω ρ)) := by
      show h n ω = addConst (addConst (h n ω) (-(h n ω ρ))) (h n ω ρ)
      rw [GFFLaw.addConst_addConst, neg_add_cancel, GFFLaw.addConst_zero']
    refine lemma23_pointwise (X := D (g n ω)) (Xb := D (gb n ω)) hlg hlb hK₁B (d := d)
      (y := Y n ω) (y' := Y' n ω) ?_ ?_
      (Mf := fun u v => (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v)
      (M'f := fun u v => (D (h n ω)).internal (ball 0 (R / 2)) u v) (E := E) (t := t) (δ := δ)
      (Real.exp_pos _) ht0 ?_ ?_ ?_ ?_
    · intro z hz w hw
      show d (coordVec ρ O s (hbar n ω)) z w = _
      rw [hdY]
      exact (hFbω z hz w hw).symm
    · intro z hz w hw
      show d (coordVec ρ O s (h n ω)) z w = _
      rw [hdY]
      exact (hFgω z hz w hw).symm
    · intro u _ v _
      show _ ≤ (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v
      rw [hfield1, hweyl _ isOpen_ball _ u v]
      have hlo : ∀ x ∈ ball (0 : ℂ) (R / 2),
          ξ * h n ω ρ - t ≤ ξ * (Kt n ω + ContinuousMap.const ℂ (hbar n ω ρ)) x := fun x hx => by
        linarith [(abs_le.1 (hfb x hx)).1]
      have hE1 : E * Real.exp (-t) = Real.exp (ξ * h n ω ρ - t) := by
        rw [hEdef, ← Real.exp_add, sub_eq_add_neg]
      rw [hE1]
      exact le_weylScaleOn_of_le hlo
    · intro u _ v _
      show (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v ≤ _
      rw [hfield1, hweyl _ isOpen_ball _ u v]
      have hhi : ∀ x ∈ ball (0 : ℂ) (R / 2),
          ξ * (Kt n ω + ContinuousMap.const ℂ (hbar n ω ρ)) x ≤ ξ * h n ω ρ + t := fun x hx => by
        linarith [(abs_le.1 (hfb x hx)).2]
      have hE2 : E * Real.exp t = Real.exp (ξ * h n ω ρ + t) := by
        rw [hEdef, ← Real.exp_add]
      rw [hE2]
      exact weylScaleOn_le_of_le hhi
    · intro u _ v _
      have := hconst (ContinuousMap.const ℂ (h n ω ρ)) (ball 0 (R / 2)) (ξ * h n ω ρ) isOpen_ball
        (fun x _ => rfl) u v
      rw [← hfield2] at this
      exact this
    · have hexp : Real.exp t - 1 ≤ δ / (2 * M₀) := by
        rw [← hexpτ₀]
        linarith [Real.exp_le_exp.2 htτ]
      have hexp0 : 0 ≤ Real.exp t - 1 := by linarith [Real.one_le_exp ht0]
      have hprod : (Real.exp t - 1) * ‖restrictPair d K₁ (Y n ω)‖ ≤ δ / 2 := by
        calc (Real.exp t - 1) * ‖restrictPair d K₁ (Y n ω)‖ ≤ δ / (2 * M₀) * M₀ :=
              mul_le_mul hexp h4.le (norm_nonneg _) hδM.le
          _ = δ / 2 := by field_simp
      linarith
  calc P n {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
      (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v ≤
          (D (h n ω)).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (ξ * h n ω ρ)) ∧
      (D (h n ω)).internal (ball 0 (R / 2)) u v ≤
          (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (ξ * h n ω ρ))}
      ≤ P n ((({ω | δ / 2 ≤ dist (restrictPair d K₁ (Y n ω)) (restrictPair d K₁ (Y' n ω))} ∪
        {ω | τ₁ ≤ |hbar n ω ρ - h n ω ρ + (∫ x, ρ x) * K n ω 0|}) ∪
        {ω | ENNReal.ofReal τ₁ ≤ supDev (K n ω) (R / 2)}) ∪
        {ω | M₀ ≤ ‖restrictPair d K₁ (Y n ω)‖}) := measure_mono_ae hincl
    _ ≤ (P n {ω | δ / 2 ≤ dist (restrictPair d K₁ (Y n ω)) (restrictPair d K₁ (Y' n ω))} +
        P n {ω | τ₁ ≤ |hbar n ω ρ - h n ω ρ + (∫ x, ρ x) * K n ω 0|} +
        P n {ω | ENNReal.ofReal τ₁ ≤ supDev (K n ω) (R / 2)}) +
        P n {ω | M₀ ≤ ‖restrictPair d K₁ (Y n ω)‖} :=
      (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ η / 2 + η / 2 := add_le_add hn1 (hSA n).le
    _ = η := ENNReal.add_halves η

/-- **[3] Lemma 2.3*** (packet CC6a, T2; CC0 Details D9), sequence form. Let `D` be a strong γ-LQG
metric, `R > 0`, `ρ` a test function supported in `B̄_{R/2}` with `∫ ρ = 1`, `K₁ ⊆ B_{R/2}` compact
and `δ > 0`. Let `(Ω n, P n, h n, h̄ n, K n)` be near-identity couplings on `B_R` (`IsNICCoupling`:
`⟨h n, |det DΦ_n| (g ∘ Φ_n)⟩ = ⟨h̄ n, g⟩ + ∫ K n g` for `g` supported in `B_R`), where `Φ n` is an
`ε n`-near-identity diffeomorphism with inverse `Ψ n` (`IsNearIdDiffeo`, `‖Φ n − id‖ ≤ ε n`),
`E sup_{B̄_{R/2}} |K n − K n(0)| ≤ ε n` and `ε n → 0`; let `K̃ n ω` be continuous with
`|K̃ n ω − K n ω| ≤ ε n` on `B_{R/2}` (D9's continuous extension of `K n` has difference `0`). Then
`P_n(∃ u, v ∈ K₁ : |𝐌_n(u, v) − 𝐌'_n(u, v)| > δ e^{ξ ⟨h n, ρ⟩}) → 0`, where
`𝐌_n = D_{h̄ n + K̃ n}(·,·; B_{R/2})` and `𝐌'_n = D_{h n}(·,·; B_{R/2})`; the event is written with
`[0, ∞]`-valued inequalities in both directions. -/
theorem lemma23_seq (hD : IsStrongLQGMetric γ D) {R : ℝ} (hR : 0 < R) {ρ : TestC}
    (hρs : tsupport (ρ : ℂ → ℝ) ⊆ closedBall 0 (R / 2)) (hρ1 : ∫ x, ρ x = 1)
    {K₁ : Set ℂ} (hK₁ : IsCompact K₁) (hK₁B : K₁ ⊆ ball 0 (R / 2))
    {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {Φ Ψ : ℕ → ℂ → ℂ} {B ε : ℕ → ℝ}
    {h hbar : ∀ n, Ω n → DistC} {K : ∀ n, Ω n → ℂ → ℝ} {Kt : ∀ n, Ω n → C(ℂ, ℝ)}
    (hc : ∀ n, IsNICCoupling (P n) (Φ n) (ball 0 R) (B n) (h n) (hbar n) (K n))
    (hΦ : ∀ n, IsNearIdDiffeo (Φ n) (Ψ n) (ball 0 R) (ε n))
    (hΦsub : ∀ n x, ‖Φ n x - x‖ ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hsup : ∀ n, ∫⁻ ω, supDev (K n ω) (R / 2) ∂(P n) ≤ ENNReal.ofReal (ε n))
    (hKt : ∀ n ω, ∀ x ∈ ball (0 : ℂ) (R / 2), |Kt n ω x - K n ω x| ≤ ε n)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P n {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
      (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v ≤
          (D (h n ω)).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (xiGamma γ * h n ω ρ)) ∧
      (D (h n ω)).internal (ball 0 (R / 2)) u v ≤
          (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (xiGamma γ * h n ω ρ))}) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hε.eventually (gt_mem_nhds
    (by norm_num : (0 : ℝ) < 1 / 32)))
  rw [← tendsto_add_atTop_iff_nat N]
  exact lemma23_seq_small hD hR hρs hρ1 hK₁ hK₁B (Ω := fun n => Ω (n + N))
    (P := fun n => P (n + N)) (fun n => hc (n + N)) (fun n => hΦ (n + N))
    (fun n => hΦsub (n + N)) (fun n => (hN (n + N) (by omega)).le)
    ((tendsto_add_atTop_iff_nat N).2 hε) (fun n => hsup (n + N)) (fun n => hKt (n + N)) hδ

/-- **[3] Lemma 2.3*, uniform form** (the contradiction argument of CC0 D10 done once): for every
`η > 0` there is `ε₁ > 0` such that for **every** near-identity coupling on `B_R` with parameter
`ε ≤ ε₁` (on any probability space), the bad event of `lemma23_seq` has probability at most `η`. -/
theorem lemma23_uniform (hD : IsStrongLQGMetric γ D) {R : ℝ} (hR : 0 < R) {ρ : TestC}
    (hρs : tsupport (ρ : ℂ → ℝ) ⊆ closedBall 0 (R / 2)) (hρ1 : ∫ x, ρ x = 1)
    {K₁ : Set ℂ} (hK₁ : IsCompact K₁) (hK₁B : K₁ ⊆ ball 0 (R / 2)) {δ : ℝ} (hδ : 0 < δ)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Φ Ψ : ℂ → ℂ) (B ε : ℝ) (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ) (Kt : Ω → C(ℂ, ℝ)),
      IsNICCoupling P Φ (ball 0 R) B h hbar K → IsNearIdDiffeo Φ Ψ (ball 0 R) ε →
      (∀ x, ‖Φ x - x‖ ≤ ε) → ε ≤ ε₁ →
      ∫⁻ ω, supDev (K ω) (R / 2) ∂P ≤ ENNReal.ofReal ε →
      (∀ ω, ∀ x ∈ ball (0 : ℂ) (R / 2), |Kt ω x - K ω x| ≤ ε) →
      P {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
        (D (addFun (hbar ω) (Kt ω))).internal (ball 0 (R / 2)) u v ≤
            (D (h ω)).internal (ball 0 (R / 2)) u v +
              ENNReal.ofReal (δ * Real.exp (xiGamma γ * h ω ρ)) ∧
        (D (h ω)).internal (ball 0 (R / 2)) u v ≤
            (D (addFun (hbar ω) (Kt ω))).internal (ball 0 (R / 2)) u v +
              ENNReal.ofReal (δ * Real.exp (xiGamma γ * h ω ρ))} ≤ η := by
  by_contra H
  have H' : ∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (Φ Ψ : ℂ → ℂ) (B ε : ℝ) (h hbar : Ω → DistC)
      (K : Ω → ℂ → ℝ) (Kt : Ω → C(ℂ, ℝ)),
      IsNICCoupling P Φ (ball 0 R) B h hbar K ∧ IsNearIdDiffeo Φ Ψ (ball 0 R) ε ∧
      (∀ x, ‖Φ x - x‖ ≤ ε) ∧ ε ≤ 1 / ((n : ℝ) + 1) ∧
      ∫⁻ ω, supDev (K ω) (R / 2) ∂P ≤ ENNReal.ofReal ε ∧
      (∀ ω, ∀ x ∈ ball (0 : ℂ) (R / 2), |Kt ω x - K ω x| ≤ ε) ∧
      η < P {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
        (D (addFun (hbar ω) (Kt ω))).internal (ball 0 (R / 2)) u v ≤
            (D (h ω)).internal (ball 0 (R / 2)) u v +
              ENNReal.ofReal (δ * Real.exp (xiGamma γ * h ω ρ)) ∧
        (D (h ω)).internal (ball 0 (R / 2)) u v ≤
            (D (addFun (hbar ω) (Kt ω))).internal (ball 0 (R / 2)) u v +
              ENNReal.ofReal (δ * Real.exp (xiGamma γ * h ω ρ))} := fun n => by
    have h0 := not_and.1 (not_exists.1 H (1 / ((n : ℝ) + 1))) (by positivity)
    by_contra h2
    apply h0
    intro Ω mΩ P hP Φ Ψ B ε h hbar K Kt hc hΦ hsub hεle hsup hKt
    by_contra h3
    exact h2 ⟨Ω, mΩ, P, hP, Φ, Ψ, B, ε, h, hbar, K, Kt, hc, hΦ, hsub, hεle, hsup, hKt,
      not_le.1 h3⟩
  choose Ω mΩ P hP Φ Ψ B ε h hbar K Kt hc hΦ hsub hεn hsup hKt hbad using H'
  have hε0 : ∀ n, 0 ≤ ε n := fun n => (norm_nonneg _).trans ((hΦ n).deriv_close 0)
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat hε0 hεn
  have hlim := lemma23_seq hD hR hρs hρ1 hK₁ hK₁B (Ω := Ω) (P := P) hc hΦ hsub hε hsup hKt hδ
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact absurd (hbad n) (not_lt.2 hn.le)

end Main

end SmallGammaGeodesics.CC
