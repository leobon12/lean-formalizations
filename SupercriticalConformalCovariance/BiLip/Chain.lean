import SupercriticalLQGUniqueness.B2.PfeLocal.L4Fill

/-!
# Lemma 2.1, step 5: the loop chain for an abstract source length and target pseudometric

Paper l. 139–141: "Let `P` be a finite `d`-length path. Using successive exits from the good balls and
concatenating the corresponding `e`-loops gives the standard planar loop-chaining construction of
[2, Lemma 2.26]. The source crossing costs are charged to disjoint parameter intervals of `P`."

This is the sealed `SupercriticalLQGUniqueness.B2.PfeLocal.l4_chain` (B2/PfeLocal/L4Chain.lean:184, Pfeffer's
chain with the "union of loops is connected" gap repaired by the filled-set invariant), generalized so that
it applies to BOTH directions of Lemma 2.1 and to the pulled-back metric `e`, which is not an `LSCMetric`:
* the source length of the fixed path `P` is an abstract additive function `lam s t` on `[a, b]`
  (the `d`-length `D_h.len P` for `e ≤ C d`; the `e`-length for `d ≤ C e`);
* the crossing cost `c` of a good annulus is abstract; only the charging inequality
  "`P[τ, t']` runs from `B̄_{r/2}(w)` to `ℂ ∖ B_r(w)` ⟹ `c ≤ lam τ t'`" is used;
* the target `D₂` is any function which is an extended pseudometric on a set `S` containing every loop
  (the confined target metric on a compact `K' ⋐ U`).
The last loop is used only as a connector and is not paid for ("never pays for the
last loop"): this is the repaired form.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness.B2.PfeLocal (l4Fill l4_fill_frontier l4_fill_mono
  l4_fill_subset_closedBall)

/-- `D₂` is an extended pseudometric on `S`: zero on the diagonal, symmetric and with the triangle
inequality, for points of `S`. -/
def IsPMetricOn (D₂ : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ) : Prop :=
  (∀ x ∈ S, D₂ x x = 0) ∧ (∀ x ∈ S, ∀ y ∈ S, D₂ x y = D₂ y x) ∧
    (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, D₂ x z ≤ D₂ x y + D₂ y z)

/-- A good loop around `B̄_r(w)` in `B̄_{2r}(w) ∖ B_r(w)`, inside `S`, of `D₂`-diameter less than `M`. -/
def IsGoodLoop (D₂ : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ) (w : ℂ) (r : ℝ) (M : ℝ≥0∞) : Prop :=
  ∃ ℓ : Set ℂ, ℓ.Nonempty ∧ IsPreconnected ℓ ∧ ℓ ⊆ S ∧ ℓ ⊆ closedBall w (2 * r) ∧
    Disjoint ℓ (ball w r) ∧ closedBall w r ⊆ l4Fill ℓ ∧
    ∃ L₀ : ℝ≥0∞, L₀ < M ∧ ∀ x ∈ ℓ, ∀ y ∈ ℓ, D₂ x y ≤ L₀

/-- Larger sets and larger bounds preserve good loops. -/
theorem IsGoodLoop.mono {D₂ D₂' : ℂ → ℂ → ℝ≥0∞} {S S' : Set ℂ} {w : ℂ} {r : ℝ} {M M' : ℝ≥0∞}
    (h : IsGoodLoop D₂ S w r M) (hS : ∀ x ∈ S, ∀ y ∈ S, D₂' x y ≤ D₂ x y) (hSS : S ⊆ S')
    (hM : M ≤ M') : IsGoodLoop D₂' S' w r M' := by
  obtain ⟨ℓ, hne, hpc, hℓS, hsub, hdisj, hfill, L₀, hL₀, hdiam⟩ := h
  exact ⟨ℓ, hne, hpc, hℓS.trans hSS, hsub, hdisj, hfill, L₀, hL₀.trans_le hM,
    fun x hx y hy => (hS x (hℓS hx) y (hℓS hy)).trans (hdiam x hx y hy)⟩

/-- The chain invariant at time `τ` for a reached set `R` (as `l4Inv`, with points kept in `S`). -/
def ChainInv (lam : ℝ → ℝ → ℝ≥0∞) (D₂ : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ) (K : ℝ≥0∞) (ρ : ℝ)
    (P : ℝ → ℂ) (a τ : ℝ) (R : Set ℂ) : Prop :=
  R ⊆ S ∧
    (∀ x ∈ R, ∃ q ∈ S, q ∈ closedBall (P a) (4 * ρ) ∧ D₂ q x ≤ K * lam a τ) ∧
    ∀ Λ : Set ℂ, P τ ∈ l4Fill Λ → (Λ ∩ R).Nonempty ∨ P a ∈ l4Fill Λ

theorem chainInv_start (lam : ℝ → ℝ → ℝ≥0∞) (D₂ : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ) (K : ℝ≥0∞)
    (ρ : ℝ) (P : ℝ → ℂ) (a : ℝ) : ChainInv lam D₂ S K ρ P a a ∅ :=
  ⟨empty_subset _, fun x hx => absurd hx (notMem_empty x), fun _ h => Or.inr h⟩

theorem dist_le_of_mem_two_closedBalls {x y w : ℂ} {r ρ : ℝ} (hx : x ∈ closedBall w (2 * r))
    (hy : y ∈ closedBall w (2 * r)) (hrρ : r ≤ ρ) : x ∈ closedBall y (4 * ρ) := by
  rw [mem_closedBall] at hx hy ⊢
  calc dist x y ≤ dist x w + dist w y := dist_triangle _ _ _
    _ ≤ 2 * r + 2 * r := add_le_add hx (by rw [dist_comm]; exact hy)
    _ ≤ 4 * ρ := by linarith

/-- The good-annulus hypothesis of the chain at time `t`: a pair `(w, r)` with `r ≤ ρ` and
`P t ∈ B_{r/2}(w)`, a crossing cost `c ≥ μ₀` charged to every crossing of `A_{r/2,r}(w)` by `P`, and a
good loop of `D₂`-diameter `< K c`. -/
def ChainGoodAt (lam : ℝ → ℝ → ℝ≥0∞) (D₂ : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ) (K : ℝ≥0∞) (ρ μ₀ : ℝ)
    (P : ℝ → ℂ) (a b t : ℝ) : Prop :=
  ∃ w : ℂ, ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ P t ∈ ball w (r / 2) ∧
    ∃ c : ℝ≥0∞, ENNReal.ofReal μ₀ ≤ c ∧
      (∀ τ t', a ≤ τ → τ ≤ t' → t' ≤ b → dist (P τ) w ≤ r / 2 → r ≤ dist (P t') w →
        c ≤ lam τ t') ∧
      IsGoodLoop D₂ S w r (K * c)

/-- The inductive chain step (as `l4_chain_step`). -/
theorem chain_step (lam : ℝ → ℝ → ℝ≥0∞) (D₂ : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ)
    (hD₂ : IsPMetricOn D₂ S) (K : ℝ≥0∞) (ρ μ₀ : ℝ) (P : ℝ → ℂ) {a b : ℝ}
    (hPc : ContinuousOn P (Icc a b))
    (hadd : ∀ s t u, a ≤ s → s ≤ t → t ≤ u → u ≤ b → lam s u = lam s t + lam t u)
    (hgood : ∀ t ∈ Icc a b, ChainGoodAt lam D₂ S K ρ μ₀ P a b t) :
    ∀ n : ℕ, ∀ τ ∈ Icc a b, ∀ R : Set ℂ, ChainInv lam D₂ S K ρ P a τ R →
      lam τ b < ENNReal.ofReal (n * μ₀) →
      ∃ x₁ ∈ S, x₁ ∈ closedBall (P a) (4 * ρ) ∧ ∃ x₂ ∈ S, x₂ ∈ closedBall (P b) (4 * ρ) ∧
        D₂ x₁ x₂ ≤ K * lam a b := by
  obtain ⟨hD0, hDsymm, hDtri⟩ := hD₂
  intro n
  induction n with
  | zero =>
    intro τ _ R _ hlt
    simp at hlt
  | succ n ih =>
    intro τ hτ R hInv hlt
    obtain ⟨w, r, hr, hrρ, hPτ, c, hμ, hcharge, hloop⟩ := hgood τ hτ
    obtain ⟨ℓ, hne, hpc, hℓS, hsub, hdisj, hfill, L₀, hL₀, hdiam⟩ := hloop
    have hPτF : P τ ∈ l4Fill ℓ :=
      hfill (ball_subset_closedBall (ball_subset_ball (by linarith) hPτ))
    have hlen_aτ_le_ab : lam a τ ≤ lam a b := by
      rw [hadd a τ b le_rfl hτ.1 hτ.2 le_rfl]; exact le_self_add
    -- every point of the loop is reached
    have hreach : ∀ y ∈ ℓ, ∃ q ∈ S, q ∈ closedBall (P a) (4 * ρ) ∧
        D₂ q y ≤ K * lam a τ + L₀ := by
      intro y hy
      rcases hInv.2.2 ℓ hPτF with ⟨x₀, hx₀ℓ, hx₀R⟩ | hPa
      · obtain ⟨q, hqS, hq, hqx⟩ := hInv.2.1 x₀ hx₀R
        refine ⟨q, hqS, hq, ?_⟩
        calc D₂ q y ≤ D₂ q x₀ + D₂ x₀ y := hDtri q hqS x₀ (hInv.1 hx₀R) y (hℓS hy)
          _ ≤ K * lam a τ + L₀ := add_le_add hqx (hdiam x₀ hx₀ℓ y hy)
      · refine ⟨y, hℓS hy, ?_, ?_⟩
        · exact dist_le_of_mem_two_closedBalls (hsub hy)
            (l4_fill_subset_closedBall (by linarith) hsub hPa) hrρ
        · rw [hD0 y (hℓS hy)]; exact zero_le
    by_cases hhit : ∃ t ∈ Icc τ b, P t ∈ ℓ
    · obtain ⟨t, ht, hPt⟩ := hhit
      have hτt : τ ≤ t := ht.1
      have htab : t ∈ Icc a b := ⟨hτ.1.trans hτt, ht.2⟩
      have hcross : c ≤ lam τ t := by
        refine hcharge τ t hτ.1 hτt ht.2 (mem_ball.1 hPτ).le ?_
        have h2 := Set.disjoint_left.1 hdisj hPt
        exact not_lt.1 (fun h => h2 (mem_ball.2 h))
      have hadd1 : lam a t = lam a τ + lam τ t := hadd a τ t le_rfl hτ.1 hτt ht.2
      have hadd2 : lam τ b = lam τ t + lam t b := hadd τ t b hτ.1 hτt ht.2 le_rfl
      refine ih t htab (R ∪ ℓ) ⟨union_subset hInv.1 hℓS, ?_, ?_⟩ ?_
      · intro x hx
        rcases hx with hxR | hxℓ
        · obtain ⟨q, hqS, hq, hqx⟩ := hInv.2.1 x hxR
          exact ⟨q, hqS, hq, hqx.trans (mul_le_mul_right (hadd1 ▸ le_self_add) K)⟩
        · obtain ⟨q, hqS, hq, hqx⟩ := hreach x hxℓ
          refine ⟨q, hqS, hq, hqx.trans ?_⟩
          rw [hadd1, mul_add]
          exact add_le_add le_rfl (hL₀.le.trans (mul_le_mul_right hcross K))
      · intro Λ hΛ
        by_cases hΛℓ : (Λ ∩ ℓ).Nonempty
        · obtain ⟨x, hxΛ, hxℓ⟩ := hΛℓ
          exact Or.inl ⟨x, hxΛ, Or.inr hxℓ⟩
        · have hℓF : ℓ ⊆ l4Fill Λ := by
            intro x hx
            by_contra hxF
            obtain ⟨y, hyℓ, hyΛ⟩ := l4_fill_frontier hpc ⟨P t, hPt, hΛ⟩ ⟨x, hx, hxF⟩
            exact hΛℓ ⟨y, hyΛ, hyℓ⟩
          rcases hInv.2.2 Λ (l4_fill_mono hℓF hPτF) with ⟨x, hxΛ, hxR⟩ | hPa
          · exact Or.inl ⟨x, hxΛ, Or.inl hxR⟩
          · exact Or.inr hPa
      · -- the remaining length decreases by at least `μ₀`
        by_contra hge
        push Not at hge
        have h1 : ENNReal.ofReal μ₀ + ENNReal.ofReal (n * μ₀) ≤ lam τ b := by
          rw [hadd2]; exact add_le_add (hμ.trans hcross) hge
        have h2 : ENNReal.ofReal ((n + 1 : ℕ) * μ₀) ≤ ENNReal.ofReal μ₀ +
            ENNReal.ofReal (n * μ₀) := by
          calc ENNReal.ofReal ((n + 1 : ℕ) * μ₀) = ENNReal.ofReal (μ₀ + n * μ₀) := by
                congr 1; push_cast; ring
            _ ≤ _ := ENNReal.ofReal_add_le
        exact absurd hlt (not_lt.2 (h2.trans h1))
    · push Not at hhit
      have hTsub : P '' Icc τ b ⊆ l4Fill ℓ := by
        rintro _ ⟨s, hs, rfl⟩
        by_contra hsF
        obtain ⟨y, ⟨u, hu, rfl⟩, hyℓ⟩ := l4_fill_frontier
          ((isPreconnected_Icc).image _ (hPc.mono (Icc_subset_Icc hτ.1 le_rfl)))
          ⟨P τ, ⟨τ, ⟨le_rfl, hτ.2⟩, rfl⟩, hPτF⟩ ⟨P s, ⟨s, hs, rfl⟩, hsF⟩
        exact hhit u hu hyℓ
      have hPb : P b ∈ closedBall w (2 * r) :=
        l4_fill_subset_closedBall (by linarith) hsub (hTsub ⟨b, ⟨hτ.2, le_rfl⟩, rfl⟩)
      rcases hInv.2.2 ℓ hPτF with ⟨x₀, hx₀ℓ, hx₀R⟩ | hPa
      · obtain ⟨q, hqS, hq, hqx⟩ := hInv.2.1 x₀ hx₀R
        exact ⟨q, hqS, hq, x₀, hℓS hx₀ℓ, dist_le_of_mem_two_closedBalls (hsub hx₀ℓ) hPb hrρ,
          hqx.trans (mul_le_mul_right hlen_aτ_le_ab K)⟩
      · obtain ⟨y, hy⟩ := hne
        refine ⟨y, hℓS hy, dist_le_of_mem_two_closedBalls (hsub hy)
          (l4_fill_subset_closedBall (by linarith) hsub hPa) hrρ, y, hℓS hy,
          dist_le_of_mem_two_closedBalls (hsub hy) hPb hrρ, ?_⟩
        rw [hD0 y (hℓS hy)]; exact zero_le

/-- **The chain lemma, abstract form** (`l4_chain` for an additive source length `lam` and a target
pseudometric `D₂` on `S`): some points of `S` within `4ρ` of the endpoints of `P` are at `D₂`-distance at
most `K · lam a b`. -/
theorem chain (lam : ℝ → ℝ → ℝ≥0∞) (D₂ : ℂ → ℂ → ℝ≥0∞) (S : Set ℂ) (hD₂ : IsPMetricOn D₂ S)
    (K : ℝ≥0∞) (ρ μ₀ : ℝ) (hμ₀ : 0 < μ₀) (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hPc : ContinuousOn P (Icc a b))
    (hadd : ∀ s t u, a ≤ s → s ≤ t → t ≤ u → u ≤ b → lam s u = lam s t + lam t u)
    (hlen : lam a b < ∞)
    (hgood : ∀ t ∈ Icc a b, ChainGoodAt lam D₂ S K ρ μ₀ P a b t) :
    ∃ x₁ ∈ S, x₁ ∈ closedBall (P a) (4 * ρ) ∧ ∃ x₂ ∈ S, x₂ ∈ closedBall (P b) (4 * ρ) ∧
      D₂ x₁ x₂ ≤ K * lam a b := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((lam a b).toReal / μ₀)
  refine chain_step lam D₂ S hD₂ K ρ μ₀ P hPc hadd hgood n a ⟨le_rfl, hab⟩ ∅
    (chainInv_start lam D₂ S K ρ P a) ?_
  rw [← ENNReal.ofReal_toReal hlen.ne]
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hn0 hμ₀)).2
  rwa [div_lt_iff₀ hμ₀] at hn

end SupercriticalConformalCovariance.BiLip
