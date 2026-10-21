import SmallGammaGeodesics.CC.ConfMetric
import LQGMetric.Papers.GM.S2.TightA
import LQGMetric.Papers.GM.S1.Eq115

/-!
# [3] Lemma 3.5: the LM good annulus for `(D_h, D^ϕ)` (track CC, packet CC8)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D11** (Gwynne–Miller,
arXiv:1905.00384 ([3]), Lemma 3.5), for a coupling `(h, h̄, f)` of a conformal neighbourhood
`IsConfNbhd ϕ W V` and the transported metric `D^ϕ = confMetric D ϕ V h̄ f`.

* `ConfLMGood D ϕ h h̄ f C w r`: the good event `E^{LM}_r(w)` of CC0 D13 at one sample: the
  internal distances of `D^ϕ` in `A_{r/2,2r}(w)` between points of `∂B_r(w)` are at most
  `C · D_h(∂B_{r/2}(w), ∂B_r(w))`.
* `le_mul_of_circle_steps`: chaining around a circle (deterministic).
* `confLMGood_of_bounds`: the deterministic core of D11: the four estimates (two crossing lower
  bounds, a modulus of continuity, and the small-scale comparison of `D^ϕ` with `D_h`) give the
  event.
* `lemma35`: **[3] Lemma 3.5** (the direction `D^ϕ ≤ C D_h` used by D13): for every `p < 1` there
  is `C > 0` (depending only on `p`, `γ` and `D`) such that for every conformal neighbourhood and
  compact `K ⊆ V` there is `r₀ > 0` with `P[E^{LM}_r(z)] ≥ p` for all couplings, `z ∈ K` and
  `r ≤ r₀`. The inputs are GM S2 tightness (`GM.Tight.gm_S2_4a` twice, `gm_S2_4b`) and the
  interface `ConfSmallScale` ([3] Prop 2.1), all normalized at the radius `3r` (so no Gaussian
  tail of `h_{3r} − h_r` is needed). The annulus locality of the event is in
  `CC/Lemma35Local.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-- **The LM good event `E^{LM}_r(w)`** (CC0 D13, [3] Lemma 3.5) at one sample: for all
`u, v ∈ ∂B_r(w)`, `D^ϕ(u, v; A_{r/2,2r}(w)) ≤ C · D_h(∂B_{r/2}(w), ∂B_r(w))`. The internal
metric of `D^ϕ` on the annulus is `confMetric D ϕ A h̄ f` (internal of internal,
`funInternal_confMetric`). -/
def ConfLMGood (D : DistC → ContMetric) (ϕ : ℂ → ℂ) (h hbar : DistC) (f : C(ℂ, ℝ)) (C : ℝ)
    (w : ℂ) (r : ℝ) : Prop :=
  ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
    confMetric D ϕ (annulus w (r / 2) (2 * r) : Set ℂ) hbar f u v ≤
      ENNReal.ofReal C * setDist (D h) (sphere w (r / 2)) (sphere w r)

/-! ## 1. Chaining around a circle -/

/-- a point of the circle `∂B_r(z)` is `circleMap z r (arg (u - z))` -/
lemma circleMap_arg {z u : ℂ} {r : ℝ} (hu : u ∈ sphere z r) :
    circleMap z r (Complex.arg (u - z)) = u := by
  have hn : ‖u - z‖ = r := mem_sphere_iff_norm.1 hu
  have h := Complex.norm_mul_exp_arg_mul_I (u - z)
  rw [hn] at h
  rw [circleMap, h]
  ring

/-- **Chaining around a circle**: if `d` satisfies the triangle inequality and `d u v ≤ c` for
points of `∂B_r(z)` at distance `≤ 2πr/n`, then `d u v ≤ n c` on `∂B_r(z)`. -/
theorem le_mul_of_circle_steps {d : ℂ → ℂ → ℝ≥0∞} (htri : ∀ x y z, d x z ≤ d x y + d y z)
    {z : ℂ} {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) {c : ℝ≥0∞}
    (hstep : ∀ u ∈ sphere z r, ∀ v ∈ sphere z r, ‖u - v‖ ≤ 2 * Real.pi * r / n → d u v ≤ c) :
    ∀ u ∈ sphere z r, ∀ v ∈ sphere z r, d u v ≤ n * c := by
  intro u hu v hv
  set α := Complex.arg (u - z) with hα
  set β := Complex.arg (v - z) with hβ
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set x : ℕ → ℂ := fun k => circleMap z r (α + k * ((β - α) / n)) with hx
  have hx0 : x 0 = u := by simp only [hx, Nat.cast_zero, zero_mul, add_zero]; exact circleMap_arg hu
  have hxn : x n = v := by
    simp only [hx]
    rw [mul_div_cancel₀ _ hnR.ne', add_sub_cancel]
    exact circleMap_arg hv
  have hmem : ∀ k, x k ∈ sphere z r := fun k => circleMap_mem_sphere z hr _
  have hab : |β - α| ≤ 2 * Real.pi := by
    have h1 := Complex.neg_pi_lt_arg (u - z)
    have h2 := Complex.arg_le_pi (u - z)
    have h3 := Complex.neg_pi_lt_arg (v - z)
    have h4 := Complex.arg_le_pi (v - z)
    rw [abs_le]
    constructor <;> linarith
  have hdist : ∀ k, ‖x k - x (k + 1)‖ ≤ 2 * Real.pi * r / n := by
    intro k
    have hL := (lipschitzWith_circleMap z r).dist_le_mul (α + k * ((β - α) / n))
      (α + ((k + 1 : ℕ) : ℝ) * ((β - α) / n))
    rw [Real.coe_nnabs, abs_of_nonneg hr, Real.dist_eq] at hL
    rw [← dist_eq_norm]
    refine hL.trans ?_
    have e : α + (k : ℝ) * ((β - α) / n) - (α + ((k + 1 : ℕ) : ℝ) * ((β - α) / n)) =
        -((β - α) / n) := by
      push_cast; ring
    rw [e, abs_neg, abs_div, abs_of_pos hnR, mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith [abs_nonneg (β - α)]) hnR.le
  -- telescoping from `x 0`
  have key : ∀ k : ℕ, d (x 0) (x (k + 1)) ≤ ((k + 1 : ℕ) : ℝ≥0∞) * c := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_one, one_mul]
      exact hstep _ (hmem 0) _ (hmem 1) (hdist 0)
    | succ k ih =>
      calc d (x 0) (x (k + 1 + 1)) ≤ d (x 0) (x (k + 1)) + d (x (k + 1)) (x (k + 1 + 1)) :=
            htri _ _ _
        _ ≤ ((k + 1 : ℕ) : ℝ≥0∞) * c + c :=
            add_le_add ih (hstep _ (hmem _) _ (hmem _) (hdist _))
        _ = ((k + 1 + 1 : ℕ) : ℝ≥0∞) * c := by push_cast; ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  have := key m
  rw [hx0, show 0 + m + 1 = m + 1 by omega] at *
  rw [← hxn]
  simpa only [zero_add] using this

/-! ## 2. The deterministic core of [3] Lemma 3.5 (CC0 D11) -/

/-- the frontier of the annulus `A_{a,b}(z)` lies on its two boundary circles -/
lemma frontier_annulus_subset (z : ℂ) (a b : ℝ) :
    frontier (annulus z a b : Set ℂ) ⊆ sphere z a ∪ sphere z b := by
  intro y hy
  have hopen : IsOpen (annulus z a b : Set ℂ) := (annulus z a b).isOpen
  rw [hopen.frontier_eq] at hy
  obtain ⟨hcl, hnot⟩ := hy
  have hsub : closure (annulus z a b : Set ℂ) ⊆ {y : ℂ | a ≤ ‖y - z‖ ∧ ‖y - z‖ ≤ b} :=
    closure_minimal (fun y hy => ⟨hy.1.le, hy.2.le⟩)
      ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
        (isClosed_le (continuous_id.sub continuous_const).norm continuous_const))
  obtain ⟨h1, h2⟩ := hsub hcl
  have hnot' : ¬ (a < ‖y - z‖ ∧ ‖y - z‖ < b) := hnot
  rcases h1.eq_or_lt with e | e
  · exact Or.inl (mem_sphere_iff_norm.2 e.symm)
  · rcases h2.eq_or_lt with e' | e'
    · exact Or.inr (mem_sphere_iff_norm.2 e')
    · exact absurd ⟨e, e'⟩ hnot'

/-- **[3] Lemma 3.5, deterministic core** (CC0 D11). Let `S > 0` be the normalization (in the
application `S = 𝔰_{3r}(z) = (3r)^{ξQ} e^{ξ h_{3r}(z)}`), and suppose:
1. `D_h(u, y) > s₁ S` for `u ∈ ∂B_r(z)` and `y ∈ ∂B_{r/2}(z) ∪ ∂B_{2r}(z)`;
2. `D_h(u, v) > s₂ S` for `u ∈ ∂B_{r/2}(z)`, `v ∈ ∂B_r(z)`;
3. `D_h(u, v) < (s₁/100) S` for `u, v ∈ B̄_{2r}(z)` with `|u − v| ≤ b`, where `2πr/n ≤ b`;
4. `|D^ϕ − D_h| ≤ (s₁/100) S` on `B_{3r}(z)` (the form of `ConfSmallScale`).
Then `E^{LM}_r(z)` holds with `C = n s₁ / (50 s₂)`: chain around `∂B_r(z)` in `n` steps of length
`≤ 2πr/n`; each step has `D^ϕ ≤ (s₁/50) S < (99/100) s₁ S ≤ D^ϕ(u, ∂A)`, so it is realized inside
the annulus (`confMetric_eq_of_lt_iInf_frontier`). -/
theorem confLMGood_of_bounds {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V : Set ℂ}
    (hϕ : IsConfNbhd ϕ W V) {h hbar : DistC} {f : C(ℂ, ℝ)} {z : ℂ} {r s₁ s₂ b S : ℝ}
    (hr : 0 < r) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hS : 0 < S) {n : ℕ} (hn : 0 < n)
    (hnb : 2 * Real.pi * r / n ≤ b) (hV : closedBall z (2 * r) ⊆ V)
    (h1 : ∀ u ∈ sphere z r, ∀ y ∈ sphere z (r / 2) ∪ sphere z (2 * r), s₁ * S < (D h).1 (u, y))
    (h2 : ∀ u ∈ sphere z (r / 2), ∀ v ∈ sphere z r, s₂ * S < (D h).1 (u, v))
    (h3 : ∀ u ∈ closedBall z (2 * r), ∀ v ∈ closedBall z (2 * r), ‖u - v‖ ≤ b →
      (D h).1 (u, v) < s₁ / 100 * S)
    (h4 : ∀ u ∈ ball z (3 * r), ∀ v ∈ ball z (3 * r),
      confMetric D ϕ V hbar f u v ≤ ENNReal.ofReal ((D h).1 (u, v) + s₁ / 100 * S) ∧
      ENNReal.ofReal ((D h).1 (u, v)) ≤
        confMetric D ϕ V hbar f u v + ENNReal.ofReal (s₁ / 100 * S)) :
    ConfLMGood D ϕ h hbar f (n * s₁ / (50 * s₂)) z r := by
  set A : Set ℂ := (annulus z (r / 2) (2 * r) : Set ℂ) with hAdef
  have hAopen : IsOpen A := (annulus z (r / 2) (2 * r)).isOpen
  have hAV : A ⊆ V := fun y hy => hV (mem_closedBall_iff_norm.2 (le_of_lt hy.2))
  have hsA : sphere z r ⊆ A := fun y hy => by
    have e := mem_sphere_iff_norm.1 hy
    show r / 2 < ‖y - z‖ ∧ ‖y - z‖ < 2 * r
    rw [e]; constructor <;> linarith
  have hsS : 0 < s₁ * S := mul_pos hs₁ hS
  -- distance to the frontier of the annulus
  have hfar : ∀ u ∈ sphere z r, ∀ y ∈ frontier A ∩ V,
      ENNReal.ofReal (99 / 100 * (s₁ * S)) ≤ confMetric D ϕ V hbar f u y := by
    intro u hu y hy
    have hy' := frontier_annulus_subset z (r / 2) (2 * r) hy.1
    have hu3 : u ∈ ball z (3 * r) := by
      rw [mem_ball_iff_norm, mem_sphere_iff_norm.1 hu]; linarith
    have hy3 : y ∈ ball z (3 * r) := by
      rw [mem_ball_iff_norm]
      rcases hy' with e | e <;> rw [mem_sphere_iff_norm.1 e] <;> linarith
    have hl := (h4 u hu3 y hy3).2
    have hlow := h1 u hu y hy'
    have e1 : ENNReal.ofReal (s₁ * S) ≤ confMetric D ϕ V hbar f u y +
        ENNReal.ofReal (s₁ / 100 * S) :=
      (ENNReal.ofReal_le_ofReal hlow.le).trans hl
    have e2 := tsub_le_iff_right.2 e1
    rw [← ENNReal.ofReal_sub _ (by positivity)] at e2
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) e2
    linarith
  -- one step of the chain is realized inside the annulus
  have hstep : ∀ u ∈ sphere z r, ∀ v ∈ sphere z r, ‖u - v‖ ≤ 2 * Real.pi * r / n →
      confMetric D ϕ A hbar f u v ≤ ENNReal.ofReal (s₁ / 50 * S) := by
    intro u hu v hv huv
    have hu2 : u ∈ closedBall z (2 * r) := by
      rw [mem_closedBall_iff_norm, mem_sphere_iff_norm.1 hu]; linarith
    have hv2 : v ∈ closedBall z (2 * r) := by
      rw [mem_closedBall_iff_norm, mem_sphere_iff_norm.1 hv]; linarith
    have hu3 : u ∈ ball z (3 * r) := by
      rw [mem_ball_iff_norm, mem_sphere_iff_norm.1 hu]; linarith
    have hv3 : v ∈ ball z (3 * r) := by
      rw [mem_ball_iff_norm, mem_sphere_iff_norm.1 hv]; linarith
    have hD3 := h3 u hu2 v hv2 (huv.trans hnb)
    have hup : confMetric D ϕ V hbar f u v ≤ ENNReal.ofReal (s₁ / 50 * S) :=
      (h4 u hu3 v hv3).1.trans (ENNReal.ofReal_le_ofReal (by linarith))
    have hlt : confMetric D ϕ V hbar f u v <
        ⨅ y ∈ frontier A ∩ V, confMetric D ϕ V hbar f u y := by
      refine lt_of_lt_of_le (hup.trans_lt ?_) (le_iInf₂ fun y hy => hfar u hu y hy)
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    rw [(confMetric_eq_of_lt_iInf_frontier hϕ hAopen hAV (hsA hu) (hAV (hsA hv)) hlt).2]
    exact hup
  -- chaining around the circle
  have hchain := le_mul_of_circle_steps (d := confMetric D ϕ A hbar f)
    (fun x y w => confMetric_triangle x y w) hr.le hn hstep
  -- the crossing lower bound
  have hset : ENNReal.ofReal (s₂ * S) ≤ setDist (D h) (sphere z (r / 2)) (sphere z r) := by
    rw [GM.setDist_eq_iInf]
    exact le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal (h2 x hx y hy).le
  intro u hu v hv
  refine (hchain u hu v hv).trans ?_
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hC : 0 ≤ (n : ℝ) * s₁ / (50 * s₂) := by positivity
  have e : (n : ℝ≥0∞) * ENNReal.ofReal (s₁ / 50 * S) =
      ENNReal.ofReal ((n : ℝ) * s₁ / (50 * s₂)) * ENNReal.ofReal (s₂ * S) := by
    rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul hnR.le]
    congr 1
    field_simp
  rw [e]
  gcongr

/-! ## 3. [3] Lemma 3.5 (CC0 D11) -/

/-- `x = R · ((x - z)/R) + z` -/
lemma rescale_eq {R : ℝ} (hR : 0 < R) (z x : ℂ) : (R : ℂ) * ((x - z) / R) + z = x := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  field_simp
  ring

/-- `|(x - z)/R| = |x - z|/R` -/
lemma norm_rescale {R : ℝ} (hR : 0 < R) (z x : ℂ) : ‖(x - z) / (R : ℂ)‖ = ‖x - z‖ / R := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]

/-- the union bound behind Lemma 3.5: four bad events of (outer) probability `≤ (1 - p)/4` -/
lemma ofReal_le_measure_of_four {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {G B₁ B₂ B₃ B₄ : Set Ω} {p : ℝ} (hp : p < 1)
    (h₁ : P B₁ ≤ ENNReal.ofReal ((1 - p) / 4)) (h₂ : P B₂ ≤ ENNReal.ofReal ((1 - p) / 4))
    (h₃ : P B₃ ≤ ENNReal.ofReal ((1 - p) / 4)) (h₄ : P B₄ ≤ ENNReal.ofReal ((1 - p) / 4))
    (hsub : ∀ ω, ω ∉ B₁ → ω ∉ B₂ → ω ∉ B₃ → ω ∉ B₄ → ω ∈ G) :
    ENNReal.ofReal p ≤ P G := by
  have hc : Gᶜ ⊆ B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    exact hω (hsub ω hcon.1.1.1 hcon.1.1.2 hcon.1.2 hcon.2)
  have hq : 0 ≤ (1 - p) / 4 := by linarith
  have hGc : P Gᶜ ≤ ENNReal.ofReal (1 - p) := by
    calc P Gᶜ ≤ P (B₁ ∪ B₂ ∪ B₃ ∪ B₄) := measure_mono hc
      _ ≤ P B₁ + P B₂ + P B₃ + P B₄ := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal ((1 - p) / 4) + ENNReal.ofReal ((1 - p) / 4) +
            ENNReal.ofReal ((1 - p) / 4) + ENNReal.ofReal ((1 - p) / 4) := by gcongr
      _ = ENNReal.ofReal (1 - p) := by
          rw [← ENNReal.ofReal_add hq hq, ← ENNReal.ofReal_add (by linarith) hq,
            ← ENNReal.ofReal_add (by linarith) hq]
          congr 1
          ring
  have h1 : (1 : ℝ≥0∞) ≤ P G + P Gᶜ := by
    rw [← measure_univ (μ := P), ← union_compl_self G]
    exact measure_union_le _ _
  rcases le_or_gt p 0 with hp0 | hp0
  · rw [ENNReal.ofReal_of_nonpos hp0]
    exact zero_le
  have hsplit : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    rw [← ENNReal.ofReal_add hp0.le (by linarith)]
    simp
  refine ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (1 - p)) ENNReal.ofReal_ne_top ?_
  rw [hsplit]
  exact h1.trans (by gcongr)

/-- the compacts of the first crossing bound of Lemma 3.5 (at scale `3r`) -/
lemma disjoint_sphere_third :
    Disjoint (sphere (0 : ℂ) (1 / 3)) (sphere (0 : ℂ) (1 / 6) ∪ sphere (0 : ℂ) (2 / 3)) := by
  refine Set.disjoint_left.2 fun x hx hy => ?_
  rw [mem_sphere_zero_iff_norm] at hx
  rcases hy with hy | hy <;> rw [mem_sphere_zero_iff_norm] at hy <;> linarith

/-- the compacts of the second crossing bound of Lemma 3.5 (at scale `3r`) -/
lemma disjoint_sphere_sixth : Disjoint (sphere (0 : ℂ) (1 / 6)) (sphere (0 : ℂ) (1 / 3)) := by
  refine Set.disjoint_left.2 fun x hx hy => ?_
  rw [mem_sphere_zero_iff_norm] at hx hy
  linarith

/-- **[3] Lemma 3.5** (CC0 D11): for every `p < 1` there is `C > 0`, depending only on `p`, `γ`
and `D`, such that for every conformal neighbourhood `(ϕ, W, V)` and compact `K ⊆ V` there is
`r₀ > 0` with `P[E^{LM}_r(z)] ≥ p` for every coupling `(h, h̄, f)`, every `z ∈ K` and every
`r ∈ (0, r₀]`. `P` is applied to the event as an outer measure (no measurability is claimed
here; see `CC/Lemma35Local.lean`). The inputs are GM S2 tightness (`GM.Tight.gm_S2_4a` twice,
`gm_S2_4b`) and `ConfSmallScale` ([3] Prop 2.1), all at the radius `3r`, and the deterministic
core `confLMGood_of_bounds`. -/
theorem lemma35 {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    (hS : ConfSmallScale γ D) {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V →
    ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)),
      IsWholePlaneGFF h P → IsWholePlaneGFF hbar P → Measurable f →
      (∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) →
      ∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) r₀,
        ENNReal.ofReal p ≤ P {ω | ConfLMGood D ϕ (h ω) (hbar ω) (f ω) C z r} := by
  have hη : 0 < (1 - p) / 4 := by linarith
  have hε : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 - p) / 4) := ENNReal.ofReal_pos.2 hη
  have hW := GM.gm_eq1_15 hγ hD
  obtain ⟨s₁, hs₁, H1⟩ := GM.Tight.gm_S2_4a hW (isCompact_sphere (0 : ℂ) (1 / 3))
    ((isCompact_sphere (0 : ℂ) (1 / 6)).union (isCompact_sphere (0 : ℂ) (2 / 3)))
    disjoint_sphere_third hε
  obtain ⟨s₂, hs₂, H2⟩ := GM.Tight.gm_S2_4a hW (isCompact_sphere (0 : ℂ) (1 / 6))
    (isCompact_sphere (0 : ℂ) (1 / 3)) disjoint_sphere_sixth hε
  obtain ⟨b, hb, H3⟩ := GM.Tight.gm_S2_4b hW (isCompact_closedBall (0 : ℂ) (2 / 3))
    (s := s₁ / 100) (by positivity) hε
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.pi / (3 * b))
  have hnR : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn0 : 0 < n := by exact_mod_cast hnR
  refine ⟨n * s₁ / (50 * s₂), by positivity, ?_⟩
  intro ϕ W V hϕ K hK hKV
  obtain ⟨r₁, hr₁, H4⟩ := hS ϕ W V hϕ K hK hKV (s₁ / 100) (by positivity) ((1 - p) / 4) hη
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hϕ.isOpen_V hKV
  refine ⟨min (r₁ / 3) (δ / 2), by positivity, ?_⟩
  intro Ω _ P _ h hbar f hh hhb hf hc z hz r hr
  have hr0 : 0 < r := hr.1
  have hR : 0 < 3 * r := by linarith
  have hr1 : r ≤ r₁ / 3 := hr.2.trans (min_le_left _ _)
  have hr2 : r ≤ δ / 2 := hr.2.trans (min_le_right _ _)
  have hV : closedBall z (2 * r) ⊆ V :=
    ((closedBall_subset_cthickening hz _).trans (cthickening_mono (by linarith) K)).trans hδV
  have hnb : 2 * Real.pi * r / n ≤ 3 * r * b := by
    rw [div_le_iff₀ hnR]
    have h' := (div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * b)).1 hn
    nlinarith
  refine ofReal_le_measure_of_four hp (H1 P h hh (3 * r) hR z).le (H2 P h hh (3 * r) hR z).le
    (H3 P h hh (3 * r) hR z).le (H4 P h hbar f hh hhb hf hc z hz (3 * r) ⟨hR, by linarith⟩) ?_
  intro ω e1 e2 e3 e4
  simp only [mem_ofPred_eq, not_not] at e1 e2 e3 e4
  set S : ℝ := (3 * r) ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) (3 * r) z)
    with hSdef
  have hSpos : 0 < S := mul_pos (Real.rpow_pos_of_pos hR _) (Real.exp_pos _)
  show ConfLMGood D ϕ (h ω) (hbar ω) (f ω) (n * s₁ / (50 * s₂)) z r
  refine confLMGood_of_bounds hϕ hr0 hs₁ hs₂ hSpos hn0 hnb hV ?_ ?_ ?_ ?_
  · intro u hu y hy
    have hu' : (u - z) / ((3 * r : ℝ) : ℂ) ∈ sphere (0 : ℂ) (1 / 3) := by
      rw [mem_sphere_zero_iff_norm, norm_rescale hR, mem_sphere_iff_norm.1 hu]
      field_simp
    have hy' : (y - z) / ((3 * r : ℝ) : ℂ) ∈ sphere (0 : ℂ) (1 / 6) ∪ sphere (0 : ℂ) (2 / 3) := by
      rcases hy with hy | hy
      · left
        rw [mem_sphere_zero_iff_norm, norm_rescale hR, mem_sphere_iff_norm.1 hy]
        field_simp
        ring
      · right
        rw [mem_sphere_zero_iff_norm, norm_rescale hR, mem_sphere_iff_norm.1 hy]
        field_simp
    have := e1 _ hu' _ hy'
    rw [rescale_eq hR, rescale_eq hR] at this
    rw [hSdef, ← mul_assoc]
    exact this
  · intro u hu v hv
    have hu' : (u - z) / ((3 * r : ℝ) : ℂ) ∈ sphere (0 : ℂ) (1 / 6) := by
      rw [mem_sphere_zero_iff_norm, norm_rescale hR, mem_sphere_iff_norm.1 hu]
      field_simp
      ring
    have hv' : (v - z) / ((3 * r : ℝ) : ℂ) ∈ sphere (0 : ℂ) (1 / 3) := by
      rw [mem_sphere_zero_iff_norm, norm_rescale hR, mem_sphere_iff_norm.1 hv]
      field_simp
    have := e2 _ hu' _ hv'
    rw [rescale_eq hR, rescale_eq hR] at this
    rw [hSdef, ← mul_assoc]
    exact this
  · intro u hu v hv huv
    have hu' : (u - z) / ((3 * r : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (2 / 3) := by
      rw [mem_closedBall_zero_iff, norm_rescale hR, div_le_iff₀ hR]
      have := mem_closedBall_iff_norm.1 hu
      linarith
    have hv' : (v - z) / ((3 * r : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (2 / 3) := by
      rw [mem_closedBall_zero_iff, norm_rescale hR, div_le_iff₀ hR]
      have := mem_closedBall_iff_norm.1 hv
      linarith
    have huv' : ‖(u - z) / ((3 * r : ℝ) : ℂ) - (v - z) / ((3 * r : ℝ) : ℂ)‖ ≤ b := by
      rw [← sub_div, show u - z - (v - z) = u - v - 0 by ring, norm_rescale hR, sub_zero,
        div_le_iff₀ hR]
      linarith
    have := e3 _ hu' _ hv' huv'
    rw [rescale_eq hR, rescale_eq hR] at this
    rw [hSdef, ← mul_assoc]
    exact this
  · intro u hu v hv
    have := e4 u hu v hv
    rw [hSdef, ← mul_assoc]
    exact this

end SmallGammaGeodesics.CC
