import HigherDimLFPPAS.Main.Prelim
import HigherDimLFPPAS.Bridge.Geodesic
import HigherDimLFPPAS.Det.InternalBasic
import HigherDimLQGMetric.Amplify.LengthScale

/-!
# Lemma 6.2: deterministic ingredients (packet L62)

The deterministic part of the proof of Lemma 6.2 (MA2 §§2.19–2.20 and Details D-D, with the corrections m5, m6; paper
l. 688–727). Throughout, `𝔐` is the metric whose minimizers are confined (`M_ε` or `N_ε` for some `ε ∈ I_n`), `M'` is the
reference metric `M_{ε_n}` at the selected scale `ε_n = n^{-a}`, `k` is the radius of the endpoint ball `B̄_k`, `R > k + 4`
is the integer radius of (6.6) and `T = T_k ≥ 1` the competitor bound of (6.5). The hypotheses are:

* `hup`, `hdown`: the density comparison on `V = B_{R+1}` with ratio `2` in both directions (from (6.7) through MA2 D-D1:
  the log density ratio is at most `log 2`, "eventually these ratios lie between 1/2 and 2");
* `hcomp`: the competitor bound (a) `M'(x, y; B_{k+3}) ≤ T − 1/2` on `B̄_k × B̄_k` (from (6.2));
* `hexit`: the exit bound (b) `M'(x, y; B_{R+1}) ≥ 4T` for `x ∈ B̄_k`, `y ∈ S_R` (from (2.12) and (6.6)).

Results:

* `l62_exists_sphere_hit`: first hitting time of `S_R` by a path started inside `B_R`;
* `l62_competitor`: `𝔐(x, y) ≤ 2T − 1` on `B̄_k × B̄_k`;
* `l62_exit_len`: every path from `x ∈ B̄_k` reaching `S_R` has `𝔐`-length `≥ 2T` (the separation `2T − 1 < 2T`);
* `l62_global_eq_internal`: global = internal on `B_R` for pairs in `B̄_k` (D-D2, D5's `internal_eq_global_of_barrier`);
* `l62_exists_geodesic`: a unit-speed `𝔐`-geodesic inside `B_R` when `𝔐 = c · D^φ` is a scaled LFPP metric (D-D3, D5's
  `fieldLfppMetric_exists_geodesic_of_barrier`, reparametrized by `t ↦ t / c`);
* `l62_window_compare`: the ratio-`2` comparisons between `M_ε`, `N_ε` and `M_{ε'}` from the log-ratio bound `log 2`;
* `l62_exists_internal_bound`, `l62_comp_of_lemma61`, `l62_exit_of_reverse`: the bounds (a) and (b) from (6.2), (2.12)
  and (6.6); `l62_log_ratio_bound`, `l62_density_bound`: the real arithmetic of (6.7).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Endpoint

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ### Paths reaching the sphere -/

/-- **First hit of the sphere** `S_R`: a path on `[a, b]` started inside `B_R` and ending outside `B_R` hits `S_R` at a
time `s` before which it stays in `B̄_R`. -/
theorem l62_exists_sphere_hit {P : ℝ → Rd d} {a b R : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (ha : ‖P a‖ < R) (hb : R ≤ ‖P b‖) :
    ∃ s ∈ Icc a b, ‖P s‖ = R ∧ ∀ t ∈ Icc a s, ‖P t‖ ≤ R := by
  have hK : IsClosed {q : Rd d | R ≤ ‖q‖} := isClosed_le continuous_const continuous_norm
  obtain ⟨s, hs, hsK, hbefore⟩ := exists_first_hit hP hK ⟨b, ⟨hab, le_rfl⟩, hb⟩
  have hsK' : R ≤ ‖P s‖ := hsK
  have hlt : ∀ t ∈ Ico a s, ‖P t‖ < R := fun t ht => lt_of_not_ge (hbefore t ht)
  have hsle : ‖P s‖ ≤ R := by
    by_contra hcon
    have hRlt : R < ‖P s‖ := lt_of_not_ge hcon
    have hnorm : ContinuousOn (fun u : ℝ => ‖P u‖) (Icc a s) :=
      (hP.mono (Icc_subset_Icc le_rfl hs.2)).norm
    obtain ⟨u, hu, huR⟩ := intermediate_value_Icc hs.1 hnorm ⟨ha.le, hRlt.le⟩
    have huR' : ‖P u‖ = R := huR
    have hus : u ≠ s := by
      rintro rfl
      exact (ne_of_gt hRlt) huR'
    have := hlt u ⟨hu.1, lt_of_le_of_ne hu.2 hus⟩
    rw [huR'] at this
    exact lt_irrefl R this
  refine ⟨s, hs, le_antisymm hsle hsK', fun t ht => ?_⟩
  rcases eq_or_lt_of_le ht.2 with hts | hts
  · rw [hts]
    exact hsle
  · exact (hlt t ⟨ht.1, hts⟩).le

/-! ### Competitors, exits, and the barrier -/

/-- **Competitors** (MA2 D-D, "Competitors: `𝔐(x, y) ≤ e^s(T_k − 1/2)`" with `e^s ≤ 2`): for `x, y ∈ B̄_k`,
`𝔐(x, y) ≤ 𝔐(x, y; B_{R+1}) ≤ 2 M'(x, y; B_{R+1}) ≤ 2 M'(x, y; B_{k+3}) ≤ 2T − 1`. -/
theorem l62_competitor {𝔐 M' : ContMetric d} {k R : ℕ} (hkR : (k : ℝ) + 4 < R) {T : ℝ}
    (hT : 1 ≤ T)
    (hup : ∀ x y : Rd d, 𝔐.internal (ball 0 ((R : ℝ) + 1)) x y ≤
      ENNReal.ofReal 2 * M'.internal (ball 0 ((R : ℝ) + 1)) x y)
    (hcomp : ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      M'.internal (ball 0 ((k : ℝ) + 3)) x y ≤ ENNReal.ofReal (T - 1 / 2))
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) k) (hy : y ∈ closedBall (0 : Rd d) k) :
    𝔐.1 (x, y) ≤ 2 * T - 1 := by
  have hsub : ball (0 : Rd d) ((k : ℝ) + 3) ⊆ ball 0 ((R : ℝ) + 1) :=
    ball_subset_ball (by linarith)
  have h : ENNReal.ofReal (𝔐.1 (x, y)) ≤ ENNReal.ofReal (2 * T - 1) := by
    calc ENNReal.ofReal (𝔐.1 (x, y)) ≤ 𝔐.internal (ball 0 ((R : ℝ) + 1)) x y :=
          𝔐.ofReal_le_internal _ x y
      _ ≤ ENNReal.ofReal 2 * M'.internal (ball 0 ((R : ℝ) + 1)) x y := hup x y
      _ ≤ ENNReal.ofReal 2 * M'.internal (ball 0 ((k : ℝ) + 3)) x y := by
          gcongr
          exact M'.internal_anti hsub x y
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (T - 1 / 2) := by
          gcongr
          exact hcomp x hx y hy
      _ = ENNReal.ofReal (2 * T - 1) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h

/-- **Exits** (MA2 §2.19 and D-D, "Exits: `> e^{-s} 4T_k`" with `e^s ≤ 2`): every path from `x ∈ B̄_k` to the sphere
`S_R` has `𝔐`-length at least `2T`. Up to its first hit `P s ∈ S_R` it stays in `B̄_R ⊂ B_{R+1}`, so its length is at
least `𝔐(x, P s; B_{R+1}) ≥ M'(x, P s; B_{R+1}) / 2 ≥ 2T`. -/
theorem l62_exit_len {𝔐 M' : ContMetric d} {k R : ℕ} (hkR : (k : ℝ) + 4 < R) {T : ℝ}
    (hdown : ∀ x y : Rd d, M'.internal (ball 0 ((R : ℝ) + 1)) x y ≤
      ENNReal.ofReal 2 * 𝔐.internal (ball 0 ((R : ℝ) + 1)) x y)
    (hexit : ∀ x ∈ closedBall (0 : Rd d) k, ∀ y : Rd d, ‖y‖ = R →
      ENNReal.ofReal (4 * T) ≤ M'.internal (ball 0 ((R : ℝ) + 1)) x y)
    {x : Rd d} (hx : x ∈ closedBall (0 : Rd d) k)
    {P : ℝ → Rd d} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) (hPa : P a = x)
    (hPb : ‖P b‖ = R) :
    ENNReal.ofReal (2 * T) ≤ 𝔐.len P a b := by
  have hxk : ‖x‖ ≤ k := mem_closedBall_zero_iff.1 hx
  have hxR : ‖P a‖ < R := by
    rw [hPa]
    linarith
  obtain ⟨s, hs, hsR, hle⟩ := l62_exists_sphere_hit hab hP hxR hPb.ge
  have hmaps : MapsTo P (Icc a s) (ball 0 ((R : ℝ) + 1)) := fun t ht => by
    rw [mem_ball_zero_iff]
    linarith [hle t ht]
  have hint := 𝔐.internal_le_len hs.1 (hP.mono (Icc_subset_Icc le_rfl hs.2)) hmaps
  rw [hPa] at hint
  have hlen : 𝔐.len P a s ≤ 𝔐.len P a b := 𝔐.len_mono P le_rfl hs.2
  have h4 : ENNReal.ofReal 2 * ENNReal.ofReal (2 * T) ≤
      ENNReal.ofReal 2 * 𝔐.internal (ball 0 ((R : ℝ) + 1)) x (P s) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), show (2 : ℝ) * (2 * T) = 4 * T by ring]
    exact (hexit x hx (P s) hsR).trans (hdown x (P s))
  have h2 := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 two_pos).ne'
    ENNReal.ofReal_ne_top).1 h4
  exact h2.trans (hint.trans hlen)

/-- **Global = internal on `B_R`** (MA2 D-D2 applied as in D-D, "D-D2 gives `𝔐(x, y) = 𝔐(x, y; B_R)`"): for a length
metric `𝔐`, the competitor bound `2T − 1` and the exit bound `2T` give `𝔐(x, y) = 𝔐(x, y; B_R)` for `x, y ∈ B̄_k`. -/
theorem l62_global_eq_internal {𝔐 M' : ContMetric d} (h𝔐 : 𝔐.IsLength) {k R : ℕ}
    (hkR : (k : ℝ) + 4 < R) {T : ℝ} (hT : 1 ≤ T)
    (hup : ∀ x y : Rd d, 𝔐.internal (ball 0 ((R : ℝ) + 1)) x y ≤
      ENNReal.ofReal 2 * M'.internal (ball 0 ((R : ℝ) + 1)) x y)
    (hdown : ∀ x y : Rd d, M'.internal (ball 0 ((R : ℝ) + 1)) x y ≤
      ENNReal.ofReal 2 * 𝔐.internal (ball 0 ((R : ℝ) + 1)) x y)
    (hcomp : ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      M'.internal (ball 0 ((k : ℝ) + 3)) x y ≤ ENNReal.ofReal (T - 1 / 2))
    (hexit : ∀ x ∈ closedBall (0 : Rd d) k, ∀ y : Rd d, ‖y‖ = R →
      ENNReal.ofReal (4 * T) ≤ M'.internal (ball 0 ((R : ℝ) + 1)) x y)
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) k) (hy : y ∈ closedBall (0 : Rd d) k) :
    ENNReal.ofReal (𝔐.1 (x, y)) = 𝔐.internal (ball 0 (R : ℝ)) x y := by
  have hxR : ‖x‖ < R := by
    have := mem_closedBall_zero_iff.1 hx
    linarith
  have hyR : ‖y‖ < R := by
    have := mem_closedBall_zero_iff.1 hy
    linarith
  have hxy : 𝔐.1 (x, y) < 2 * T := by
    linarith [l62_competitor hkR hT hup hcomp hx hy]
  exact (Bridge.internal_eq_global_of_barrier 𝔐 h𝔐 hxR hyR hxy
    fun hab hP hPa hPb => l62_exit_len hkR hdown hexit hx hab hP hPa hPb).symm

/-- **Unit-speed geodesics inside `B_R`** (MA2 D-D3 applied as in D-D, m6): if `𝔐 = c · D^φ` is a scaled LFPP metric of
a continuous field, the competitor bound `2T − 1` and the exit bound `2T` give a strict barrier for `D^φ` with gap
`1/(2c)`; D5's `fieldLfppMetric_exists_geodesic_of_barrier` gives a unit-speed `D^φ`-geodesic `P` from `x` to `y` in
`B_R`, and `γ(t) = P(t / c)` on `[0, 𝔐(x, y)]` is a unit-speed `𝔐`-geodesic: `𝔐(γ s, γ t) = |t − s|`. -/
theorem l62_exists_geodesic {ξ : ℝ} (hξ : 0 < ξ) {𝔐 M' : ContMetric d} {φ : C(Rd d, ℝ)} {c : ℝ}
    (hc : 0 < c) (h𝔐 : 𝔐 = (fieldLfppMetric ξ φ).smul c hc) {k R : ℕ}
    (hkR : (k : ℝ) + 4 < R) {T : ℝ} (hT : 1 ≤ T)
    (hup : ∀ x y : Rd d, 𝔐.internal (ball 0 ((R : ℝ) + 1)) x y ≤
      ENNReal.ofReal 2 * M'.internal (ball 0 ((R : ℝ) + 1)) x y)
    (hdown : ∀ x y : Rd d, M'.internal (ball 0 ((R : ℝ) + 1)) x y ≤
      ENNReal.ofReal 2 * 𝔐.internal (ball 0 ((R : ℝ) + 1)) x y)
    (hcomp : ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      M'.internal (ball 0 ((k : ℝ) + 3)) x y ≤ ENNReal.ofReal (T - 1 / 2))
    (hexit : ∀ x ∈ closedBall (0 : Rd d) k, ∀ y : Rd d, ‖y‖ = R →
      ENNReal.ofReal (4 * T) ≤ M'.internal (ball 0 ((R : ℝ) + 1)) x y)
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) k) (hy : y ∈ closedBall (0 : Rd d) k) :
    ∃ (γ : ℝ → Rd d) (T' : ℝ), 0 ≤ T' ∧ γ 0 = x ∧ γ T' = y ∧ ContinuousOn γ (Icc 0 T') ∧
      MapsTo γ (Icc 0 T') (ball 0 (R : ℝ)) ∧
      ∀ s ∈ Icc 0 T', ∀ t ∈ Icc 0 T', 𝔐.1 (γ s, γ t) = |t - s| := by
  have hcomp' := l62_competitor hkR hT hup hcomp hx hy
  have hexit' : ∀ {P : ℝ → Rd d} {a b : ℝ}, a ≤ b → ContinuousOn P (Icc a b) → P a = x →
      ‖P b‖ = R → ENNReal.ofReal (2 * T) ≤ 𝔐.len P a b :=
    fun hab hP hPa hPb => l62_exit_len hkR hdown hexit hx hab hP hPa hPb
  subst h𝔐
  set G : ContMetric d := fieldLfppMetric ξ φ with hGdef
  have hxR : ‖x‖ < R := by
    have := mem_closedBall_zero_iff.1 hx
    linarith
  have hyR : ‖y‖ < R := by
    have := mem_closedBall_zero_iff.1 hy
    linarith
  have hR0 : (0 : ℝ) < R := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hκ : 0 < 1 / (2 * c) := by positivity
  have hcG : c * G.1 (x, y) ≤ 2 * T - 1 := by
    simpa only [ContMetric.smul_apply] using hcomp'
  -- the strict barrier for `D^φ`, with gap `1/(2c)`
  have hbar : ∀ {P : ℝ → Rd d} {a b : ℝ}, a ≤ b → ContinuousOn P (Icc a b) → P a = x →
      ‖P b‖ = R → ENNReal.ofReal (G.1 (x, y) + 1 / (2 * c)) < G.len P a b := by
    intro P a b hab hP hPa hPb
    by_contra hcon
    have hle : G.len P a b ≤ ENNReal.ofReal (G.1 (x, y) + 1 / (2 * c)) := not_lt.1 hcon
    have h1 := hexit' hab hP hPa hPb
    rw [amplify_len_smul] at h1
    have h2 : ENNReal.ofReal c * G.len P a b ≤ ENNReal.ofReal (c * G.1 (x, y) + 1 / 2) := by
      calc ENNReal.ofReal c * G.len P a b ≤
            ENNReal.ofReal c * ENNReal.ofReal (G.1 (x, y) + 1 / (2 * c)) := by gcongr
        _ = ENNReal.ofReal (c * G.1 (x, y) + 1 / 2) := by
            rw [← ENNReal.ofReal_mul hc.le]
            congr 1
            field_simp
    have h3 : ENNReal.ofReal (2 * T) ≤ ENNReal.ofReal (c * G.1 (x, y) + 1 / 2) := h1.trans h2
    have h4 := (ENNReal.ofReal_le_ofReal_iff
      (by have := mul_nonneg hc.le (G.nonneg x y); linarith)).1 h3
    linarith
  obtain ⟨P, h0, hL, hgeo, hu, hstay⟩ :=
    Bridge.fieldLfppMetric_exists_geodesic_of_barrier hR0 hξ hκ φ x y hxR hyR hbar
  set L : ℝ := G.1 (x, y) with hLdef
  have hL0 : 0 ≤ L := G.nonneg x y
  -- the all-pairs identity for `D^φ` along `P`
  have hpair : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, G.1 (P s, P t) = |t - s| := by
    have hle : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t → G.1 (P s, P t) = t - s := by
      intro s hs t ht hst
      have h := hgeo.edist_eq_of_hasUnitSpeedOn hu hs ht hst
      rw [Function.comp_apply, Function.comp_apply, G.edist_pt] at h
      exact (ENNReal.ofReal_eq_ofReal_iff (G.nonneg _ _) (sub_nonneg.2 hst)).1 h
    intro s hs t ht
    rcases le_total s t with hst | hts
    · rw [hle s hs t ht hst, abs_of_nonneg (sub_nonneg.2 hst)]
    · rw [G.apply_comm, hle t ht s hs hts, abs_of_nonpos (sub_nonpos.2 hts)]
      ring
  have hPc : ContinuousOn P (Icc 0 L) := (G.continuousOn_pt_comp_iff).1 hgeo.2.1
  -- the reparametrization `γ(t) = P(t / c)` on `[0, c L]`
  have hmem : ∀ t ∈ Icc (0 : ℝ) (c * L), t / c ∈ Icc 0 L := by
    intro t ht
    refine ⟨div_nonneg ht.1 hc.le, ?_⟩
    rw [div_le_iff₀ hc]
    linarith [ht.2]
  refine ⟨fun t => P (t / c), c * L, mul_nonneg hc.le hL0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [zero_div] using h0
  · simp only
    rw [mul_div_cancel_left₀ _ hc.ne']
    exact hL
  · exact hPc.comp (continuousOn_id.div_const c) hmem
  · intro t ht
    rw [mem_ball_zero_iff]
    exact hstay _ (hmem t ht)
  · intro s hs t ht
    rw [ContMetric.smul_apply, hpair _ (hmem s hs) _ (hmem t ht),
      show t / c - s / c = (t - s) / c by ring, abs_div, abs_of_pos hc,
      mul_div_cancel₀ _ hc.ne']

/-! ### The density comparison with ratio `2` -/

/-- The reverse direction of the density comparison (MA2 D-D1): the hypothesis of
`Main.thm_smul_internal_le` is symmetric under `(α, φ) ↔ (β, ψ)`. -/
theorem l62_smul_internal_le_rev {ξ s α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (φ ψ : C(Rd d, ℝ))
    {V : Set (Rd d)} (hV : IsOpen V)
    (hb : ∀ z ∈ V, |Real.log (α / β) + ξ * (φ z - ψ z)| ≤ s) (x y : Rd d) :
    ((fieldLfppMetric ξ ψ).smul β hβ).internal V x y ≤
      ENNReal.ofReal (Real.exp s) * ((fieldLfppMetric ξ φ).smul α hα).internal V x y := by
  refine Main.thm_smul_internal_le hβ hα ψ φ hV (fun z hz => ?_) x y
  have hlog : Real.log (β / α) = -Real.log (α / β) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog, show -Real.log (α / β) + ξ * (ψ z - φ z) =
    -(Real.log (α / β) + ξ * (φ z - ψ z)) by ring, abs_neg]
  exact hb z hz

/-- **The window comparisons** (MA2 D-D (c) and the conclusion for `𝔐 ∈ {M_ε, N_ε}`): if the logarithms of the density
ratios of `M_ε` and of `N_ε` against `M_{ε'}` are at most `log 2` on the open set `V`, then on `V` the internal metrics
of `M_ε` and `N_ε` compare with that of `M_{ε'}` with ratio `2` in both directions. -/
theorem l62_window_compare (κ : Rd d → ℝ) {ξ ε ε' : ℝ} {g : DistRd d} {V : Set (Rd d)}
    (hV : IsOpen V) (ha : 0 < aEps κ ξ ε) (ha' : 0 < aEps κ ξ ε')
    (hcl : Continuous (locField κ ε g)) (hcl' : Continuous (locField κ ε' g))
    (hcc : Continuous (convMollify κ ε g))
    (hbM : ∀ z ∈ V, |Real.log (aEps κ ξ ε' / aEps κ ξ ε) +
      ξ * (locField κ ε g z - locField κ ε' g z)| ≤ Real.log 2)
    (hbN : ∀ z ∈ V, |Real.log (aEps κ ξ ε' / aEps κ ξ ε) +
      ξ * (convMollify κ ε g z - locField κ ε' g z)| ≤ Real.log 2) (x y : Rd d) :
    (Core.Meps κ ξ ε g).internal V x y ≤ ENNReal.ofReal 2 * (Core.Meps κ ξ ε' g).internal V x y ∧
      (Core.Meps κ ξ ε' g).internal V x y ≤
        ENNReal.ofReal 2 * (Core.Meps κ ξ ε g).internal V x y ∧
      (Core.Neps κ ξ ε g).internal V x y ≤
        ENNReal.ofReal 2 * (Core.Meps κ ξ ε' g).internal V x y ∧
      (Core.Meps κ ξ ε' g).internal V x y ≤
        ENNReal.ofReal 2 * (Core.Neps κ ξ ε g).internal V x y := by
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log two_pos
  have hbM' : ∀ z ∈ V, |Real.log ((aEps κ ξ ε)⁻¹ / (aEps κ ξ ε')⁻¹) +
      ξ * (Core.locFieldC κ ε g z - Core.locFieldC κ ε' g z)| ≤ Real.log 2 := by
    intro z hz
    rw [inv_div_inv, Main.thm_locFieldC_eq κ hcl, Main.thm_locFieldC_eq κ hcl']
    exact hbM z hz
  have hbN' : ∀ z ∈ V, |Real.log ((aEps κ ξ ε)⁻¹ / (aEps κ ξ ε')⁻¹) +
      ξ * (Core.convFieldC κ ε g z - Core.locFieldC κ ε' g z)| ≤ Real.log 2 := by
    intro z hz
    rw [inv_div_inv, Main.thm_convFieldC_eq κ hcc, Main.thm_locFieldC_eq κ hcl']
    exact hbN z hz
  rw [Main.thm_meps_eq κ g ha, Main.thm_meps_eq κ g ha', Main.thm_neps_eq κ g ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [h2] using
      Main.thm_smul_internal_le (inv_pos.2 ha) (inv_pos.2 ha') _ _ hV hbM' x y
  · simpa only [h2] using l62_smul_internal_le_rev (inv_pos.2 ha) (inv_pos.2 ha') _ _ hV hbM' x y
  · simpa only [h2] using
      Main.thm_smul_internal_le (inv_pos.2 ha) (inv_pos.2 ha') _ _ hV hbN' x y
  · simpa only [h2] using l62_smul_internal_le_rev (inv_pos.2 ha) (inv_pos.2 ha') _ _ hV hbN' x y

/-! ### The bounds (a) and (b) from (6.2), (2.12) and (6.6) -/

/-- The internal metric of a continuous length metric on `B_{r+2}` is bounded on `B̄_r × B̄_r` (Lemma 2.1; finite and
continuous, D1's `internal_finite_continuous`, on a compact set). This is the finiteness of `T_k` in (6.5). -/
theorem l62_exists_internal_bound (G : ContMetric d) (hG : G.IsLength) {r : ℝ} (hr : 0 ≤ r) :
    ∃ Δ : ℝ, 0 ≤ Δ ∧ ∀ x ∈ closedBall (0 : Rd d) r, ∀ y ∈ closedBall (0 : Rd d) r,
      G.internal (ball 0 (r + 2)) x y ≤ ENNReal.ofReal Δ := by
  have hsub : closedBall (0 : Rd d) r ⊆ ball 0 (r + 2) := closedBall_subset_ball (by linarith)
  obtain ⟨hfin, hcont⟩ := Det.internal_finite_continuous G hG (isOpen_ball (x := (0 : Rd d)))
    (isConnected_ball (by linarith : (0 : ℝ) < r + 2))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Rd d) r).prod
    (isCompact_closedBall (0 : Rd d) r)).exists_bound_of_continuousOn (hcont.mono (prod_mono hsub hsub))
  refine ⟨max C 0, le_max_right _ _, fun x hx y hy => ?_⟩
  rw [← ENNReal.ofReal_toReal (hfin x (hsub hx) y (hsub hy))]
  exact ENNReal.ofReal_le_ofReal
    ((Real.le_norm_self _).trans ((hC (x, y) ⟨hx, hy⟩).trans (le_max_left _ _)))

/-- **The competitor bound (a)** (MA2 D-D (a), from (6.2) at the integer radius `k + 1` with error `1/2`): if
`G(x, y; B_{k+2}) ≤ Δ` on `B̄_k × B̄_k`, then `M(x, y; B_{k+3}) ≤ C₁ Δ + 1/2` there. -/
theorem l62_comp_of_lemma61 {G M : ContMetric d} {C₁ Δ : ℝ} (hC₁ : 0 < C₁) (hΔ0 : 0 ≤ Δ) {k : ℕ}
    (hΔ : ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      G.internal (ball 0 ((k : ℝ) + 2)) x y ≤ ENNReal.ofReal Δ)
    (h61 : ∀ x ∈ closedBall (0 : Rd d) ((k + 1 : ℕ) : ℝ), ∀ y ∈ closedBall (0 : Rd d) ((k + 1 : ℕ) : ℝ),
      M.internal (ball 0 (((k + 1 : ℕ) : ℝ) + 2)) x y ≤
        ENNReal.ofReal C₁ * G.internal (ball 0 (((k + 1 : ℕ) : ℝ) + 1)) x y + ENNReal.ofReal (1 / 2)) :
    ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      M.internal (ball 0 ((k : ℝ) + 3)) x y ≤ ENNReal.ofReal (C₁ * Δ + 1 / 2) := by
  intro x hx y hy
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hsub : closedBall (0 : Rd d) k ⊆ closedBall 0 ((k + 1 : ℕ) : ℝ) :=
    closedBall_subset_closedBall (by rw [hk1]; linarith)
  have h := h61 x (hsub hx) y (hsub hy)
  rw [hk1, show (k : ℝ) + 1 + 2 = (k : ℝ) + 3 by ring,
    show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring] at h
  calc M.internal (ball 0 ((k : ℝ) + 3)) x y ≤
        ENNReal.ofReal C₁ * G.internal (ball 0 ((k : ℝ) + 2)) x y + ENNReal.ofReal (1 / 2) := h
    _ ≤ ENNReal.ofReal C₁ * ENNReal.ofReal Δ + ENNReal.ofReal (1 / 2) := by
        gcongr
        exact hΔ x hx y hy
    _ = ENNReal.ofReal (C₁ * Δ + 1 / 2) := by
        rw [← ENNReal.ofReal_mul hC₁.le,
          ← ENNReal.ofReal_add (mul_nonneg hC₁.le hΔ0) (by norm_num)]

/-- A lower bound for a set distance by lower bounds for the global distances between the two sets. -/
theorem l62_le_setDistIn (G : ContMetric d) {V A B : Set (Rd d)} {e : ℝ≥0∞}
    (h : ∀ u ∈ A, ∀ v ∈ B, e ≤ ENNReal.ofReal (G.1 (u, v))) : e ≤ setDistIn G V A B := by
  unfold setDistIn
  exact le_iInf₂ fun u hu => le_iInf₂ fun v hv => (h u hu v hv).trans (G.ofReal_le_internal V u v)

/-- **The exit bound (b)** (MA2 §2.19, D-D (b)): if (6.6) holds in the form `G(u, v) > 4 C₂ T` for `u ∈ B̄_{k+1}`,
`‖v‖ ≥ R − 1`, and the reverse comparison (2.12) holds on `B_{R+1}` with endpoint radius `r < 1` and constant `C₂`, then
`M(x, y; B_{R+1}) ≥ 4T` for `x ∈ B̄_k` and `y ∈ S_R` (the `r`-balls around `x` and `y` lie in `B̄_{k+1}` and outside
`B_{R−1}`). -/
theorem l62_exit_of_reverse {G M : ContMetric d} {C₂ T r R₁ : ℝ} {k R : ℕ} {W : Set (Rd d)}
    (hC₂ : 0 < C₂) (hr : r < 1) (hkR : (k : ℝ) + 4 < R)
    (hR₁ : ∀ u ∈ closedBall (0 : Rd d) ((k : ℝ) + 1), ∀ v : Rd d, R₁ ≤ ‖v‖ →
      C₂ * (4 * T) < G.1 (u, v))
    (hR₁R : R₁ ≤ (R : ℝ) - 1)
    (hrev : ∀ x ∈ ball (0 : Rd d) ((R : ℝ) + 1), ∀ y ∈ ball (0 : Rd d) ((R : ℝ) + 1),
      setDistIn G W (ball x r) (ball y r) ≤
        ENNReal.ofReal C₂ * M.internal (ball 0 ((R : ℝ) + 1)) x y) :
    ∀ x ∈ closedBall (0 : Rd d) k, ∀ y : Rd d, ‖y‖ = R →
      ENNReal.ofReal (4 * T) ≤ M.internal (ball 0 ((R : ℝ) + 1)) x y := by
  intro x hx y hy
  have hxk : ‖x‖ ≤ k := mem_closedBall_zero_iff.1 hx
  have hxV : x ∈ ball (0 : Rd d) ((R : ℝ) + 1) := by
    rw [mem_ball_zero_iff]
    linarith
  have hyV : y ∈ ball (0 : Rd d) ((R : ℝ) + 1) := by
    rw [mem_ball_zero_iff, hy]
    linarith
  have hlow : ENNReal.ofReal C₂ * ENNReal.ofReal (4 * T) ≤ setDistIn G W (ball x r) (ball y r) := by
    rw [← ENNReal.ofReal_mul hC₂.le]
    refine l62_le_setDistIn G fun u hu v hv => ENNReal.ofReal_le_ofReal (hR₁ u ?_ v ?_).le
    · rw [mem_ball, dist_eq_norm] at hu
      rw [mem_closedBall_zero_iff]
      calc ‖u‖ = ‖x + (u - x)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x‖ + ‖u - x‖ := norm_add_le _ _
        _ ≤ (k : ℝ) + 1 := by linarith
    · rw [mem_ball, dist_eq_norm] at hv
      have h1 : ‖y‖ ≤ ‖v‖ + ‖v - y‖ := by
        calc ‖y‖ = ‖v - (v - y)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖v‖ + ‖v - y‖ := norm_sub_le _ _
      linarith
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hC₂).ne' ENNReal.ofReal_ne_top).1
    (hlow.trans (hrev x hxV y hyV))

/-! ### The real arithmetic of (6.7) -/

/-- `|log(A'/A)| ≤ 2η` when `|A/A' − 1| ≤ η ≤ 1/2` (from (2.10) through `Main.thm_abs_log_le`). -/
theorem l62_log_ratio_bound {A A' η : ℝ} (hA : 0 < A) (hA' : 0 < A') (hη : η ≤ 1 / 2)
    (h : |A / A' - 1| ≤ η) : |Real.log (A' / A)| ≤ 2 * η := by
  have h1 := Main.thm_abs_log_le (div_pos hA hA') hη h
  rwa [← inv_div, Real.log_inv, abs_neg]

/-- The two log density ratios of (6.7): with `|L| ≤ θ`, `|u| ≤ θ/ξ` (Lemma 2.3 (iii)) and `|w| ≤ θ/ξ` (Lemma 2.3 (i)),
`|L + ξ u| ≤ 2θ` and `|L + ξ (u − w)| ≤ 3θ`. -/
theorem l62_density_bound {L u w ξ θ : ℝ} (hξ : 0 < ξ) (hL : |L| ≤ θ) (hu : |u| ≤ θ / ξ)
    (hw : |w| ≤ θ / ξ) : |L + ξ * u| ≤ 2 * θ ∧ |L + ξ * (u - w)| ≤ 3 * θ := by
  have hξu : |ξ * u| ≤ θ := by
    rw [abs_mul, abs_of_pos hξ]
    exact (le_div_iff₀' hξ).1 hu
  have hξw : |ξ * w| ≤ θ := by
    rw [abs_mul, abs_of_pos hξ]
    exact (le_div_iff₀' hξ).1 hw
  obtain ⟨h1, h2⟩ := abs_le.1 hL
  obtain ⟨h3, h4⟩ := abs_le.1 hξu
  obtain ⟨h5, h6⟩ := abs_le.1 hξw
  rw [mul_sub]
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

end HigherDimLFPPAS.Endpoint
