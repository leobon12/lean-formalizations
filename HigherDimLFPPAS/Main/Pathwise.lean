import HigherDimLFPPAS.Main.Prelim

/-!
# Proof of Theorem 1.2: the pathwise argument (packet THM)

The deterministic part of the proof of Theorem 1.2 (MA2 §§2.21–2.25, Details D-E; paper l. 729–771), for one fixed
sample `g = h(ω)` with `G = D_g`, on which the almost-sure conclusions of Proposition 5.1 (through Borel–Cantelli),
Lemmas 6.1, 6.2, 2.3 (i), (iii), and Lemma 2.2 hold:

* `thm_seq_compare`: (6.8)–(6.9) along `ε_n = n^{-a}` on `B̄_k`, with the error `2σ` for any `σ > 0` (Proposition 5.1
  at a common radius `R` containing the `D`- and `M_{ε_n}`-geodesics, (6.3) of Lemma 6.1 on `B̄_{k+1}`, continuity of
  `D`);
* `thm_window_compare`: (6.10), `M_ε ≤ e^s M_{ε_n}` and `M_{ε_n} ≤ e^s M_ε` on `B̄_k` for `ε ∈ I_n` (Lemma 6.2's global
  = internal on `B_R`, Lemma 2.3 (iii), (2.10));
* `thm_meps_close`: (6.11) for every `δ_j` and the limit `j → ∞`: `sup_{B̄_k²} |M_ε − D| → 0`;
* `thm_neps_close`: the transfer to `N_ε` (Lemma 2.3 (i), Lemma 6.2);
* `thm_tendsto_of_uniform` and `thm_pathwise`: compact sets and the `[0, ∞]`-supremum form of (1.7).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Main

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- **(6.8)–(6.9)** along `ε_n = n^{-a}` (MA2 §2.21): for every `σ > 0`, eventually in `n`, for `x, y ∈ B̄_k`,
`M_{ε_n}(x, y) ≤ (1 + δ) D(x, y) + 2σ` and `D(x, y) ≤ (1 + δ) M_{ε_n}(x, y) + 2σ`. Inputs: the Borel–Cantelli form of
Proposition 5.1 at every integer `R ≥ 2` (`hcomp`), (6.3) of Lemma 6.1 (`hmod`), the `M_ε`-geodesics of Lemma 6.2 in
`B_{R₀}` (`hgeo`), and properness/escape of `D` (Lemma 2.2), which confines the `D`-geodesics. -/
theorem thm_seq_compare (hus : Core.UnitSpeedAdmissible d) {κ : Rd d → ℝ} {ξ : ℝ} {g : DistRd d}
    {G : ContMetric d} (hG : G.IsLength) [ProperSpace G.Space]
    (hesc : ∀ K : Set (Rd d), IsCompact K → ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ K, ∀ y : Rd d,
      R ≤ ‖y‖ → M < G.1 (x, y))
    {a q δ : ℝ} (ha : 0 < a) (hq : 0 < q) (hδ : 0 ≤ δ)
    (hcomp : ∀ R : ℕ, 2 ≤ R → ∀ᶠ n : ℕ in atTop,
      Core.Comp G (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g) R ((n : ℝ) ^ (-a)) q (1 + δ) ∧
        Core.Comp (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g) G R ((n : ℝ) ^ (-a)) q (1 + δ))
    (hmod : ∀ R : ℕ, 1 ≤ R → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
        ‖x - y‖ ≤ ρ n →
          (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g).internal (ball 0 (R + 2)) x y ≤ ENNReal.ofReal η)
    (k R₀ : ℕ)
    (hgeo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = x ∧ γ T = y ∧ ContinuousOn γ (Icc 0 T) ∧
        MapsTo γ (Icc 0 T) (ball 0 R₀) ∧
        ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, (Core.Meps κ ξ ε g).1 (γ s, γ t) = |t - s|)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g).1 (x, y) ≤ (1 + δ) * G.1 (x, y) + 2 * σ ∧
        G.1 (x, y) ≤ (1 + δ) * (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g).1 (x, y) + 2 * σ := by
  obtain ⟨RD, hRD⟩ := thm_exists_geodesic_confined G hG hesc k
  have hR₀R : (R₀ : ℝ) ≤ (max (max R₀ RD) 2 : ℕ) := by
    exact_mod_cast (le_max_left R₀ RD).trans (le_max_left _ 2)
  have hRDR : (RD : ℝ) ≤ (max (max R₀ RD) 2 : ℕ) := by
    exact_mod_cast (le_max_right R₀ RD).trans (le_max_left _ 2)
  obtain ⟨ρ₀, hρ₀, hmodG⟩ := thm_exists_modulus G ((k : ℝ) + 1) hσ
  have hρ := thm_tendsto_radius ha hq
  filter_upwards [hcomp _ (le_max_right _ 2), hρ.eventually (gt_mem_nhds (lt_min hρ₀ one_pos)),
    hmod (k + 1) (Nat.le_add_left 1 k) _ hρ σ hσ, (thm_tendsto_seq ha).eventually hgeo]
    with n hCn hρn hmodn hgeon
  intro x hx y hy
  -- points of `B̄_k` and their `ρ_n`-neighbours lie in `B̄_{k+1}` and are `min ρ₀ 1`-close
  have hnear : ∀ p ∈ closedBall (0 : Rd d) k, ∀ p' ∈ ball p (8 * ((n : ℝ) ^ (-a)) ^ q),
      p ∈ closedBall (0 : Rd d) ((k : ℝ) + 1) ∧ p' ∈ closedBall (0 : Rd d) ((k : ℝ) + 1) ∧
        ‖p - p'‖ < min ρ₀ 1 ∧ ‖p' - p‖ < min ρ₀ 1 := by
    intro p hp p' hp'
    rw [mem_closedBall_zero_iff] at hp
    rw [mem_ball, dist_eq_norm] at hp'
    have h1 : ‖p' - p‖ < min ρ₀ 1 := hp'.trans hρn
    have h2 : ‖p'‖ ≤ ‖p‖ + ‖p' - p‖ := by
      calc ‖p'‖ = ‖p + (p' - p)‖ := by rw [add_sub_cancel]
        _ ≤ ‖p‖ + ‖p' - p‖ := norm_add_le _ _
    refine ⟨mem_closedBall_zero_iff.2 (by linarith), mem_closedBall_zero_iff.2 ?_,
      by rwa [norm_sub_rev], h1⟩
    linarith [min_le_right ρ₀ 1]
  have hmodM : ∀ p ∈ closedBall (0 : Rd d) ((k : ℝ) + 1), ∀ p' ∈ closedBall (0 : Rd d) ((k : ℝ) + 1),
      ‖p - p'‖ < min ρ₀ 1 → ‖p - p'‖ ≤ 8 * ((n : ℝ) ^ (-a)) ^ q →
        (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g).1 (p, p') ≤ σ := by
    intro p hp p' hp' _ hpp'
    have hint := hmodn p (by exact_mod_cast hp) p' (by exact_mod_cast hp') hpp'
    exact (ENNReal.ofReal_le_ofReal_iff hσ.le).1 ((ContMetric.ofReal_le_internal _ _ p p').trans hint)
  have hδ1 : (0 : ℝ) ≤ 1 + δ := by linarith
  constructor
  · -- (6.8): the `D`-geodesic, `𝒞^{D → M}` and (6.3) at the endpoints
    obtain ⟨γ, T, hT, h0, h1, hc, hmaps, hu⟩ := hRD x hx y hy
    refine thm_le_of_comp hus G _ hδ1 hσ.le
      ⟨γ, T, hT, h0, h1, hc, hmaps.mono_right (ball_subset_ball hRDR), hu⟩ hCn.1 ?_ ?_
    · intro x' hx'
      obtain ⟨hxk, hx'k, hd, -⟩ := hnear x hx x' hx'
      refine hmodM x hxk x' hx'k hd ?_
      rw [← dist_eq_norm, dist_comm]
      exact (mem_ball.1 hx').le
    · intro y' hy'
      obtain ⟨hyk, hy'k, -, hd⟩ := hnear y hy y' hy'
      refine hmodM y' hy'k y hyk hd ?_
      rw [← dist_eq_norm]
      exact (mem_ball.1 hy').le
  · -- (6.9): the `M_{ε_n}`-geodesic of Lemma 6.2, `𝒞^{M → D}` and continuity of `D` at the endpoints
    obtain ⟨γ, T, hT, h0, h1, hc, hmaps, hu⟩ := hgeon x hx y hy
    refine thm_le_of_comp hus _ G hδ1 hσ.le
      ⟨γ, T, hT, h0, h1, hc, hmaps.mono_right (ball_subset_ball hR₀R), hu⟩ hCn.2 ?_ ?_
    · intro x' hx'
      obtain ⟨hxk, hx'k, hd, -⟩ := hnear x hx x' hx'
      exact (hmodG x hxk x' hx'k (hd.trans_le (min_le_left _ _))).le
    · intro y' hy'
      obtain ⟨hyk, hy'k, -, hd⟩ := hnear y hy y' hy'
      exact (hmodG y' hy'k y hyk (hd.trans_le (min_le_left _ _))).le

/-- **(6.10)** (MA2 §2.22): for every `s > 0`, eventually in `n`, for all `ε ∈ I_n = [(n+1)^{-a}, n^{-a}]` and
`x, y ∈ B̄_k`, `M_ε(x, y) ≤ e^s M_{ε_n}(x, y)` and `M_{ε_n}(x, y) ≤ e^s M_ε(x, y)`. Both global distances equal the
internal ones on `B_{R₀}` (Lemma 6.2, `hint`), where the log-density ratio
`log(𝔞_{ε_n}/𝔞_ε) + ξ(ĥ*_ε − ĥ*_{ε_n})` is small by (2.10) (`h25`) and Lemma 2.3 (iii) (`hosc`). -/
theorem thm_window_compare {κ : Rd d → ℝ} {ξ : ℝ} {g : DistRd d} (hξ : 0 < ξ)
    (hapos : ∀ ε : ℝ, 0 < ε → 0 < aEps κ ξ ε) (h25 : Core.Lemma25Window κ ξ)
    (hloc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Continuous (locField κ ε g))
    {a : ℝ} (ha : 0 < a)
    (hosc : ∀ R η : ℝ, 0 < R → 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)), ∀ x ∈ closedBall (0 : Rd d) R,
        |convMollify κ ε g x - convMollify κ δ g x| ≤ η ∧ |locField κ ε g x - locField κ δ g x| ≤ η)
    (k R₀ : ℕ) (hR₀ : 0 < R₀)
    (hint : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      ENNReal.ofReal ((Core.Meps κ ξ ε g).1 (x, y)) = (Core.Meps κ ξ ε g).internal (ball 0 R₀) x y)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
        (Core.Meps κ ξ ε g).1 (x, y) ≤ Real.exp s * (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g).1 (x, y) ∧
          (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g).1 (x, y) ≤ Real.exp s * (Core.Meps κ ξ ε g).1 (x, y) := by
  have hη₃ : 0 < min (1 / 2 : ℝ) (s / 4) := lt_min (by norm_num) (by linarith)
  filter_upwards [h25 a ha _ hη₃, hosc R₀ (s / (2 * ξ)) (by exact_mod_cast hR₀) (by positivity),
    thm_eventually_tiles_of_nhdsGT ha (hloc.and hint), eventually_ge_atTop 1]
    with n h25n hoscn hgoodn hn1
  intro ε hε x hx y hy
  have hεn := thm_seq_mem_tile ha hn1
  have ha1 := hapos ε (thm_pos_of_mem_tile hε)
  have ha2 := hapos _ (thm_pos_of_mem_tile hεn)
  have hlog : |Real.log (aEps κ ξ ε / aEps κ ξ ((n : ℝ) ^ (-a)))| ≤ s / 2 := by
    have := thm_abs_log_le (div_pos ha1 ha2) (min_le_left _ _) (h25n ε hε)
    linarith [min_le_right (1 / 2 : ℝ) (s / 4)]
  have hlog' : |Real.log (aEps κ ξ ((n : ℝ) ^ (-a)) / aEps κ ξ ε)| ≤ s / 2 := by
    rw [← inv_div, Real.log_inv, abs_neg]
    exact hlog
  have hoscz : ∀ z ∈ ball (0 : Rd d) R₀,
      ξ * |locField κ ε g z - locField κ ((n : ℝ) ^ (-a)) g z| ≤ s / 2 := by
    intro z hz
    have := (hoscn ε hε _ hεn z (ball_subset_closedBall hz)).2
    calc ξ * |locField κ ε g z - locField κ ((n : ℝ) ^ (-a)) g z| ≤ ξ * (s / (2 * ξ)) :=
          mul_le_mul_of_nonneg_left this hξ.le
      _ = s / 2 := by field_simp
  obtain ⟨hc1, hi1⟩ := hgoodn ε hε
  obtain ⟨hc2, hi2⟩ := hgoodn _ hεn
  constructor
  · refine thm_le_of_internal_le (Real.exp_pos s).le (hi1 x hx y hy) (hi2 x hx y hy) ?_
    refine thm_meps_internal_le κ isOpen_ball ha1 ha2 hc1 hc2 (fun z hz => ?_) x y
    calc _ ≤ |Real.log (aEps κ ξ ((n : ℝ) ^ (-a)) / aEps κ ξ ε)| +
          |ξ * (locField κ ε g z - locField κ ((n : ℝ) ^ (-a)) g z)| := abs_add_le _ _
      _ ≤ s / 2 + s / 2 := by
          rw [abs_mul, abs_of_pos hξ]
          exact add_le_add hlog' (hoscz z hz)
      _ = s := by ring
  · refine thm_le_of_internal_le (Real.exp_pos s).le (hi2 x hx y hy) (hi1 x hx y hy) ?_
    refine thm_meps_internal_le κ isOpen_ball ha2 ha1 hc2 hc1 (fun z hz => ?_) x y
    calc _ ≤ |Real.log (aEps κ ξ ε / aEps κ ξ ((n : ℝ) ^ (-a)))| +
          |ξ * (locField κ ((n : ℝ) ^ (-a)) g z - locField κ ε g z)| := abs_add_le _ _
      _ ≤ s / 2 + s / 2 := by
          rw [abs_mul, abs_of_pos hξ, abs_sub_comm]
          exact add_le_add hlog (hoscz z hz)
      _ = s := by ring

/-- **(6.11) and the intersection over `δ`** (MA2 §2.23, D-E): `sup_{x,y ∈ B̄_k} |M_ε(x, y) − D(x, y)| → 0` as `ε ↓ 0`,
along all `ε`. For each `j` the comparison parameter `δ_j`, the exponents `q_j` of Proposition 5.1 and the sequence
`ε_n = n^{-a_j}` give `limsup ≤ O(δ_j)` through (6.8)–(6.10); `δ_j → 0`. -/
theorem thm_meps_close (hus : Core.UnitSpeedAdmissible d) {κ : Rd d → ℝ} {ξ : ℝ} {g : DistRd d}
    {G : ContMetric d} (hξ : 0 < ξ) (hapos : ∀ ε : ℝ, 0 < ε → 0 < aEps κ ξ ε)
    (h25 : Core.Lemma25Window κ ξ) (hloc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Continuous (locField κ ε g))
    (hG : G.IsLength) [ProperSpace G.Space]
    (hesc : ∀ K : Set (Rd d), IsCompact K → ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ K, ∀ y : Rd d,
      R ≤ ‖y‖ → M < G.1 (x, y))
    {a q δ : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hq : ∀ j, 0 < q j) (hδ : ∀ j, 0 ≤ δ j)
    (hδlim : ∀ θ : ℝ, 0 < θ → ∃ j, δ j ≤ θ)
    (hcomp : ∀ j, ∀ R : ℕ, 2 ≤ R → ∀ᶠ n : ℕ in atTop,
      Core.Comp G (Core.Meps κ ξ ((n : ℝ) ^ (-a j)) g) R ((n : ℝ) ^ (-a j)) (q j) (1 + δ j) ∧
        Core.Comp (Core.Meps κ ξ ((n : ℝ) ^ (-a j)) g) G R ((n : ℝ) ^ (-a j)) (q j) (1 + δ j))
    (hmod : ∀ j, ∀ R : ℕ, 1 ≤ R → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
        ‖x - y‖ ≤ ρ n →
          (Core.Meps κ ξ ((n : ℝ) ^ (-a j)) g).internal (ball 0 (R + 2)) x y ≤ ENNReal.ofReal η)
    (hosc : ∀ j, ∀ R η : ℝ, 0 < R → 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a j)) ((n : ℝ) ^ (-a j)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a j)) ((n : ℝ) ^ (-a j)), ∀ x ∈ closedBall (0 : Rd d) R,
        |convMollify κ ε g x - convMollify κ δ g x| ≤ η ∧ |locField κ ε g x - locField κ δ g x| ≤ η)
    (k R₀ : ℕ) (hR₀ : 0 < R₀)
    (h62k : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      ENNReal.ofReal ((Core.Meps κ ξ ε g).1 (x, y)) = (Core.Meps κ ξ ε g).internal (ball 0 R₀) x y ∧
      ENNReal.ofReal ((Core.Neps κ ξ ε g).1 (x, y)) = (Core.Neps κ ξ ε g).internal (ball 0 R₀) x y ∧
      ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = x ∧ γ T = y ∧ ContinuousOn γ (Icc 0 T) ∧
        MapsTo γ (Icc 0 T) (ball 0 R₀) ∧
        ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, (Core.Meps κ ξ ε g).1 (γ s, γ t) = |t - s|) :
    ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ closedBall (0 : Rd d) k,
      ∀ y ∈ closedBall (0 : Rd d) k, |(Core.Meps κ ξ ε g).1 (x, y) - G.1 (x, y)| ≤ η := by
  intro η hη
  obtain ⟨Δ, hΔ0, hΔ⟩ := thm_exists_bound G k
  -- the parameters: `t` (comparison and window factors) and `σ` (endpoint errors)
  obtain ⟨t, ht0, ht1, htη⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ 12 * t * (Δ + 1) ≤ η / 2 := by
    refine ⟨min 1 (η / (24 * (Δ + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    have h1 : min 1 (η / (24 * (Δ + 1))) * (24 * (Δ + 1)) ≤ η :=
      (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    linarith
  obtain ⟨σ, hσ0, hσ1, hση⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 4 * σ ≤ η / 2 :=
    ⟨min 1 (η / 8), lt_min one_pos (by positivity), min_le_left _ _,
      by linarith [min_le_right (1 : ℝ) (η / 8)]⟩
  obtain ⟨j, hj⟩ := hδlim t ht0
  have hA := thm_seq_compare hus hG hesc (ha j) (hq j) (hδ j) (hcomp j) (hmod j) k R₀
    (h62k.mono fun ε h x hx y hy => (h x hx y hy).2.2) hσ0
  have hB := thm_window_compare hξ hapos h25 hloc (ha j) (hosc j) k R₀ hR₀
    (h62k.mono fun ε h x hx y hy => (h x hx y hy).1) (Real.log_pos (by linarith : (1 : ℝ) < 1 + t))
  rw [Real.exp_log (by linarith)] at hB
  apply thm_eventually_of_tiles (ha j)
  filter_upwards [hA, hB] with n hAn hBn ε hε x hx y hy
  obtain ⟨hA1, hA2⟩ := hAn x hx y hy
  obtain ⟨hB1, hB2⟩ := hBn ε hε x hx y hy
  have := thm_real_combine ht0.le ht1 (hδ j) hj hσ0.le hσ1 (G.nonneg x y) (hΔ x hx y hy)
    (ContMetric.nonneg _ x y) hA1 hA2 hB1 hB2
  linarith

/-- **The transfer to `N_ε`** (MA2 §2.24): both `M_ε` and `N_ε` have global = internal distances on `B_{R₀}` for pairs
in `B̄_k` (Lemma 6.2), and their densities differ by `e^{ξ(h*_ε − ĥ*_ε)}`, uniformly close to `1` on `B̄_{R₀}` by
Lemma 2.3 (i); hence `sup_{B̄_k²} |N_ε − D| → 0` follows from the same for `M_ε`. -/
theorem thm_neps_close {κ : Rd d → ℝ} {ξ : ℝ} {g : DistRd d} {G : ContMetric d} (hξ : 0 < ξ)
    (hapos : ∀ ε : ℝ, 0 < ε → 0 < aEps κ ξ ε)
    (hloc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Continuous (locField κ ε g))
    (hconv : ∀ ε : ℝ, 0 < ε → Continuous (convMollify κ ε g))
    (k R₀ : ℕ)
    (h23 : TendstoUniformlyOn (fun ε x => locField κ ε g x - convMollify κ ε g x) (fun _ => 0)
      (𝓝[>] (0 : ℝ)) (closedBall (0 : Rd d) R₀))
    (hint : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      ENNReal.ofReal ((Core.Meps κ ξ ε g).1 (x, y)) = (Core.Meps κ ξ ε g).internal (ball 0 R₀) x y ∧
      ENNReal.ofReal ((Core.Neps κ ξ ε g).1 (x, y)) = (Core.Neps κ ξ ε g).internal (ball 0 R₀) x y)
    (hM : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ closedBall (0 : Rd d) k,
      ∀ y ∈ closedBall (0 : Rd d) k, |(Core.Meps κ ξ ε g).1 (x, y) - G.1 (x, y)| ≤ η) :
    ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ closedBall (0 : Rd d) k,
      ∀ y ∈ closedBall (0 : Rd d) k, |(Core.Neps κ ξ ε g).1 (x, y) - G.1 (x, y)| ≤ η := by
  intro η hη
  obtain ⟨Δ, hΔ0, hΔ⟩ := thm_exists_bound G k
  obtain ⟨t, ht0, ht1, htη⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ 2 * t * (Δ + η) ≤ η / 2 := by
    refine ⟨min 1 (η / (4 * (Δ + η + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    have h1 : min 1 (η / (4 * (Δ + η + 1))) * (4 * (Δ + η + 1)) ≤ η :=
      (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith [lt_min one_pos (by positivity : (0 : ℝ) < η / (4 * (Δ + η + 1)))]
  have hlog : 0 < Real.log (1 + t) := Real.log_pos (by linarith)
  filter_upwards [hM (η / 2) (by linarith), hloc, hint,
    Metric.tendstoUniformlyOn_iff.1 h23 _ (div_pos hlog hξ), self_mem_nhdsWithin]
    with ε hMε hlocε hintε hunifε hε0
  intro x hx y hy
  have ha := hapos ε hε0
  have hc := hconv ε hε0
  have hb : ∀ z ∈ ball (0 : Rd d) R₀,
      |ξ * (locField κ ε g z - convMollify κ ε g z)| ≤ Real.log (1 + t) := by
    intro z hz
    have h1 := hunifε z (ball_subset_closedBall hz)
    rw [Real.dist_eq, zero_sub, abs_neg] at h1
    rw [abs_mul, abs_of_pos hξ]
    calc ξ * |locField κ ε g z - convMollify κ ε g z| ≤ ξ * (Real.log (1 + t) / ξ) :=
          mul_le_mul_of_nonneg_left h1.le hξ.le
      _ = Real.log (1 + t) := by field_simp
  have hb' : ∀ z ∈ ball (0 : Rd d) R₀,
      |ξ * (convMollify κ ε g z - locField κ ε g z)| ≤ Real.log (1 + t) := by
    intro z hz
    rw [← abs_neg, ← mul_neg, neg_sub]
    exact hb z hz
  obtain ⟨hiM, hiN⟩ := hintε x hx y hy
  have h1 := thm_le_of_internal_le (Real.exp_pos _).le hiN hiM
    (thm_neps_internal_le_meps κ isOpen_ball ha hc hlocε hb' x y)
  have h2 := thm_le_of_internal_le (Real.exp_pos _).le hiM hiN
    (thm_meps_internal_le_neps κ isOpen_ball ha hc hlocε hb x y)
  rw [Real.exp_log (by linarith)] at h1 h2
  exact thm_real_transfer ht0.le ht1 (ContMetric.nonneg _ x y) h1 h2 (hMε x hx y hy)
    (hΔ x hx y hy) htη

/-- **Compact sets and the `[0, ∞]`-supremum form** (S1 `explicit`, S0 `chk_explicit`): uniform convergence of `N_ε` to
`D` on every `B̄_k × B̄_k` gives the conclusion (1.7) of the frozen anchor for every compact `F`, with
`N_ε = 𝔞_ε⁻¹ D^ε_g` (`thm_neps_apply`). -/
theorem thm_tendsto_of_uniform {κ : Rd d → ℝ} {ξ : ℝ} {g : DistRd d} {G : ContMetric d}
    (hapos : ∀ ε : ℝ, 0 < ε → 0 < aEps κ ξ ε)
    (hconv : ∀ ε : ℝ, 0 < ε → Continuous (convMollify κ ε g))
    (hN : ∀ k : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ closedBall (0 : Rd d) k,
      ∀ y ∈ closedBall (0 : Rd d) k, |(Core.Neps κ ξ ε g).1 (x, y) - G.1 (x, y)| ≤ η) :
    ∀ F : Set (Rd d), IsCompact F →
      Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
          edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) p) (G.1 p)) (𝓝[>] 0) (𝓝 0) := by
  intro F hF
  obtain ⟨r, hr⟩ := hF.isBounded.subset_closedBall 0
  have hFk : F ⊆ closedBall (0 : Rd d) (⌈r⌉₊ : ℕ) :=
    hr.trans (closedBall_subset_closedBall (Nat.le_ceil r))
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨η, hη, hηe⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ e := by
    by_cases htop : e = ⊤
    · exact ⟨1, one_pos, htop ▸ le_top⟩
    · exact ⟨e.toReal, ENNReal.toReal_pos he.ne' htop, (ENNReal.ofReal_toReal htop).le⟩
  filter_upwards [hN ⌈r⌉₊ η hη, self_mem_nhdsWithin] with ε hε hε0
  refine iSup₂_le fun p hp => ?_
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hy⟩ := mem_prod.1 hp
  rw [← thm_neps_apply κ (hapos ε hε0) (hconv ε hε0), edist_dist, Real.dist_eq]
  exact (ENNReal.ofReal_le_ofReal (hε x (hFk hx) y (hFk hy))).trans hηe

/-- **The pathwise proof of (1.7)** for one sample `g = h(ω)`, `G = D_g`, from the `ω`-sections of the almost-sure
inputs (D-E): Proposition 5.1 through Borel–Cantelli (`hcomp`), (6.3) of Lemma 6.1 (`hmod`), Lemma 2.3 (iii) (`hosc`)
for the exponents `a_j`, Lemma 6.2 (`h62`), Lemma 2.3 (i) (`h23`), and Lemma 2.2 for `D` (`hG`, properness, `hesc`). -/
theorem thm_pathwise (hus : Core.UnitSpeedAdmissible d) {κ : Rd d → ℝ} {ξ : ℝ} {g : DistRd d}
    {G : ContMetric d} (hξ : 0 < ξ) (hapos : ∀ ε : ℝ, 0 < ε → 0 < aEps κ ξ ε)
    (h25 : Core.Lemma25Window κ ξ) (hloc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Continuous (locField κ ε g))
    (hconv : ∀ ε : ℝ, 0 < ε → Continuous (convMollify κ ε g))
    (hG : G.IsLength) [ProperSpace G.Space]
    (hesc : ∀ K : Set (Rd d), IsCompact K → ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ K, ∀ y : Rd d,
      R ≤ ‖y‖ → M < G.1 (x, y))
    {a q δ : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hq : ∀ j, 0 < q j) (hδ : ∀ j, 0 ≤ δ j)
    (hδlim : ∀ θ : ℝ, 0 < θ → ∃ j, δ j ≤ θ)
    (hcomp : ∀ j, ∀ R : ℕ, 2 ≤ R → ∀ᶠ n : ℕ in atTop,
      Core.Comp G (Core.Meps κ ξ ((n : ℝ) ^ (-a j)) g) R ((n : ℝ) ^ (-a j)) (q j) (1 + δ j) ∧
        Core.Comp (Core.Meps κ ξ ((n : ℝ) ^ (-a j)) g) G R ((n : ℝ) ^ (-a j)) (q j) (1 + δ j))
    (hmod : ∀ j, ∀ R : ℕ, 1 ≤ R → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
        ‖x - y‖ ≤ ρ n →
          (Core.Meps κ ξ ((n : ℝ) ^ (-a j)) g).internal (ball 0 (R + 2)) x y ≤ ENNReal.ofReal η)
    (hosc : ∀ j, ∀ R η : ℝ, 0 < R → 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a j)) ((n : ℝ) ^ (-a j)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a j)) ((n : ℝ) ^ (-a j)), ∀ x ∈ closedBall (0 : Rd d) R,
        |convMollify κ ε g x - convMollify κ δ g x| ≤ η ∧ |locField κ ε g x - locField κ δ g x| ≤ η)
    (h62 : ∀ k : ℕ, ∃ R : ℕ, (k : ℝ) + 4 < R ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
        ENNReal.ofReal ((Core.Meps κ ξ ε g).1 (x, y)) = (Core.Meps κ ξ ε g).internal (ball 0 R) x y ∧
        ENNReal.ofReal ((Core.Neps κ ξ ε g).1 (x, y)) = (Core.Neps κ ξ ε g).internal (ball 0 R) x y ∧
        ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = x ∧ γ T = y ∧ ContinuousOn γ (Icc 0 T) ∧
          MapsTo γ (Icc 0 T) (ball 0 R) ∧
          ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, (Core.Meps κ ξ ε g).1 (γ s, γ t) = |t - s|)
    (h23 : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun ε x => locField κ ε g x - convMollify κ ε g x) (fun _ => 0)
        (𝓝[>] (0 : ℝ)) (closedBall (0 : Rd d) R)) :
    ∀ F : Set (Rd d), IsCompact F →
      Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
          edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) p) (G.1 p)) (𝓝[>] 0) (𝓝 0) := by
  refine thm_tendsto_of_uniform hapos hconv fun k => ?_
  obtain ⟨R₀, hR₀k, h62k⟩ := h62 k
  have hR₀ : 0 < R₀ := by
    have : (0 : ℝ) < R₀ := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact_mod_cast this
  exact thm_neps_close hξ hapos hloc hconv k R₀ (h23 R₀ (by exact_mod_cast hR₀))
    (h62k.mono fun ε h x hx y hy => ⟨(h x hx y hy).1, (h x hx y hy).2.1⟩)
    (thm_meps_close hus hξ hapos h25 hloc hG hesc ha hq hδ hδlim hcomp hmod hosc k R₀ hR₀ h62k)

end HigherDimLFPPAS.Main
