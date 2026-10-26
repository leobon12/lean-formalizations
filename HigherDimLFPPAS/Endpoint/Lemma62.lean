import HigherDimLFPPAS.Endpoint.Lemma62Det
import HigherDimLFPPAS.Proper.Lemma22

/-!
# Lemma 6.2: confinement of minimizers along the full continuum (packet L62)

**Lemma 6.2** in the interface form `Core.Lemma62Stmt` consumed by the proof of Theorem 1.2 (MA2 §§2.19–2.20 and Details
D-D, with the corrections m5 and m6; paper l. 688–727): almost surely, for every `k`, some integer `R > k + 4` is such
that for every small `ε > 0` and all `x, y ∈ B̄_k` the global `M_ε`- and `N_ε`-distances equal the internal ones on `B_R`,
and a unit-speed `M_ε`-geodesic from `x` to `y` exists inside `B_R`.

Route (MA2 D-D, "Lemma 6.2 (proof with m5)"):
1. constants: `C₁, β₁` of Lemma 6.1 ((6.2)), `C₂, β₂` of Lemma 2.7 at `q = 1/2` (the reverse comparison (2.12)), and one
   integer exponent `a ≥ 2/β₁ + 2/β₂`, so that `a β₁ > 1` and `a β₂ > 1` (both Borel–Cantelli arguments run along the
   same sequence `ε_n = n^{-a}`);
2. the event (m5): Borel–Cantelli for (2.12) along `ε_n = n^{-a}` on `B_{R+1}` for **every** integer `R` (countable
   intersection, `ae_all_iff`), the Lemma 6.1 event at `a`, the Lemma 2.3 (iii) event at `a` and the Lemma 2.3 (i)
   event (both for all radii), Lemma 2.2 (escape of `D` from compact sets, D2), axiom (I) (length property of `D`) and
   the joint continuity of `h*_ε`;
3. the pathwise argument `l62_pathwise`: `T_k = C₁ max_{B̄_k²} D(·,·;B_{k+2}) + 1` (6.5), the integer `R > k + 4` with
   `D(B̄_{k+1}, ℝ^d ∖ B_{R−1}) > 4 C₂ T_k` (6.6), and for `n ≥ n₁`: (a) competitors `M_{ε_n}(x, y; B_{k+3}) ≤ T_k − 1/2`,
   (b) exits `M_{ε_n}(x, y; B_{R+1}) ≥ 4 T_k` for `y ∈ S_R`, (c) the log density ratios of `M_ε`, `N_ε` against
   `M_{ε_n}` on `B_{R+1}` are at most `log 2` for every `ε ∈ I_n = [(n+1)^{-a}, n^{-a}]` ((6.7) by Lemma 2.3 (iii) with
   `δ = ε_n`, (2.10), and Lemma 2.3 (i) for `h*_ε` vs `ĥ*_ε`); then the deterministic lemmas of `Lemma62Det` (D-D2, D-D3)
   give the conclusion for every `ε ∈ I_n`, and the `I_n` tile `(0, n₁^{-a}]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Endpoint

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- **Lemma 6.2, the pathwise argument** (MA2 D-D, for one sample `g = h(ω)` with `G = D_g` on the probability-one event
of the proof): `G` is a length metric whose distances escape uniformly from compact sets (Lemma 2.2), `𝔞_ε > 0`, the
fields `ĥ*_ε` (small `ε`) and `h*_ε` (all `ε > 0`) are continuous, (2.10) and Lemma 2.3 (iii) hold along `I_n`, Lemma 2.3 (i)
holds on every ball, and along `ε_n = n^{-a}` the forward comparison (6.2) of Lemma 6.1 and the reverse comparison (2.12)
of Lemma 2.7 hold eventually at every integer radius. Then for every `k` some integer `R > k + 4` confines, for every small
`ε`, the `M_ε`- and `N_ε`-minimizers between points of `B̄_k`, and unit-speed `M_ε`-geodesics exist inside `B_R`. -/
theorem l62_pathwise {κ : Rd d → ℝ} {ξ : ℝ} {g : DistRd d} {G : ContMetric d}
    (hξ : 0 < ξ) (hG : G.IsLength)
    (hesc : ∀ K : Set (Rd d), IsCompact K → ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ K, ∀ y : Rd d,
      R ≤ ‖y‖ → M < G.1 (x, y))
    (haE : ∀ ε : ℝ, 0 < ε → 0 < aEps κ ξ ε)
    (hlocC : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Continuous (locField κ ε g))
    (hconvC : ∀ ε : ℝ, 0 < ε → Continuous (convMollify κ ε g))
    {a : ℝ} (ha : 0 < a)
    (hwin : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
        |aEps κ ξ ε / aEps κ ξ ((n : ℝ) ^ (-a)) - 1| ≤ η)
    (hosc : ∀ R η : ℝ, 0 < R → 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ x ∈ closedBall (0 : Rd d) R,
        |convMollify κ ε g x - convMollify κ δ g x| ≤ η ∧
          |locField κ ε g x - locField κ δ g x| ≤ η)
    (hloc : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun ε x => locField κ ε g x - convMollify κ ε g x) (fun _ => 0)
        (𝓝[>] (0 : ℝ)) (closedBall (0 : Rd d) R))
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (h62 : ∀ R : ℕ, 1 ≤ R → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
        (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g).internal (ball 0 (R + 2)) x y ≤
          ENNReal.ofReal C₁ * G.internal (ball 0 (R + 1)) x y + ENNReal.ofReal η)
    {C₂ q : ℝ} (hC₂ : 0 < C₂) (hq : 0 < q)
    (h212 : ∀ R : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ x ∈ ball (0 : Rd d) ((R : ℝ) + 1), ∀ y ∈ ball (0 : Rd d) ((R : ℝ) + 1),
        setDistIn G (thickening (((n : ℝ) ^ (-a)) ^ q) (ball 0 ((R : ℝ) + 1)))
            (ball x (((n : ℝ) ^ (-a)) ^ q)) (ball y (((n : ℝ) ^ (-a)) ^ q)) ≤
          ENNReal.ofReal C₂ *
            (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g).internal (ball 0 ((R : ℝ) + 1)) x y)
    (k : ℕ) :
    ∃ R : ℕ, (k : ℝ) + 4 < R ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
        ENNReal.ofReal ((Core.Meps κ ξ ε g).1 (x, y)) = (Core.Meps κ ξ ε g).internal (ball 0 R) x y ∧
        ENNReal.ofReal ((Core.Neps κ ξ ε g).1 (x, y)) = (Core.Neps κ ξ ε g).internal (ball 0 R) x y ∧
        ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = x ∧ γ T = y ∧ ContinuousOn γ (Icc 0 T) ∧
          MapsTo γ (Icc 0 T) (ball 0 R) ∧
          ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, (Core.Meps κ ξ ε g).1 (γ s, γ t) = |t - s| := by
  -- the competitor bound `T_k` of (6.5)
  obtain ⟨Δ, hΔ0, hΔ⟩ := l62_exists_internal_bound G hG (Nat.cast_nonneg (α := ℝ) k)
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = C₁ * Δ + 1 := ⟨_, rfl⟩
  have hT : 1 ≤ T := by
    have := mul_nonneg hC₁.le hΔ0
    linarith
  -- the integer radius `R` of (6.6)
  obtain ⟨R₁, hR₁⟩ := hesc (closedBall (0 : Rd d) ((k : ℝ) + 1)) (isCompact_closedBall _ _)
    (C₂ * (4 * T))
  obtain ⟨R, hR5, hRc⟩ : ∃ R : ℕ, k + 5 ≤ R ∧ ⌈R₁⌉₊ + 1 ≤ R :=
    ⟨max (k + 5) (⌈R₁⌉₊ + 1), le_max_left _ _, le_max_right _ _⟩
  have hkR : (k : ℝ) + 4 < R := by
    have h1 : ((k + 5 : ℕ) : ℝ) ≤ R := by exact_mod_cast hR5
    push_cast at h1
    linarith
  have hR₁R : R₁ ≤ (R : ℝ) - 1 := by
    have h1 : ((⌈R₁⌉₊ + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hRc
    push_cast at h1
    linarith [Nat.le_ceil R₁]
  refine ⟨R, hkR, Main.thm_eventually_of_tiles ha ?_⟩
  -- the tolerance `θ = (log 2)/3` for the three parts of the log density ratio (6.7)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = Real.log 2 / 3 := ⟨_, rfl⟩
  have hθ : 0 < θ := by
    rw [hθdef]
    positivity
  obtain ⟨η₁, hη₁def⟩ : ∃ η₁ : ℝ, η₁ = min (1 / 2) (θ / 2) := ⟨_, rfl⟩
  have hη₁ : 0 < η₁ := by
    rw [hη₁def]
    exact lt_min (by norm_num) (by positivity)
  have hη₁h : η₁ ≤ 1 / 2 := by
    rw [hη₁def]
    exact min_le_left _ _
  have hη₁θ : 2 * η₁ ≤ θ := by
    have := min_le_right (1 / 2 : ℝ) (θ / 2)
    rw [← hη₁def] at this
    linarith
  have hRpos : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  -- Lemma 2.3 (i) on `B̄_{R+1}` with tolerance `θ/ξ`
  have hloc' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ closedBall (0 : Rd d) ((R : ℝ) + 1),
      |locField κ ε g z - convMollify κ ε g z| ≤ θ / ξ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hloc _ hRpos) (θ / ξ) (by positivity)]
      with ε hε z hz
    have h := hε z hz
    rw [dist_comm, Real.dist_eq, sub_zero] at h
    exact h.le
  filter_upwards [h62 (k + 1) (by omega) (1 / 2) (by norm_num), h212 R, hwin η₁ hη₁,
    hosc ((R : ℝ) + 1) (θ / ξ) hRpos (by positivity), Main.thm_eventually_tiles_of_nhdsGT ha hloc',
    Main.thm_eventually_tiles_of_nhdsGT ha hlocC, eventually_ge_atTop 2]
    with n hA hB hW hO hL hC hn2
  intro ε hε x hx y hy
  -- the scale `ε_n = n^{-a}` lies in `I_n`
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hεn : (n : ℝ) ^ (-a) ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)) :=
    Main.thm_seq_mem_tile ha hn1
  have hεnpos : 0 < (n : ℝ) ^ (-a) := Main.thm_pos_of_mem_tile hεn
  have hεpos : 0 < ε := Main.thm_pos_of_mem_tile hε
  have haε := haE ε hεpos
  have haεn := haE _ hεnpos
  -- the endpoint balls of (2.12) have radius `< 1`
  have hr1 : ((n : ℝ) ^ (-a)) ^ q < 1 := by
    have h1 : (n : ℝ) ^ (-a) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn2) (by linarith)
    exact Real.rpow_lt_one hεnpos.le h1 hq
  -- (a) the competitor bound
  have hcomp : ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      (Core.Meps κ ξ ((n : ℝ) ^ (-a)) g).internal (ball 0 ((k : ℝ) + 3)) x y ≤
        ENNReal.ofReal (T - 1 / 2) := by
    rw [show T - 1 / 2 = C₁ * Δ + 1 / 2 by rw [hTdef]; ring]
    exact l62_comp_of_lemma61 hC₁ hΔ0 hΔ hA
  -- (b) the exit bound
  have hexit := l62_exit_of_reverse hC₂ hr1 hkR hR₁ hR₁R hB
  -- (c) the log density ratios of `M_ε` and `N_ε` against `M_{ε_n}` on `B_{R+1}`
  have hb : ∀ z ∈ ball (0 : Rd d) ((R : ℝ) + 1),
      |Real.log (aEps κ ξ ((n : ℝ) ^ (-a)) / aEps κ ξ ε) +
          ξ * (locField κ ε g z - locField κ ((n : ℝ) ^ (-a)) g z)| ≤ Real.log 2 ∧
        |Real.log (aEps κ ξ ((n : ℝ) ^ (-a)) / aEps κ ξ ε) +
          ξ * (convMollify κ ε g z - locField κ ((n : ℝ) ^ (-a)) g z)| ≤ Real.log 2 := by
    intro z hz
    have hz' := ball_subset_closedBall hz
    have hlogb := l62_log_ratio_bound haε haεn hη₁h (hW ε hε)
    obtain ⟨h1, h2⟩ := l62_density_bound hξ (hlogb.trans hη₁θ) (hO ε hε _ hεn z hz').2
      (hL ε hε z hz')
    have e : convMollify κ ε g z - locField κ ((n : ℝ) ^ (-a)) g z =
        (locField κ ε g z - locField κ ((n : ℝ) ^ (-a)) g z) -
          (locField κ ε g z - convMollify κ ε g z) := by ring
    rw [e]
    constructor <;> linarith
  have hcmp := l62_window_compare κ isOpen_ball haε haεn (hC ε hε) (hC _ hεn) (hconvC ε hεpos)
    (fun z hz => (hb z hz).1) (fun z hz => (hb z hz).2)
  -- the conclusion for `M_ε` and `N_ε` (D-D2, D-D3)
  have hlenM : (Core.Meps κ ξ ε g).IsLength := by
    rw [Main.thm_meps_eq κ g haε]
    exact ContMetric.isLength_smul _ (fieldLfppMetric_isLength ξ _)
  have hlenN : (Core.Neps κ ξ ε g).IsLength := by
    rw [Main.thm_neps_eq κ g haε]
    exact ContMetric.isLength_smul _ (fieldLfppMetric_isLength ξ _)
  exact ⟨l62_global_eq_internal hlenM hkR hT (fun x y => (hcmp x y).1) (fun x y => (hcmp x y).2.1)
      hcomp hexit hx hy,
    l62_global_eq_internal hlenN hkR hT (fun x y => (hcmp x y).2.2.1)
      (fun x y => (hcmp x y).2.2.2) hcomp hexit hx hy,
    l62_exists_geodesic hξ (inv_pos.2 haε) (Main.thm_meps_eq κ g haε) hkR hT
      (fun x y => (hcmp x y).1) (fun x y => (hcmp x y).2.1) hcomp hexit hx hy⟩

/-- **Lemma 6.2** (MA2 §§2.19–2.20, D-D2, D-D3; m5, m6), the interface `Core.Lemma62Stmt`: under the standing hypotheses
and the interface statements of Lemmas 6.1, 2.7, 2.3 (i), (iii) and (2.10), almost surely, for every `k`, some integer
`R > k + 4` is such that for every small `ε`, for all `x, y ∈ B̄_k`, the global `M_ε`- and `N_ε`-distances equal the
internal ones on `B_R`, and a unit-speed `M_ε`-geodesic from `x` to `y` exists inside `B_R`. -/
theorem lemma62_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (h61 : Core.Lemma61Stmt κ ξ D P h)
    (h27 : Core.Lemma27Stmt κ ξ D P h) (h23i : Core.Lemma23i κ P h) (h23iii : Core.Lemma23iii κ P h)
    (h25 : Core.Lemma25Window κ ξ) : Core.Lemma62Stmt κ ξ P h := by
  -- the constants of Lemma 6.1 and of Lemma 2.7 at `q = 1/2`, and the exponent `a`
  obtain ⟨C₁, β₁, hC₁, hβ₁, h61'⟩ := h61
  obtain ⟨C₂, β₂, hC₂, hβ₂, h27'⟩ := h27 (1 / 2) ⟨by norm_num, by norm_num⟩
  -- one integer exponent `a ≥ 2/β₁ + 2/β₂`, so that `a β₁ > 1` and `a β₂ > 1`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 / β₁ + 2 / β₂ ≤ (m : ℝ) := ⟨_, Nat.le_ceil _⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (m : ℝ) := ⟨_, rfl⟩
  have hma : 2 / β₁ + 2 / β₂ ≤ a := hadef ▸ hm
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hma
  have ha1 : 1 < a * β₁ := by
    have h1 : (2 / β₁ + 2 / β₂) * β₁ = 2 + 2 / β₂ * β₁ := by
      rw [add_mul, div_mul_cancel₀ _ hβ₁.ne']
    have h2 : 0 < 2 / β₂ * β₁ := by positivity
    have h3 := mul_le_mul_of_nonneg_right hma hβ₁.le
    linarith
  have ha2 : 1 < a * β₂ := by
    have h1 : (2 / β₁ + 2 / β₂) * β₂ = 2 / β₁ * β₂ + 2 := by
      rw [add_mul, div_mul_cancel₀ _ hβ₂.ne']
    have h2 : 0 < 2 / β₁ * β₂ := by positivity
    have h3 := mul_le_mul_of_nonneg_right hma hβ₂.le
    linarith
  -- (m5) Borel–Cantelli for the reverse comparison (2.12) on `B_{R+1}`, for every integer `R`
  have hBC : ∀ᵐ ω ∂P, ∀ R : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ x ∈ ball (0 : Rd d) ((R : ℝ) + 1), ∀ y ∈ ball (0 : Rd d) ((R : ℝ) + 1),
        setDistIn (D (h ω)) (thickening (((n : ℝ) ^ (-a)) ^ (1 / 2 : ℝ)) (ball 0 ((R : ℝ) + 1)))
            (ball x (((n : ℝ) ^ (-a)) ^ (1 / 2 : ℝ))) (ball y (((n : ℝ) ^ (-a)) ^ (1 / 2 : ℝ))) ≤
          ENNReal.ofReal C₂ *
            (Core.Meps κ ξ ((n : ℝ) ^ (-a)) (h ω)).internal (ball 0 ((R : ℝ) + 1)) x y := by
    refine ae_all_iff.2 fun R => ?_
    obtain ⟨K, ε₀, hε₀, hbound⟩ := h27' ((R : ℝ) + 1) (by positivity)
    filter_upwards [Main.thm_ae_eventually_of_rate ha ha2 hε₀ hbound] with ω hω
    filter_upwards [hω] with n hn x hx y hy
    simp only [not_not] at hn
    exact (hn x hx y hy).2
  -- Lemma 2.2, axiom (I) and the joint continuity of `h*_ε`
  have hD2 := lemma22_ae_proper_and_geodesic hS.dim hS.xi_pos hS.subcrit P h hS.field D hS.strong
  have hlen := hS.strong.length P h hS.field.1.isLGFPlusCont
  have hjc := hS.seed.jointCont P h hS.field
  filter_upwards [hBC, h61' a ha1, h23iii a ha, h23i, hD2, hlen, hjc]
    with ω hBCω h61ω h23ω h23iω hD2ω hlenω hjcω
  intro k
  have hconv : ∀ ε : ℝ, 0 < ε → Continuous (convMollify κ ε (h ω)) := fun ε hε =>
    (hjcω.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hε, mem_univ x⟩).congr
      fun _ => rfl
  have hlocC : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Continuous (locField κ ε (h ω)) :=
    hS.seed.locHyp.mono fun ε hε => continuous_locField hS.seed.kernelSmooth hε.2.2.1 (h ω)
  exact l62_pathwise hS.xi_pos hlenω hD2ω.2.1 (fun ε hε => hS.seed.aEps_pos ξ ε hε) hlocC hconv ha
    (h25 a ha) h23ω h23iω hC₁ (fun R hR η hη => (h61ω R hR).1 η hη) (by linarith)
    (by norm_num : (0 : ℝ) < 1 / 2) hBCω k

end HigherDimLFPPAS.Endpoint
