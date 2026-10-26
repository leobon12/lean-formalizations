import HigherDimLFPPAS.Annulus.MarginalRealize
import HigherDimLFPPAS.Det.MetricComparison
import HigherDimLFPPAS.Det.SmallPairs
import HigherDimLFPPAS.Det.InternalBasic
import HigherDimLQGMetric.Config.Geometry
import HigherDimLQGMetric.Thm13.ProbSubseq

/-!
# Lemma 3.2, marginal part — Step 3: the pinned field (packet L32p)

Source: `planning/audits/MA1-sections-1-3.md` Details A10.4–A10.6 and the conclusion of A10; MA4 §2.2.

On the pinned field `h`, along any sequence `(ε_j, r_j)` with `ε_j ≤ r_j ≤ 1`, `ε_j → 0`, `ε_j / r_j → 0`, the rescaled
metrics `𝔐_j = 𝔐_{ε_j,ε_j/r_j}(h)` converge to `D_h` in probability locally uniformly (`Core.RescaledConv`), hence almost
surely along a subsequence. Lemma 2.1 (packet D1) then gives, pathwise and eventually: (i′) from the multiplicative
comparison on `F = Ā_{1/2,3/2} ⊂ Ũ = A_{1/4,2}`; (ii′) from the same comparison with `η′ = 1` and the triangle inequality
through the antipode, against the internal diameter of `S_{3/4}` in `V = A_{1/2,3/2}` (`l32pGoodD`); (iii′) from the
small-pair modulus and the positive crossing lower bounds.

Deviations from MA1 A10.5 (both harmless): the diameter is taken in `V = A_{1/2,3/2}` rather than `A_{0.6,1.5}`, and no
reverse Fatou or measurability is needed: the eventual pathwise statement is turned into a probability bound by
continuity from below of the outer measure (`Monotone.measure_iUnion`). `A` is chosen from the law of `D_h` only
(`l32p_choose_A`), before `η, u, q₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Annulus

open HigherDimLFPPAS.Core HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The `D`-only event that fixes `A` -/

/-- The `D`-only good event (MA1 A10.5, with `V = A_{1/2,3/2}`): a positive lower bound `δ₀` for `D` on
`S_{3/4} × S_1`, and the internal diameter bound `D(x, y; V) ≤ A δ₀ / 8` on `S_{3/4}`. -/
def l32pGoodD (G : ContMetric d) (A : ℝ) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧
    (∀ x ∈ sphere (0 : Rd d) (3 / 4), ∀ y ∈ sphere (0 : Rd d) 1, δ₀ ≤ G.1 (x, y)) ∧
    ∀ x ∈ sphere (0 : Rd d) (3 / 4), ∀ y ∈ sphere (0 : Rd d) (3 / 4),
      G.internal (ann 0 (1 / 2) (3 / 2)) x y ≤ ENNReal.ofReal (A * δ₀ / 8)

theorem l32p_goodD_mono {G : ContMetric d} {A A' : ℝ} (hAA : A ≤ A') (h : l32pGoodD G A) :
    l32pGoodD G A' := by
  obtain ⟨δ₀, hδ₀, h1, h2⟩ := h
  refine ⟨δ₀, hδ₀, h1, fun x hx y hy => (h2 x hx y hy).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have := mul_le_mul_of_nonneg_right hAA hδ₀.le
  linarith

/-- Every length metric satisfies `l32pGoodD` for some integer `A` (`d ≥ 2`: `V` is connected, so the internal
diameter of the compact sphere `S_{3/4} ⊂ V` is finite; `D > 0` on the compact `S_{3/4} × S_1`). -/
theorem l32p_exists_goodD (hd : 2 ≤ d) {G : ContMetric d} (hG : G.IsLength) :
    ∃ n : ℕ, l32pGoodD G n := by
  have hd0 : 0 < d := by omega
  have he : ‖HigherDimLFPP.e₁ d‖ = 1 := HigherDimLFPP.norm_e₁ hd0
  have hK : IsCompact (sphere (0 : Rd d) (3 / 4) ×ˢ sphere (0 : Rd d) 1) :=
    (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hne : (sphere (0 : Rd d) (3 / 4) ×ˢ sphere (0 : Rd d) 1).Nonempty :=
    ⟨((3 / 4 : ℝ) • HigherDimLFPP.e₁ d, HigherDimLFPP.e₁ d),
      by rw [mem_sphere_zero_iff_norm, norm_smul, he]; norm_num,
      by rw [mem_sphere_zero_iff_norm, he]⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne (G.continuous_apply.continuousOn)
  have hp₀ne : p₀.1 ≠ p₀.2 := by
    intro heq
    have h1 : ‖p₀.1‖ = 3 / 4 := mem_sphere_zero_iff_norm.1 hp₀.1
    have h2 : ‖p₀.2‖ = 1 := mem_sphere_zero_iff_norm.1 hp₀.2
    rw [heq] at h1
    rw [h1] at h2
    norm_num at h2
  have hδ₀ : 0 < G.1 (p₀.1, p₀.2) := G.apply_pos hp₀ne
  have hSiV : sphere (0 : Rd d) (3 / 4) ⊆ ann 0 (1 / 2) (3 / 2) :=
    l32p_sphere_subset_ann (by norm_num) (by norm_num)
  obtain ⟨hfin, hcont⟩ := Det.internal_finite_continuous G hG (isOpen_ann (0 : Rd d) (1 / 2) (3 / 2))
    (config_isConnected_ann hd 0 (by norm_num) (by norm_num))
  have hKI : IsCompact (sphere (0 : Rd d) (3 / 4) ×ˢ sphere (0 : Rd d) (3 / 4)) :=
    (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  obtain ⟨C, hC⟩ := hKI.exists_bound_of_continuousOn (hcont.mono (prod_mono hSiV hSiV))
  obtain ⟨n, hn⟩ := exists_nat_ge (8 * C / G.1 (p₀.1, p₀.2))
  refine ⟨n, G.1 (p₀.1, p₀.2), hδ₀, fun x hx y hy => isMinOn_iff.1 hmin (x, y) ⟨hx, hy⟩,
    fun x hx y hy => ?_⟩
  rw [← ENNReal.ofReal_toReal (hfin x (hSiV hx) y (hSiV hy))]
  apply ENNReal.ofReal_le_ofReal
  have h1 := hC (x, y) ⟨hx, hy⟩
  rw [Real.norm_eq_abs] at h1
  have h2 : (G.internal (ann 0 (1 / 2) (3 / 2)) x y).toReal ≤ C := (le_abs_self _).trans h1
  have h3 : 8 * C ≤ n * G.1 (p₀.1, p₀.2) := by rwa [div_le_iff₀ hδ₀] at hn
  linarith

/-! ### The pathwise core (deterministic) -/

/-- **The pathwise core of A10.4–A10.6** (deterministic): if length metrics `Gₙ → G` locally uniformly, `G` is a length
metric with `l32pGoodD G A` (`A ≥ 0`) and `bₙ → 0`, then eventually `Ẽ(G, Gₙ; A, η, bₙ)`. -/
theorem l32p_eventually_unitGood (hd : 2 ≤ d) {Gn : ℕ → ContMetric d} {G : ContMetric d}
    (hGn : ∀ n, (Gn n).IsLength) (hG : G.IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Gn n).1) ⇑G.1 atTop
      (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R))
    {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0)) {A η : ℝ} (hA : 0 ≤ A) (hη : 0 < η)
    (hgood : l32pGoodD G A) :
    ∀ᶠ n in atTop, l32pUnitGood G (Gn n) A η (b n) := by
  obtain ⟨δ₀, hδ₀, hlow, hdiam⟩ := hgood
  have hAδ : 0 ≤ A * δ₀ := mul_nonneg hA hδ₀.le
  have hηδ : 0 ≤ η * δ₀ := mul_nonneg hη.le hδ₀.le
  have hUo : IsOpen (ann (0 : Rd d) (1 / 4) 2) := isOpen_ann _ _ _
  have hUc : IsConnected (ann (0 : Rd d) (1 / 4) 2) :=
    config_isConnected_ann hd 0 (by norm_num) (by norm_num)
  have hFc : IsCompact (annCl (0 : Rd d) (1 / 2) (3 / 2)) := by
    refine isCompact_of_isClosed_isBounded (isClosed_annCl _ _ _) ?_
    refine (isBounded_closedBall (x := (0 : Rd d)) (r := 3 / 2)).subset fun x hx => ?_
    rw [l32p_mem_annCl_zero] at hx
    rw [mem_closedBall, dist_zero_right]
    exact hx.2
  have hFU : annCl (0 : Rd d) (1 / 2) (3 / 2) ⊆ ann 0 (1 / 4) 2 :=
    l32p_annCl_subset_ann (by norm_num) (by norm_num)
  have hVF : ann (0 : Rd d) (1 / 2) (3 / 2) ⊆ annCl 0 (1 / 2) (3 / 2) := by
    intro x hx
    rw [l32p_mem_ann_zero] at hx
    rw [l32p_mem_annCl_zero]
    exact ⟨hx.1.le, hx.2.le⟩
  have hVU : ann (0 : Rd d) (1 / 2) (3 / 2) ⊆ ann 0 (1 / 4) 2 := hVF.trans hFU
  have hSiV : sphere (0 : Rd d) (3 / 4) ⊆ ann 0 (1 / 2) (3 / 2) :=
    l32p_sphere_subset_ann (by norm_num) (by norm_num)
  have hSoV : sphere (0 : Rd d) 1 ⊆ ann 0 (1 / 2) (3 / 2) :=
    l32p_sphere_subset_ann (by norm_num) (by norm_num)
  have hSiF := hSiV.trans hVF
  have hSoF := hSoV.trans hVF
  have hAnnF : annCl (0 : Rd d) (3 / 4) 1 ⊆ annCl 0 (1 / 2) (3 / 2) := by
    intro x hx
    rw [l32p_mem_annCl_zero] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hconvG : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun _ : ℕ => ⇑G.1) ⇑G.1 atTop
      (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
    intro R _
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with n x _
    simp only [dist_self]
    exact hε
  obtain ⟨N1, hN1⟩ := Det.eventually_internal_multiplicative_comparison Gn G hGn hG hconv hUo hUc
    hFc hFU (a := 1 / 4) (η := η) (by norm_num) hη
  obtain ⟨N2, hN2⟩ := Det.eventually_internal_multiplicative_comparison Gn G hGn hG hconv hUo hUc
    hFc hFU (a := 1 / 4) (η := 1) (by norm_num) one_pos
  obtain ⟨N3, hN3⟩ := Det.eventually_uniform_metric_error_on_compact Gn G hconv
    (isCompact_closedBall (0 : Rd d) 1) (half_pos hδ₀)
  obtain ⟨N4, hN4⟩ := Det.internal_small_pair_tendsto Gn G hGn hconv hUo hFc hFU b hb
    (η * δ₀ / 2) (by positivity)
  obtain ⟨N5, hN5⟩ := Det.internal_small_pair_tendsto (fun _ => G) G (fun _ => hG) hconvG hUo
    hFc hFU b hb (η * δ₀ / 2) (by positivity)
  obtain ⟨N6, hN6⟩ :=
    eventually_atTop.1 (hb.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  refine eventually_atTop.2 ⟨max (max (max N1 N2) (max N3 N4)) (max N5 N6), fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) hn
  have hn4 : N4 ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _)) hn
  have hn5 : N5 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn6 : N6 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  -- positive lower bounds for the crossing distances
  have hsdG : ENNReal.ofReal δ₀ ≤
      setDistIn G (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1) := by
    unfold setDistIn
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    exact (ENNReal.ofReal_le_ofReal (hlow x hx y hy)).trans (G.ofReal_le_internal _ x y)
  have hsdGn : ENNReal.ofReal (δ₀ / 2) ≤
      setDistIn (Gn n) (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1) := by
    unfold setDistIn
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) ((Gn n).ofReal_le_internal _ x y)
    have hx1 : x ∈ closedBall (0 : Rd d) 1 := by
      rw [mem_closedBall, dist_zero_right, mem_sphere_zero_iff_norm.1 hx]; norm_num
    have hy1 : y ∈ closedBall (0 : Rd d) 1 := by
      rw [mem_closedBall, dist_zero_right, mem_sphere_zero_iff_norm.1 hy]
    have h := (abs_lt.1 (hN3 n hn3 x hx1 y hy1)).1
    linarith [hlow x hx y hy]
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun x hx w hw => ?_⟩
  · -- (i′): Lemma 2.1, multiplicative comparison with `η`
    have hdist : 1 / 4 ≤ dist x y := by
      rw [dist_eq_norm]
      have h1 := norm_sub_norm_le y x
      rw [mem_sphere_zero_iff_norm.1 hy, mem_sphere_zero_iff_norm.1 hx, norm_sub_rev] at h1
      linarith
    obtain ⟨k1, k2⟩ := hN1 n hn1 x (hSiF hx) y (hSoF hy) hdist
    exact ⟨k1.trans (mul_le_mul_right (G.internal_anti hVF x y) _),
      k2.trans (mul_le_mul_right ((Gn n).internal_anti hVF x y) _)⟩
  · -- (ii′): the diameter bound of `l32pGoodD`; for `Gₙ`, comparison with `η′ = 1` and the antipode
    have hdiamGn : ∀ x' ∈ sphere (0 : Rd d) (3 / 4), ∀ y' ∈ sphere (0 : Rd d) (3 / 4),
        1 / 4 ≤ dist x' y' →
          (Gn n).internal (ann 0 (1 / 4) 2) x' y' ≤ ENNReal.ofReal (A * δ₀ / 4) := by
      intro x' hx' y' hy' hd'
      have k := (hN2 n hn2 x' (hSiF hx') y' (hSiF hy') hd').1
      calc (Gn n).internal (ann 0 (1 / 4) 2) x' y'
          ≤ ENNReal.ofReal (1 + 1) * G.internal (annCl 0 (1 / 2) (3 / 2)) x' y' := k
        _ ≤ ENNReal.ofReal (1 + 1) * ENNReal.ofReal (A * δ₀ / 8) :=
            mul_le_mul_right ((G.internal_anti hVF x' y').trans (hdiam x' hx' y' hy')) _
        _ = ENNReal.ofReal (A * δ₀ / 4) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
    have hM : (Gn n).internal (ann 0 (1 / 4) 2) x y ≤ ENNReal.ofReal (A * δ₀ / 2) := by
      by_cases hxy : 1 / 4 ≤ dist x y
      · exact (hdiamGn x hx y hy hxy).trans (ENNReal.ofReal_le_ofReal (by linarith))
      · push Not at hxy
        have hxn : ‖x‖ = 3 / 4 := mem_sphere_zero_iff_norm.1 hx
        have hnx : -x ∈ sphere (0 : Rd d) (3 / 4) := by
          rw [mem_sphere_zero_iff_norm, norm_neg]; exact hxn
        have hxnx : 1 / 4 ≤ dist x (-x) := by
          rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul, hxn, Real.norm_eq_abs]
          norm_num
        have hnxy : 1 / 4 ≤ dist (-x) y := by
          rw [dist_eq_norm]
          have h2 : ‖(2 : ℝ) • x‖ ≤ ‖-x - y‖ + ‖x - y‖ := by
            calc ‖(2 : ℝ) • x‖ = ‖-(-x - y) + (x - y)‖ := by congr 1; rw [two_smul]; abel
              _ ≤ ‖-(-x - y)‖ + ‖x - y‖ := norm_add_le _ _
              _ = ‖-x - y‖ + ‖x - y‖ := by rw [norm_neg]
          rw [norm_smul, hxn, ← dist_eq_norm x y, Real.norm_eq_abs] at h2
          norm_num at h2
          linarith
        calc (Gn n).internal (ann 0 (1 / 4) 2) x y
            ≤ (Gn n).internal (ann 0 (1 / 4) 2) x (-x) +
                (Gn n).internal (ann 0 (1 / 4) 2) (-x) y :=
              (Gn n).internal_triangle _ x (-x) y
          _ ≤ ENNReal.ofReal (A * δ₀ / 4) + ENNReal.ofReal (A * δ₀ / 4) :=
              add_le_add (hdiamGn x hx (-x) hnx hxnx) (hdiamGn (-x) hnx y hy hnxy)
          _ = ENNReal.ofReal (A * δ₀ / 2) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    refine ⟨?_, ?_⟩
    · calc G.internal (ann 0 (1 / 4) 2) x y ≤ G.internal (ann 0 (1 / 2) (3 / 2)) x y :=
            G.internal_anti hVU x y
        _ ≤ ENNReal.ofReal (A * δ₀ / 8) := hdiam x hx y hy
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal δ₀ := by
            rw [← ENNReal.ofReal_mul hA]; exact ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ _ := mul_le_mul_right hsdG _
    · calc (Gn n).internal (ann 0 (1 / 4) 2) x y ≤ ENNReal.ofReal (A * δ₀ / 2) := hM
        _ = ENNReal.ofReal A * ENNReal.ofReal (δ₀ / 2) := by
            rw [← ENNReal.ofReal_mul hA]; congr 1; ring
        _ ≤ _ := mul_le_mul_right hsdGn _
  · -- (iii′): the small-pair modulus (2.3) for `Gₙ` and for `G`
    have hbn : b n ≤ 1 / 4 := hN6 n hn6
    have hxF : x ∈ annCl (0 : Rd d) (1 / 2) (3 / 2) := hAnnF hx
    have hwF : w ∈ annCl (0 : Rd d) (1 / 2) (3 / 2) := l32p_conn_mem hbn hx hw
    have hdist : dist x w ≤ b n := by rw [dist_comm]; exact (mem_ball.1 hw).le
    refine ⟨?_, ?_⟩
    · calc (Gn n).internal (ann 0 (1 / 4) 2) x w ≤ ENNReal.ofReal (η * δ₀ / 2) :=
            hN4 n hn4 x hxF w hwF hdist
        _ ≤ ENNReal.ofReal η * ENNReal.ofReal δ₀ := by
            rw [← ENNReal.ofReal_mul hη.le]; exact ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ _ := mul_le_mul_right hsdG _
    · calc G.internal (ann 0 (1 / 4) 2) x w ≤ ENNReal.ofReal (η * δ₀ / 2) :=
            hN5 n hn5 x hxF w hwF hdist
        _ = ENNReal.ofReal η * ENNReal.ofReal (δ₀ / 2) := by
            rw [← ENNReal.ofReal_mul hη.le]; congr 1; ring
        _ ≤ _ := mul_le_mul_right hsdGn _

/-! ### The choice of `A` and the probability bound on the pinned field -/

/-- **The choice of `A`** (MA1 A10.5): for `p < 1` there is `A ≥ 1`, depending only on `p` and the law of `D_h`, with
`P[l32pGoodD (D_h) A] > p` (continuity from below; `D_h` is a length metric almost surely). -/
theorem l32p_choose_A {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Setting d ξ Q κ D P h) {p : ℝ} (hp : p < 1) :
    ∃ A : ℝ, 1 ≤ A ∧ ENNReal.ofReal p < P {ω | l32pGoodD (D (h ω)) A} := by
  have hd2 : 2 ≤ d := le_trans (by norm_num) hS.dim
  have hmono : Monotone fun n : ℕ => {ω | l32pGoodD (D (h ω)) n} :=
    fun m n hmn ω hω => l32p_goodD_mono (by exact_mod_cast hmn) hω
  have hcover : (univ : Set Ω) ≤ᵐ[P] ⋃ n : ℕ, {ω | l32pGoodD (D (h ω)) n} := by
    filter_upwards [hS.strong.length P h hS.field.1.isLGFPlusCont] with ω hω _
    obtain ⟨n, hn⟩ := l32p_exists_goodD hd2 hω
    exact mem_iUnion.2 ⟨n, hn⟩
  have h1 : (1 : ℝ≥0∞) ≤ ⨆ n : ℕ, P {ω | l32pGoodD (D (h ω)) n} := by
    rw [← hmono.measure_iUnion, ← measure_univ (μ := P)]
    exact measure_mono_ae hcover
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 (lt_of_lt_of_le (ENNReal.ofReal_lt_one.2 hp) h1)
  exact ⟨max n 1, le_max_right _ _,
    lt_of_lt_of_le hn (measure_mono fun ω hω => l32p_goodD_mono (le_max_left _ _) hω)⟩

/-- **The pinned field along a sequence** (MA1 A10.3–A10.6): along every sequence `(ε_j, r_j)` with
`0 < ε_j ≤ r_j ≤ 1`, `ε_j → 0`, `ε_j / r_j → 0`, and radii `b_j → 0`, some index has
`P[Ẽ(D_h, 𝔐_{ε_j,ε_j/r_j}(h); A, η, b_j)] > p`, given `P[l32pGoodD (D_h) A] > p`. -/
theorem l32p_seq {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Setting d ξ Q κ D P h) (hpl : PairLaw κ ξ D P h) (hrc : RescaledConv κ ξ D P h)
    {A η p : ℝ} (hA0 : 0 ≤ A) (hη : 0 < η)
    (hA : ENNReal.ofReal p < P {ω | l32pGoodD (D (h ω)) A})
    (ε r b : ℕ → ℝ) (hεr : ∀ j, 0 < ε j ∧ ε j ≤ r j ∧ r j ≤ 1) (hε : Tendsto ε atTop (𝓝 0))
    (hεr0 : Tendsto (fun j => ε j / r j) atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0)) :
    ∃ j, ENNReal.ofReal p <
      P {ω | l32pUnitGood (D (h ω)) (MepsR κ ξ (ε j) (r j) (h ω)) A η (b j)} := by
  have hd2 : 2 ≤ d := le_trans (by norm_num) hS.dim
  have hprob := hrc ε r hεr hε hεr0
  have hXm : ∀ j, AEMeasurable (fun ω => (MepsR κ ξ (ε j) (r j) (h ω)).1) P := fun j =>
    (measurable_subtype_coe.comp measurable_snd).comp_aemeasurable
      (hpl (ε j) (r j) (hεr j).1 (hεr j).2.1 (hεr j).2.2 0).1
  obtain ⟨ns, hns, hae⟩ := l8_exists_subseq_ae_of_prob P
    (fun j ω => (MepsR κ ξ (ε j) (r j) (h ω)).1) (fun ω => (D (h ω)).1) hXm hprob
  have hbns : Tendsto (fun n => b (ns n)) atTop (𝓝 0) := hb.comp hns.tendsto_atTop
  have hTmono : Monotone fun N : ℕ => {ω | ∀ n ≥ N,
      l32pUnitGood (D (h ω)) (MepsR κ ξ (ε (ns n)) (r (ns n)) (h ω)) A η (b (ns n))} :=
    fun N M hNM ω hω n hn => hω n (hNM.trans hn)
  have hcover : {ω | l32pGoodD (D (h ω)) A} ≤ᵐ[P] ⋃ N : ℕ, {ω | ∀ n ≥ N,
      l32pUnitGood (D (h ω)) (MepsR κ ξ (ε (ns n)) (r (ns n)) (h ω)) A η (b (ns n))} := by
    filter_upwards [hae, hS.strong.length P h hS.field.1.isLGFPlusCont] with ω hω hlen hgood
    have hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn
        (fun n => ⇑(MepsR κ ξ (ε (ns n)) (r (ns n)) (h ω)).1) ⇑(D (h ω)).1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := fun R _ =>
      ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hω _
        ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    obtain ⟨N, hN⟩ := eventually_atTop.1 (l32p_eventually_unitGood hd2
      (fun n => l32p_MepsR_isLength κ ξ _ _ _) hlen hconv hbns hA0 hη hgood)
    exact mem_iUnion.2 ⟨N, hN⟩
  have hle : P {ω | l32pGoodD (D (h ω)) A} ≤ ⨆ N : ℕ, P {ω | ∀ n ≥ N,
      l32pUnitGood (D (h ω)) (MepsR κ ξ (ε (ns n)) (r (ns n)) (h ω)) A η (b (ns n))} := by
    rw [← hTmono.measure_iUnion]
    exact measure_mono_ae hcover
  obtain ⟨N, hN⟩ := lt_iSup_iff.1 (lt_of_lt_of_le hA hle)
  exact ⟨ns N, lt_of_lt_of_le hN (measure_mono fun ω hω => hω N le_rfl)⟩

/-- Elementary facts on the window `𝒩_ε(u)` for `0 < ε < 1`, `0 < u < 1`. -/
theorem l32p_window_facts {ε u r : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hu : 0 < u) (hu1 : u < 1)
    (hr : r ∈ window ε u) : ε ^ u ≤ r ∧ ε ≤ r ∧ r ≤ 1 ∧ 0 < r := by
  obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hr
  have hεu : ε ≤ ε ^ u := by
    have := Real.rpow_le_rpow_of_exponent_ge hε hε1.le hu1.le
    rwa [Real.rpow_one] at this
  have hu2 : ε ^ (u / 2) ≤ 1 := Real.rpow_le_one hε.le hε1.le (by positivity)
  exact ⟨hk1, hεu.trans hk1, hk2.trans hu2, zpow_pos (by norm_num) _⟩

/-- `ε ↦ ε^a` tends to `0` at `0` along a sequence, for `a > 0`. -/
theorem l32p_tendsto_rpow_zero {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun j => ε j ^ a) atTop (𝓝 0) := by
  have hc : ContinuousAt (fun x : ℝ => x ^ a) 0 := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  have h := hc.tendsto.comp hε
  rwa [Function.comp_def, Real.zero_rpow ha.ne'] at h

/-- **Step 3** (MA1 A10, conclusion): for `A` as in `l32p_choose_A` and every `η > 0`, `0 < u < q₀ < 1`, there is
`ε₀ > 0` such that for all `ε ∈ (0, ε₀)` and `r ∈ 𝒩_ε(u)` the rescaled event with connection radius `8 ε^{q₀ − u}`
has probability `≥ p` on the pinned field. By contradiction along a violating sequence (`l32p_seq`). -/
theorem l32p_pinned {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Setting d ξ Q κ D P h) (hpl : PairLaw κ ξ D P h) (hrc : RescaledConv κ ξ D P h)
    {A η p : ℝ} (hA0 : 0 ≤ A) (hη : 0 < η)
    (hA : ENNReal.ofReal p < P {ω | l32pGoodD (D (h ω)) A})
    {u q₀ : ℝ} (hu : 0 < u) (huq : u < q₀) (hq1 : q₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ r ∈ window ε u,
      ENNReal.ofReal p ≤
        P {ω | l32pUnitGood (D (h ω)) (MepsR κ ξ ε r (h ω)) A η (8 * ε ^ (q₀ - u))} := by
  by_contra hcon
  have hchoice : ∀ j : ℕ, ∃ ε : ℝ, ε ∈ Ioo (0 : ℝ) (1 / ((j : ℝ) + 2)) ∧ ∃ r ∈ window ε u,
      P {ω | l32pUnitGood (D (h ω)) (MepsR κ ξ ε r (h ω)) A η (8 * ε ^ (q₀ - u))} <
        ENNReal.ofReal p := by
    intro j
    by_contra hj
    apply hcon
    refine ⟨1 / ((j : ℝ) + 2), by positivity, fun ε hε r hr => ?_⟩
    by_contra hlt
    exact hj ⟨ε, hε, r, hr, not_le.1 hlt⟩
  choose ε hε r hr hlt using hchoice
  have hu1 : u < 1 := huq.trans hq1
  have hε1 : ∀ j, ε j < 1 := fun j => (hε j).2.trans_le (by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hwin := fun j => l32p_window_facts (hε j).1 (hε1 j) hu hu1 (hr j)
  have hεt : Tendsto ε atTop (𝓝 0) := by
    refine squeeze_zero (fun j => (hε j).1.le) (fun j => ((hε j).2.le.trans ?_))
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hratio : Tendsto (fun j => ε j / r j) atTop (𝓝 0) := by
    refine squeeze_zero (fun j => div_nonneg (hε j).1.le (hwin j).2.2.2.le) (fun j => ?_)
      (l32p_tendsto_rpow_zero hεt (sub_pos.2 hu1))
    have hpos : 0 < ε j ^ u := Real.rpow_pos_of_pos (hε j).1 u
    calc ε j / r j ≤ ε j / ε j ^ u := div_le_div_of_nonneg_left (hε j).1.le hpos (hwin j).1
      _ = ε j ^ (1 - u) := by rw [Real.rpow_sub (hε j).1, Real.rpow_one]
  have hb : Tendsto (fun j => 8 * ε j ^ (q₀ - u)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (l32p_tendsto_rpow_zero hεt (sub_pos.2 huq)).const_mul 8
  obtain ⟨j, hj⟩ := l32p_seq hS hpl hrc hA0 hη hA ε r (fun j => 8 * ε j ^ (q₀ - u))
    (fun j => ⟨(hε j).1, (hwin j).2.1, (hwin j).2.2.1⟩) hεt hratio hb
  exact absurd (hlt j) (not_lt.2 hj.le)

end HigherDimLFPPAS.Annulus
