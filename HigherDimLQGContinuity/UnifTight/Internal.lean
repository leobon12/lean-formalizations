import HigherDimLQGContinuity.UnifTight.Holder
import HigherDimLQGMetric.DGZ.TightInternal

/-!
# Uniform DGZ Lemma 6.2: Hölder bounds for internal metrics (packet U4)

Blueprint Part D, `d:lem-u61`(b) (NA3 §2.7; [8]-bp `r2:lem:62`, with MA7 G15). Ports of
`HigherDimLQGMetric.DGZ.holder_box`, `holder_internal_core`, `holder_internal`, `holder_internal_sub` and
`holderTightAQ` (`DGZ/TightInternal.lean`), with every constant chosen before `ξ ∈ S(b, μ)`.

* `holder_box_unif`: uniform Lemma 6.1 on the small boxes `B_{2^{-m}ρ}(c)` for `h_{m, n+m} = h_{n+m} - h_m`
  (shifted and rescaled realization, `DGZ.isDyadicRealization_shiftScale`, similarity covariance `lfppDistOn_sim`).
* `holder_internal_core_unif` (Lemma 6.2, core): for open `U`, compact preconnected `T ⊆ U` and an arbitrary
  continuous perturbation `G`,
  `P[∃ x, y ∈ T : M a^ξ_n(q) ‖x - y‖^β < D(h_n - G)(x, y; U)] ≤ θ + P[∃ z ∈ B̄_R(0), |G z| > L_G]`.
* **`holder_internal_unif`** (`G = 0`), `holder_internal_sub_unif` (`G = h_m`, the field `h_{m,n}`), and
  `holderTightAQ_unif` (`T = V̄`): the form of `UHolderTightShape` normalized by `a^ξ_n(q)` (NA3 §5.3: "first in
  `aQ(q₀)` units").

**Uniformity** (blueprint `d:lem-u61`(b)): the factors of the sealed proof that depend on `ξ` are bounded
uniformly: `e^{ξ(L + L_G)} ≤ e^{b(L + L_G)}` (`L, L_G ≥ 0`), `2^{(1-ϕ(ξ)+1)j} ≤ 2^{2j}` (`ϕ(ξ) ≥ 0`); U3's `uCor52`
gives `a^ξ_{n-m'}(q₀) ≤ C₅ 2^{(1-ϕ(ξ)+1)m'} a^ξ_n(q)` and U1's `exists_le_aQ_unif` gives
`a^ξ_n(q) ≥ c₂ 2^{-(1-ϕ(ξ)+1)n}`, both with constants before `ξ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- `β ≤ 1` for `β < μ` under the uniform hypothesis (`μ ≤ ξ(Q(ξ) - √(2d)) ≤ 1`). -/
lemma u4_beta_le_one {κ : Rd d → ℝ} {b μ ξ β : ℝ} (hU : UHyp d κ b μ ξ) (hβ : β < μ) : β ≤ 1 := by
  have h1 := hU.gap
  have h2 := hU.gap_le_one
  linarith

/-! ### Lemma 6.1 on small boxes -/

/-- **Uniform Lemma 6.1 on small boxes** (port of `DGZ.holder_box`): for `0 < β < μ` there is `q₀ ∈ (0, 1)` such that
for `q ∈ [q₀, 1)` and `θ > 0` there is `M > 0` with
`P[∃ x, y ∈ B_{2^{-m}ρ}(c) : D(h_{n+m} - h_m)(x, y; B_{2^{-m}ρ}(c)) > M a^ξ_n(q) ‖x - y‖^β] ≤ θ`
for every `ξ ∈ S(b, μ)`, every realization, `ρ ∈ [1, 3/2]`, `m`, `c` and `n`. -/
theorem holder_box_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {β : ℝ} (hβ0 : 0 < β) (hβ : β < μ) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ q₀ < 1 ∧ ∀ q : ℝ≥0∞, q₀ ≤ q → q < 1 → ∀ θ : ℝ, 0 < θ →
      ∃ M : ℝ, 0 < M ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ ρ : ℝ, 1 ≤ ρ → ρ ≤ 3 / 2 →
          ∀ (m : ℕ) (c : Rd d) (n : ℕ), P {ω | ∃ x ∈ obox c ((2 : ℝ)⁻¹ ^ m * ρ),
            ∃ y ∈ obox c ((2 : ℝ)⁻¹ ^ m * ρ), M * aQ P H ξ n q * ‖x - y‖ ^ β <
              lfppDistOn ξ (fun z => H (n + m) z ω - H m z ω)
                (obox c ((2 : ℝ)⁻¹ ^ m * ρ)) x y} ≤ ENNReal.ofReal θ := by
  obtain ⟨q₀, hq₀0, hq₀, hmain⟩ := holder_selfInternal_unif hd hκ hb hμ hβ0 hβ
  refine ⟨q₀, hq₀0, hq₀, fun q hq₀q hq1 θ hθ => ?_⟩
  obtain ⟨M, hM, hMb⟩ := hmain q hq₀q hq1 θ hθ
  refine ⟨M, hM, fun ξ hU Ω _ P W H hH ρ hρ1 hρ2 m c n => ?_⟩
  have hβ1 : β ≤ 1 := u4_beta_le_one hU hβ
  have hH' := isDyadicRealization_shiftScale hκ hH m c
  have hb' := hMb ξ hU Ω P _ _ hH' ρ hρ1 hρ2 n
  rw [aQ_eq_of_isDyadicRealization hH' hH] at hb'
  refine le_trans (measure_mono ?_) hb'
  intro ω hω
  obtain ⟨x, hx, y, hy, hlt⟩ := hω
  set s : ℝ := (2 : ℝ)⁻¹ ^ m with hs
  have hs0 : 0 < s := tb_inv_two_pow_pos m
  have hs1 : s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set x' : Rd d := s⁻¹ • (x - c) with hx'
  set y' : Rd d := s⁻¹ • (y - c) with hy'
  have hxx : c + s • x' = x := smul_add_inv c x hs0
  have hyy : c + s • y' = y := smul_add_inv c y hs0
  have hpre := ti_preimage_obox (c := c) (ρ := ρ) hs0
  have hx'm : x' ∈ obox (0 : Rd d) ρ := by rw [← hpre, mem_preimage, hxx]; exact hx
  have hy'm : y' ∈ obox (0 : Rd d) ρ := by rw [← hpre, mem_preimage, hyy]; exact hy
  refine ⟨x', hx'm, y', hy'm, ?_⟩
  -- similarity covariance
  have hsim : lfppDistOn ξ (fun z => H (n + m) z ω - H m z ω) (obox c (s * ρ)) x y =
      s * lfppDistOn ξ (fun z => H (n + m) (c + s • z) ω - H m (c + s • z) ω)
        (obox (0 : Rd d) ρ) x' y' := by
    have := lfppDistOn_sim (LinearIsometryEquiv.refl ℝ (Rd d)) c hs0 ξ
      (fun z => H (n + m) z ω - H m z ω) (obox c (s * ρ)) x' y'
    simp only [LinearIsometryEquiv.coe_refl, id] at this
    rw [hxx, hyy, hpre] at this
    exact this
  have hnorm : ‖x - y‖ = s * ‖x' - y'‖ := by
    rw [← hxx, ← hyy, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0]
  rw [hsim, hnorm] at hlt
  -- `s ‖x' - y'‖^β ≤ (s ‖x' - y'‖)^β` since `s ≤ 1`, `β ≤ 1`
  have hsβ : s ≤ s ^ β := by
    have := Real.rpow_le_rpow_of_exponent_ge hs0 hs1 hβ1
    rwa [Real.rpow_one] at this
  have hpow : s * ‖x' - y'‖ ^ β ≤ (s * ‖x' - y'‖) ^ β := by
    rw [Real.mul_rpow hs0.le (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right hsβ (Real.rpow_nonneg (norm_nonneg _) _)
  have ha0 : 0 ≤ aQ P H ξ n q := (tight_aQ_pos (by omega) hH ξ n
    (lt_of_lt_of_le hq₀0 hq₀q) hq1).le
  have hMa : 0 ≤ M * aQ P H ξ n q := mul_nonneg hM.le ha0
  have h2 : s * (M * aQ P H ξ n q * ‖x' - y'‖ ^ β) <
      s * lfppDistOn ξ (fun z => H (n + m) (c + s • z) ω - H m (c + s • z) ω)
        (obox (0 : Rd d) ρ) x' y' := by
    calc s * (M * aQ P H ξ n q * ‖x' - y'‖ ^ β) = M * aQ P H ξ n q * (s * ‖x' - y'‖ ^ β) := by
          ring
      _ ≤ M * aQ P H ξ n q * (s * ‖x' - y'‖) ^ β := mul_le_mul_of_nonneg_left hpow hMa
      _ < _ := hlt
  exact lt_of_mul_lt_mul_left h2 hs0.le

/-! ### Lemma 6.2: the core estimate -/

/-- **Uniform DGZ Lemma 6.2, core estimate** (Part D `d:lem-u61`(b); port of `DGZ.holder_internal_core`). For
`0 < β < μ` there is `q₁ ∈ (0, 1)` such that for every `q ∈ [q₁, 1)`, every open `U` and every compact preconnected
`T ⊆ U` there is `R ≥ 0` such that for all `θ > 0`, `L_G ≥ 0` there is `M > 0` with
`P[∃ x, y ∈ T : M a^ξ_n(q) ‖x - y‖^β < D(h_n - G)(x, y; U)] ≤ θ + P[∃ z ∈ B̄_R(0), |G z| > L_G]`
for every `ξ ∈ S(b, μ)`, every dyadic realization, every continuous perturbation `G` and every `n`. -/
theorem holder_internal_core_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {β : ℝ} (hβ0 : 0 < β) (hβ : β < μ) :
    ∃ q₁ : ℝ≥0∞, 0 < q₁ ∧ q₁ < 1 ∧ ∀ q : ℝ≥0∞, q₁ ≤ q → q < 1 →
      ∀ U T : Set (Rd d), IsOpen U → IsCompact T → IsPreconnected T → T ⊆ U →
        ∃ R : ℝ, 0 ≤ R ∧ ∀ θ : ℝ, 0 < θ → ∀ LG : ℝ, 0 ≤ LG → ∃ M : ℝ, 0 < M ∧
          ∀ ξ : ℝ, UHyp d κ b μ ξ →
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
            (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
            ∀ G : Rd d → Ω → ℝ, (∀ ω, Continuous fun z => G z ω) → ∀ n : ℕ,
              P {ω | ∃ x ∈ T, ∃ y ∈ T, M * aQ P H ξ n q * ‖x - y‖ ^ β <
                lfppDistOn ξ (fun z => H n z ω - G z ω) U x y} ≤
                ENNReal.ofReal θ + P {ω | ∃ z ∈ cbox (0 : Rd d) R, LG < |G z ω|} := by
  have hd0 : 0 < d := by omega
  obtain ⟨q₀, hq₀0, hq₀, hbox⟩ := holder_box_unif hd hκ hb hμ hβ0 hβ
  obtain ⟨q₁, hq₀q₁, hq₁⟩ := exists_between hq₀
  refine ⟨q₁, hq₀0.trans hq₀q₁, hq₁, fun q hq₁q hq1 U T hU hT hTc hTU => ?_⟩
  have hq₀q : q₀ < q := lt_of_lt_of_le hq₀q₁ hq₁q
  have hq0 : 0 < q := hq₀0.trans hq₀q
  obtain ⟨C₅, hC₅, hcor⟩ := uCor52 hd hκ b μ hb hμ 1 one_pos q₀ q hq₀0 hq₀q hq1
  obtain ⟨c₂, hc₂, hlow⟩ := exists_le_aQ_unif.{0} hd hκ hb hq0 hq1 one_pos
  obtain ⟨R₀, hR₀⟩ := hT.isBounded.subset_closedBall (0 : Rd d)
  obtain ⟨k, hk1, F, hFT, hcov, hsub⟩ := exists_box_cover hT hU hTU
  set R : ℝ := max R₀ 0 + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨R, hR0, fun θ hθ LG hLG => ?_⟩
  set m' : ℕ := k - 1 with hm'
  set r : ℝ := (2 : ℝ)⁻¹ ^ k with hr
  have hr0 : 0 < r := tb_inv_two_pow_pos k
  have h2r : (2 : ℝ)⁻¹ ^ m' * 1 = 2 * r := by rw [mul_one, hm', ti_inv_two_pow_pred hk1]
  have h2r1 : 2 * r ≤ 1 := by
    rw [← h2r, mul_one]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hboxR : ∀ c ∈ F, obox c (2 * r) ⊆ cbox (0 : Rd d) R := fun c hc => by
    have hcT := hR₀ (hFT c hc)
    rw [Metric.mem_closedBall, dist_zero_right] at hcT
    exact ti_obox_subset_cbox h2r1 hcT
  -- the box events
  set θb : ℝ := θ / (3 * ((F.card : ℝ) + 1)) with hθb
  have hθb0 : 0 < θb := by positivity
  obtain ⟨Mb, hMb, hboxb⟩ := hbox q₀ le_rfl hq₀ θb hθb0
  -- supremum tails at the fixed levels
  have hL : ∀ j : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WN d → Ω → ℝ}, IsWhiteNoise P W → ∀ {X : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ j) 1 X → ∀ c : Rd d,
          P {ω | ∃ z ∈ cbox c R, L < |X z ω|} ≤ ENNReal.ofReal (θ / 3) := fun j =>
    exists_sup_tail_level_tight hκ j hR0 (by positivity)
  choose L hL0 hLt using hL
  set Kbig : ℝ := Real.exp (b * (L m' + LG)) * Mb * C₅ * (2 : ℝ) ^ ((2 : ℝ) * m') with hKbig
  set Ksmall : ℝ := ∑ j ∈ Finset.range m', Real.exp (b * (L j + LG)) * (1 + 2 * Real.sqrt d) *
    (2 : ℝ) ^ ((2 : ℝ) * j) / c₂ with hKsmall
  have hKbig0 : 0 ≤ Kbig := by positivity
  have hKsmall0 : 0 ≤ Ksmall := Finset.sum_nonneg fun j _ => by positivity
  set Kc : ℝ := 1 + F.card * (2 * Real.sqrt d) ^ β with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨Kc * (Kbig + Ksmall) + 1, by positivity, fun ξ hU Ω _ P W H hH G hG n => ?_⟩
  have hξ : 0 < ξ := hU.base.xi_pos
  have hξb : ξ ≤ b := hU.le_b
  have hφ0 : 0 ≤ ξ * distExp d ξ := u4_phi_nonneg hμ hU
  have hβ1 : β ≤ 1 := u4_beta_le_one hU hβ
  have ha0 : 0 < aQ P H ξ n q := tight_aQ_pos hd0 hH ξ n hq0 hq1
  set a := aQ P H ξ n q with ha
  have hφc : ∀ ω, Continuous fun z => H n z ω - G z ω := fun ω =>
    ((hH.band n).continuous ω).sub (hG ω)
  -- `2^{(1-ϕ+1)j} ≤ 2^{2j}`
  have hpow2 : ∀ j : ℕ, (2 : ℝ) ^ ((1 - ξ * distExp d ξ + 1) * j) ≤ (2 : ℝ) ^ ((2 : ℝ) * j) := by
    intro j
    have := u4_two_rpow_le_of_phi_nonneg (ε := 1) hφ0 j
    have e : (1 + 1 : ℝ) = 2 := by norm_num
    rwa [e] at this
  -- the deterministic conclusion from per-box bounds
  have hdet : ∀ ω, (∀ c ∈ F, ∀ u ∈ obox c (2 * r), ∀ v ∈ obox c (2 * r),
      lfppDistOn ξ (fun z => H n z ω - G z ω) (obox c (2 * r)) u v ≤
        ((Kbig + Ksmall) * a) * ‖u - v‖ ^ β) →
      ω ∉ {ω | ∃ x ∈ T, ∃ y ∈ T, (Kc * (Kbig + Ksmall) + 1) * a * ‖x - y‖ ^ β <
        lfppDistOn ξ (fun z => H n z ω - G z ω) U x y} := by
    intro ω hω hbad
    obtain ⟨x, hx, y, hy, hlt⟩ := hbad
    have hc := chain_holder_bound (hφc ω) ξ hTc hFT hr0 hcov hsub
      (by positivity : 0 ≤ (Kbig + Ksmall) * a) hβ0 hω x hx y hy
    have hsβ : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
    have : (Kbig + Ksmall) * a * Kc * ‖x - y‖ ^ β ≤
        (Kc * (Kbig + Ksmall) + 1) * a * ‖x - y‖ ^ β := by
      have : (Kbig + Ksmall) * a * Kc = Kc * (Kbig + Ksmall) * a := by ring
      rw [this]
      gcongr
      linarith
    exact absurd hlt (not_lt.2 (hc.trans this))
  set E₃ : Set Ω := {ω | ∃ z ∈ cbox (0 : Rd d) R, LG < |G z ω|} with hE₃
  by_cases hnm : m' ≤ n
  · -- large `n`: the box bounds and the fixed-level supremum of `h_{m'}`
    set boxbad : Rd d → Set Ω := fun c => {ω | ∃ x ∈ obox c ((2 : ℝ)⁻¹ ^ m' * 1),
      ∃ y ∈ obox c ((2 : ℝ)⁻¹ ^ m' * 1), Mb * aQ P H ξ (n - m') q₀ * ‖x - y‖ ^ β <
        lfppDistOn ξ (fun z => H (n - m' + m') z ω - H m' z ω)
          (obox c ((2 : ℝ)⁻¹ ^ m' * 1)) x y} with hboxbad
    set E₁ : Set Ω := ⋃ c ∈ F, boxbad c with hE₁
    set E₂ : Set Ω := {ω | ∃ z ∈ cbox (0 : Rd d) R, L m' < |H m' z ω|} with hE₂
    have hcomp : aQ P H ξ (n - m') q₀ ≤ C₅ * (2 : ℝ) ^ ((2 : ℝ) * m') * a := by
      have h1 := hcor ξ hU Ω P W H hH n m' hnm
      have h2 : C₅ * (2 : ℝ) ^ ((1 - ξ * distExp d ξ + 1) * m') * a ≤
          C₅ * (2 : ℝ) ^ ((2 : ℝ) * m') * a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow2 m') hC₅.le) ha0.le
      exact h1.trans h2
    have hnm' : n - m' + m' = n := Nat.sub_add_cancel hnm
    have hsub' : {ω | ∃ x ∈ T, ∃ y ∈ T, (Kc * (Kbig + Ksmall) + 1) * a * ‖x - y‖ ^ β <
        lfppDistOn ξ (fun z => H n z ω - G z ω) U x y} ⊆ E₁ ∪ E₂ ∪ E₃ := by
      intro ω hω
      by_contra hout
      simp only [mem_union, not_or] at hout
      obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hout
      refine hdet ω (fun c hc u hu v hv => ?_) hω
      have hnb : ω ∉ boxbad c := fun hb => h₁ (mem_iUnion₂.2 ⟨c, hc, hb⟩)
      have hub : lfppDistOn ξ (fun z => H n z ω - H m' z ω) (obox c (2 * r)) u v ≤
          Mb * aQ P H ξ (n - m') q₀ * ‖u - v‖ ^ β := by
        by_contra hc'
        push Not at hc'
        apply hnb
        refine ⟨u, by rw [h2r]; exact hu, v, by rw [h2r]; exact hv, ?_⟩
        rw [h2r, hnm']
        exact hc'
      have hcmp : ∀ z ∈ obox c (2 * r),
          |(H n z ω - G z ω) - (H n z ω - H m' z ω)| ≤ L m' + LG := by
        intro z hz
        have hzR := hboxR c hc hz
        have e1 : |H m' z ω| ≤ L m' := by
          by_contra hh; push Not at hh; exact h₂ ⟨z, hzR, hh⟩
        have e2 : |G z ω| ≤ LG := by
          by_contra hh; push Not at hh; exact h₃ ⟨z, hzR, hh⟩
        calc |(H n z ω - G z ω) - (H n z ω - H m' z ω)| = |H m' z ω - G z ω| := by ring_nf
          _ ≤ |H m' z ω| + |G z ω| := abs_sub _ _
          _ ≤ L m' + LG := add_le_add e1 e2
      have h1 := lfppDistOn_le_exp_mul (ζ := ξ) (x := u) (y := v) (hφc ω)
        (((hH.band n).continuous ω).sub ((hH.band m').continuous ω)) hcmp
      rw [abs_of_pos hξ] at h1
      have hsβ : 0 ≤ ‖u - v‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
      have hexp := u4_exp_mul_le hξb (add_nonneg (hL0 m') hLG)
      have haq0 : 0 ≤ aQ P H ξ (n - m') q₀ := (tight_aQ_pos hd0 hH ξ (n - m') hq₀0 hq₀).le
      calc lfppDistOn ξ (fun z => H n z ω - G z ω) (obox c (2 * r)) u v
          ≤ Real.exp (ξ * (L m' + LG)) *
              lfppDistOn ξ (fun z => H n z ω - H m' z ω) (obox c (2 * r)) u v := h1
        _ ≤ Real.exp (ξ * (L m' + LG)) * (Mb * aQ P H ξ (n - m') q₀ * ‖u - v‖ ^ β) :=
            mul_le_mul_of_nonneg_left hub (Real.exp_pos _).le
        _ ≤ Real.exp (b * (L m' + LG)) *
              (Mb * (C₅ * (2 : ℝ) ^ ((2 : ℝ) * m') * a) * ‖u - v‖ ^ β) := by
            gcongr
        _ = Kbig * a * ‖u - v‖ ^ β := by rw [hKbig]; ring
        _ ≤ (Kbig + Ksmall) * a * ‖u - v‖ ^ β := by
            gcongr
            linarith
    have hP₁ : P E₁ ≤ ENNReal.ofReal (F.card * θb) := by
      refine (measure_biUnion_finset_le F boxbad).trans ?_
      calc ∑ c ∈ F, P (boxbad c) ≤ ∑ _c ∈ F, ENNReal.ofReal θb :=
            Finset.sum_le_sum fun c _ =>
              hboxb ξ hU Ω P W H hH 1 le_rfl (by norm_num) m' c (n - m')
        _ = ENNReal.ofReal (F.card * θb) := by
            rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast]
    have hP₂ : P E₂ ≤ ENNReal.ofReal (θ / 3) := hLt m' hH.whiteNoise (hH.band m') 0
    have hFθ : (F.card : ℝ) * θb ≤ θ / 3 := by
      rw [hθb, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc P _ ≤ P (E₁ ∪ E₂ ∪ E₃) := measure_mono hsub'
      _ ≤ P E₁ + P E₂ + P E₃ := (measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (θ / 3) + ENNReal.ofReal (θ / 3) + P E₃ :=
          add_le_add (add_le_add (hP₁.trans (ENNReal.ofReal_le_ofReal hFθ)) hP₂) le_rfl
      _ ≤ ENNReal.ofReal θ + P E₃ := by
          refine add_le_add ?_ le_rfl
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  · -- small `n`: the segment bound inside each box
    push Not at hnm
    set E₂ : Set Ω := {ω | ∃ z ∈ cbox (0 : Rd d) R, L n < |H n z ω|} with hE₂
    have hsub' : {ω | ∃ x ∈ T, ∃ y ∈ T, (Kc * (Kbig + Ksmall) + 1) * a * ‖x - y‖ ^ β <
        lfppDistOn ξ (fun z => H n z ω - G z ω) U x y} ⊆ E₂ ∪ E₃ := by
      intro ω hω
      by_contra hout
      simp only [mem_union, not_or] at hout
      obtain ⟨h₂, h₃⟩ := hout
      refine hdet ω (fun c hc u hu v hv => ?_) hω
      have hM : ∀ z ∈ obox c (2 * r), ξ * (H n z ω - G z ω) ≤ ξ * (L n + LG) := by
        intro z hz
        have hzR := hboxR c hc hz
        have e1 : |H n z ω| ≤ L n := by
          by_contra hh; push Not at hh; exact h₂ ⟨z, hzR, hh⟩
        have e2 : |G z ω| ≤ LG := by
          by_contra hh; push Not at hh; exact h₃ ⟨z, hzR, hh⟩
        refine mul_le_mul_of_nonneg_left ?_ hξ.le
        have := abs_sub (H n z ω) (G z ω)
        linarith [le_abs_self (H n z ω - G z ω)]
      have h1 := lfppDistOn_le_exp_mul_norm_of_convex (hφc ω)
        (HigherDimLFPP.DGZ.convex_obox c _) hu hv hM
      rw [norm_sub_rev] at h1
      have huv : ‖u - v‖ ≤ 2 * Real.sqrt d := by
        have := norm_sub_le_of_forall_abs_le (x := u) (y := v) (s := 2) fun i => by
          have e1 := hu i
          have e2 := hv i
          rw [abs_lt] at e1 e2
          rw [abs_le]; constructor <;> linarith
        linarith
      have hnorm := th_le_rpow_mul (norm_nonneg (u - v)) huv hβ0 hβ1
      have hsβ : 0 ≤ ‖u - v‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
      -- the small-level constant
      have hterm : Real.exp (ξ * (L n + LG)) * (1 + 2 * Real.sqrt d) ≤ Ksmall * a := by
        have hsingle : Real.exp (b * (L n + LG)) * (1 + 2 * Real.sqrt d) *
            (2 : ℝ) ^ ((2 : ℝ) * n) / c₂ ≤ Ksmall :=
          Finset.single_le_sum (f := fun j => Real.exp (b * (L j + LG)) *
            (1 + 2 * Real.sqrt d) * (2 : ℝ) ^ ((2 : ℝ) * j) / c₂) (fun j _ => by positivity)
            (Finset.mem_range.2 hnm)
        have hexp := u4_exp_mul_le hξb (add_nonneg (hL0 n) hLG)
        have hunif : Real.exp (ξ * (L n + LG)) * (1 + 2 * Real.sqrt d) *
            (2 : ℝ) ^ ((1 - ξ * distExp d ξ + 1) * n) / c₂ ≤ Ksmall := by
          refine le_trans ?_ hsingle
          have hp2 := hpow2 n
          gcongr
        have hlowN := hlow ξ hξ hξb Ω P W H hH n
        have e : (2 : ℝ) ^ ((1 - ξ * distExp d ξ + 1) * n) *
            (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + 1) * n) = 1 := by
          rw [← Real.rpow_add two_pos,
            show (1 - ξ * distExp d ξ + 1) * (n : ℝ) + -(1 - ξ * distExp d ξ + 1) * n = 0 by
              ring, Real.rpow_zero]
        calc Real.exp (ξ * (L n + LG)) * (1 + 2 * Real.sqrt d)
            = Real.exp (ξ * (L n + LG)) * (1 + 2 * Real.sqrt d) *
                ((2 : ℝ) ^ ((1 - ξ * distExp d ξ + 1) * n) *
                  (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + 1) * n)) * (c₂ / c₂) := by
              rw [e, div_self hc₂.ne']; ring
          _ = Real.exp (ξ * (L n + LG)) * (1 + 2 * Real.sqrt d) *
                (2 : ℝ) ^ ((1 - ξ * distExp d ξ + 1) * n) / c₂ *
                  (c₂ * (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + 1) * n)) := by ring
          _ ≤ Ksmall * a := mul_le_mul hunif hlowN (by positivity) hKsmall0
      calc lfppDistOn ξ (fun z => H n z ω - G z ω) (obox c (2 * r)) u v
          ≤ Real.exp (ξ * (L n + LG)) * ‖u - v‖ := h1
        _ ≤ Real.exp (ξ * (L n + LG)) * (‖u - v‖ ^ β * (1 + 2 * Real.sqrt d)) :=
            mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
        _ = Real.exp (ξ * (L n + LG)) * (1 + 2 * Real.sqrt d) * ‖u - v‖ ^ β := by ring
        _ ≤ Ksmall * a * ‖u - v‖ ^ β := mul_le_mul_of_nonneg_right hterm hsβ
        _ ≤ (Kbig + Ksmall) * a * ‖u - v‖ ^ β := by
            gcongr
            linarith
    have hP₂ : P E₂ ≤ ENNReal.ofReal (θ / 3) := hLt n hH.whiteNoise (hH.band n) 0
    calc P _ ≤ P (E₂ ∪ E₃) := measure_mono hsub'
      _ ≤ P E₂ + P E₃ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (θ / 3) + P E₃ := add_le_add hP₂ le_rfl
      _ ≤ ENNReal.ofReal θ + P E₃ :=
          add_le_add (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

/-! ### Lemma 6.2: the fields `h_n` and `h_{m,n}` -/

/-- **Uniform DGZ Lemma 6.2 for `h_n`** (Part D `d:lem-u61`(b) with `m = 0`; port of `DGZ.holder_internal`): for
`0 < β < μ` there is `q₁ ∈ (0, 1)` such that for `q ∈ [q₁, 1)`, every open `U`, every compact preconnected `T ⊆ U`
and `θ > 0` there is `M > 0` with `P[∃ x, y ∈ T : D_n(x, y; U) > M a^ξ_n(q) ‖x - y‖^β] ≤ θ` for every
`ξ ∈ S(b, μ)`, every dyadic realization and every `n`. -/
theorem holder_internal_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {β : ℝ} (hβ0 : 0 < β) (hβ : β < μ) :
    ∃ q₁ : ℝ≥0∞, 0 < q₁ ∧ q₁ < 1 ∧ ∀ q : ℝ≥0∞, q₁ ≤ q → q < 1 →
      ∀ U T : Set (Rd d), IsOpen U → IsCompact T → IsPreconnected T → T ⊆ U →
        ∀ θ : ℝ, 0 < θ → ∃ M : ℝ, 0 < M ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
            (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
              P {ω | ∃ x ∈ T, ∃ y ∈ T, M * aQ P H ξ n q * ‖x - y‖ ^ β <
                lfppDistOn ξ (fun z => H n z ω) U x y} ≤ ENNReal.ofReal θ := by
  obtain ⟨q₁, hq₁0, hq₁, hcore⟩ := holder_internal_core_unif hd hκ hb hμ hβ0 hβ
  refine ⟨q₁, hq₁0, hq₁, fun q hq₁q hq1 U T hU hT hTc hTU θ hθ => ?_⟩
  obtain ⟨R, -, hR⟩ := hcore q hq₁q hq1 U T hU hT hTc hTU
  obtain ⟨M, hM, hMb⟩ := hR θ hθ 0 le_rfl
  refine ⟨M, hM, fun ξ hU Ω _ P W H hH n => ?_⟩
  have hb' := hMb ξ hU Ω P W H hH (fun _ _ => 0) (fun _ => continuous_const) n
  simp only [sub_zero, abs_zero, lt_self_iff_false, and_false, exists_false, ofPred_false,
    measure_empty, add_zero] at hb'
  exact hb'

/-- **Uniform DGZ Lemma 6.2 for `h_{m,n} = h_n - h_m`** (Part D `d:lem-u61`(b), every `m`; port of
`DGZ.holder_internal_sub`): the same bound for the internal metric of `h_n - h_m`, with `M` depending on
`(d, κ, b, μ, β, q, U, T, m, θ)`, not on `ξ ∈ S(b, μ)`. -/
theorem holder_internal_sub_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {β : ℝ} (hβ0 : 0 < β) (hβ : β < μ) :
    ∃ q₁ : ℝ≥0∞, 0 < q₁ ∧ q₁ < 1 ∧ ∀ q : ℝ≥0∞, q₁ ≤ q → q < 1 →
      ∀ U T : Set (Rd d), IsOpen U → IsCompact T → IsPreconnected T → T ⊆ U →
        ∀ (m : ℕ) (θ : ℝ), 0 < θ → ∃ M : ℝ, 0 < M ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
            (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
              P {ω | ∃ x ∈ T, ∃ y ∈ T, M * aQ P H ξ n q * ‖x - y‖ ^ β <
                lfppDistOn ξ (fun z => H n z ω - H m z ω) U x y} ≤ ENNReal.ofReal θ := by
  obtain ⟨q₁, hq₁0, hq₁, hcore⟩ := holder_internal_core_unif hd hκ hb hμ hβ0 hβ
  refine ⟨q₁, hq₁0, hq₁, fun q hq₁q hq1 U T hU hT hTc hTU m θ hθ => ?_⟩
  obtain ⟨R, hR0, hR⟩ := hcore q hq₁q hq1 U T hU hT hTc hTU
  obtain ⟨LG, hLG0, hLG⟩ := exists_sup_tail_level_tight hκ m hR0 (θ := θ / 2)
    (by positivity)
  obtain ⟨M, hM, hMb⟩ := hR (θ / 2) (by positivity) LG hLG0
  refine ⟨M, hM, fun ξ hU Ω _ P W H hH n => ?_⟩
  have hb' := hMb ξ hU Ω P W H hH (H m) (hH.band m).continuous n
  have hG := hLG hH.whiteNoise (hH.band m) 0
  calc _ ≤ _ := hb'
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := add_le_add le_rfl hG
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- **Uniform Hölder tightness normalized by `a^ξ_n(q)`** (Part D `d:lem-u61`(b) with `T = V̄`, `m = 0`; port of
`DGZ.holderTightAQ`; the form of `UHolderTightShape` in `a^ξ_n(q₁)` units, NA3 §5.3): for `0 < β < μ` there is
`q₁ ∈ (0, 1)` such that for `q ∈ [q₁, 1)`, `U` open and `V` bounded, open and connected with `V̄ ⊆ U`, and `θ > 0`,
there is `M > 0` with `P[∃ x, y ∈ V : M a^ξ_n(q) ‖x - y‖^β < D_n(x, y; U)] ≤ θ` for every `ξ ∈ S(b, μ)`, every
dyadic realization and every `n`. -/
theorem holderTightAQ_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {β : ℝ} (hβ0 : 0 < β) (hβ : β < μ) :
    ∃ q₁ : ℝ≥0∞, 0 < q₁ ∧ q₁ < 1 ∧ ∀ q : ℝ≥0∞, q₁ ≤ q → q < 1 →
      ∀ U V : Set (Rd d), IsOpen U → IsOpen V → IsConnected V → Bornology.IsBounded V →
        closure V ⊆ U → ∀ θ : ℝ, 0 < θ → ∃ M : ℝ, 0 < M ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
            (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
              P {ω | ∃ x ∈ V, ∃ y ∈ V, M * aQ P H ξ n q * ‖x - y‖ ^ β <
                lfppDistOn ξ (fun z => H n z ω) U x y} ≤ ENNReal.ofReal θ := by
  obtain ⟨q₁, hq₁0, hq₁, hint⟩ := holder_internal_unif hd hκ hb hμ hβ0 hβ
  refine ⟨q₁, hq₁0, hq₁, fun q hq₁q hq1 U V hU _ hVc hVb hVU θ hθ => ?_⟩
  obtain ⟨M, hM, hMb⟩ := hint q hq₁q hq1 U (closure V) hU hVb.isCompact_closure
    hVc.isPreconnected.closure hVU θ hθ
  refine ⟨M, hM, fun ξ hU Ω _ P W H hH n => le_trans (measure_mono ?_) (hMb ξ hU Ω P W H hH n)⟩
  rintro ω ⟨x, hx, y, hy, hlt⟩
  exact ⟨x, subset_closure hx, y, subset_closure hy, hlt⟩

end HigherDimLQGContinuity
