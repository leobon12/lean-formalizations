import HigherDimLFPPAS.Normalizer.Transfer
import HigherDimLFPPAS.Normalizer.Exponent
import HigherDimLQGMetric.Sec10.Pure

/-!
# Lemma 2.5: `c_ε(r) → 1` uniformly on compact sets of radii (packet N1; MA1 A7)

`c_ε(r) = r 𝔞_{ε/r} / (r^{ξQ} 𝔞_ε)` ((1.8)). Lemma 2.5 of `source/higher-dimensional-lfpp-almost-sure.pdf`
(l. 290–310) states (2.9) `c_ε(r) → 1` for each `r > 0`, (2.10), and `𝔞_ε = ε^{1−ξQ+o(1)}`; the paper derives
the last two from regular-variation theory. Here everything follows from the **uniform** statement
`sup_{r ∈ [a, b]} |c_ε(r) − 1| → 0` (`n1_ratio_unif_of_cont`), whose proof is a direct coupling argument
along sequences `ε_n ↓ 0`, `r_n → r₀ > 0` (`n1_ratio_tendsto_seq_of_cont`), followed by compactness
(`n1_ratio_unif_of_seq`). The consequences (2.10) and the exponent are the real-analysis lemmas of
`Normalizer/Exponent.lean`.

**The coupling argument** (a variant of MA1 A7.3 that needs neither `lemma103` nor median continuity).
Fix `ε > 0`, `r > 0`, `δ = ε/r`, and the normalized field `g = recentAff r 0 h` (`= h(r ·) − h_r(0)` a.s.).
Almost surely, with `F = r^{ξQ} e^{ξ h_r(0)} > 0`, `A = 𝔞_δ⁻¹ D^δ_g(0, e₁)`, `X = D_g(0, e₁) > 0`:
* `N := 𝔞_ε⁻¹ D^ε_h(0, r e₁) = c_ε(r) F A` (LFPP scaling, hypothesis `hscale`), and
* `D_h(0, r e₁) = F X` (coordinate change (iv) and Weyl scaling by a constant).
On the event `{|N − D_h(0, r e₁)| ≤ τ D_h(0, r e₁)} ∩ {|A − X| ≤ τ X}` the deterministic inequality
`n1_ratio_core` gives `|c_ε(r) − 1| ≤ 4τ`, so it suffices that this event has positive probability. The first
event is controlled by (1.6) for `h` and a lower bound for `D_h(0, r e₁)`; the second has the probability of
the corresponding event for `h` itself at cutoff `δ` (the pair `(A, X)` is a null-measurable function of the
normalized field `g`, which has the law of `h`), so it is controlled by (1.6) for `h` at `(0, e₁)`. The seed
enters only through the a.s. continuity of the convolution field (`hc`) and the LFPP scaling identity
(`hscale`); both are supplied for admissible seeds in `Normalizer/Seed.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Normalizer

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-! ## Elementary inputs -/

/-- **The deterministic core.** If `N = c F A`, `D = F X` with `F, X > 0`, `|N − D| ≤ τ D`, `|A − X| ≤ τ X`
and `0 < τ ≤ 1/2`, then `|c − 1| ≤ 4τ`. -/
theorem n1_ratio_core {c A X N Dn F τ : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2) (hF : 0 < F)
    (hX : 0 < X) (hN : N = c * F * A) (hD : Dn = F * X) (h1 : |N - Dn| ≤ τ * Dn)
    (h2 : |A - X| ≤ τ * X) : |c - 1| ≤ 4 * τ := by
  have hA : X / 2 ≤ A := by
    have := (abs_le.1 h2).1
    nlinarith
  have hApos : 0 < A := by linarith
  -- `|c A − X| ≤ τ X`
  have h1' : |c * A - X| ≤ τ * X := by
    rw [hN, hD] at h1
    have heq : c * F * A - F * X = F * (c * A - X) := by ring
    rw [heq, abs_mul, abs_of_pos hF] at h1
    have : F * |c * A - X| ≤ F * (τ * X) := by linarith
    exact le_of_mul_le_mul_left this hF
  -- `|c − 1| A ≤ 2 τ X ≤ 4 τ A`
  have hkey : |c - 1| * A ≤ 4 * τ * A := by
    have heq : (c - 1) * A = (c * A - X) + (X - A) := by ring
    have hle : |(c - 1) * A| ≤ 2 * τ * X := by
      rw [heq]
      calc |(c * A - X) + (X - A)| ≤ |c * A - X| + |X - A| := abs_add_le _ _
        _ = |c * A - X| + |A - X| := by rw [abs_sub_comm X A]
        _ ≤ τ * X + τ * X := add_le_add h1' h2
        _ = 2 * τ * X := by ring
    rw [abs_mul, abs_of_pos hApos] at hle
    nlinarith
  exact le_of_mul_le_mul_right hkey hApos

/-- A strictly positive measurable random variable is below a small deterministic level `a > 0` with
small probability. -/
theorem n1_exists_prob_lt_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hXm : Measurable X) (hX : ∀ ω, 0 < X ω) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ a : ℝ, 0 < a ∧ P {ω | X ω < a} < η := by
  let s : ℕ → Set Ω := fun n => {ω | X ω < 1 / ((n : ℝ) + 1)}
  have hs : ∀ n, NullMeasurableSet (s n) P := fun n =>
    (hXm measurableSet_Iio).nullMeasurableSet
  have hanti : Antitone s := by
    intro m n hmn ω hω
    change X ω < 1 / ((n : ℝ) + 1) at hω
    change X ω < 1 / ((m : ℝ) + 1)
    refine lt_of_lt_of_le hω ?_
    gcongr
  have hinter : (⋂ n, s n) = ∅ := by
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hX ω)
    exact absurd (mem_iInter.1 hω n) (not_lt.2 hn.le)
  have hlim := tendsto_measure_iInter_atTop hs hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

/-- Continuity of the metric in its arguments, as convergence in probability: if `p_n → p₀` then
`P[|D_h(p_n) − D_h(p₀)| ≥ a] → 0`. -/
theorem n1_eventually_prob_dist_lt {d : ℕ} {D : DistRd d → ContMetric d} (hDm : Measurable D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistRd d}
    (hhm : Measurable h) {ps : ℕ → Rd d × Rd d} {p₀ : Rd d × Rd d} (hps : Tendsto ps atTop (𝓝 p₀))
    {a : ℝ} (ha : 0 < a) {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ n in atTop, P {ω | a ≤ |(D (h ω)).1 (ps n) - (D (h ω)).1 p₀|} < η := by
  have hmeas : TendstoInMeasure P (fun n ω => (D (h ω)).1 (ps n)) atTop
      (fun ω => (D (h ω)).1 p₀) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) (Eventually.of_forall fun ω => ?_)
    · exact ((n1_measurable_apply hDm (ps n)).comp hhm).aestronglyMeasurable
    · exact ((D (h ω)).1.continuous.tendsto p₀).comp hps
  have h1 := hmeas (ENNReal.ofReal a) (ENNReal.ofReal_pos.2 ha)
  filter_upwards [h1.eventually (gt_mem_nhds hη)] with n hn
  refine lt_of_le_of_lt (measure_mono fun ω hω => ?_) hn
  change a ≤ |(D (h ω)).1 (ps n) - (D (h ω)).1 p₀| at hω
  change ENNReal.ofReal a ≤ edist ((D (h ω)).1 (ps n)) ((D (h ω)).1 p₀)
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal hω

/-- **Uniformity from sequences** (compactness of `[a, b]`): if `c(ε_n, r_n) → 1` whenever `ε_n ↓ 0` and
`r_n → r₀ > 0` with `r_n > 0`, then `sup_{r ∈ [a, b]} |c(ε, r) − 1| → 0` for every `0 < a`. -/
theorem n1_ratio_unif_of_seq {c : ℝ → ℝ → ℝ}
    (hseq : ∀ (εs rs : ℕ → ℝ) (r₀ : ℝ), Tendsto εs atTop (𝓝[>] 0) → Tendsto rs atTop (𝓝 r₀) →
      0 < r₀ → (∀ n, 0 < rs n) → Tendsto (fun n => c (εs n) (rs n)) atTop (𝓝 1))
    {a b : ℝ} (ha : 0 < a) :
    ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc a b, |c ε r - 1| ≤ η := by
  intro η hη
  by_contra hcon
  rw [not_eventually] at hcon
  simp only [not_forall, not_le, exists_prop] at hcon
  obtain ⟨εs, hεs, hbad⟩ := frequently_iff_seq_forall.1 hcon
  choose rs hrs hrbad using hbad
  obtain ⟨r₀, hr₀, φ, hφ, hlim⟩ := (isCompact_Icc (a := a) (b := b)).tendsto_subseq hrs
  have hconv := hseq (εs ∘ φ) (rs ∘ φ) r₀ (hεs.comp hφ.tendsto_atTop) hlim
    (lt_of_lt_of_le ha hr₀.1) (fun n => lt_of_lt_of_le ha (hrs (φ n)).1)
  obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.1 hconv) η hη).exists
  rw [Real.dist_eq] at hn
  exact absurd (hrbad (φ n)) (not_lt.2 hn.le)

/-! ## The two scaling identities -/

/-- **(1.5) at `(0, r e₁)`** (coordinate change (iv) and Weyl scaling by a constant): almost surely
`D_h(0, r e₁) = r^{ξQ} e^{ξ h_r(0)} D_g(0, e₁)` with `g = recentAff r 0 h`. -/
theorem n1_ae_coord_e₁ {d : ℕ} (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ Q D) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, (D (h ω)).1 (0, r • e₁ d) =
      r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r 0) * (D (recentAff r 0 (h ω))).1 (0, e₁ d) := by
  filter_upwards [hD.ae_normalizedAtScale_pure hh.1 hr,
    hh.1.ae_sphereAvg_affineComp hd hr 0 one_pos 0] with ω hn hs
  have hg : s8a_pureRescaled h r ω = recentAff r 0 (h ω) := by
    simp only [s8a_pureRescaled, recentAff, hs, mul_one, smul_zero, zero_add]
  have hev := congrArg (fun F : C(Rd d × Rd d, ℝ) => F (0, e₁ d)) hn
  simp only [normalizedAtScale, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, smul_eq_mul, smul_zero, hg] at hev
  have hrq : 0 < r ^ (ξ * Q) := Real.rpow_pos_of_pos hr _
  have hexp : Real.exp (-ξ * sphereAvg (h ω) r 0) * Real.exp (ξ * sphereAvg (h ω) r 0) = 1 := by
    rw [← Real.exp_add, show -ξ * sphereAvg (h ω) r 0 + ξ * sphereAvg (h ω) r 0 = 0 by ring,
      Real.exp_zero]
  rw [← hev]
  calc (D (h ω)).1 (0, r • e₁ d)
      = (r ^ (ξ * Q) * (r ^ (ξ * Q))⁻¹) * (Real.exp (-ξ * sphereAvg (h ω) r 0) *
          Real.exp (ξ * sphereAvg (h ω) r 0)) * (D (h ω)).1 (0, r • e₁ d) := by
        rw [mul_inv_cancel₀ hrq.ne', hexp, one_mul, one_mul]
    _ = r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r 0) * ((r ^ (ξ * Q))⁻¹ *
          Real.exp (-ξ * sphereAvg (h ω) r 0) * (D (h ω)).1 (0, r • e₁ d)) := by ring

/-! ## One step of the coupling argument -/

/-- **One step** (MA1 A7.3, coupling form). Fix `ε, r > 0` with positive normalizers, `R ≥ r`, `a > 0`
and `0 < τ ≤ 1/2`. If the LFPP scaling identity holds a.s. at `(ε, r)` and the three bad events
`{τ a ≤ sup_{B̄_R²} |𝔞_ε⁻¹ D^ε_h − D_h|}`, `{D_h(0, r e₁) < a}` and
`{τ D_g(0, e₁) < |𝔞_δ⁻¹ D^δ_g(0, e₁) − D_g(0, e₁)|}` (`g = recentAff r 0 h`, `δ = ε/r`) have total
probability `< 1`, then `|c_ε(r) − 1| ≤ 4τ`. -/
theorem n1_ratio_step {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ Q D) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsNormalizedLGF h P)
    {ε r R τ a : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2) (ha : 0 < a)
    (haε : 0 < aEps κ ξ ε) (haδ : 0 < aEps κ ξ (ε / r))
    (hscale : ∀ᵐ ω ∂P, lfppDist κ ξ ε (h ω) (0, r • e₁ d) =
      r * Real.exp (ξ * sphereAvg (h ω) r 0) * lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d))
    (hsmall : P {ω | ENNReal.ofReal (τ * a) ≤
          ⨆ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p)} +
        P {ω | (D (h ω)).1 (0, r • e₁ d) < a} +
        P {ω | τ * (D (recentAff r 0 (h ω))).1 (0, e₁ d) <
          |(aEps κ ξ (ε / r))⁻¹ * lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d) -
            (D (recentAff r 0 (h ω))).1 (0, e₁ d)|} < 1) :
    |r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε) - 1| ≤ 4 * τ := by
  set B1 : Set Ω := {ω | ENNReal.ofReal (τ * a) ≤
      ⨆ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
        edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p)} with hB1
  set B2 : Set Ω := {ω | (D (h ω)).1 (0, r • e₁ d) < a} with hB2
  set B3 : Set Ω := {ω | τ * (D (recentAff r 0 (h ω))).1 (0, e₁ d) <
      |(aEps κ ξ (ε / r))⁻¹ * lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d) -
        (D (recentAff r 0 (h ω))).1 (0, e₁ d)|} with hB3
  have hae := hscale.and (n1_ae_coord_e₁ hd hD hh hr)
  -- a good sample point
  obtain ⟨ω, h1, h2, h3, hs, hco⟩ : ∃ ω, ω ∉ B1 ∧ ω ∉ B2 ∧ ω ∉ B3 ∧
      lfppDist κ ξ ε (h ω) (0, r • e₁ d) = r * Real.exp (ξ * sphereAvg (h ω) r 0) *
        lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d) ∧
      (D (h ω)).1 (0, r • e₁ d) = r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r 0) *
        (D (recentAff r 0 (h ω))).1 (0, e₁ d) := by
    by_contra hcon
    push Not at hcon
    set N0 : Set Ω := {ω | ¬ (lfppDist κ ξ ε (h ω) (0, r • e₁ d) =
        r * Real.exp (ξ * sphereAvg (h ω) r 0) *
          lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d) ∧
      (D (h ω)).1 (0, r • e₁ d) = r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r 0) *
        (D (recentAff r 0 (h ω))).1 (0, e₁ d))} with hN0
    have hnull : P N0 = 0 := ae_iff.1 hae
    have hcover : (univ : Set Ω) ⊆ B1 ∪ B2 ∪ B3 ∪ N0 := by
      intro ω _
      by_cases g1 : ω ∈ B1
      · exact Or.inl (Or.inl (Or.inl g1))
      by_cases g2 : ω ∈ B2
      · exact Or.inl (Or.inl (Or.inr g2))
      by_cases g3 : ω ∈ B3
      · exact Or.inl (Or.inr g3)
      refine Or.inr fun hboth => ?_
      exact hcon ω g1 g2 g3 hboth.1 hboth.2
    have hle : P univ ≤ P B1 + P B2 + P B3 := by
      calc P univ ≤ P (B1 ∪ B2 ∪ B3 ∪ N0) := measure_mono hcover
        _ ≤ P (B1 ∪ B2 ∪ B3) + P N0 := measure_union_le _ _
        _ = P (B1 ∪ B2 ∪ B3) := by rw [hnull, add_zero]
        _ ≤ P (B1 ∪ B2) + P B3 := measure_union_le _ _
        _ ≤ P B1 + P B2 + P B3 := add_le_add (measure_union_le _ _) le_rfl
    rw [measure_univ] at hle
    exact absurd (lt_of_le_of_lt hle hsmall) (lt_irrefl _)
  -- the deterministic quantities at `ω`
  have hne : (0 : Rd d) ≠ e₁ d := (HigherDimLFPP.e₁_ne_zero (by omega)).symm
  have hXpos : 0 < (D (recentAff r 0 (h ω))).1 (0, e₁ d) := ContMetric.apply_pos _ hne
  have hFpos : 0 < r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r 0) :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)
  -- `|N − D_h(0, r e₁)| < τ a` from `ω ∉ B1`
  have hmem : ((0 : Rd d), r • e₁ d) ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R := by
    refine ⟨mem_closedBall_self (le_trans hr.le hrR), ?_⟩
    rw [mem_closedBall, dist_zero_right, norm_smul, HigherDimLFPP.norm_e₁ (by omega), mul_one,
      Real.norm_eq_abs, abs_of_pos hr]
    exact hrR
  have hd1 : |(aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε (h ω) (0, r • e₁ d) - (D (h ω)).1 (0, r • e₁ d)| <
      τ * a := by
    have hlt : ⨆ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
        edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p) <
          ENNReal.ofReal (τ * a) := not_le.1 h1
    have hpt := lt_of_le_of_lt (le_biSup (fun p =>
      edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p)) hmem) hlt
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity), Real.dist_eq] at hpt
    simpa only [Pi.smul_apply, smul_eq_mul] using hpt
  have hd2 : a ≤ (D (h ω)).1 (0, r • e₁ d) := not_lt.1 h2
  have hd3 : |(aEps κ ξ (ε / r))⁻¹ * lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d) -
      (D (recentAff r 0 (h ω))).1 (0, e₁ d)| ≤ τ * (D (recentAff r 0 (h ω))).1 (0, e₁ d) :=
    not_lt.1 h3
  have hN : (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε (h ω) (0, r • e₁ d) =
      (r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε)) *
        (r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r 0)) *
        ((aEps κ ξ (ε / r))⁻¹ * lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d)) := by
    rw [hs]
    have hrq : 0 < r ^ (ξ * Q) := Real.rpow_pos_of_pos hr _
    field_simp
  exact n1_ratio_core hτ hτ2 hFpos hXpos hN hco
    (le_trans hd1.le (mul_le_mul_of_nonneg_left hd2 hτ.le)) hd3

/-! ## The third bad event has the law of the corresponding event for `h` -/

/-- The third bad event of `n1_ratio_step` for any normalized LGF `g` has the probability of the same
event for `h` (law transfer: it is the preimage of a set that is null-measurable for `normLGFLaw d`), and
the latter is bounded by an event of (1.6) for `h` plus `P[D_h(0, e₁) < a']`. -/
theorem n1_prob_bad3_le {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} {ξ : ℝ} {δ : ℝ}
    (hc : ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ δ g z)
    {D : DistRd d → ContMetric d} (hDm : Measurable D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h g : Ω → DistRd d} (hh : IsNormalizedLGF h P) (hg : IsNormalizedLGF g P)
    {τ a' : ℝ} (hτ : 0 < τ) :
    P {ω | τ * (D (g ω)).1 (0, e₁ d) <
        |(aEps κ ξ δ)⁻¹ * lfppDist κ ξ δ (g ω) (0, e₁ d) - (D (g ω)).1 (0, e₁ d)|} ≤
      P {ω | ENNReal.ofReal (τ * a') ≤
          ⨆ p ∈ closedBall (0 : Rd d) 1 ×ˢ closedBall (0 : Rd d) 1,
            edist (((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ (h ω)) p) ((D (h ω)).1 p)} +
        P {ω | (D (h ω)).1 (0, e₁ d) < a'} := by
  -- the event as a set of distributions, null-measurable for the normalized law
  set S : Set (DistRd d) := {f | τ * (D f).1 (0, e₁ d) <
      |(aEps κ ξ δ)⁻¹ * lfppDist κ ξ δ f (0, e₁ d) - (D f).1 (0, e₁ d)|} with hSdef
  have hX : AEMeasurable (fun f : DistRd d => (D f).1 (0, e₁ d)) (normLGFLaw d) :=
    (n1_measurable_apply hDm (0, e₁ d)).aemeasurable
  have hL : AEMeasurable (fun f : DistRd d => lfppDist κ ξ δ f (0, e₁ d)) (normLGFLaw d) :=
    n1_aemeasurable_lfppDist ξ measurable_id hc (0, e₁ d)
  have hS : NullMeasurableSet S (normLGFLaw d) := by
    refine nullMeasurableSet_lt (hX.const_mul τ) ?_
    exact continuous_abs.measurable.comp_aemeasurable ((hL.const_mul _).sub hX)
  have heq : P (g ⁻¹' S) = P (h ⁻¹' S) := n1_preimage_eq_preimage hd hg hh hS
  change P (g ⁻¹' S) ≤ _
  rw [heq]
  have hmem : ((0 : Rd d), e₁ d) ∈ closedBall (0 : Rd d) 1 ×ˢ closedBall (0 : Rd d) 1 := by
    refine ⟨mem_closedBall_self zero_le_one, ?_⟩
    rw [mem_closedBall, dist_zero_right, HigherDimLFPP.norm_e₁ (by omega)]
  refine le_trans (measure_mono fun ω hω => ?_) (measure_union_le _ _)
  change τ * (D (h ω)).1 (0, e₁ d) <
    |(aEps κ ξ δ)⁻¹ * lfppDist κ ξ δ (h ω) (0, e₁ d) - (D (h ω)).1 (0, e₁ d)| at hω
  by_cases hsmall : (D (h ω)).1 (0, e₁ d) < a'
  · exact Or.inr hsmall
  · left
    push Not at hsmall
    change ENNReal.ofReal (τ * a') ≤ _
    refine le_trans ?_ (le_biSup (fun p =>
      edist (((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ (h ω)) p) ((D (h ω)).1 p)) hmem)
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have : τ * a' ≤ τ * (D (h ω)).1 (0, e₁ d) := mul_le_mul_of_nonneg_left hsmall hτ.le
    linarith

/-! ## Lemma 2.5 along sequences and uniformly -/

/-- `1/8 + 2/8 + 2/8 < 1` in `ℝ≥0∞`. -/
theorem n1_eighths_lt_one :
    ENNReal.ofReal (1 / 8) + (ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8)) +
      (ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8)) < 1 := by
  have e1 : ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) = ENNReal.ofReal (1 / 4) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [e1, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  exact ENNReal.ofReal_lt_one.2 (by norm_num)

/-- **`c_{ε_n}(r_n) → 1`** along every `ε_n ↓ 0` and `r_n → r₀ > 0` (MA1 A7.3, coupling form), given
(1.6) for the normalized LGF `h`, the a.s. continuity of the convolution fields of the normalized law
(`hc`) and the a.s. LFPP scaling identity at every radius (`hscale`). -/
theorem n1_ratio_tendsto_seq_of_cont {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} {ξ Q : ℝ}
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    (hc : ∀ ε : ℝ, 0 < ε → ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    (hscale : ∀ r : ℝ, 0 < r → ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      lfppDist κ ξ ε (h ω) (0, r • e₁ d) =
        r * Real.exp (ξ * sphereAvg (h ω) r 0) * lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d))
    {εs rs : ℕ → ℝ} {r₀ : ℝ} (hεs : Tendsto εs atTop (𝓝[>] 0)) (hrs : Tendsto rs atTop (𝓝 r₀))
    (hr₀ : 0 < r₀) (hrpos : ∀ n, 0 < rs n) :
    Tendsto (fun n => rs n * aEps κ ξ (εs n / rs n) / (rs n ^ (ξ * Q) * aEps κ ξ (εs n)))
      atTop (𝓝 1) := by
  have hne : (0 : Rd d) ≠ e₁ d := (HigherDimLFPP.e₁_ne_zero (by omega)).symm
  have hDm := hD.measurable
  rw [Metric.tendsto_nhds]
  intro e he
  set τ : ℝ := min (e / 8) (1 / 2) with hτdef
  have hτ : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτ2 : τ ≤ 1 / 2 := min_le_right _ _
  have h8 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 8) := ENNReal.ofReal_pos.2 (by norm_num)
  -- levels `a` (for `D_h(0, r₀ e₁)`) and `a'` (for `D_h(0, e₁)`)
  obtain ⟨a₂, ha₂, hPa₂⟩ := n1_exists_prob_lt_lt (P := P)
    (X := fun ω => (D (h ω)).1 (0, r₀ • e₁ d)) ((n1_measurable_apply hDm _).comp hh.1.measurable)
    (fun ω => ContMetric.apply_pos _ (by
      intro h0
      have h1 : r₀ • e₁ d = 0 := h0.symm
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact hr₀.ne' h2
      · exact HigherDimLFPP.e₁_ne_zero (by omega) h2)) h8
  obtain ⟨a', ha', hPa'⟩ := n1_exists_prob_lt_lt (P := P)
    (X := fun ω => (D (h ω)).1 (0, e₁ d)) ((n1_measurable_apply hDm _).comp hh.1.measurable)
    (fun ω => ContMetric.apply_pos _ hne) h8
  set a : ℝ := a₂ / 2 with hadef
  have ha : 0 < a := by positivity
  -- `δ_n = ε_n / r_n → 0⁺`
  have hδs : Tendsto (fun n => εs n / rs n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (tendsto_nhdsWithin_iff.1 hεs).1.div hrs hr₀.ne'
      rw [zero_div] at this
      exact this
    · filter_upwards [(tendsto_nhdsWithin_iff.1 hεs).2] with n hn
      exact div_pos hn (hrpos n)
  -- the eventual bounds
  have hE1 : ∀ᶠ n in atTop, P {ω | ENNReal.ofReal (τ * a) ≤
      ⨆ p ∈ closedBall (0 : Rd d) (2 * r₀) ×ˢ closedBall (0 : Rd d) (2 * r₀),
        edist (((aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (h ω)) p) ((D (h ω)).1 p)} <
          ENNReal.ofReal (1 / 8) := by
    have hlim := (hconv (2 * r₀) (by positivity) (τ * a) (by positivity)).comp hεs
    exact hlim.eventually (gt_mem_nhds h8)
  have hE2 : ∀ᶠ n in atTop, P {ω | (D (h ω)).1 (0, rs n • e₁ d) < a} <
      ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := by
    have hps : Tendsto (fun n => ((0 : Rd d), rs n • e₁ d)) atTop (𝓝 ((0 : Rd d), r₀ • e₁ d)) :=
      tendsto_const_nhds.prodMk_nhds (hrs.smul_const (e₁ d))
    filter_upwards [n1_eventually_prob_dist_lt (P := P) hDm hh.1.measurable hps ha h8] with n hn
    calc P {ω | (D (h ω)).1 (0, rs n • e₁ d) < a}
        ≤ P ({ω | (D (h ω)).1 (0, r₀ • e₁ d) < a₂} ∪
            {ω | a ≤ |(D (h ω)).1 (0, rs n • e₁ d) - (D (h ω)).1 (0, r₀ • e₁ d)|}) := by
          refine measure_mono fun ω hω => ?_
          change (D (h ω)).1 (0, rs n • e₁ d) < a at hω
          by_cases hb : (D (h ω)).1 (0, r₀ • e₁ d) < a₂
          · exact Or.inl hb
          · right
            push Not at hb
            change a ≤ |(D (h ω)).1 (0, rs n • e₁ d) - (D (h ω)).1 (0, r₀ • e₁ d)|
            rw [abs_sub_comm]
            refine le_trans ?_ (le_abs_self _)
            linarith
      _ ≤ P {ω | (D (h ω)).1 (0, r₀ • e₁ d) < a₂} +
            P {ω | a ≤ |(D (h ω)).1 (0, rs n • e₁ d) - (D (h ω)).1 (0, r₀ • e₁ d)|} :=
          measure_union_le _ _
      _ < ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := ENNReal.add_lt_add hPa₂ hn
  have hE3 : ∀ᶠ n in atTop, P {ω | ENNReal.ofReal (τ * a') ≤
      ⨆ p ∈ closedBall (0 : Rd d) 1 ×ˢ closedBall (0 : Rd d) 1,
        edist (((aEps κ ξ (εs n / rs n))⁻¹ • lfppDist κ ξ (εs n / rs n) (h ω)) p)
          ((D (h ω)).1 p)} < ENNReal.ofReal (1 / 8) := by
    have hlim := (hconv 1 one_pos (τ * a') (by positivity)).comp hδs
    exact hlim.eventually (gt_mem_nhds h8)
  have hE4 : ∀ᶠ n in atTop, rs n ≤ 2 * r₀ :=
    hrs.eventually (ge_mem_nhds (by linarith))
  have hE5 : ∀ᶠ n in atTop, 0 < εs n := (tendsto_nhdsWithin_iff.1 hεs).2
  filter_upwards [hE1, hE2, hE3, hE4, hE5] with n h1 h2 h3 h4 h5
  have hrn := hrpos n
  have hδn : 0 < εs n / rs n := div_pos h5 hrn
  have hgn : IsNormalizedLGF (fun ω => recentAff (rs n) 0 (h ω)) P :=
    isNormalizedLGF_recentAff hd hh.1 hrn 0
  have hB3 := n1_prob_bad3_le (ξ := ξ) hd (hc _ hδn) hDm hh hgn (a' := a') hτ
  have hsum : P {ω | ENNReal.ofReal (τ * a) ≤
          ⨆ p ∈ closedBall (0 : Rd d) (2 * r₀) ×ˢ closedBall (0 : Rd d) (2 * r₀),
            edist (((aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (h ω)) p) ((D (h ω)).1 p)} +
        P {ω | (D (h ω)).1 (0, rs n • e₁ d) < a} +
        P {ω | τ * (D (recentAff (rs n) 0 (h ω))).1 (0, e₁ d) <
          |(aEps κ ξ (εs n / rs n))⁻¹ *
              lfppDist κ ξ (εs n / rs n) (recentAff (rs n) 0 (h ω)) (0, e₁ d) -
            (D (recentAff (rs n) 0 (h ω))).1 (0, e₁ d)|} < 1 := by
    calc _ < ENNReal.ofReal (1 / 8) + (ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8)) +
          (ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8)) :=
          ENNReal.add_lt_add (ENNReal.add_lt_add h1 h2)
            (lt_of_le_of_lt hB3 (ENNReal.add_lt_add h3 hPa'))
      _ < 1 := n1_eighths_lt_one
  have hscale_n : ∀ᵐ ω ∂P, lfppDist κ ξ (εs n) (h ω) (0, rs n • e₁ d) =
      rs n * Real.exp (ξ * sphereAvg (h ω) (rs n) 0) *
        lfppDist κ ξ (εs n / rs n) (recentAff (rs n) 0 (h ω)) (0, e₁ d) := by
    filter_upwards [hscale (rs n) hrn] with ω hω
    exact hω (εs n) h5
  have hstep := n1_ratio_step hd hD hh hrn h4 hτ hτ2 ha
    (n1_aEps_pos_of_cont hd ξ (hc _ h5)) (n1_aEps_pos_of_cont hd ξ (hc _ hδn)) hscale_n hsum
  rw [Real.dist_eq]
  calc |rs n * aEps κ ξ (εs n / rs n) / (rs n ^ (ξ * Q) * aEps κ ξ (εs n)) - 1| ≤ 4 * τ := hstep
    _ ≤ 4 * (e / 8) := by
        have := min_le_left (e / 8) (1 / 2)
        linarith
    _ < e := by linarith

/-- **Lemma 2.5, uniform form** (MA1 A7.4): `sup_{r ∈ [a, b]} |c_ε(r) − 1| → 0` as `ε ↓ 0`, for every
`0 < a`, given (1.6) for `h` and the two seed inputs `hc`, `hscale`. -/
theorem n1_ratio_unif_of_cont {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} {ξ Q : ℝ}
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    (hc : ∀ ε : ℝ, 0 < ε → ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    (hscale : ∀ r : ℝ, 0 < r → ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      lfppDist κ ξ ε (h ω) (0, r • e₁ d) =
        r * Real.exp (ξ * sphereAvg (h ω) r 0) * lfppDist κ ξ (ε / r) (recentAff r 0 (h ω)) (0, e₁ d))
    {a b : ℝ} (ha : 0 < a) :
    ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc a b,
      |r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε) - 1| ≤ η :=
  n1_ratio_unif_of_seq (c := fun ε r => r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε))
    (fun _ _ _ hεs hrs hr₀ hrpos =>
      n1_ratio_tendsto_seq_of_cont hd hD hh hconv hc hscale hεs hrs hr₀ hrpos) ha

end HigherDimLFPPAS.Normalizer
