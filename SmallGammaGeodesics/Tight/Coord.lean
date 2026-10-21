import SmallGammaGeodesics.Tight.LowPass
import SmallGammaGeodesics.Tight.SmallScale
import SmallGammaGeodesics.Upper.Good

/-!
# §6: Theorem 1.2 on the coordinate space, the parts that use no interface (packet P-T1)

Blueprint `blueprint/sections/s6-tightness.tex`, Theorem `thm:tight`; statements of
`planning/packets/BP2-planned-statements.md` (§6 block), BP2 details D13–D14, rulings G12 and G27.

Notation: `G : GSetup`, `P = stdP`, `ξ = ξ_γ`, `δ = ξ^{2/3}`, and `η : ℝ → Coord → C([0,1], ℂ)` with every `η γ`
measurable and a.s. a constant-speed `D^γ_{h₀}`-geodesic from `0` to `1` for `γ ∈ (0,2)`;
`X_γ = X^{γ^{2/3}}(η γ)`.

* `aemeasurable_rescaled` (Theorem `thm:tight` (a)): `X_γ` is measurable.
* `tendstoInMeasure_horizDev` (Theorem `thm:tight` (c), source (1.11); BP2 D14): `hd_{γ^{2/3}}(η γ) → 0` in
  `P`-measure. On the good event `𝒢_γ`, `hd ≤ 3 ξ^{97/300}` (`horizDev_le_of_approx`), so
  `P{hd ≥ ε} ≤ P[𝒢_γᶜ] ≤ C ξ^{20}` once `3 ξ^{97/300} < ε`. Neither interface is used.
* `tight_compact_of_bandScale` (the assembly of Theorem `thm:tight` (b), BP2 D13): **if** the band events at the
  scale `Kδ` satisfy the bound of Lemma `lem:band-event-K` (`P[𝒢_γ ∩ {η γ ∈ ℬ_γ(Kδ)}] ≤ C (K^{-3} + K^{-4}) + ε`
  for small `γ`), then for every `ε > 0` one compact set `modulusSet ω_K` carries `X_γ` with probability
  `≥ 1 − ε` for all small `γ`. The probability budget is `ε/4` (`𝒢ᶜ`) `+ ε/2` (band event) `+ ε/4` (the small-scale
  event of Lemma 6.0) `+ 0` (the null set where `η γ` is not a geodesic).
* `tightConcl_of_bandScale`: the three clauses together, under the same band-event bound.

The band-event bound itself (`bandEv_scale_le`) needs Lemma 5.1 (`lemma51`, packet P-U3) and the mean bound
(`mean_maxDev_le`); its reduction to those two statements is `bandEv_scale_le_of_lemma51` (file
`Tight/Band.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## Limits as `γ → 0⁺` -/

/-- `γ ∈ (0, a)` for all small `γ > 0`. -/
theorem Tight.eventually_mem_Ioo_zero {a : ℝ} (ha : 0 < a) : ∀ᶠ γ in 𝓝[>] (0 : ℝ), γ ∈ Ioo 0 a :=
  Ioo_mem_nhdsGT ha

/-- For `q > 0` and `e > 0`: `c γ^q < e` for all small `γ > 0` (real power). -/
theorem Tight.eventually_mul_rpow_lt (c : ℝ) {q e : ℝ} (hq : 0 < q) (he : 0 < e) :
    ∀ᶠ γ in 𝓝[>] (0 : ℝ), c * γ ^ q < e := by
  have h : Tendsto (fun γ : ℝ => c * γ ^ q) (𝓝 0) (𝓝 (c * (0 : ℝ) ^ q)) :=
    (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto.const_mul c
  rw [Real.zero_rpow hq.ne', mul_zero] at h
  exact (h.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds he)

/-- For `n ≠ 0` and `e > 0`: `c γ^n < e` for all small `γ > 0` (natural power). -/
theorem Tight.eventually_mul_pow_lt (c : ℝ) {n : ℕ} (hn : n ≠ 0) {e : ℝ} (he : 0 < e) :
    ∀ᶠ γ in 𝓝[>] (0 : ℝ), c * γ ^ n < e := by
  have h : Tendsto (fun γ : ℝ => c * γ ^ n) (𝓝 0) (𝓝 (c * (0 : ℝ) ^ n)) :=
    ((continuous_pow n).tendsto 0).const_mul c
  rw [zero_pow hn, mul_zero] at h
  exact (h.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds he)

/-! ## Theorem `thm:tight` (a): measurability -/

/-- **Theorem `thm:tight` (a)**: `X_γ = X^{γ^{2/3}}(η γ)` is measurable (`rescaledPath` is continuous). -/
theorem aemeasurable_rescaled (η : ℝ → Coord → C(unitInterval, ℂ)) (hm : ∀ γ, Measurable (η γ)) :
    ∀ γ, 0 < γ → γ < 2 → AEMeasurable (fun ω => rescaledPath (γ ^ (2/3 : ℝ)) (η γ ω)) stdP := by
  intro γ _ _
  exact ((continuous_rescaledPath _).measurable.comp (hm γ)).aemeasurable

/-! ## Theorem `thm:tight` (c): source (1.11) -/

/-- `hd_s(η) ≥ 0` for `s > 0`. -/
theorem Tight.horizDev_nonneg {s : ℝ} (hs : 0 < s) (η : C(unitInterval, ℂ)) : 0 ≤ horizDev s η := by
  rw [horizDev_eq_div hs]
  exact div_nonneg ((abs_nonneg _).trans (le_ciSup (bddAbove_horiz η) 0)) hs.le

set_option linter.unusedVariables false in
/-- **Theorem `thm:tight` (c)** (source (1.11); BP2 D14): `hd_{γ^{2/3}}(η γ) → 0` in `stdP`-measure as `γ ↓ 0`.
For small `γ` (`γ ≤ γ_g`, `ξ ≤ γ`, `3 γ^{97/300} < ε`), outside `𝒢_γᶜ` and the null set where `η γ` is not a
geodesic, `hd ≤ 3 ξ^{97/300} < ε` (`horizDev_le_of_approx`); hence `P{hd ≥ ε} ≤ P[𝒢_γᶜ] ≤ C ξ^{20} → 0`
(`good_compl_le`). Neither interface is used.

The signature is the planned one (BP2 §6 block). The measurability hypothesis `hm` is part of it but the bound
is on the outer measure, so the argument does not use it; the unused-variable linter is silenced here. -/
theorem tendstoInMeasure_horizDev (G : GSetup) (η : ℝ → Coord → C(unitInterval, ℂ))
    (hm : ∀ γ, Measurable (η γ))
    (hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)) :
    TendstoInMeasure stdP (fun γ ω => horizDev (γ ^ (2/3 : ℝ)) (η γ ω)) (𝓝[>] 0) (fun _ => 0) := by
  obtain ⟨γg, hγg, -, hgood⟩ := approxGeod_of_good G
  obtain ⟨γc, Cc, hγc, hcompl⟩ := good_compl_le G
  obtain ⟨γ₀, hγ₀, hγ₀1, hξ⟩ := exists_xiGamma_pos_le
  refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  rcases eq_or_ne δ ⊤ with hδt | hδt
  · exact Filter.Eventually.of_forall fun γ => by rw [hδt]; exact le_top
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have hδr : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
  have hγ₁0 : 0 < min (min γg γc) γ₀ := lt_min (lt_min hγg hγc) hγ₀
  filter_upwards [Tight.eventually_mem_Ioo_zero hγ₁0,
    Tight.eventually_mul_rpow_lt 3 (q := 97 / 300) (by norm_num) he,
    Tight.eventually_mul_pow_lt (max Cc 0) (n := 20) (by norm_num) hδr] with γ hγ h3 h20
  have hγ0 : 0 < γ := hγ.1
  have hγg' : γ ≤ γg := hγ.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγc' : γ ≤ γc := hγ.2.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγ₀' : γ ≤ γ₀ := hγ.2.le.trans (min_le_right _ _)
  have hγ2 : γ < 2 := by linarith
  obtain ⟨hξ0, hξγ⟩ := hξ γ ⟨hγ0, hγ₀'⟩
  -- the event is contained in `𝒢ᶜ ∪ {η γ is not a geodesic}`
  have hsub : {ω | ε ≤ edist (horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) 0} ⊆
      {ω | ¬ goodEv G γ ω} ∪ {ω | ¬ IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)} := by
    intro ω hω
    by_contra hcon
    have hgω : goodEv G γ ω := by
      by_contra h
      exact hcon (Or.inl h)
    have hgeo : IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω) := by
      by_contra h
      exact hcon (Or.inr h)
    rw [← (G.compat γ ⟨hγ0, hγ2⟩).2 ω] at hgeo
    obtain ⟨hA, hΔ, -⟩ := (hgood γ ⟨hγ0, hγg'⟩).2 ω hgω (η γ ω) hgeo
    have hhd := horizDev_le_of_approx hA hΔ hξ0 hξγ
    have hhd0 := Tight.horizDev_nonneg (Real.rpow_pos_of_pos hγ0 (2 / 3)) (η γ ω)
    have hlt : horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω) < ε.toReal := by
      have : xiGamma γ ^ (97 / 300 : ℝ) ≤ γ ^ (97 / 300 : ℝ) :=
        Real.rpow_le_rpow hξ0.le hξγ (by norm_num)
      linarith
    have hω' : ε ≤ ENNReal.ofReal (horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) := by
      have e1 : edist (horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) 0 =
          ENNReal.ofReal (horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) := by
        rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg hhd0]
      rw [← e1]
      exact hω
    have hlt' : ENNReal.ofReal (horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) < ε := by
      rw [← ENNReal.ofReal_toReal hεtop]
      exact (ENNReal.ofReal_lt_ofReal_iff he).2 hlt
    exact absurd hω' (not_le.2 hlt')
  have hnull : stdP {ω | ¬ IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)} = 0 :=
    ae_iff.1 (hη γ hγ0 hγ2)
  calc stdP {ω | ε ≤ edist (horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) 0}
      ≤ stdP ({ω | ¬ goodEv G γ ω} ∪ {ω | ¬ IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)}) :=
        measure_mono hsub
    _ ≤ stdP {ω | ¬ goodEv G γ ω} + stdP {ω | ¬ IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)} :=
        measure_union_le _ _
    _ = stdP {ω | ¬ goodEv G γ ω} := by rw [hnull, add_zero]
    _ ≤ ENNReal.ofReal (Cc * xiGamma γ ^ 20) := hcompl γ ⟨hγ0, hγc'⟩
    _ ≤ ENNReal.ofReal (max Cc 0 * γ ^ 20) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc Cc * xiGamma γ ^ 20 ≤ max Cc 0 * xiGamma γ ^ 20 :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max Cc 0 * γ ^ 20 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hξ0.le hξγ 20) (le_max_right _ _)
    _ ≤ ENNReal.ofReal δ.toReal := ENNReal.ofReal_le_ofReal h20.le
    _ = δ := ENNReal.ofReal_toReal hδt

/-! ## Theorem `thm:tight` (b): the assembly from the band-event bound -/

/-- For every `C` and `ε > 0` there is `K ≥ 1` with `C (K^{-3} + K^{-4}) ≤ ε/4` (take `K = max(1, 8C⁺/ε)`). -/
theorem Tight.exists_one_le_mul_rpow_neg_le (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ C * (K ^ (-3 : ℝ) + K ^ (-4 : ℝ)) ≤ ε / 4 := by
  set K : ℝ := max 1 (8 * max C 0 / ε) with hK_def
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  refine ⟨K, hK1, ?_⟩
  have h3 : K ^ (-3 : ℝ) ≤ K⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
  have h4 : K ^ (-4 : ℝ) ≤ K⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
  have hpos : 0 ≤ K ^ (-3 : ℝ) + K ^ (-4 : ℝ) := by positivity
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hK8 : 8 * max C 0 ≤ ε * K := by
    have := le_max_right 1 (8 * max C 0 / ε)
    rw [← hK_def, div_le_iff₀ hε] at this
    linarith
  calc C * (K ^ (-3 : ℝ) + K ^ (-4 : ℝ)) ≤ max C 0 * (K ^ (-3 : ℝ) + K ^ (-4 : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    _ ≤ max C 0 * (2 * K⁻¹) := mul_le_mul_of_nonneg_left (by linarith) hC0
    _ = 2 * max C 0 / K := by ring
    _ ≤ ε / 4 := by
        rw [div_le_iff₀ hK0]
        linarith

/-- The modulus `ω(r) = a r^{1/8} + b r^{1/200} + c r^{7/15}` tends to `0` as `r ↓ 0`. -/
theorem Tight.tendsto_modulusFn_zero (a b c : ℝ) :
    Tendsto (fun r : ℝ => a * r ^ (1 / 8 : ℝ) + b * r ^ (1 / 200 : ℝ) + c * r ^ (7 / 15 : ℝ))
      (𝓝[≥] 0) (𝓝 0) := by
  have h1 := (Real.continuousAt_rpow_const 0 (1 / 8 : ℝ) (Or.inr (by norm_num))).tendsto
  have h2 := (Real.continuousAt_rpow_const 0 (1 / 200 : ℝ) (Or.inr (by norm_num))).tendsto
  have h3 := (Real.continuousAt_rpow_const 0 (7 / 15 : ℝ) (Or.inr (by norm_num))).tendsto
  have h := ((h1.const_mul a).add (h2.const_mul b)).add (h3.const_mul c)
  rw [Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
    at h
  simp only [mul_zero, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Assembly of Theorem `thm:tight` (b)** (BP2 D13). Suppose the band events at the scale `Kδ` satisfy the
bound of Lemma `lem:band-event-K`: for some `C`, every `K ≥ 1` and every `ε > 0`, for all small `γ > 0`,
`P[𝒢_γ ∩ {η γ ∈ ℬ_γ(Kδ)}] ≤ C (K^{-3} + K^{-4}) + ε`. Then for every `ε > 0` there is a compact
`𝒦 ⊆ C([0,1], ℂ)` with `P{X_γ ∉ 𝒦} ≤ ε` for all small `γ > 0`.

Proof. Choose `K ≥ 1` with `C (K^{-3} + K^{-4}) ≤ ε/4`, and `n` by Lemma 6.0 (`smallScale_lower`) for `ε/4`; put
`𝒦 = modulusSet ω_K` with `ω_K` from `rescaled_mem_modulusSet`, compact by Arzelà–Ascoli
(`isCompact_modulusSet`). For small `γ`: `P[𝒢ᶜ] ≤ ε/4`, `P[𝒢 ∩ ℬ(Kδ)] ≤ ε/2`, `P[SS_γ] ≤ ε/4`, and the set where
`η γ` is not a geodesic is null. Off these four sets `rescaled_mem_modulusSet` applies with
`d = e^{-b_γ} S.D^γ(ω)` and `Δ = Δ₈(ω)` (`approxGeod_of_good`), so `X_γ ∈ 𝒦`. -/
theorem tight_compact_of_bandScale (G : GSetup) (η : ℝ → Coord → C(unitInterval, ℂ))
    (hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)) (C : ℝ)
    (hband : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ∀ᶠ γ in 𝓝[>] (0 : ℝ),
      stdP {ω | goodEv G γ ω ∧ bandEv γ (K * dlt γ) (η γ ω)} ≤
        ENNReal.ofReal (C * (K ^ (-3 : ℝ) + K ^ (-4 : ℝ)) + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : Set C(unitInterval, ℂ), IsCompact K ∧
      ∀ᶠ γ in 𝓝[>] (0:ℝ), stdP {ω | rescaledPath (γ ^ (2/3 : ℝ)) (η γ ω) ∉ K} ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨C₁, C₂, hC₁, hC₂, hres⟩ := rescaled_mem_modulusSet
  obtain ⟨K, hK1, hKC⟩ := Tight.exists_one_le_mul_rpow_neg_le C hε
  obtain ⟨n, γs, hγs, hss⟩ := smallScale_lower G.S (ε / 4) (by positivity)
  obtain ⟨γg, hγg, -, hgood⟩ := approxGeod_of_good G
  obtain ⟨γc, Cc, hγc, hcompl⟩ := good_compl_le G
  obtain ⟨γ₀, hγ₀, hγ₀1, hξ⟩ := exists_xiGamma_pos_le
  set mK : ℝ → ℝ := fun r => C₁ * K * r ^ (1/8 : ℝ) + C₂ * r ^ (1/200 : ℝ) + 3 * r ^ (7/15 : ℝ)
    with hmK
  refine ⟨modulusSet mK, isCompact_modulusSet mK (Tight.tendsto_modulusFn_zero _ _ _), ?_⟩
  set τ : ℝ := ((2 : ℝ)⁻¹ ^ n) ^ (5 / 4 : ℝ) / 2 with hτ
  have hτ0 : 0 < τ := by positivity
  have hγ₁0 : 0 < min (min γg γc) (min γ₀ γs) := lt_min (lt_min hγg hγc) (lt_min hγ₀ hγs)
  filter_upwards [Tight.eventually_mem_Ioo_zero hγ₁0,
    Tight.eventually_mul_pow_lt 1 (n := 2) (by norm_num) hτ0,
    Tight.eventually_mul_pow_lt (max Cc 0) (n := 20) (by norm_num) (by positivity : (0 : ℝ) < ε / 4),
    hband K hK1 (ε / 4) (by positivity)] with γ hγ h2 h20 hb
  have hγ0 : 0 < γ := hγ.1
  have hγg' : γ ≤ γg := hγ.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγc' : γ ≤ γc := hγ.2.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγ₀' : γ ≤ γ₀ := hγ.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγs' : γ ≤ γs := hγ.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγ1 : γ ≤ 1 := hγ₀'.trans hγ₀1.le
  have hγ2 : γ < 2 := by linarith
  have hγn : γ ^ 2 < τ := by linarith
  obtain ⟨hξ0, hξγ⟩ := hξ γ ⟨hγ0, hγ₀'⟩
  obtain ⟨hξa, hgoodγ⟩ := hgood γ ⟨hγ0, hγg'⟩
  -- the four exceptional sets
  set B1 : Set Coord := {ω | ¬ goodEv G γ ω} with hB1
  set B2 : Set Coord := {ω | goodEv G γ ω ∧ bandEv γ (K * dlt γ) (η γ ω)} with hB2
  set B3 : Set Coord := {ω | ∃ z ∈ Metric.closedBall (0 : ℂ) 2, ∃ w ∈ Metric.closedBall (0 : ℂ) 2,
      0 < ‖z - w‖ ∧ ‖z - w‖ ≤ (2 : ℝ)⁻¹ ^ n ∧
        Real.exp (-G.S.b γ) * (G.S.D γ ω).1 (z, w) < ‖z - w‖ ^ (5 / 4 : ℝ)} with hB3
  set B4 : Set Coord := {ω | ¬ IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)} with hB4
  have hsub : {ω | rescaledPath (γ ^ (2/3 : ℝ)) (η γ ω) ∉ modulusSet mK} ⊆ B1 ∪ B2 ∪ B3 ∪ B4 := by
    intro ω hω
    by_contra hcon
    have h1 : goodEv G γ ω := by
      by_contra h
      exact hcon (Or.inl (Or.inl (Or.inl h)))
    have h2' : ¬ bandEv γ (K * dlt γ) (η γ ω) := fun h => hcon (Or.inl (Or.inl (Or.inr ⟨h1, h⟩)))
    have h3 : ω ∉ B3 := fun h => hcon (Or.inl (Or.inr h))
    have h4 : IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω) := by
      by_contra h
      exact hcon (Or.inr h)
    rw [← (G.compat γ ⟨hγ0, hγ2⟩).2 ω] at h4
    obtain ⟨hA, hΔ, -⟩ := hgoodγ ω h1 (η γ ω) h4
    have hsmall : ∀ z ∈ Metric.closedBall (0 : ℂ) 2, ∀ w ∈ Metric.closedBall (0 : ℂ) 2,
        0 < ‖z - w‖ → ‖z - w‖ ≤ (2 : ℝ)⁻¹ ^ n →
          ‖z - w‖ ^ (5 / 4 : ℝ) ≤ (fun p => Real.exp (-G.S.b γ) * (G.S.D γ ω).1 p) (z, w) := by
      intro z hz w hw hzw0 hzw
      by_contra hlt
      exact h3 ⟨z, hz, w, hw, hzw0, hzw, lt_of_not_ge hlt⟩
    have hbd : ∀ j ≤ Jxi (xiGamma γ), ∀ a ∈ probeGrid j, |band (yPath (η γ ω)) j a| ≤
        cBeta * K * xiGamma γ ^ (2 / 3 : ℝ) * ell j ^ (1 / 8 : ℝ) := by
      intro j hj a ha
      by_contra hlt
      refine h2' ⟨j, hj, a, ha, ?_⟩
      have e : cBeta * (K * dlt γ) * ell j ^ (1 / 8 : ℝ) =
          cBeta * K * xiGamma γ ^ (2 / 3 : ℝ) * ell j ^ (1 / 8 : ℝ) := by
        rw [dlt]
        ring
      rw [e]
      exact lt_of_not_ge hlt
    exact hω (hres γ (xiGamma γ) K _ n _ (η γ ω) hξ0 hξγ hγ1 hξa hK1 hγn hA hΔ hsmall hbd)
  -- the probability budget `ε/4 + ε/2 + ε/4 + 0`
  have hP1 : stdP B1 ≤ ENNReal.ofReal (ε / 4) := by
    refine (hcompl γ ⟨hγ0, hγc'⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    calc Cc * xiGamma γ ^ 20 ≤ max Cc 0 * xiGamma γ ^ 20 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Cc 0 * γ ^ 20 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hξ0.le hξγ 20) (le_max_right _ _)
      _ ≤ ε / 4 := h20.le
  have hP2 : stdP B2 ≤ ENNReal.ofReal (ε / 2) :=
    hb.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hP3 : stdP B3 ≤ ENNReal.ofReal (ε / 4) := hss γ ⟨hγ0, hγs'⟩
  have hP4 : stdP B4 = 0 := ae_iff.1 (hη γ hγ0 hγ2)
  calc stdP {ω | rescaledPath (γ ^ (2/3 : ℝ)) (η γ ω) ∉ modulusSet mK}
      ≤ stdP (B1 ∪ B2 ∪ B3 ∪ B4) := measure_mono hsub
    _ ≤ stdP B1 + stdP B2 + stdP B3 + stdP B4 := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) + 0 := by
        rw [hP4]
        gcongr
    _ = ENNReal.ofReal ε := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **Theorem `thm:tight`, assembled from the band-event bound**: the three clauses of `TightConcl` for `stdP`
and `η`, given the bound of Lemma `lem:band-event-K` for `η` (clauses (a) and (c) do not use it). -/
theorem tightConcl_of_bandScale (G : GSetup) (η : ℝ → Coord → C(unitInterval, ℂ))
    (hm : ∀ γ, Measurable (η γ))
    (hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η γ ω)) (C : ℝ)
    (hband : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ∀ᶠ γ in 𝓝[>] (0 : ℝ),
      stdP {ω | goodEv G γ ω ∧ bandEv γ (K * dlt γ) (η γ ω)} ≤
        ENNReal.ofReal (C * (K ^ (-3 : ℝ) + K ^ (-4 : ℝ)) + ε)) :
    TightConcl stdP η :=
  ⟨aemeasurable_rescaled η hm, tight_compact_of_bandScale G η hη C hband,
    tendstoInMeasure_horizDev G η hm hη⟩

end SmallGammaGeodesics
