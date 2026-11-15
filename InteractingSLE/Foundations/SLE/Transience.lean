import InteractingSLE.Foundations.SLE.TraceGtEight
import QuantumZipper.Proofs.RS.TransienceScale
import QuantumZipper.Proofs.RS.TransienceMarkov
import QuantumZipper.Proofs.RS.GenerationBasic

/-!
# Transience of the chordal SLE_κ trace

Design `planning/INFRA-GEO.md` §4, packet GEO-RSALL (the `SLE/Transience.lean` half); worker packet
`planning/packets/PROVE-GEO-RSALL.md`.

[RS05] S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Theorem 7.1: for
`κ ≠ 8`, almost surely `|η(t)| → ∞` (arXiv v4, `SLEcont.tex` lines 2220–2401). Its proof has two
parts:

* **scaling step** (p. 34): if almost surely `0 ∉ closure η([1,∞))`, then a.s. `|η(t)| → ∞`;
* **avoidance input**: for `κ ≤ 4` this is [RS05, Lemma 7.2] plus the two-sided boundary
  correspondence at time `1`; for `κ > 4` it comes from [RS05, Lemma 7.3] ("interior"): for
  `κ > 4`, `κ ≠ 8` and `t > 0`, almost surely `K_t ⊇ {z ∈ ℍ : |z| < ε}` for some `ε > 0`.

QuantumZipper proves the scaling step for `κ < 8` (`QuantumZipper.RS.transience_of_avoid_zero`,
probability spaces in `Type` only) and the avoidance input for `κ ≤ 4`
(`QuantumZipper.RS.ae_zero_not_mem_closure_Ici_one`). This file

* proves the scaling step for every `κ` whose trace is a.s. the radial limit and has a measurable
  continuous version (`ae_tendsto_norm_sleTrace_of_avoid`, any universe), and instantiates it with
  QuantumZipper's trace (`κ < 8`), the trace of `TraceGtEight.lean` (`κ > 8`) and the statement of
  the SLE₈ anchor (`κ = 8`);
* proves the deterministic step from Lemma 7.3 to the avoidance input
  (`zero_not_mem_closure_trace_image_Ici_one`): if `K_1 ⊇ ℍ ∩ B(0,ε)` then `|η(t)| ≥ ε` for all
  `t ≥ 1`, because `f̂_t(iy) ∈ ℍ \ K_t ⊆ ℍ \ K_1`;
* proves transience unconditionally for `0 < κ ≤ 4` (`ae_tendsto_norm_sleTrace_of_le_four`).

For `κ > 4` the statements below take [RS05, Lemma 7.3] at `t = 1` as an explicit hypothesis
(`ae_tendsto_norm_sleTrace_of_interior`; `κ = 8` also takes the statement of the SLE₈ anchor
`InteractingSLE.SLE8.ae_exists_continuous_trace`). Lemma 7.3 is not available in any library: its
proof uses [RS05, Lemma 6.6] (`ncard`, the law of the first hit of `[1,∞)`: an interval is
swallowed at once with positive probability), the strong Markov property at the swallowing time
`τ(1)`, scaling and Blumenthal's zero-one law and, for `κ > 8`, [RS05, Theorem 6.4, Lemma 6.5] and
the zero area of `∂K_t` ([RS05, Corollary 5.3]); see the handoff
`planning/handoffs/PROVE-GEO-RSALL.md`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

/-! ### The deterministic step: from `K_1 ⊇ ℍ ∩ B(0,ε)` to `|η(t)| ≥ ε` for `t ≥ 1` -/

section Deterministic

variable {W : ℝ → ℝ}

/-- If the hull at time `1` contains `ℍ ∩ B(0,ε)`, then for `t ≥ 1` every point `f̂_t(iy)` of the
radial path lies outside `B(0,ε)`, hence so does its limit `η(t)`. -/
theorem le_norm_trace_of_ball_subset_fwdHull (hW : Continuous W) (hW0 : W 0 = 0) {ε : ℝ}
    (hball : ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull W 1) {t : ℝ} (ht : 1 ≤ t)
    (hlim : Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (trace W t))) :
    ε ≤ ‖trace W t‖ := by
  have hev : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), fwdMapInv W t ((y : ℂ) * I) ∈ {p : ℂ | ε ≤ ‖p‖} := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hm := fwdMapInv_mem_compl_fwdHull hW hW0 (zero_le_one.trans ht) (mem_H_mul_I hy)
    show ε ≤ ‖fwdMapInv W t (y * I)‖
    by_contra hlt
    exact hm.2 (QuantumZipper.fwdHull_mono.1 ht (hball _ hm.1 (not_le.1 hlt)))
  exact (isClosed_le continuous_const continuous_norm).mem_of_tendsto hlim hev

/-- **Avoidance from the interior property.** If `K_1 ⊇ ℍ ∩ B(0,ε)` for some `ε > 0` and the trace
is the radial limit at every time `t ≥ 1`, then `0 ∉ closure η([1,∞))`. -/
theorem zero_not_mem_closure_trace_image_Ici_one (hW : Continuous W) (hW0 : W 0 = 0) {ε : ℝ}
    (hε : 0 < ε) (hball : ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull W 1)
    (hlim : ∀ t : ℝ, 1 ≤ t →
      Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (trace W t))) :
    (0 : ℂ) ∉ closure (trace W '' Ici 1) := by
  have hsub : closure (trace W '' Ici 1) ⊆ {p : ℂ | ε ≤ ‖p‖} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    rintro _ ⟨t, ht, rfl⟩
    exact le_norm_trace_of_ball_subset_fwdHull hW hW0 hball ht (hlim t ht)
  intro h0
  have := hsub h0
  simp only [mem_ofPred_eq, norm_zero] at this
  linarith

end Deterministic

/-! ### Transfer from the canonical path space -/

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A property of the SLE driving function that holds almost surely for the coordinate process
under every Brownian law on `CPath` holds almost surely for every Brownian motion, on a
probability space in any universe. -/
theorem ae_drive_of_forall_canon [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (κ : ℝ)
    {Q : (ℝ → ℝ) → Prop}
    (hQ : ∀ (μ : Measure CPath) [IsProbabilityMeasure μ], IsBrownianReal canonBM μ →
      ∀ᵐ f ∂μ, Q (drive κ canonBM f)) :
    ∀ᵐ ω ∂P, Q (drive κ B ω) := by
  obtain ⟨G0, hG0m, hG0c, -, hG0br, hG0eq⟩ := exists_good_version0 hB
  set μ : Measure CPath := P.map (toCPath G0 hG0c) with hμ
  have hm := measurable_toCPath hG0m hG0c
  have hcan : IsBrownianReal canonBM μ :=
    isBrownianReal_canonBM hG0br.toIsPreBrownianReal hG0m hG0c
  have hpull := ae_of_ae_map hm.aemeasurable (hQ μ hcan)
  filter_upwards [hpull, hG0eq] with ω h1 h2
  have hdr : drive κ canonBM (toCPath G0 hG0c ω) = drive κ B ω :=
    funext fun t => by simp [drive, h2]
  rwa [hdr] at h1

end Transfer

/-! ### The scaling step of [RS05, Theorem 7.1] for a general `κ` -/

section Scaling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Scaling of the SLE trace** (a.s. form, mirror of `QuantumZipper.RS.ae_sleTrace_scale`): if
almost surely the trace is the radial limit at every time, then for `a > 0` the trace driven by
`a⁻¹ B(a² ·)` is almost surely `s ↦ η(a² s)/a` on `[0,∞)`. -/
theorem ae_sleTrace_scale_of_tendsto (hB : IsBrownianReal B P) {κ : ℝ}
    (hlim : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * I))
      (𝓝[>] 0) (𝓝 (sleTrace κ B ω t)))
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s →
      sleTrace κ (fun t ω => (√((a ^ 2).toNNReal : ℝ))⁻¹ * B ((a ^ 2).toNNReal * t) ω) ω s =
        sleTrace κ B ω (a ^ 2 * s) / a := by
  filter_upwards [hlim, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hc h0 s hs
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hdr : drive κ (fun t ω => (√((a ^ 2).toNNReal : ℝ))⁻¹ * B ((a ^ 2).toNNReal * t) ω) ω =
      fun r => drive κ B ω (a ^ 2 * r) / a := by
    funext r
    simp only [drive, Real.coe_toNNReal _ (sq_nonneg a), Real.sqrt_sq ha.le,
      Real.toNNReal_mul (sq_nonneg a)]
    field_simp
  have h := (trace_scale hW hW0 ha hs (hω (a ^ 2 * s) (by positivity))).2
  unfold sleTrace
  rw [hdr, h]

/-- **The scaling step of [RS05, Theorem 7.1]** (p. 34), for a general `κ`, on a probability space
in any universe (generalizing `QuantumZipper.RS.transience_of_avoid_zero`, which is stated for
`κ < 8` and spaces in `Type`). Its inputs are stated for the coordinate process on `CPath`: the
trace is a.s. the radial limit (`hlim`), it has a measurable continuous version (`hmeas`), and
a.s. `0 ∉ closure η([1,∞))` (`hav`). Then a.s. `|η(t)| → ∞`. -/
theorem ae_tendsto_norm_sleTrace_of_avoid {κ : ℝ}
    (hlim : ∀ (μ : Measure CPath) [IsProbabilityMeasure μ], IsBrownianReal canonBM μ →
      ∀ᵐ f ∂μ, ∀ t : ℝ, 0 ≤ t → Tendsto (fun y : ℝ => fwdMapInv (drive κ canonBM f) t (y * I))
        (𝓝[>] 0) (𝓝 (trace (drive κ canonBM f) t)))
    (hmeas : ∀ (μ : Measure CPath) [IsProbabilityMeasure μ], IsBrownianReal canonBM μ →
      ∃ η : CPath → ℝ → ℂ, Measurable η ∧ (∀ f, Continuous (η f)) ∧
        ∀ᵐ f ∂μ, EqOn (η f) (sleTrace κ canonBM f) (Ici 0))
    (hav : ∀ (μ : Measure CPath) [IsProbabilityMeasure μ], IsBrownianReal canonBM μ →
      ∀ᵐ f ∂μ, (0 : ℂ) ∉ closure (sleTrace κ canonBM f '' Ici 1))
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖sleTrace κ B ω t‖) atTop atTop := by
  have hlimB : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * I)) (𝓝[>] 0)
        (𝓝 (sleTrace κ B ω t)) :=
    ae_drive_of_forall_canon hB κ
      (Q := fun W => ∀ t : ℝ, 0 ≤ t →
        Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (trace W t))) hlim
  obtain ⟨G0, hG0m, hG0c, -, hG0br, -⟩ := exists_good_version0 hB
  set μ : Measure CPath := P.map (toCPath G0 hG0c) with hμ
  have hcan : IsBrownianReal canonBM μ :=
    isBrownianReal_canonBM hG0br.toIsPreBrownianReal hG0m hG0c
  obtain ⟨η, hηm, hηc, hηeq⟩ := hmeas μ hcan
  have hlimE := tendsto_measure_transE hηm hηeq (hav μ hcan)
  -- the scaling bound `P[∃ t ≥ a², |η(t)| < M] ≤ μ(E_{M/a})`
  have key : ∀ a : ℝ, 0 < a → ∀ M : ℝ,
      P {ω | ∃ t, a ^ 2 ≤ t ∧ ‖sleTrace κ B ω t‖ < M} ≤ μ (transE η (M / a)) := by
    intro a ha M
    have hc0 : (a ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
    obtain ⟨G, hGm, hGc, -, hGbr, hGeq⟩ := exists_good_version0 (hB.smul hc0)
    have hmapeq : P.map (toCPath G hGc) = μ :=
      map_toCPath_eq hGbr.toIsPreBrownianReal hG0br.toIsPreBrownianReal hGm hG0m hGc hG0c
    have hGm' := measurable_toCPath hGm hGc
    have hη' := hηeq
    rw [← hmapeq] at hη'
    have hpull := ae_of_ae_map hGm'.aemeasurable hη'
    calc P {ω | ∃ t, a ^ 2 ≤ t ∧ ‖sleTrace κ B ω t‖ < M}
        ≤ P (toCPath G hGc ⁻¹' transE η (M / a)) := by
          refine measure_mono_ae ?_
          filter_upwards [hpull, hGeq, ae_sleTrace_scale_of_tendsto hB hlimB ha] with ω h1 h2 h3 hω
          obtain ⟨t, ht, htM⟩ := hω
          have ha2 : 0 < a ^ 2 := by positivity
          have hs0 : 0 ≤ t / a ^ 2 := div_nonneg (ha2.le.trans ht) ha2.le
          refine mem_transE_of (hηc _) ((one_le_div ha2).2 ht) ?_
          rw [h1 (mem_Ici.2 hs0), sleTrace_toCPath, sleTrace_congr_of_eq (B := fun t ω =>
              (√((a ^ 2).toNNReal : ℝ))⁻¹ * B ((a ^ 2).toNNReal * t) ω) h2, h3 _ hs0,
            show a ^ 2 * (t / a ^ 2) = t by field_simp, norm_div, Complex.norm_of_nonneg ha.le]
          exact div_lt_div_of_pos_right htM ha
      _ = μ (transE η (M / a)) := by
          rw [← hmapeq, Measure.map_apply hGm' (measurableSet_transE hηm _)]
  have hm : ∀ m : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, ∀ t ≥ T, (m : ℝ) ≤ ‖sleTrace κ B ω t‖ := by
    intro m
    rw [ae_iff]
    refine le_antisymm (ge_of_tendsto' hlimE fun k => ?_) bot_le
    have ha : 0 < ((m : ℝ) + 1) * ((k : ℝ) + 1) := by positivity
    calc P {ω | ¬∃ T : ℝ, ∀ t ≥ T, (m : ℝ) ≤ ‖sleTrace κ B ω t‖}
        ≤ P {ω | ∃ t, (((m : ℝ) + 1) * ((k : ℝ) + 1)) ^ 2 ≤ t ∧ ‖sleTrace κ B ω t‖ < m} := by
          refine measure_mono fun ω hω => ?_
          simp only [Set.mem_ofPred_eq, not_exists, not_forall, not_le] at hω ⊢
          obtain ⟨t, ht, h⟩ := hω ((((m : ℝ) + 1) * ((k : ℝ) + 1)) ^ 2)
          exact ⟨t, ht, h⟩
      _ ≤ μ (transE η (m / (((m : ℝ) + 1) * ((k : ℝ) + 1)))) := key _ ha _
      _ ≤ μ (transE η (1 / ((k : ℝ) + 1))) := by
          refine measure_mono (transE_mono η ?_)
          rw [div_le_div_iff₀ ha (by positivity), one_mul]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  filter_upwards [ae_all_iff.2 hm] with ω h
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨T, hT⟩ := h ⌈b⌉₊
  exact eventually_atTop.2 ⟨T, fun t ht => (Nat.le_ceil b).trans (hT t ht)⟩

end Scaling

/-! ### The trace inputs for `κ ≠ 8` -/

section TraceInputs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A power-rate radial bound on every `[0, N]` gives the radial limit at every time `t ≥ 0`. -/
theorem ae_tendsto_fwdMapInv_of_rpow_bound {κ : ℝ}
    (h : ∃ δ > (0 : ℝ), ∀ᵐ ω ∂P, sleTrace κ B ω 0 = 0 ∧
      ContinuousOn (sleTrace κ B ω) (Ici 0) ∧
      ∀ N : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
        ‖fwdMapInv (drive κ B ω) t (y * I) - sleTrace κ B ω t‖ ≤ C * y ^ δ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * I))
      (𝓝[>] 0) (𝓝 (trace (drive κ B ω) t)) := by
  obtain ⟨δ, hδ, h⟩ := h
  filter_upwards [h] with ω hω t ht
  obtain ⟨C, hC⟩ := hω.2.2 ⌈t⌉₊
  exact tendsto_fwdMapInv_of_rpow_bound hδ (hC t ⟨ht, Nat.le_ceil t⟩)

/-- For `0 < κ`, `κ ≠ 8`, the SLE trace is almost surely the radial limit at every time
(QuantumZipper's `RS.ae_sleTrace_good` for `κ < 8`, `ae_sleTrace_good_of_eight_lt` for `κ > 8`). -/
theorem ae_tendsto_fwdMapInv_of_ne_eight (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ)
    (hκ8 : κ ≠ 8) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * I))
      (𝓝[>] 0) (𝓝 (trace (drive κ B ω) t)) := by
  rcases lt_or_gt_of_ne hκ8 with h8 | h8
  · exact ae_tendsto_fwdMapInv_of_rpow_bound (ae_sleTrace_good hB hκ h8)
  · exact ae_tendsto_fwdMapInv_of_rpow_bound (ae_sleTrace_good_of_eight_lt hB h8)

/-- For `0 < κ`, `κ ≠ 8`, the SLE trace has a measurable continuous version. -/
theorem exists_measurable_sleTrace_of_ne_eight (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ)
    (hκ8 : κ ≠ 8) :
    ∃ η : Ω → ℝ → ℂ, Measurable η ∧ (∀ ω, Continuous (η ω)) ∧
      ∀ᵐ ω ∂P, EqOn (η ω) (sleTrace κ B ω) (Ici 0) := by
  rcases lt_or_gt_of_ne hκ8 with h8 | h8
  · obtain ⟨η, -, hηm, hηc, hηeq⟩ := exists_measurable_sleTrace hB hκ h8
    exact ⟨η, hηm, hηc, hηeq⟩
  · obtain ⟨η, -, hηm, hηc, hηeq⟩ := exists_measurable_sleTrace_of_eight_lt hB h8
    exact ⟨η, hηm, hηc, hηeq⟩

/-- **The scaling step for `κ ≠ 8`**: almost-sure avoidance of `0` by `η([1,∞))` under every
Brownian law on `CPath` implies transience. -/
theorem ae_tendsto_norm_sleTrace_of_avoid_of_ne_eight {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ ≠ 8)
    (hav : ∀ (μ : Measure CPath) [IsProbabilityMeasure μ], IsBrownianReal canonBM μ →
      ∀ᵐ f ∂μ, (0 : ℂ) ∉ closure (sleTrace κ canonBM f '' Ici 1))
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖sleTrace κ B ω t‖) atTop atTop :=
  ae_tendsto_norm_sleTrace_of_avoid
    (fun _ _ hμ => ae_tendsto_fwdMapInv_of_ne_eight hμ hκ hκ8)
    (fun _ _ hμ => exists_measurable_sleTrace_of_ne_eight hμ hκ hκ8) hav hB

end TraceInputs

/-! ### From [RS05, Lemma 7.3] to the avoidance input -/

section Interior

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Avoidance from [RS05, Lemma 7.3] at `t = 1`.** If almost surely the trace is the radial
limit at every time and `K_1 ⊇ ℍ ∩ B(0,ε)` for some `ε > 0`, then almost surely
`0 ∉ closure η([1,∞))`. -/
theorem ae_zero_not_mem_closure_of_ball_subset_sleHull (hB : IsBrownianReal B P) {κ : ℝ}
    (hlim : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * I))
      (𝓝[>] 0) (𝓝 (trace (drive κ B ω) t)))
    (hint : ∀ᵐ ω ∂P, ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull κ B ω 1) :
    ∀ᵐ ω ∂P, (0 : ℂ) ∉ closure (sleTrace κ B ω '' Ici 1) := by
  filter_upwards [hlim, hint, hB.cont, hB.eval_zero_ae_eq_zero] with ω hl hi hc h0
  obtain ⟨ε, hε, hball⟩ := hi
  exact zero_not_mem_closure_trace_image_Ici_one (drive_continuous hc) (drive_zero h0) hε hball
    fun t ht => hl t (zero_le_one.trans ht)

end Interior

/-! ### Transience -/

section Transience

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Transience of the SLE trace for `0 < κ ≤ 4`** ([RS05, Theorem 7.1], the case `κ ≤ 4`):
almost surely `|η(t)| → ∞` as `t → ∞`. The avoidance input is QuantumZipper's
`RS.ae_zero_not_mem_closure_Ici_one` ([RS05, Lemma 7.2] and the boundary correspondence at time
`1`). -/
theorem ae_tendsto_norm_sleTrace_of_le_four (hB : IsBrownianReal B P) [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖sleTrace κ B ω t‖) atTop atTop :=
  ae_tendsto_norm_sleTrace_of_avoid_of_ne_eight hκ (by linarith)
    (fun _ _ hμ => ae_zero_not_mem_closure_Ici_one hκ hκ4 hμ) hB

/-- **Transience of the SLE trace for `0 < κ`, `κ ≠ 8`, conditional on [RS05, Lemma 7.3].**
For `κ ≤ 4` the hypothesis `hint` is not used (`ae_tendsto_norm_sleTrace_of_le_four`). For
`κ > 4` it is [RS05, Lemma 7.3] ("interior", `SLEcont.tex` lines 2304–2376) at `t = 1`: for every
Brownian motion, almost surely the hull `K_1` contains `ℍ ∩ B(0,ε)` for some `ε > 0`. This
conditional form is not [RS05, Theorem 7.1]: Lemma 7.3 is an unproved input (see the module
docstring). -/
theorem ae_tendsto_norm_sleTrace_of_interior (hB : IsBrownianReal B P) [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ ≠ 8)
    (hint : 4 < κ → ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
      {B' : ℝ≥0 → Ω' → ℝ}, IsBrownianReal B' P' →
        ∀ᵐ ω ∂P', ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull κ B' ω 1) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖sleTrace κ B ω t‖) atTop atTop := by
  by_cases hκ4 : κ ≤ 4
  · exact ae_tendsto_norm_sleTrace_of_le_four hB hκ hκ4
  · refine ae_tendsto_norm_sleTrace_of_avoid_of_ne_eight hκ hκ8 (fun _ _ hμ => ?_) hB
    exact ae_zero_not_mem_closure_of_ball_subset_sleHull hμ
      (ae_tendsto_fwdMapInv_of_ne_eight hμ hκ hκ8) (hint (not_le.1 hκ4) hμ)

end Transience

/-! ### The case `κ = 8`, from the statement of the SLE₈ anchor -/

section Eight

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Locally uniform radial convergence to a continuous `γ` (the form of the SLE₈ anchor) gives the
radial limit at every time and the continuity of `t ↦ η(t)` on `ℝ≥0`. -/
theorem trace_good_of_tendstoLocallyUniformly {W : ℝ → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : TendstoLocallyUniformly (fun (y : ℝ) (t : ℝ≥0) => fwdMapInv W t (y * I)) γ (𝓝[>] 0))
    (hγc : Continuous γ) :
    Continuous (fun t : ℝ≥0 => trace W t) ∧ ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (trace W t)) := by
  have hpt : ∀ t : ℝ≥0, Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (γ t)) :=
    fun t => (hγ.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ t)
  have heq : ∀ t : ℝ≥0, trace W t = γ t := fun t => (hpt t).limUnder_eq
  refine ⟨by simpa only [heq] using hγc, fun t ht => ?_⟩
  have h := hpt t.toNNReal
  rw [Real.coe_toNNReal t ht] at h
  have htr : trace W t = γ t.toNNReal := by rw [← heq, Real.coe_toNNReal t ht]
  rwa [htr]

/-- A measurable continuous version of the trace, from the a.s. continuity of `t ↦ η(t)` on `ℝ≥0`
and the a.s. radial limits (any `κ`; mirror of `QuantumZipper.RS.exists_measurable_sleTrace`). -/
theorem exists_measurable_sleTrace_of_tendsto (hB : IsBrownianReal B P) {κ : ℝ}
    (hgood : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => sleTrace κ B ω t) ∧ ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * I)) (𝓝[>] 0)
        (𝓝 (trace (drive κ B ω) t))) :
    ∃ η : Ω → ℝ → ℂ, Measurable η ∧ (∀ ω, Continuous (η ω)) ∧
      ∀ᵐ ω ∂P, EqOn (η ω) (sleTrace κ B ω) (Ici 0) := by
  obtain ⟨B'', hB''m, hB''c, hB''0, -, hae⟩ := exists_good_version0 hB
  have hgood'' : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => sleTrace κ B'' ω t) ∧ ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun y : ℝ => fwdMapInv (drive κ B'' ω) t (y * I)) (𝓝[>] 0)
        (𝓝 (trace (drive κ B'' ω) t)) := by
    filter_upwards [hgood, hae] with ω h h'
    have hdr : drive κ B'' ω = drive κ B ω := funext fun t => by simp [drive, h']
    rw [sleTrace_congr_of_eq h' κ, hdr]
    exact h
  obtain ⟨S, hS, hSm, hSp⟩ := hgood''.exists_measurable_mem
  set η : Ω → ℝ → ℂ := fun ω t => S.indicator (fun ω' => sleTrace κ B'' ω' (max t 0)) ω
    with hηdef
  have hy : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  have hηm : Measurable η := by
    refine measurable_pi_iff.2 fun t => ?_
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) => S.indicator
      (fun ω' => fwdMapInv (drive κ B'' ω') (max t 0) (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)))
      (fun n => ?_) (tendsto_pi_nhds.2 fun ω => ?_)
    · refine Measurable.indicator ?_ hSm
      refine measurable_fwdMapInv_drive hB''m hB''c hB''0 κ (le_max_right t 0) ?_
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      positivity
    · by_cases hω : ω ∈ S
      · simp only [hηdef, indicator_of_mem hω]
        exact ((hSp ω hω).2 (max t 0) (le_max_right t 0)).comp hy
      · simp only [hηdef, indicator_of_notMem hω]
        exact tendsto_const_nhds
  refine ⟨η, hηm, fun ω => ?_, ?_⟩
  · by_cases hω : ω ∈ S
    · have : η ω = (fun t : ℝ≥0 => sleTrace κ B'' ω t) ∘ Real.toNNReal := by
        funext t
        simp only [hηdef, indicator_of_mem hω, Function.comp_apply, Real.coe_toNNReal']
      rw [this]
      exact (hSp ω hω).1.comp continuous_real_toNNReal
    · have : η ω = fun _ => 0 := by
        funext t
        simp only [hηdef, indicator_of_notMem hω]
      rw [this]
      exact continuous_const
  · filter_upwards [hS, hae] with ω hω h' t ht
    simp only [hηdef, indicator_of_mem hω, max_eq_left (mem_Ici.1 ht)]
    rw [sleTrace_congr_of_eq h' κ]

/-- **Transience for `κ = 8`, conditional on the SLE₈ anchor and on [RS05, Lemma 7.3] at `κ = 8`.**
`htrace` is the statement of the frozen anchor `InteractingSLE.SLE8.ae_exists_continuous_trace`
(SLE₈ note, Theorem 1.1; not yet proved), for Brownian motions on spaces in `Type`; `hint` is the
interior property `K_1 ⊇ ℍ ∩ B(0,ε)` at `κ = 8` (Lemma 7.3 is stated for `κ ≠ 8`; the Update after
[RS05, Corollary 7.4], `SLEcont.tex` lines 2418–2423, extends Theorem 7.1 to `κ = 8` with proofs "otherwise the
same", which includes Lemma 7.3; not proved here). -/
theorem ae_tendsto_norm_sleTrace_eight_of_interior (hB : IsBrownianReal B P)
    [IsProbabilityMeasure P]
    (htrace : ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {B' : ℝ≥0 → Ω' → ℝ},
      IsBrownianReal B' P' →
      ∀ᵐ ω ∂P', ∃ γ : ℝ≥0 → ℂ,
        TendstoLocallyUniformly
            (fun (y : ℝ) (t : ℝ≥0) =>
              QuantumZipper.fwdMapInv (QuantumZipper.drive 8 B' ω) t (y * Complex.I))
            γ (𝓝[>] 0) ∧
          Continuous γ ∧ (∀ t, γ t ∈ QuantumZipper.Hbar) ∧ γ 0 = 0 ∧
          ∀ t : ℝ≥0,
            (∃ z ∈ QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B' ω) t,
                connectedComponentIn (QuantumZipper.H \ γ '' Icc 0 t) z =
                  QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B' ω) t) ∧
              ¬ Bornology.IsBounded
                (QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B' ω) t))
    (hint : ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {B' : ℝ≥0 → Ω' → ℝ},
      IsBrownianReal B' P' →
        ∀ᵐ ω ∂P', ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull 8 B' ω 1) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖sleTrace 8 B ω t‖) atTop atTop := by
  have hgood : ∀ (μ : Measure CPath) [IsProbabilityMeasure μ], IsBrownianReal canonBM μ →
      ∀ᵐ f ∂μ, Continuous (fun t : ℝ≥0 => sleTrace 8 canonBM f t) ∧ ∀ t : ℝ, 0 ≤ t →
        Tendsto (fun y : ℝ => fwdMapInv (drive 8 canonBM f) t (y * I)) (𝓝[>] 0)
          (𝓝 (trace (drive 8 canonBM f) t)) := fun μ _ hμ =>
    (htrace hμ).mono fun _ ⟨_, h1, h2, _⟩ => trace_good_of_tendstoLocallyUniformly h1 h2
  have hlim : ∀ (μ : Measure CPath) [IsProbabilityMeasure μ], IsBrownianReal canonBM μ →
      ∀ᵐ f ∂μ, ∀ t : ℝ, 0 ≤ t → Tendsto (fun y : ℝ => fwdMapInv (drive 8 canonBM f) t (y * I))
        (𝓝[>] 0) (𝓝 (trace (drive 8 canonBM f) t)) := fun μ _ hμ =>
    (hgood μ hμ).mono fun _ h => h.2
  exact ae_tendsto_norm_sleTrace_of_avoid hlim
    (fun μ _ hμ => exists_measurable_sleTrace_of_tendsto hμ (hgood μ hμ))
    (fun μ _ hμ => ae_zero_not_mem_closure_of_ball_subset_sleHull hμ (hlim μ hμ) (hint hμ)) hB

end Eight

end InteractingSLE
