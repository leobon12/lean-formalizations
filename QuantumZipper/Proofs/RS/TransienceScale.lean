import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# EXT-RS node TRANS: the scaling step of transience

Rohde–Schramm, *Basic properties of SLE*, Ann. of Math. 161 (2005), proof of Theorem 7.1
(p. 34 of `literature/math_0106036.pdf`): "the scaling property of SLE shows that for all
`t > 0`, `P[K_t ⊃ {|z| < r₀ √t}] ≥ 1 − ε` … This implies `P[∃ t' > t : |γ(t')| < r₀ √t] < ε`",
with (for `κ ≤ 4`) "`0 ∉ closure γ[1,∞)` a.s." in place of `K_1 ⊃ ball`.

* `ae_sleTrace_scale`: the trace of `a⁻¹ B(a² ·)` is `s ↦ η(a² s)/a` a.s. (P3(d) `trace_scale`
  plus TR4 `ae_sleTrace_good`);
* `transience_of_avoid_zero`: if a.s. `0 ∉ closure (η [1,∞))` for every Brownian motion, then
  a.s. `|η(t)| → ∞`.

The bookkeeping follows RS's scaling argument with the input `0 ∉ closure η[1,∞)`: all scaled
motions have the same law `μ` on `CPath`; under `μ` the events
`E_r = {∃ q ∈ ℚ, q > 1, |η̃(q)| < r}` decrease to a null set; and
`P[∃ t ≥ a², |η(t)| < M] ≤ μ(E_{M/a})`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RS

/-- **Scaling of the SLE trace (P3(d), a.s. form).** For `a > 0`, almost surely the trace driven
by `a⁻¹ B(a² ·)` is `s ↦ η(a² s)/a` on `[0,∞)`. -/
theorem ae_sleTrace_scale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s →
      sleTrace κ (fun t ω => (√((a ^ 2).toNNReal : ℝ))⁻¹ * B ((a ^ 2).toNNReal * t) ω) ω s =
        sleTrace κ B ω (a ^ 2 * s) / a := by
  obtain ⟨δ, hδ, hgood⟩ := ae_sleTrace_good hB hκ hκ8
  filter_upwards [hgood, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hc h0 s hs
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hdr : drive κ (fun t ω => (√((a ^ 2).toNNReal : ℝ))⁻¹ * B ((a ^ 2).toNNReal * t) ω) ω =
      fun r => drive κ B ω (a ^ 2 * r) / a := by
    funext r
    simp only [drive, Real.coe_toNNReal _ (sq_nonneg a), Real.sqrt_sq ha.le,
      Real.toNNReal_mul (sq_nonneg a)]
    field_simp
  obtain ⟨C, hC⟩ := hω.2.2 ⌈a ^ 2 * s⌉₊
  have hp := tendsto_fwdMapInv_of_rpow_bound hδ (hC _ ⟨by positivity, Nat.le_ceil _⟩)
  have h := (trace_scale hW hW0 ha hs hp).2
  unfold sleTrace
  rw [hdr, h]

/-- The events `E_r = {∃ q ∈ ℚ, q > 1, ‖η̃ q‖ < r}`. -/
def transE {α : Type*} (η : α → ℝ → ℂ) (r : ℝ) : Set α :=
  {f | ∃ q : ℚ, 1 < (q : ℝ) ∧ ‖η f q‖ < r}

theorem measurableSet_transE {α : Type*} [MeasurableSpace α] {η : α → ℝ → ℂ}
    (hη : Measurable η) (r : ℝ) : MeasurableSet (transE η r) := by
  have : transE η r = ⋃ q : ℚ, {_f : α | 1 < (q : ℝ)} ∩ {f | ‖η f q‖ < r} := by
    ext f; simp [transE]
  rw [this]
  exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
    (measurableSet_lt ((measurable_pi_apply (q : ℝ)).comp hη).norm measurable_const)

theorem transE_mono {α : Type*} (η : α → ℝ → ℂ) {r r' : ℝ} (h : r ≤ r') :
    transE η r ⊆ transE η r' := fun _ ⟨q, hq, hn⟩ => ⟨q, hq, hn.trans_le h⟩

/-- Continuity turns a real time `t ≥ 1` into a rational time `q > 1`. -/
theorem mem_transE_of {α : Type*} {η : α → ℝ → ℂ} {f : α} (hc : Continuous (η f)) {t r : ℝ}
    (ht : 1 ≤ t) (hr : ‖η f t‖ < r) : f ∈ transE η r := by
  have hU : IsOpen ({s | ‖η f s‖ < r} ∩ Ioi 1) :=
    (isOpen_lt hc.norm continuous_const).inter isOpen_Ioi
  have hev : ∀ᶠ s in 𝓝[>] t, ‖η f s‖ < r ∧ t < s :=
    ((hc.norm.continuousAt.eventually_lt continuousAt_const hr).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨s, hs1, hs2⟩ := hev.exists
  obtain ⟨q, hq1, hq2⟩ :=
    Rat.denseRange_cast.exists_mem_open hU ⟨s, hs1, lt_of_le_of_lt ht hs2⟩
  exact ⟨q, hq2, hq1⟩

/-- Under `0 ∉ closure (η [1,∞))` a.s., the events `E_{1/(k+1)}` have measure tending to `0`. -/
theorem tendsto_measure_transE {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {η γ : α → ℝ → ℂ} (hη : Measurable η)
    (heq : ∀ᵐ f ∂μ, EqOn (η f) (γ f) (Ici 0))
    (hav : ∀ᵐ f ∂μ, (0 : ℂ) ∉ closure (γ f '' Ici 1)) :
    Tendsto (fun k : ℕ => μ (transE η (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
  have hanti : Antitone fun k : ℕ => transE η (1 / ((k : ℝ) + 1)) := by
    intro k k' hk
    refine transE_mono η ?_
    gcongr
  have h := tendsto_measure_iInter_atTop
    (fun k : ℕ => (measurableSet_transE hη (1 / ((k : ℝ) + 1))).nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  have hnull : μ (⋂ k : ℕ, transE η (1 / ((k : ℝ) + 1))) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (heq.and hav))
    intro f hf hgood
    refine hgood.2 (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨q, hq, hn⟩ := mem_iInter.1 hf k
    refine ⟨η f q, ⟨q, mem_Ici.2 hq.le, (hgood.1 (mem_Ici.2 (by linarith))).symm⟩, ?_⟩
    rw [dist_zero_left]
    exact hn.trans hk
  rw [hnull] at h
  exact h

/-- **Transience from avoidance of `0` (RS Thm 7.1, scaling step, p. 34).** If for every
Brownian motion a.s. `0 ∉ closure (η [1,∞))`, then a.s. `|η(t)| → ∞`. -/
theorem transience_of_avoid_zero {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hav : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      ∀ᵐ ω ∂P, (0 : ℂ) ∉ closure (sleTrace κ B ω '' Set.Ici 1))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖sleTrace κ B ω t‖) atTop atTop := by
  obtain ⟨G0, hG0m, hG0c, -, hG0br, -⟩ := exists_good_version0 hB
  set μ : Measure CPath := P.map (toCPath G0 hG0c) with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hcan : IsBrownianReal canonBM μ :=
    isBrownianReal_canonBM hG0br.toIsPreBrownianReal hG0m hG0c
  obtain ⟨η, -, hηm, hηc, hηeq⟩ := exists_measurable_sleTrace hcan hκ hκ8
  have hlim := tendsto_measure_transE hηm hηeq (hav μ canonBM hcan)
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
          filter_upwards [hpull, hGeq, ae_sleTrace_scale hB hκ hκ8 ha] with ω h1 h2 h3 hω
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
    refine le_antisymm (ge_of_tendsto' hlim fun k => ?_) bot_le
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
          rw [div_le_div_iff₀ ha (by positivity)]
          nlinarith
  filter_upwards [ae_all_iff.2 hm] with ω h
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨T, hT⟩ := h ⌈b⌉₊
  exact eventually_atTop.2 ⟨T, fun t ht => (Nat.le_ceil b).trans (hT t ht)⟩

end RS
end QuantumZipper
