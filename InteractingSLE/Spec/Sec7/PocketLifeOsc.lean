/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.CouplingFrozen

/-!
# The oscillation step at a finite lifetime: a localized `L²`-bounded martingale has a left limit

Packet PROVE-STRIPSYS13. Proof of Aux. lemma 125 (`source/spec/p385-432.md` L224–L232, p. 397): "Stop before a fixed
coordinate bound or at `ζ`, whichever occurs first. On the latter event, bounded monotone force coordinates give
finite reciprocal integrals and finite coordinate limits; the Brownian driver has its continuous limit."

The pathwise half of Aux. lemma 125 (`Aux125.lifetime_eq_top_of_not_isBounded`, `PocketLife.capLife_eq_top_of_driverEq`)
needs the driving noise continuous **up to** a finite lifetime. When the noise `M` is only known before the lifetime
`T` (the setting of Aux. lemma 122 at announced lifetimes, PROVE-STRIPSYS5/6), its left limit at `T` is the
oscillation argument flagged in PROVE-STRIPSYS5 §5 item 2: with announcing stopping times `σₙ < T`, the stopped
processes `M^{σₙ}` bounded martingales and `E M²_{σₙ ∧ N}` bounded in `n`, the orthogonality
`E (M_{σₘ∧N} − M_{σₙ∧N})² = E M²_{σₘ∧N} − E M²_{σₙ∧N}` and Doob's maximal inequality make the oscillation of `M` on
`[σₙ, T)` small with high probability, uniformly in the horizon. This is the argument of
`WangWu.exists_martingale_frozenMean` (PROVE-WW-A), stated here for an arbitrary process.

## Main results

* **`ae_exists_tendsto_of_announcing`**: almost surely, at a finite `T` the process has a finite left limit;
* `bddAbove_integral_sq_of_martingale_sq_sub`: the `L²` bound from the martingale `(M^{σₙ})² − κ (t ∧ σₙ)`
  (quadratic variation `κ t`, as for `√κ` times a Brownian motion);
* **`exists_continuous_extension_of_tendsto`**: the noise frozen at its left limit after `T` is continuous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketLife

open WangWu (measureReal_iSup_ge_le integral_sq_sub_eq_of_stopped exists_tendsto_nhdsLT_of_osc)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The oscillation step** (proof of Aux. lemma 125, "the Brownian driver has its continuous limit"): let `σₙ` be
stopping times strictly before `T`, nondecreasing in `n` and exhausting `[0, T)`, and let `M` be continuous on `[0, T)`
for every `ω`, with each stopped process `M^{σₙ}` a bounded martingale and `E M²_{σₙ ∧ N}` bounded in `n` for every
horizon `N`. Then almost surely, if `T` is finite, `M` has a finite left limit at `T`. -/
theorem ae_exists_tendsto_of_announcing [IsProbabilityMeasure P] {T : Ω → ℝ≥0∞} {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0)) (hσT : ∀ n ω, (σ n ω : ℝ≥0∞) < T ω)
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσex : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < T ω → ∃ n, t ≤ σ n ω)
    {M : ℝ≥0 → Ω → ℝ} (hMc : ∀ ω, ContinuousOn (M · ω) {t | (t : ℝ≥0∞) < T ω})
    (hMb : ∀ n, ∃ C, ∀ ω t, t ≤ σ n ω → |M t ω| ≤ C)
    (hMm : ∀ n, Martingale (fun t ω => M (min t (σ n ω)) ω) 𝓕 P)
    (hL2 : ∀ N : ℝ≥0, BddAbove (range fun n => ∫ ω, M (min N (σ n ω)) ω ^ 2 ∂P)) :
    ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∃ L, Tendsto (M · ω) (𝓝[<] (T ω).toNNReal) (𝓝 L) := by
  choose C hC using hMb
  set Y : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω => M (min t (σ n ω)) ω with hYdef
  -- the stopped processes are continuous and bounded
  have hYc : ∀ n ω, Continuous (Y n · ω) := fun n ω =>
    (hMc ω).comp_continuous (continuous_id.min continuous_const) fun t =>
      lt_of_le_of_lt (by exact_mod_cast min_le_right t (σ n ω)) (hσT n ω)
  have hYrc : ∀ n ω t, ContinuousWithinAt (Y n · ω) (Ici t) t := fun n ω t =>
    (hYc n ω).continuousAt.continuousWithinAt
  have hYb : ∀ n t ω, |Y n t ω| ≤ C n := fun n t ω => hC n ω _ (min_le_right _ _)
  have hconsist : ∀ n m, n ≤ m → ∀ (N : ℝ≥0) ω, Y n N ω = Y m (min N (σ n ω)) ω := fun n m hnm N ω => by
    simp only [hYdef, min_assoc, min_eq_left (hσm ω hnm)]
  have hstab : ∀ n m, n ≤ m → ∀ t ω, Y n (min t (σ m ω)) ω = Y n t ω := fun n m hnm t ω => by
    simp only [hYdef, min_assoc, min_eq_right (hσm ω hnm)]
  -- one horizon `N`
  have hN : ∀ N : ℝ≥0, ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ n, ∀ m, n ≤ m →
      (⨆ i : Iic N, ‖Y m i ω - Y n i ω‖) < 1 / ((k : ℝ) + 1) := by
    intro N
    set a : ℕ → ℝ := fun n => ∫ ω, Y n N ω ^ 2 ∂P with hadef
    have horth : ∀ n m, n ≤ m → ∫ ω, (Y m N ω - Y n N ω) ^ 2 ∂P = a m - a n := fun n m hnm =>
      integral_sq_sub_eq_of_stopped (hMm m) (hYrc m) (hYb m) (hσ n) (hconsist n m hnm N)
    have ha_mono : Monotone a := fun n m hnm => by
      have h := horth n m hnm
      have : 0 ≤ ∫ ω, (Y m N ω - Y n N ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
      linarith
    have ha_bdd : BddAbove (range a) := hL2 N
    have ha_tend : Tendsto a atTop (𝓝 (⨆ n, a n)) := tendsto_atTop_ciSup ha_mono ha_bdd
    set osc : ℕ → ℕ → Ω → ℝ := fun n m ω => ⨆ i : Iic N, ‖Y m i ω - Y n i ω‖ with hoscdef
    have hosc_bdd : ∀ n m ω, BddAbove (range fun i : Iic N => ‖Y m i ω - Y n i ω‖) := fun n m ω =>
      ⟨C m + C n, by
        rintro _ ⟨i, rfl⟩
        show ‖Y m i ω - Y n i ω‖ ≤ C m + C n
        rw [Real.norm_eq_abs]
        have := abs_sub (Y m i ω) (Y n i ω)
        linarith [hYb m i ω, hYb n i ω]⟩
    have hosc_mono : ∀ n m m' ω, n ≤ m → m ≤ m' → osc n m ω ≤ osc n m' ω := by
      intro n m m' ω hnm hmm'
      refine ciSup_le fun i => ?_
      refine le_ciSup_of_le (hosc_bdd n m' ω)
        ⟨min i (σ m ω), Set.mem_Iic.2 ((min_le_left _ _).trans (Set.mem_Iic.1 i.2))⟩ ?_
      show ‖Y m i ω - Y n i ω‖ ≤ ‖Y m' (min i (σ m ω)) ω - Y n (min i (σ m ω)) ω‖
      rw [← hconsist m m' hmm' i ω, hstab n m hnm i ω]
    have hprob : ∀ n m, n ≤ m → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        P.real {ω | ε ≤ osc n m ω} ≤ ((a m - a n) / δ + δ) / (2 * ε) := by
      intro n m hnm ε δ hε hδ
      have hD := (hMm m).sub (hMm n)
      have hDrc : ∀ ω, IsRightContinuous ((Y m - Y n) · ω) := fun ω t =>
        (((hYc m ω).sub (hYc n ω)).continuousAt (x := t)).continuousWithinAt
      have hDb : ∀ ω, |(Y m - Y n) N ω| ≤ C m + C n := fun ω => by
        simp only [Pi.sub_apply]
        have := abs_sub (Y m N ω) (Y n N ω)
        linarith [hYb m N ω, hYb n N ω]
      have hDint : Integrable (fun ω => (Y m - Y n) N ω ^ 2) P := by
        refine Integrable.of_bound ((((hMm m).1 N).mono (Filtration.le _ N)).aestronglyMeasurable.sub
          (((hMm n).1 N).mono (Filtration.le _ N)).aestronglyMeasurable |>.pow 2) ((C m + C n) ^ 2)
          (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hDb ω) 2
      have h := measureReal_iSup_ge_le hD hDrc N hε hδ hDint
      simp only [Pi.sub_apply] at h
      rwa [horth n m hnm] at h
    rw [ae_all_iff]
    intro k
    set ε : ℝ := 1 / ((k : ℝ) + 1) with hεdef
    have hε : 0 < ε := by positivity
    set Bad : Set Ω := ⋂ n, ⋃ j, {ω | ε ≤ osc n (n + j) ω} with hBad
    have hBadle : ∀ n δ, 0 < δ → P.real Bad ≤ (((⨆ n, a n) - a n) / δ + δ) / (2 * ε) := by
      intro n δ hδ
      have hmonoS : Monotone fun j => {ω | ε ≤ osc n (n + j) ω} := fun j j' hjj' ω hω =>
        le_trans hω (hosc_mono n (n + j) (n + j') ω (Nat.le_add_right _ _) (by omega))
      have hbound : 0 ≤ (((⨆ n, a n) - a n) / δ + δ) / (2 * ε) := by
        have : a n ≤ ⨆ n, a n := le_ciSup ha_bdd n
        have : 0 ≤ (⨆ n, a n) - a n := by linarith
        positivity
      have hU : P (⋃ j, {ω | ε ≤ osc n (n + j) ω}) ≤
          ENNReal.ofReal ((((⨆ n, a n) - a n) / δ + δ) / (2 * ε)) := by
        rw [hmonoS.measure_iUnion]
        refine iSup_le fun j => ?_
        rw [← ofReal_measureReal (measure_ne_top _ _)]
        refine ENNReal.ofReal_le_ofReal ((hprob n (n + j) (Nat.le_add_right _ _) ε δ hε hδ).trans ?_)
        have : a (n + j) ≤ ⨆ n, a n := le_ciSup ha_bdd _
        gcongr
      have h1 : P.real Bad ≤ P.real (⋃ j, {ω | ε ≤ osc n (n + j) ω}) :=
        measureReal_mono (iInter_subset _ n)
      exact h1.trans (ENNReal.toReal_le_of_le_ofReal hbound hU)
    have hBad0 : P.real Bad ≤ 0 := by
      by_contra hpos
      push Not at hpos
      set p := P.real Bad
      have hδ : 0 < ε * p := mul_pos hε hpos
      have hlim : Tendsto (fun n => (((⨆ n, a n) - a n) / (ε * p) + ε * p) / (2 * ε)) atTop
          (𝓝 ((((⨆ n, a n) - (⨆ n, a n)) / (ε * p) + ε * p) / (2 * ε))) :=
        (((tendsto_const_nhds.sub ha_tend).div_const _).add_const _).div_const _
      have := ge_of_tendsto' hlim fun n => hBadle n (ε * p) hδ
      rw [sub_self, zero_div, zero_add] at this
      have : p ≤ p / 2 := by
        calc p ≤ ε * p / (2 * ε) := this
          _ = p / 2 := by field_simp
      linarith
    have hBadz : P Bad = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm hBad0 measureReal_nonneg)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hBadz] with ω hω
    simp only [hBad, mem_iInter, mem_iUnion, mem_ofPred_eq, not_forall, not_exists, not_le] at hω
    obtain ⟨n, hn⟩ := hω
    refine ⟨n, fun m hnm => ?_⟩
    have := hn (m - n)
    rwa [Nat.add_sub_cancel' hnm] at this
  -- all horizons at once, then the pathwise conclusion
  filter_upwards [ae_all_iff.2 fun N : ℕ => hN N] with ω hω hT
  obtain ⟨N, hN'⟩ := exists_nat_ge (T ω).toNNReal
  have hTN : (T ω).toNNReal ≤ (N : ℝ≥0) := hN'
  have hTe : (((T ω).toNNReal : ℝ≥0) : ℝ≥0∞) = T ω := ENNReal.coe_toNNReal hT
  have hρs : ∀ n, σ n ω < (T ω).toNNReal := fun n => by
    have := hσT n ω
    rw [← hTe] at this
    exact_mod_cast this
  refine exists_tendsto_nhdsLT_of_osc hρs fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨n, hn⟩ := hω N k
  refine ⟨n, fun r hr hrs => ?_⟩
  have hrT : (r : ℝ≥0∞) < T ω := by rw [← hTe]; exact_mod_cast hrs
  obtain ⟨m₀, hm₀⟩ := hσex ω r hrT
  set m := max m₀ n
  have hrm : r ≤ σ m ω := hm₀.trans (hσm ω (le_max_left _ _))
  have hrN : r ≤ (N : ℝ≥0) := hrs.le.trans hTN
  have h1 : Y m r ω = M r ω := by simp only [hYdef, min_eq_left hrm]
  have h2 : Y n r ω = M (σ n ω) ω := by simp only [hYdef, min_eq_right hr]
  have hosc : |M r ω - M (σ n ω) ω| ≤ ⨆ i : Iic (N : ℝ≥0), ‖Y m i ω - Y n i ω‖ := by
    rw [← h1, ← h2, ← Real.norm_eq_abs]
    refine le_ciSup (f := fun i : Iic (N : ℝ≥0) => ‖Y m i ω - Y n i ω‖) ⟨C m + C n, ?_⟩ ⟨r, hrN⟩
    rintro _ ⟨i, rfl⟩
    show ‖Y m i ω - Y n i ω‖ ≤ C m + C n
    rw [Real.norm_eq_abs]
    have := abs_sub (Y m i ω) (Y n i ω)
    linarith [hYb m i ω, hYb n i ω]
  exact (hosc.trans_lt ((hn m (le_max_right _ _)).trans hk)).le

/-- **The `L²` bound from the quadratic variation**: if `(M^{σₙ})² − κ (t ∧ σₙ)` is a martingale (`κ ≥ 0`), then
`E M²_{σₙ ∧ N} = E M₀² + κ E (N ∧ σₙ) ≤ E M₀² + κ N` for every `n`. -/
theorem bddAbove_integral_sq_of_martingale_sq_sub [IsProbabilityMeasure P] {σ : ℕ → Ω → ℝ≥0}
    {M : ℝ≥0 → Ω → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hint : ∀ n (N : ℝ≥0), Integrable (fun ω => M (min N (σ n ω)) ω ^ 2) P)
    (hQ : ∀ n, Martingale (fun t ω => M (min t (σ n ω)) ω ^ 2 - κ * ((min t (σ n ω) : ℝ≥0) : ℝ)) 𝓕 P)
    (N : ℝ≥0) : BddAbove (range fun n => ∫ ω, M (min N (σ n ω)) ω ^ 2 ∂P) := by
  refine ⟨∫ ω, M 0 ω ^ 2 ∂P + κ * N, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hYi := (hQ n).integrable N
  have he := (hQ n).setIntegral_eq (show (0 : ℝ≥0) ≤ N from zero_le) (s := univ) MeasurableSet.univ
  simp only [setIntegral_univ, zero_min, NNReal.coe_zero, mul_zero, sub_zero] at he
  have hci : Integrable (fun ω => κ * ((min N (σ n ω) : ℝ≥0) : ℝ)) P :=
    ((hint n N).sub hYi).congr (Eventually.of_forall fun ω => by simp)
  have hsplit : ∫ ω, M (min N (σ n ω)) ω ^ 2 ∂P =
      ∫ ω, (M (min N (σ n ω)) ω ^ 2 - κ * ((min N (σ n ω) : ℝ≥0) : ℝ)) ∂P +
        ∫ ω, κ * ((min N (σ n ω) : ℝ≥0) : ℝ) ∂P := by
    rw [← integral_add hYi hci]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp)
  have hb : ∫ ω, κ * ((min N (σ n ω) : ℝ≥0) : ℝ) ∂P ≤ κ * N := by
    have := integral_mono hci (integrable_const (κ * (N : ℝ))) fun ω =>
      mul_le_mul_of_nonneg_left (show ((min N (σ n ω) : ℝ≥0) : ℝ) ≤ N from
        NNReal.coe_le_coe.2 (min_le_left _ _)) hκ
    simpa using this
  show ∫ ω, M (min N (σ n ω)) ω ^ 2 ∂P ≤ _
  rw [hsplit, ← he]
  linarith

/-- **The noise frozen at its left limit is continuous**: a function continuous on `[0, T)` with a left limit `L` at
`T` becomes continuous on `[0, ∞)` when it is set to `L` from `T` on. -/
theorem continuous_extend_of_tendsto {f : ℝ≥0 → ℝ} {T : ℝ≥0} (hf : ContinuousOn f (Iio T)) {L : ℝ}
    (hL : Tendsto f (𝓝[<] T) (𝓝 L)) : Continuous fun t => if t < T then f t else L := by
  classical
  set g : ℝ≥0 → ℝ := fun t => if t < T then f t else L with hg
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases lt_trichotomy t T with htT | rfl | hTt
  · refine ((hf.continuousAt (Iio_mem_nhds htT))).congr ?_
    filter_upwards [Iio_mem_nhds htT] with s hs
    simp only [hg, show s < T from hs, ↓reduceIte]
  · refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
    · rw [← continuousWithinAt_Iio_iff_Iic]
      show Tendsto g (𝓝[<] t) (𝓝 (g t))
      rw [show g t = L by simp only [hg, lt_irrefl, ↓reduceIte]]
      refine hL.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [hg, show s < t from hs, ↓reduceIte]
    · show Tendsto g (𝓝[≥] t) (𝓝 (g t))
      rw [show g t = L by simp only [hg, lt_irrefl, ↓reduceIte]]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [hg, not_lt.2 (show t ≤ s from hs), ↓reduceIte]
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ≥0 => L) t).congr ?_
    filter_upwards [Ioi_mem_nhds hTt] with s hs
    simp only [hg, not_lt.2 (le_of_lt (show T < s from hs)), ↓reduceIte]

end InteractingSLE.Sec7.PocketLife
