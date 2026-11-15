/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RectLawLimit
import InteractingSLE.Spec.ZhanGT4.A1CanonFactor
import InteractingSLE.Spec.Coupling.WholeField3Brown
import InteractingSLE.Spec.ZhanGT4.A1CoreFibre

/-!
# Zhan's A.1: the continuous image noise through the image lifetime, up to a null set

Packet PROVE-A1-RECTLAW. The image noise `N` of A.1's rectangle construction (the compensated residual of the image
data) is record-local, continuous before each cap `S m`, and a Brownian motion stopped at each cap; the caps exhaust the
image lifetime only from below. A1-CANON's canonical layer asks for a noise continuous on all of `ℝ≥0` at every sample.
On one probability space with a filtration that contains the null sets, this file provides it:

* `capGood N c`: the measurable set of samples where the stopped noises `t ↦ N (t ∧ c n)` are uniformly Cauchy on every
  `[0, K]` (rational times; `c` the running maxima of the caps);
* `capNoiseExt N c t ω`: on `capGood`, the uniform limit of the stopped noises; `0` elsewhere;
* **`continuous_capNoiseExt`** (every sample), `capNoiseExt_zero`, **`capNoiseExt_eq`** (on `capGood`, equal to `N`
  before every cap), **`measurable_capNoiseExt`** (adapted to the null augmentation of `𝓗`);
* **`ae_mem_capGood`**: `capGood` has full measure when `N` is a stopped Brownian motion at every cap
  (`ae_cauchy_of_isStoppedBM`);
* `IsStoppedBM.max_of_continuousOn`, `isStoppedBM_capMax_of_continuousOn`: A1-CANON's cap patching with continuity
  before the caps only;
* **`isStoppedBM_capNoiseExt`**: the masked noise is a stopped Brownian motion at every cap for the null augmentation.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RectLaw

open A1Canon

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ}

/-! ### Cap patching with continuity before the caps -/

section Patch

/-- The stopped Wald exponential is continuous in time when the noise is continuous before the cap. -/
theorem continuous_stopExp_of_continuousOn {S : Ω → ℝ≥0} {ω : Ω} (hNc : ContinuousOn (N · ω) (Icc 0 (S ω)))
    (a : ℝ) : Continuous fun t => stopExp a N S t ω := by
  have hc : Continuous fun t : ℝ≥0 => N (min t (S ω)) ω :=
    hNc.comp_continuous (continuous_id.min continuous_const) fun _ => ⟨bot_le, min_le_right _ _⟩
  exact Real.continuous_exp.comp ((hc.const_mul a).sub
    (((NNReal.continuous_coe.comp (continuous_id.min continuous_const)).const_mul (a ^ 2)).div_const 2))

/-- **Two caps patch to their maximum** (`IsStoppedBM.max` with continuity before the caps only). -/
theorem IsStoppedBM.max_of_continuousOn [IsFiniteMeasure P] {S S' : Ω → ℝ≥0} (h : IsStoppedBM P 𝓗 N S)
    (h' : IsStoppedBM P 𝓗 N S') (hS' : IsStoppingTime 𝓗 fun ω => (S' ω : WithTop ℝ≥0))
    (hNc : ∀ ω, ContinuousOn (N · ω) (Icc 0 (S ω))) : IsStoppedBM P 𝓗 N fun ω => max (S ω) (S' ω) := by
  intro a
  rw [stopExp_max, stopExp_min]
  exact ((h a).add (h' a)).sub (InteractingSLE.Martingale.stoppedProcess_of_rightContinuous (h a)
    (fun ω t => (continuous_stopExp_of_continuousOn (hNc ω) a).continuousWithinAt) hS')

theorem continuousOn_capMax {S : ℕ → Ω → ℝ≥0} (hNc : ∀ m ω, ContinuousOn (N · ω) (Icc 0 (S m ω))) (n : ℕ)
    (ω : Ω) : ContinuousOn (N · ω) (Icc 0 (capMax S n ω)) := by
  induction n with
  | zero => simpa only [capMax_zero] using hNc 0 ω
  | succ n ih =>
    rw [capMax_succ]
    rcases le_total (capMax S n ω) (S (n + 1) ω) with h | h
    · rw [max_eq_right h]; exact hNc (n + 1) ω
    · rw [max_eq_left h]; exact ih

/-- **Finitely many caps patch to their running maximum** (continuity before the caps only). -/
theorem isStoppedBM_capMax_of_continuousOn [IsFiniteMeasure P] {S : ℕ → Ω → ℝ≥0}
    (h : ∀ m, IsStoppedBM P 𝓗 N (S m)) (hS : ∀ m, IsStoppingTime 𝓗 fun ω => (S m ω : WithTop ℝ≥0))
    (hNc : ∀ m ω, ContinuousOn (N · ω) (Icc 0 (S m ω))) (n : ℕ) : IsStoppedBM P 𝓗 N (capMax S n) := by
  induction n with
  | zero =>
    have e : capMax S 0 = S 0 := funext fun ω => capMax_zero S ω
    rw [e]; exact h 0
  | succ n ih =>
    have e : capMax S (n + 1) = fun ω => max (capMax S n ω) (S (n + 1) ω) := funext fun ω => capMax_succ S n ω
    rw [e]
    exact IsStoppedBM.max_of_continuousOn ih (h (n + 1)) (hS (n + 1)) (continuousOn_capMax hNc n)

end Patch

/-! ### The good set and the masked noise -/

section Mask

variable {c : ℕ → Ω → ℝ≥0}

/-- **The samples where the stopped noises are uniformly Cauchy on every `[0, K]`** (checked at rational times). -/
def capGood (N : ℝ≥0 → Ω → ℝ) (c : ℕ → Ω → ℝ≥0) : Set Ω :=
  {ω | ∀ K j : ℕ, ∃ n₀, ∀ n, n₀ ≤ n → ∀ q : ℚ, (q : ℝ).toNNReal ≤ K →
    |N (min (q : ℝ).toNNReal (c n ω)) ω - N (min (q : ℝ).toNNReal (c n₀ ω)) ω| ≤ 1 / ((j : ℝ) + 1)}

theorem measurableSet_capGood (hm : ∀ n (t : ℝ≥0), Measurable fun ω => N (min t (c n ω)) ω) :
    MeasurableSet (capGood N c) := by
  have e : capGood N c = ⋂ K : ℕ, ⋂ j : ℕ, ⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ q : ℚ,
      ({_ω : Ω | ¬ (n₀ ≤ n ∧ (q : ℝ).toNNReal ≤ K)} ∪
        {ω | |N (min (q : ℝ).toNNReal (c n ω)) ω - N (min (q : ℝ).toNNReal (c n₀ ω)) ω| ≤
          1 / ((j : ℝ) + 1)}) := by
    ext ω
    simp only [capGood, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_union, not_and_or, not_le]
    refine forall_congr' fun K => forall_congr' fun j => exists_congr fun n₀ => ?_
    constructor
    · intro h n q
      by_cases h1 : n₀ ≤ n
      · by_cases h2 : (q : ℝ).toNNReal ≤ K
        · exact Or.inr (h n h1 q h2)
        · exact Or.inl (Or.inr (not_le.1 h2))
      · exact Or.inl (Or.inl (not_le.1 h1))
    · intro h n h1 q h2
      rcases h n q with (h3 | h3) | h3
      · exact absurd h1 (not_le.2 h3)
      · exact absurd h2 (not_le.2 h3)
      · exact h3
  rw [e]
  refine MeasurableSet.iInter fun K => MeasurableSet.iInter fun j => MeasurableSet.iUnion fun n₀ =>
    MeasurableSet.iInter fun n => MeasurableSet.iInter fun q => (MeasurableSet.const _).union ?_
  exact measurableSet_le (continuous_abs.measurable.comp ((hm n _).sub (hm n₀ _))) measurable_const

/-- On the good set the stopped noises are uniformly close on every `[0, K]` at all real times. -/
theorem close_of_mem_capGood {c : ℕ → Ω → ℝ≥0} (hNc : ∀ n ω, ContinuousOn (N · ω) (Icc 0 (c n ω))) {ω : Ω}
    (hω : ω ∈ capGood N c) :
    ∀ (K j : ℕ), ∃ n₀, ∀ n, n₀ ≤ n → ∀ t : ℝ≥0, t ≤ K →
      |N (min t (c n ω)) ω - N (min t (c n₀ ω)) ω| ≤ 1 / ((j : ℝ) + 1) := by
  intro K j
  obtain ⟨n₀, hn₀⟩ := hω K j
  refine ⟨n₀, fun n hn t htK => ?_⟩
  have hF : ∀ m, Continuous fun t : ℝ≥0 => N (min t (c m ω)) ω := fun m =>
    (hNc m ω).comp_continuous (continuous_id.min continuous_const) fun _ => ⟨bot_le, min_le_right _ _⟩
  have hh : Continuous fun t : ℝ≥0 => |N (min t (c n ω)) ω - N (min t (c n₀ ω)) ω| :=
    continuous_abs.comp ((hF n).sub (hF n₀))
  by_contra hlt
  push Not at hlt
  have hU : IsOpen {s : ℝ≥0 | 1 / ((j : ℝ) + 1) < |N (min s (c n ω)) ω - N (min s (c n₀ ω)) ω|} :=
    isOpen_lt continuous_const hh
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hU t hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) - η < t by linarith)
  have hqt : |((q : ℝ).toNNReal : ℝ) - t| < η :=
    (abs_toNNReal_sub_le q t).trans_lt (abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩)
  have hqK : (q : ℝ).toNNReal ≤ K := by
    refine le_trans ?_ htK
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal']
    exact max_le hq2.le t.coe_nonneg
  have hmem : (q : ℝ).toNNReal ∈ Metric.ball t η := by rw [Metric.mem_ball, NNReal.dist_eq]; exact hqt
  exact absurd (hn₀ n hn q hqK) (not_le.2 (hball hmem))

/-- **The masked noise**: on the good set, the limit of the stopped noises; `0` elsewhere. -/
def capNoiseExt (N : ℝ≥0 → Ω → ℝ) (c : ℕ → Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (capGood N c).indicator (fun ω => limUnder atTop fun n => N (min t (c n ω)) ω) ω

/-- **The masked noise is continuous at every sample.** -/
theorem continuous_capNoiseExt (hNc : ∀ n ω, ContinuousOn (N · ω) (Icc 0 (c n ω))) (ω : Ω) :
    Continuous (capNoiseExt N c · ω) := by
  by_cases hω : ω ∈ capGood N c
  · have hF : ∀ m, Continuous fun t : ℝ≥0 => N (min t (c m ω)) ω := fun m =>
      (hNc m ω).comp_continuous (continuous_id.min continuous_const) fun _ => ⟨bot_le, min_le_right _ _⟩
    have h := (continuous_limUnder_of_close hF (close_of_mem_capGood hNc hω)).2
    simpa only [capNoiseExt, indicator_of_mem hω] using h
  · simp only [capNoiseExt, indicator_of_notMem hω]
    exact continuous_const

/-- **On the good set the masked noise is the noise before every cap** (monotone caps). -/
theorem capNoiseExt_eq (hmono : ∀ ω, Monotone fun n => c n ω) {ω : Ω} (hω : ω ∈ capGood N c) {n : ℕ}
    {t : ℝ≥0} (ht : t ≤ c n ω) : capNoiseExt N c t ω = N t ω := by
  simp only [capNoiseExt, indicator_of_mem hω]
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [min_eq_left (ht.trans (hmono ω hm))]

theorem capNoiseExt_zero (hN0 : ∀ ω, N 0 ω = 0) (ω : Ω) : capNoiseExt N c 0 ω = 0 := by
  by_cases hω : ω ∈ capGood N c
  · simp only [capNoiseExt, indicator_of_mem hω, zero_min, hN0]
    exact tendsto_const_nhds.limUnder_eq
  · simp only [capNoiseExt, indicator_of_notMem hω]

/-- **The good set has full measure** when the noise is a stopped Brownian motion at every (monotone) cap. -/
theorem ae_mem_capGood [IsProbabilityMeasure P] {c : ℕ → Ω → ℝ≥0}
    (hc : ∀ n, IsStoppingTime 𝓗 fun ω => (c n ω : WithTop ℝ≥0)) (hmono : ∀ ω, Monotone fun n => c n ω)
    (hNc : ∀ n ω, ContinuousOn (N · ω) (Icc 0 (c n ω))) (hN0 : ∀ ω, N 0 ω = 0)
    (hbm : ∀ n, IsStoppedBM P 𝓗 N (c n)) {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {𝓦 : Filtration ℝ≥0 m₀} {β : ℝ≥0 → Ω₀ → ℝ}
    (hβ : IsFilteredBrownianReal 𝓦 β P₀) (hβc : ∀ w, Continuous (β · w)) (hβ0 : ∀ w, β 0 w = 0) :
    ∀ᵐ ω ∂P, ω ∈ capGood N c := by
  filter_upwards [ae_cauchy_of_isStoppedBM hc hmono hNc hN0 hbm hβ hβc hβ0] with ω hω K j
  obtain ⟨n₀, hn₀⟩ := close_of_cauchy (f := (N · ω)) (c := fun n => c n ω) (hmono ω) hω K j
  exact ⟨n₀, fun n hn q hq => hn₀ n hn _ hq⟩

/-- **The masked noise is adapted to the null augmentation** (the good set has full measure). -/
theorem measurable_capNoiseExt {c : ℕ → Ω → ℝ≥0} (hNa : ∀ t, Measurable[𝓗 t] (N t))
    (hc : ∀ n, IsStoppingTime 𝓗 fun ω => (c n ω : WithTop ℝ≥0))
    (hNc : ∀ n ω, ContinuousOn (N · ω) (Icc 0 (c n ω))) (hG : P (capGood N c)ᶜ = 0) (t : ℝ≥0) :
    Measurable[Ito.nullAugmented 𝓗 P t] (capNoiseExt N c t) := by
  have hst : ∀ n (s : ℝ≥0), Measurable[𝓗 s] fun ω => N (min s (c n ω)) ω := fun n s =>
    measurable_stopped_of_continuousOn hNa (hc n) (hNc n) s
  have hm : ∀ n (s : ℝ≥0), Measurable fun ω => N (min s (c n ω)) ω := fun n s => (hst n s).mono (𝓗.le s) le_rfl
  have hGm : MeasurableSet (capGood N c) := measurableSet_capGood hm
  have hGa : MeasurableSet[Ito.nullAugmented 𝓗 P t] (capGood N c) := by
    have h := Ito.measurableSet_nullAugmented_of_null (𝓕 := 𝓗) hGm.compl hG t
    simpa only [compl_compl] using h.compl
  have hlim : Measurable[𝓗 t] fun ω => limUnder atTop fun n => N (min t (c n ω)) ω :=
    (@StronglyMeasurable.limUnder ℕ Ω ℝ (𝓗 t) _ _ atTop _ (fun n ω => N (min t (c n ω)) ω) _ _
      fun n => (hst n t).stronglyMeasurable).measurable
  exact (hlim.mono (Ito.le_nullAugmented 𝓗 P t) le_rfl).indicator hGa

/-- **The masked noise is a stopped Brownian motion at every cap below which it equals the noise almost surely**, for
the null augmentation. -/
theorem isStoppedBM_capNoiseExt [IsProbabilityMeasure P] {c : ℕ → Ω → ℝ≥0} (hmono : ∀ ω, Monotone fun n => c n ω)
    (hNa : ∀ t, Measurable[𝓗 t] (N t)) (hc : ∀ n, IsStoppingTime 𝓗 fun ω => (c n ω : WithTop ℝ≥0))
    (hNc : ∀ n ω, ContinuousOn (N · ω) (Icc 0 (c n ω))) (hG : ∀ᵐ ω ∂P, ω ∈ capGood N c) {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓗 fun ω => (S ω : WithTop ℝ≥0)) (hSc : ∀ ω, ∃ n, S ω ≤ c n ω)
    (hbm : IsStoppedBM P 𝓗 N S) : IsStoppedBM P (Ito.nullAugmented 𝓗 P) (capNoiseExt N c) S := by
  have hG0 : P (capGood N c)ᶜ = 0 := by rwa [ae_iff] at hG
  have hbm' := A1Core.IsStoppedBM.nullAugmented hbm
  intro a
  refine WholeField.martingale_of_ae_eq_of_null (hbm' a) (fun t => ?_) (fun t => ?_)
    (fun t E hE hE0 => Ito.measurableSet_nullAugmented_of_null hE hE0 t)
  · have hcm : Measurable fun ω => capNoiseExt N c (min t (S ω)) ω := by
      have hst := measurable_stopped_of_continuousOn
        (fun s => measurable_capNoiseExt hNa hc hNc hG0 s) (fun s => Ito.le_nullAugmented 𝓗 P s _ (hS s))
        (fun ω => (continuous_capNoiseExt hNc ω).continuousOn) t
      exact hst.mono ((Ito.nullAugmented 𝓗 P).le t) le_rfl
    have hSm : Measurable fun ω => ((min t (S ω) : ℝ≥0) : ℝ) :=
      measurable_coe_nnreal_real.comp ((measurable_min_of_isStoppingTime hS t).mono (𝓗.le t) le_rfl)
    exact Real.measurable_exp.comp ((hcm.const_mul a).sub ((hSm.const_mul _).div_const 2))
  · filter_upwards [hG] with ω hω
    obtain ⟨n, hn⟩ := hSc ω
    simp only [stopExp, capNoiseExt_eq hmono hω ((min_le_right t (S ω)).trans hn)]

/-- **The continuous noise through the supremum of the caps** (the repair of A1-CANON's global-continuity clause):
a noise that is adapted, continuous before each cap `S m`, `0` at time `0` and a Brownian motion stopped at each cap
agrees almost surely, before every cap, with a noise `Ñ` that is continuous at **every** sample, `0` at `0`, adapted to
the null augmentation of `𝓗`, and a Brownian motion stopped at every cap for that augmentation. The independent
Brownian motion `β` is auxiliary (it completes the stopped noise to a Brownian motion inside the proof). -/
theorem exists_continuous_noise_of_isStoppedBM [IsProbabilityMeasure P] {S : ℕ → Ω → ℝ≥0}
    (hS : ∀ m, IsStoppingTime 𝓗 fun ω => (S m ω : WithTop ℝ≥0)) (hNa : ∀ t, Measurable[𝓗 t] (N t))
    (hNc : ∀ m ω, ContinuousOn (N · ω) (Icc 0 (S m ω))) (hN0 : ∀ ω, N 0 ω = 0)
    (hbm : ∀ m, IsStoppedBM P 𝓗 N (S m)) {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {𝓦 : Filtration ℝ≥0 m₀} {β : ℝ≥0 → Ω₀ → ℝ}
    (hβ : IsFilteredBrownianReal 𝓦 β P₀) (hβc : ∀ w, Continuous (β · w)) (hβ0 : ∀ w, β 0 w = 0) :
    ∃ N' : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (N' · ω)) ∧ (∀ ω, N' 0 ω = 0) ∧
      (∀ t, Measurable[Ito.nullAugmented 𝓗 P t] (N' t)) ∧
      (∀ m, IsStoppedBM P (Ito.nullAugmented 𝓗 P) N' (S m)) ∧
      ∀ᵐ ω ∂P, ∀ m t, t ≤ S m ω → N' t ω = N t ω := by
  set c := capMax S with hcdef
  have hc : ∀ n, IsStoppingTime 𝓗 fun ω => (c n ω : WithTop ℝ≥0) := isStoppingTime_capMax hS
  have hmono : ∀ ω, Monotone fun n => c n ω := monotone_capMax S
  have hcc : ∀ n ω, ContinuousOn (N · ω) (Icc 0 (c n ω)) := continuousOn_capMax hNc
  have hcbm : ∀ n, IsStoppedBM P 𝓗 N (c n) := isStoppedBM_capMax_of_continuousOn hbm hS hNc
  have hG := ae_mem_capGood hc hmono hcc hN0 hcbm hβ hβc hβ0
  have hG0 : P (capGood N c)ᶜ = 0 := by rwa [ae_iff] at hG
  refine ⟨capNoiseExt N c, continuous_capNoiseExt hcc, capNoiseExt_zero hN0,
    measurable_capNoiseExt hNa hc hcc hG0, fun m => ?_, ?_⟩
  · exact isStoppedBM_capNoiseExt hmono hNa hc hcc hG (hS m) (fun ω => ⟨m, le_capMax S le_rfl ω⟩) (hbm m)
  · filter_upwards [hG] with ω hω m t ht
    exact capNoiseExt_eq hmono hω (ht.trans (le_capMax S le_rfl ω))

end Mask

end InteractingSLE.ZhanGT4.A1RectLaw
