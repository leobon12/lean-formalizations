/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Optional sampling for right-continuous martingales in continuous time

Packet PROVE-SC-P3 (gap P3 of `planning/INFRA-SC.md`). Time is `ℝ≥0`, stopping times are
Mathlib stopping times `Ω → WithTop ℝ≥0`.

## Main results

* `InteractingSLE.Supermartingale.condExp_stoppedValue_le_of_rightContinuous`: optional sampling
  for a right-continuous supermartingale and bounded stopping times `σ ≤ τ`;
* `InteractingSLE.Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous`: optional sampling
  for a right-continuous martingale (Revuz–Yor II.3.2, Karatzas–Shreve Thm 1.3.22);
* `InteractingSLE.Martingale.stoppedProcess_of_rightContinuous`: a stopped right-continuous
  martingale is a martingale.

## Method

Revuz–Yor Ch. II §§1–3. A stopping time `τ` is approximated from above by the dyadic stopping
times `dyadicUpperTime n τ = (⌊2ⁿ τ⌋ + 1) / 2ⁿ`; on the grid `2⁻ⁿ ℕ` Mathlib's discrete optional
stopping theorem applies (`Submartingale.expected_stoppedValue_mono`). The values of a
right-continuous supermartingale at `dyadicUpperTime n τ` form a backward supermartingale, which is
uniformly integrable (`uniformIntegrable_of_backward`); Vitali's theorem then passes the discrete
inequalities to the limit. Right-continuous adapted processes are progressively measurable
(`isStronglyProgressive_of_rightContinuous`), which gives the `𝓕_τ`-measurability of `X_τ`.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Dyadic points above a time -/

/-- The smallest point `(⌊2ⁿ t⌋ + 1) / 2ⁿ` of the grid `2⁻ⁿ ℕ` strictly above `t`. -/
def dyadicUp (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  ((⌊(2 : ℝ≥0) ^ n * t⌋₊ + 1 : ℕ) : ℝ≥0) / 2 ^ n

lemma two_pow_pos (n : ℕ) : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n

lemma lt_dyadicUp (n : ℕ) (t : ℝ≥0) : t < dyadicUp n t := by
  rw [dyadicUp, lt_div_iff₀ (two_pow_pos n), mul_comm]
  exact_mod_cast Nat.lt_floor_add_one _

lemma dyadicUp_le_add (n : ℕ) (t : ℝ≥0) : dyadicUp n t ≤ t + 1 / 2 ^ n := by
  rw [dyadicUp, div_le_iff₀ (two_pow_pos n), add_mul, one_div,
    inv_mul_cancel₀ (two_pow_pos n).ne', mul_comm t]
  push_cast
  gcongr
  exact Nat.floor_le (by positivity)

/-- The dyadic point above `t` is at most `s` iff `t` lies strictly below the grid point
`⌊2ⁿ s⌋ / 2ⁿ`. -/
lemma dyadicUp_le_iff (n : ℕ) (t s : ℝ≥0) :
    dyadicUp n t ≤ s ↔ t < (⌊(2 : ℝ≥0) ^ n * s⌋₊ : ℝ≥0) / 2 ^ n := by
  rw [dyadicUp, div_le_iff₀ (two_pow_pos n), lt_div_iff₀ (two_pow_pos n), mul_comm s,
    mul_comm t, ← Nat.le_floor_iff (by positivity), Nat.add_one_le_iff,
    Nat.floor_lt (by positivity)]

lemma floor_div_le (n : ℕ) (s : ℝ≥0) : (⌊(2 : ℝ≥0) ^ n * s⌋₊ : ℝ≥0) / 2 ^ n ≤ s := by
  rw [div_le_iff₀ (two_pow_pos n), mul_comm s]
  exact Nat.floor_le (by positivity)

lemma dyadicUp_mono (n : ℕ) : Monotone (dyadicUp n) := by
  intro s t hst
  unfold dyadicUp
  gcongr

lemma dyadicUp_succ_le (n : ℕ) (t : ℝ≥0) : dyadicUp (n + 1) t ≤ dyadicUp n t := by
  rw [dyadicUp_le_iff]
  have h : (2 : ℝ≥0) ^ (n + 1) * dyadicUp n t = ((2 * (⌊(2 : ℝ≥0) ^ n * t⌋₊ + 1) : ℕ) : ℝ≥0) := by
    rw [dyadicUp, pow_succ]
    push_cast
    field_simp
  rw [h, Nat.floor_natCast]
  calc t < dyadicUp n t := lt_dyadicUp n t
    _ = _ := by
      rw [dyadicUp, pow_succ]
      push_cast
      field_simp

lemma dyadicUp_antitone (t : ℝ≥0) : Antitone fun n => dyadicUp n t :=
  antitone_nat_of_succ_le fun n => dyadicUp_succ_le n t

lemma tendsto_dyadicUp (t : ℝ≥0) :
    Tendsto (fun n => dyadicUp n t) atTop (𝓝[Ici t] t) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (lt_dyadicUp n t).le⟩
  have h2 : Tendsto (fun n : ℕ => t + 1 / (2 : ℝ≥0) ^ n) atTop (𝓝 (t + 0)) := by
    refine tendsto_const_nhds.add ?_
    simp_rw [one_div, ← inv_pow]
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  rw [add_zero] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun n => (lt_dyadicUp n t).le) fun n => dyadicUp_le_add n t

/-- Along the dyadic points above `t`, a path that is right-continuous at `t` converges to its
value at `t`. -/
lemma tendsto_comp_dyadicUp {E : Type*} [TopologicalSpace E] {f : ℝ≥0 → E} {t : ℝ≥0}
    (hf : ContinuousWithinAt f (Ici t) t) :
    Tendsto (fun n => f (dyadicUp n t)) atTop (𝓝 (f t)) :=
  hf.tendsto.comp (tendsto_dyadicUp t)

/-! ### Right-continuous adapted processes are progressively measurable -/

/-- The dyadic point above `s`, capped at `i`. -/
def cappedDyadicUp (n : ℕ) (i s : ℝ≥0) : ℝ≥0 := min (dyadicUp n s) i

lemma measurable_cappedDyadicUp (n : ℕ) (i : ℝ≥0) : Measurable (cappedDyadicUp n i) := by
  unfold cappedDyadicUp dyadicUp
  refine Measurable.min ?_ measurable_const
  refine Measurable.div_const ?_ _
  exact measurable_from_nat.comp ((measurable_const.mul measurable_id).nat_floor.add_const 1)

/-- A right-continuous adapted real process indexed by `ℝ≥0` is progressively measurable. -/
theorem isStronglyProgressive_of_rightContinuous {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : StronglyAdapted 𝓕 X) (hXrc : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t) :
    IsStronglyProgressive 𝓕 X := by
  intro i
  -- the approximations `(s, ω) ↦ X (min (dyadicUp n s) i) ω`
  set U : ℕ → Set.Iic i × Ω → ℝ := fun n p => X (cappedDyadicUp n i p.1) p.2 with hU
  refine @stronglyMeasurable_of_tendsto _ _ _ (MeasurableSpace.prod _ (𝓕 i)) _ _ atTop _ _ U _
    (fun n => ?_) ?_
  · -- each approximation is measurable: it factors through `(⌊2ⁿ s⌋, ω)`
    let F : ℕ × Ω → ℝ := fun q => X (min (((q.1 + 1 : ℕ) : ℝ≥0) / 2 ^ n) i) q.2
    have hF : @Measurable (ℕ × Ω) ℝ (MeasurableSpace.prod inferInstance (𝓕 i)) inferInstance F := by
      refine measurable_from_prod_countable_right fun k => ?_
      change Measurable[𝓕 i] (X (min (((k + 1 : ℕ) : ℝ≥0) / 2 ^ n) i))
      exact ((hX _).mono (𝓕.mono (min_le_right _ _))).measurable
    have hφ : @Measurable (Set.Iic i × Ω) (ℕ × Ω) (MeasurableSpace.prod inferInstance (𝓕 i))
        (MeasurableSpace.prod inferInstance (𝓕 i))
        fun p : Set.Iic i × Ω => ((⌊(2 : ℝ≥0) ^ n * (p.1 : ℝ≥0)⌋₊, p.2) : ℕ × Ω) := by
      refine Measurable.prodMk ?_ ?_
      · exact ((measurable_const.mul measurable_subtype_coe).nat_floor).comp
          (@measurable_fst _ _ _ (𝓕 i))
      · exact @measurable_snd _ _ _ (𝓕 i)
    refine (Measurable.stronglyMeasurable ?_)
    convert! hF.comp hφ using 1
  · -- pointwise convergence by right-continuity
    rw [tendsto_pi_nhds]
    rintro ⟨⟨s, hs⟩, ω⟩
    have h1 : Tendsto (fun n => cappedDyadicUp n i s) atTop (𝓝[Ici s] s) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        le_min (lt_dyadicUp n s).le hs⟩
      have h := (tendsto_nhdsWithin_iff.1 (tendsto_dyadicUp s)).1.min
        (tendsto_const_nhds (x := i))
      rwa [min_eq_left hs] at h
    exact (hXrc ω s).tendsto.comp h1

section Approximation

/-! ### Dyadic approximation of stopping times from above -/

/-- The dyadic approximation from above `(⌊2ⁿ τ⌋ + 1) / 2ⁿ` of a random time (`⊤` where
`τ = ⊤`). It is a stopping time when `τ` is one, strictly above `τ` where `τ` is finite, and
decreases to `τ` as `n → ∞`. -/
def dyadicUpperTime (n : ℕ) (τ : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => (τ ω).map (dyadicUp n)

variable {𝓕 : Filtration ℝ≥0 mΩ} {σ τ : Ω → WithTop ℝ≥0}

lemma dyadicUpperTime_of_eq {n : ℕ} {ω : Ω} {t : ℝ≥0} (h : τ ω = t) :
    dyadicUpperTime n τ ω = dyadicUp n t := by
  simp only [dyadicUpperTime, h, WithTop.map_coe]

lemma isStoppingTime_dyadicUpperTime (hτ : IsStoppingTime 𝓕 τ) (n : ℕ) :
    IsStoppingTime 𝓕 (dyadicUpperTime n τ) := by
  intro s
  have h : {ω | dyadicUpperTime n τ ω ≤ s} =
      {ω | τ ω < (((⌊(2 : ℝ≥0) ^ n * s⌋₊ : ℝ≥0) / 2 ^ n : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    cases h' : τ ω with
    | top =>
      simp only [dyadicUpperTime, h', WithTop.map_top]
      exact iff_of_false (fun h => WithTop.coe_ne_top (top_le_iff.1 h)) (not_top_lt)
    | coe t =>
      rw [dyadicUpperTime_of_eq h', WithTop.coe_le_coe, WithTop.coe_lt_coe, dyadicUp_le_iff]
  rw [h]
  exact 𝓕.mono (floor_div_le n s) _ (hτ.measurableSet_lt _)

lemma le_dyadicUpperTime (n : ℕ) (τ : Ω → WithTop ℝ≥0) : τ ≤ dyadicUpperTime n τ := by
  intro ω
  cases h' : τ ω with
  | top => simp [dyadicUpperTime, h']
  | coe t =>
    rw [dyadicUpperTime_of_eq h', WithTop.coe_le_coe]
    exact (lt_dyadicUp n t).le

lemma dyadicUpperTime_mono (n : ℕ) (h : σ ≤ τ) :
    dyadicUpperTime n σ ≤ dyadicUpperTime n τ := by
  intro ω
  cases hτ' : τ ω with
  | top => simp [dyadicUpperTime, hτ']
  | coe t =>
    have hσt : σ ω ≤ t := hτ' ▸ h ω
    obtain ⟨s, hs, hst⟩ := WithTop.le_coe_iff.1 hσt
    rw [dyadicUpperTime_of_eq hs, dyadicUpperTime_of_eq hτ', WithTop.coe_le_coe]
    exact dyadicUp_mono n hst

lemma dyadicUpperTime_antitone (τ : Ω → WithTop ℝ≥0) {n m : ℕ} (hnm : n ≤ m) :
    dyadicUpperTime m τ ≤ dyadicUpperTime n τ := by
  intro ω
  cases h' : τ ω with
  | top => simp [dyadicUpperTime, h']
  | coe t =>
    rw [dyadicUpperTime_of_eq h', dyadicUpperTime_of_eq h', WithTop.coe_le_coe]
    exact dyadicUp_antitone t hnm

/-- A bound for the dyadic approximation of a bounded random time. -/
lemma dyadicUpperTime_le_natCeil {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (n : ℕ) (ω : Ω) :
    dyadicUpperTime n τ ω ≤ (((⌈T⌉₊ + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) := by
  obtain ⟨t, ht, htT⟩ := WithTop.le_coe_iff.1 (hτT ω)
  rw [dyadicUpperTime_of_eq ht, WithTop.coe_le_coe]
  calc dyadicUp n t ≤ t + 1 / 2 ^ n := dyadicUp_le_add n t
    _ ≤ T + 1 := by
      gcongr
      rw [one_div]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    _ ≤ _ := by
      push_cast
      gcongr
      exact Nat.le_ceil T

/-! ### Stopping times on a dyadic grid and the discrete theorem -/

/-- `τ` takes only values of the grid `2⁻ⁿ ℕ` (in particular it is finite). -/
def OnDyadicGrid (n : ℕ) (τ : Ω → WithTop ℝ≥0) : Prop :=
  ∀ ω, ∃ k : ℕ, τ ω = (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : WithTop ℝ≥0)

lemma onDyadicGrid_dyadicUpperTime (n : ℕ) (hfin : ∀ ω, τ ω ≠ ⊤) :
    OnDyadicGrid n (dyadicUpperTime n τ) := by
  intro ω
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (hfin ω)
  exact ⟨⌊(2 : ℝ≥0) ^ n * t⌋₊ + 1, dyadicUpperTime_of_eq ht.symm⟩

lemma OnDyadicGrid.mono {n m : ℕ} (h : OnDyadicGrid n τ) (hnm : n ≤ m) : OnDyadicGrid m τ := by
  intro ω
  obtain ⟨k, hk⟩ := h ω
  refine ⟨k * 2 ^ (m - n), ?_⟩
  rw [hk]
  congr 1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [Nat.add_sub_cancel_left, pow_add]
  push_cast
  rw [mul_div_mul_right _ _ (pow_pos two_pos d).ne']

lemma onDyadicGrid_const_nat (n N : ℕ) :
    OnDyadicGrid n (fun _ : Ω => WithTop.some (N : ℝ≥0)) := by
  intro ω
  refine ⟨N * 2 ^ n, ?_⟩
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_right₀ _ (two_pow_pos n).ne']

lemma OnDyadicGrid.piecewise {n : ℕ} (hσ : OnDyadicGrid n σ) (hτ : OnDyadicGrid n τ) (A : Set Ω)
    [DecidablePred (· ∈ A)] : OnDyadicGrid n (A.piecewise σ τ) := by
  intro ω
  by_cases hω : ω ∈ A
  · simpa [hω] using hσ ω
  · simpa [hω] using hτ ω

/-- The filtration `𝓕` sampled on the grid `2⁻ⁿ ℕ`. -/
def gridFiltration (𝓕 : Filtration ℝ≥0 mΩ) (n : ℕ) : Filtration ℕ mΩ where
  seq k := 𝓕 ((k : ℝ≥0) / 2 ^ n)
  mono' i j hij := 𝓕.mono (by gcongr)
  le' k := 𝓕.le _

/-- A grid-valued random time in grid units. -/
def gridTime (n : ℕ) (τ : Ω → WithTop ℝ≥0) : Ω → WithTop ℕ :=
  fun ω => WithTop.some ⌊(2 : ℝ≥0) ^ n * (τ ω).untopA⌋₊

lemma gridTime_of_eq {n k : ℕ} {ω : Ω} (h : τ ω = (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : WithTop ℝ≥0)) :
    gridTime n τ ω = WithTop.some k := by
  simp only [gridTime, h, WithTop.untopA, WithTop.untopD_coe]
  rw [mul_div_cancel₀ _ (two_pow_pos n).ne', Nat.floor_natCast]

lemma isStoppingTime_gridTime {n : ℕ} (hτ : IsStoppingTime 𝓕 τ) (hg : OnDyadicGrid n τ) :
    IsStoppingTime (gridFiltration 𝓕 n) (gridTime n τ) := by
  intro k
  have h : {ω | gridTime n τ ω ≤ WithTop.some k} =
      {ω | τ ω ≤ (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    obtain ⟨j, hj⟩ := hg ω
    simp only [Set.mem_ofPred_eq, gridTime_of_eq hj, hj]
    rw [WithTop.coe_le_coe, WithTop.coe_le_coe, div_le_div_iff_of_pos_right (two_pow_pos n),
      Nat.cast_le]
  change MeasurableSet[𝓕 ((k : ℝ≥0) / 2 ^ n)] {ω | gridTime n τ ω ≤ WithTop.some k}
  rw [h]
  exact hτ _

lemma stoppedValue_gridTime {n : ℕ} (hg : OnDyadicGrid n τ) {E : Type*} (X : ℝ≥0 → Ω → E) :
    stoppedValue (fun k : ℕ => X ((k : ℝ≥0) / 2 ^ n)) (gridTime n τ) = stoppedValue X τ := by
  funext ω
  obtain ⟨j, hj⟩ := hg ω
  simp only [stoppedValue, gridTime_of_eq hj, hj, WithTop.untopA, WithTop.untopD_coe]

lemma gridTime_le_of_le {n N : ℕ} (hg : OnDyadicGrid n τ) (hτN : ∀ ω, τ ω ≤ (N : ℝ≥0)) (ω : Ω) :
    gridTime n τ ω ≤ WithTop.some (N * 2 ^ n) := by
  obtain ⟨j, hj⟩ := hg ω
  have h := hτN ω
  rw [hj, WithTop.coe_le_coe, div_le_iff₀ (two_pow_pos n)] at h
  rw [gridTime_of_eq hj, WithTop.coe_le_coe]
  exact_mod_cast h

lemma gridTime_mono {n : ℕ} (hgσ : OnDyadicGrid n σ) (hgτ : OnDyadicGrid n τ) (hle : σ ≤ τ) :
    gridTime n σ ≤ gridTime n τ := by
  intro ω
  obtain ⟨i, hi⟩ := hgσ ω
  obtain ⟨j, hj⟩ := hgτ ω
  have h := hle ω
  rw [hi, hj, WithTop.coe_le_coe, div_le_div_iff_of_pos_right (two_pow_pos n),
    Nat.cast_le] at h
  rw [gridTime_of_eq hi, gridTime_of_eq hj, WithTop.coe_le_coe]
  exact h

variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

lemma supermartingale_grid (hX : Supermartingale X 𝓕 P) (n : ℕ) :
    Supermartingale (fun k : ℕ => X ((k : ℝ≥0) / 2 ^ n)) (gridFiltration 𝓕 n) P :=
  ⟨fun k => hX.1 _, fun i j hij => hX.2.1 _ _ (by gcongr), fun k => hX.2.2 _⟩

lemma integrable_stoppedValue_of_onDyadicGrid (hint : ∀ t, Integrable (X t) P)
    (hτ : IsStoppingTime 𝓕 τ) {n N : ℕ} (hg : OnDyadicGrid n τ)
    (hτN : ∀ ω, τ ω ≤ (N : ℝ≥0)) : Integrable (stoppedValue X τ) P := by
  rw [← stoppedValue_gridTime hg]
  exact integrable_stoppedValue ℕ (isStoppingTime_gridTime hτ hg) (fun k => hint _)
    (gridTime_le_of_le hg hτN)

/-- Optional stopping on a dyadic grid, expectation form. -/
lemma integral_stoppedValue_le_of_onDyadicGrid [IsFiniteMeasure P] (hX : Supermartingale X 𝓕 P)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) (hle : σ ≤ τ) {n N : ℕ}
    (hgσ : OnDyadicGrid n σ) (hgτ : OnDyadicGrid n τ) (hτN : ∀ ω, τ ω ≤ (N : ℝ≥0)) :
    ∫ ω, stoppedValue X τ ω ∂P ≤ ∫ ω, stoppedValue X σ ω ∂P := by
  have h := (supermartingale_grid hX n).neg.expected_stoppedValue_mono
    (isStoppingTime_gridTime hσ hgσ) (isStoppingTime_gridTime hτ hgτ) (gridTime_mono hgσ hgτ hle)
    (gridTime_le_of_le hgτ hτN)
  have e : ∀ ρ : Ω → WithTop ℕ, stoppedValue (-fun k : ℕ => X ((k : ℝ≥0) / 2 ^ n)) ρ =
      -stoppedValue (fun k : ℕ => X ((k : ℝ≥0) / 2 ^ n)) ρ := fun _ => rfl
  simpa only [e, Pi.neg_apply, integral_neg, neg_le_neg_iff, stoppedValue_gridTime hgσ,
    stoppedValue_gridTime hgτ] using h

/-- Pasting two stopping times `σ ≤ τ` along a set of `𝓕_σ`. -/
lemma isStoppingTime_piecewise (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ)
    (hle : σ ≤ τ) {A : Set Ω} [DecidablePred (· ∈ A)]
    (hA : MeasurableSet[hσ.measurableSpace] A) : IsStoppingTime 𝓕 (A.piecewise σ τ) := by
  intro i
  have h : {ω | A.piecewise σ τ ω ≤ i} =
      (A ∩ {ω | σ ω ≤ i}) ∪ ((Aᶜ ∩ {ω | σ ω ≤ i}) ∩ {ω | τ ω ≤ i}) := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [hω]
    · simp only [Set.piecewise_eq_of_notMem _ _ _ hω, Set.mem_ofPred_eq, Set.mem_union,
        Set.mem_inter_iff, hω, false_and, Set.mem_compl_iff, not_false_eq_true, true_and,
        false_or]
      exact ⟨fun h => ⟨(hle ω).trans h, h⟩, fun h => h.2⟩
  rw [h]
  have hAc : MeasurableSet[hσ.measurableSpace] Aᶜ := hA.compl
  exact (hA.2 i).union ((hAc.2 i).inter (hτ i))

/-- Optional stopping on a dyadic grid, conditional form. -/
lemma setIntegral_stoppedValue_le_of_onDyadicGrid [IsFiniteMeasure P]
    (hX : Supermartingale X 𝓕 P) (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ)
    (hle : σ ≤ τ) {n N : ℕ} (hgσ : OnDyadicGrid n σ) (hgτ : OnDyadicGrid n τ)
    (hτN : ∀ ω, τ ω ≤ (N : ℝ≥0)) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    ∫ ω in A, stoppedValue X τ ω ∂P ≤ ∫ ω in A, stoppedValue X σ ω ∂P := by
  classical
  have hAm : MeasurableSet A := hσ.measurableSpace_le A hA
  have hρ := isStoppingTime_piecewise hσ hτ hle hA
  have hρτ : A.piecewise σ τ ≤ τ := fun ω => by
    by_cases hω : ω ∈ A
    · simpa [hω] using hle ω
    · simp [hω]
  have h := integral_stoppedValue_le_of_onDyadicGrid hX hρ hτ hρτ (hgσ.piecewise hgτ A) hgτ hτN
  have hσN : ∀ ω, σ ω ≤ (N : ℝ≥0) := fun ω => (hle ω).trans (hτN ω)
  have hiσ := integrable_stoppedValue_of_onDyadicGrid hX.2.2 hσ hgσ hσN
  have hiτ := integrable_stoppedValue_of_onDyadicGrid hX.2.2 hτ hgτ hτN
  have hsv : stoppedValue X (A.piecewise σ τ) = A.piecewise (stoppedValue X σ) (stoppedValue X τ) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [stoppedValue, hω]
  rw [hsv, integral_piecewise hAm hiσ.integrableOn hiτ.integrableOn,
    ← integral_add_compl hAm hiτ] at h
  linarith

/-! ### Uniform integrability of backward supermartingales -/

/-- **Backward supermartingales are uniformly integrable** (Revuz–Yor II.2.3, Karatzas–Shreve
Problem 1.3.11). If `Y k` is `G k`-measurable, `∫_s Y j ≤ ∫_s Y k` for `j ≤ k` and `s ∈ G k`, and
the expectations are bounded above, then `(Y k)` is uniformly integrable. -/
theorem uniformIntegrable_of_backward [IsFiniteMeasure P] {Y : ℕ → Ω → ℝ}
    {G : ℕ → MeasurableSpace Ω} (hG : ∀ k, G k ≤ mΩ) (hYm : ∀ k, StronglyMeasurable[G k] (Y k))
    (hYi : ∀ k, Integrable (Y k) P)
    (hmono : ∀ j k, j ≤ k → ∀ s, MeasurableSet[G k] s →
      ∫ ω in s, Y j ω ∂P ≤ ∫ ω in s, Y k ω ∂P)
    {c : ℝ} (hup : ∀ k, ∫ ω, Y k ω ∂P ≤ c) :
    UniformIntegrable Y 1 P := by
  -- the expectations increase to a finite limit
  set a : ℕ → ℝ := fun k => ∫ ω, Y k ω ∂P with ha
  have ha_bdd : BddAbove (range a) := ⟨c, by rintro _ ⟨k, rfl⟩; exact hup k⟩
  have hcauchy : ∀ ε > 0, ∃ N, ∀ k, N ≤ k → a k - a N ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_lt_of_lt_ciSup (by linarith : (⨆ k, a k) - ε < ⨆ k, a k)
    refine ⟨N, fun k _ => ?_⟩
    have := le_ciSup ha_bdd k
    linarith
  -- comparison with the conditional expectation of a fixed `Y N`
  have hcomp : ∀ N k, N ≤ k → ∀ s : Set Ω, eLpNorm (Y k) 1 (P.restrict s) ≤
      eLpNorm (P[Y N | G k]) 1 (P.restrict s) + ENNReal.ofReal (a k - a N) := by
    intro N k hNk s
    have hV : P[Y N | G k] ≤ᵐ[P] Y k := by
      refine ae_le_of_ae_le_trim (hm := hG k) ?_
      refine ae_le_of_forall_setIntegral_le
        (integrable_condExp.trim (hG k) stronglyMeasurable_condExp)
        ((hYi k).trim (hG k) (hYm k)) fun s hs _ => ?_
      rw [← setIntegral_trim (hG k) stronglyMeasurable_condExp hs,
        ← setIntegral_trim (hG k) (hYm k) hs, setIntegral_condExp (hG k) (hYi N) hs]
      exact hmono N k hNk s hs
    have hD : 0 ≤ᵐ[P] Y k - P[Y N | G k] := by
      filter_upwards [hV] with ω hω
      simpa only [Pi.zero_apply, Pi.sub_apply, sub_nonneg] using hω
    have hDi : Integrable (Y k - P[Y N | G k]) P := (hYi k).sub integrable_condExp
    have hDint : ∫ ω, (Y k - P[Y N | G k]) ω ∂P = a k - a N := by
      change ∫ ω, (Y k ω - P[Y N | G k] ω) ∂P = _
      rw [integral_sub (hYi k) integrable_condExp, integral_condExp (hG k)]
    have hDn : eLpNorm (Y k - P[Y N | G k]) 1 P = ENNReal.ofReal (a k - a N) := by
      rw [eLpNorm_one_eq_lintegral_enorm, ← hDint, ofReal_integral_eq_lintegral_ofReal hDi hD]
      refine lintegral_congr_ae ?_
      filter_upwards [hD] with ω hω
      exact Real.enorm_of_nonneg hω
    calc eLpNorm (Y k) 1 (P.restrict s)
        = eLpNorm (P[Y N | G k] + (Y k - P[Y N | G k])) 1 (P.restrict s) := by
          rw [add_sub_cancel]
      _ ≤ eLpNorm (P[Y N | G k]) 1 (P.restrict s) +
            eLpNorm (Y k - P[Y N | G k]) 1 (P.restrict s) :=
          eLpNorm_add_le integrable_condExp.aestronglyMeasurable.restrict
            hDi.aestronglyMeasurable.restrict le_rfl
      _ ≤ eLpNorm (P[Y N | G k]) 1 (P.restrict s) + eLpNorm (Y k - P[Y N | G k]) 1 P := by
          gcongr
          exact Measure.restrict_le_self
      _ = eLpNorm (P[Y N | G k]) 1 (P.restrict s) + ENNReal.ofReal (a k - a N) := by
          rw [hDn]
  refine ⟨fun k => (hYi k).aestronglyMeasurable, ?_, ?_⟩
  · -- uniform absolute continuity
    rw [unifIntegrable_iff]
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · exact ⟨1, one_pos, fun _ _ _ => le_top⟩
    have hε₀ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    obtain ⟨N, hN⟩ := hcauchy (ε.toReal / 2) (by positivity)
    have hUI₁ := ((hYi N).uniformIntegrable_condExp hG).2.1
    rw [unifIntegrable_iff] at hUI₁
    obtain ⟨δ₁, hδ₁, h₁⟩ := hUI₁ (ε / 2) (ENNReal.half_pos hε.ne')
    have hUI₂ : UnifIntegrable (fun j : Fin (N + 1) => Y j) 1 P :=
      unifIntegrable_finite le_rfl ENNReal.one_ne_top fun j => memLp_one_iff_integrable.2 (hYi j)
    rw [unifIntegrable_iff] at hUI₂
    obtain ⟨δ₂, hδ₂, h₂⟩ := hUI₂ ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun k s hs => ?_⟩
    rcases lt_or_ge k N with hk | hk
    · exact h₂ ⟨k, by omega⟩ s (hs.trans (min_le_right _ _))
    · calc eLpNorm (Y k) 1 (P.restrict s)
          ≤ eLpNorm (P[Y N | G k]) 1 (P.restrict s) + ENNReal.ofReal (a k - a N) :=
            hcomp N k hk s
        _ ≤ ε / 2 + ε / 2 := by
            gcongr
            · exact h₁ k s (hs.trans (min_le_left _ _))
            · calc ENNReal.ofReal (a k - a N) ≤ ENNReal.ofReal (ε.toReal / 2) :=
                    ENNReal.ofReal_le_ofReal (hN k hk)
                _ = ε / 2 := by
                    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hεtop,
                      ENNReal.ofReal_ofNat]
        _ = ε := ENNReal.add_halves ε
  · -- `L¹` bound
    obtain ⟨N, hN⟩ := hcauchy 1 one_pos
    set C : ℝ≥0∞ := (∑ j ∈ Finset.range (N + 1), eLpNorm (Y j) 1 P) + 1 with hC
    have hCtop : C ≠ ⊤ := by
      refine ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun j _ => ?_, ENNReal.one_ne_top⟩
      exact (memLp_one_iff_integrable.2 (hYi j)).eLpNorm_ne_top
    refine ⟨C.toNNReal, fun k => ?_⟩
    rw [ENNReal.coe_toNNReal hCtop]
    rcases le_or_gt k N with hk | hk
    · calc eLpNorm (Y k) 1 P ≤ ∑ j ∈ Finset.range (N + 1), eLpNorm (Y j) 1 P :=
            Finset.single_le_sum (f := fun j => eLpNorm (Y j) 1 P) (fun _ _ => zero_le)
              (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
        _ ≤ C := le_self_add
    · have h := hcomp N k hk.le univ
      rw [Measure.restrict_univ] at h
      calc eLpNorm (Y k) 1 P ≤ eLpNorm (P[Y N | G k]) 1 P + ENNReal.ofReal (a k - a N) := h
        _ ≤ eLpNorm (Y N) 1 P + 1 := by
            gcongr
            · exact eLpNorm_condExp_le_eLpNorm _ le_rfl
            · calc ENNReal.ofReal (a k - a N) ≤ ENNReal.ofReal 1 :=
                    ENNReal.ofReal_le_ofReal (hN k hk.le)
                _ = 1 := ENNReal.ofReal_one
        _ ≤ C := by
            rw [hC]
            gcongr
            exact Finset.single_le_sum (f := fun j => eLpNorm (Y j) 1 P) (fun _ _ => zero_le)
              (Finset.mem_range.2 (Nat.lt_succ_self N))

/-! ### `L¹` convergence along the dyadic approximation of a bounded stopping time -/

/-- For a right-continuous supermartingale `X` and a bounded stopping time `ρ`: the values at the
dyadic approximations `dyadicUpperTime n ρ` are integrable, `X_ρ` is integrable, and
`X_{dyadicUpperTime n ρ} → X_ρ` in `L¹`. -/
theorem tendsto_lintegral_stoppedValue_dyadicUpperTime [IsFiniteMeasure P]
    (hX : Supermartingale X 𝓕 P) (hXrc : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ) {T : ℝ≥0} (hρT : ∀ ω, ρ ω ≤ T) :
    (∀ n, Integrable (stoppedValue X (dyadicUpperTime n ρ)) P) ∧
      Integrable (stoppedValue X ρ) P ∧
      Tendsto (fun n => ∫⁻ ω, ‖stoppedValue X (dyadicUpperTime n ρ) ω - stoppedValue X ρ ω‖ₑ ∂P)
        atTop (𝓝 0) := by
  have hprog := isStronglyProgressive_of_rightContinuous hX.1 hXrc
  have hfin : ∀ ω, ρ ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top WithTop.coe_ne_top (hρT ω)
  have hρn := fun n => isStoppingTime_dyadicUpperTime hρ n
  have hgn : ∀ n, OnDyadicGrid n (dyadicUpperTime n ρ) :=
    fun n => onDyadicGrid_dyadicUpperTime n hfin
  have hbd : ∀ n ω, dyadicUpperTime n ρ ω ≤ ((⌈T⌉₊ + 1 : ℕ) : ℝ≥0) :=
    fun n ω => dyadicUpperTime_le_natCeil hρT n ω
  set Y : ℕ → Ω → ℝ := fun n => stoppedValue X (dyadicUpperTime n ρ) with hY
  have hYi : ∀ n, Integrable (Y n) P :=
    fun n => integrable_stoppedValue_of_onDyadicGrid hX.2.2 (hρn n) (hgn n) (hbd n)
  have hYm : ∀ n, StronglyMeasurable[(hρn n).measurableSpace] (Y n) :=
    fun n => (measurable_stoppedValue hprog (hρn n)).stronglyMeasurable
  have hmono : ∀ j k, j ≤ k → ∀ s, MeasurableSet[(hρn k).measurableSpace] s →
      ∫ ω in s, Y j ω ∂P ≤ ∫ ω in s, Y k ω ∂P := by
    intro j k hjk s hs
    exact setIntegral_stoppedValue_le_of_onDyadicGrid hX (hρn k) (hρn j)
      (dyadicUpperTime_antitone ρ hjk) (hgn k) ((hgn j).mono hjk) (hbd j) hs
  have hup : ∀ k, ∫ ω, Y k ω ∂P ≤ ∫ ω, X 0 ω ∂P := by
    intro k
    have h := integral_stoppedValue_le_of_onDyadicGrid hX (isStoppingTime_const 𝓕 (0 : ℝ≥0))
      (hρn k) (fun ω => by simp) (by simpa using onDyadicGrid_const_nat (Ω := Ω) k 0) (hgn k)
      (hbd k)
    rwa [stoppedValue_const] at h
  have hUI := uniformIntegrable_of_backward (fun n => (hρn n).measurableSpace_le) hYm hYi hmono hup
  have hlim : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (stoppedValue X ρ ω)) := by
    intro ω
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (hfin ω)
    have e : ∀ n, Y n ω = X (dyadicUp n t) ω := fun n => by
      simp only [hY, stoppedValue, dyadicUpperTime_of_eq ht.symm, WithTop.untopA,
        WithTop.untopD_coe]
    have e2 : stoppedValue X ρ ω = X t ω := by
      simp only [stoppedValue, ← ht, WithTop.untopA, WithTop.untopD_coe]
    simp_rw [e, e2]
    exact tendsto_comp_dyadicUp (hXrc ω t)
  have hgm : AEStronglyMeasurable (stoppedValue X ρ) P :=
    ((measurable_stoppedValue hprog hρ).mono hρ.measurableSpace_le le_rfl).aestronglyMeasurable
  obtain ⟨C, hC⟩ := hUI.2.2
  have hgL : eLpNorm (stoppedValue X ρ) 1 P ≤ C :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hC) (fun n => (hYi n).aestronglyMeasurable)
      (Eventually.of_forall hlim)
  have hgi : Integrable (stoppedValue X ρ) P :=
    memLp_one_iff_integrable.1 ⟨hgm, hgL.trans_lt ENNReal.coe_lt_top⟩
  refine ⟨hYi, hgi, ?_⟩
  have h := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun n => (hYi n).aestronglyMeasurable) (memLp_one_iff_integrable.2 hgi) hUI.2.1
    (Eventually.of_forall hlim)
  simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using h

/-- Optional sampling for a right-continuous supermartingale and bounded stopping times, in
set-integral form. -/
theorem setIntegral_stoppedValue_le_of_rightContinuous [IsFiniteMeasure P]
    (hX : Supermartingale X 𝓕 P) (hXrc : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) (hle : σ ≤ τ) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    ∫ ω in A, stoppedValue X τ ω ∂P ≤ ∫ ω in A, stoppedValue X σ ω ∂P := by
  have hσT : ∀ ω, σ ω ≤ T := fun ω => (hle ω).trans (hτT ω)
  obtain ⟨hYσ, hiσ, hσc⟩ := tendsto_lintegral_stoppedValue_dyadicUpperTime hX hXrc hσ hσT
  obtain ⟨hYτ, hiτ, hτc⟩ := tendsto_lintegral_stoppedValue_dyadicUpperTime hX hXrc hτ hτT
  have h1 := tendsto_setIntegral_of_L1 _ hiσ.aestronglyMeasurable (Eventually.of_forall hYσ) hσc A
  have h2 := tendsto_setIntegral_of_L1 _ hiτ.aestronglyMeasurable (Eventually.of_forall hYτ) hτc A
  have hfinσ : ∀ ω, σ ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top WithTop.coe_ne_top (hσT ω)
  have hfinτ : ∀ ω, τ ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top WithTop.coe_ne_top (hτT ω)
  refine le_of_tendsto_of_tendsto' h2 h1 fun n => ?_
  exact setIntegral_stoppedValue_le_of_onDyadicGrid hX (isStoppingTime_dyadicUpperTime hσ n)
    (isStoppingTime_dyadicUpperTime hτ n) (dyadicUpperTime_mono n hle)
    (onDyadicGrid_dyadicUpperTime n hfinσ) (onDyadicGrid_dyadicUpperTime n hfinτ)
    (dyadicUpperTime_le_natCeil hτT n)
    (hσ.measurableSpace_mono (isStoppingTime_dyadicUpperTime hσ n) (le_dyadicUpperTime n σ) A hA)

end Approximation

/-! ## P3a. Optional sampling -/

section P3

variable {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {M X : ℝ≥0 → Ω → ℝ}

/-- [P3a] Optional sampling for a right-continuous supermartingale and bounded stopping times. -/
theorem Supermartingale.condExp_stoppedValue_le_of_rightContinuous [IsFiniteMeasure P]
    (hX : Supermartingale X 𝓕 P) (hXrc : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) (hle : σ ≤ τ)
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) :
    P[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[P] stoppedValue X σ := by
  have hm := hσ.measurableSpace_le
  have hprog := isStronglyProgressive_of_rightContinuous hX.1 hXrc
  have hσm : StronglyMeasurable[hσ.measurableSpace] (stoppedValue X σ) :=
    (measurable_stoppedValue hprog hσ).stronglyMeasurable
  have hiσ := (tendsto_lintegral_stoppedValue_dyadicUpperTime hX hXrc hσ
    fun ω => (hle ω).trans (hτT ω)).2.1
  have hiτ := (tendsto_lintegral_stoppedValue_dyadicUpperTime hX hXrc hτ hτT).2.1
  refine ae_le_of_ae_le_trim (hm := hm) ?_
  refine ae_le_of_forall_setIntegral_le (integrable_condExp.trim hm stronglyMeasurable_condExp)
    (hiσ.trim hm hσm) fun s hs _ => ?_
  rw [← setIntegral_trim hm stronglyMeasurable_condExp hs, ← setIntegral_trim hm hσm hs,
    setIntegral_condExp hm hiτ hs]
  exact setIntegral_stoppedValue_le_of_rightContinuous hX hXrc hσ hτ hle hτT hs

/-- Optional sampling for a right-continuous martingale and bounded stopping times, in
set-integral form. -/
theorem setIntegral_stoppedValue_eq_of_rightContinuous [IsFiniteMeasure P]
    (hM : Martingale M 𝓕 P) (hMrc : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) (hle : σ ≤ τ)
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    ∫ ω in A, stoppedValue M σ ω ∂P = ∫ ω in A, stoppedValue M τ ω ∂P := by
  have h1 := setIntegral_stoppedValue_le_of_rightContinuous hM.supermartingale hMrc hσ hτ hle
    hτT hA
  have hMrc' : ∀ ω t, ContinuousWithinAt ((-M) · ω) (Ici t) t := fun ω t => (hMrc ω t).neg
  have h2 := setIntegral_stoppedValue_le_of_rightContinuous hM.neg.supermartingale hMrc' hσ hτ
    hle hτT hA
  have e : ∀ ρ : Ω → WithTop ℝ≥0, stoppedValue (-M) ρ = fun ω => -stoppedValue M ρ ω :=
    fun _ => rfl
  simp only [e, integral_neg, neg_le_neg_iff] at h2
  exact le_antisymm h2 h1

/-- [P3a] Optional sampling for a right-continuous martingale and bounded stopping times
(Revuz–Yor II.3.2; KS Thm 1.3.22). -/
theorem Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous [IsFiniteMeasure P]
    (hM : Martingale M 𝓕 P) (hMrc : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) (hle : σ ≤ τ)
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) :
    stoppedValue M σ =ᵐ[P] P[stoppedValue M τ | hσ.measurableSpace] := by
  have h1 := Supermartingale.condExp_stoppedValue_le_of_rightContinuous hM.supermartingale hMrc
    hσ hτ hle hτT
  have hMrc' : ∀ ω t, ContinuousWithinAt ((-M) · ω) (Ici t) t := fun ω t => (hMrc ω t).neg
  have h2 := Supermartingale.condExp_stoppedValue_le_of_rightContinuous hM.neg.supermartingale
    hMrc' hσ hτ hle hτT
  have e : ∀ ρ : Ω → WithTop ℝ≥0, stoppedValue (-M) ρ = -stoppedValue M ρ := fun _ => rfl
  rw [e, e] at h2
  filter_upwards [h1, h2, condExp_neg (stoppedValue M τ) hσ.measurableSpace] with ω h1 h2 h3
  rw [h3] at h2
  simp only [Pi.neg_apply, neg_le_neg_iff] at h2
  exact le_antisymm h2 h1

/-- [P3a] A right-continuous martingale stopped at a stopping time is a martingale. -/
theorem Martingale.stoppedProcess_of_rightContinuous [IsFiniteMeasure P]
    (hM : Martingale M 𝓕 P) (hMrc : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (stoppedProcess M τ) 𝓕 P := by
  have hprog := isStronglyProgressive_of_rightContinuous hM.1 hMrc
  have hadp := hprog.stronglyAdapted_stoppedProcess hτ
  have hρ : ∀ u : ℝ≥0, IsStoppingTime 𝓕 (fun ω => min (u : WithTop ℝ≥0) (τ ω)) :=
    fun u => (isStoppingTime_const 𝓕 u).min hτ
  have hρu : ∀ u : ℝ≥0, ∀ ω, min (u : WithTop ℝ≥0) (τ ω) ≤ u := fun u ω => min_le_left _ _
  have hint : ∀ u : ℝ≥0, Integrable (stoppedProcess M τ u) P := fun u => by
    rw [stoppedProcess_eq_stoppedValue]
    exact (tendsto_lintegral_stoppedValue_dyadicUpperTime hM.supermartingale hMrc (hρ u)
      (hρu u)).2.1
  refine ⟨hadp, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (hadp s).aestronglyMeasurable).symm
  have hgt : MeasurableSet[𝓕 s] {ω | (s : WithTop ℝ≥0) < τ ω} := hτ.measurableSet_gt s
  rw [← integral_inter_add_sdiff (𝓕.le s _ hgt) (hint s).integrableOn,
    ← integral_inter_add_sdiff (𝓕.le s _ hgt) (hint t).integrableOn]
  congr 1
  · -- on `A ∩ {s < τ}`: optional sampling between `s ∧ τ` and `t ∧ τ`
    have hB : MeasurableSet[(hρ s).measurableSpace] (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω}) := by
      refine ⟨(le_iSup (fun u => (𝓕 u : MeasurableSpace Ω)) s) _ (hA.inter hgt), fun i => ?_⟩
      by_cases hsi : s ≤ i
      · have h : A ∩ {ω | (s : WithTop ℝ≥0) < τ ω} ∩ {ω | min (s : WithTop ℝ≥0) (τ ω) ≤ i} =
            A ∩ {ω | (s : WithTop ℝ≥0) < τ ω} := by
          refine Set.inter_eq_left.2 fun ω _ => ?_
          show min (s : WithTop ℝ≥0) (τ ω) ≤ i
          exact (min_le_left _ _).trans (WithTop.coe_le_coe.2 hsi)
        rw [h]
        exact 𝓕.mono hsi _ (hA.inter hgt)
      · have h : A ∩ {ω | (s : WithTop ℝ≥0) < τ ω} ∩ {ω | min (s : WithTop ℝ≥0) (τ ω) ≤ i} =
            ∅ := by
          refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
          obtain ⟨⟨_, hsτ⟩, hmin⟩ := hω
          have hi : (i : WithTop ℝ≥0) < s := WithTop.coe_lt_coe.2 (not_le.1 hsi)
          rcases min_le_iff.1 (show min (s : WithTop ℝ≥0) (τ ω) ≤ i from hmin) with h | h
          · exact absurd h (not_le.2 hi)
          · exact absurd h (not_le.2 (hi.trans hsτ))
        rw [h]
        exact @MeasurableSet.empty _ (𝓕 i)
    simp only [stoppedProcess_eq_stoppedValue]
    exact setIntegral_stoppedValue_eq_of_rightContinuous hM hMrc (hρ s) (hρ t)
      (fun ω => min_le_min_right _ (WithTop.coe_le_coe.2 hst)) (hρu t) hB
  · -- on `A \ {s < τ}` both values are `M_τ`
    refine setIntegral_congr_fun ((𝓕.le s _ hA).diff (𝓕.le s _ hgt)) fun ω hω => ?_
    have hτs : τ ω ≤ s := not_lt.1 hω.2
    have hτt : τ ω ≤ t := hτs.trans (WithTop.coe_le_coe.2 hst)
    simp only [stoppedProcess, min_eq_right hτs, min_eq_right hτt]

end P3

end InteractingSLE
