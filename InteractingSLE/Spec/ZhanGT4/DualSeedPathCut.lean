/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedPathOn
import InteractingSLE.Spec.Sec6.Prop65Point

/-!
# Zhan's A.1.6, the seeded field XI: the cut-off stopping times `τ_k`

Packet PROVE-ZHAN-GT4-A21. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L507, R38): "The identity extends to time zero by bounded convergence on a protected
rectangle", with A19's localization: `τ_k` is the first time after `ε` at which a seed gap leaves `[1/k, k]`.

For a finite family `Y_i` of continuous adapted real processes (the gaps and scale factors of `SeedConst`), a horizon
`T` (a stopping time) and levels `0 < γ < Γ`:

* `bandMargin γ Γ y = min (|y| − γ) (Γ − |y|)` (positive iff `γ < |y| < Γ`) and the combined margin `bandProc` of the
  family at time `ε + u`;
* **`bandExit`** `= max ε (min T (ε + first u with combined margin ≤ 0))` (capped at `ε + R`), and the `𝓕_ε`-event
  **`bandEv`** `= {ε ≤ T} ∩ {all |Y_i(ε)| strictly inside (γ, Γ)}`;
* `isStoppingTime_bandExit`, `measurableSet_bandEv`, `le_bandExit`, `bandExit_le`;
* **`bounds_of_le_bandExit`**: on `bandEv`, `γ ≤ |Y_i(t)| ≤ Γ` for every `t ∈ [ε, bandExit]`;
* **`eventually_bandEv_bandExit_eq`**: along the levels `γ_k = 1/(k+1)`, `Γ_k = k + 1`, every path on which no `Y_i`
  vanishes on `[ε, T]` is eventually in `bandEv` with `bandExit = T` (compactness).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Sec6.Prop65 (hitLe isStoppingTime_hitLe le_of_le_hitLe le_hitLe_of_forall)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Stopping times after a deterministic time -/

/-- `ε + τ` is an `𝓕`-stopping time when `τ` is a stopping time of the shifted filtration `𝓕_{ε + ·}`. -/
theorem isStoppingTime_const_add {𝓕 : Filtration ℝ≥0 mΩ} {ε : ℝ≥0} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (LP.LP4HB.shiftFiltration 𝓕 ε) fun ω => (τ ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓕 fun ω => ((ε + τ ω : ℝ≥0) : WithTop ℝ≥0) := by
  intro t
  by_cases ht : ε ≤ t
  · have e : {ω | ((ε + τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        {ω | (τ ω : WithTop ℝ≥0) ≤ ((t - ε : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
      constructor
      · intro h; exact le_tsub_of_add_le_left h
      · intro h
        calc ε + τ ω ≤ ε + (t - ε) := add_le_add_right h ε
          _ = t := add_tsub_cancel_of_le ht
    rw [e]
    have h2 : MeasurableSet[𝓕 (ε + (t - ε))] {ω | (τ ω : WithTop ℝ≥0) ≤ ((t - ε : ℝ≥0) : WithTop ℝ≥0)} :=
      hτ (t - ε)
    rwa [add_tsub_cancel_of_le ht] at h2
  · have e : {ω | ((ε + τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, WithTop.coe_le_coe, not_le]
      exact (not_le.1 ht).trans_le le_self_add
    rw [e]
    exact @MeasurableSet.empty _ (𝓕 t)

/-! ### The band margin -/

/-- The margin of `y` in the band `γ ≤ |y| ≤ Γ`. -/
def bandMargin (γ Γ y : ℝ) : ℝ := min (|y| - γ) (Γ - |y|)

theorem continuous_bandMargin (γ Γ : ℝ) : Continuous (bandMargin γ Γ) := by
  unfold bandMargin; fun_prop

theorem bounds_of_bandMargin_nonneg {γ Γ y : ℝ} (h : 0 ≤ bandMargin γ Γ y) : γ ≤ |y| ∧ |y| ≤ Γ := by
  unfold bandMargin at h
  exact ⟨by linarith [le_min_iff.1 h], by linarith [(le_min_iff.1 h).2]⟩

theorem bandMargin_pos {γ Γ y : ℝ} (h1 : γ < |y|) (h2 : |y| < Γ) : 0 < bandMargin γ Γ y := by
  unfold bandMargin
  exact lt_min (by linarith) (by linarith)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The combined margin of a finite family at time `ε + u`. -/
def bandProc (Y : ι → ℝ≥0 → Ω → ℝ) (γ Γ : ℝ) (ε u : ℝ≥0) (ω : Ω) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => bandMargin γ Γ (Y i (ε + u) ω)

theorem bandProc_nonneg_iff {Y : ι → ℝ≥0 → Ω → ℝ} {γ Γ : ℝ} {ε u : ℝ≥0} {ω : Ω} :
    0 ≤ bandProc Y γ Γ ε u ω ↔ ∀ i, 0 ≤ bandMargin γ Γ (Y i (ε + u) ω) := by
  unfold bandProc
  rw [Finset.le_inf'_iff]
  simp

theorem bandProc_pos_iff {Y : ι → ℝ≥0 → Ω → ℝ} {γ Γ : ℝ} {ε u : ℝ≥0} {ω : Ω} :
    0 < bandProc Y γ Γ ε u ω ↔ ∀ i, 0 < bandMargin γ Γ (Y i (ε + u) ω) := by
  unfold bandProc
  rw [Finset.lt_inf'_iff]
  simp

theorem continuous_bandProc {Y : ι → ℝ≥0 → Ω → ℝ} (hYc : ∀ i ω, Continuous (Y i · ω)) (γ Γ : ℝ) (ε : ℝ≥0)
    (ω : Ω) : Continuous fun u => bandProc Y γ Γ ε u ω := by
  unfold bandProc
  refine Continuous.finset_inf'_apply _ fun i _ => (continuous_bandMargin γ Γ).comp ?_
  exact (hYc i ω).comp (continuous_const.add continuous_id)

/-- The combined margin at time `ε + u` is `𝓕_{ε + u}`-measurable. -/
theorem measurable_bandProc {𝓕 : Filtration ℝ≥0 mΩ} {Y : ι → ℝ≥0 → Ω → ℝ} (hYm : ∀ i u, Measurable[𝓕 u] (Y i u))
    (γ Γ : ℝ) (ε u : ℝ≥0) : Measurable[𝓕 (ε + u)] (bandProc Y γ Γ ε u) := by
  have hc : Continuous fun y : ι → ℝ => Finset.univ.inf' Finset.univ_nonempty fun i => bandMargin γ Γ (y i) :=
    Continuous.finset_inf'_apply _ fun i _ => (continuous_bandMargin γ Γ).comp (continuous_apply i)
  exact hc.measurable.comp (@Measurable.of_eval _ _ _ (𝓕 (ε + u)) _ _ fun i => hYm i (ε + u))

/-! ### The band exit time and the good event -/

/-- **The band exit after `ε`**, capped at the horizon `T` (and at `ε + R`): `max ε (min T (ε + τ'))`, `τ'` the
first `u` with combined margin `≤ 0` at time `ε + u`. -/
def bandExit (Y : ι → ℝ≥0 → Ω → ℝ) (γ Γ : ℝ) (ε R : ℝ≥0) (T : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  max ε (min (T ω) (ε + hitLe (bandProc Y γ Γ ε) 0 R ω))

/-- **The good event at time `ε`**: `ε ≤ T` and every `|Y_i(ε)|` strictly inside the band. -/
def bandEv (Y : ι → ℝ≥0 → Ω → ℝ) (γ Γ : ℝ) (ε : ℝ≥0) (T : Ω → ℝ≥0) : Set Ω :=
  {ω | ε ≤ T ω} ∩ {ω | 0 < bandProc Y γ Γ ε 0 ω}

section Exit

variable {Y : ι → ℝ≥0 → Ω → ℝ} {γ Γ : ℝ} {ε R : ℝ≥0} {T : Ω → ℝ≥0}

theorem le_bandExit (ω : Ω) : ε ≤ bandExit Y γ Γ ε R T ω := le_max_left _ _

theorem bandExit_le {ω : Ω} (hω : ε ≤ T ω) : bandExit Y γ Γ ε R T ω ≤ T ω :=
  max_le hω (min_le_left _ _)

theorem isStoppingTime_bandExit {𝓕 : Filtration ℝ≥0 mΩ} (hYc : ∀ i ω, Continuous (Y i · ω))
    (hYm : ∀ i u, Measurable[𝓕 u] (Y i u)) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓕 fun ω => (bandExit Y γ Γ ε R T ω : WithTop ℝ≥0) := by
  have h1 : IsStoppingTime (LP.LP4HB.shiftFiltration 𝓕 ε)
      fun ω => (hitLe (bandProc Y γ Γ ε) 0 R ω : WithTop ℝ≥0) :=
    isStoppingTime_hitLe (fun ω => continuous_bandProc hYc γ Γ ε ω) (fun u => measurable_bandProc hYm γ Γ ε u) 0 R
  have h2 := ((isStoppingTime_const_add h1).min hT).max (isStoppingTime_const 𝓕 ε)
  convert h2 using 1
  funext ω
  simp only [bandExit, WithTop.coe_max, WithTop.coe_min]
  rw [max_comm, min_comm]

theorem measurableSet_bandEv {𝓕 : Filtration ℝ≥0 mΩ} (hYm : ∀ i u, Measurable[𝓕 u] (Y i u))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) : MeasurableSet[𝓕 ε] (bandEv Y γ Γ ε T) := by
  have hm : Measurable[𝓕 ε] (bandProc Y γ Γ ε 0) := by
    have := measurable_bandProc hYm γ Γ ε 0
    rwa [add_zero] at this
  exact (measurableSet_ge_of_isStoppingTime hT ε).inter
    (@measurableSet_lt _ _ _ _ _ (𝓕 ε) _ _ _ _ _ measurable_const hm)

/-- **The band bounds up to the band exit**, on the good event. -/
theorem bounds_of_le_bandExit (hYc : ∀ i ω, Continuous (Y i · ω)) {ω : Ω} (hω : ω ∈ bandEv Y γ Γ ε T)
    {t : ℝ≥0} (hεt : ε ≤ t) (ht : t ≤ bandExit Y γ Γ ε R T ω) (i : ι) : γ ≤ |Y i t ω| ∧ |Y i t ω| ≤ Γ := by
  have hT : bandExit Y γ Γ ε R T ω = min (T ω) (ε + hitLe (bandProc Y γ Γ ε) 0 R ω) :=
    max_eq_right (le_min hω.1 le_self_add)
  rw [hT] at ht
  have hu : t - ε ≤ hitLe (bandProc Y γ Γ ε) 0 R ω := tsub_le_iff_left.2 (ht.trans (min_le_right _ _))
  have h0 : (0 : ℝ) < bandProc Y γ Γ ε 0 ω := hω.2
  have hnn := le_of_le_hitLe (fun ω => continuous_bandProc hYc γ Γ ε ω) h0 hu
  have := bandProc_nonneg_iff.1 hnn i
  rw [add_tsub_cancel_of_le hεt] at this
  exact bounds_of_bandMargin_nonneg this

/-- The band bounds at real times `t ∈ [ε, bandExit]`. -/
theorem bounds_of_mem_Icc_bandExit (hYc : ∀ i ω, Continuous (Y i · ω)) {ω : Ω} (hω : ω ∈ bandEv Y γ Γ ε T)
    {t : ℝ} (ht : t ∈ Icc (ε : ℝ) (bandExit Y γ Γ ε R T ω)) (i : ι) :
    γ ≤ |Y i t.toNNReal ω| ∧ |Y i t.toNNReal ω| ≤ Γ := by
  have ht0 : 0 ≤ t := ε.coe_nonneg.trans ht.1
  refine bounds_of_le_bandExit (R := R) hYc hω ?_ ?_ i
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]; exact ht.1
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]; exact ht.2

end Exit

/-! ### Eventually good along the levels `1/(k+1)`, `k + 1` -/

/-- **Every path on which no `Y_i` vanishes on `[ε, T]` is eventually good, with band exit `T`**, along the levels
`γ_k = 1/(k+1)`, `Γ_k = k + 1` (if `T ≤ ε + R`). -/
theorem eventually_bandEv_bandExit_eq {Y : ι → ℝ≥0 → Ω → ℝ} (hYc : ∀ i ω, Continuous (Y i · ω)) {ε R : ℝ≥0}
    {T : Ω → ℝ≥0} {ω : Ω} (hεT : ε ≤ T ω) (hTR : T ω ≤ ε + R)
    (hne : ∀ i, ∀ t : ℝ≥0, ε ≤ t → t ≤ T ω → Y i t ω ≠ 0) :
    ∀ᶠ k : ℕ in atTop, ω ∈ bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T ∧
      bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T ω = T ω := by
  -- the extreme values of `|Y_i|` on the compact interval `[ε, T]`
  set K : Set ℝ≥0 := Icc ε (T ω) with hK
  have hKc : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := ⟨ε, le_rfl, hεT⟩
  have hfc : Continuous fun t => Finset.univ.inf' Finset.univ_nonempty fun i => |Y i t ω| :=
    Continuous.finset_inf'_apply _ fun i _ => (hYc i ω).abs
  have hgc : Continuous fun t => Finset.univ.sup' Finset.univ_nonempty fun i => |Y i t ω| :=
    Continuous.finset_sup'_apply _ fun i _ => (hYc i ω).abs
  obtain ⟨t₁, ht₁, hmin⟩ := hKc.exists_isMinOn hKne hfc.continuousOn
  obtain ⟨t₂, ht₂, hmax⟩ := hKc.exists_isMaxOn hKne hgc.continuousOn
  set m := Finset.univ.inf' Finset.univ_nonempty fun i => |Y i t₁ ω| with hm
  set M := Finset.univ.sup' Finset.univ_nonempty fun i => |Y i t₂ ω| with hM
  have hm0 : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]
    exact fun i _ => abs_pos.2 (hne i t₁ ht₁.1 ht₁.2)
  have hlow : ∀ t ∈ K, ∀ i, m ≤ |Y i t ω| := fun t ht i =>
    (hmin ht).trans (Finset.inf'_le _ (Finset.mem_univ i))
  have hup : ∀ t ∈ K, ∀ i, |Y i t ω| ≤ M := fun t ht i =>
    (Finset.le_sup' (fun i => |Y i t ω|) (Finset.mem_univ i)).trans (hmax ht)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / m)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt M
  refine eventually_atTop.2 ⟨max N₁ N₂, fun k hk => ?_⟩
  have hk1 : (N₁ : ℝ) ≤ k := by exact_mod_cast (le_max_left _ _).trans hk
  have hk2 : (N₂ : ℝ) ≤ k := by exact_mod_cast (le_max_right _ _).trans hk
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlo : 1 / ((k : ℝ) + 1) < m := by
    rw [div_lt_iff₀ hkpos]
    have : 1 < m * (N₁ + 1) := by
      have h := (div_lt_iff₀ hm0).1 hN₁
      nlinarith
    nlinarith
  have hhi : M < (k : ℝ) + 1 := by linarith
  -- the combined margin is positive on `[ε, T]`
  have hpos : ∀ u : ℝ≥0, u ≤ T ω - ε → 0 < bandProc Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε u ω := by
    intro u hu
    have hmem : ε + u ∈ K := ⟨le_self_add, by
      calc ε + u ≤ ε + (T ω - ε) := add_le_add_right hu ε
        _ = T ω := add_tsub_cancel_of_le hεT⟩
    exact bandProc_pos_iff.2 fun i => bandMargin_pos ((hlow _ hmem i).trans_lt' hlo) ((hup _ hmem i).trans_lt hhi)
  have hω : ω ∈ bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T := ⟨hεT, hpos 0 zero_le⟩
  refine ⟨hω, ?_⟩
  have hTR' : T ω - ε ≤ R := tsub_le_iff_left.2 hTR
  have hhit : T ω - ε ≤ hitLe (bandProc Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε) 0 R ω :=
    le_hitLe_of_forall (fun ω => continuous_bandProc hYc _ _ ε ω) hTR' fun s hs => hpos s hs
  have hle : T ω ≤ ε + hitLe (bandProc Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε) 0 R ω :=
    tsub_le_iff_left.1 hhit
  simp only [bandExit, min_eq_left hle, max_eq_right hεT]

end InteractingSLE.ZhanGT4
