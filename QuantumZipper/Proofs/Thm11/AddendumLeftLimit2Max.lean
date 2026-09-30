import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Doob's weak-type maximal inequality for continuous-path martingales on `ℝ≥0`

Sub-task of THM11-AD3.

* `Thm11Add.measure_exists_abs_gt_le` : for a martingale `D` indexed by `ℝ≥0` with continuous
  paths, `P {∃ t ≤ T, ε < |D t|} ≤ 2 E|D T| / ε` (the proof gives the sharper bound without
  the factor `2`, `measure_exists_abs_gt_le_one`).

Source: Doob's maximal inequality, Revuz–Yor, *Continuous Martingales and Brownian Motion*,
Ch. II, Thm. 1.7 (proof: discrete inequality on finite sets, then monotone limit along dyadic
sets using path continuity). The discrete inequality is mathlib's `MeasureTheory.maximal_ineq`,
applied to the nonnegative grid submartingale `|D (t_k)| = D (t_k) ⊔ -D (t_k)`
(`Submartingale.sup`). The dyadic limit follows `BMOsc.bmOsc_tail`
(`QuantumZipper/Proofs/ItoLite/Oscillation.lean`).
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Thm11Add

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The filtration `𝓕` sampled along a monotone sequence of times. -/
def seqFiltration (𝓕 : Filtration ℝ≥0 mΩ) (u : ℕ → ℝ≥0) (hu : Monotone u) :
    Filtration ℕ mΩ :=
  ⟨fun k => 𝓕 (u k), fun _ _ hij => 𝓕.mono (hu hij), fun k => 𝓕.le (u k)⟩

theorem martingale_seq {𝓕 : Filtration ℝ≥0 mΩ} {D : ℝ≥0 → Ω → ℝ} (hD : Martingale D 𝓕 P)
    {u : ℕ → ℝ≥0} (hu : Monotone u) :
    Martingale (fun k => D (u k)) (seqFiltration 𝓕 u hu) P :=
  ⟨fun k => hD.stronglyAdapted (u k), fun _ _ hij => hD.condExp_ae_eq (hu hij)⟩

/-- Dyadic grid of `[0, T]`. -/
noncomputable def lgrid (T : ℝ≥0) (N k : ℕ) : ℝ≥0 := T * ((k : ℝ≥0) / 2 ^ N)

theorem lgrid_mono (T : ℝ≥0) (N : ℕ) : Monotone (lgrid T N) := by
  intro a b hab
  unfold lgrid
  gcongr

theorem lgrid_top (T : ℝ≥0) (N : ℕ) : lgrid T N (2 ^ N) = T := by
  simp [lgrid]

theorem lgrid_two_mul (T : ℝ≥0) (N k : ℕ) : lgrid T (N + 1) (2 * k) = lgrid T N k := by
  unfold lgrid
  congr 1
  rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm (2 : ℝ≥0),
    mul_div_mul_right _ _ (two_ne_zero)]

theorem coe_lgrid (T : ℝ≥0) (N k : ℕ) :
    ((lgrid T N k : ℝ≥0) : ℝ) = T * ((k : ℝ) / 2 ^ N) := by
  simp [lgrid]

/-- The discrete maximal inequality on one grid. -/
theorem measure_grid_le [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {D : ℝ≥0 → Ω → ℝ} (hD : Martingale D 𝓕 P) {u : ℕ → ℝ≥0} (hu : Monotone u) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ∃ k ≤ n, ε < |D (u k) ω|} ≤ ENNReal.ofReal ((∫ ω, |D (u n) ω| ∂P) / ε) := by
  have hm := martingale_seq hD hu
  have hsub := hm.submartingale.sup hm.neg.submartingale
  have hnn : 0 ≤ ((fun k => D (u k)) ⊔ -fun k => D (u k)) := fun k ω => by
    simp only [Pi.sup_apply, Pi.neg_apply, Pi.zero_apply]
    exact le_sup_iff.2 (by rcases le_total 0 (D (u k) ω) with h | h
                           · exact Or.inl h
                           · exact Or.inr (by linarith))
  have hmax := maximal_ineq hsub hnn (ε := ε.toNNReal) n
  rw [Real.coe_toNNReal _ hε.le] at hmax
  have habs : ∀ k ω, ((fun k => D (u k)) ⊔ -fun k => D (u k)) k ω = |D (u k) ω| := by
    intro k ω; rfl
  simp only [habs] at hmax
  set S := {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => |D (u k) ω|}
  have hsubset : {ω | ∃ k ≤ n, ε < |D (u k) ω|} ⊆ S := by
    rintro ω ⟨k, hk, hak⟩
    exact le_trans hak.le
      (Finset.le_sup' (fun k => |D (u k) ω|) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  have hle : ∫ ω in S, |D (u n) ω| ∂P ≤ ∫ ω, |D (u n) ω| ∂P :=
    setIntegral_le_integral ((hD.integrable _).abs)
      (Eventually.of_forall fun ω => abs_nonneg _)
  have h2 : ENNReal.ofReal ε * P S ≤ ENNReal.ofReal (∫ ω, |D (u n) ω| ∂P) := by
    exact le_trans le_rfl (hmax.trans (ENNReal.ofReal_le_ofReal hle))
  have hS : P S ≤ ENNReal.ofReal (∫ ω, |D (u n) ω| ∂P) / ENNReal.ofReal ε := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hε])) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact h2
  rw [← ENNReal.ofReal_div_of_pos hε] at hS
  exact (measure_mono hsubset).trans hS

/-- Doob's weak maximal inequality for continuous-path martingales (sharp constant). -/
theorem measure_exists_abs_gt_le_one [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {D : ℝ≥0 → Ω → ℝ} (hD : Martingale D 𝓕 P) (hc : ∀ ω, Continuous fun t => D t ω)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ∃ t ≤ T, ε < |D t ω|} ≤ ENNReal.ofReal ((∫ ω, |D T ω| ∂P) / ε) := by
  set E : ℕ → Set Ω := fun N => {ω | ∃ k ≤ 2 ^ N, ε < |D (lgrid T N k) ω|}
  have hmono : Monotone E := by
    refine monotone_nat_of_le_succ fun N ω hω => ?_
    obtain ⟨k, hk, h⟩ := hω
    refine ⟨2 * k, by rw [pow_succ]; omega, ?_⟩
    rw [lgrid_two_mul]
    exact h
  have hcover : {ω | ∃ t ≤ T, ε < |D t ω|} ⊆ ⋃ N, E N := by
    rintro ω ⟨r, hrT, hr⟩
    rcases eq_zero_or_pos T with hT | hT
    · subst hT
      have : r = 0 := le_antisymm hrT bot_le
      subst this
      exact mem_iUnion.2 ⟨0, 0, Nat.zero_le _, by simpa [lgrid] using hr⟩
    have hs' : (0 : ℝ) < T := hT
    have hr2 : ((r : ℝ≥0) : ℝ) ≤ T := by exact_mod_cast hrT
    set x : ℝ := ((r : ℝ≥0) : ℝ) / T
    have hx0 : 0 ≤ x := div_nonneg r.2 hs'.le
    have hx1 : x ≤ 1 := (div_le_one hs').2 hr2
    have hlim : Tendsto (fun N : ℕ => (⌊x * 2 ^ N⌋₊ : ℝ) / 2 ^ N) atTop (𝓝 x) :=
      (tendsto_nat_floor_mul_div_atTop hx0).comp
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have hlim2 : Tendsto (fun N : ℕ => ((lgrid T N ⌊x * 2 ^ N⌋₊ : ℝ≥0) : ℝ)) atTop
        (𝓝 ((r : ℝ≥0) : ℝ)) := by
      have h3 := (tendsto_const_nhds (x := (T : ℝ))).mul hlim
      have hx : (T : ℝ) * x = ((r : ℝ≥0) : ℝ) := by
        simp only [x]; field_simp
      rw [hx] at h3
      refine h3.congr fun N => ?_
      rw [coe_lgrid]
    have hlim3 := NNReal.tendsto_coe.1 hlim2
    have hlim4 : Tendsto (fun N : ℕ => |D (lgrid T N ⌊x * 2 ^ N⌋₊) ω|) atTop
        (𝓝 |D r ω|) :=
      ((continuous_abs.comp (hc ω)).tendsto _).comp hlim3
    obtain ⟨N, hN⟩ := (hlim4.eventually (lt_mem_nhds hr)).exists
    refine mem_iUnion.2 ⟨N, ⌊x * 2 ^ N⌋₊, ?_, hN⟩
    refine Nat.floor_le_of_le ?_
    push_cast
    exact mul_le_of_le_one_left (by positivity) hx1
  refine (measure_mono hcover).trans ?_
  rw [hmono.measure_iUnion]
  refine iSup_le fun N => ?_
  have := measure_grid_le hD (lgrid_mono T N) (2 ^ N) hε
  rwa [lgrid_top] at this

/-- **Doob's weak-type maximal inequality** for a continuous-path real martingale on `ℝ≥0`
(Revuz–Yor, Ch. II, Thm. 1.7), in the form used by THM11-AD3. -/
theorem measure_exists_abs_gt_le [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {D : ℝ≥0 → Ω → ℝ} (hD : Martingale D 𝓕 P) (hc : ∀ ω, Continuous fun t => D t ω)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ∃ t ≤ T, ε < |D t ω|} ≤ ENNReal.ofReal (2 * (∫ ω, |D T ω| ∂P) / ε) := by
  refine (measure_exists_abs_gt_le_one hD hc T hε).trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ ∫ ω, |D T ω| ∂P := integral_nonneg fun ω => abs_nonneg _
  rw [mul_div_assoc]
  have : 0 ≤ (∫ ω, |D T ω| ∂P) / ε := div_nonneg h0 hε.le
  linarith

end QuantumZipper.Thm11Add
