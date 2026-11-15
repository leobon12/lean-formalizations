/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowBessel
import InteractingSLE.Foundations.SLE.SpaceFilling.Swallow

/-!
# Lemma LP3: the deterministic real flow

Packet PROVE-LP15. Supplement §6.3, Lemma LP3 (`source/spec/p481-528.md` L22–L35, pp. 481–482). The real
characteristics of the Loewner flow, `u_t(x) = x − W_t + ∫₀ᵗ 2/u_s(x) ds` (QuantumZipper's `IsForwardSol` with a
real starting point), and the deterministic facts the proof of LP3 uses:

* `alive_of_forall_add_le`: a right point stays alive while the driver stays a fixed distance to its left, and
  `u_t(x) ≥ x − W_t` ("the outer characteristics move outward");
* `re_le_of_isForwardSol`: while `u ≥ m`, `x − W_t ≤ u_t(x) ≤ x − W_t + 2t/m` (the displacement bound `2T/ε` of
  the steering step);
* `not_alive_of_restart`, `alive_glue`: the flow restarted at time `T` (driver `W(T + ·) − W_T`, starting point
  `u_T(x)`), with the monotonicity in the starting point (QuantumZipper's `exists_isForwardSol_of_lt`);
* `alive_neg_iff`: reflection `x ↦ −x`, `W ↦ −W` (left points);
* `alive_iff_tamed`, `measurableSet_alive_bmFilt`: being alive at `T` is an event of the natural filtration at `T`
  (through the tamed flow, QuantumZipper's `realTamed`, and `Dynkin.measurable_of_integralEq`);
* `exists_aliveSet`: one measurable set of paths that decides "alive at `T`" for every continuous path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE.LP.LP3

/-- The point `x` is alive on `[0, T]` under the driver `W` (a solution of the centered forward flow exists). -/
def Alive (W : ℝ → ℝ) (x T : ℝ) : Prop := ∃ v, IsForwardSol W (x : ℂ) T v

/-- The driver `t ↦ s · y(t)` of a path `y` (QuantumZipper's `sDrive` for one sample). -/
def pathDrive (s : ℝ) (y : ℝ≥0 → ℝ) : ℝ → ℝ := fun t => s * y t.toNNReal

theorem continuous_pathDrive {s : ℝ} {y : ℝ≥0 → ℝ} (hy : Continuous y) : Continuous (pathDrive s y) :=
  continuous_const.mul (hy.comp continuous_real_toNNReal)

theorem pathDrive_zero {s : ℝ} {y : ℝ≥0 → ℝ} (hy0 : y 0 = 0) : pathDrive s y 0 = 0 := by
  simp [pathDrive, hy0]

section Deterministic

variable {W : ℝ → ℝ}

theorem Alive.mono {x T T' : ℝ} (h : Alive W x T) (hT' : 0 ≤ T') (hTT' : T' ≤ T) : Alive W x T' := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, isForwardSol_restrict hv hT' hTT'⟩

/-- **Survival of a right point.** If the driver stays `m > 0` to the left of `x` on `[0, T]`, then `x` is alive
on `[0, T]`, with a solution satisfying `x − W_t ≤ u_t(x)`. -/
theorem exists_isForwardSol_of_forall_add_le (hW : Continuous W) {x T m : ℝ} (hT : 0 ≤ T) (hm : 0 < m)
    (h : ∀ t ∈ Icc (0 : ℝ) T, W t + m ≤ x) :
    ∃ v, IsForwardSol W (x : ℂ) T v ∧ ∀ t ∈ Icc (0 : ℝ) T, x - W t ≤ (v t).re := by
  have hlow : ∀ t ∈ Icc (0 : ℝ) T, x - W t ≤ realTamed W m x t := by
    intro t ht
    rw [realTamed_eq hW hm x ht.1]
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, realDrift m (realTamed W m x s) :=
      intervalIntegral.integral_nonneg ht.1 fun s _ => by
        unfold realDrift
        exact div_nonneg zero_le_two (hm.le.trans (le_max_right _ _))
    linarith
  have hge : ∀ t ∈ Icc (0 : ℝ) T, m ≤ realTamed W m x t := fun t ht => by
    have := h t ht; have := hlow t ht; linarith
  refine ⟨_, isForwardSol_realTamed hW hm hT hge, fun t ht => ?_⟩
  simpa using hlow t ht

theorem alive_of_forall_add_le (hW : Continuous W) {x T m : ℝ} (hT : 0 ≤ T) (hm : 0 < m)
    (h : ∀ t ∈ Icc (0 : ℝ) T, W t + m ≤ x) : Alive W x T :=
  (exists_isForwardSol_of_forall_add_le hW hT hm h).imp fun _ hv => hv.1

/-- **The displacement bound.** For a right point `x > 0 = W 0` alive on `[0, T]` with `u ≥ m > 0`,
`x − W_t ≤ u_t(x) ≤ x − W_t + 2t/m`. -/
theorem re_le_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x T m : ℝ} (hm : 0 < m)
    {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) (hge : ∀ t ∈ Icc (0 : ℝ) T, m ≤ (v t).re) :
    ∀ t ∈ Icc (0 : ℝ) T, x - W t ≤ (v t).re ∧ (v t).re ≤ x - W t + 2 * t / m := by
  intro t ht
  have heq := realTamed_eq_re_of_isForwardSol hW hW0 hm hv hge t ht
  rw [← heq, realTamed_eq hW hm x ht.1]
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hcont : ContinuousOn (fun s => realDrift m (realTamed W m x s)) (Icc 0 t) :=
    (lipschitz_realDrift hm).continuous.comp_continuousOn
      ((continuousOn_realTamed hW hm (ht.1.trans ht.2) x).mono hsub)
  have hint : IntervalIntegrable (fun s => realDrift m (realTamed W m x s)) volume 0 t :=
    hcont.intervalIntegrable_of_Icc ht.1
  have hval : ∀ s ∈ Icc (0 : ℝ) t, realDrift m (realTamed W m x s) ≤ 2 / m := by
    intro s hs
    have hs' := realTamed_eq_re_of_isForwardSol hW hW0 hm hv hge s (hsub hs)
    have hms : m ≤ realTamed W m x s := by rw [hs']; exact hge s (hsub hs)
    rw [realDrift_of_le hms]
    exact div_le_div_of_nonneg_left zero_le_two hm hms
  have hpos : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ realDrift m (realTamed W m x s) := fun s _ => by
    unfold realDrift
    exact div_nonneg zero_le_two (hm.le.trans (le_max_right _ _))
  have h1 : 0 ≤ ∫ s in (0 : ℝ)..t, realDrift m (realTamed W m x s) :=
    intervalIntegral.integral_nonneg ht.1 fun s hs => hpos s hs
  have h2 : (∫ s in (0 : ℝ)..t, realDrift m (realTamed W m x s)) ≤ ∫ _ in (0 : ℝ)..t, 2 / m :=
    intervalIntegral.integral_mono_on ht.1 hint intervalIntegrable_const hval
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h2
  constructor
  · linarith
  · have : t * (2 / m) = 2 * t / m := by ring
    linarith

/-- A real solution is real: `v t = (v t).re`. -/
theorem eq_ofReal_re_of_isForwardSol (hW : Continuous W) {x T : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : v t = ((v t).re : ℂ) := by
  have him := im_isForwardSol_real hW (ht.1.trans ht.2) hv t ht
  exact Complex.ext (by simp) (by simp [him])

/-- **Restarting a right point.** If `x > 0 = W 0` is alive on `[0, T]` with value `u_T(x) ≤ y` and `y` is not
alive on `[0, S]` under the restarted driver `W(T + ·) − W_T`, then `x` is not alive on `[0, T + S]`. -/
theorem not_alive_of_restart (hW : Continuous W) (hW0 : W 0 = 0) {x T S y : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (hS : 0 ≤ S) {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) (hvy : (v T).re ≤ y)
    (hdead : ¬ Alive (fun r => W (T + r) - W T) y S) : ¬ Alive W x (T + S) := by
  rintro ⟨u, hu⟩
  have huv : u T = v T :=
    eqOn_of_isForwardSol hW (isForwardSol_restrict hu hT (le_add_of_nonneg_right hS)) hv ⟨hT, le_rfl⟩
  have hsh := isForwardSol_shift hu hT hS
  rw [huv, eq_ofReal_re_of_isForwardSol hW hv ⟨hT, le_rfl⟩] at hsh
  have hW' : Continuous fun r => W (T + r) - W T :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  rcases hvy.eq_or_lt with heq | hlt
  · exact hdead ⟨_, heq ▸ hsh⟩
  · have hpos : 0 < (v T).re :=
      re_pos_isForwardSol_real hW hT hv (by rw [hW0]; exact hx) T ⟨hT, le_rfl⟩
    exact hdead (exists_isForwardSol_of_lt hW' hS (by simpa using hpos) hlt hsh)

/-- **Gluing.** If `x` is alive on `[0, T]` and its value `u_T(x)` is alive on `[0, S]` under the restarted
driver, then `x` is alive on `[0, T + S]`, and the restarted solution continues the first one. -/
theorem exists_isForwardSol_glue (hW : Continuous W) {x T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) {w : ℝ → ℂ}
    (hw : IsForwardSol (fun r => W (T + r) - W T) ((v T).re : ℂ) S w) :
    ∃ u, IsForwardSol W (x : ℂ) (T + S) u ∧ u (T + S) = w S := by
  rw [← eq_ofReal_re_of_isForwardSol hW hv ⟨hT, le_rfl⟩] at hw
  refine ⟨_, isForwardSol_glue hT hS hv hw, ?_⟩
  rcases hS.eq_or_lt with h0 | hpos
  · subst h0
    have hw0 := (hw.2 0 ⟨le_rfl, le_rfl⟩).2
    simp only [add_zero, le_refl, ↓reduceIte, sub_self, intervalIntegral.integral_same] at hw0 ⊢
    rw [hw0]; simp
  · have : ¬ T + S ≤ T := by linarith
    simp only [this, ↓reduceIte, add_sub_cancel_left]

/-- **Reflection.** `x` is alive under `W` iff `−x` is alive under `−W`. -/
theorem alive_neg_iff {x T : ℝ} : Alive (fun t => -W t) (-x) T ↔ Alive W x T := by
  have h := exists_isForwardSol_neg_iff (W := W) (x := x) (T := T)
  simpa [Alive] using h

end Deterministic

/-! ### Alive through the tamed flow, and measurability -/

section Tamed

variable {W : ℝ → ℝ}

/-- **Alive through the tamed flow.** For `x > 0 = W 0`, `x` is alive on `[0, T]` iff for some level
`c = 1/(n+1)` the tamed flow at level `c` stays `≥ c` on `[0, T]`. -/
theorem alive_iff_tamed (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    Alive W x T ↔ ∃ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T,
      1 / ((n : ℝ) + 1) ≤ realTamed W (1 / ((n : ℝ) + 1)) x t := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨c₀, hc₀, hle⟩ := exists_pos_le_re_of_isForwardSol hW hW0 hx hT hv
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc₀
    have hc : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    refine ⟨n, fun t ht => ?_⟩
    rw [realTamed_eq_re_of_isForwardSol hW hW0 hc hv (fun s hs => hn.le.trans (hle s hs)) t ht]
    exact hn.le.trans (hle t ht)
  · rintro ⟨n, hn⟩
    exact ⟨_, isForwardSol_realTamed hW Nat.one_div_pos_of_nat hT hn⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- The tamed flow driven by `s B` is adapted to the natural filtration of `B`. -/
theorem measurable_realTamed (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (s : ℝ)
    {c : ℝ} (hc : 0 < c) (x : ℝ) (t : ℝ≥0) :
    Measurable[NonSwallow.bmFilt hBm t] fun ω => realTamed (sDrive s B ω) c x t := by
  have hb := lipschitz_realDrift hc
  have hbM : ∀ y, ‖realDrift c y‖ ≤ 2 / c := fun y => by
    rw [Real.norm_eq_abs]; exact abs_realDrift_le hc y
  have hU := fun ω (r : ℝ≥0) => realTamed_sDrive_eq hBc s hc x ω r
  have hUc : ∀ ω, Continuous fun r : ℝ≥0 => realTamed (sDrive s B ω) c x r :=
    Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  exact Dynkin.measurable_of_integralEq (NonSwallow.bmFilt hBm) (NonSwallow.bmFilt_adapted hBm) hBc hb
    hbM hU hUc t

/-- **Being alive at `T` is an event of the natural filtration at `T`.** -/
theorem measurableSet_alive_bmFilt (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (s : ℝ) {x : ℝ} (hx : 0 < x) (T : ℝ≥0) :
    MeasurableSet[NonSwallow.bmFilt hBm T] {ω | Alive (sDrive s B ω) x T} := by
  have hW : ∀ ω, Continuous (sDrive s B ω) := fun ω => continuous_sDrive hBc s ω
  have hW0 : ∀ ω, sDrive s B ω 0 = 0 := fun ω => by simp [sDrive, hB0 ω]
  set c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hcdef
  have hcpos : ∀ n, 0 < c n := fun n => Nat.one_div_pos_of_nat
  have hset : {ω | Alive (sDrive s B ω) x T} = ⋃ n : ℕ,
      ((⋂ q : ℚ, ⋂ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
        {ω | c n ≤ realTamed (sDrive s B ω) (c n) x ((q : ℝ).toNNReal : ℝ)}) ∩
        {ω | c n ≤ realTamed (sDrive s B ω) (c n) x (T : ℝ)}) := by
    ext ω
    rw [mem_ofPred_eq, alive_iff_tamed (hW ω) (hW0 ω) hx T.coe_nonneg]
    simp only [mem_iUnion, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    refine exists_congr fun n => ⟨fun h => ⟨fun q hq => ?_, h T ⟨T.coe_nonneg, le_rfl⟩⟩, fun h => ?_⟩
    · rw [Real.coe_toNNReal _ hq.1]; exact h q hq
    · refine ge_of_ge_rat T.coe_nonneg
        (continuousOn_realTamed (hW ω) (hcpos n) T.coe_nonneg x) (fun q hq0 hqT => ?_) h.2
      have := h.1 q ⟨hq0, hqT⟩
      rwa [Real.coe_toNNReal _ hq0] at this
  rw [hset]
  refine MeasurableSet.iUnion fun n => MeasurableSet.inter
    (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_) ?_
  · have hle : (q : ℝ).toNNReal ≤ T := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq.1]; exact hq.2
    exact measurableSet_le measurable_const
      ((measurable_realTamed hBm hBc s (hcpos n) x _).mono ((NonSwallow.bmFilt hBm).mono hle) le_rfl)
  · exact measurableSet_le measurable_const (measurable_realTamed hBm hBc s (hcpos n) x T)

end Tamed

/-! ### One measurable set of paths deciding "alive" -/

/-- **A universal measurable set.** There is a measurable set `A` of paths such that a continuous path `y` with
`y 0 = 0` lies in `A` iff `x` is alive on `[0, T]` under the driver `s y`. -/
theorem exists_aliveSet (s : ℝ) {x : ℝ} (hx : 0 < x) (T : ℝ≥0) :
    ∃ A : Set (ℝ≥0 → ℝ), MeasurableSet A ∧
      ∀ y : ℝ≥0 → ℝ, Continuous y → y 0 = 0 → (y ∈ A ↔ Alive (pathDrive s y) x T) := by
  let Ω₀ := {y : ℝ≥0 → ℝ // Continuous y ∧ y 0 = 0}
  let Bc : ℝ≥0 → Ω₀ → ℝ := fun t y => y.1 t
  have hBm : ∀ t, Measurable (Bc t) := fun t => (measurable_pi_apply t).comp measurable_subtype_coe
  have hBc : ∀ y : Ω₀, Continuous (Bc · y) := fun y => y.2.1
  have hB0 : ∀ y : Ω₀, Bc 0 y = 0 := fun y => y.2.2
  have hE := ((NonSwallow.bmFilt hBm).le T) _ (measurableSet_alive_bmFilt hBm hBc hB0 s hx T)
  obtain ⟨A, hA, hAE⟩ := hE
  refine ⟨A, hA, fun y hy hy0 => ?_⟩
  have h := congrArg (fun S : Set Ω₀ => (⟨y, hy, hy0⟩ : Ω₀) ∈ S) hAE
  simp only [mem_preimage, eq_iff_iff] at h
  exact h

end InteractingSLE.LP.LP3
