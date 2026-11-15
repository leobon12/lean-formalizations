/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Meas

/-!
# A.3.2: the reconstruction from a continuous strip path

Packet PROVE-ZHAN-A35. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L657–L720, ruling R38): "Mapping back gives the original killed
chordal law as a mixture". PROVE-ZHAN-A34 (`CrosscutA3Meas.lean`) reconstructs the chordal driver from a strip path
`η`: the chordal clock `C(t) = ∫₀ᵗ e^{2(η_r − r)} dr`, its total `reconEnd η`, its inverse `reconTime η`, and the
driver `reconDrv η = reconVal η ∘ reconTime η` with `reconVal η t = V_{C(t)} + e^{η_t − t}`.

This file proves the elementary properties of the reconstruction for an arbitrary **continuous** path `η` (no SLE
input): `C` is continuous and strictly increasing with `C 0 = 0`; `reconTime η` is its inverse on
`[0, reconEnd η)` (the Galois relation `reconTime_le_iff`), continuous there; the driver is continuous there; and if
`reconVal η t` converges as `t → ∞` and `reconEnd η` is finite, the driver extends continuously past `reconEnd η`
(`exists_continuous_extension`). The Cauchy condition along rational times `ValCauchy η` is the countable form of that
convergence.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A35

open A34

/-- The chordal driver at strip time `t`: `V_{C(t)} + e^{η_t − t}` (so `reconDrv η = reconVal η ∘ reconTime η`). -/
def reconVal (η : ℝ≥0 → ℝ) (t : ℝ) : ℝ := reconMark η t + Real.exp (Strip.extPath η t - t)

theorem reconDrv_eq_reconVal (η : ℝ≥0 → ℝ) (s : ℝ) : reconDrv η s = reconVal η (reconTime η s) := rfl

/-- **The countable convergence certificate**: `reconVal η` is Cauchy along the rational times. -/
def ValCauchy (η : ℝ≥0 → ℝ) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, ∀ q q' : ℚ, (m : ℝ) ≤ q → (m : ℝ) ≤ q' →
    |reconVal η q - reconVal η q'| ≤ 1 / ((k : ℝ) + 1)

variable {η : ℝ≥0 → ℝ}

theorem continuous_extPath (hη : Continuous η) : Continuous (Strip.extPath η) :=
  hη.comp continuous_real_toNNReal

theorem continuous_clockIntegrand (hη : Continuous η) :
    Continuous fun r => Real.exp (2 * (Strip.extPath η r - r)) :=
  Real.continuous_exp.comp (continuous_const.mul ((continuous_extPath hη).sub continuous_id))

theorem continuous_markIntegrand (hη : Continuous η) : Continuous fun r => Real.exp (Strip.extPath η r - r) :=
  Real.continuous_exp.comp ((continuous_extPath hη).sub continuous_id)

theorem continuous_reconClock (hη : Continuous η) : Continuous (reconClock η) :=
  intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => (continuous_clockIntegrand hη).intervalIntegrable a b) 0

theorem continuous_reconMark (hη : Continuous η) : Continuous (reconMark η) := by
  have h := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => (continuous_markIntegrand hη).intervalIntegrable a b) 0
  exact continuous_const.sub (continuous_const.mul h)

theorem continuous_reconVal (hη : Continuous η) : Continuous (reconVal η) :=
  (continuous_reconMark hη).add (continuous_markIntegrand hη)

@[simp] theorem reconClock_zero : reconClock η 0 = 0 := intervalIntegral.integral_same

theorem reconVal_zero : reconVal η 0 = -1 + Real.exp (η 0) := by
  simp [reconVal, reconMark, Strip.extPath]

theorem strictMono_reconClock (hη : Continuous η) : StrictMono (reconClock η) := by
  intro a b hab
  have hc := continuous_clockIntegrand hη
  have hsub := intervalIntegral.integral_interval_sub_left (μ := volume) (a := (0 : ℝ)) (b := b) (c := a)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable a b)
    (fun x _ => Real.exp_pos _) hab
  have : reconClock η b - reconClock η a > 0 := by
    simp only [reconClock]; rw [hsub]; exact hpos
  linarith

theorem reconClock_pos (hη : Continuous η) {t : ℝ} (ht : 0 < t) : 0 < reconClock η t := by
  have := strictMono_reconClock hη ht
  rwa [reconClock_zero] at this

theorem reconClock_nonneg (hη : Continuous η) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ reconClock η t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · exact (reconClock_pos hη ht).le

/-! ### The total chordal time -/

theorem ofReal_reconClock_le (t : ℝ≥0) : ENNReal.ofReal (reconClock η t) ≤ reconEnd η :=
  le_iSup (fun t : ℝ≥0 => ENNReal.ofReal (reconClock η t)) t

theorem ofReal_reconClock_lt (hη : Continuous η) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (reconClock η t) < reconEnd η := by
  have h1 : reconClock η t < reconClock η (t + 1) := strictMono_reconClock hη (by linarith)
  have h2 : 0 < reconClock η (t + 1) := reconClock_pos hη (by linarith)
  refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff h2).2 h1) ?_
  have := ofReal_reconClock_le (η := η) (t + 1).toNNReal
  rwa [Real.coe_toNNReal _ (by linarith)] at this

theorem reconEnd_pos (hη : Continuous η) : 0 < reconEnd η := by
  have := ofReal_reconClock_lt hη (le_refl (0 : ℝ))
  rwa [reconClock_zero, ENNReal.ofReal_zero] at this

/-- `reconEnd` along the integer times. -/
theorem reconEnd_eq_iSup_nat (hη : Continuous η) :
    reconEnd η = ⨆ n : ℕ, ENNReal.ofReal (reconClock η n) := by
  refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun n => ?_)
  · refine le_trans ?_ (le_iSup _ ⌈(t : ℝ)⌉₊)
    exact ENNReal.ofReal_le_ofReal ((strictMono_reconClock hη).monotone (Nat.le_ceil _))
  · have := ofReal_reconClock_le (η := η) (n : ℝ≥0)
    simpa using this

/-- Along real times, `ofReal (C t)` increases to `reconEnd`. -/
theorem tendsto_ofReal_reconClock (hη : Continuous η) :
    Tendsto (fun t : ℝ => ENNReal.ofReal (reconClock η t)) atTop (𝓝 (reconEnd η)) := by
  have hmono : Monotone fun t : ℝ => ENNReal.ofReal (reconClock η t) :=
    fun a b hab => ENNReal.ofReal_le_ofReal ((strictMono_reconClock hη).monotone hab)
  have h := tendsto_atTop_iSup hmono
  have he : (⨆ t : ℝ, ENNReal.ofReal (reconClock η t)) = reconEnd η := by
    refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun t => le_iSup_of_le (t : ℝ) le_rfl)
    rcases le_or_gt 0 t with ht | ht
    · have := ofReal_reconClock_le (η := η) t.toNNReal
      rwa [Real.coe_toNNReal _ ht] at this
    · have : reconClock η t ≤ 0 := by
        have := (strictMono_reconClock hη) ht
        rw [reconClock_zero] at this; exact this.le
      rw [ENNReal.ofReal_of_nonpos this]; exact bot_le
  rwa [he] at h

theorem tendsto_reconClock (hη : Continuous η) (hfin : reconEnd η < ⊤) :
    Tendsto (reconClock η) atTop (𝓝 (reconEnd η).toReal) := by
  have h := (ENNReal.tendsto_toReal hfin.ne).comp (tendsto_ofReal_reconClock hη)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  simp [ENNReal.toReal_ofReal (reconClock_nonneg hη ht)]

theorem tendsto_reconClock_nat (hη : Continuous η) (hfin : reconEnd η < ⊤) :
    Tendsto (fun n : ℕ => reconClock η n) atTop (𝓝 (reconEnd η).toReal) :=
  (tendsto_reconClock hη hfin).comp tendsto_natCast_atTop_atTop

theorem reconClock_lt_toReal (hη : Continuous η) (hfin : reconEnd η < ⊤) {t : ℝ} (ht : 0 ≤ t) :
    reconClock η t < (reconEnd η).toReal :=
  (ENNReal.ofReal_lt_iff_lt_toReal (reconClock_nonneg hη ht) hfin.ne).1 (ofReal_reconClock_lt hη ht)

theorem toReal_reconEnd_pos (hη : Continuous η) (hfin : reconEnd η < ⊤) : 0 < (reconEnd η).toReal :=
  ENNReal.toReal_pos (reconEnd_pos hη).ne' hfin.ne

/-! ### The inverse clock -/

/-- The chordal times inside the strip life: `0 ≤ s` and `s < reconEnd η`. -/
def lifeSet (η : ℝ≥0 → ℝ) : Set ℝ := {s | 0 ≤ s ∧ ENNReal.ofReal s < reconEnd η}

theorem reconTime_nonneg (η : ℝ≥0 → ℝ) (s : ℝ) : 0 ≤ reconTime η s :=
  Real.sInf_nonneg fun _ hx => hx.1

theorem exists_le_reconClock {s : ℝ} (hs : s ∈ lifeSet η) : ∃ t, 0 ≤ t ∧ s ≤ reconClock η t := by
  obtain ⟨t, ht⟩ := lt_iSup_iff.1 hs.2
  exact ⟨t, t.coe_nonneg, (ENNReal.ofReal_lt_ofReal_iff'.1 ht).1.le⟩

theorem reconTime_mem (hη : Continuous η) {s : ℝ} (hs : s ∈ lifeSet η) :
    s ≤ reconClock η (reconTime η s) := by
  have hne : {t | 0 ≤ t ∧ s ≤ reconClock η t}.Nonempty := exists_le_reconClock hs
  have hcl : IsClosed {t | 0 ≤ t ∧ s ≤ reconClock η t} :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_le continuous_const (continuous_reconClock hη))
  exact (hcl.csInf_mem hne ⟨0, fun _ hx => hx.1⟩).2

theorem reconTime_le_of_le {s τ : ℝ} (hτ : 0 ≤ τ) (h : s ≤ reconClock η τ) : reconTime η s ≤ τ :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hτ, h⟩

/-- **The Galois relation** between the clock and its inverse on the strip life. -/
theorem reconTime_le_iff (hη : Continuous η) {s τ : ℝ} (hs : s ∈ lifeSet η) (hτ : 0 ≤ τ) :
    reconTime η s ≤ τ ↔ s ≤ reconClock η τ :=
  ⟨fun h => (reconTime_mem hη hs).trans ((strictMono_reconClock hη).monotone h), reconTime_le_of_le hτ⟩

theorem reconClock_reconTime (hη : Continuous η) {s : ℝ} (hs : s ∈ lifeSet η) :
    reconClock η (reconTime η s) = s := by
  have h1 := reconTime_mem hη hs
  have h0 : reconClock η 0 ≤ s := by rw [reconClock_zero]; exact hs.1
  obtain ⟨t, ht, hts⟩ := intermediate_value_Icc (reconTime_nonneg η s)
    (continuous_reconClock hη).continuousOn ⟨h0, h1⟩
  have hle : reconTime η s ≤ t := reconTime_le_of_le ht.1 hts.ge
  rw [le_antisymm ht.2 hle] at hts
  exact hts

theorem reconTime_reconClock (hη : Continuous η) {t : ℝ} (ht : 0 ≤ t) :
    reconTime η (reconClock η t) = t := by
  refine IsLeast.csInf_eq ⟨⟨ht, le_rfl⟩, fun t' ht' => ?_⟩
  exact (strictMono_reconClock hη).le_iff_le.1 ht'.2

theorem reconClock_mem_lifeSet (hη : Continuous η) {t : ℝ} (ht : 0 ≤ t) : reconClock η t ∈ lifeSet η :=
  ⟨reconClock_nonneg hη ht, ofReal_reconClock_lt hη ht⟩

theorem reconDrv_reconClock (hη : Continuous η) {t : ℝ} (ht : 0 ≤ t) :
    reconDrv η (reconClock η t) = reconVal η t := by
  rw [reconDrv_eq_reconVal, reconTime_reconClock hη ht]

theorem reconDrv_zero (hη : Continuous η) (h0 : η 0 = 0) : reconDrv η 0 = 0 := by
  have := reconDrv_reconClock hη (le_refl (0 : ℝ))
  rw [reconClock_zero, reconVal_zero, h0, Real.exp_zero] at this
  rw [this]; norm_num

theorem lt_reconTime_iff (hη : Continuous η) {s a : ℝ} (hs : s ∈ lifeSet η) (ha : 0 ≤ a) :
    a < reconTime η s ↔ reconClock η a < s := by
  rw [← not_le, reconTime_le_iff hη hs ha, not_le]

/-- **The inverse clock is continuous on the strip life.** -/
theorem continuousOn_reconTime (hη : Continuous η) : ContinuousOn (reconTime η) (lifeSet η) := by
  intro s₀ hs₀
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a 0 with ha0 | ha0
    · exact Eventually.of_forall fun s => lt_of_lt_of_le ha0 (reconTime_nonneg η s)
    · have h := (lt_reconTime_iff hη hs₀ ha0).1 ha
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds h)] with s hs hs'
      exact (lt_reconTime_iff hη hs ha0).2 hs'
  · obtain ⟨τ, hτ1, hτ2⟩ := exists_between hb
    have hτ0 : 0 ≤ τ := (reconTime_nonneg η s₀).trans hτ1.le
    have h : s₀ < reconClock η τ := by
      rw [← reconClock_reconTime hη hs₀]; exact strictMono_reconClock hη hτ1
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)] with s hs hs'
    exact lt_of_le_of_lt ((reconTime_le_iff hη hs hτ0).2 (le_of_lt hs')) hτ2

theorem continuousOn_reconDrv (hη : Continuous η) : ContinuousOn (reconDrv η) (lifeSet η) :=
  (continuous_reconVal hη).comp_continuousOn (continuousOn_reconTime hη)

theorem mem_lifeSet_iff (hfin : reconEnd η < ⊤) {s : ℝ} : s ∈ lifeSet η ↔ s ∈ Ico 0 (reconEnd η).toReal := by
  refine ⟨fun h => ⟨h.1, (ENNReal.ofReal_lt_iff_lt_toReal h.1 hfin.ne).1 h.2⟩, fun h => ⟨h.1, ?_⟩⟩
  exact (ENNReal.ofReal_lt_iff_lt_toReal h.1 hfin.ne).2 h.2

/-! ### Extension past the end of the strip life -/

/-- Approaching the end of the strip life, the strip time tends to `∞`. -/
theorem tendsto_reconTime_atTop (hη : Continuous η) (hfin : reconEnd η < ⊤) :
    Tendsto (reconTime η) (𝓝[<] (reconEnd η).toReal) atTop := by
  refine tendsto_atTop.2 fun N => ?_
  set N' := max N 0 with hN'
  have hN'0 : 0 ≤ N' := le_max_right _ _
  have hlt := reconClock_lt_toReal hη hfin hN'0
  have hmem : Ioo (reconClock η N') (reconEnd η).toReal ∈ 𝓝[<] (reconEnd η).toReal := Ioo_mem_nhdsLT hlt
  filter_upwards [hmem] with s hs
  have hs0 : 0 ≤ s := (reconClock_nonneg hη hN'0).trans hs.1.le
  have hsl : s ∈ lifeSet η := (mem_lifeSet_iff hfin).2 ⟨hs0, hs.2⟩
  exact (le_max_left N 0).trans ((lt_reconTime_iff hη hsl hN'0).2 hs.1).le

theorem exists_tendsto_of_valCauchy (hη : Continuous η) (h : ValCauchy η) :
    ∃ L, Tendsto (reconVal η) atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨m, hm⟩ := h k
  refine ⟨m, fun t ht => ?_⟩
  -- approximate `t` and `m` by rationals
  have hc := continuous_reconVal hη
  have key : ∀ x : ℝ, (m : ℝ) ≤ x → |reconVal η x - reconVal η m| ≤ 1 / ((k : ℝ) + 1) := by
    intro x hx
    -- the set of `x ≥ m` where the bound holds contains the rationals and is closed
    have hcl : IsClosed {x : ℝ | |reconVal η x - reconVal η m| ≤ 1 / ((k : ℝ) + 1)} :=
      isClosed_le ((hc.sub continuous_const).abs) continuous_const
    have hsub : {x : ℝ | (m : ℝ) < x} ⊆ closure ((fun q : ℚ => (q : ℝ)) '' {q : ℚ | (m : ℝ) < q}) := by
      intro x hx
      rw [mem_closure_iff_nhds]
      intro U hU
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (m : ℝ) (x - δ) < x from
        max_lt hx (by linarith))
      refine ⟨q, hball ?_, q, (le_max_left _ _).trans_lt hq1, rfl⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right (m : ℝ) (x - δ)]
    have hrat : (fun q : ℚ => (q : ℝ)) '' {q : ℚ | (m : ℝ) < q} ⊆
        {x : ℝ | |reconVal η x - reconVal η m| ≤ 1 / ((k : ℝ) + 1)} := by
      rintro _ ⟨q, hq, rfl⟩
      have := hm q (m : ℚ) hq.le (by simp)
      simpa using this
    rcases hx.eq_or_lt with hxm | hxm
    · rw [← hxm, sub_self, abs_zero]; positivity
    · exact closure_minimal hrat hcl (hsub hxm)
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (key t (by exact_mod_cast ht)) hk

theorem valCauchy_of_tendsto {L : ℝ} (h : Tendsto (reconVal η) atTop (𝓝 L)) : ValCauchy η := by
  intro k
  have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) / 2 := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h) _ hε
  refine ⟨⌈N⌉₊, fun q q' hq hq' => ?_⟩
  have h1 := hN q ((Nat.le_ceil N).trans hq)
  have h2 := hN q' ((Nat.le_ceil N).trans hq')
  rw [Real.dist_eq] at h1 h2
  calc |reconVal η q - reconVal η q'| ≤ |reconVal η q - L| + |reconVal η q' - L| := by
        rw [← abs_neg (reconVal η q' - L)]
        exact (abs_sub_le _ L _).trans (by rw [abs_sub_comm L]; simp [abs_sub_comm])
    _ ≤ 1 / ((k : ℝ) + 1) := by linarith

/-- **The continuous extension of the reconstructed driver**: if `η` is continuous with `η 0 = 0`, the total chordal
time `σ = reconEnd η` is finite and `reconVal η t` converges as `t → ∞`, then a continuous `W` with `W 0 = 0` agrees
with `reconDrv η` on `[0, σ)`. -/
theorem exists_continuous_extension (hη : Continuous η) (h0 : η 0 = 0) (hfin : reconEnd η < ⊤) {L : ℝ}
    (hL : Tendsto (reconVal η) atTop (𝓝 L)) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∀ s ∈ Ico (0 : ℝ) (reconEnd η).toReal, W s = reconDrv η s := by
  classical
  set σ := (reconEnd η).toReal with hσ
  have hσ0 : 0 < σ := toReal_reconEnd_pos hη hfin
  set W : ℝ → ℝ := fun s => if s < σ then reconDrv η (max s 0) else L with hW
  have hlife : ∀ s, s < σ → max s 0 ∈ lifeSet η := fun s hs =>
    (mem_lifeSet_iff hfin).2 ⟨le_max_right _ _, max_lt hs hσ0⟩
  have hcont_lt : ContinuousOn (fun s => reconDrv η (max s 0)) (Iio σ) :=
    (continuousOn_reconDrv hη).comp (continuous_id.max continuous_const).continuousOn fun s hs => hlife s hs
  have hleft : Tendsto W (𝓝[<] σ) (𝓝 L) := by
    have h1 : Tendsto (fun s => reconVal η (reconTime η s)) (𝓝[<] σ) (𝓝 L) :=
      hL.comp (tendsto_reconTime_atTop hη hfin)
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT hσ0] with s hs hs0
    simp only [hW, ite_eq_left (show s < σ from hs), max_eq_left hs0.1.le, reconDrv_eq_reconVal]
  refine ⟨W, ?_, ?_, fun s hs => ?_⟩
  · refine continuous_iff_continuousAt.2 fun s => ?_
    rcases lt_trichotomy s σ with hs | rfl | hs
    · have hev : W =ᶠ[𝓝 s] fun s => reconDrv η (max s 0) := by
        filter_upwards [Iio_mem_nhds hs] with x hx
        simp only [hW, ite_eq_left (show x < σ from hx)]
      exact ((hcont_lt.continuousAt (Iio_mem_nhds hs)).congr hev.symm)
    · have hWσ : W σ = L := by simp [hW]
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, hWσ]
        exact hleft
      · refine (continuousWithinAt_const (b := L)).congr (fun x hx => ?_) hWσ
        simp only [hW, ite_eq_right (not_lt.2 (show σ ≤ x from hx))]
    · have hev : W =ᶠ[𝓝 s] fun _ => L := by
        filter_upwards [Ioi_mem_nhds hs] with x hx
        simp only [hW, ite_eq_right (not_lt.2 (show σ ≤ x from hx.le))]
      exact (continuousAt_const).congr hev.symm
  · simp only [hW, ite_eq_left hσ0, max_self]
    exact reconDrv_zero hη h0
  · simp only [hW, ite_eq_left hs.2, max_eq_left hs.1]

end InteractingSLE.ZhanGT4.A35
