/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CState
import InteractingSLE.Spec.Supplement.BW1PropFrozen
import InteractingSLE.Foundations.Loewner.Concat
import InteractingSLE.Spec.Sec7.ContinuityProb3Coding

/-!
# The own record's trace up to the restart time, and its global Loewner extension

Packet PROVE-AUX61-R1CHART. R1's chart theorem asks, for every record, a continuous driver with a **global** Loewner
trace (`IsLoewnerTrace`), simple and interior on `[0, q]`. A record stopped at `q` only knows the flow up to `q`; the
trace read from it after `q` is that of the driver killed to `0` there, which jumps. So the global trace is the slit
extension of the record's prefix at the horizon `q` (`fullTrace`): the driver frozen at `q` and the trace continued by
the image of the vertical slit (`BW1Prop.isLoewnerTrace_ext_close`, which closes the trace at the horizon by
`TraceClose`). On `[0, q]` it is the trace read from the record (`fullTrace_of_le`).

Countable (Borel) certificates on the record:

* `TraceCert q`: the frozen driver has a generating trace on `[0, q]` (`Sec7.RandRestart.traceSet`). With `StateCert q`
  the trace read from the record is that trace on `[0, q]`, including the tip at `q`
  (`recTrace_eq_of_isGeneratingTrace`), so it generates the chain before `q`, is continuous on `[0, q]`
  (`StateCert.isLoewnerTraceLT_recTrace`), and `fullTrace` is a global Loewner trace of the frozen driver
  (`StateCert.isLoewnerTrace_fullTrace`).
* `InjCert q`: the images of `[0, b]` and `[c, q]` (`b < c` rational) are at positive distance, read at rational
  times; with continuity it gives injectivity on `[0, q]` (`injOn_of_rat`).
* `ImCert q`: the imaginary part is bounded below on every rational window `[a, q]`, `a > 0`; with continuity the trace
  lies in `ℍ` on `(0, q]` (`mapsTo_H_of_rat`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61R1C

open LawUnique Restart.FlowStopIdentG

variable {nL nR : ℕ}

/-! ### The trace read from a record -/

/-- The own trace read from a record, in real time. -/
def recTrace (γ : HistorySpace nL nR) (t : ℝ) : ℂ := histTrace 0 γ t.toNNReal

theorem measurable_recTrace (t : ℝ) : Measurable fun γ : HistorySpace nL nR => recTrace γ t :=
  measurable_histTrace 0 t.toNNReal

/-- **The trace certificate**: the frozen driver read from the record has a generating trace on `[0, q]`. -/
def TraceCert (q : ℝ≥0) (γ : HistorySpace nL nR) : Prop :=
  (frozenDrv q γ, (q : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet

theorem measurableSet_traceCert (q : ℝ≥0) : MeasurableSet {γ : HistorySpace nL nR | TraceCert q γ} :=
  ((measurable_frozenDrv_pi q).prodMk measurable_const) Sec7.RandRestart.measurableSet_traceSet

variable {q : ℝ≥0} {γ : HistorySpace nL nR}

/-- Up to `q` the trace read from the record is the measurable trace of the frozen driver. -/
theorem recTrace_eq_traceAt {t : ℝ} (ht : t ≤ q) (γ : HistorySpace nL nR) :
    recTrace γ t = LP.traceAt t.toNNReal (frozenDrv q γ) := by
  have hle : t.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2 ht
  unfold recTrace histTrace
  rw [Complex.ofReal_zero, zero_add]
  exact LP.traceAt_congr fun r hr => (frozenDrv_of_le (hr.trans hle) γ).symm

theorem StateCert.continuous_rpath (hS : StateCert q γ) : Continuous (Ito.rpath (frozenDrv q γ)) :=
  hS.continuous_frozenDrv.comp continuous_real_toNNReal

theorem StateCert.rpath_zero (hS : StateCert q γ) : Ito.rpath (frozenDrv q γ) 0 = 0 := by
  simp only [Ito.rpath, Real.toNNReal_zero, hS.frozenDrv_zero]

/-- On certified records the frozen driver has a generating trace on `[0, q]`. -/
theorem StateCert.exists_isGeneratingTrace (hS : StateCert q γ) (hT : TraceCert q γ) :
    ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (frozenDrv q γ) q η' := by
  have hc := hS.continuous_frozenDrv
  obtain ⟨η', hη', -⟩ := (Sec7.RandRestart.mem_traceSet_iff hc.continuousOn hS.frozenDrv_zero
    fun _ _ => ⟨_, (hc.tendsto _).mono_left nhdsWithin_le_nhds⟩).1 hT
  exact ⟨η', hη'⟩

/-- The vertical approach to `0` stays in `ℍ`. -/
theorem tendsto_ofReal_mul_I_nhdsWithin_H :
    Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝[H] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Continuous fun y : ℝ => (y : ℂ) * Complex.I := Complex.continuous_ofReal.mul continuous_const
    have h0 := h.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    show 0 < ((y : ℂ) * Complex.I).im
    simpa using hy

/-- **On certified records the trace read from the record is the generating trace on `[0, q]`**, including the tip at
the horizon `q` (closed by `TraceClose`). -/
theorem recTrace_eq_of_isGeneratingTrace (hS : StateCert q γ) {η' : ℝ≥0 → ℂ}
    (hη' : IsGeneratingTrace (frozenDrv q γ) q η') (hq : 0 < q) {t : ℝ} (ht : t ∈ Icc 0 (q : ℝ)) :
    recTrace γ t = η' t.toNNReal := by
  have hc := hS.continuous_frozenDrv
  have h0 := hS.frozenDrv_zero
  rw [recTrace_eq_traceAt ht.2]
  rcases ht.2.lt_or_eq with hlt | heq
  · refine LP.traceAt_eq_of_isGeneratingTrace hη' hc.continuousOn h0 ?_
    exact ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe ht.1).2 hlt)
  · rw [heq, Real.toNNReal_coe]
    have hq1 : (q : ℝ) < (q : ℝ) + 1 := by linarith
    rw [LP.traceAt_eq_trace hq1 hc.continuousOn h0]
    have hLT := LoewnerConcat.isLoewnerTraceLT_prefix hη'
    have hco := LoewnerConcat.continuousOn_prefix hη'
    have htip := TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT hLT hS.continuous_rpath hS.rpath_zero
      (by exact_mod_cast hq) hco
    rw [Real.toNNReal_coe] at htip
    exact (htip.comp tendsto_ofReal_mul_I_nhdsWithin_H).limUnder_eq

/-- **On certified records the trace read from the record generates the chain of the frozen driver before `q` and
is continuous on `[0, q]`.** -/
theorem StateCert.isLoewnerTraceLT_recTrace (hS : StateCert q γ) (hT : TraceCert q γ) (hq : 0 < q) :
    IsLoewnerTraceLT (Ito.rpath (frozenDrv q γ)) q (recTrace γ) ∧ ContinuousOn (recTrace γ) (Icc 0 q) := by
  obtain ⟨η', hη'⟩ := hS.exists_isGeneratingTrace hT
  have heq : EqOn (recTrace γ) (fun t : ℝ => η' t.toNNReal) (Icc 0 q) := fun t ht =>
    recTrace_eq_of_isGeneratingTrace hS hη' hq ht
  have hLT := LoewnerConcat.isLoewnerTraceLT_prefix hη'
  have hco := LoewnerConcat.continuousOn_prefix hη'
  refine ⟨⟨?_, (hco.mono Ico_subset_Icc_self).congr (heq.mono Ico_subset_Icc_self), fun t ht htq => ?_⟩,
    hco.congr heq⟩
  · rw [heq ⟨le_rfl, q.coe_nonneg⟩]
    exact hLT.1
  · rw [hLT.2.2 t ht htq, (heq.mono (Icc_subset_Icc_right htq.le)).image_eq]

/-! ### The global Loewner trace: the slit extension at the horizon -/

/-- **The global trace of a record**: the trace read from the record on `[0, q]`, continued after `q` by the image of
the vertical slit under the inverse map at `q` (the driver frozen at `q`). -/
def fullTrace (q : ℝ≥0) (γ : HistorySpace nL nR) : ℝ → ℂ :=
  YuanCorollary13.extTrace (Ito.rpath (frozenDrv q γ)) (recTrace γ) q

theorem fullTrace_of_le {t : ℝ} (ht : t ≤ q) : fullTrace q γ t = recTrace γ t :=
  YuanCorollary13.extTrace_eq ht

/-- The frozen driver is its own freezing at `q`. -/
theorem extDrive_rpath_frozenDrv :
    YuanCorollary13.extDrive (Ito.rpath (frozenDrv q γ)) q = Ito.rpath (frozenDrv q γ) := by
  funext r
  simp only [YuanCorollary13.extDrive, Ito.rpath, frozenDrv]
  rcases le_total r q with h | h
  · rw [min_eq_left h]
  · have hq : q ≤ r.toNNReal := by
      have h1 := Real.toNNReal_le_toNNReal h
      rwa [Real.toNNReal_coe] at h1
    rw [min_eq_right h, Real.toNNReal_coe, min_self, min_eq_right hq]

/-- **On certified records the global trace is a continuous Loewner trace of the frozen driver.** -/
theorem StateCert.isLoewnerTrace_fullTrace (hS : StateCert q γ) (hT : TraceCert q γ) (hq : 0 < q) :
    IsLoewnerTrace (Ito.rpath (frozenDrv q γ)) (fullTrace q γ) := by
  obtain ⟨hLT, hco⟩ := hS.isLoewnerTraceLT_recTrace hT hq
  have h := Theorem14.BW1Prop.isLoewnerTrace_ext_close hLT hS.continuous_rpath hS.rpath_zero
    (by exact_mod_cast hq) hco
  rwa [extDrive_rpath_frozenDrv] at h

/-! ### Injectivity and interior position from rational-time certificates -/

/-- **Injectivity from rational times**: a path continuous on `[0, q]` whose rational-time images of `[0, b]` and
`[c, q]` (`b < c`) are at positive distance is injective on `[0, q]`. -/
theorem injOn_of_rat {η : ℝ → ℂ} {q : ℚ} (hc : ContinuousOn η (Icc 0 (q : ℝ)))
    (h : ∀ b c : ℚ, 0 ≤ b → b < c → c ≤ q → ∃ m : ℕ, ∀ u v : ℚ, 0 ≤ u → u ≤ b → c ≤ v → v ≤ q →
      1 / ((m : ℝ) + 1) ≤ ‖η u - η v‖) :
    InjOn η (Icc 0 (q : ℝ)) := by
  have key : ∀ s t : ℝ, s ∈ Icc 0 (q : ℝ) → t ∈ Icc 0 (q : ℝ) → s < t → η s ≠ η t := by
    intro s t hs ht hst hEq
    obtain ⟨b, hsb, hbt⟩ := exists_rat_btwn hst
    obtain ⟨c, hbc, hct⟩ := exists_rat_btwn hbt
    have hb0 : (0 : ℚ) ≤ b := by exact_mod_cast hs.1.trans hsb.le
    have hbc' : b < c := by exact_mod_cast hbc
    have hcq : c ≤ q := by exact_mod_cast hct.le.trans ht.2
    obtain ⟨m, hm⟩ := h b c hb0 hbc' hcq
    set ε : ℝ := 1 / ((m : ℝ) + 1) with hε
    have hεpos : 0 < ε := by positivity
    obtain ⟨δ₁, hδ₁, hs'⟩ := Metric.continuousOn_iff.1 hc s hs (ε / 2) (by positivity)
    obtain ⟨δ₂, hδ₂, ht'⟩ := Metric.continuousOn_iff.1 hc t ht (ε / 2) (by positivity)
    obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn (show s < min (s + δ₁) b from lt_min (by linarith) hsb)
    obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn (show max (t - δ₂) c < t from max_lt (by linarith) hct)
    have hub : (u : ℝ) < b := lt_of_lt_of_le hu2 (min_le_right _ _)
    have hus : (u : ℝ) < s + δ₁ := lt_of_lt_of_le hu2 (min_le_left _ _)
    have hvc : (c : ℝ) < v := lt_of_le_of_lt (le_max_right _ _) hv1
    have hvt : t - δ₂ < v := lt_of_le_of_lt (le_max_left _ _) hv1
    have huI : (u : ℝ) ∈ Icc 0 (q : ℝ) := ⟨hs.1.trans hu1.le, (hub.trans hbc).le.trans (by exact_mod_cast hcq)⟩
    have hvI : (v : ℝ) ∈ Icc 0 (q : ℝ) := ⟨(by exact_mod_cast hb0 : (0 : ℝ) ≤ b).trans (hbc.trans hvc).le,
      hv2.le.trans ht.2⟩
    have h1 := hs' u huI (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    have h2 := ht' v hvI (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    have h3 := hm u v (by exact_mod_cast huI.1) (by exact_mod_cast hub.le) (by exact_mod_cast hvc.le)
      (by exact_mod_cast hvI.2)
    rw [dist_eq_norm] at h1 h2
    have htri : ‖η u - η v‖ ≤ ‖η u - η s‖ + ‖η v - η t‖ := by
      have he : η u - η v = (η u - η s) - (η v - η t) := by rw [hEq]; ring
      rw [he]
      exact norm_sub_le _ _
    linarith
  intro s hs t ht hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact key s t hs ht h' hst
  · exact key t s ht hs h' hst.symm

/-- **Interior position from rational times**: a path continuous on `[0, q]` whose imaginary part is bounded below at
the rational times of every window `[a, q]`, `a > 0`, lies in `ℍ` on `(0, q]`. -/
theorem mapsTo_H_of_rat {η : ℝ → ℂ} {q : ℚ} (hc : ContinuousOn η (Icc 0 (q : ℝ)))
    (h : ∀ a : ℚ, 0 < a → a ≤ q → ∃ m : ℕ, ∀ u : ℚ, a ≤ u → u ≤ q → 1 / ((m : ℝ) + 1) ≤ (η u).im) :
    MapsTo η (Ioc 0 (q : ℝ)) H := by
  intro t ht
  obtain ⟨a, ha0, hat⟩ := exists_rat_btwn ht.1
  have ha0' : (0 : ℚ) < a := by exact_mod_cast ha0
  have haq : a ≤ q := by exact_mod_cast hat.le.trans ht.2
  obtain ⟨m, hm⟩ := h a ha0' haq
  set ε : ℝ := 1 / ((m : ℝ) + 1) with hε
  have hεpos : 0 < ε := by positivity
  have htI : t ∈ Icc 0 (q : ℝ) := ⟨ht.1.le, ht.2⟩
  obtain ⟨δ, hδ, ht'⟩ := Metric.continuousOn_iff.1 hc t htI (ε / 2) (by positivity)
  obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn (show max (t - δ) a < t from max_lt (by linarith) hat)
  have hua : (a : ℝ) < u := lt_of_le_of_lt (le_max_right _ _) hu1
  have hut : t - δ < u := lt_of_le_of_lt (le_max_left _ _) hu1
  have huI : (u : ℝ) ∈ Icc 0 (q : ℝ) := ⟨ha0.le.trans hua.le, hu2.le.trans ht.2⟩
  have h1 := ht' u huI (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have h2 := hm u (by exact_mod_cast hua.le) (by exact_mod_cast huI.2)
  rw [dist_eq_norm] at h1
  have h3 : (η u).im - (η t).im ≤ ‖η u - η t‖ := by
    have := Complex.abs_im_le_norm (η u - η t)
    rw [Complex.sub_im] at this
    exact (le_abs_self _).trans this
  show 0 < (η t).im
  linarith

/-- **The injectivity certificate** at rational times of the trace read from the record. -/
def InjCert (q : ℚ) (γ : HistorySpace nL nR) : Prop :=
  ∀ b c : ℚ, 0 ≤ b → b < c → c ≤ q → ∃ m : ℕ, ∀ u v : ℚ, 0 ≤ u → u ≤ b → c ≤ v → v ≤ q →
    1 / ((m : ℝ) + 1) ≤ ‖recTrace γ u - recTrace γ v‖

/-- **The interior certificate** at rational times of the trace read from the record. -/
def ImCert (q : ℚ) (γ : HistorySpace nL nR) : Prop :=
  ∀ a : ℚ, 0 < a → a ≤ q → ∃ m : ℕ, ∀ u : ℚ, a ≤ u → u ≤ q → 1 / ((m : ℝ) + 1) ≤ (recTrace γ u).im

theorem measurableSet_injCert (q : ℚ) : MeasurableSet {γ : HistorySpace nL nR | InjCert q γ} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun b => Measurable.forall fun c => ?_)
  refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const ?_))
  refine Measurable.exists fun m => Measurable.forall fun u => Measurable.forall fun v => ?_
  refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const
    (Measurable.imp measurable_const ?_)))
  exact measurableSet_setOfPred.1
    (measurableSet_le measurable_const ((measurable_recTrace _).sub (measurable_recTrace _)).norm)

theorem measurableSet_imCert (q : ℚ) : MeasurableSet {γ : HistorySpace nL nR | ImCert q γ} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun a => ?_)
  refine Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
  refine Measurable.exists fun m => Measurable.forall fun u => ?_
  refine Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
  exact measurableSet_setOfPred.1
    (measurableSet_le measurable_const (Complex.measurable_im.comp (measurable_recTrace _)))

end InteractingSLE.Sec5.Aux61R1C
