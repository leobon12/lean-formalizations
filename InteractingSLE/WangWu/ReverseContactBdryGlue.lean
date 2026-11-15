/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactBdryIdent
import InteractingSLE.WangWu.ReverseContactChart

/-!
# Good reverse histories for the two-slit chart

Packet PROVE-WW-B14 (glued-space part of the contact step's N3). On the glued space the reverse slit is read from the
reverse history `y = p.2` through its frozen regularized driver `w_y = regPath (revStop s y)` (the driver of B13's
explicit reverse mean `histMean`). This file gives a **Borel** set `BetaSet s` of histories on which `w_y` generates a
simple proper Loewner trace `frzLine s y` whose hull at time `s` is B13's `histHull s y`, with strictly ordered force
positions `v_L(y) < 0 < v_R(y)`.

* `chartAR_pos`, `chartAL_neg`: for a simple proper trace and `t > 0`, `a_L < 0 < a_R` (if `a_R = 0`, every `x > 0` is
  sent to a real point, so the tip `F̄_t(0) = η(t)` would be real).
* `BetaSet`, `measurableSet_betaSet`, **`trace_of_mem_betaSet`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open MartChar.RealFlow
open LawUnique
open Sec4 (regPath posLProc posRProc)

/-! ### Strict force positions -/

section Strict

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- **The right force image is strictly right of the driver** at positive times of a simple proper trace. -/
theorem chartAR_pos (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 < t) : 0 < chartAR W t := by
  by_contra hle
  have h0 : chartAR W t = 0 := le_antisymm (not_lt.1 hle) (chartAR_nonneg hW ht.le)
  have hreal : ∀ n : ℕ, (extendFrom H (fwdMapInv W t) ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)).im = 0 := by
    intro n
    have hxH := extendFrom_mem_Hbar hη hW hW0 ht.le (x := (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ))
      (show (0 : ℝ) ≤ ((((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)).im by simp)
    refine le_antisymm (not_lt.1 fun hpos => ?_) hxH
    have h1 := lt_rightImg_sub_of_extendFrom_mem_H hη hW hW0 ht.le hpos
    rw [← chartAR, h0] at h1
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have h := im_extendFrom_eq_zero_of_tendsto hη hW hW0 ht.le tendsto_one_div_add_atTop_nhds_zero_nat hreal
  rw [Complex.ofReal_zero, extendFrom_zero hη hW hW0 ht.le] at h
  have h3 : (0 : ℝ) < (η t).im := hγ.mem_H t ht
  rw [h] at h3
  exact lt_irrefl _ h3

/-- **The left force image is strictly left of the driver** at positive times of a simple proper trace. -/
theorem chartAL_neg (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 < t) : chartAL W t < 0 := by
  by_contra hle
  have h0 : chartAL W t = 0 := le_antisymm (chartAL_nonpos hW ht.le) (not_lt.1 hle)
  have hreal : ∀ n : ℕ, (extendFrom H (fwdMapInv W t) ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)).im = 0 := by
    intro n
    have hxH := extendFrom_mem_Hbar hη hW hW0 ht.le (x := (((-(1 / ((n : ℝ) + 1))) : ℝ) : ℂ))
      (show (0 : ℝ) ≤ ((((-(1 / ((n : ℝ) + 1))) : ℝ) : ℂ)).im by simp)
    refine le_antisymm (not_lt.1 fun hpos => ?_) hxH
    have h1 := neg_rightImg_sub_lt_of_extendFrom_mem_H hη hW hW0 ht.le hpos
    rw [← chartAL, h0] at h1
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hlim : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have h := im_extendFrom_eq_zero_of_tendsto hη hW hW0 ht.le hlim hreal
  rw [Complex.ofReal_zero, extendFrom_zero hη hW hW0 ht.le] at h
  have h3 : (0 : ℝ) < (η t).im := hγ.mem_H t ht
  rw [h] at h3
  exact lt_irrefl _ h3

end Strict

/-! ### The Borel set of good reverse histories -/

section BetaSet

/-- The frozen regularized driver `w_y = regPath (revStop s y)` of a reverse history (the driver of `histMean`). -/
def frzDrive (s : ℚ) (y : HistorySpace 1 1) : ℝ≥0 → ℝ := regPath (revStop s y)

/-- Its trace, read at every real time by the measurable trace evaluation. -/
def frzLine (s : ℚ) (y : HistorySpace 1 1) (u : ℝ) : ℂ := LP.traceAt u.toNNReal (frzDrive s y)

/-- The centred left force position of `histMean` at the stop. -/
def frzVL (s : ℚ) (y : HistorySpace 1 1) : ℝ :=
  posLProc 0 (revStopT s) (revStop s y) - regPath (revStop s y) (revStopT s)

/-- The centred right force position of `histMean` at the stop. -/
def frzVR (s : ℚ) (y : HistorySpace 1 1) : ℝ :=
  posRProc 0 (revStopT s) (revStop s y) - regPath (revStop s y) (revStopT s)

theorem measurable_frzDrive (s : ℚ) : Measurable (frzDrive s) :=
  measurable_pi_iff.2 fun t => (Sec4.measurable_regPath_apply t).comp (measurable_revStop s)

theorem measurable_frzLine (s : ℚ) (u : ℝ) : Measurable fun y => frzLine s y u :=
  (LP.measurable_traceAt _).comp (measurable_frzDrive s)

theorem measurable_frzVL (s : ℚ) : Measurable (frzVL s) :=
  ((Sec4.measurable_posLProc 0 (revStopT s)).comp (measurable_revStop s)).sub
    ((Sec4.measurable_regPath_apply _).comp (measurable_revStop s))

theorem measurable_frzVR (s : ℚ) : Measurable (frzVR s) :=
  ((Sec4.measurable_posRProc 0 (revStopT s)).comp (measurable_revStop s)).sub
    ((Sec4.measurable_regPath_apply _).comp (measurable_revStop s))

/-- **Good reverse histories**: the frozen driver codes a transient generating trace (`traceSet`), starts at `0`, its
trace satisfies the window conditions (so it is a simple proper arc), agrees with B13's `histLine` at the rational
times of `[0, s]`, and the force positions are strictly ordered. -/
def BetaSet (s : ℚ) : Set (HistorySpace 1 1) :=
  {y | (frzDrive s y, (⊤ : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet} ∩ {y | frzDrive s y 0 = 0} ∩
    {y | ImPosCond (frzLine s y)} ∩ {y | SepCond (frzLine s y)} ∩
    {y | ∀ q : ℚ, 0 ≤ q → q ≤ s → histLine y q = frzLine s y q} ∩ {y | frzVL s y < 0} ∩ {y | 0 < frzVR s y}

theorem measurableSet_betaSet (s : ℚ) : MeasurableSet (BetaSet s) := by
  have h1 : MeasurableSet {y : HistorySpace 1 1 | (frzDrive s y, (⊤ : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet} :=
    ((measurable_frzDrive s).prodMk measurable_const) Sec7.RandRestart.measurableSet_traceSet
  have h2 : MeasurableSet {y : HistorySpace 1 1 | frzDrive s y 0 = 0} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp (measurable_frzDrive s)) measurable_const
  have h3 : MeasurableSet {y : HistorySpace 1 1 | ImPosCond (frzLine s y)} := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b => ?_)
    refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.exists fun m => ?_))
    refine Measurable.forall fun p => Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
    exact measurableSet_setOfPred.1
      (measurableSet_le measurable_const (Complex.measurable_im.comp (measurable_frzLine s _)))
  have h4 : MeasurableSet {y : HistorySpace 1 1 | SepCond (frzLine s y)} := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b =>
      Measurable.forall fun c => Measurable.forall fun d => ?_)
    refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.exists fun m => ?_))))
    refine Measurable.forall fun p => Measurable.forall fun q => Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const ?_)))
    exact measurableSet_setOfPred.1
      (measurableSet_le measurable_const ((measurable_frzLine s _).sub (measurable_frzLine s _)).norm)
  have h5 : MeasurableSet {y : HistorySpace 1 1 | ∀ q : ℚ, 0 ≤ q → q ≤ s → histLine y q = frzLine s y q} := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun q => ?_)
    refine Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
    exact measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_histLine _) (measurable_frzLine s _))
  have h6 : MeasurableSet {y : HistorySpace 1 1 | frzVL s y < 0} :=
    measurableSet_lt (measurable_frzVL s) measurable_const
  have h7 : MeasurableSet {y : HistorySpace 1 1 | 0 < frzVR s y} :=
    measurableSet_lt measurable_const (measurable_frzVR s)
  exact (((((h1.inter h2).inter h3).inter h4).inter h5).inter h6).inter h7

/-- **On a good reverse history, the frozen driver generates a simple proper Loewner trace whose hull at time `s` is
B13's `histHull s y`.** -/
theorem trace_of_mem_betaSet {s : ℚ} (hs : 0 < s) {y : HistorySpace 1 1} (hy : y ∈ BetaSet s) :
    Continuous (Ito.rpath (frzDrive s y)) ∧ Ito.rpath (frzDrive s y) 0 = 0 ∧
      IsLoewnerTrace (Ito.rpath (frzDrive s y)) (frzLine s y) ∧ IsProperArc (frzLine s y) ∧
      histHull s y = fwdHull (Ito.rpath (frzDrive s y)) s ∧ frzVL s y < 0 ∧ 0 < frzVR s y := by
  obtain ⟨⟨⟨⟨⟨⟨htr, hw0⟩, him⟩, hsep⟩, hrat⟩, hvL⟩, hvR⟩ := hy
  have hcont' : Continuous (Ito.rpath (frzDrive s y)) := Sec4.continuous_rpath_regPath _
  have hcont : Continuous (frzDrive s y) := by
    have := hcont'.comp NNReal.continuous_coe
    refine this.congr fun t => ?_
    simp [Ito.rpath]
  have hc : ContinuousOn (frzDrive s y) {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} := hcont.continuousOn
  obtain ⟨η, hη, htend⟩ := (Sec7.RandRestart.mem_traceSet_iff hc hw0
    (fun _ h => absurd h (lt_irrefl _))).1 htr
  have hline : frzLine s y = fun u : ℝ => η u.toNNReal := by
    funext u
    exact LP.traceAt_eq_of_isGeneratingTrace hη hc hw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hLT : IsLoewnerTrace (Ito.rpath (frzDrive s y)) (frzLine s y) := by
    rw [hline]
    exact isLoewnerTrace_of_isGeneratingTrace hη
  have hP : IsProperArc (frzLine s y) := by
    refine isProperArc_of_conds ?_ ?_ hsep him ?_
    · rw [hline]; exact (hηc.comp continuous_real_toNNReal).continuousOn
    · rw [hline]; simpa using hη.1
    · rw [hline]; exact (htend rfl).comp tendsto_real_toNNReal_atTop
  have hw0' : Ito.rpath (frzDrive s y) 0 = 0 := by
    have h : frzDrive s y 0 = 0 := hw0
    simp [Ito.rpath, h]
  refine ⟨hcont', hw0', hLT, hP, ?_, hvL, hvR⟩
  -- the hull
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  rw [fwdHull_eq_image_Ioc hLT hP hs']
  have himg : histLine y '' ratWindow 0 s = frzLine s y '' ratWindow 0 s := by
    refine image_congr fun u hu => ?_
    obtain ⟨p, rfl, hp0, hps⟩ := hu
    exact hrat p hp0 hps
  rw [histHull, himg, closure_image_ratWindow (hP.cont.mono Icc_subset_Ici_self)]
  ext z
  constructor
  · rintro ⟨hzH, u, hu, rfl⟩
    rcases hu.1.eq_or_lt with h0 | hpos
    · exfalso; rw [← h0, hP.zero] at hzH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH)
    · exact ⟨u, ⟨hpos, hu.2⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hP.mem_H u hu.1, u, ⟨hu.1.le, hu.2⟩, rfl⟩

end BetaSet

/-! ### The frozen extension of a simple trace is a simple proper arc -/

section Ext

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {T T' : ℝ}

theorem isLoewnerTraceLT_of_isLoewnerTrace (hη : IsLoewnerTrace W η) (T : ℝ) : IsLoewnerTraceLT W T η :=
  ⟨hη.1, hη.2.1.mono Ico_subset_Ici_self, fun t ht _ => hη.2.2 t ht⟩

/-- **The frozen slit extension of a simple trace is a simple proper arc.** -/
theorem isProperArc_extTrace (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) (hT' : 0 ≤ T')
    (hT'T : T' < T) (hinj : InjOn η (Icc 0 T')) (hH : ∀ u ∈ Ioc 0 T', η u ∈ H) :
    IsProperArc (YuanCorollary13.extTrace W η T') := by
  have hext := hη.isLoewnerTrace_ext hW hW0 hT' hT'T
  have hwH : ∀ r : ℝ, 0 < r → (((2 * Real.sqrt r : ℝ) : ℂ) * I) ∈ H := fun r hr => by
    show (0 : ℝ) < ((((2 * Real.sqrt r : ℝ) : ℂ) * I)).im
    simpa using Real.sqrt_pos.2 hr
  have hF : ∀ r : ℝ, 0 < r → YuanCorollary13.extTrace W η T' (T' + r) =
      fwdMapInv W T' (((2 * Real.sqrt r : ℝ) : ℂ) * I) ∧
      fwdMapInv W T' (((2 * Real.sqrt r : ℝ) : ℂ) * I) ∈ H \ fwdHull W T' := by
    intro r hr
    refine ⟨?_, QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT' (hwH r hr)⟩
    simp only [YuanCorollary13.extTrace, show ¬ (T' + r ≤ T') by linarith, ↓reduceIte, add_sub_cancel_left]
    exact extendFrom_fwdMapInv_eq hW hW0 hT' (hwH r hr)
  have hK : ∀ u ∈ Ioc 0 T', η u ∈ fwdHull W T' := fun u hu => by
    rw [hη.2.2 T' hT' hT'T]
    exact mem_fillH_of_mem_closure (hH u hu) (subset_closure ⟨u, ⟨hu.1.le, hu.2⟩, rfl⟩)
  have hpre : ∀ τ ∈ Icc 0 T', YuanCorollary13.extTrace W η T' τ = η τ := fun τ hτ =>
    YuanCorollary13.extTrace_eq hτ.2
  have hne : ∀ τ ∈ Icc 0 T', ∀ r : ℝ, 0 < r →
      YuanCorollary13.extTrace W η T' τ ≠ YuanCorollary13.extTrace W η T' (T' + r) := by
    intro τ hτ r hr e
    obtain ⟨e2, hm⟩ := hF r hr
    rw [hpre τ hτ, e2] at e
    rcases hτ.1.eq_or_lt with h0 | hpos
    · rw [← h0, hη.1] at e
      have := hm.1; rw [← e] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · exact hm.2 (e ▸ hK τ ⟨hpos, hτ.2⟩)
  refine ⟨hext.2.1, fun a ha b hb hab => ?_, hext.1, fun τ hτ => ?_, ?_⟩
  · rcases le_or_gt a T' with hat | hat <;> rcases le_or_gt b T' with hbt | hbt
    · rw [hpre a ⟨ha, hat⟩, hpre b ⟨hb, hbt⟩] at hab
      exact hinj ⟨ha, hat⟩ ⟨hb, hbt⟩ hab
    · exfalso
      have := hne a ⟨ha, hat⟩ (b - T') (by linarith)
      rw [show T' + (b - T') = b by ring] at this
      exact this hab
    · exfalso
      have := hne b ⟨hb, hbt⟩ (a - T') (by linarith)
      rw [show T' + (a - T') = a by ring] at this
      exact this hab.symm
    · obtain ⟨e1, -⟩ := hF (a - T') (by linarith)
      obtain ⟨e2, -⟩ := hF (b - T') (by linarith)
      rw [show T' + (a - T') = a by ring] at e1
      rw [show T' + (b - T') = b by ring] at e2
      rw [e1, e2] at hab
      have h2 := congrArg (fwdMap W T') hab
      rw [QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hT' (hwH _ (by linarith)),
        QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hT' (hwH _ (by linarith))] at h2
      have h3 := congrArg Complex.im h2
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at h3
      have h4 : Real.sqrt (a - T') = Real.sqrt (b - T') := by linarith
      have h5 := congrArg (fun x => x ^ 2) h4
      simp only [Real.sq_sqrt (show 0 ≤ a - T' by linarith), Real.sq_sqrt (show 0 ≤ b - T' by linarith)] at h5
      linarith
  · rcases le_or_gt τ T' with hτt | hτt
    · rw [hpre τ ⟨hτ.le, hτt⟩]; exact hH τ ⟨hτ, hτt⟩
    · obtain ⟨e1, hm⟩ := hF (τ - T') (by linarith)
      rw [show T' + (τ - T') = τ by ring] at e1
      rw [e1]; exact hm.1
  · obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hT'
    rw [tendsto_atTop_atTop]
    intro B
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hwH 1 one_pos))
    refine ⟨T' + ((|B| + C + 1) / 2) ^ 2 + 1, fun τ hτ => ?_⟩
    have hr : 0 < τ - T' := by nlinarith [sq_nonneg ((|B| + C + 1) / 2)]
    obtain ⟨e1, -⟩ := hF (τ - T') hr
    rw [show T' + (τ - T') = τ by ring] at e1
    rw [e1]
    have h1 := hC _ (hwH _ hr)
    have hn : ‖(((2 * Real.sqrt (τ - T') : ℝ) : ℂ) * I)‖ = 2 * Real.sqrt (τ - T') := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsq : (|B| + C + 1) / 2 ≤ Real.sqrt (τ - T') := by
      rw [show (|B| + C + 1) / 2 = Real.sqrt (((|B| + C + 1) / 2) ^ 2) from
        (Real.sqrt_sq (by have := abs_nonneg B; linarith)).symm]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith [le_abs_self B, norm_sub_norm_le (((2 * Real.sqrt (τ - T') : ℝ) : ℂ) * I)
      (fwdMapInv W T' (((2 * Real.sqrt (τ - T') : ℝ) : ℂ) * I)),
      norm_sub_rev (fwdMapInv W T' (((2 * Real.sqrt (τ - T') : ℝ) : ℂ) * I)) (((2 * Real.sqrt (τ - T') : ℝ) : ℂ) * I)]

/-- A curve agreeing with a simple proper arc on `[0, ∞)` is a simple proper arc. -/
theorem IsProperArc.congr {γ γ' : ℝ → ℂ} (hγ : IsProperArc γ) (h : EqOn γ' γ (Ici 0)) : IsProperArc γ' where
  cont := hγ.cont.congr h
  inj := fun a ha b hb e => hγ.inj ha hb (by rw [← h ha, ← h hb]; exact e)
  zero := by rw [h self_mem_Ici]; exact hγ.zero
  mem_H := fun t ht => by rw [h (mem_Ici.2 ht.le)]; exact hγ.mem_H t ht
  tendsto := hγ.tendsto.congr' (by
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [h (mem_Ici.2 ht)])

end Ext

/-! ### Almost every reverse history is good -/

section AeGood

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {rL rR : ℝ}

/-- **Almost every killed history of a nonnegative two-seed chain is a good reverse history** (`BetaSet s`): its
frozen driver generates the frozen extension of the seed line, a simple proper transient trace. -/
theorem ae_killedHistory_mem_betaSet [IsProbabilityMeasure P] (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hE : IsMarkedChain LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) {s : ℚ}
    (hs : 0 < s) : ∀ᵐ ω ∂P, killedHistory W VL VR ζ ω ∈ BetaSet s := by
  filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hE,
    ae_revStop_good hL hR hE hs, hE.2.2.2.2] with ω hω hg hp
  obtain ⟨hζ, -, hLT, hP, -⟩ := hω
  obtain ⟨hgs, hVLle, hWVR, -⟩ := hg
  set y := killedHistory W VL VR ζ ω with hy
  set T : ℝ≥0 := revStopT s with hTdef
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hT : (T : ℝ) = s := by rw [hTdef, revStopT, Real.coe_toNNReal _ hs'.le]
  have hTpos : (0 : ℝ) < T := by rw [hT]; exact hs'
  have hWc : Continuous fun t => W t ω := by
    have h := hgs.2.1
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  have hW0 : W 0 ω = 0 := hp.1
  have hrw : Continuous (Ito.rpath (W · ω)) := continuous_rpath hWc
  have hrw0 : Ito.rpath (W · ω) 0 = 0 := by simp [Ito.rpath, hW0]
  -- the frozen driver
  have hC : Sec4.IsContHist (revStop s y) := Sec4.isContHist_stopHistory hgs
  have hfrz : frzDrive s y = fun t => W (min t T) ω := by
    funext t
    rw [frzDrive, hC.regPath_eq]
    exact Sec4.histPath_stopHistory hgs.1 hgs.2.1 t
  have hfrz0 : frzDrive s y 0 = 0 := by rw [hfrz]; simp [hW0]
  have hfrzc : Continuous (frzDrive s y) := by
    rw [hfrz]; exact hWc.comp (continuous_id.min continuous_const)
  -- the frozen extension of the seed line
  have hLT' := isLoewnerTraceLT_of_isLoewnerTrace hLT ((T : ℝ) + 1)
  set ext := YuanCorollary13.extTrace (Ito.rpath (W · ω)) (seedLine ζ W ω) (T : ℝ) with hext
  have hextLT := hLT'.isLoewnerTrace_ext hrw hrw0 T.2 (lt_add_one _)
  have hextP : IsProperArc ext := isProperArc_extTrace hLT' hrw hrw0 T.2 (lt_add_one _)
    (hP.inj.mono Icc_subset_Ici_self) fun u hu => hP.mem_H u hu.1
  have hdrv : (fun r : ℝ => frzDrive s y r.toNNReal) = YuanCorollary13.extDrive (Ito.rpath (W · ω)) (T : ℝ) := by
    funext r
    rw [hfrz, YuanCorollary13.extDrive, Ito.rpath]
    rw [Monotone.map_min (fun a b h => Real.toNNReal_le_toNNReal h), Real.toNNReal_coe]
  -- the generating trace of the frozen driver
  set η' : ℝ≥0 → ℂ := fun t => ext t with hη'
  have hgen : IsGeneratingTrace (frzDrive s y) ⊤ η' := by
    refine ⟨by simp [hη', hext, YuanCorollary13.extTrace_eq (show (0 : ℝ) ≤ T from T.2), hP.zero], ?_,
      fun t _ => ?_⟩
    · exact (hextLT.2.1.comp_continuous NNReal.continuous_coe fun t => t.2).continuousOn
    · have hh := hextLT.2.2 (t : ℝ) t.2
      have himg : η' '' Icc 0 t = ext '' Icc 0 (t : ℝ) := by
        ext z
        constructor
        · rintro ⟨u, hu, rfl⟩; exact ⟨u, ⟨u.2, hu.2⟩, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact ⟨⟨u, hu.1⟩, ⟨zero_le, show (⟨u, hu.1⟩ : ℝ≥0) ≤ t from hu.2⟩, rfl⟩
      have hsub : Icc (0 : ℝ) (t : ℝ) ⊆ Ici 0 := fun u hu => hu.1
      have hfill := isFilling_fillH (isCompact_Icc.image_of_continuousOn (hextLT.2.1.mono hsub))
      rw [← hh] at hfill
      have e1 := congrArg (fun f : ℝ → ℝ => fwdHull f (t : ℝ)) hdrv
      show IsFilling (fwdHull (fun r : ℝ => frzDrive s y r.toNNReal) (t : ℝ)) (η' '' Icc 0 t)
      rw [e1, himg]
      exact hfill
  have htend : Tendsto (fun t : ℝ≥0 => ‖η' t‖) atTop atTop :=
    hextP.tendsto.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have htr : (frzDrive s y, (⊤ : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet :=
    (Sec7.RandRestart.mem_traceSet_iff hfrzc.continuousOn hfrz0 (fun _ h => absurd h (lt_irrefl _))).2
      ⟨η', hgen, fun _ => htend⟩
  have hline : EqOn (frzLine s y) ext (Ici 0) := fun u hu => by
    rw [frzLine, LP.traceAt_eq_of_isGeneratingTrace hgen hfrzc.continuousOn hfrz0 ENNReal.coe_lt_top]
    simp [hη', Real.coe_toNNReal _ hu]
  have hlineP : IsProperArc (frzLine s y) := hextP.congr hline
  -- positions
  have hpos : frzVL s y = VL 0 T ω - W T ω ∧ frzVR s y = VR 0 T ω - W T ω := by
    have hstop : Sec4.histStop (revStop s y) = T := histStop_revStop s y
    have hWT : regPath (revStop s y) T = W T ω := by
      have := congrFun hfrz T
      rw [frzDrive, min_self] at this
      exact this
    have hVL : Sec4.histVL (revStop s y) 0 = VL 0 T ω := Sec4.histVL_stopHistory hgs.1 hgs.2.2.1 0
    have hVR : Sec4.histVR (revStop s y) 0 = VR 0 T ω := Sec4.histVR_stopHistory hgs.1 hgs.2.2.2 0
    refine ⟨?_, ?_⟩
    · simp only [frzVL, posLProc, add_sub_cancel_left, hstop, hWT, hVL]
      exact min_eq_right (sub_nonpos.2 hVLle)
    · simp only [frzVR, posRProc, add_sub_cancel_left, hstop, hWT, hVR]
      exact max_eq_right (sub_nonneg.2 hWVR)
  have hTζ : ((T : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hvL := vL_eq_neg_rightImg hp hWc hTζ 0
  have hvR := vR_eq_rightImg hp hWc hTζ 0
  have hrT : Ito.rpath (W · ω) (T : ℝ) = W T ω := by simp [Ito.rpath]
  have hneg := chartAL_neg hLT hP hrw hrw0 hTpos
  have hposR := chartAR_pos hLT hP hrw hrw0 hTpos
  refine ⟨⟨⟨⟨⟨⟨htr, hfrz0⟩, hlineP.imPosCond⟩, hlineP.sepCond⟩, fun q hq0 hqs => ?_⟩, ?_⟩, ?_⟩
  · rw [histLine_killedHistory hζ hWc, hline (mem_Ici.2 (by exact_mod_cast hq0)), hext,
      YuanCorollary13.extTrace_eq (by rw [hT]; exact_mod_cast hqs)]
  · show frzVL s y < 0
    rw [hpos.1, hvL]
    simp only [LP.twoSeedXL, neg_zero]
    rw [chartAL, hrT] at hneg
    linarith
  · show 0 < frzVR s y
    rw [hpos.2, hvR]
    simp only [LP.twoSeedXR]
    rw [chartAR, hrT] at hposR
    linarith

end AeGood

/-! ### The union mean before contact, identified -/

section Assembly

open LQGMetric (DistOn TestOn)
open LocalSets (IsLocalSetMean germSigma)
open SupercriticalConformalCovariance (IsConformalBijection)

universe u

variable {rL rR : ℝ}
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- B13's reflected reverse mean is the explicit `revSlitMean` of the frozen driver (with `u₀` split off). -/
theorem revMean_eq_revSlitMean (u₀ : ℂ → ℝ) {s : ℚ} (hs : 0 < s) (y : HistorySpace 1 1) (z : ℂ) :
    revMean rL rR u₀ s y z =
      -revSlitMean rL rR (Ito.rpath (frzDrive s y)) s (frzVL s y) (frzVR s y) z - u₀ z := by
  have hT : ((revStopT s : ℝ≥0) : ℝ) = s := by
    rw [revStopT, Real.coe_toNNReal _ (by exact_mod_cast hs.le)]
  have e1 : (fun i : Fin 1 => posLProc i (revStopT s) (revStop s y) - regPath (revStop s y) (revStopT s)) =
      fun _ => posLProc 0 (revStopT s) (revStop s y) - regPath (revStop s y) (revStopT s) := by
    funext i; rw [Subsingleton.elim i 0]
  have e2 : (fun i : Fin 1 => posRProc i (revStopT s) (revStop s y) - regPath (revStop s y) (revStopT s)) =
      fun _ => posRProc 0 (revStopT s) (revStop s y) - regPath (revStop s y) (revStopT s) := by
    funext i; rw [Subsingleton.elim i 0]
  simp only [revMean, histMean, meanAt, revSlitMean, frzVL, frzVR, frzDrive, hT, e1, e2]

/-- **Step (S3) of the contact step, completed before contact.** On the glued space, almost surely on
`{A ∩ G = ∅}` (`A = α((0, t])`, `G = R(β((0, s]))`), the union mean of the two stopped slits has a harmonic
representative `w` on `C = ℍ \ (A ∪ G)` and the image chain `W'` of `Ψ(A)` (`Ψ = revChart` of the reverse frozen
driver) exists, with `w + u₀ = chartMean ∘ f'_T ∘ Ψ` on `C`: the uncentred union mean is, in `Ψ`-coordinates, the
explicit `SLE₄(r_L, −r_L; r_R, −r_R)` mean of the image slit with forces at the images of `0∓` and of `Ψ(∞∓)`. -/
theorem ae_union_mean_eq_chartMean_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) {g : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k h hC.2.1) g) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1),
      Disjoint (histHull t (killedHistory W VL VR ζ p.1)) (negInv '' histHull s p.2) →
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w
          (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) →
            g p φ = ∫ z, w z * φ z) ∧
        ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T : ℝ, 0 < T ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧
          IsProperArc η' ∧
          fwdHull W' T = revChart (Ito.rpath (frzDrive s p.2)) s '' histHull t (killedHistory W VL VR ζ p.1) ∧
          ∀ z ∈ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2),
            w z + u₀ z = chartMean rL rR W' T (frzVL s p.2) (frzVR s p.2)
              (fwdMap W' T (revChart (Ito.rpath (frzDrive s p.2)) s z)) := by
  obtain ⟨hX, -⟩ := hC.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hh := hC.2.1
  -- Corollary 4.8 through a half-plane chart, on the glued space
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 1 1 =>
      WholeField.centredField h u₀ p.1) (glueMeasure P k h hh) :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => WholeField.centredField h u₀ ω) (f := Prod.fst)
      measurable_fst (glueMeasure_fst (μ := P) k hh) (WholeField.isZeroBoundaryGFF_centredField hC hu₀)
  have hloc := isLocalSet_twoSlit_glue hL hR hC hC₂ hlaw k hk hu₀ ht hs
  have hAm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 => histHull t (killedHistory W VL VR ζ p.1) :=
    (measurable_histHull t).comp ((measurable_killedHistory hX).comp measurable_fst)
  have hGm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 => negInv '' histHull s p.2 :=
    (measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd
  have hcor := ae_eqOn_of_condMean_halfPlaneChart hF
    (fun φ => Sec6.IsLocalSetMean.ae_eq_condExp_germSigma hF (LocalSets.measurable_union_hitting hAm hGm) hloc hg φ)
    (hloc.2.1.mono fun _ hp => hp.2)
  -- forward facts
  have hfwd : ∀ᵐ p ∂(glueMeasure P k h hh), Continuous (fun r => W r p.1) ∧ W 0 p.1 = 0 ∧
      IsLoewnerTrace (Ito.rpath (W · p.1)) (seedLine ζ W p.1) ∧ IsProperArc (seedLine ζ W p.1) ∧
      histHull t (killedHistory W VL VR ζ p.1) = fwdHull (Ito.rpath (W · p.1)) t ∧
      ∀ z, meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1) (fun i => (VL i · p.1))
        (fun i => (VR i · p.1)) (Real.toNNReal t) z = fwdSlitMean rL rR (Ito.rpath (W · p.1)) t z := by
    refine ae_glue_fst (μ := P) k hh (Q := fun ω => Continuous (fun r => W r ω) ∧ W 0 ω = 0 ∧
      IsLoewnerTrace (Ito.rpath (W · ω)) (seedLine ζ W ω) ∧ IsProperArc (seedLine ζ W ω) ∧
      histHull t (killedHistory W VL VR ζ ω) = fwdHull (Ito.rpath (W · ω)) t ∧
      ∀ z, meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · ω) (fun i => (VL i · ω))
        (fun i => (VR i · ω)) (Real.toNNReal t) z = fwdSlitMean rL rR (Ito.rpath (W · ω)) t z) ?_
    filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1,
      ae_histHull_eq_fwdHull hL hR hC.1 ht, hC.1.2.2.2.2] with ω hω hH hp
    obtain ⟨hζ, -, hLT, hP, -⟩ := hω
    have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht.le
    have hTt : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht'
    have hWc : Continuous fun r => W r ω := by
      have h1 := hp.2.2.2.1
      rw [hζ] at h1
      exact continuousOn_univ.1 (h1.mono fun r _ => ENNReal.coe_lt_top)
    have hTζ : ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
    refine ⟨hWc, hp.1, hLT, hP, ?_, fun z => ?_⟩
    · rw [hH, hTt]; rfl
    · have hvL := vL_eq_neg_rightImg hp hWc hTζ 0
      have hvR := vR_eq_rightImg hp hWc hTζ 0
      have hrT : Ito.rpath (W · ω) t = W (Real.toNNReal t) ω := rfl
      simp only [meanAt, fwdSlitMean, chartAL, chartAR, hTt]
      congr 1
      · funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [hvL, hrT]
        simp [LP.twoSeedXL, hTt]
      · funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [hvR, hrT]
        simp [LP.twoSeedXR, hTt]
  -- reverse facts
  have hrev : ∀ᵐ p ∂(glueMeasure P k h hh), p.2 ∈ BetaSet s :=
    ae_glue_snd (X₂ := fun ω => reflectField (h₂ ω)) (D₂ := killedHistory W₂ VL₂ VR₂ ζ₂) hh
      (measurable_reflectField.comp hC₂.2.1) (measurable_killedHistory hX₂) hlaw k hk
      (measurableSet_betaSet s) (ae_killedHistory_mem_betaSet hR hL hC₂.1 hs)
  filter_upwards [ae_union_mean_glue_of_disjoint hL hR hC hC₂ hlaw k hk hu₀ ht hs hg, hcor, hfwd, hrev,
    ae_goodHist_snd_glue hL hR hC hC₂ hlaw k hk s] with p hp hcorp hfp hrp hgp hdisj
  obtain ⟨w, hw, hrep, hlimA, hlimG⟩ := hp hdisj
  obtain ⟨hWc, hW0, hLT, hP, hAeq, hmeanA⟩ := hfp
  obtain ⟨hWβ, hWβ0, hβ, hβp, hGeq, hvL, hvR⟩ := trace_of_mem_betaSet hs hrp
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  set A := histHull t (killedHistory W VL VR ζ p.1) with hAdef
  set G := negInv '' histHull s p.2 with hGdef
  set Wα := Ito.rpath (W · p.1) with hWαdef
  set Wβ := Ito.rpath (frzDrive s p.2) with hWβdef
  have hGclosed : IsClosed (negInv '' fwdHull Wβ s) := by
    rw [← hGeq]; exact isClosed_image_negInv_histHull hs hgp
  have hdisj' : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s) := by rw [← hAeq, ← hGeq]; exact hdisj
  have hWαc : Continuous Wα := continuous_rpath hWc
  have hWα0 : Wα 0 = 0 := by simp [hWαdef, Ito.rpath, hW0]
  obtain ⟨W', hW', hW'0, T, hT, η', hη', hη'p, hK', htip⟩ :=
    exists_imageTrace hLT hP hWβ hWβ0 hs'.le hGclosed ht' hdisj'
  have hCeq : H \ (A ∪ G) = H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) := by rw [hAeq, hGdef, hGeq]
  -- the two boundary limits for `M = w + u₀`
  have hA' : ∀ z₀ ∈ fwdHull Wα t ∪ {z : ℂ | z.im = 0},
      Tendsto (fun z => (w z + u₀ z) - fwdSlitMean rL rR Wα t z)
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0) := by
    intro z₀ hz₀
    rw [← hCeq]
    have := hlimA z₀ (by rw [hAeq]; exact hz₀)
    refine this.congr fun z => ?_
    rw [hmeanA z]; ring
  have hG' : ∀ z₀ ∈ negInv '' fwdHull Wβ s ∪ ({z : ℂ | z.im = 0} \ {0}),
      Tendsto (fun z => (w z + u₀ z) + revSlitMean rL rR Wβ s (frzVL s p.2) (frzVR s p.2) z)
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0) := by
    intro z₀ hz₀
    rw [← hCeq]
    have := hlimG z₀ (by rw [hGdef, hGeq]; exact hz₀)
    refine this.congr fun z => ?_
    rw [revMean_eq_revSlitMean u₀ hs]; ring
  obtain ⟨E, hEfin, hE⟩ := exists_finite_tendsto_twoSlitChart hLT hP hWαc hWα0 ht' hWβ hWβ0 hβ hβp hs' hGclosed
    hdisj' hW' hW'0 hη' hη'p hT hK' htip hvL hvR hA' hG'
  -- the chart of `C`
  have hΦ : IsConformalBijection (twoSlitChart Wβ s W' T) H (H \ (A ∪ G)) := by
    have h1 := isConformalBijection_comp_fwdMapInv (isConformalBijection_revChartInv hWβ hWβ0 hs'.le) hW' hW'0
      hT.le
    have hset : (H \ negInv '' fwdHull Wβ s) \ revChartInv Wβ s '' fwdHull W' T = H \ (A ∪ G) := by
      rw [hCeq, hK', image_image]
      have himg : (fun a => revChartInv Wβ s (revChart Wβ s a)) '' fwdHull Wα t = fwdHull Wα t := by
        refine (image_congr fun a ha => revChartInv_revChart hWβ hWβ0 hs'.le
          ⟨ha.1, fun h' => disjoint_left.1 hdisj' ha h'⟩).trans (image_id' _)
      rw [himg]
      ext z; simp only [Set.mem_sdiff, mem_union, not_or]; tauto
    rw [hset] at h1
    exact h1
  -- the candidate
  set v : ℂ → ℝ := fun z => chartMean rL rR W' T (frzVL s p.2) (frzVR s p.2)
    (fwdMap W' T (revChart Wβ s z)) - u₀ z with hvdef
  have hCH : ∀ z ∈ H \ (A ∪ G), z ∈ H \ negInv '' fwdHull Wβ s := fun z hz =>
    ⟨hz.1, fun h' => hz.2 (Or.inr (by rw [hGdef, hGeq]; exact h'))⟩
  have hCA : ∀ z ∈ H \ (A ∪ G), revChart Wβ s z ∈ H \ fwdHull W' T := fun z hz => by
    refine ⟨revChart_mem_H hWβ hs'.le (hCH z hz), fun hK => ?_⟩
    rw [hK'] at hK
    obtain ⟨a, ha, e⟩ := hK
    have := injOn_revChart hWβ hWβ0 hs'.le ⟨ha.1, fun h' => disjoint_left.1 hdisj' ha h'⟩ (hCH z hz) e
    exact hz.2 (Or.inl (by rw [hAeq, ← this]; exact ha))
  have hvL' : ∀ i, (![chartAL W' T, chartBL W' T (frzVR s p.2)] : Fin 2 → ℝ) i ≤ 0 := by
    intro i; fin_cases i
    · exact chartAL_nonpos hW' hT.le
    · exact (chartBL_lt hη' hη'p hW' hW'0 hT.le hvR).le.trans (chartAL_nonpos hW' hT.le)
  have hvR' : ∀ i, 0 ≤ (![chartAR W' T, chartBR W' T (frzVL s p.2)] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · exact chartAR_nonneg hW' hT.le
    · exact (chartAR_nonneg hW' hT.le).trans (chartAR_lt hη' hη'p hW' hW'0 hT.le hvL).le
  have hcm := isBoundedHarmonicExtension_condMean ![rL, -rL] ![rR, -rR] hvL' hvR'
  have hCopen : IsOpen (H \ (A ∪ G)) := by
    rw [hCeq]
    have h1 := (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWαc ht'.le).inter
      (isOpen_H_diff_negInv_fwdHull hWβ hs'.le)
    convert h1 using 1
    ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]; tauto
  have hv : InnerProductSpace.HarmonicOnNhd v (H \ (A ∪ G)) := by
    intro z hz
    have hz' := hCH z hz
    have hRd : DifferentiableAt ℂ (revChart Wβ s) z := by
      have hz0 : z ≠ 0 := fun h0 => by
        have := hz.1; rw [h0] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
      have hw := negInv_notMem_fwdHull hz'
      have h1 : DifferentiableAt ℂ negInv z := by
        unfold negInv; exact (differentiableAt_inv hz0).neg
      have h2 : DifferentiableAt ℂ (fwdMap Wβ s) (negInv z) :=
        (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWβ hs'.le).differentiableAt
          ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWβ hs'.le).mem_nhds hw)
      have h3 : fwdMap Wβ s (negInv z) ≠ 0 := fun h0 => by
        have := QuantumZipper.FwdHolo.mapsTo_fwdMap hWβ hs'.le hw
        rw [h0] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
      have h4 : DifferentiableAt ℂ negInv (fwdMap Wβ s (negInv z)) := by
        unfold negInv; exact (differentiableAt_inv h3).neg
      exact h4.comp z (h2.comp z h1)
    have hGd : DifferentiableOn ℂ (fun z => fwdMap W' T (revChart Wβ s z)) (H \ (A ∪ G)) := by
      intro z₁ hz₁
      have hRd₁ : DifferentiableAt ℂ (revChart Wβ s) z₁ := by
        have hz0 : z₁ ≠ 0 := fun h0 => by
          have := hz₁.1; rw [h0] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
        have hw := negInv_notMem_fwdHull (hCH z₁ hz₁)
        have h1 : DifferentiableAt ℂ negInv z₁ := by
          unfold negInv; exact (differentiableAt_inv hz0).neg
        have h2 : DifferentiableAt ℂ (fwdMap Wβ s) (negInv z₁) :=
          (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWβ hs'.le).differentiableAt
            ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWβ hs'.le).mem_nhds hw)
        have h3 : fwdMap Wβ s (negInv z₁) ≠ 0 := fun h0 => by
          have := QuantumZipper.FwdHolo.mapsTo_fwdMap hWβ hs'.le hw
          rw [h0] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
        have h4 : DifferentiableAt ℂ negInv (fwdMap Wβ s (negInv z₁)) := by
          unfold negInv; exact (differentiableAt_inv h3).neg
        exact h4.comp z₁ (h2.comp z₁ h1)
      have hfd : DifferentiableAt ℂ (fwdMap W' T) (revChart Wβ s z₁) :=
        (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW' hT.le).differentiableAt
          ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW' hT.le).mem_nhds (hCA z₁ hz₁))
      exact (hfd.comp z₁ hRd₁).differentiableWithinAt
    have han : AnalyticAt ℂ (fun z => fwdMap W' T (revChart Wβ s z)) z :=
      hGd.analyticAt (hCopen.mem_nhds hz)
    have hcz := hcm.1 _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT.le (hCA z hz))
    have h1 := QuantumZipper.FieldLawler.fl_harmonicAt_comp (h := chartMean rL rR W' T (frzVL s p.2) (frzVR s p.2))
      han hcz
    exact h1.sub (hu₀.1 z hz.1)
  have hvb : ∃ M, ∀ z ∈ H \ (A ∪ G), |v z| ≤ M := by
    obtain ⟨C₁, hC₁⟩ := hcm.2.1
    obtain ⟨C₂, hC₂'⟩ := hu₀.2.1
    refine ⟨C₁ + C₂, fun z hz => ?_⟩
    have h1 := hC₁ _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT.le (hCA z hz))
    have h2 := hC₂' z hz.1
    simp only [hvdef]
    calc |chartMean rL rR W' T (frzVL s p.2) (frzVR s p.2) (fwdMap W' T (revChart Wβ s z)) - u₀ z|
        ≤ |chartMean rL rR W' T (frzVL s p.2) (frzVR s p.2) (fwdMap W' T (revChart Wβ s z))| + |u₀ z| :=
          abs_sub _ _
      _ ≤ C₁ + C₂ := add_le_add h1 h2
  have hlim : ∀ x : ℝ, x ∉ E → Tendsto (fun y => w (twoSlitChart Wβ s W' T y) - v (twoSlitChart Wβ s W' T y))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x hx
    refine (hE x hx).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hF' := QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT.le hy
    simp only [hvdef, twoSlitChart, revChart_revChartInv hWβ hWβ0 hs'.le hF',
      QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT.le hy]
    ring
  have hEq := hcorp w hw hrep (H \ (A ∪ G)) hCopen subset_rfl _ hΦ v hv hvb E hEfin hlim
  refine ⟨w, hw, hrep, W', hW', hW'0, T, hT, η', hη', hη'p, by rw [hK', hAeq], fun z hz => ?_⟩
  have := hEq hz
  simp only [hvdef] at this
  linarith

end Assembly

end InteractingSLE.WangWu
