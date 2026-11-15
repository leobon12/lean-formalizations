/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGen
import InteractingSLE.WangWu.ReverseContactImgLim

/-!
# Localization for contact words

Packet PROVE-CROSSCOND-GEN. The localization and finite-lifetime martingale-limit arguments of
`WangWu.ReverseContactImgLim` use no strict force-gap separation. These are their adapters to
`IsContactWord`; the existing `sysV`, `locN` and `stopM` definitions and all generic martingale
results are reused. Localizations bound time and coordinates, allowing individual gaps to vanish.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open WangWu.ImgDrv MartChar Sec7.PhaseSelAdapt Sec7.PhaseSelFull

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → ℝ≥0}

section Path

variable (hK : IsContactWord W VL VR T) (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
include hK hσT

theorem IsContactWord.continuous_sysV (n : ℕ) (j : Fin nL ⊕ Fin nR) (ω : Ω) :
    Continuous fun t => sysV W VL VR (σ n) j t ω := by
  cases j with
  | inl i => exact hK.continuous_sysVL (hσT n) i ω
  | inr i => exact hK.continuous_sysVR (hσT n) i ω

theorem IsContactWord.sysV_of_le {n : ℕ} {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ n ω) (j : Fin nL ⊕ Fin nR) :
    sysV W VL VR (σ n) j t ω = jointV VL VR j t ω := by
  cases j with
  | inl i => exact hK.sysVL_of_le (hσT n) ht i
  | inr i => exact hK.sysVR_of_le (hσT n) ht i

theorem IsContactWord.absSum_sys_eq {n : ℕ} {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ n ω) :
    absSum (sysW W (σ n)) (sysV W VL VR (σ n)) t ω = absSum W (jointV VL VR) t ω := by
  simp only [absSum, sysW_of_le ht, hK.sysV_of_le hσT ht]

theorem IsContactWord.martProc_sys_eq (ρ : Fin nL ⊕ Fin nR → ℝ) {n : ℕ} {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ n ω) :
    martProc ρ (sysW W (σ n)) (sysV W VL VR (σ n)) t ω = martProc ρ W (jointV VL VR) t ω := by
  simp only [martProc, sysW_of_le ht, sysW_of_le (zero_le : (0 : ℝ≥0) ≤ σ n ω), hK.sysV_of_le hσT ht,
    hK.sysV_of_le hσT (zero_le : (0 : ℝ≥0) ≤ σ n ω)]

/-- The stopped martingale part is the killed martingale part up to `locN n`. -/
theorem IsContactWord.stopM_eq (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : ℕ} {ω : Ω} {t : ℝ≥0}
    (ht : t ≤ locN W VL VR σ n ω) :
    stopM ρL ρR W VL VR σ n t ω = martProc (jointρ ρL ρR) W (jointV VL VR) t ω := by
  simp only [stopM, min_eq_left ht]
  exact hK.martProc_sys_eq hσT _ (ht.trans (locN_le_σ n ω))

/-- The exit times of the continued systems: the exit of the `m`-th system from level `n` comes no earlier than the
exit of the `n`-th one, up to `σ n`. -/
theorem IsContactWord.min_exitTime_le {n m : ℕ} (ω : Ω) (hσm : σ n ω ≤ σ m ω) :
    min (MathFin.exitTime (absSum (sysW W (σ n)) (sysV W VL VR (σ n))) n ω) (σ n ω : WithTop ℝ≥0) ≤
      MathFin.exitTime (absSum (sysW W (σ m)) (sysV W VL VR (σ m))) n ω := by
  have hcn := continuous_absSum (fun ω => hK.continuous_sysW (hσT n) ω) (hK.continuous_sysV hσT n)
  have hcm := continuous_absSum (fun ω => hK.continuous_sysW (hσT m) ω) (hK.continuous_sysV hσT m)
  rcases eq_or_ne (MathFin.exitTime (absSum (sysW W (σ m)) (sysV W VL VR (σ m))) n ω) ⊤ with h | h
  · rw [h]; exact le_top
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1 h
  rw [← he]
  rcases le_total (σ n ω) e with hσe | heσ
  · exact (min_le_right _ _).trans (WithTop.coe_le_coe.2 hσe)
  · obtain ⟨s, hs, hsn⟩ := (MathFin.exitTime_le_iff hcm n e ω).1 he.ge
    have hsσ : s ≤ σ n ω := hs.2.trans heσ
    have e1 : absSum (sysW W (σ m)) (sysV W VL VR (σ m)) s ω = absSum (sysW W (σ n)) (sysV W VL VR (σ n)) s ω := by
      rw [hK.absSum_sys_eq hσT (hsσ.trans hσm), hK.absSum_sys_eq hσT hsσ]
    rw [e1] at hsn
    exact (min_le_left _ _).trans ((MathFin.exitTime_le_iff hcn n e ω).2 ⟨s, hs, hsn⟩)

/-- **The localizing times increase.** -/
theorem IsContactWord.locN_mono (hσm : ∀ ω, Monotone (σ · ω)) (ω : Ω) : Monotone (locN W VL VR σ · ω) := by
  intro n m hnm
  refine WithTop.coe_le_coe.1 ?_
  rw [coe_locN, coe_locN]
  have h0 : ∀ k, absSum (sysW W (σ k)) (sysV W VL VR (σ k)) 0 ω = absSum W (jointV VL VR) 0 ω :=
    fun k => hK.absSum_sys_eq hσT zero_le
  by_cases hω : ω ∈ initEvent (sysW W (σ n)) (sysV W VL VR (σ n)) n
  · have hω' : ω ∈ initEvent (sysW W (σ m)) (sysV W VL VR (σ m)) m := by
      have h1 : absSum (sysW W (σ n)) (sysV W VL VR (σ n)) 0 ω < n := hω
      show absSum (sysW W (σ m)) (sysV W VL VR (σ m)) 0 ω < m
      rw [h0] at h1 ⊢
      exact h1.trans_le (by exact_mod_cast hnm)
    rw [lifeLoc_of_mem hω, lifeLoc_of_mem hω']
    simp only [locTime]
    have hcm := continuous_absSum (fun ω => hK.continuous_sysW (hσT m) ω) (hK.continuous_sysV hσT m)
    have hσnm : σ n ω ≤ σ m ω := hσm ω hnm
    have hex := hK.min_exitTime_le hσT ω hσnm (n := n) (m := m)
    have hex' := MathFin.exitTime_mono hcm hnm ω
    refine le_min (le_min ?_ ?_) ?_
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (WithTop.coe_le_coe.2 (by exact_mod_cast hnm)))
    · calc min (min ((n : ℝ≥0) : WithTop ℝ≥0) _) (σ n ω : WithTop ℝ≥0)
            ≤ min (MathFin.exitTime (absSum (sysW W (σ n)) (sysV W VL VR (σ n))) n ω) (σ n ω : WithTop ℝ≥0) :=
            min_le_min (min_le_right _ _) le_rfl
        _ ≤ _ := hex.trans hex'
    · exact (min_le_right _ _).trans (WithTop.coe_le_coe.2 hσnm)
  · rw [lifeLoc_of_notMem hω, ← coe_locN]
    exact WithTop.coe_le_coe.2 (zero_le : (0 : ℝ≥0) ≤ locN W VL VR σ m ω)

/-- **The localizing times exhaust `[0, T)`** along a path on which the `σ n` do. -/
theorem IsContactWord.exists_le_locN (hσm : ∀ ω, Monotone (σ · ω)) {ω : Ω}
    (hlim : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ σ n ω) {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) < T ω) :
    ∃ n, u ≤ locN W VL VR σ n ω := by
  obtain ⟨n₀, hn₀⟩ := hlim u hu
  -- a bound of the killed coordinates on `[0, u]`
  have hcont : ContinuousOn (fun t => absSum W (jointV VL VR) t ω) (Icc 0 u) := by
    have hsub : Icc (0 : ℝ≥0) u ⊆ Iic (σ n₀ ω) := fun t ht => ht.2.trans hn₀
    refine (ContinuousOn.congr (f := fun t => absSum (sysW W (σ n₀)) (sysV W VL VR (σ n₀)) t ω)
      ((continuous_absSum (fun ω => hK.continuous_sysW (hσT n₀) ω) (hK.continuous_sysV hσT n₀) ω).continuousOn)
      fun t ht => ?_)
    exact (hK.absSum_sys_eq hσT (hsub ht)).symm
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (max C (u : ℝ))
  set n := max n₀ N with hn
  refine ⟨n, ?_⟩
  have hσn : u ≤ σ n ω := hn₀.trans (hσm ω (le_max_left _ _))
  have hCn : C < n := lt_of_lt_of_le ((le_max_left _ _).trans_lt hN) (by exact_mod_cast le_max_right n₀ N)
  have hun : (u : ℝ) < n := lt_of_lt_of_le ((le_max_right _ _).trans_lt hN) (by exact_mod_cast le_max_right n₀ N)
  have hbd : ∀ t ∈ Icc (0 : ℝ≥0) u, absSum W (jointV VL VR) t ω ≤ C := fun t ht => hC ⟨t, ht, rfl⟩
  have hmem : ω ∈ initEvent (sysW W (σ n)) (sysV W VL VR (σ n)) n := by
    show absSum (sysW W (σ n)) (sysV W VL VR (σ n)) 0 ω < n
    rw [hK.absSum_sys_eq hσT zero_le]
    exact (hbd 0 ⟨le_rfl, zero_le⟩).trans_lt hCn
  refine WithTop.coe_le_coe.1 ?_
  rw [coe_locN, lifeLoc_of_mem hmem]
  simp only [locTime]
  have hc := continuous_absSum (fun ω => hK.continuous_sysW (hσT n) ω) (hK.continuous_sysV hσT n)
  refine le_min (le_min (WithTop.coe_le_coe.2 (by exact_mod_cast hun.le)) ?_) (WithTop.coe_le_coe.2 hσn)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨s, hs, hsn⟩ := (MathFin.exitTime_le_iff hc n u ω).1 hlt.le
  rw [hK.absSum_sys_eq hσT (hs.2.trans hσn)] at hsn
  have h1 := hbd s hs
  have h2 : 0 ≤ absSum W (jointV VL VR) s ω := by
    simp only [absSum]; positivity
  rw [abs_of_nonneg h2] at hsn
  linarith

end Path

/-! ### The stopped martingale parts -/

section Mart

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
  (hK : IsContactWord W VL VR T) (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
  (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) (hWa : StronglyAdapted 𝓖 W)
  (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓖 (VR j))
  {κ : ℝ} (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
    (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
    (coupProc κ ρL ρR W VL VR z))
include hK hσT hσ hWa hVLa hVRa hκ hmart

omit [IsProbabilityMeasure P] hκ hmart in
theorem IsContactWord.isStoppingTime_locN (n : ℕ) :
    IsStoppingTime 𝓖 fun ω => (locN W VL VR σ n ω : WithTop ℝ≥0) := by
  have h := isStoppingTime_lifeLoc (fun ω => hK.continuous_sysW (hσT n) ω) (hK.continuous_sysV hσT n)
    (hK.stronglyAdapted_sysW (hσT n) (hσ n) hWa)
    (fun j => by
      cases j with
      | inl i => exact hK.stronglyAdapted_sysVL (hσT n) (hσ n) hWa hVLa i
      | inr i => exact hK.stronglyAdapted_sysVR (hσT n) (hσ n) hWa hVRa i) (hσ n) n
  convert h using 2 with ω
  exact coe_locN n ω

/-- **The martingale part of the `n`-th continued system**, stopped at `lifeLoc n` (the landed
`martingale_martProc_lifeLoc`). -/
theorem IsContactWord.martingale_lifeLoc_sys (n : ℕ) :
    Martingale (stoppedProcess (martProc (jointρ ρL ρR) (sysW W (σ n)) (sysV W VL VR (σ n)))
        (lifeLoc (sysW W (σ n)) (sysV W VL VR (σ n)) (fun ω => (σ n ω : WithTop ℝ≥0)) n)) 𝓖 P ∧
      Martingale (stoppedProcess (fun t ω => martProc (jointρ ρL ρR) (sysW W (σ n)) (sysV W VL VR (σ n)) t ω ^ 2 -
        κ * t) (lifeLoc (sysW W (σ n)) (sysV W VL VR (σ n)) (fun ω => (σ n ω : WithTop ℝ≥0)) n)) 𝓖 P :=
  martingale_martProc_lifeLoc hκ (sysW_zero hK.w_zero) (fun ω => hK.continuous_sysW (hσT n) ω)
    (hK.stronglyAdapted_sysW (hσT n) (hσ n) hWa) (fun i => hK.stronglyAdapted_sysVL (hσT n) (hσ n) hWa hVLa i)
    (fun j => hK.stronglyAdapted_sysVR (hσT n) (hσ n) hWa hVRa j) (fun _ t _ => contV_left_le_contW t)
    (fun _ t _ => contW_le_contV_right t) (fun ω i => hK.isForcePath_sysVL (hσT n) ω i)
    (fun ω j => hK.isForcePath_sysVR (hσT n) ω j) (hσ n)
    (hK.isLocalMartingaleBefore_sys (hσT n) (hσ n) hmart) n

theorem IsContactWord.martingale_stopM (n : ℕ) : Martingale (stopM ρL ρR W VL VR σ n) 𝓖 P := by
  have h := (hK.martingale_lifeLoc_sys hσT hσ hWa hVLa hVRa hκ hmart n).1
  convert h using 1
  funext t ω
  rw [stoppedProcess_lifeLoc]
  rfl

theorem IsContactWord.martingale_stopM_sq (n : ℕ) :
    Martingale (fun t ω => stopM ρL ρR W VL VR σ n t ω ^ 2 - κ * ((min t (locN W VL VR σ n ω) : ℝ≥0) : ℝ))
      𝓖 P := by
  have h := (hK.martingale_lifeLoc_sys hσT hσ hWa hVLa hVRa hκ hmart n).2
  convert h using 1
  funext t ω
  rw [stoppedProcess_lifeLoc]
  rfl

omit hσ hWa hVLa hVRa hκ hmart in
theorem IsContactWord.continuous_stopM (n : ℕ) (ω : Ω) : Continuous fun t => stopM ρL ρR W VL VR σ n t ω :=
  (continuous_martProc (fun ω => hK.continuous_sysW (hσT n) ω) (hK.continuous_sysV hσT n) ω).comp
    (continuous_id.min continuous_const)

omit hσ hWa hVLa hVRa hκ hmart in
theorem IsContactWord.abs_stopM_le (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |stopM ρL ρR W VL VR σ n t ω| ≤ 2 * n + (∑ j, |jointρ ρL ρR j|) * n :=
  abs_martProc_lifeLocN_le (fun ω => hK.continuous_sysW (hσT n) ω) (hK.continuous_sysV hσT n) n t ω

/-- `E M(U ∧ locN n)² = κ E(U ∧ locN n) ≤ κ U`. -/
theorem IsContactWord.integral_stopM_sq_le (n : ℕ) (U : ℝ≥0) :
    ∫ ω, stopM ρL ρR W VL VR σ n U ω ^ 2 ∂P ≤ κ * U := by
  have hM := hK.martingale_stopM_sq hσT hσ hWa hVLa hVRa hκ hmart n
  have hM1 := hK.martingale_stopM hσT hσ hWa hVLa hVRa hκ hmart n
  set Y : Ω → ℝ := fun ω => stopM ρL ρR W VL VR σ n U ω with hY
  set S : Ω → ℝ := fun ω => ((min U (locN W VL VR σ n ω) : ℝ≥0) : ℝ) with hS
  have h0 := hM.setIntegral_eq (zero_le (a := U)) (@MeasurableSet.univ _ (𝓖 0))
  simp only [Measure.restrict_univ, zero_min, stopM_zero, NNReal.coe_zero, mul_zero, sub_zero] at h0
  set C : ℝ := 2 * n + (∑ j, |jointρ ρL ρR j|) * n
  have hYm : StronglyMeasurable Y := (hM1.1 U).mono (𝓖.le U)
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := by
    refine Integrable.of_bound (hYm.aestronglyMeasurable.pow 2) (C ^ 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hK.abs_stopM_le hσT n U ω) 2
  have hdiff : Integrable (fun ω => Y ω ^ 2 - κ * S ω) P := hM.integrable U
  have hSi : Integrable (fun ω => κ * S ω) P := (hY2.sub hdiff).congr (Eventually.of_forall fun ω => by simp)
  have hsplit : ∫ ω, Y ω ^ 2 ∂P = ∫ ω, (Y ω ^ 2 - κ * S ω) ∂P + ∫ ω, κ * S ω ∂P := by
    rw [← integral_add hdiff hSi]; congr 1; funext ω; ring
  have hzero : ∫ ω, (Y ω ^ 2 - κ * S ω) ∂P = 0 := by
    rw [← h0]; simp
  have hSle : ∫ ω, κ * S ω ∂P ≤ κ * U := by
    have : ∫ ω, κ * S ω ∂P ≤ ∫ _ω, κ * (U : ℝ) ∂P :=
      integral_mono hSi (integrable_const _) fun ω => by
        show κ * ((min U (locN W VL VR σ n ω) : ℝ≥0) : ℝ) ≤ κ * (U : ℝ)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left _ _) hκ.le
    simpa using this
  rw [hsplit, hzero, zero_add]
  exact hSle

/-- **The martingale part has a limit at a finite killing time**, almost surely. -/
theorem IsContactWord.ae_tendsto_martProc (hσm : ∀ ω, Monotone (σ · ω))
    (hσlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ σ n ω) :
    ∀ᵐ ω ∂P, ∀ T₀ : ℝ≥0, T ω = T₀ → ∃ L,
      Tendsto (fun t => martProc (jointρ ρL ρR) W (jointV VL VR) t ω) (𝓝[<] T₀) (𝓝 L) := by
  set Y : ℕ → ℝ≥0 → Ω → ℝ := fun n => stopM ρL ρR W VL VR σ n with hYdef
  have hYS : ∀ n t ω, Y n t ω = Y n (min t (locN W VL VR σ n ω)) ω := fun n t ω => by
    show stopM ρL ρR W VL VR σ n t ω = stopM ρL ρR W VL VR σ n (min t (locN W VL VR σ n ω)) ω
    simp only [stopM, min_assoc, min_self]
  have hcons : ∀ n m', n ≤ m' → ∀ t ω, Y n t ω = Y m' (min t (locN W VL VR σ n ω)) ω := by
    intro n m' hnm t ω
    have hle : locN W VL VR σ n ω ≤ locN W VL VR σ m' ω := hK.locN_mono hσT hσm ω hnm
    have h1 : min t (locN W VL VR σ n ω) ≤ locN W VL VR σ m' ω := (min_le_right _ _).trans hle
    show stopM ρL ρR W VL VR σ n t ω = stopM ρL ρR W VL VR σ m' (min t (locN W VL VR σ n ω)) ω
    rw [hK.stopM_eq hσT ρL ρR h1, ← hK.stopM_eq hσT ρL ρR (min_le_right t (locN W VL VR σ n ω))]
    simp only [stopM, min_assoc, min_self]
  have hosc : ∀ U : ℕ, ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ n, ∀ m', n ≤ m' →
      ⨆ i : Iic (U : ℝ≥0), ‖Y m' i ω - Y n i ω‖ < 1 / ((k : ℝ) + 1) := fun U =>
    Zhan.Retarget.ae_osc_small (fun n => hK.martingale_stopM hσT hσ hWa hVLa hVRa hκ hmart n)
      (fun n ω => hK.continuous_stopM hσT n ω) (fun n => ⟨_, fun t ω => hK.abs_stopM_le hσT n t ω⟩)
      (fun n => hK.isStoppingTime_locN hσT hσ hWa hVLa hVRa n) (fun ω => hK.locN_mono hσT hσm ω)
      hYS hcons (U : ℝ≥0) (c := κ * (U : ℝ))
      fun n => hK.integral_stopM_sq_le hσT hσ hWa hVLa hVRa hκ hmart n U
  filter_upwards [ae_all_iff.2 hosc, hσlim] with ω hω hlim T₀ hT₀
  have hρs : ∀ n, locN W VL VR σ n ω < T₀ := fun n => by
    have h := lt_of_le_of_lt (WithTop.coe_le_coe.2 (locN_le_σ (W := W) (VL := VL) (VR := VR) n ω)) (hσT n ω)
    rw [hT₀] at h
    exact WithTop.coe_lt_coe.1 h
  obtain ⟨U, hU⟩ := exists_nat_gt (T₀ : ℝ)
  refine WangWu.exists_tendsto_nhdsLT_of_osc (f := fun t => martProc (jointρ ρL ρR) W (jointV VL VR) t ω) hρs
    fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨n, hn⟩ := hω U k
  refine ⟨n, fun r hr hrT => ?_⟩
  have hrT' : (r : WithTop ℝ≥0) < T ω := by rw [hT₀]; exact WithTop.coe_lt_coe.2 hrT
  obtain ⟨m₀, hm₀⟩ := hK.exists_le_locN hσT hσm hlim hrT'
  set m' := max n m₀
  have hrm' : r ≤ locN W VL VR σ m' ω := hm₀.trans (hK.locN_mono hσT hσm ω (le_max_right _ _))
  have h1 : Y m' r ω = martProc (jointρ ρL ρR) W (jointV VL VR) r ω := hK.stopM_eq hσT ρL ρR hrm'
  have h2 : Y n r ω = martProc (jointρ ρL ρR) W (jointV VL VR) (locN W VL VR σ n ω) ω := by
    show stopM ρL ρR W VL VR σ n r ω = _
    rw [← hK.stopM_eq hσT ρL ρR le_rfl]
    simp only [stopM, min_eq_right hr, min_self]
  have hrU : r ≤ (U : ℝ≥0) := by
    have : (r : ℝ) < U := lt_trans (by exact_mod_cast hrT) hU
    exact_mod_cast this.le
  set C₁ : ℝ := 2 * m' + (∑ j, |jointρ ρL ρR j|) * m'
  set C₂ : ℝ := 2 * n + (∑ j, |jointρ ρL ρR j|) * n
  have hbdd : BddAbove (range fun i : Iic (U : ℝ≥0) => ‖Y m' i ω - Y n i ω‖) :=
    ⟨C₁ + C₂, by
      rintro _ ⟨i, rfl⟩
      show ‖Y m' i ω - Y n i ω‖ ≤ C₁ + C₂
      rw [Real.norm_eq_abs]
      have := abs_sub (Y m' i ω) (Y n i ω)
      linarith [hK.abs_stopM_le hσT m' i ω (ρL := ρL) (ρR := ρR),
        hK.abs_stopM_le hσT n i ω (ρL := ρL) (ρR := ρR)]⟩
  have hle : ‖Y m' r ω - Y n r ω‖ ≤ ⨆ i : Iic (U : ℝ≥0), ‖Y m' i ω - Y n i ω‖ :=
    le_ciSup (f := fun i : Iic (U : ℝ≥0) => ‖Y m' i ω - Y n i ω‖) hbdd ⟨r, hrU⟩
  rw [h1, h2, Real.norm_eq_abs] at hle
  exact (hle.trans (hn m' (le_max_left _ _)).le).trans hk.le

end Mart

end InteractingSLE.Sec5.CrossCond.Gen
