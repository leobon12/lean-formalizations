/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedExistsTime
import InteractingSLE.Spec.Sec2.TwoSeedPath
import MathFin.Probability.Brownian.LevyCharacterization
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal

/-!
# Two seeds: the driving Brownian motion in physical time

Packet PROVE-SEC2-JAC3. With the modified Jacobi path `V = modU U` (every path good), the
physical-time filtration `𝓖 = physFilt` (`𝓖_t = (𝓗 ∨ 𝒩)_{u(t)}`), and the localizing times
`σ_m = t(m)`, the stopped processes `B^{σ_m}_t = N(u(t) ∧ m)/√κ` and
`(B^{σ_m}_t)² - t ∧ σ_m = Q(u(t) ∧ m)/κ` are `𝓖`-martingales (`martingale_of_phys`, from the
optional sampling of `TwoSeedExistsMart`). Lévy's characterization (vendored MathFin) then gives
`isFilteredBrownianReal_bPath`: the landed driving path `bPath κ ρ_L ρ_R V` is a Brownian motion in
`𝓖`, which is the driving Brownian motion of the two-seed evolution (Specification L530–L534).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

open Jacobi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ a b : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓗 : Filtration ℝ mΩ} {U : ℝ → Ω → ℝ}

/-- The physical-time filtration of the two-seed construction. -/
def physFilt (hU : IsJacobiDiffusion κ a b P 𝓗 U) (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) :
    Filtration ℝ≥0 mΩ :=
  physF (augF 𝓗 P) (tauP U) (isStoppingTime_tauP hU hκ ha hb) (tauP_mono hU)

section Filt

variable (hU : IsJacobiDiffusion κ a b P 𝓗 U) (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b)
include hU hκ ha hb

theorem physFilt_pos {t : ℝ≥0} (ht : 0 < t) :
    physFilt hU hκ ha hb t = (isStoppingTime_tauP hU hκ ha hb t ht).measurableSpace := by
  simp [physFilt, physF, ht]

theorem physFilt_zero : physFilt hU hκ ha hb 0 = ⊥ := by
  simp [physFilt, physF]

/-- A continuous adapted process of the logarithmic clock, read at `u(t)`, is `𝓖_t`-measurable. -/
theorem measurable_physFilt {Y : ℝ → Ω → ℝ} (hYa : ∀ u, Measurable[augF 𝓗 P u] (Y u))
    (hYc : ∀ ω, Continuous fun u => Y u ω) {t : ℝ≥0} (ht : 0 < t) :
    Measurable[physFilt hU hκ ha hb t] fun ω => Y (tauP U t ω) ω := by
  have hprog := StronglyAdapted.isStronglyProgressive_of_continuous
    (fun u => (hYa u).stronglyMeasurable) hYc
  have h := measurable_stoppedValue hprog (isStoppingTime_tauP hU hκ ha hb t ht)
  have e : stoppedValue Y (fun ω => ((tauP U t ω : ℝ) : WithTop ℝ)) = fun ω => Y (tauP U t ω) ω := by
    funext ω; simp [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
  rw [physFilt_pos hU hκ ha hb ht, ← e]
  exact h

/-- `phys` of a continuous adapted clock functional is `𝓖`-adapted. -/
theorem measurable_phys_physFilt {F : (ℝ → ℝ) → ℝ → ℝ}
    (hFa : ∀ u, Measurable[augF 𝓗 P u] fun ω => F (modU U · ω) u)
    (hFc : ∀ ω, Continuous fun u => F (modU U · ω) u) (t : ℝ≥0) :
    Measurable[physFilt hU hκ ha hb t] fun ω => phys (modU U · ω) (F (modU U · ω)) t := by
  by_cases ht : 0 < t
  · have e : (fun ω => phys (modU U · ω) (F (modU U · ω)) t) =
        fun ω => F (modU U · ω) (tauP U t ω) := by
      funext ω; rw [phys_of_pos (NNReal.coe_pos.2 ht)]; rfl
    rw [e]
    exact measurable_physFilt hU hκ ha hb (Y := fun u ω => F (modU U · ω) u) hFa hFc ht
  · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) bot_le
    have e : (fun ω => phys (modU U · ω) (F (modU U · ω)) t) = fun _ => 0 := by
      funext ω; rw [phys_of_nonpos (by simp [ht0])]
    rw [e]; exact measurable_const

/-- The physical inverse clock is `augF`-measurable. -/
theorem measurable_tauP {t : ℝ≥0} (ht : 0 < t) : Measurable (tauP U t) :=
  measurable_of_isStopping (𝓗 := augF 𝓗 P) (isStopping_tauP hU hκ ha hb ht)

omit [IsProbabilityMeasure P] hκ ha hb in
/-- `u(t ∧ t(m)) = u(t) ∧ m`. -/
theorem tauP_min {t : ℝ≥0} (ht : 0 < t) (m : ℝ) (ω : Ω) :
    tauP U (min t (clock (modU U · ω) m).toNNReal) ω = min (tauP U t ω) m := by
  have hc := continuous_modU hU ω
  have h01 : ∀ v, modU U v ω ∈ Icc (0 : ℝ) 1 := fun v => modU_mem hU v ω
  have hnull := volume_modU_boundary (U := U) ω
  have htop := tendsto_clock_modU hU ω
  have hcpos : 0 < clock (modU U · ω) m := clock_pos hc h01 hnull m
  have hcm : tauP U (clock (modU U · ω) m).toNNReal ω = m := by
    simp only [tauP, Real.coe_toNNReal _ hcpos.le]
    exact invClock_clock hc h01 hnull htop m
  have hc0 : 0 < (clock (modU U · ω) m).toNNReal := Real.toNNReal_pos.2 hcpos
  rcases le_total t (clock (modU U · ω) m).toNNReal with h | h
  · rw [min_eq_left h, min_eq_left]
    rw [← hcm]; exact tauP_mono hU _ _ ht h ω
  · rw [min_eq_right h, min_eq_right, hcm]
    rw [← hcm]; exact tauP_mono hU _ _ hc0 h ω

/-! ### Localization -/

/-- The localizing times `σ_m = t(m)`. -/
def sigmaLoc (U : ℝ → Ω → ℝ) (m : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  (((clock (modU U · ω) m).toNNReal : ℝ≥0) : WithTop ℝ≥0)

theorem isStoppingTime_sigmaLoc (m : ℕ) : IsStoppingTime (physFilt hU hκ ha hb) (sigmaLoc U m) := by
  intro t
  by_cases ht : 0 < t
  · rw [physFilt_pos hU hκ ha hb ht]
    have e : {ω | sigmaLoc U m ω ≤ t} = {ω | (m : ℝ) ≤ tauP U t ω} := by
      ext ω
      simp only [sigmaLoc, mem_ofPred_eq, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
      rw [← not_lt, ← not_lt, tauP, invClock_lt_iff (continuous_modU hU ω)
        (fun v => modU_mem hU v ω) (volume_modU_boundary ω) (tendsto_clock_modU hU ω)
        (NNReal.coe_pos.2 ht)]
    rw [e]
    have hS : MeasurableSet[augF 𝓗 P m] {ω | (m : ℝ) ≤ tauP U t ω} := by
      have e2 : {ω | (m : ℝ) ≤ tauP U t ω} = {ω | clock (modU U · ω) m ≤ t} := by
        ext ω
        simp only [mem_ofPred_eq]
        rw [← not_lt, ← not_lt, tauP, invClock_lt_iff (continuous_modU hU ω)
          (fun v => modU_mem hU v ω) (volume_modU_boundary ω) (tendsto_clock_modU hU ω)
          (NNReal.coe_pos.2 ht)]
      rw [e2]
      exact measurableSet_le (adapted_clock_modU hU hκ ha hb m) measurable_const
    refine ⟨(le_iSup (fun u => augF 𝓗 P u) (m : ℝ)) _ hS, fun u => ?_⟩
    simp_rw [WithTop.coe_le_coe]
    rcases lt_or_ge u (m : ℝ) with hu | hu
    · have : {ω | (m : ℝ) ≤ tauP U t ω} ∩ {ω | tauP U t ω ≤ u} = ∅ := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro h; linarith [h.1, h.2]
      rw [this]; exact @MeasurableSet.empty _ (augF 𝓗 P u)
    · exact ((augF 𝓗 P).mono hu _ hS).inter (isStopping_tauP hU hκ ha hb ht u)
  · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) bot_le
    have e : {ω | sigmaLoc U m ω ≤ t} = ∅ := by
      ext ω
      simp only [sigmaLoc, ht0, mem_ofPred_eq, mem_empty_iff_false, iff_false, WithTop.coe_le_coe,
        nonpos_iff_eq_zero, Real.toNNReal_eq_zero, not_le]
      exact clock_pos (continuous_modU hU ω) (fun v => modU_mem hU v ω) (volume_modU_boundary ω) _
    rw [e]; exact @MeasurableSet.empty _ (physFilt hU hκ ha hb t)

theorem isLocalizingSequence_sigmaLoc :
    IsLocalizingSequence (physFilt hU hκ ha hb) (sigmaLoc U) P where
  isStoppingTime := isStoppingTime_sigmaLoc hU hκ ha hb
  mono := ae_of_all _ fun ω m n hmn => WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal
    (monotone_clock (continuous_modU hU ω) (fun v => modU_mem hU v ω) (by exact_mod_cast hmn)))
  tendsto_top := ae_of_all _ fun ω => by
    rw [WithTop.tendsto_nhds_top_iff]
    intro x
    have h := (tendsto_clock_modU hU ω).comp tendsto_natCast_atTop_atTop
    filter_upwards [h.eventually (eventually_gt_atTop ((x : ℝ)))] with m hm
    simp only [sigmaLoc, WithTop.coe_lt_coe]
    exact Real.lt_toNNReal_iff_coe_lt.2 hm

/-! ### Martingales in physical time -/

/-- **Stopped physical-time processes are `𝓖`-martingales.** If `X_0 = 0` and
`X_t = c Y(u(t) ∧ m)` for `t > 0`, where `Y` is a continuous `augF`-martingale on the clock with
`|Y_u| ≤ C₀ e^u` for `u ≤ 0` and `|Y_u| ≤ C_m` for `u ≤ m`, then `X` is a `𝓖`-martingale. -/
theorem martingale_of_phys {Y : ℝ → Ω → ℝ} (hY : IsRegProc Y)
    (hYa : ∀ u, Measurable[augF 𝓗 P u] (Y u))
    (hmart : ∀ w x, w ≤ x → ∀ A, MeasurableSet[augF 𝓗 P w] A →
      ∫ ω in A, Y x ω ∂P = ∫ ω in A, Y w ω ∂P)
    {C₀ : ℝ} (hY0 : ∀ u ω, u ≤ 0 → |Y u ω| ≤ C₀ * exp u) (m : ℕ) {Cm : ℝ}
    (hYb : ∀ (u : ℝ) ω, u ≤ (m : ℝ) → |Y u ω| ≤ Cm) (c : ℝ) {X : ℝ≥0 → Ω → ℝ}
    (hXa : StronglyAdapted (physFilt hU hκ ha hb) X) (hX0 : ∀ ω, X 0 ω = 0)
    (hXt : ∀ t, 0 < t → ∀ ω, X t ω = c * Y (min (tauP U t ω) m) ω) :
    Martingale X (physFilt hU hκ ha hb) P := by
  have hint : ∀ t, Integrable (X t) P := by
    intro t
    by_cases ht : 0 < t
    · refine Integrable.of_bound ((hXa t).mono ((physFilt hU hκ ha hb).le t)).aestronglyMeasurable
        (|c| * Cm) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, hXt t ht ω, abs_mul]
      exact mul_le_mul_of_nonneg_left (hYb _ ω (min_le_right _ _)) (abs_nonneg c)
    · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) bot_le
      have : X t = fun _ => 0 := funext fun ω => by rw [ht0, hX0]
      rw [this]; exact integrable_const _
  refine ⟨hXa, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((physFilt hU hκ ha hb).le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    ((hXa s).mono le_rfl).aestronglyMeasurable).symm
  have hAm : MeasurableSet A := (physFilt hU hκ ha hb).le s A hA
  by_cases hs : 0 < s
  · have ht : 0 < t := lt_of_lt_of_le hs hst
    rw [setIntegral_congr_fun hAm (fun ω _ => hXt s hs ω),
      setIntegral_congr_fun hAm (fun ω _ => hXt t ht ω), integral_const_mul, integral_const_mul]
    congr 1
    rw [physFilt_pos hU hκ ha hb hs] at hA
    refine (setIntegral_min_eq hY hYa hmart (isStopping_tauP hU hκ ha hb hs)
      (isStopping_tauP hU hκ ha hb ht) (tauP_mono hU s t hs hst) m hYb hAm fun u => ?_).symm
    have := hA.2 u
    simp_rw [WithTop.coe_le_coe] at this
    exact this
  · have hs0 : s = 0 := le_antisymm (not_lt.1 hs) bot_le
    rw [hs0, physFilt_zero hU hκ ha hb] at hA
    rw [hs0]
    simp only [hX0, integral_zero]
    rcases MeasurableSpace.measurableSet_bot_iff.1 hA with rfl | rfl
    · simp
    · rw [Measure.restrict_univ]
      by_cases ht : 0 < t
      · rw [integral_congr_ae (ae_of_all _ fun ω => hXt t ht ω), integral_const_mul,
          integral_min_eq_zero hY hYa hmart (isStopping_tauP hU hκ ha hb ht)
            (Nat.cast_nonneg m) hYb hY0, mul_zero]
      · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) bot_le
        simp [ht0, hX0]

end Filt

/-! ### Lévy's characterization -/

theorem stoppedProcess_indicator_eq' {X : ℝ≥0 → Ω → ℝ} (hX0 : ∀ ω, X 0 ω = 0)
    (τ : Ω → WithTop ℝ≥0) :
    stoppedProcess (fun i => {ω | ⊥ < τ ω}.indicator (X i)) τ = stoppedProcess X τ := by
  funext i ω
  simp only [stoppedProcess]
  by_cases h : ⊥ < τ ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from h)]
  · have h0 : τ ω = ⊥ := not_bot_lt_iff.1 h
    rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from h), h0, min_eq_right bot_le]
    exact (hX0 ω).symm

theorem stoppedProcess_sigmaLoc_apply (X : ℝ≥0 → Ω → ℝ) (m : ℕ) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess X (sigmaLoc U m) t ω = X (min t (clock (modU U · ω) m).toNNReal) ω := by
  simp only [stoppedProcess, sigmaLoc, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]

section Levy

variable {ρL ρR : Fin 1 → ℝ} (hU : IsJacobiDiffusion κ (ρL 0 + 2) (ρR 0 + 2) P 𝓗 U)
  (hκ : 0 < κ) (ha : 0 < ρL 0 + 2) (hb : 0 < ρR 0 + 2)
include hU hκ ha hb

theorem ae_nProc_modU_eq :
    ∀ᵐ ω ∂P, ∀ u, nProc (ρL 0) (ρR 0) (modU U) u ω = nProc (ρL 0) (ρR 0) U u ω := by
  filter_upwards [ae_modU_eq hU hκ.le ha hb] with ω hω u
  have e : (fun v => modU U v ω) = fun v => U v ω := funext hω
  simp only [nProc, e]

theorem ae_qProc_modU_eq :
    ∀ᵐ ω ∂P, ∀ u, qProc κ (ρL 0) (ρR 0) (modU U) u ω = qProc κ (ρL 0) (ρR 0) U u ω := by
  filter_upwards [ae_modU_eq hU hκ.le ha hb] with ω hω u
  have e : (fun v => modU U v ω) = fun v => U v ω := funext hω
  simp only [qProc, nProc, e]

omit [IsProbabilityMeasure P] hU hκ ha hb in
theorem bPath_eq_nProc {t : ℝ≥0} (ht : 0 < t) (ω : Ω) :
    bPath κ ρL ρR (modU U · ω) t = nProc (ρL 0) (ρR 0) (modU U) (tauP U t ω) ω / Real.sqrt κ := by
  simp only [bPath, wPath, phys_of_pos (NNReal.coe_pos.2 ht), nProc, tauP]

omit [IsProbabilityMeasure P] hU hκ ha hb in
theorem bPath_zero (ω : Ω) : bPath κ ρL ρR (modU U · ω) 0 = 0 := by
  simp [bPath, wPath, phys_of_nonpos]

omit [IsProbabilityMeasure P] hκ ha hb in
theorem continuous_bPath_modU (ω : Ω) : Continuous fun t => bPath κ ρL ρR (modU U · ω) t := by
  have hc := continuous_modU hU ω
  have h01 : ∀ v, modU U v ω ∈ Icc (0 : ℝ) 1 := fun v => modU_mem hU v ω
  have hnull := volume_modU_boundary (U := U) ω
  have htop := tendsto_clock_modU hU ω
  have h1 := continuous_phys hc h01 hnull htop (continuous_driver hc h01) (tendsto_driver_atBot hc h01)
  have h2 := continuous_phys hc h01 hnull htop (continuous_lowerL hc h01) (tendsto_lowerL_atBot hc h01)
  have h3 := continuous_phys hc h01 hnull htop (continuous_upperL hc h01) (tendsto_upperL_atBot hc h01)
  simp only [bPath, wPath]
  exact (((h1.comp NNReal.continuous_coe).add (continuous_const.mul (h2.comp NNReal.continuous_coe))).add
    (continuous_const.mul (h3.comp NNReal.continuous_coe))).div_const _

theorem stronglyAdapted_bPath :
    StronglyAdapted (physFilt hU hκ.le ha hb) fun t ω => bPath κ ρL ρR (modU U · ω) t := by
  intro t
  refine Measurable.stronglyMeasurable ?_
  show Measurable[physFilt hU hκ.le ha hb t] fun ω => bPath κ ρL ρR (modU U · ω) t
  by_cases ht : 0 < t
  · have e : (fun ω => bPath κ ρL ρR (modU U · ω) t) =
        fun ω => nProc (ρL 0) (ρR 0) (modU U) (tauP U t ω) ω / Real.sqrt κ :=
      funext fun ω => bPath_eq_nProc (κ := κ) (ρL := ρL) (ρR := ρR) ht ω
    rw [e]
    exact (measurable_physFilt hU hκ.le ha hb
      (adapted_nProc (modU_mem hU) (continuous_modU hU) (adapted_modU hU hκ.le ha hb))
      (continuous_nProc (modU_mem hU) (continuous_modU hU)) ht).div_const _
  · have ht0 : t = 0 := le_antisymm (not_lt.1 ht) bot_le
    have e : (fun ω => bPath κ ρL ρR (modU U · ω) t) = fun _ => 0 :=
      funext fun ω => by rw [ht0]; exact bPath_zero (κ := κ) (ρL := ρL) (ρR := ρR) (U := U) ω
    rw [e]; exact measurable_const

/-- **The driving Brownian motion.** `bPath κ ρ_L ρ_R (modU U)` is a Brownian motion in the
physical-time filtration. -/
theorem isFilteredBrownianReal_bPath :
    IsFilteredBrownianReal (physFilt hU hκ.le ha hb)
      (fun t ω => bPath κ ρL ρR (modU U · ω) t) P := by
  set 𝓖 := physFilt hU hκ.le ha hb
  set B : ℝ≥0 → Ω → ℝ := fun t ω => bPath κ ρL ρR (modU U · ω) t with hB
  have hB0 : ∀ ω, B 0 ω = 0 := bPath_zero (κ := κ) (ρL := ρL) (ρR := ρR) (U := U)
  have hBc : ∀ ω, Continuous fun t => B t ω := continuous_bPath_modU (κ := κ) (ρL := ρL) (ρR := ρR) hU
  have hBa : StronglyAdapted 𝓖 B := stronglyAdapted_bPath hU hκ ha hb
  have hprog := hBa.isStronglyProgressive_of_continuous hBc
  have hB2a : StronglyAdapted 𝓖 fun t ω => B t ω ^ 2 - (t : ℝ) := fun t =>
    (((hBa t).measurable.pow_const 2).sub measurable_const).stronglyMeasurable
  have hprog2 := hB2a.isStronglyProgressive_of_continuous fun ω =>
    ((hBc ω).pow 2).sub NNReal.continuous_coe
  set C : ℝ := 1 + |ρL 0| / 2 + |ρR 0| / 2 with hC
  have hNb : ∀ u ω, |nProc (ρL 0) (ρR 0) (modU U) u ω| ≤ C * exp u :=
    abs_nProc_le (modU_mem hU) (continuous_modU hU)
  have hNreg := isRegProc_nProc (ρL := ρL 0) (ρR := ρR 0) (modU_mem hU) (continuous_modU hU)
    (adapted_modU hU hκ.le ha hb)
  have hQreg := isRegProc_qProc (κ := κ) (ρL := ρL 0) (ρR := ρR 0) (modU_mem hU)
    (continuous_modU hU) (adapted_modU hU hκ.le ha hb)
  have hNmart := fun w x hwx A hA => setIntegral_augF_eq (ae_nProc_modU_eq hU hκ ha hb)
    (fun w x hwx A hA => setIntegral_nProc_eq hU hwx hA) (w := w) (x := x) hwx (A := A) hA
  have hQmart := fun w x hwx A hA => setIntegral_augF_eq (ae_qProc_modU_eq hU hκ ha hb)
    (fun w x hwx A hA => setIntegral_qProc_eq hU hwx hA) (w := w) (x := x) hwx (A := A) hA
  have hQb : ∀ u ω, |qProc κ (ρL 0) (ρR 0) (modU U) u ω| ≤ (C ^ 2 + κ / 8) * (exp u * exp u) := by
    intro u ω
    have h1 := hNb u ω
    have h2 := clock_le (continuous_modU hU ω) (fun v => modU_mem hU v ω) u
    have h3 := clock_nonneg (U := fun v => modU U v ω) (fun v => modU_mem hU v ω) u
    have hC0 : 0 ≤ C := by positivity
    unfold qProc
    have hsq : nProc (ρL 0) (ρR 0) (modU U) u ω ^ 2 ≤ C ^ 2 * (exp u * exp u) := by
      have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
      nlinarith [exp_pos u]
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (nProc (ρL 0) (ρR 0) (modU U) u ω), exp_pos u]
  have hcpos : ∀ ω (m : ℕ), 0 < clock (modU U · ω) m := fun ω m =>
    clock_pos (continuous_modU hU ω) (fun v => modU_mem hU v ω) (volume_modU_boundary ω) _
  have hminpos : ∀ (m : ℕ) {t : ℝ≥0} (ht : 0 < t) ω, 0 < min t (clock (modU U · ω) m).toNNReal :=
    fun m t ht ω => lt_min ht (Real.toNNReal_pos.2 (hcpos ω m))
  have hσ := isLocalizingSequence_sigmaLoc hU hκ.le ha hb
  have hBloc : IsLocalMartingale B 𝓖 P := by
    refine ⟨sigmaLoc U, hσ, fun m => ?_⟩
    rw [stoppedProcess_indicator_eq' hB0]
    refine ⟨?_, fun ω => ?_⟩
    · refine martingale_of_phys hU hκ.le ha hb hNreg
        (adapted_nProc (modU_mem hU) (continuous_modU hU) (adapted_modU hU hκ.le ha hb)) hNmart
        (C₀ := C) (fun u ω _ => hNb u ω) m (Cm := C * exp m)
        (fun u ω hu => (hNb u ω).trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 hu)
          (by positivity))) (Real.sqrt κ)⁻¹
        (hprog.stronglyAdapted_stoppedProcess (isStoppingTime_sigmaLoc hU hκ.le ha hb m))
        (fun ω => ?_) (fun t ht ω => ?_)
      · rw [stoppedProcess_sigmaLoc_apply, zero_min, hB0]
      · rw [stoppedProcess_sigmaLoc_apply, hB]
        beta_reduce
        rw [bPath_eq_nProc (κ := κ) (ρL := ρL) (ρR := ρR) (hminpos m ht ω), tauP_min hU ht,
          div_eq_inv_mul]
    · have e : (fun t => stoppedProcess B (sigmaLoc U m) t ω) =
          fun t => B (min t (clock (modU U · ω) m).toNNReal) ω :=
        funext fun t => stoppedProcess_sigmaLoc_apply B m t ω
      rw [e]
      exact ((hBc ω).comp (continuous_id.min continuous_const)).isCadlag
  have hB2loc : IsLocalMartingale (fun t ω => B t ω ^ 2 - (t : ℝ)) 𝓖 P := by
    refine ⟨sigmaLoc U, hσ, fun m => ?_⟩
    rw [stoppedProcess_indicator_eq' (X := fun t ω => B t ω ^ 2 - (t : ℝ)) (fun ω => by simp [hB0])]
    refine ⟨?_, fun ω => ?_⟩
    · refine martingale_of_phys hU hκ.le ha hb hQreg
        (adapted_qProc (modU_mem hU) (continuous_modU hU) (adapted_modU hU hκ.le ha hb)) hQmart
        (C₀ := C ^ 2 + κ / 8) (fun u ω hu => (hQb u ω).trans (mul_le_mul_of_nonneg_left
          (by have := exp_le_one_iff.2 hu; nlinarith [exp_pos u]) (by positivity))) m
        (Cm := (C ^ 2 + κ / 8) * (exp m * exp m))
        (fun u ω hu => (hQb u ω).trans (mul_le_mul_of_nonneg_left (by
          have := exp_le_exp.2 hu; nlinarith [exp_pos u, exp_pos (m : ℝ)]) (by positivity))) κ⁻¹
        (hprog2.stronglyAdapted_stoppedProcess (isStoppingTime_sigmaLoc hU hκ.le ha hb m))
        (fun ω => ?_) (fun t ht ω => ?_)
      · rw [stoppedProcess_sigmaLoc_apply, zero_min]; simp [hB0]
      · rw [stoppedProcess_sigmaLoc_apply]
        simp only [hB]
        rw [bPath_eq_nProc (κ := κ) (ρL := ρL) (ρR := ρR) (hminpos m ht ω), tauP_min hU ht]
        have hcl : ((min t (clock (modU U · ω) m).toNNReal : ℝ≥0) : ℝ) =
            clock (modU U · ω) (min (tauP U t ω) m) := by
          rw [← tauP_min hU ht, tauP, clock_invClock (continuous_modU hU ω)
            (fun v => modU_mem hU v ω) (tendsto_clock_modU hU ω)
            (NNReal.coe_pos.2 (hminpos m ht ω))]
        rw [hcl, qProc, div_pow, Real.sq_sqrt hκ.le]
        field_simp
    · have e : (fun t => stoppedProcess (fun t ω => B t ω ^ 2 - (t : ℝ)) (sigmaLoc U m) t ω) =
          fun t => B (min t (clock (modU U · ω) m).toNNReal) ω ^ 2 -
            ((min t (clock (modU U · ω) m).toNNReal : ℝ≥0) : ℝ) :=
        funext fun t => stoppedProcess_sigmaLoc_apply _ m t ω
      rw [e]
      exact ((((hBc ω).comp (continuous_id.min continuous_const)).pow 2).sub
        (NNReal.continuous_coe.comp (continuous_id.min continuous_const))).isCadlag
  have hpre := MathFin.LevyCharacterization.isFilteredPreBrownian_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  have hbm := MathFin.LevyCharacterization.isBrownianReal_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  exact ⟨hbm, hBa.adapted, fun s t hst => hpre.indep s t hst⟩

end Levy

end TwoSeed

end Sec2

end InteractingSLE
