/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CanonStopBM
import InteractingSLE.Spec.ZhanGT4.DualSeedLawPath

/-!
# Zhan's A.1: stopped Brownian motions from a noise that is continuous only up to the cap

Packet PROVE-A1-RECTLAW. A1-CANON's `isStoppedBM_of_agree` (A.1.3, "inside this rectangle") asks the image noise `N`
to be continuous on all of `ℝ≥0` at every sample. Its proof uses that only for the adaptedness of the stopped Wald
exponential `stopExp a N S`, i.e. of the stopped process `N_{t ∧ S}`. Continuity on `[0, S]` suffices: approximate
`t ∧ S` from below by dyadic `𝓗_t`-measurable times. This is the form needed when the noise is the compensated
residual of the image data (continuous before each cap, possibly without a limit at the image lifetime).

Main results:

* `measurable_stopped_of_continuousOn`: an adapted `N`, continuous on `[0, S ω]` at every sample, read at `t ∧ S` is
  `𝓗_t`-measurable (`S` an `𝓗`-stopping time);
* `stronglyAdapted_stopExp_of_continuousOn`: the stopped Wald exponentials are adapted;
* **`isStoppedBM_of_agree_of_continuousOn`**: `isStoppedBM_of_agree` with continuity of `N` on `[0, S]` only;
* `continuousOn_seedCapacityNoise`: the compensated residual is continuous on `[0, T]` when the driver and the force
  points are, and the gaps are integrable on `[0, T]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RectLaw

open A1Canon

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓗 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}

/-- The dyadic approximation from below of a nonnegative real at level `n`. -/
def dyadicBelow (n : ℕ) (x : ℝ≥0) : ℝ≥0 := (⌊(2 : ℝ≥0) ^ n * x⌋₊ : ℝ≥0) / 2 ^ n

theorem dyadicBelow_le (n : ℕ) (x : ℝ≥0) : dyadicBelow n x ≤ x := by
  unfold dyadicBelow
  rw [div_le_iff₀ (pow_pos (by norm_num) n), mul_comm]
  exact Nat.floor_le (by positivity)

theorem sub_lt_dyadicBelow (n : ℕ) (x : ℝ≥0) : (x : ℝ) - (1 / 2) ^ n < (dyadicBelow n x : ℝ) := by
  unfold dyadicBelow
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hfl := Nat.lt_floor_add_one ((2 : ℝ≥0) ^ n * x)
  have hfl' : (2 : ℝ) ^ n * (x : ℝ) < (⌊(2 : ℝ≥0) ^ n * x⌋₊ : ℝ) + 1 := by
    have := (NNReal.coe_lt_coe).2 hfl
    simpa using this
  rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat, lt_div_iff₀ h2, sub_mul,
    one_div, inv_pow, inv_mul_cancel₀ h2.ne']
  linarith

theorem tendsto_dyadicBelow (x : ℝ≥0) : Tendsto (fun n => dyadicBelow n x) atTop (𝓝 x) := by
  rw [← NNReal.tendsto_coe]
  have hlo : Tendsto (fun n : ℕ => (x : ℝ) - (1 / 2) ^ n) atTop (𝓝 (x : ℝ)) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_sub
      (x : ℝ)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n => (sub_lt_dyadicBelow n x).le) (fun n => NNReal.coe_le_coe.2 (dyadicBelow_le n x))

/-- **An adapted noise, continuous on `[0, S]` at every sample, read at `t ∧ S` is `𝓗_t`-measurable.** -/
theorem measurable_stopped_of_continuousOn (hNa : ∀ t, Measurable[𝓗 t] (N t))
    (hS : IsStoppingTime 𝓗 fun ω => (S ω : WithTop ℝ≥0)) (hNc : ∀ ω, ContinuousOn (N · ω) (Icc 0 (S ω)))
    (t : ℝ≥0) : Measurable[𝓗 t] fun ω => N (min t (S ω)) ω := by
  have hm : Measurable[𝓗 t] fun ω => min t (S ω) := measurable_min_of_isStoppingTime hS t
  -- the approximations `N (dyadicBelow n (t ∧ S))`
  have hk : ∀ n : ℕ, Measurable[𝓗 t] fun ω => ⌊(2 : ℝ≥0) ^ n * min t (S ω)⌋₊ := fun n =>
    Nat.measurable_floor.comp (hm.const_mul _)
  have hg : ∀ (n k : ℕ), Measurable[𝓗 t] fun ω => N (min ((k : ℝ≥0) / 2 ^ n) t) ω := fun n k =>
    (hNa _).mono (𝓗.mono (min_le_right _ _)) le_rfl
  have hf : ∀ n : ℕ, Measurable[𝓗 t] fun ω => N (dyadicBelow n (min t (S ω))) ω := by
    intro n
    have hjoint : Measurable[@Prod.instMeasurableSpace ℕ Ω _ (𝓗 t)]
        fun p : ℕ × Ω => N (min ((p.1 : ℝ≥0) / 2 ^ n) t) p.2 :=
      measurable_from_prod_countable_right fun k => hg n k
    have e : (fun ω => N (dyadicBelow n (min t (S ω))) ω) =
        (fun p : ℕ × Ω => N (min ((p.1 : ℝ≥0) / 2 ^ n) t) p.2) ∘
          fun ω => (⌊(2 : ℝ≥0) ^ n * min t (S ω)⌋₊, ω) := by
      funext ω
      simp only [Function.comp_apply]
      congr 1
      exact (min_eq_left ((dyadicBelow_le n _).trans (min_le_left _ _))).symm
    rw [e]
    exact hjoint.comp ((hk n).prodMk measurable_id)
  refine @measurable_of_tendsto_metrizable Ω ℝ (𝓗 t) _ _ _ _
    (fun n ω => N (dyadicBelow n (min t (S ω))) ω) _ hf ?_
  refine tendsto_pi_nhds.2 fun ω => ?_
  have hmem : min t (S ω) ∈ Icc 0 (S ω) := ⟨bot_le, min_le_right _ _⟩
  have hlim : Tendsto (fun n => dyadicBelow n (min t (S ω))) atTop (𝓝[Icc 0 (S ω)] min t (S ω)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicBelow _, Eventually.of_forall fun n =>
      ⟨bot_le, (dyadicBelow_le n _).trans (min_le_right _ _)⟩⟩
  exact ((hNc ω) _ hmem).tendsto.comp hlim

/-- **The stopped Wald exponentials of a noise continuous on `[0, S]` are adapted.** -/
theorem stronglyAdapted_stopExp_of_continuousOn (hNa : ∀ t, Measurable[𝓗 t] (N t))
    (hS : IsStoppingTime 𝓗 fun ω => (S ω : WithTop ℝ≥0)) (hNc : ∀ ω, ContinuousOn (N · ω) (Icc 0 (S ω)))
    (a : ℝ) : StronglyAdapted 𝓗 (stopExp a N S) := fun t => by
  have h1 := measurable_stopped_of_continuousOn hNa hS hNc t
  have h2 : Measurable[𝓗 t] fun ω => ((min t (S ω) : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp (measurable_min_of_isStoppingTime hS t)
  have h : Measurable[𝓗 t] fun ω => Real.exp (a * N (min t (S ω)) ω - a ^ 2 * ((min t (S ω) : ℝ≥0) : ℝ) / 2) :=
    Real.measurable_exp.comp ((h1.const_mul a).sub ((h2.const_mul _).div_const 2))
  exact h.stronglyMeasurable

variable {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- **One rectangle with a noise continuous only up to the cap** (`isStoppedBM_of_agree` with `N` continuous on
`[0, S ω]` instead of on `ℝ≥0`): a Brownian motion `B` of `𝓖` equal to `N` up to the `𝓗`-stopping time `S` almost
surely, `𝓗` and `𝓖` agreeing before `S`, makes `N` an `𝓗`-Brownian motion stopped at `S`. -/
theorem isStoppedBM_of_agree_of_continuousOn (hB : IsFilteredBrownianReal 𝓖 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hNc : ∀ ω, ContinuousOn (N · ω) (Icc 0 (S ω))) (hNa : ∀ t, Measurable[𝓗 t] (N t))
    (hS : IsStoppingTime 𝓗 fun ω => (S ω : WithTop ℝ≥0))
    (hagree : ∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[𝓗 s] A → MeasurableSet[𝓖 s] (A ∩ {ω | s < S ω}))
    (heq : ∀ᵐ ω ∂P, ∀ t, t ≤ S ω → B t ω = N t ω) : IsStoppedBM P 𝓗 N S := by
  intro a
  have hP := hB.isProbabilityMeasure'
  have hSG : IsStoppingTime 𝓖 fun ω => (S ω : WithTop ℝ≥0) := by
    intro t
    have h := hagree t univ MeasurableSet.univ
    have e : {ω | (S ω : WithTop ℝ≥0) ≤ t} = (univ ∩ {ω | t < S ω})ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_univ, true_and, not_lt]
      exact WithTop.coe_le_coe
    rw [e]
    exact h.compl
  have hMB : Martingale (stopExp a B S) 𝓖 P := by
    rw [stopExp_eq_stoppedProcess]
    exact InteractingSLE.Martingale.stoppedProcess_of_rightContinuous (martingale_wald hB a)
      (fun ω t => (Real.continuous_exp.comp (((hBc ω).const_mul a).sub
        ((NNReal.continuous_coe.const_mul (a ^ 2)).div_const 2))).continuousWithinAt) hSG
  have hae : ∀ t, stopExp a N S t =ᵐ[P] stopExp a B S t := fun t => by
    filter_upwards [heq] with ω hω
    simp only [stopExp, hω _ (min_le_right t (S ω))]
  have hadp := stronglyAdapted_stopExp_of_continuousOn hNa hS hNc a
  have hint : ∀ t, Integrable (stopExp a N S t) P := fun t => (hMB.integrable t).congr (hae t).symm
  refine ⟨hadp, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓗.le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_) (hadp s).aestronglyMeasurable).symm
  have hgt : MeasurableSet {ω | s < S ω} := by
    have h := hagree s univ MeasurableSet.univ
    simpa using 𝓖.le s _ h
  have hAm : MeasurableSet A := 𝓗.le s A hA
  rw [← integral_inter_add_sdiff hgt (hint t).integrableOn, ← integral_inter_add_sdiff hgt (hint s).integrableOn]
  congr 1
  · rw [setIntegral_congr_ae (hAm.inter hgt) (Eventually.mono (hae t) fun ω h _ => h),
      setIntegral_congr_ae (hAm.inter hgt) (Eventually.mono (hae s) fun ω h _ => h)]
    exact hMB.setIntegral_eq hst (hagree s A hA)
  · refine setIntegral_congr_fun (hAm.diff hgt) fun ω hω => ?_
    have hle : S ω ≤ s := not_lt.1 hω.2
    simp only [stopExp, min_eq_right hle, min_eq_right (hle.trans hst)]

end Stopped

/-! ### Continuity of the compensated residual before a cap -/

section Residual

variable {nL nR : ℕ}

/-- A primitive `t ↦ ∫₀ᵗ f` read on `ℝ≥0` is continuous on `[0, T]` when `f` is integrable on `[0, T]`. -/
theorem continuousOn_primitive_nnreal {f : ℝ → ℝ} {T : ℝ≥0} (hf : IntervalIntegrable f MeasureTheory.volume 0 T) :
    ContinuousOn (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..(t : ℝ), f s) (Icc 0 T) := by
  have hf' : IntegrableOn f (uIcc 0 (T : ℝ)) volume := by
    rw [uIcc_of_le T.coe_nonneg]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le T.coe_nonneg).1 hf
  have h := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := (T : ℝ)) hf'
  have hmaps : MapsTo (fun t : ℝ≥0 => (t : ℝ)) (Icc 0 T) (uIcc 0 (T : ℝ)) := fun t ht => by
    rw [uIcc_of_le T.coe_nonneg]
    exact ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht.2⟩
  exact h.comp NNReal.continuous_coe.continuousOn hmaps

/-- **The compensated residual is continuous on `[0, T]`** when the driver is and the gap integrands are integrable
on `[0, T]`. -/
theorem continuousOn_seedCapacityNoise {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0} (hw : ContinuousOn w (Icc 0 T))
    (hL : ∀ i, IntervalIntegrable (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 T)
    (hR : ∀ j, IntervalIntegrable (fun s : ℝ => ρR j / (w s.toNNReal - vR j s.toNNReal)) volume 0 T) :
    ContinuousOn (seedCapacityNoise κ ρL ρR w vL vR) (Icc 0 T) := by
  unfold seedCapacityNoise
  refine ((hw.sub ?_).sub ?_).div_const _
  · exact continuousOn_finsetSum _ fun i _ => continuousOn_primitive_nnreal (hL i)
  · exact continuousOn_finsetSum _ fun j _ => continuousOn_primitive_nnreal (hR j)

end Residual

end InteractingSLE.ZhanGT4.A1RectLaw
