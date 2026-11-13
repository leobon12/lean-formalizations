import InteractingSLE.SLE8.Assembly
import InteractingSLE.SLE8.Counting
import InteractingSLE.SLE8.ChangeOfMeasure
import InteractingSLE.SLE8.AL14.Corollary1

/-!
# SLE₈ note, Theorem 1.1: the last two bridges

Source: `source/sle8-continuity.pdf` (transcription `source/sle8/sle8-continuity.md`), Lemma 3.1
(anchor `lem-3.1`, p. 4), Proposition 4.1 (anchor `prop-4.1`, p. 7), proof of Theorem 1.1 (anchor
`thm-1.1-proof`, pp. 11–12), and [AL14] Corollary 1.

The assembly `ae_exists_continuous_trace_of_corollaryOne_of_scale_count` (`Assembly.lean`) proves
the frozen Theorem 1.1 from two hypotheses:

* `AL14CorollaryOneStatement P` (`Lemma21.lean`): the convergent half of [AL14] Corollary 1 at the
  scales `n + 1`; it is `AL14.al14_corollary1_summable` (`AL14/Corollary1.lean`) with the index
  shifted by one (`al14CorollaryOneStatement_holds`);
* Proposition 4.1, which is `scaleCount_of_lemma31` (`Counting.lean`) given `Lemma31Statement P`
  (`Counting/Height.lean`). This file proves `Lemma31Statement P` (`lemma31Statement_holds`) from
  the construction of the packet PROVE-S8-L31 (`ChangeOfMeasure.lean` and its submodules).

## The Lemma 3.1 bridge

`Lemma31Statement` concerns the reverse flow driven by `√8 β` itself (`β` a Brownian motion with
continuous paths and `β 0 = 0`), the height-parameter objects `heightJ`, `heightTau`, `rfPhi` of
`Counting/Height.lean` and the σ-algebra `heightStoppedSigma`. The construction of PROVE-S8-L31 is
applied to `B₃ = goodBM β y` (`β` modified on the null set `notReach β y` where the height never
reaches `√5`), whose objects are `vJ`, `vPhi`, `termLevel`, the filtration `vFilt` and
`ℚ = tiltMeasure P B₃ y`.

* `heightClock_eq_hitTime`, `heightJ_eq_htJ`, `heightJ_eq_vJ`, `rfPhi_eq_vPhi`, `heightTau_eq`:
  deterministic identities between the two parametrizations (every path);
* `measurable_heightStoppedMap`: the generator of `heightStoppedSigma` for `B₃` is measurable with
  respect to the σ-algebra of the stopping time `τ_T − u₀` (progressive measurability of the
  continuous adapted processes `vJ`, `vPhi`);
* off `notReach β y` the flows of `β` and `B₃` coincide, and `ℚ ≪ P` (a density), so the `ℚ`-a.s.
  identification `J = 2β'` and (3.2) transfer; (3.3) is deterministic.

## Main results

* `al14CorollaryOneStatement_holds`: [AL14] Corollary 1 in the form `Assembly.lean` consumes;
* `lemma31Statement_holds`: Lemma 3.1 in the form `Counting.lean` consumes;
* `ae_exists_continuous_trace_final`: the conclusion of the frozen Theorem 1.1, unconditionally.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology ENNReal NNReal

namespace InteractingSLE.SLE8

open QuantumZipper ChangeOfMeasure AL14

/-! ### [AL14] Corollary 1 at the scales `n + 1` -/

/-- **[AL14] Corollary 1** (convergent half) in the form of `AL14CorollaryOneStatement`: the series
of `al14_corollary1_summable` restricted to the indices `n + 1`. -/
theorem al14CorollaryOneStatement_holds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    AL14CorollaryOneStatement P := by
  intro B _ _ _ hB β _ hβ4
  set F : ℕ → ℝ≥0∞ := fun n => ∑ j ∈ Finset.range (4 ^ n + 1),
    P {ω | (2 : ℝ) ^ n * (n : ℝ) ^ (-β) ≤
      ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime n j)) ((alHeight n : ℂ) * I)‖} with hF
  have hsum : ∑' n, F n ≠ ∞ := AL14.al14_corollary1_summable hβ4 hB
  have hle := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective 1) F
  simp only [hF, Nat.cast_add, Nat.cast_one] at hle hsum
  exact ne_top_of_le_ne_top hsum hle

/-! ### Deterministic identities between the two height parametrizations -/

/-- The clock of `Counting/Height.lean` is the hitting time of `ChangeOfMeasure/Clock.lean`. -/
theorem heightClock_eq_hitTime (W : ℝ → ℝ) (y u : ℝ) :
    heightClock W y u = (hitTime W y (Real.exp u) : ℝ) := by
  rw [heightClock, hitTime, NNReal.coe_sInf]
  congr 1
  ext s
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨hs0, hs⟩
    exact ⟨⟨s, hs0⟩, hs, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.2, ht⟩

/-- Below the cap `U`, `J_u` of `Counting/Height.lean` is `htJ` of `ChangeOfMeasure/Clock.lean`. -/
theorem heightJ_eq_htJ (W : ℝ → ℝ) (y : ℝ) {U u : ℝ} (hu : u ≤ U) :
    heightJ W y u = htJ W y U u := by
  rw [heightJ, htJ, min_eq_left hu, heightClock_eq_hitTime]
  rfl

section Paths

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {y : ℝ}

/-- `J_u` of `Counting/Height.lean` for the flow of `√8 B` is `vJ B y (u − u₀)` (for `u ≤ U = log
√5`; both are `J_{u₀} = 0` below `u₀`). -/
theorem heightJ_eq_vJ (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (hy1 : y ≤ 1) {u : ℝ}
    (hu : u ≤ Real.log √5) (ω : Ω) :
    heightJ (drive 8 B ω) y u = vJ B y (u - Real.log y).toNNReal ω := by
  rcases le_total (Real.log y) u with h | h
  · rw [vJ_eq_htJ hy hy1 h ω, heightJ_eq_htJ _ _ hu]
  · have hW := continuous_drive8 hBc ω
    have h0 : (u - Real.log y).toNNReal = (Real.log y - Real.log y).toNNReal := by
      rw [sub_self, Real.toNNReal_zero, Real.toNNReal_eq_zero]
      linarith
    rw [h0, vJ_eq_htJ hy hy1 le_rfl ω,
      ← heightJ_eq_htJ _ _ (Real.log_le_log hy (y_le_sqrt5 hy1)), heightJ, heightJ,
      heightClock_eq_hitTime, heightClock_eq_hitTime, Real.exp_log hy,
      hitTime_eq_zero hW hy le_rfl,
      hitTime_eq_zero hW hy (by calc Real.exp u ≤ Real.exp (Real.log y) := Real.exp_le_exp.2 h
        _ = y := Real.exp_log hy)]

/-- `τ_T = log Y_T = u₀ + termLevel`. -/
theorem heightTau_eq (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) {T : ℝ} (hT : 0 ≤ T) (ω : Ω) :
    heightTau (drive 8 B ω) y T = Real.log y + termLevel B y T ω :=
  log_im_eq_termLevel hBc hy hT ω

/-- `τ_T ≤ U = log √5`. -/
theorem heightTau_le (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (hy1 : y ≤ 1) {T : ℝ}
    (hT : T ∈ Icc (0 : ℝ) 1) (ω : Ω) :
    heightTau (drive 8 B ω) y T ≤ Real.log √5 := by
  have h := termLevel_le hBc hy hy1 hT ω
  have h' : ((termLevel B y T ω : ℝ≥0) : ℝ) ≤ vTop y := by exact_mod_cast h
  rw [coe_vTop hy hy1, Real.log_div (by positivity) hy.ne'] at h'
  rw [heightTau_eq hBc hy hT.1]
  linarith

/-- `Φ_T = Φ̂` at the terminal level. -/
theorem rfPhi_eq_vPhi (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (hy1 : y ≤ 1) {T : ℝ}
    (hT : T ∈ Icc (0 : ℝ) 1) (ω : Ω) :
    rfPhi (drive 8 B ω) y T = vPhi B y (termLevel B y T ω) ω := by
  have hW := continuous_drive8 hBc ω
  have hc := vClock_termLevel hBc hy hy1 hT ω
  rw [vPhi, min_eq_left (termLevel_le hBc hy hy1 hT ω), snd_stProc_eq hBc hy, hc,
    Real.exp_log (norm_pos_iff.2 (deriv_revMap_ne_zero _ hW hT.1 (mem_H_mul_I hy))), rfPhi,
    deriv_revFlow]

end Paths

/-! ### The generator of `heightStoppedSigma` is `𝓖_{τ_T}`-measurable -/

/-- The map generating `heightStoppedSigma`: `(τ_T, Φ_T, u ↦ J_{min(u, τ_T)})`. -/
def heightStoppedMap (V : ℝ → ℝ) (y T : ℝ) : ℝ × ℝ × (ℝ → ℝ) :=
  (heightTau V y T, rfPhi V y T, fun u => heightJ V y (min u (heightTau V y T)))

theorem heightStoppedSigma_eq {Ω : Type*} (V : Ω → ℝ → ℝ) (y T : ℝ) :
    heightStoppedSigma V y T =
      MeasurableSpace.comap (fun ω => heightStoppedMap (V ω) y T) inferInstance :=
  rfl

section Stopped

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {y : ℝ}

/-- The truncated level `(min u (u₀ + t) − u₀)⁺ = min (u − u₀)⁺ t`. -/
theorem toNNReal_min_sub (u l : ℝ) (t : ℝ≥0) :
    (min u (l + t) - l).toNNReal = min (u - l).toNNReal t := by
  rw [← min_sub_sub_right, add_sub_cancel_left,
    Monotone.map_min (fun _ _ h => Real.toNNReal_mono h), Real.toNNReal_coe]

/-- **The generator of `heightStoppedSigma` is `𝓖_{τ_T}`-measurable**: `τ_T`, `Φ_T = Φ̂_{τ_T}` and
`J_{min(u, τ_T)} = J` at the stopping time `min(τ_T, u)` are measurable with respect to the
σ-algebra of the stopping time `τ_T − u₀` (stopped values of the continuous adapted, hence
progressive, processes `vJ`, `vPhi`). -/
theorem measurable_heightStoppedMap (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    (hy : 0 < y) (hy1 : y ≤ 1) (hreach : ReachesTop B y) {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) :
    Measurable[(isStoppingTime_termLevel hBc hBm hy hy1 hreach hT).measurableSpace]
      (fun ω => heightStoppedMap (drive 8 B ω) y T) := by
  have hτ := isStoppingTime_termLevel hBc hBm hy hy1 hreach hT
  have hτm : Measurable[hτ.measurableSpace] (fun ω => (termLevel B y T ω : ℝ≥0)) :=
    hτ.measurable.untopA
  have hPhi : IsStronglyProgressive (vFilt hBc hBm hy hy1 hreach) (vPhi B y) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun v => (measurable_vPhi hBc hBm hy hy1 hreach v).stronglyMeasurable)
      (continuous_vPhi hBc hy hy1 hreach)
  have hJ : IsStronglyProgressive (vFilt hBc hBm hy hy1 hreach) (vJ B y) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun v => (measurable_vJ hBc hBm hy hy1 hreach v).stronglyMeasurable)
      (continuous_vJ hBc hy hy1 hreach)
  have hPhim : Measurable[hτ.measurableSpace]
      (stoppedValue (vPhi B y) fun ω => ((termLevel B y T ω : ℝ≥0) : WithTop ℝ≥0)) :=
    measurable_stoppedValue hPhi hτ
  have hJm : ∀ c : ℝ≥0, Measurable[hτ.measurableSpace]
      (stoppedValue (vJ B y) fun ω => min ((termLevel B y T ω : ℝ≥0) : WithTop ℝ≥0) c) := by
    intro c
    have hτc := hτ.min_const c
    exact (measurable_stoppedValue hJ hτc).mono
      (hτc.measurableSpace_mono hτ fun ω => min_le_left _ _) le_rfl
  have heq : (fun ω => heightStoppedMap (drive 8 B ω) y T) = fun ω =>
      (Real.log y + (termLevel B y T ω : ℝ),
        stoppedValue (vPhi B y) (fun ω => ((termLevel B y T ω : ℝ≥0) : WithTop ℝ≥0)) ω,
        fun u => stoppedValue (vJ B y)
          (fun ω => min ((termLevel B y T ω : ℝ≥0) : WithTop ℝ≥0) (u - Real.log y).toNNReal)
          ω) := by
    funext ω
    refine Prod.ext (heightTau_eq hBc hy hT.1 ω) (Prod.ext (rfPhi_eq_vPhi hBc hy hy1 hT ω) ?_)
    funext u
    have hle : min u (heightTau (drive 8 B ω) y T) ≤ Real.log √5 :=
      (min_le_right _ _).trans (heightTau_le hBc hy hy1 hT ω)
    show heightJ (drive 8 B ω) y (min u (heightTau (drive 8 B ω) y T)) =
      vJ B y (min ((termLevel B y T ω : ℝ≥0) : WithTop ℝ≥0)
        ((u - Real.log y).toNNReal : WithTop ℝ≥0)).untopA ω
    rw [heightJ_eq_vJ hBc hy hy1 hle ω, heightTau_eq hBc hy hT.1 ω, toNNReal_min_sub,
      ← WithTop.coe_min, min_comm]
    rfl
  rw [heq]
  exact ((measurable_const_add (Real.log y)).comp (measurable_coe_nnreal_real.comp hτm)).prodMk
    (hPhim.prodMk
      ((@measurable_pi_iff Ω ℝ (fun _ => ℝ) hτ.measurableSpace _ _).mpr fun u => hJm _))

end Stopped

/-! ### Lemma 3.1 in the form of `Lemma31Statement` -/

/-- **Lemma 3.1 of the SLE₈ note** in the form consumed by Proposition 4.1 (`Lemma31Statement`,
`Counting/Height.lean`), with `C_occ = occConst = cosh² 1 / 2`. The construction of
`exists_criticalChangeOfMeasure` is applied to `goodBM β y`, which agrees with `β` off the `P`-null
set `notReach β y`; `ℚ = tiltMeasure P (goodBM β y) y ≪ P`. -/
theorem lemma31Statement_holds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    Lemma31Statement P := by
  refine ⟨occConst, fun β hβ hβc hβm hβ0 T hT y hy => ?_⟩
  obtain ⟨hy0, hy1⟩ := hy
  have hy5 : y ≤ √5 := y_le_sqrt5 hy1
  have hB₃ : IsBrownianReal (goodBM β y) P := isBrownianReal_goodBM hβ hβc hβm hβ0 hy0 hy5
  have hB₃c : ∀ ω, Continuous (goodBM β y · ω) := continuous_goodBM hβc
  have hB₃m : ∀ t, Measurable (goodBM β y t) := measurable_goodBM hβc hβm hy0
  have hB₃0 : ∀ ω, goodBM β y 0 ω = 0 := fun ω => by
    simp only [goodBM]; split_ifs <;> simp [hβ0]
  have hreach : ReachesTop (goodBM β y) y := reachesTop_goodBM hy0 hy1
  have hBpre := hB₃.toIsPreBrownianReal
  have hnull : P (notReach β y) = 0 :=
    measure_not_reachesTop hβ.toIsPreBrownianReal hβc hβm hβ0 hy0 hy5
  have hgood : ∀ᵐ ω ∂P, ω ∉ notReach β y := measure_eq_zero_iff_ae_notMem.1 hnull
  have hQP : tiltMeasure P (goodBM β y) y ≪ P := withDensity_absolutelyContinuous _ _
  have hdrive : ∀ ω, ω ∉ notReach β y → drive 8 (goodBM β y) ω = drive 8 β ω :=
    fun ω h => drive_goodBM_of_not_mem h
  refine ⟨⟨tiltMeasure P (goodBM β y) y,
    isProbabilityMeasure_tiltMeasure hBpre hB₃c hB₃m hB₃0 hy0 hy1 hreach,
    ⟨tiltBM (goodBM β y) y, isBrownianReal_tiltBM hBpre hB₃c hB₃m hB₃0 hy0 hy1 hreach, ?_⟩, ?_⟩, ?_⟩
  · -- `ℚ`-a.s. `J_{u₀+v} = 2 β'_v` up to `τ_T`
    refine hQP.ae_le ?_
    filter_upwards [hgood] with ω hω v hv
    rw [← hdrive ω hω] at hv ⊢
    have hτle := heightTau_le hB₃c hy0 hy1 hT ω
    have hv' : v ≤ vTop y := by
      rw [← NNReal.coe_le_coe, coe_vTop hy0 hy1, Real.log_div (by positivity) hy0.ne']
      linarith
    have hu : Real.log y + v ≤ Real.log √5 := by linarith
    rw [heightJ_eq_vJ hB₃c hy0 hy1 hu ω, add_sub_cancel_left, Real.toNNReal_coe,
      tiltBM_of_le hy0 hy1 hv', vJ, min_eq_left hv']
    ring
  · -- (3.2)
    intro a ha E hE hEa
    rw [heightStoppedSigma_eq, MeasurableSpace.measurableSet_comap] at hE
    obtain ⟨S, hS, rfl⟩ := hE
    have hτ := isStoppingTime_termLevel hB₃c hB₃m hy0 hy1 hreach hT
    have hE' : MeasurableSet[hτ.measurableSpace]
        ((fun ω => heightStoppedMap (drive 8 (goodBM β y) ω) y T) ⁻¹' S) :=
      measurable_heightStoppedMap hB₃c hB₃m hy0 hy1 hreach hT hS
    have hae : (fun ω => heightStoppedMap (drive 8 β ω) y T) ⁻¹' S =ᵐ[P]
        (fun ω => heightStoppedMap (drive 8 (goodBM β y) ω) y T) ⁻¹' S := by
      filter_upwards [hgood] with ω hω
      simp only [mem_preimage, hdrive ω hω]
    rw [measure_congr hae, measure_congr (hQP.ae_le hae)]
    have hexp : y ^ 2 * a ^ (-2 : ℝ) = y ^ 2 / a ^ 2 := by
      rw [Real.rpow_neg ha.1.le, Real.rpow_two, div_eq_mul_inv]
    rw [← hexp]
    refine measure_le_tilt hBpre hB₃c hB₃m hB₃0 hy0 hy1 hreach hT ha.1 hE' ?_
    filter_upwards [hgood] with ω hω hωE
    have h := hdrive ω hω
    have hω' : ω ∈ (fun ω => heightStoppedMap (drive 8 β ω) y T) ⁻¹' S := by
      simp only [mem_preimage] at hωE ⊢
      rwa [h] at hωE
    have := hEa hω'
    simp only [mem_ofPred_eq, rfPhi, deriv_revFlow] at this
    rwa [h]
  · -- (3.3), on every path
    intro a ha ω hphi
    have hW := continuous_drive8 hβc ω
    have hYT := im_htZ_pos hW hy0 hT.1
    have hY5 : (htZ (drive 8 β ω) y T).im ≤ √5 := by
      have h := im_htZ_sq_le hW hy0 hT.1
      rw [← Real.sqrt_sq hYT.le]
      exact Real.sqrt_le_sqrt (by nlinarith [hT.2])
    have hphi' : a ≤ y * ‖deriv (revMap (drive 8 β ω) T) ((y : ℂ) * I)‖ := by
      rw [rfPhi, deriv_revFlow] at hphi
      exact hphi
    have hτ5 : Real.log (htZ (drive 8 β ω) y T).im ≤ Real.log √5 := Real.log_le_log hYT hY5
    refine ⟨?_, ?_⟩
    · show Real.log a ≤ Real.log (htZ (drive 8 β ω) y T).im
      have := phi_le_im_div hW hy0 hT.1
      have h3 : a ≤ (htZ (drive 8 β ω) y T).im := by
        calc a ≤ y * ‖deriv (revMap (drive 8 β ω) T) ((y : ℂ) * I)‖ := hphi'
          _ ≤ y * ((htZ (drive 8 β ω) y T).im / y) := by gcongr
          _ = (htZ (drive 8 β ω) y T).im := by field_simp
      exact Real.log_le_log ha.1 h3
    · have hocc := volume_occupation_le hW hy0 hT.1 (U := Real.log √5) hτ5 hY5 ha.1 hphi'
      have hset : {u | u ∈ Icc (Real.log y) (heightTau (drive 8 β ω) y T) ∧
            |heightJ (drive 8 β ω) y u| ≤ 1} =
          {u | u ∈ Icc (Real.log y) (Real.log (htZ (drive 8 β ω) y T).im) ∧
            |htJ (drive 8 β ω) y (Real.log √5) u| ≤ 1} := by
        ext u
        simp only [mem_ofPred_eq, mem_Icc]
        constructor
        · rintro ⟨⟨hu1, hu2⟩, hu3⟩
          exact ⟨⟨hu1, hu2⟩, by rwa [← heightJ_eq_htJ _ _ (hu2.trans hτ5)]⟩
        · rintro ⟨⟨hu1, hu2⟩, hu3⟩
          exact ⟨⟨hu1, hu2⟩, by rwa [heightJ_eq_htJ _ _ (hu2.trans hτ5)]⟩
      rw [hset]
      refine hocc.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ occConst_pos.le))
      have h5 := log_sqrt_five_le_one
      rw [one_div, Real.log_inv]
      linarith

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1 of the SLE₈ note** (continuity of the SLE₈ trace), with the conclusion of the
frozen `InteractingSLE.SLE8.ae_exists_continuous_trace`: the assembly
`ae_exists_continuous_trace_of_corollaryOne_of_scale_count` applied to [AL14] Corollary 1
(`al14CorollaryOneStatement_holds`) and Proposition 4.1 (`scaleCount_of_lemma31` with
`lemma31Statement_holds`). -/
theorem ae_exists_continuous_trace_final {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ,
      TendstoLocallyUniformly
          (fun (y : ℝ) (t : ℝ≥0) =>
            QuantumZipper.fwdMapInv (QuantumZipper.drive 8 B ω) t (y * Complex.I))
          γ (𝓝[>] 0) ∧
        Continuous γ ∧ (∀ t, γ t ∈ QuantumZipper.Hbar) ∧ γ 0 = 0 ∧
        ∀ t : ℝ≥0,
          (∃ z ∈ QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t,
              connectedComponentIn (QuantumZipper.H \ γ '' Icc 0 t) z =
                QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) ∧
            ¬ Bornology.IsBounded
              (QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) :=
  ae_exists_continuous_trace_of_corollaryOne_of_scale_count (al14CorollaryOneStatement_holds P)
    (scaleCount_of_lemma31 (lemma31Statement_holds P)) hB

end InteractingSLE.SLE8
