/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketMartLife
import InteractingSLE.Spec.Sec7.PhaseSelAdaptMain
import InteractingSLE.Spec.Sec7.ContinuityWeights

/-!
# Aux. lemma 125 before the lifetime, part 2: Theorem 2.4's converse at one stopping time before the lifetime

Packet PROVE-STRIPSYS14 (specification §7.4, proof of Aux. lemma 125, `source/spec/p385-432.md` L224–L232, p. 397:
"Stop before a fixed coordinate bound or at `ζ`, whichever occurs first […] These are genuine stopping times in the
relative history and supply pre-lifetime localizations for the martingale and SDE arguments"; Aux. lemma 122,
pp. 389–391).

Setting: a driver `W` continuous before a lifetime `T`, random `𝓕₀`-measurable marks with the force points at their
geometric images (`PocketTraversal.geomLW`, `geomRW`), and Aux. lemma 122's hypotheses before `T`
(`HasPhaseMeansBefore`: for every choice of the bounded harmonic extensions of the phase-shifted word data before `T`,
the coupling means are local martingales before `min (swallowTime z) T` and continuous before swallowing). At a
stopping time `σ < T` the coordinates are restarted (`stopW`: the driver frozen after `σ`; the force points its
geometric images), Aux. lemma 122 (`PhaseSelAdapt.aux122_adapt`) selects the zero phase on a time-zero event of full
measure in `{σ > 0}`, and Theorem 2.4's converse applies there. Results:

* `hasPhaseMeans_stop`: Aux. lemma 122's hypotheses for the restarted coordinates with the lifetime `σ`;
* **`martingale_martProc_stop`**: the driver's martingale part `M = W − W₀ + ½ ∑ ρ (V − V₀)` stopped at `σ`, and
  `M² − k t` stopped at `σ`, are martingales when the coordinates are bounded up to `σ`;
* **`ae_isWordEntrance_stop`**: almost surely Definition 2.1's equations hold before `σ`, with the noise `M/√k`, when
  all side partial sums of the weights exceed `−2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketMartLife

open MartChar PocketTraversal PhaseSel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}

/-- **Aux. lemma 122's hypotheses before a lifetime `T`, for the geometric coordinates of random marks**: for every
choice `U` of the bounded harmonic extensions of the phase-shifted word data (`PhaseSel.phaseData`, phase `d`) before
`T`, every coupling mean is a local martingale before `min (swallowTime z) T` and continuous on every window `[0, T']`,
`T' < T`, before swallowing (specification pp. 389–390: "Retain a stopped Gaussian field kernel whose harmonic mean
`M_t(z)` is a continuous local martingale until `z` is swallowed"). -/
def HasPhaseMeansBefore (k : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (d : ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0) : Prop :=
  ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω) (d t ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U ω t)) →
    (∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (fun t ω => couplingMean k (wpath W ω) t (U ω t) z)) ∧
    ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → ((T'.toNNReal : ℝ≥0) : WithTop ℝ≥0) < T ω →
      z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' →
      ContinuousOn (fun t : ℝ => couplingMean k (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T')

/-- The driver frozen after the random time `σ`. -/
def stopW (W : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := fun t ω => PhaseSelAdapt.contW (W · ω) (σ ω) t

/-- The phase kept up to `σ` and set to `0` afterwards. -/
def stopD (d : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := fun t ω => if t ≤ σ ω then d t ω else 0

section Basic

variable {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0} {σ : Ω → ℝ≥0}

theorem stopW_of_le {t : ℝ≥0} {ω : Ω} (h : t ≤ σ ω) : stopW W σ t ω = W t ω := PhaseSelAdapt.contW_of_le h

theorem continuousOn_Iic_of_lt (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) (ω : Ω) : ContinuousOn (W · ω) (Iic (σ ω)) :=
  (hWc ω).mono fun _ hr => lt_of_le_of_lt (WithTop.coe_le_coe.2 hr) (hσT ω)

theorem continuous_stopW (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) (ω : Ω) : Continuous (stopW W σ · ω) :=
  PhaseSelAdapt.continuous_contW (continuousOn_Iic_of_lt hWc hσT ω)

theorem geomLW_stopW {xL : Ω → Fin nL → ℝ} (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ ω) (i : Fin nL) :
    geomLW (stopW W σ) xL i t ω = geomLW W xL i t ω :=
  (geomLW_congr (continuous_stopW hWc hσT ω) (fun _ hs => (stopW_of_le (hs.trans ht)).symm) xL i).symm

theorem geomRW_stopW {xR : Ω → Fin nR → ℝ} (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ ω) (j : Fin nR) :
    geomRW (stopW W σ) xR j t ω = geomRW W xR j t ω :=
  (geomRW_congr (continuous_stopW hWc hσT ω) (fun _ hs => (stopW_of_le (hs.trans ht)).symm) xR j).symm

/-- The frozen driver is adapted when an adapted process agrees with the driver before `T`. -/
theorem stronglyAdapted_stopW {Wk : ℝ≥0 → Ω → ℝ} (hWka : StronglyAdapted 𝓕 Wk)
    (hWk : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Wk t ω = W t ω)
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) :
    StronglyAdapted 𝓕 (stopW W σ) := by
  have hlt : ∀ ω t, t ≤ σ ω → (t : WithTop ℝ≥0) < T ω := fun ω t ht =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 ht) (hσT ω)
  have hc : ∀ ω, ContinuousOn (Wk · ω) (Iic (σ ω)) := fun ω =>
    (continuousOn_Iic_of_lt hWc hσT ω).congr fun t ht => hWk ω t (hlt ω t ht)
  have h := PhaseSelAdapt.stronglyAdapted_contW hσ hWka hc
  have e : (fun t ω => PhaseSelAdapt.contW (Wk · ω) (σ ω) t) = stopW W σ := by
    funext t ω
    simp only [stopW, PhaseSelAdapt.contW]
    exact hWk ω _ (hlt ω _ (min_le_right _ _))
  rwa [e] at h

end Basic

/-! ### Aux. lemma 122's hypotheses for the restarted coordinates -/

section Hyps

variable {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}
  {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {d : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ≥0}

/-- **Aux. lemma 122's hypotheses for the coordinates restarted at `σ < T`**, with the lifetime `σ`, in the form of
`PhaseSelAdapt.aux122_adapt` (the extensions of the restarted data are extensions of the original data up to `σ`,
completed after `σ` by the explicit phase-shifted extension; the coupling means stopped at `σ` do not see the
completion). -/
theorem hasPhaseMeans_stop [IsFiniteMeasure P] (hk : 0 < k)
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR d T)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω)
    (U' : Ω → ℝ≥0 → ℂ → ℝ) (hU' : ∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => geomLW (stopW W σ) xL i t ω - stopW W σ t ω)
          (fun j => geomRW (stopW W σ) xR j t ω - stopW W σ t ω) (stopD d σ t ω))
        (forceJumpSet (fun i => geomLW (stopW W σ) xL i t ω - stopW W σ t ω)
          (fun j => geomRW (stopW W σ) xR j t ω - stopW W σ t ω)) (U' ω t)) :
    (∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath (stopW W σ) ω) z : WithTop ℝ≥0) (σ ω))
      (fun t ω => couplingMean k (wpath (stopW W σ) ω) t (U' ω t) z)) ∧
    ∀ ω (z : ℂ) (T'' : ℝ), 0 ≤ T'' → ((T''.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (σ ω : WithTop ℝ≥0) →
      z ∈ H \ QuantumZipper.fwdHull (wpath (stopW W σ) ω) T'' →
      ContinuousOn (fun t : ℝ => couplingMean k (wpath (stopW W σ) ω) t (U' ω t.toNNReal) z) (Icc 0 T'') := by
  classical
  have hlt : ∀ ω t, t ≤ σ ω → (t : WithTop ℝ≥0) < T ω := fun ω t ht =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 ht) (hσT ω)
  -- the explicit phase-shifted extension of the original data before `T`
  set U₀ : Ω → ℝ≥0 → ℂ → ℝ := fun ω t ξ => meanExt k (shiftL k ρL (d t ω)) (shiftR k ρR (d t ω)) (W t ω)
    (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω) ξ + d t ω with hU₀def
  have hU₀ : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω) (d t ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U₀ ω t) :=
    fun ω t ht => isBoundedHarmonicExtension_unshift hk (sub_nonpos.2 (geomLW_le_of_lt (hWc ω) ht xL 0))
      (sub_nonneg.2 (le_geomRW_of_lt (hWc ω) ht xR 0)) (isBoundedHarmonicExtension_meanExt k _ _ (W t ω) _ _)
  -- the completed extension of the original data
  set U : Ω → ℝ≥0 → ℂ → ℝ := fun ω t => if t ≤ σ ω then U' ω t else U₀ ω t with hUdef
  have hU : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω) (d t ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U ω t) := by
    intro ω t ht
    by_cases hts : t ≤ σ ω
    · simp only [hUdef, hts, ↓reduceIte]
      have e1 : (fun i => geomLW (stopW W σ) xL i t ω - stopW W σ t ω) = fun i => geomLW W xL i t ω - W t ω :=
        funext fun i => by rw [geomLW_stopW hWc hσT hts, stopW_of_le hts]
      have e2 : (fun j => geomRW (stopW W σ) xR j t ω - stopW W σ t ω) = fun j => geomRW W xR j t ω - W t ω :=
        funext fun j => by rw [geomRW_stopW hWc hσT hts, stopW_of_le hts]
      have e3 : stopD d σ t ω = d t ω := by simp only [stopD, hts, ↓reduceIte]
      have h := hU' ω t
      rw [e1, e2, e3] at h
      exact h
    · simp only [hUdef, hts, ↓reduceIte]
      exact hU₀ ω t ht
  obtain ⟨hm, hc⟩ := hM U hU
  have hpeq : ∀ ω (r : ℝ), 0 ≤ r → ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (σ ω : WithTop ℝ≥0) →
      wpath (stopW W σ) ω r = wpath W ω r := fun ω r _ hr => stopW_of_le (WithTop.coe_le_coe.1 hr)
  have hagree : ∀ ω (t : ℝ), 0 ≤ t → t.toNNReal ≤ σ ω → EqOn (wpath (stopW W σ) ω) (wpath W ω) (Icc 0 t) :=
    fun ω t _ hts r hr => hpeq ω r hr.1 (WithTop.coe_le_coe.2 ((Real.toNNReal_le_toNNReal hr.2).trans hts))
  refine ⟨fun z hz => ?_, fun ω z T'' h0 hT'' hzK => ?_⟩
  · have hrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) <
        min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω) →
        ContinuousWithinAt (fun t : ℝ≥0 => couplingMean k (wpath W ω) t (U ω t) z) (Ici s) s := fun ω s hs => by
      have h := PhaseSelAdapt.continuousWithinAt_of_continuousOn_Icc hz
        (f := fun t : ℝ => couplingMean k (wpath W ω) t (U ω t.toNNReal) z)
        (fun T' h0 hT' hzK => hc ω z T' h0 hT' hzK) hs
      simpa only [Real.toNNReal_coe] using h
    have h2 := PhaseSelAdapt.isLocalMartingaleBefore_min_stop (hm z hz) hrc hσ
    have hζ : (fun ω => min (min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
        (σ ω : WithTop ℝ≥0)) =
        fun ω => min (QuantumZipper.swallowTime (wpath (stopW W σ) ω) z : WithTop ℝ≥0) (σ ω) := funext fun ω => by
      calc _ = min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (min (T ω) (σ ω : WithTop ℝ≥0)) :=
            min_assoc _ _ _
        _ = min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (σ ω : WithTop ℝ≥0) :=
            congrArg (min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (min_eq_right (hσT ω).le)
        _ = _ := Lemma71B.min_swallowTime_congr (fun r hr hrs => (hpeq ω r hr hrs).symm) hz
    have h3 : IsLocalMartingaleBefore 𝓕 P
        (fun ω => min (QuantumZipper.swallowTime (wpath (stopW W σ) ω) z : WithTop ℝ≥0) (σ ω))
        (fun t ω => couplingMean k (wpath W ω) t (U ω t) z) :=
      PhaseSelAdapt.isLocalMartingaleBefore_congr_life (fun ω => congrFun hζ ω) h2
    refine PhaseSelFull.isLocalMartingaleBefore_sub_const_before 0 h3 fun t ω ht => ?_
    have hts : t ≤ σ ω := WithTop.coe_le_coe.1 (ht.trans (min_le_right _ _))
    rw [sub_zero]
    simp only [hUdef, hts, ↓reduceIte]
    exact Lemma71B.couplingMean_congr t.coe_nonneg (hagree ω t t.coe_nonneg (by rwa [Real.toNNReal_coe])) k _ z
  · have hT''σ : T''.toNNReal ≤ σ ω := WithTop.coe_le_coe.1 hT''
    have hT''σ' : T'' ≤ σ ω := (Real.toNNReal_le_iff_le_coe).1 hT''σ
    obtain ⟨r, hσr, hrT⟩ := WithTop.lt_iff_exists_coe_btwn.1 (hσT ω)
    have hσr' : σ ω < r := WithTop.coe_lt_coe.1 hσr
    have hWr : ContinuousOn (W · ω) (Iic r) := (hWc ω).mono fun t ht =>
      lt_of_le_of_lt (WithTop.coe_le_coe.2 ht) hrT
    have hzK' : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T'' := by
      refine PhaseSelAdapt.notMem_fwdHull_of_eqOn (w₂ := fun x : ℝ => PhaseSelAdapt.contW (W · ω) r x.toNNReal)
        ((PhaseSelAdapt.continuous_contW hWr).comp continuous_real_toNNReal) h0
        (lt_of_le_of_lt hT''σ' (by exact_mod_cast hσr')) ?_ ?_ hzK
      · intro x hx
        have hx' : x.toNNReal ≤ σ ω := (Real.toNNReal_le_toNNReal hx.2).trans hT''σ
        show PhaseSelAdapt.contW (W · ω) (σ ω) x.toNNReal = PhaseSelAdapt.contW (W · ω) r x.toNNReal
        rw [PhaseSelAdapt.contW_of_le hx', PhaseSelAdapt.contW_of_le (hx'.trans hσr'.le)]
      · intro x hx
        show PhaseSelAdapt.contW (W · ω) r x.toNNReal = W x.toNNReal ω
        exact PhaseSelAdapt.contW_of_le (Real.toNNReal_le_iff_le_coe.2 hx.2)
    have hcc := hc ω z T'' h0 (lt_of_le_of_lt hT'' (hσT ω)) hzK'
    refine hcc.congr fun t ht => ?_
    have hts : t.toNNReal ≤ σ ω := (Real.toNNReal_le_toNNReal ht.2).trans hT''σ
    simp only [hUdef, hts, ↓reduceIte]
    exact Lemma71B.couplingMean_congr ht.1 (hagree ω t ht.1 hts) k _ z

/-- **Aux. lemma 122 for the coordinates restarted at `σ < T`** (`PhaseSelAdapt.aux122_adapt` with the lifetime
`σ`): there is a time-zero event `A`, containing almost every `ω` with `σ ω > 0`, under whose conditional law the
canonical coupling means of the restarted coordinates are local martingales before `min (swallowTime z) σ`. -/
theorem exists_aux122_stop [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    {Wk : ℝ≥0 → Ω → ℝ} (hWka : StronglyAdapted 𝓕 Wk) (hWk : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Wk t ω = W t ω)
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < T ω → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR d T)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) :
    ∃ A : Set Ω, MeasurableSet[𝓕 0] A ∧ (∀ᵐ ω ∂P, 0 < σ ω → ω ∈ A) ∧
      (P A ≠ 0 → ∀ z ∈ H, IsLocalMartingaleBefore (subFilt 𝓕 A) (condSub P A)
        (fun ω : A => min (QuantumZipper.swallowTime (wpath (fun t (ω : A) => stopW W σ t ω) ω) z :
          WithTop ℝ≥0) (σ ω))
        (coupProc k ρL ρR (fun t (ω : A) => stopW W σ t ω) (fun i t (ω : A) => geomLW (stopW W σ) xL i t ω)
          (fun j t (ω : A) => geomRW (stopW W σ) xR j t ω) z)) := by
  have hk0 : 0 < k := by linarith
  have hWc' : ∀ ω, Continuous (stopW W σ · ω) := continuous_stopW hWc hσT
  have hW0' : ∀ ω, stopW W σ 0 ω = 0 := fun ω => (stopW_of_le zero_le).trans (hW0 ω)
  have hWa' : StronglyAdapted 𝓕 (stopW W σ) := stronglyAdapted_stopW hWka hWk hWc hσ hσT
  have hxL0 : ∀ ω i, xL ω i ≤ 0 := fun ω i => (hxLi ω (Fin.zero_le i)).trans_eq (hseedL ω)
  have hxR0 : ∀ ω j, 0 ≤ xR ω j := fun ω j => (hseedR ω).symm.trans_le (hxRi ω (Fin.zero_le j))
  have hd' : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) ≤ (σ ω : WithTop ℝ≥0) →
      ∃ n : ℤ, stopD d σ t ω = n * phaseStep k := fun t ω ht hts => by
    have hts' : t ≤ σ ω := WithTop.coe_le_coe.1 hts
    simp only [stopD, hts', ↓reduceIte]
    exact hd t ω ht (lt_of_le_of_lt hts (hσT ω))
  obtain ⟨A, hA0, -, hAae, hloc⟩ := PhaseSelAdapt.aux122_adapt (P := P) (𝓕 := 𝓕)
    (T := fun ω => (σ ω : WithTop ℝ≥0)) (d := stopD d σ) hk hrL hrL' hrR hrR'
    (fun ω => by rw [geomLW_zero hWc' hW0' (hxL0 ω 0), hseedL ω])
    (fun ω => by rw [geomRW_zero hWc' hW0' (hxR0 ω 0), hseedR ω])
    (fun ω i => by rw [geomLW_zero hWc' hW0' (hxL0 ω _)]; exact hxLd ω i)
    (fun ω j => by rw [geomRW_zero hWc' hW0' (hxR0 ω _)]; exact hxRd ω j)
    hW0' hWc' hWa' (stronglyAdapted_geomLW hWa' hWc' hxLm) (stronglyAdapted_geomRW hWa' hWc' hxRm)
    (fun ω t i => geomLW_le hWc' xL ω t i) (fun ω t j => le_geomRW hWc' xR ω t j)
    (isForcePath_geomLW hWc' xL) (isForcePath_geomRW hWc' xR) (antitone_geomLW hWc' xL)
    (monotone_geomRW hWc' xR) (fun ω t => antitone_index_geomLW hWc' (hxLi ω) t)
    (fun ω t => monotone_index_geomRW hWc' (hxRi ω) t)
    (fun ω i j s t hst => geomLW_merge hWc' xL ω i j s t hst)
    (fun ω i j s t hst => geomRW_merge hWc' xR ω i j s t hst)
    (fun ω t ht i j => geom_sep hWc' xL xR ω t ht i j) hσ hd'
    (fun U hU z hz => (hasPhaseMeans_stop hk0 hWc hM hσ hσT U hU).1 z hz)
    (fun U hU => (hasPhaseMeans_stop hk0 hWc hM hσ hσT U hU).2)
  refine ⟨A, hA0, ?_, hloc⟩
  filter_upwards [hAae] with ω hω hσ0
  exact hω (WithTop.coe_lt_coe.2 hσ0)

end Hyps

/-! ### The martingale part stopped at `σ` -/

section Mart

open PhaseSelFull

/-- **The localizing time at a level above a bound of the coordinates up to `σ ≤ N` is `σ` itself.** -/
theorem lifeLoc_eq_of_le {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W t ω) (hVc : ∀ j ω, Continuous fun t => V j t ω) {σ : Ω → ℝ≥0} {N : ℕ}
    (hσN : ∀ ω, σ ω ≤ N) (hbd : ∀ ω, 0 < σ ω → ∀ t ≤ σ ω, absSum W V t ω ≤ N) (ω : Ω) :
    lifeLoc W V (fun ω => (σ ω : WithTop ℝ≥0)) (N + 1) ω = σ ω := by
  refine le_antisymm (lifeLoc_le_T W V _ (N + 1) ω) ?_
  rcases (zero_le : (0 : ℝ≥0) ≤ σ ω).eq_or_lt with h0 | h0
  · have hb : ((0 : ℝ≥0) : WithTop ℝ≥0) = ⊥ := rfl
    rw [← h0, hb]; exact bot_le
  have hZc := continuous_absSum hWc hVc
  have hmem : ω ∈ initEvent W V (N + 1) := by
    show absSum W V 0 ω < ((N + 1 : ℕ) : ℝ)
    push_cast
    linarith [hbd ω h0 0 zero_le]
  rw [lifeLoc_of_mem hmem]
  refine le_min (le_min ?_ ?_) le_rfl
  · exact WithTop.coe_le_coe.2 ((hσN ω).trans (by exact_mod_cast Nat.le_succ N))
  · by_contra hlt
    push Not at hlt
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    rw [← he] at hlt
    have hle : MathFin.exitTime (absSum W V) (N + 1) ω ≤ (e : WithTop ℝ≥0) := he.ge
    obtain ⟨u, hu, hN⟩ := (MathFin.exitTime_le_iff hZc (N + 1) e ω).1 hle
    have hue : u ≤ σ ω := hu.2.trans (WithTop.coe_lt_coe.1 hlt).le
    have hb := hbd ω h0 u hue
    have hpos : 0 ≤ absSum W V u ω := by
      simp only [absSum]; positivity
    rw [abs_of_nonneg hpos] at hN
    push_cast at hN
    linarith

variable {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}
  {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {d : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ≥0}

/-- The martingale part of the original coordinates up to `σ` is that of the restarted coordinates. -/
theorem martProc_stopW (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) {t : ℝ≥0} {ω : Ω} (ht : t ≤ σ ω) :
    martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) t ω =
      martProc (jointρ ρL ρR) (stopW W σ) (jointV (geomLW (stopW W σ) xL) (geomRW (stopW W σ) xR)) t ω := by
  have h0 : (0 : ℝ≥0) ≤ σ ω := zero_le
  have hV : ∀ s, s ≤ σ ω → ∀ j, jointV (geomLW W xL) (geomRW W xR) j s ω =
      jointV (geomLW (stopW W σ) xL) (geomRW (stopW W σ) xR) j s ω := fun s hs j => by
    cases j with
    | inl i => exact (geomLW_stopW hWc hσT hs i).symm
    | inr j => exact (geomRW_stopW hWc hσT hs j).symm
  simp only [martProc, stopW_of_le ht, stopW_of_le h0, hV t ht, hV 0 h0]

/-- **The driver's martingale part stopped at `σ < T`, and its square compensated by `k t`, are martingales**
(Theorem 2.4's converse before the lifetime, specification p. 397: "Stop before a fixed coordinate bound or at `ζ`,
whichever occurs first"), when the coordinates are bounded by `N` up to `σ ≤ N`. -/
theorem martingale_martProc_stop [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    {Wk : ℝ≥0 → Ω → ℝ} (hWka : StronglyAdapted 𝓕 Wk) (hWk : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Wk t ω = W t ω)
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < T ω → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR d T)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω)
    {N : ℕ} (hσN : ∀ ω, σ ω ≤ N)
    (hbd : ∀ ω, 0 < σ ω → ∀ t ≤ σ ω, absSum W (jointV (geomLW W xL) (geomRW W xR)) t ω ≤ N) :
    Martingale (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) (min t (σ ω)) ω) 𝓕 P ∧
      Martingale (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) (min t (σ ω)) ω ^ 2
        - k * ((min t (σ ω) : ℝ≥0) : ℝ)) 𝓕 P := by
  have hk0 : 0 < k := by linarith
  obtain ⟨A, hA0, hAae, hloc⟩ := exists_aux122_stop hk hrL hrL' hrR hrR' hW0 hWc hWka hWk hxLm hxRm hseedL
    hseedR hxLd hxRd hxLi hxRi hd hM hσ hσT
  have hA : MeasurableSet A := 𝓕.le 0 _ hA0
  set W' := stopW W σ with hW'def
  set VL' := geomLW W' xL with hVL'def
  set VR' := geomRW W' xR with hVR'def
  set ρ := jointρ ρL ρR with hρ
  set V' := jointV VL' VR' with hV'def
  have hWc' : ∀ ω, Continuous (W' · ω) := continuous_stopW hWc hσT
  have hW0' : ∀ ω, W' 0 ω = 0 := fun ω => (stopW_of_le zero_le).trans (hW0 ω)
  have hWa' : StronglyAdapted 𝓕 W' := stronglyAdapted_stopW hWka hWk hWc hσ hσT
  have hVLa' : ∀ i, StronglyAdapted 𝓕 (VL' i) := stronglyAdapted_geomLW hWa' hWc' hxLm
  have hVRa' : ∀ j, StronglyAdapted 𝓕 (VR' j) := stronglyAdapted_geomRW hWa' hWc' hxRm
  have hVc' : ∀ j ω, Continuous fun t => V' j t ω := fun j ω => by
    cases j with
    | inl i => exact (isForcePath_geomLW hWc' xL ω i).1
    | inr j => exact (isForcePath_geomRW hWc' xR ω j).1
  have hVa' : ∀ j, StronglyAdapted 𝓕 (V' j) := fun j => by
    cases j with
    | inl i => exact hVLa' i
    | inr j => exact hVRa' j
  -- the bound of the restarted coordinates up to `σ`
  have hbd' : ∀ ω, 0 < σ ω → ∀ t ≤ σ ω, absSum W' V' t ω ≤ N := fun ω h0 t ht => by
    have e : absSum W' V' t ω = absSum W (jointV (geomLW W xL) (geomRW W xR)) t ω := by
      simp only [absSum, hW'def, stopW_of_le ht]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      cases j with
      | inl i =>
        show |geomLW (stopW W σ) xL i t ω| = |geomLW W xL i t ω|
        rw [geomLW_stopW hWc hσT ht i]
      | inr j =>
        show |geomRW (stopW W σ) xR j t ω| = |geomRW W xR j t ω|
        rw [geomRW_stopW hWc hσT ht j]
    rw [e]; exact hbd ω h0 t ht
  have hll : ∀ ω, lifeLocN W' V' (fun ω => (σ ω : WithTop ℝ≥0)) (N + 1) ω = σ ω := fun ω => by
    have h := lifeLoc_eq_of_le hWc' hVc' hσN hbd' ω
    rw [← coe_lifeLocN] at h
    exact WithTop.coe_le_coe.1 h.le |>.antisymm (WithTop.coe_le_coe.1 h.ge)
  -- the two processes, in the restarted coordinates
  set Y : ℝ≥0 → Ω → ℝ := fun t ω => martProc ρ W' V' (min t (σ ω)) ω with hYdef
  set Y2 : ℝ≥0 → Ω → ℝ := fun t ω => Y t ω ^ 2 - k * ((min t (σ ω) : ℝ≥0) : ℝ) with hY2def
  have e1 : (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) (min t (σ ω)) ω) = Y :=
    funext fun t => funext fun ω => martProc_stopW hWc hσT (min_le_right _ _)
  have e2 : (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) (min t (σ ω)) ω ^ 2
      - k * ((min t (σ ω) : ℝ≥0) : ℝ)) = Y2 := by
    funext t ω
    exact congrArg (fun x => x ^ 2 - k * ((min t (σ ω) : ℝ≥0) : ℝ)) (martProc_stopW hWc hσT (min_le_right t (σ ω)))
  rw [e1, e2]
  have hMa : StronglyAdapted 𝓕 (martProc ρ W' V') := stronglyAdapted_martProc hWa' hVa'
  have hMc : ∀ ω, Continuous fun t => martProc ρ W' V' t ω := continuous_martProc hWc' hVc'
  have hYa : StronglyAdapted 𝓕 Y := fun t =>
    (PhaseSelAdapt.measurable_stopped_value hσ hMa (fun ω => (hMc ω).continuousOn) t).stronglyMeasurable
  have hmin := PhaseSelAdapt.measurable_min_coe hσ
  have hY2a : StronglyAdapted 𝓕 Y2 := fun t =>
    (((hYa t).measurable.pow_const 2).sub (measurable_const.mul (hmin t))).stronglyMeasurable
  have hYb : ∀ t ω, |Y t ω| ≤ 2 * (N + 1 : ℕ) + (∑ j, |ρ j|) * (N + 1 : ℕ) := fun t ω => by
    have h := abs_martProc_lifeLocN_le (ρ := ρ) (T := fun ω => (σ ω : WithTop ℝ≥0)) hWc' hVc' (N + 1) t ω
    rwa [hll ω] at h
  have hYi : ∀ t, Integrable (Y t) P := fun t =>
    Integrable.of_bound ((hYa t).mono (𝓕.le t)).aestronglyMeasurable _ (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hYb t ω)
  have hσb : ∀ t ω, |((min t (σ ω) : ℝ≥0) : ℝ)| ≤ N := fun t ω => by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast (min_le_right _ _).trans (hσN ω)
  have hY2i : ∀ t, Integrable (Y2 t) P := fun t => by
    refine Integrable.of_bound ((hY2a t).mono (𝓕.le t)).aestronglyMeasurable
      ((2 * (N + 1 : ℕ) + (∑ j, |ρ j|) * (N + 1 : ℕ)) ^ 2 + |k| * N) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hYb t ω) 2
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hσb t ω) (abs_nonneg _)
  -- off `A`, almost surely `σ = 0`
  have hY0 : ∀ ω, σ ω = 0 → ∀ t, Y t ω = 0 := fun ω h0 t => by
    simp only [hYdef, h0, min_eq_right (zero_le : (0 : ℝ≥0) ≤ t), martProc, martValue, sub_self, mul_zero,
      Finset.sum_const_zero, add_zero]
  have hY20 : ∀ ω, σ ω = 0 → ∀ t, Y2 t ω = 0 := fun ω h0 t => by
    simp only [hY2def, hY0 ω h0 t, h0, min_eq_right (zero_le : (0 : ℝ≥0) ≤ t), NNReal.coe_zero, mul_zero,
      sub_zero]; norm_num
  have hoff : ∀ᵐ ω ∂P, ω ∉ A → σ ω = 0 := by
    filter_upwards [hAae] with ω hω hωA
    by_contra h
    exact hωA (hω (pos_iff_ne_zero.2 h))
  by_cases h0 : P A = 0
  · have hnA : ∀ᵐ ω ∂P, ω ∉ A := measure_eq_zero_iff_ae_notMem.1 h0
    have hz : ∀ᵐ ω ∂P, σ ω = 0 := by filter_upwards [hnA, hoff] with ω h1 h2 using h2 h1
    have hz1 : ∀ t, Y t =ᵐ[P] (0 : ℝ≥0 → Ω → ℝ) t := fun t => by
      filter_upwards [hz] with ω hω using hY0 ω hω t
    have hz2 : ∀ t, Y2 t =ᵐ[P] (0 : ℝ≥0 → Ω → ℝ) t := fun t => by
      filter_upwards [hz] with ω hω using hY20 ω hω t
    have h00 : Martingale (0 : ℝ≥0 → Ω → ℝ) 𝓕 P := martingale_zero _ _ _
    exact ⟨⟨hYa, fun i j hij => (condExp_congr_ae (hz1 j)).trans ((h00.2 i j hij).trans (hz1 i).symm)⟩,
      ⟨hY2a, fun i j hij => (condExp_congr_ae (hz2 j)).trans ((h00.2 i j hij).trans (hz2 i).symm)⟩⟩
  have hQ : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA h0
  have hMM := martingale_martProc_lifeLoc (P := condSub P A) (𝓕 := subFilt 𝓕 A) (ρL := ρL) (ρR := ρR)
    (W := fun t (ω : A) => W' t ω) (VL := fun i t (ω : A) => VL' i t ω) (VR := fun j t (ω : A) => VR' j t ω)
    hk0 (fun ω => hW0' ω) (fun ω => hWc' ω) (stronglyAdapted_sub hWa') (fun i => stronglyAdapted_sub (hVLa' i))
    (fun j => stronglyAdapted_sub (hVRa' j)) (fun ω t i => geomLW_le hWc' xL ω t i)
    (fun ω t j => le_geomRW hWc' xR ω t j) (fun ω i => isForcePath_geomLW hWc' xL ω i)
    (fun ω j => isForcePath_geomRW hWc' xR ω j) (isStoppingTime_sub hσ) (hloc h0) (N + 1)
  have hjV : (jointV (fun i t (ω : A) => VL' i t ω) (fun j t (ω : A) => VR' j t ω)) =
      fun j t (ω : A) => V' j t ω := funext fun j => by cases j <;> rfl
  rw [hjV] at hMM
  have hllA : ∀ ω : A, lifeLocN (fun t (ω : A) => W' t ω) (fun j t (ω : A) => V' j t ω)
      (fun ω : A => (σ ω : WithTop ℝ≥0)) (N + 1) ω = σ ω := fun ω => by
    have h := lifeLoc_eq_of_le (W := fun t (ω : A) => W' t ω) (V := fun j t (ω : A) => V' j t ω)
      (σ := fun ω : A => σ ω) (fun ω => hWc' ω) (fun j ω => hVc' j ω) (fun ω => hσN ω)
      (fun ω h0 t ht => hbd' ω h0 t ht) ω
    rw [← coe_lifeLocN] at h
    exact WithTop.coe_le_coe.1 h.le |>.antisymm (WithTop.coe_le_coe.1 h.ge)
  have hs1 : stoppedProcess (martProc ρ (fun t (ω : A) => W' t ω) fun j t (ω : A) => V' j t ω)
      (lifeLoc (fun t (ω : A) => W' t ω) (fun j t (ω : A) => V' j t ω) (fun ω : A => (σ ω : WithTop ℝ≥0)) (N + 1)) =
      fun t (ω : A) => Y t ω := by
    funext t ω
    rw [stoppedProcess_lifeLoc, hllA ω]
    rfl
  have hs2 : stoppedProcess (fun t (ω : A) => martProc ρ (fun t (ω : A) => W' t ω)
      (fun j t (ω : A) => V' j t ω) t ω ^ 2 - k * t)
      (lifeLoc (fun t (ω : A) => W' t ω) (fun j t (ω : A) => V' j t ω) (fun ω : A => (σ ω : WithTop ℝ≥0)) (N + 1)) =
      fun t (ω : A) => Y2 t ω := by
    funext t ω
    rw [stoppedProcess_lifeLoc, hllA ω]
    rfl
  rw [hs1, hs2] at hMM
  refine ⟨martingale_of_martingale_sub hA0 h0 hYa hYi ?_ hMM.1, martingale_of_martingale_sub hA0 h0 hY2a hY2i ?_
    hMM.2⟩
  · filter_upwards [hoff] with ω hω hωA t
    rw [hY0 ω (hω hωA) t, hY0 ω (hω hωA) 0]
  · filter_upwards [hoff] with ω hω hωA t
    rw [hY20 ω (hω hωA) t, hY20 ω (hω hωA) 0]

/-- **Definition 2.1's equations hold before `σ < T`, almost surely, with the noise `M/√k`** (Aux. lemma 122's
conclusion before the lifetime: "the coordinates satisfy this SDE"; specification p. 397: "All side partial sums are
greater than `−2`, so the integrated driving construction has no continuation threshold"): Aux. lemma 117 before the
stopping lifetime `σ` (`PhaseSelFull.exists_isWordEntrance_before`) for the restarted coordinates, under the
conditional law given the time-zero event of `exists_aux122_stop`. -/
theorem ae_isWordEntrance_stop [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    {Wk : ℝ≥0 → Ω → ℝ} (hWka : StronglyAdapted 𝓕 Wk) (hWk : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Wk t ω = W t ω)
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < T ω → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR d T)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) :
    ∀ᵐ ω ∂P, Aux117.IsWordEntrance k (xL ω) (xR ω) ρL ρR (W · ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω)
      (fun t => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) t ω / Real.sqrt k) (σ ω) := by
  have hk0 : 0 < k := by linarith
  obtain ⟨A, hA0, hAae, hloc⟩ := exists_aux122_stop hk hrL hrL' hrR hrR' hW0 hWc hWka hWk hxLm hxRm hseedL
    hseedR hxLd hxRd hxLi hxRi hd hM hσ hσT
  have hA : MeasurableSet A := 𝓕.le 0 _ hA0
  set W' := stopW W σ with hW'def
  have hWc' : ∀ ω, Continuous (W' · ω) := continuous_stopW hWc hσT
  have hW0' : ∀ ω, W' 0 ω = 0 := fun ω => (stopW_of_le zero_le).trans (hW0 ω)
  have hWa' : StronglyAdapted 𝓕 W' := stronglyAdapted_stopW hWka hWk hWc hσ hσT
  have hxL0 : ∀ ω i, xL ω i ≤ 0 := fun ω i => (hxLi ω (Fin.zero_le i)).trans_eq (hseedL ω)
  have hxR0 : ∀ ω j, 0 ≤ xR ω j := fun ω j => (hseedR ω).symm.trans_le (hxRi ω (Fin.zero_le j))
  have hlt : ∀ ω (t : ℝ≥0), t ≤ σ ω → (t : WithTop ℝ≥0) < T ω := fun ω t ht =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 ht) (hσT ω)
  -- the initial values of the original coordinates
  have hL0 : ∀ ω i, geomLW W xL i 0 ω = xL ω i := fun ω i => by
    rw [← geomLW_stopW hWc hσT zero_le i, geomLW_zero hWc' hW0' (hxL0 ω i)]
  have hR0 : ∀ ω j, geomRW W xR j 0 ω = xR ω j := fun ω j => by
    rw [← geomRW_stopW hWc hσT zero_le j, geomRW_zero hWc' hW0' (hxR0 ω j)]
  -- the conclusion at `σ = 0`
  have hzero : ∀ ω, σ ω = 0 → Aux117.IsWordEntrance k (xL ω) (xR ω) ρL ρR (W · ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω)
      (fun t => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) t ω / Real.sqrt k) (σ ω) :=
    fun ω h0 => by
      rw [h0, ENNReal.coe_zero]
      exact isWordEntrance_zero (hW0 ω) (hL0 ω) (hR0 ω)
  -- the conclusion from that of the restarted coordinates
  have hconv : ∀ ω, Aux117.IsWordEntrance k (fun i => geomLW W' xL i 0 ω) (fun j => geomRW W' xR j 0 ω) ρL ρR
      (W' · ω) (fun i t => geomLW W' xL i t ω) (fun j t => geomRW W' xR j t ω)
      (fun t => martProc (jointρ ρL ρR) W' (jointV (geomLW W' xL) (geomRW W' xR)) t ω / Real.sqrt k) (σ ω) →
      Aux117.IsWordEntrance k (xL ω) (xR ω) ρL ρR (W · ω) (fun i t => geomLW W xL i t ω)
        (fun j t => geomRW W xR j t ω)
        (fun t => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) t ω / Real.sqrt k) (σ ω) := by
    intro ω h
    have e1 : (fun i => geomLW W' xL i 0 ω) = xL ω := funext fun i => by
      rw [geomLW_stopW hWc hσT zero_le i, hL0 ω i]
    have e2 : (fun j => geomRW W' xR j 0 ω) = xR ω := funext fun j => by
      rw [geomRW_stopW hWc hσT zero_le j, hR0 ω j]
    rw [e1, e2] at h
    refine isWordEntrance_congr_le h (fun t ht => (stopW_of_le (ENNReal.coe_le_coe.1 ht)).symm)
      (fun t ht i => (geomLW_stopW hWc hσT (ENNReal.coe_le_coe.1 ht) i).symm)
      (fun t ht j => (geomRW_stopW hWc hσT (ENNReal.coe_le_coe.1 ht) j).symm) (fun t ht => ?_)
    rw [martProc_stopW hWc hσT (ENNReal.coe_le_coe.1 ht.le)]
  have hoff : ∀ᵐ ω ∂P, ω ∉ A → σ ω = 0 := by
    filter_upwards [hAae] with ω hω hωA
    by_contra h
    exact hωA (hω (pos_iff_ne_zero.2 h))
  by_cases h0 : P A = 0
  · have hnA : ∀ᵐ ω ∂P, ω ∉ A := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [hnA, hoff] with ω h1 h2 using hzero ω (h2 h1)
  have hQ : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA h0
  have hVLa' := stronglyAdapted_geomLW hWa' hWc' hxLm
  have hVRa' := stronglyAdapted_geomRW hWa' hWc' hxRm
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, -, -, hBeq, hae⟩ := PhaseSelFull.exists_isWordEntrance_before
    (P := condSub P A) (𝓕 := subFilt 𝓕 A) (ρL := ρL) (ρR := ρR)
    (W := fun t (ω : A) => W' t ω) (VL := fun i t (ω : A) => geomLW W' xL i t ω)
    (VR := fun j t (ω : A) => geomRW W' xR j t ω) hk0 (fun ω => hW0' ω) (fun ω => hWc' ω)
    (stronglyAdapted_sub hWa') (fun i => stronglyAdapted_sub (hVLa' i)) (fun j => stronglyAdapted_sub (hVRa' j))
    (fun ω t i => geomLW_le hWc' xL ω t i) (fun ω t j => le_geomRW hWc' xR ω t j)
    (fun ω i => isForcePath_geomLW hWc' xL ω i) (fun ω j => isForcePath_geomRW hWc' xR ω j)
    (fun ω i => antitone_geomLW hWc' xL ω i) (fun ω j => monotone_geomRW hWc' xR ω j)
    (fun ω t => antitone_index_geomLW hWc' (hxLi ω) t) (fun ω t => monotone_index_geomRW hWc' (hxRi ω) t)
    (fun ω i j s t hst => geomLW_merge hWc' xL ω i j s t hst) (fun ω i j s t hst => geomRW_merge hWc' xR ω i j s t hst)
    (fun ω t ht i j => geom_sep hWc' xL xR ω t ht i j) (isStoppingTime_sub hσ) (hloc h0)
  have hjV : (jointV (fun i t (ω : A) => geomLW W' xL i t ω) (fun j t (ω : A) => geomRW W' xR j t ω)) =
      fun j t (ω : A) => jointV (geomLW W' xL) (geomRW W' xR) j t ω := funext fun j => by cases j <;> rfl
  set R : Ω → Prop := fun ω => Aux117.IsWordEntrance k (fun i => geomLW W' xL i 0 ω)
      (fun j => geomRW W' xR j 0 ω) ρL ρR (W' · ω) (fun i t => geomLW W' xL i t ω)
      (fun j t => geomRW W' xR j t ω)
      (fun t => martProc (jointρ ρL ρR) W' (jointV (geomLW W' xL) (geomRW W' xR)) t ω / Real.sqrt k)
      (σ ω) with hRdef
  have h1 : ∀ᵐ p ∂((condSub P A).prod P₀), R (p.1 : Ω) := by
    filter_upwards [hae] with p hp
    have hcol : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < (σ (p.1 : Ω) : ℝ≥0∞) →
        Aux117.ColliderNe ρL (fun t => W' t (p.1 : Ω)) (fun i t => geomLW W' xL i t (p.1 : Ω)) u ∧
          Aux117.ColliderNe ρR (fun t => W' t (p.1 : Ω)) (fun j t => geomRW W' xR j t (p.1 : Ω)) u :=
      fun u _ _ => Aux117.colliderNe_of_not_thresholdCondition (not_thresholdCondition_of_partialSums
        (antitone_index_geomLW hWc' (hxLi _) u) (fun i => geomLW_le hWc' xL _ u i)
        (monotone_index_geomRW hWc' (hxRi _) u) (fun j => le_geomRW hWc' xR _ u j) hsL hsR)
    have hE := hp (σ (p.1 : Ω) : ℝ≥0∞) le_rfl hcol
    refine PhaseSelFull.IsWordEntrance.congr_b hE fun t ht => ?_
    rw [hBeq p t (WithTop.coe_le_coe.2 (ENNReal.coe_le_coe.1 ht.le)), hjV]
    rfl
  have h2 := ae_of_ae_condSub (p := R) hA (ae_of_ae_prod_fst (p := fun ω : A => R ω) h1)
  filter_upwards [h2, hoff] with ω h3 h4
  by_cases hωA : ω ∈ A
  · exact hconv ω (h3 hωA)
  · exact hzero ω (h4 hωA)

end Mart

end InteractingSLE.Sec7.PocketMartLife
