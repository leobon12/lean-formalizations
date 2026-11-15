/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelAdaptPath
import InteractingSLE.Spec.Sec7.Lemma71BStop

/-!
# §7.4, Aux. lemma 122 before an announced lifetime: the random continuation

Packet PROVE-STRIPSYS6 (specification §7.4, Aux. lemma 122, `source/spec/p385-432.md` L104–L131, p. 389: "Consider a
continuous Loewner trace from zero in `ℍ`, with continuous driver and positive stopping lifetime `T` … At each
`0 < t < T`, the unvisited original boundary keeps this word … Then `d_t = 0` for every `0 < t < T`, almost surely").

Here the coordinates are only assumed nice **before** the lifetime `T` (continuous, force paths, ordered, merging,
separated, on `{t < T}`), the boundary description holds on `(0, T)`, the means are local martingales before
`min (swallowTime z) T` and continuous before `T`. Given an announcing sequence `σₙ < T` of finite stopping times
(`σₙ ↑ T`; Aux. lemma 125 supplies it for the pocket traversal: "`ζₙ = n ∧ inf{s < ζ : |X_C(s)| ≥ n}` … These are
genuine stopping times in the relative history and supply pre-lifetime localizations"), each `σₙ` is a lifetime for
`aux122_adapt` after continuing the coordinates past it (`PhaseSelAdaptPath`): the coupling means before `σₙ` do not see
the continuation.

## Main results

* `IsForcePathBefore`: a force path before a time `L`;
* `continuousWithinAt_of_continuousOn_Icc`: right-continuity of the means before `min (swallowTime z) T`;
* `isLocalMartingaleBefore_min_stop`: a right-continuous local martingale before `ζ` is one before `min ζ τ`;
* `measurable_stopped_value`, `stronglyAdapted_contW`, `stronglyAdapted_contV`;
* **`ae_phase_eq_zero_of_announcing`**: Aux. lemma 122's conclusion `d_t = 0` for every `0 < t < T`, almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSelAdapt

open MartChar PhaseSel PhaseSelFull Lemma71B

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **A force path before `L`**: `v` is continuous before `L`, has the Loewner derivative `2/(v − w)` at every
`0 < u < L` off the driver, and its collision set before `L` is null. -/
def IsForcePathBefore (w v : ℝ≥0 → ℝ) (L : WithTop ℝ≥0) : Prop :=
  ContinuousOn v {t | (t : WithTop ℝ≥0) < L} ∧
    (∀ u : ℝ, 0 < u → ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) < L → v u.toNNReal ≠ w u.toNNReal →
      HasDerivAt (fun r : ℝ => v r.toNNReal) (2 / (v u.toNNReal - w u.toNNReal)) u) ∧
    volume {u : ℝ | 0 ≤ u ∧ ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) < L ∧ v u.toNNReal = w u.toNNReal} = 0

/-! ### Local martingales stopped at a stopping time -/

/-- **A right-continuous local martingale before `ζ` is a local martingale before `min ζ τ`** for every stopping time
`τ` (optional stopping of the localized martingales). -/
theorem isLocalMartingaleBefore_min_stop [IsFiniteMeasure P] {ζ τ : Ω → WithTop ℝ≥0} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsLocalMartingaleBefore 𝓕 P ζ X)
    (hrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < ζ ω → ContinuousWithinAt (X · ω) (Ici s) s)
    (hτ : IsStoppingTime 𝓕 τ) : IsLocalMartingaleBefore 𝓕 P (fun ω => min (ζ ω) (τ ω)) X := by
  obtain ⟨σ, hσ, hσζ, hae, hmart⟩ := hX
  refine ⟨fun k ω => min (σ k ω) (τ ω), fun k => (hσ k).min hτ, fun k ω => min_le_min (hσζ k ω) le_rfl, ?_,
    fun k => ?_⟩
  · filter_upwards [hae] with ω hω r hr
    filter_upwards [hω r (lt_of_lt_of_le hr (min_le_left _ _))] with k hk
    exact lt_min hk (lt_of_lt_of_le hr (min_le_right _ _))
  · have h := Martingale.stoppedProcess_of_rightContinuous (hmart k) (continuousWithinAt_stoppedProcess (hσζ k) hrc)
      hτ
    rw [stoppedProcess_stoppedProcess] at h
    convert h using 2
    funext ω
    exact min_comm _ _

theorem isLocalMartingaleBefore_congr_life {ζ ζ' : Ω → WithTop ℝ≥0} {X : ℝ≥0 → Ω → ℝ} (h : ∀ ω, ζ ω = ζ' ω)
    (hX : IsLocalMartingaleBefore 𝓕 P ζ X) : IsLocalMartingaleBefore 𝓕 P ζ' X := by
  obtain rfl : ζ = ζ' := funext h
  exact hX

/-- **Right-continuity before `min (swallowTime z) T` from continuity on compact windows**: if the mean is continuous
on `[0, T']` whenever `T' < T` and `z` is not swallowed by `T'`, it is right-continuous before
`min (swallowTime z) T`. -/
theorem continuousWithinAt_of_continuousOn_Icc {w : ℝ → ℝ} {z : ℂ} (hz : z ∈ H) {L : WithTop ℝ≥0}
    {f : ℝ → ℝ} (hf : ∀ T' : ℝ, 0 ≤ T' → ((T'.toNNReal : ℝ≥0) : WithTop ℝ≥0) < L →
      z ∈ H \ QuantumZipper.fwdHull w T' → ContinuousOn f (Icc 0 T'))
    {s : ℝ≥0} (hs : (s : WithTop ℝ≥0) < min (QuantumZipper.swallowTime w z : WithTop ℝ≥0) L) :
    ContinuousWithinAt (fun t : ℝ≥0 => f t) (Ici s) s := by
  obtain ⟨r, hsr, hr⟩ := WithTop.lt_iff_exists_coe_btwn.1 hs
  have hsr' : s < r := WithTop.coe_lt_coe.1 hsr
  have hr1 : (r : WithTop ℝ≥0) < (QuantumZipper.swallowTime w z : WithTop ℝ≥0) := lt_of_lt_of_le hr (min_le_left _ _)
  have hr2 : (r : WithTop ℝ≥0) < L := lt_of_lt_of_le hr (min_le_right _ _)
  have hzK : z ∈ H \ QuantumZipper.fwdHull w r := by
    refine ⟨hz, fun hK => ?_⟩
    have h := hK.2
    rw [ENNReal.ofReal_coe_nnreal] at h
    exact absurd hr1 (not_lt.2 h)
  have hc := hf r r.coe_nonneg (by rwa [Real.toNNReal_coe]) hzK
  have hcw : ContinuousWithinAt f (Ici (s : ℝ)) s := by
    refine (hc (s : ℝ) ⟨s.coe_nonneg, hsr'.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_of_superset (Icc_mem_nhdsGE (by exact_mod_cast hsr')) fun x hx => ⟨s.coe_nonneg.trans hx.1, hx.2⟩
  exact hcw.comp NNReal.continuous_coe.continuousWithinAt fun x hx => by
    exact_mod_cast (mem_Ici.1 hx)

/-! ### Stopped values -/

/-- **The value of an adapted process at `t ∧ σ`** is `𝓕_t`-measurable when its paths are continuous on `[0, σ]`
(`Ito.measurable_stopped_of_agree`). -/
theorem measurable_stopped_value {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0))
    {X : ℝ≥0 → Ω → ℝ} (hXa : StronglyAdapted 𝓕 X) (hXc : ∀ ω, ContinuousOn (X · ω) (Iic (σ ω))) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => X (min t (σ ω)) ω := by
  have h := Ito.measurable_stopped_of_agree (𝓖 := 𝓕) (K := X) (X := X) hσ (fun s => (hXa s).measurable)
    (@MeasurableSet.univ Ω (𝓕 0)) 0 (fun _ _ _ _ => rfl) (fun ω _ => hXc ω) t
  simpa only [mem_univ, ↓reduceIte] using h

theorem measurable_min_coe {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => ((min t (σ ω) : ℝ≥0) : ℝ) :=
  measurable_stopped_value (X := fun s _ => (s : ℝ)) hσ (fun _ => stronglyMeasurable_const)
    (fun _ => NNReal.continuous_coe.continuousOn) t

theorem stronglyAdapted_contW {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0))
    {W : ℝ≥0 → Ω → ℝ} (hWa : StronglyAdapted 𝓕 W) (hWc : ∀ ω, ContinuousOn (W · ω) (Iic (σ ω))) :
    StronglyAdapted 𝓕 fun t ω => contW (W · ω) (σ ω) t := fun t =>
  (measurable_stopped_value hσ hWa hWc t).stronglyMeasurable

theorem stronglyAdapted_contV (e : ℝ) {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0))
    {W V : ℝ≥0 → Ω → ℝ} (hWa : StronglyAdapted 𝓕 W) (hVa : StronglyAdapted 𝓕 V)
    (hWc : ∀ ω, ContinuousOn (W · ω) (Iic (σ ω))) (hVc : ∀ ω, ContinuousOn (V · ω) (Iic (σ ω))) :
    StronglyAdapted 𝓕 fun t ω => contV e (W · ω) (V · ω) (σ ω) t := fun t => by
  have hW := measurable_stopped_value hσ hWa hWc t
  have hV := measurable_stopped_value hσ hVa hVc t
  have hm := measurable_min_coe hσ t
  refine Measurable.stronglyMeasurable ?_
  simp only [contV]
  exact hW.add (measurable_const.mul (((hV.sub hW).pow_const 2).add
    (measurable_const.mul (measurable_const.sub hm))).sqrt)

/-- **Non-swallowing transfers between drivers that agree up to `t`**, the second driver only agreeing with a
continuous one on a longer interval `[0, t₂]`: if `z` is not swallowed by `t` under `w₁`, and `w₁ = w₂`
on `[0, t]` with `w₂` continuous and `w₂ = w₃` on `[0, t₂]`, `t < t₂`, then `z` is not swallowed by `t` under `w₃`. -/
theorem notMem_fwdHull_of_eqOn {w₁ w₂ w₃ : ℝ → ℝ} (hw₂ : Continuous w₂) {t t₂ : ℝ}
    (ht : 0 ≤ t) (htt₂ : t < t₂) (h₁₂ : EqOn w₁ w₂ (Icc 0 t)) (h₂₃ : ∀ r ∈ Icc (0 : ℝ) t₂, w₂ r = w₃ r) {z : ℂ}
    (hz : z ∈ H \ QuantumZipper.fwdHull w₁ t) : z ∈ H \ QuantumZipper.fwdHull w₃ t := by
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht hz.1 hz.2
  have hu' := (Ito.isForwardSol_iff_of_eqOn h₁₂ u).1 hu
  have h2 := Ito.notMem_fwdHull_of_isForwardSol hw₂ hz.1 ht hu'
  rw [fwdHull_eq_of_eqOn ht htt₂ h₂₃] at h2
  exact ⟨hz.1, h2⟩

/-! ### Aux. lemma 122 before an announced lifetime -/

/-- **Aux. lemma 122 before an announced lifetime: the phase is zero** (specification p. 389, with the coordinates
only defined before the lifetime). Put `k > 4`, `A = k/2 − 2`; seed weights `r_L, r_R ∈ (−2, 2A − 2)`. Let the driver
and the force coordinates (seeds `0⁻, 0⁺` at index `0` started at `0`, other marks started strictly away from `0`) be
adapted, in a right-continuous filtration, and have the deterministic properties of geometric force images before a
lifetime `T` (continuity, force paths, ordering, monotonicity, index order, merging, separation on
`{t < T}`). Assume the exact boundary description on `(0, T)` with a common phase `d_t ∈ 2πχℤ` (no measurability
assumed), coupling means that are local martingales before swallowing and before `T`, continuous on every `[0, T']`,
`T' < T`, before swallowing (for every choice of the extensions before `T`). Given an announcing sequence of finite
stopping times `σₙ < T` exhausting `[0, T)` almost surely, almost surely `d_t = 0` for every `0 < t < T`. (`T` need not
be a stopping time and is positive because `σₙ < T`: only the `σₙ` enter the proof.) -/
theorem ae_phase_eq_zero_of_announcing [IsProbabilityMeasure P] [𝓕.IsRightContinuous] {k : ℝ} (hk : 4 < k)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
    (hseedL : ∀ ω, VL 0 0 ω = 0) (hseedR : ∀ ω, VR 0 0 ω = 0)
    (hxLd : ∀ ω (i : Fin nL), VL i.succ 0 ω < 0) (hxRd : ∀ ω (j : Fin nR), 0 < VR j.succ 0 ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    {T : Ω → WithTop ℝ≥0}
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hordL : ∀ ω (t : ℝ≥0) i, (t : WithTop ℝ≥0) < T ω → VL i t ω ≤ W t ω)
    (hordR : ∀ ω (t : ℝ≥0) i, (t : WithTop ℝ≥0) < T ω → W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePathBefore (W · ω) (VL i · ω) (T ω))
    (hpathR : ∀ ω i, IsForcePathBefore (W · ω) (VR i · ω) (T ω))
    (hantiL : ∀ ω i, AntitoneOn (VL i · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hmonoR : ∀ ω j, MonotoneOn (VR j · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hidxL : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Antitone fun i => VL i t ω)
    (hidxR : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j (s t : ℝ≥0), s ≤ t → (t : WithTop ℝ≥0) < T ω → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j (s t : ℝ≥0), s ≤ t → (t : WithTop ℝ≥0) < T ω → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω (t : ℝ≥0), 0 < t → (t : WithTop ℝ≥0) < T ω → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    {d : ℝ≥0 → Ω → ℝ}
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < T ω → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
        (fun t ω => couplingMean k (wpath W ω) t (U ω t) z))
    (hcont : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → ((T'.toNNReal : ℝ≥0) : WithTop ℝ≥0) < T ω →
        z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' →
        ContinuousOn (fun t : ℝ => couplingMean k (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T'))
    {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0))
    (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
    (hσlim : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < T ω → ∃ n, t ≤ σ n ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) < T ω → d t ω = 0 := by
  classical
  have hk0 : 0 < k := by linarith
  -- times up to `σ n` are before `T`
  have hlt : ∀ n ω (t : ℝ≥0), t ≤ σ n ω → (t : WithTop ℝ≥0) < T ω := fun n ω t ht =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 ht) (hσT n ω)
  have hIic : ∀ n ω, Iic (σ n ω) ⊆ {t : ℝ≥0 | (t : WithTop ℝ≥0) < T ω} := fun n ω t ht => hlt n ω t ht
  have hstep : ∀ n, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ σ n ω → d t ω = 0 := by
    intro n
    -- the continued coordinates
    set W' : ℝ≥0 → Ω → ℝ := fun t ω => contW (W · ω) (σ n ω) t with hW'
    set VL' : Fin (nL + 1) → ℝ≥0 → Ω → ℝ := fun i t ω => contV (-1) (W · ω) (VL i · ω) (σ n ω) t with hVL'
    set VR' : Fin (nR + 1) → ℝ≥0 → Ω → ℝ := fun j t ω => contV 1 (W · ω) (VR j · ω) (σ n ω) t with hVR'
    set d' : ℝ≥0 → Ω → ℝ := fun t ω => if t ≤ σ n ω then d t ω else 0 with hd'
    have hWcI : ∀ ω, ContinuousOn (W · ω) (Iic (σ n ω)) := fun ω => (hWc ω).mono (hIic n ω)
    have hVLcI : ∀ ω i, ContinuousOn (VL i · ω) (Iic (σ n ω)) := fun ω i => (hpathL ω i).1.mono (hIic n ω)
    have hVRcI : ∀ ω j, ContinuousOn (VR j · ω) (Iic (σ n ω)) := fun ω j => (hpathR ω j).1.mono (hIic n ω)
    -- the continued coordinates agree with the original ones up to `σ n`
    have hWeq : ∀ ω t, t ≤ σ n ω → W' t ω = W t ω := fun ω t ht => contW_of_le ht
    have hVLeq : ∀ ω i t, t ≤ σ n ω → VL' i t ω = VL i t ω := fun ω i t ht =>
      contV_left_of_le (hordL ω t i (hlt n ω t ht)) ht
    have hVReq : ∀ ω j t, t ≤ σ n ω → VR' j t ω = VR j t ω := fun ω j t ht =>
      contV_right_of_le (hordR ω t j (hlt n ω t ht)) ht
    have hdeq : ∀ ω t, t ≤ σ n ω → d' t ω = d t ω := fun ω t ht => by simp only [hd', ht, ↓reduceIte]
    have hpeq : ∀ ω (r : ℝ), 0 ≤ r → ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (σ n ω : WithTop ℝ≥0) →
        wpath W' ω r = wpath W ω r := fun ω r _ hr => hWeq ω _ (WithTop.coe_le_coe.1 hr)
    -- extensions of the continued data give extensions of the original data
    set U₀ : Ω → ℝ≥0 → ℂ → ℝ := fun ω t ξ => meanExt k (shiftL k ρL (d t ω)) (shiftR k ρR (d t ω)) (W t ω)
      (fun i => VL i t ω) (fun j => VR j t ω) ξ + d t ω with hU₀def
    have hU₀ : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U₀ ω t) := fun ω t ht =>
      isBoundedHarmonicExtension_unshift hk0 (sub_nonpos.2 (hordL ω t 0 ht))
        (sub_nonneg.2 (hordR ω t 0 ht)) (isBoundedHarmonicExtension_meanExt k _ _ (W t ω) _ _)
    -- the continued hypotheses of `aux122_adapt`
    have hz0 : ∀ ω, (0 : ℝ≥0) ≤ σ n ω := fun ω => zero_le
    have hseedL' : ∀ ω, VL' 0 0 ω = 0 := fun ω => by rw [hVLeq ω 0 0 (hz0 ω), hseedL]
    have hseedR' : ∀ ω, VR' 0 0 ω = 0 := fun ω => by rw [hVReq ω 0 0 (hz0 ω), hseedR]
    have hxLd' : ∀ ω (i : Fin nL), VL' i.succ 0 ω < 0 := fun ω i => by
      rw [hVLeq ω _ 0 (hz0 ω)]; exact hxLd ω i
    have hxRd' : ∀ ω (j : Fin nR), 0 < VR' j.succ 0 ω := fun ω j => by
      rw [hVReq ω _ 0 (hz0 ω)]; exact hxRd ω j
    have hW0' : ∀ ω, W' 0 ω = 0 := fun ω => by rw [hWeq ω 0 (hz0 ω), hW0]
    have hWc' : ∀ ω, Continuous fun t => W' t ω := fun ω => continuous_contW (hWcI ω)
    have hWa' : StronglyAdapted 𝓕 W' := stronglyAdapted_contW (hσ n) hWa hWcI
    have hVLa' : ∀ i, StronglyAdapted 𝓕 (VL' i) := fun i =>
      stronglyAdapted_contV (-1) (hσ n) hWa (hVLa i) hWcI fun ω => hVLcI ω i
    have hVRa' : ∀ j, StronglyAdapted 𝓕 (VR' j) := fun j =>
      stronglyAdapted_contV 1 (hσ n) hWa (hVRa j) hWcI fun ω => hVRcI ω j
    have hordL' : ∀ ω t i, VL' i t ω ≤ W' t ω := fun ω t i => contV_left_le_contW t
    have hordR' : ∀ ω t i, W' t ω ≤ VR' i t ω := fun ω t i => contW_le_contV_right t
    have hpathL' : ∀ ω i, IsForcePath (fun t => W' t ω) (fun t => VL' i t ω) := fun ω i =>
      isForcePath_contV_left (hWcI ω) (hVLcI ω i) (fun t ht => hordL ω t i (hlt n ω t ht))
        ((hantiL ω i).mono (hIic n ω))
        (fun u hu hus hne => (hpathL ω i).2.1 u hu (hlt n ω _ (Real.toNNReal_le_iff_le_coe.2 hus)) hne)
        (by
          refine measure_mono_null (fun u hu => ?_) (hpathL ω i).2.2
          exact ⟨hu.1, hlt n ω _ (Real.toNNReal_le_iff_le_coe.2 hu.2.1), hu.2.2⟩)
    have hpathR' : ∀ ω j, IsForcePath (fun t => W' t ω) (fun t => VR' j t ω) := fun ω j =>
      isForcePath_contV_right (hWcI ω) (hVRcI ω j) (fun t ht => hordR ω t j (hlt n ω t ht))
        ((hmonoR ω j).mono (hIic n ω))
        (fun u hu hus hne => (hpathR ω j).2.1 u hu (hlt n ω _ (Real.toNNReal_le_iff_le_coe.2 hus)) hne)
        (by
          refine measure_mono_null (fun u hu => ?_) (hpathR ω j).2.2
          exact ⟨hu.1, hlt n ω _ (Real.toNNReal_le_iff_le_coe.2 hu.2.1), hu.2.2⟩)
    have hantiL' : ∀ ω i, Antitone fun t => VL' i t ω := fun ω i =>
      antitone_contV_left (fun t ht => hordL ω t i (hlt n ω t ht)) ((hantiL ω i).mono (hIic n ω))
    have hmonoR' : ∀ ω j, Monotone fun t => VR' j t ω := fun ω j =>
      monotone_contV_right (fun t ht => hordR ω t j (hlt n ω t ht)) ((hmonoR ω j).mono (hIic n ω))
    have hidxL' : ∀ ω t, Antitone fun i => VL' i t ω := fun ω t i j hij =>
      contV_left_le (fun t ht => hordL ω t i (hlt n ω t ht)) (fun t ht => hidxL ω t (hlt n ω t ht) hij) t
    have hidxR' : ∀ ω t, Monotone fun j => VR' j t ω := fun ω t i j hij =>
      contV_right_le (fun t ht => hordR ω t i (hlt n ω t ht)) (fun t ht => hidxR ω t (hlt n ω t ht) hij) t
    have hmergeL' : ∀ ω i j s t, s ≤ t → VL' i s ω = VL' j s ω → VL' i t ω = VL' j t ω :=
      fun ω i j s t hst h => contV_eq_of_eq (Or.inr rfl)
        (by have := hordL ω (σ n ω) i (hσT n ω); linarith) (by have := hordL ω (σ n ω) j (hσT n ω); linarith)
        (fun t ht => ⟨hVLeq ω i t ht, hVLeq ω j t ht⟩)
        (fun t₀ t h1 h2 h3 => hmergeL ω i j t₀ t h1 (hlt n ω t h2) h3) hst h
    have hmergeR' : ∀ ω i j s t, s ≤ t → VR' i s ω = VR' j s ω → VR' i t ω = VR' j t ω :=
      fun ω i j s t hst h => contV_eq_of_eq (Or.inl rfl)
        (by have := hordR ω (σ n ω) i (hσT n ω); linarith) (by have := hordR ω (σ n ω) j (hσT n ω); linarith)
        (fun t ht => ⟨hVReq ω i t ht, hVReq ω j t ht⟩)
        (fun t₀ t h1 h2 h3 => hmergeR ω i j t₀ t h1 (hlt n ω t h2) h3) hst h
    have hsep' : ∀ ω t, 0 < t → ∀ i j, VL' i t ω = W' t ω → VR' j t ω ≠ W' t ω := by
      intro ω t ht i j hL
      by_cases hts : t ≤ σ n ω
      · rw [hVLeq ω i t hts, hWeq ω t hts] at hL
        rw [hVReq ω j t hts, hWeq ω t hts]
        exact hsep ω t ht (hlt n ω t hts) i j hL
      · exact contV_ne_contW one_ne_zero (lt_of_not_ge hts)
    have hd' : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) ≤ (σ n ω : WithTop ℝ≥0) →
        ∃ m : ℤ, d' t ω = m * phaseStep k := fun t ω ht hts => by
      have hts' : t ≤ σ n ω := WithTop.coe_le_coe.1 hts
      rw [hdeq ω t hts']
      exact hd t ω ht (hlt n ω t hts')
    -- an extension of the continued data gives one of the original data before `T`
    have hU : ∀ U' : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL' i t ω - W' t ω) (fun j => VR' j t ω - W' t ω) (d' t ω))
        (forceJumpSet (fun i => VL' i t ω - W' t ω) (fun j => VR' j t ω - W' t ω)) (U' ω t)) →
        ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → IsBoundedHarmonicExtension
          (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
          (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
          (if t ≤ σ n ω then U' ω t else U₀ ω t) := by
      intro U' hU' ω t ht
      by_cases hts : t ≤ σ n ω
      · simp only [hts, ↓reduceIte]
        have e1 : (fun i => VL' i t ω - W' t ω) = fun i => VL i t ω - W t ω :=
          funext fun i => by rw [hVLeq ω i t hts, hWeq ω t hts]
        have e2 : (fun j => VR' j t ω - W' t ω) = fun j => VR j t ω - W t ω :=
          funext fun j => by rw [hVReq ω j t hts, hWeq ω t hts]
        have h := hU' ω t
        rw [e1, e2, hdeq ω t hts] at h
        exact h
      · simp only [hts, ↓reduceIte]
        exact hU₀ ω t ht
    have hagree : ∀ ω (t : ℝ), 0 ≤ t → t.toNNReal ≤ σ n ω → EqOn (wpath W' ω) (wpath W ω) (Icc 0 t) :=
      fun ω t _ hts r hr => hpeq ω r hr.1
        (WithTop.coe_le_coe.2 ((Real.toNNReal_le_toNNReal hr.2).trans hts))
    have hmart' : ∀ U' : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL' i t ω - W' t ω) (fun j => VR' j t ω - W' t ω) (d' t ω))
        (forceJumpSet (fun i => VL' i t ω - W' t ω) (fun j => VR' j t ω - W' t ω)) (U' ω t)) →
        ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
          (fun ω => min (QuantumZipper.swallowTime (wpath W' ω) z : WithTop ℝ≥0) (σ n ω))
          (fun t ω => couplingMean k (wpath W' ω) t (U' ω t) z) := by
      intro U' hU' z hz
      set U : Ω → ℝ≥0 → ℂ → ℝ := fun ω t => if t ≤ σ n ω then U' ω t else U₀ ω t with hUdef
      have h1 := hmart U (hU U' hU') z hz
      have hrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) <
          min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω) →
          ContinuousWithinAt (fun t : ℝ≥0 => couplingMean k (wpath W ω) t (U ω t) z) (Ici s) s := fun ω s hs => by
        have h := continuousWithinAt_of_continuousOn_Icc hz
          (f := fun t : ℝ => couplingMean k (wpath W ω) t (U ω t.toNNReal) z)
          (fun T' h0 hT' hzK => hcont U (hU U' hU') ω z T' h0 hT' hzK) hs
        simpa only [Real.toNNReal_coe] using h
      have h2 := isLocalMartingaleBefore_min_stop h1 hrc (hσ n)
      have hζ : (fun ω => min (min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
          (σ n ω : WithTop ℝ≥0)) =
          fun ω => min (QuantumZipper.swallowTime (wpath W' ω) z : WithTop ℝ≥0) (σ n ω) := funext fun ω => by
        calc _ = min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (min (T ω) (σ n ω : WithTop ℝ≥0)) :=
              min_assoc _ _ _
          _ = min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (σ n ω : WithTop ℝ≥0) :=
              congrArg (min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
                (min_eq_right (hσT n ω).le)
          _ = _ := min_swallowTime_congr (fun r hr hrs => (hpeq ω r hr hrs).symm) hz
      have h3 : IsLocalMartingaleBefore 𝓕 P
          (fun ω => min (QuantumZipper.swallowTime (wpath W' ω) z : WithTop ℝ≥0) (σ n ω))
          (fun t ω => couplingMean k (wpath W ω) t (U ω t) z) := by
        exact isLocalMartingaleBefore_congr_life (fun ω => congrFun hζ ω) h2
      refine isLocalMartingaleBefore_sub_const_before 0 h3 fun t ω ht => ?_
      have hts : t ≤ σ n ω := WithTop.coe_le_coe.1 (ht.trans (min_le_right _ _))
      rw [sub_zero]
      simp only [hUdef, hts, ↓reduceIte]
      exact couplingMean_congr t.coe_nonneg (hagree ω t t.coe_nonneg (by rwa [Real.toNNReal_coe])) k _ z
    have hcont' : ∀ U' : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL' i t ω - W' t ω) (fun j => VR' j t ω - W' t ω) (d' t ω))
        (forceJumpSet (fun i => VL' i t ω - W' t ω) (fun j => VR' j t ω - W' t ω)) (U' ω t)) →
        ∀ ω (z : ℂ) (T'' : ℝ), 0 ≤ T'' → ((T''.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (σ n ω : WithTop ℝ≥0) →
          z ∈ H \ QuantumZipper.fwdHull (wpath W' ω) T'' →
          ContinuousOn (fun t : ℝ => couplingMean k (wpath W' ω) t (U' ω t.toNNReal) z) (Icc 0 T'') := by
      intro U' hU' ω z T'' h0 hT'' hzK
      have hT''σ : T''.toNNReal ≤ σ n ω := WithTop.coe_le_coe.1 hT''
      have hT''σ' : T'' ≤ σ n ω := by
        have := (Real.toNNReal_le_iff_le_coe).1 hT''σ; exact this
      -- a time strictly between `σ n` and `T`
      obtain ⟨r, hσr, hrT⟩ := WithTop.lt_iff_exists_coe_btwn.1 (hσT n ω)
      have hσr' : σ n ω < r := WithTop.coe_lt_coe.1 hσr
      have hWr : ContinuousOn (W · ω) (Iic r) := (hWc ω).mono fun t ht =>
        lt_of_le_of_lt (WithTop.coe_le_coe.2 ht) hrT
      have hzK' : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T'' := by
        refine notMem_fwdHull_of_eqOn (w₂ := fun x : ℝ => contW (W · ω) r x.toNNReal)
          ((continuous_contW hWr).comp continuous_real_toNNReal) h0
          (lt_of_le_of_lt hT''σ' (by exact_mod_cast hσr')) ?_ ?_ hzK
        · intro x hx
          have hx' : x.toNNReal ≤ σ n ω := (Real.toNNReal_le_toNNReal hx.2).trans hT''σ
          show contW (W · ω) (σ n ω) x.toNNReal = contW (W · ω) r x.toNNReal
          rw [contW_of_le hx', contW_of_le (hx'.trans hσr'.le)]
        · intro x hx
          show contW (W · ω) r x.toNNReal = W x.toNNReal ω
          exact contW_of_le (Real.toNNReal_le_iff_le_coe.2 hx.2)
      have hc := hcont U' |> fun _ => hcont (fun ω t => if t ≤ σ n ω then U' ω t else U₀ ω t) (hU U' hU') ω z
        T'' h0 (lt_of_le_of_lt hT'' (hσT n ω)) hzK'
      refine hc.congr fun t ht => ?_
      have hts : t.toNNReal ≤ σ n ω := (Real.toNNReal_le_toNNReal ht.2).trans hT''σ
      simp only [hts, ↓reduceIte]
      exact couplingMean_congr ht.1 (hagree ω t ht.1 hts) k _ z
    have h := ae_phase_eq_zero_adapt (P := P) (𝓕 := 𝓕) hk hrL hrL' hrR hrR' hseedL' hseedR' hxLd' hxRd' hW0'
      hWc' hWa' hVLa' hVRa' hordL' hordR' hpathL' hpathR' hantiL' hmonoR' hidxL' hidxR' hmergeL' hmergeR' hsep'
      (hσ n) hd' hmart' hcont'
    filter_upwards [h] with ω hω t ht hts
    rw [← hdeq ω t hts]
    exact hω t ht (WithTop.coe_le_coe.2 hts)
  filter_upwards [ae_all_iff.2 hstep, hσlim] with ω hω hlim t ht htT
  obtain ⟨n, hn⟩ := hlim t htT
  exact hω n t ht hn

end PhaseSelAdapt

end Sec7

end InteractingSLE
