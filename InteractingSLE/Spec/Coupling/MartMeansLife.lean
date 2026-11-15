/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.MartMeans

/-!
# Martingale means for a coupling with a lifetime (the frozen optional hull specification)

Packet PROVE-CPL-MART. `MartMeans` treats a global driver whose path properties hold for every `ω`. The driving
evolution of the frozen `IsOptionalHullCoupling` lives up to a lifetime `ζ`, its path properties hold only almost
surely, and the conditional-law clause is only available at stopping times `τ < ζ`. Here the localization is the same
(the hull reaching the ball `B̄(z, Im z/(n+2))`), additionally kept below an announcing sequence `T_n < ζ` of the
lifetime, and the conclusion is in the form of `TestMean`: for every `z ∈ ℍ`, there are stopping times
`σ_n < ζ ∧ s(z)` (almost surely) exhausting `ζ ∧ s(z)`, such that the stopped coupling mean `𝔥_{t∧σ_n}(z)` agrees almost
surely, at every time, with a martingale (`exists_martingale_stoppedProcess_meanProc`).

* `locTimeL z n T ζ w`: the safe exit time of the localizing ball below the horizon `T` and the lifetime `ζ`;
  `isSafeAt_locTimeL`, `locTimeL_le_swallowTime`, `eventually_lt_locTimeL` (exhaustion);
* `isStoppingTime_locStopL`: on a good event `G ∈ 𝓖₀` (and `0` off it), a stopping time;
* **`exists_martingale_stoppedProcess_meanProc`**: the generic statement;
* **`IsOptionalHullCoupling.exists_martingale_stoppedProcess_meanProc`**: for the frozen specification, given an
  announcing sequence of the lifetime in the driving filtration (conditional helper: such a sequence is constructed in
  `AnnounceLifetime` only for the evolution's own filtration).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Complex Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

namespace MartMeans

open Ito

variable {nL nR : ℕ}

/-! ### Localizing times below a lifetime -/

section Loc

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {z : ℂ}

/-- **The `n`-th localizing time of `z` below the horizon `T` and the lifetime `ζ`**: the safe exit time of the ball
`B̄(z, Im z/(n+2))` at level `(Im z/2)/(n+1)`. -/
def locTimeL (z : ℂ) (n : ℕ) (T : ℝ≥0) (ζ : ℝ≥0∞) (w : ℝ≥0 → ℝ) : ℝ≥0 :=
  safeExitTime (closedBall z (locRad z n)) (locLevel z n) n T ζ w

theorem isSafeAt_locTimeL (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hz : 0 < z.im)
    (n : ℕ) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) :
    IsSafeAt (closedBall z (locRad z n)) (locLevel z n) n T ζ w (locTimeL z n T ζ w) :=
  isSafeAt_safeExitTime hw (closedBall_locRad_subset hz n) (locLevel_pos hz n) hT
    (isSafeAt_zero (closedBall_locRad_subset hz n)
      (fun _ hy => (locLevel_le hz n).trans (half_le_im_of_mem_closedBall_locRad hz hy)) hw0
      (pos_of_gt hT) n.cast_nonneg)

theorem locTimeL_le_swallowTime (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hz : 0 < z.im) (n : ℕ) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) :
    ((locTimeL z n T ζ w : ℝ≥0) : ℝ≥0∞) ≤ swallowTime (rpath w) z := by
  obtain ⟨u, hu⟩ := ((isSafeAt_locTimeL hw hw0 hz n hT).2.2.2 z
    (mem_closedBall_self (locRad_pos hz n).le)).1
  exact le_sSup ⟨_, ⟨(locTimeL z n T ζ w).coe_nonneg, u, hu⟩, ENNReal.ofReal_coe_nnreal⟩

/-- **Exhaustion below a lifetime**: if the horizons `T n` are nondecreasing and exhaust `[0, ζ)`, every time before
`ζ` and before the swallowing time of `z` lies below all large localizing times. -/
theorem eventually_lt_locTimeL (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hz : 0 < z.im)
    {T : ℕ → ℝ≥0} (hTm : Monotone T) (hTex : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∃ n, t ≤ T n) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < swallowTime (rpath w) z) (hrζ : (r : ℝ≥0∞) < ζ) :
    ∀ᶠ n in atTop, r < locTimeL z n (T n) ζ w := by
  obtain ⟨x, ⟨T₀, ⟨hT0, u, hu⟩, rfl⟩, hrx⟩ := lt_sSup_iff.1 hr
  have hrT : (r : ℝ) < T₀ := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg] at hrx
    exact hrx
  obtain ⟨a, hra, haζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hrζ
  set b : ℝ≥0 := ⟨((r : ℝ) + T₀) / 2, by have := r.coe_nonneg; linarith⟩ with hb
  have hrb : r < b := by
    rw [← NNReal.coe_lt_coe]; show (r : ℝ) < ((r : ℝ) + T₀) / 2; linarith
  have hbT : (b : ℝ) < T₀ := by show ((r : ℝ) + T₀) / 2 < T₀; linarith
  set t' : ℝ≥0 := min a b with ht'
  have hrt' : r < t' := lt_min (by exact_mod_cast hra) hrb
  have ht'ζ : (t' : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast min_le_left a b) haζ
  have ht'T : (t' : ℝ) ≤ T₀ := (show (t' : ℝ) ≤ b from by exact_mod_cast min_le_right a b).trans hbT.le
  -- a continuous clamped driver beyond `t'`
  obtain ⟨T', ht'T', hT'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht'ζ
  have ht'T'r : (t' : ℝ) ≤ T' := by exact_mod_cast (le_of_lt (by exact_mod_cast ht'T'))
  have hWc : Continuous (clampDrv (rpath w) T') :=
    continuous_clampDrv T'.coe_nonneg (continuousOn_rpath hw hT'ζ)
  have heq : EqOn (clampDrv (rpath w) T') (rpath w) (Icc 0 (t' : ℝ)) := fun s hs =>
    clampDrv_eqOn ⟨hs.1, hs.2.trans ht'T'r⟩
  have hzt' : z ∈ H \ fwdHull (clampDrv (rpath w) T') t' := by
    refine ⟨hz, notMem_fwdHull_of_isForwardSol hWc hz t'.coe_nonneg (u := u) ?_⟩
    exact (isForwardSol_iff_of_eqOn heq u).2 (isForwardSol_of_le hu t'.coe_nonneg ht'T)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (FwdHolo.isOpen_compl_fwdHull hWc t'.coe_nonneg) z hzt'
  set ε₁ := min (ε / 2) (z.im / 2) with hε₁
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hKball : closedBall z ε₁ ⊆ ball z ε :=
    closedBall_subset_ball ((min_le_left _ _).trans_lt (by linarith))
  have hKH : closedBall z ε₁ ⊆ H := fun y hy => (hball (hKball hy)).1
  have halive : ∀ y ∈ closedBall z ε₁, ∃ u, IsForwardSol (rpath w) y t' u := fun y hy => by
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_mem t'.coe_nonneg (hball (hKball hy))
    exact ⟨v, (isForwardSol_iff_of_eqOn heq v).1 hv⟩
  obtain ⟨j, hj⟩ := hTex t' ht'ζ
  have hev := eventually_le_safeExitTime hw (isCompact_closedBall z ε₁) hKH (z.im / 2) hj ht'ζ halive
  have hrad : ∀ᶠ n : ℕ in atTop, locRad z n ≤ ε₁ := by
    have h0 : Tendsto (fun n : ℕ => locRad z n) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
      simpa [locRad] using this.const_div_atTop z.im
    exact h0.eventually (ge_mem_nhds hε₁)
  filter_upwards [hev, hrad, eventually_ge_atTop j] with n h1 h2 h3
  calc r < t' := hrt'
    _ ≤ safeExitTime (closedBall z ε₁) (z.im / 2 / ((n : ℝ) + 1)) n (T j) ζ w := h1
    _ ≤ safeExitTime (closedBall z ε₁) (z.im / 2 / ((n : ℝ) + 1)) n (T n) ζ w :=
        safeExitTime_mono le_rfl le_rfl (hTm h3)
    _ ≤ locTimeL z n (T n) ζ w := safeExitTime_anti_set (closedBall_subset_closedBall h2)

end Loc

/-! ### The localizing stopping times on a good event -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- The `n`-th localizing stopping time of `z` below the announcing time `T n` and the lifetime, on the good event
`G` (and `0` off it). -/
def locStopL (z : ℂ) (n : ℕ) (T : ℕ → Ω → ℝ≥0) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) :
    Ω → WithTop ℝ≥0 :=
  open Classical in
  fun ω => ((if ω ∈ G then locTimeL z n (T n ω) (ζ ω) (W · ω) else 0 : ℝ≥0) : WithTop ℝ≥0)

theorem locStopL_of_mem {z : ℂ} {n : ℕ} {T : ℕ → Ω → ℝ≥0} {ω : Ω} (hω : ω ∈ G) :
    locStopL z n T ζ G W ω = ((locTimeL z n (T n ω) (ζ ω) (W · ω) : ℝ≥0) : WithTop ℝ≥0) := by
  unfold locStopL
  simp only [hω, ↓reduceIte]

/-- **The localizing times are stopping times** of a right-continuous filtration in which the driver is adapted
before the lifetime, given a good event `G ∈ 𝓖₀` of continuous paths and stopping times `T n`. -/
theorem isStoppingTime_locStopL [𝓖.IsRightContinuous] (hWa : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : ∀ t, MeasurableSet[𝓖 t] G) {T : ℕ → Ω → ℝ≥0} {n : ℕ}
    (hT : IsStoppingTime 𝓖 fun ω => (T n ω : WithTop ℝ≥0)) {z : ℂ} (hz : 0 < z.im) :
    IsStoppingTime 𝓖 (locStopL z n T ζ G W) := by
  classical
  set K := closedBall z (locRad z n) with hK
  have hKH : K ⊆ H := closedBall_locRad_subset hz n
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hδ := locLevel_pos hz n
  have hiff : ∀ ω ∈ G, ∀ d, IsSafeAt K (locLevel z n) n (T n ω) (ζ ω) (W · ω) d ↔
      IsSafeAt D (locLevel z n) n (T n ω) (ζ ω) (W · ω) d := fun ω hω d =>
    ⟨fun h => h.subset hDK, fun h => h.of_dense (hGc ω hω) hKH hKD hDK hδ⟩
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
  have heq : {ω | locStopL z n T ζ G W ω < (t : WithTop ℝ≥0)} =
      (⋃ d ∈ Q ∩ Iio t, G \ {ω | ω ∈ G ∧ IsSafeAt D (locLevel z n) n (T n ω) (ζ ω) (W · ω) d}) ∪
        (Gᶜ ∩ {_ω | (0 : ℝ≥0) < t}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [locStopL, hω, ↓reduceIte, mem_ofPred_eq, WithTop.coe_lt_coe, mem_union, mem_iUnion,
        mem_inter_iff, Set.mem_sdiff, mem_Iio, exists_prop, true_and, mem_compl_iff, not_true_eq_false,
        false_and, or_false]
      rw [locTimeL, safeExitTime_lt_iff (hGc ω hω) hKH hQd]
      constructor
      · rintro ⟨d, hd, hdt, hnp⟩; exact ⟨d, ⟨hd, hdt⟩, fun h => hnp ((hiff ω hω d).2 h)⟩
      · rintro ⟨d, ⟨hd, hdt⟩, hnp⟩; exact ⟨d, hd, hdt, fun h => hnp ((hiff ω hω d).1 h)⟩
    · simp only [locStopL, hω, ↓reduceIte, mem_ofPred_eq, WithTop.coe_lt_coe, mem_union, mem_iUnion,
        mem_inter_iff, Set.mem_sdiff, false_and, exists_false, false_or, mem_compl_iff,
        not_false_eq_true, true_and]
  rw [heq]
  refine MeasurableSet.union (MeasurableSet.biUnion (hQc.mono inter_subset_left) fun d hd => ?_)
    ((hG t).compl.inter (MeasurableSet.const _))
  exact 𝓖.mono hd.2.le _ ((hG d).diff (measurableSet_isSafeAt hWa hGc (hG 0) hDc (hDK.trans hKH) hT
    _ _ d))

end Random

/-! ### Martingale means below the lifetime -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

theorem stoppedProcess_apply_of_eq {X : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {ω : Ω} {s : ℝ≥0}
    (hσ : σ ω = (s : WithTop ℝ≥0)) (t : ℝ≥0) : stoppedProcess X σ t ω = X (min t s) ω := by
  simp only [stoppedProcess, hσ, ← WithTop.coe_min]
  rfl

/-- **The coupling means are martingales up to the localizing times, below the lifetime.** Let `𝓖` be a
right-continuous filtration containing the `P`-null sets, in which the driver `W` is adapted before the lifetime `ζ`,
let the lifetime have an announcing sequence `T` in `𝓖`, and suppose that almost surely `W₀ = 0`, `W` is continuous on
`[0, ζ)` and `V^L ≤ W ≤ V^R` there. If the random distribution `h` has integrable pairings and satisfies the
conditional-law clause (`IsCouplingCharFun` with lifetime `ζ`), then for every choice `u` of the bounded harmonic
extensions and every `z ∈ ℍ` there are stopping times `σ_n`, almost surely below `ζ` and the swallowing time `s(z)` and
exhausting `[0, ζ ∧ s(z))`, such that each stopped coupling mean `t ↦ 𝔥_{t∧σ_n}(z)` agrees almost surely, at every
time, with a martingale. -/
theorem exists_martingale_stoppedProcess_meanProc [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (hWa : AdaptedBefore 𝓖 ζ W)
    (hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω ≤ W t ω) ∧ ∀ i, W t ω ≤ VR i t ω)
    {T : ℕ → Ω → ℝ≥0} (hT : IsAnnouncingSeq 𝓖 P ζ T)
    (hint : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t))
    {z : ℂ} (hz : z ∈ H) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime 𝓖 (σ n)) ∧
      (∀ n, ∀ᵐ ω ∂P, (σ n ω : ℝ≥0∞) < ζ ω ∧
        (σ n ω : ℝ≥0∞) ≤ QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z) ∧
      (∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω →
        (r : ℝ≥0∞) < QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z →
        ∀ᶠ n in atTop, (r : WithTop ℝ≥0) < σ n ω) ∧
      ∀ n, ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 P ∧
        ∀ t, stoppedProcess (meanProc κ W u z) (σ n) t =ᵐ[P] M t := by
  have hz' : 0 < z.im := hz
  -- the good event
  set good : Ω → Prop := fun ω => (W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω ≤ W t ω) ∧ ∀ i, W t ω ≤ VR i t ω) ∧
    (∀ n, (T n ω : ℝ≥0∞) < ζ ω) ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, ae_all_iff.2 hT.2.2.1, hT.2.2.2] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  have hG0 : MeasurableSet[𝓖 0] G := by
    have := (hnull _ hGm.compl hGc).compl
    rwa [compl_compl] at this
  have hG : ∀ t, MeasurableSet[𝓖 t] G := fun t => 𝓖.mono bot_le _ hG0
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hwc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGgood ω hω).1.2.1
  have hσ : ∀ n, IsStoppingTime 𝓖 (locStopL z n T ζ G W) := fun n =>
    isStoppingTime_locStopL hWa hwc hG (hT.1 n) hz'
  refine ⟨fun n => locStopL z n T ζ G W, hσ, fun n => ?_, ?_, fun n => ?_⟩
  · filter_upwards [hGae] with ω hω
    obtain ⟨⟨hw0, hwc', -⟩, hTζ, -⟩ := hGgood ω hω
    rw [locStopL_of_mem hω]
    exact ⟨(isSafeAt_locTimeL hwc' hw0 hz' n (hTζ n)).1,
      locTimeL_le_swallowTime hwc' hw0 hz' n (hTζ n)⟩
  · filter_upwards [hGae] with ω hω r hrζ hr
    obtain ⟨⟨-, hwc', -⟩, -, hTex⟩ := hGgood ω hω
    refine (eventually_lt_locTimeL hwc' hz' (hT.2.1 ω) hTex hr hrζ).mono fun n hn => ?_
    rw [locStopL_of_mem hω]
    exact WithTop.coe_lt_coe.2 hn
  -- the martingale: conditional means of the normalized bump pairing at `σ_n ∧ t`
  set φ := bumpTestAt z hz' n with hφ
  refine ⟨fun t => P[fun ω => h ω φ / bumpNorm z n | ((hσ n).min_const t).measurableSpace],
    martingale_of_ae_eq_condExp_min_const (hσ n) ((hint _).div_const _)
      (fun t => stronglyMeasurable_condExp.mono
        (((hσ n).min_const t).measurableSpace_le_of_le_const fun ω => min_le_right _ _))
      (fun t => EventuallyEq.rfl), fun t => ?_⟩
  set τ : Ω → WithTop ℝ≥0 := fun ω => min (locStopL z n T ζ G W ω) (t : WithTop ℝ≥0) with hτ
  have hτu : ∀ ω ∈ G, (τ ω).untopD 0 = min (locTimeL z n (T n ω) (ζ ω) (W · ω)) t := fun ω hω => by
    rw [hτ]
    dsimp only
    rw [locStopL_of_mem hω, ← WithTop.coe_min, WithTop.untopD_coe]
  have hsafe : ∀ ω ∈ G, IsSafeAt (closedBall z (locRad z n)) (locLevel z n) n (T n ω) (ζ ω) (W · ω)
      (locTimeL z n (T n ω) (ζ ω) (W · ω)) := fun ω hω =>
    isSafeAt_locTimeL (hGgood ω hω).1.2.1 (hGgood ω hω).1.1 hz' n ((hGgood ω hω).2.1 n)
  have hlt : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hGae] with ω hω
    have h1 : (τ ω : ℝ≥0∞) ≤ (locTimeL z n (T n ω) (ζ ω) (W · ω) : ℝ≥0∞) := by
      have : τ ω ≤ locStopL z n T ζ G W ω := min_le_left _ _
      rw [locStopL_of_mem hω] at this
      exact this
    exact lt_of_le_of_lt h1 (hsafe ω hω).1
  have key : ∀ c : ℝ, P[fun ω => cexp (I * ((c * h ω φ : ℝ) : ℂ)) |
      ((hσ n).min_const t).measurableSpace] =ᵐ[P] fun ω => cexp (I * ((c *
        (∫ y, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
          (u ω ((τ ω).untopD 0)) y * GFF.bumpFun z (bumpRadius z n) y) : ℝ) : ℂ) -
        (((1 / 2) * (c ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
          ((τ ω).untopD 0 : ℝ≥0) (GFF.bumpFun z (bumpRadius z n))) : ℝ) : ℂ)) := by
    intro c
    have hcl := hcf τ ((hσ n).min_const t) hlt (fun ω => u ω ((τ ω).untopD 0)) (fun ω => hu ω _)
      (c • φ)
    have e1 : (fun ω' => cexp (I * ((h ω' (c • φ) : ℝ) : ℂ))) =
        fun ω' => cexp (I * ((c * h ω' φ : ℝ) : ℂ)) := by
      funext ω'; simp
    rw [e1] at hcl
    filter_upwards [hcl, hGae] with ω hω hωG
    have hcoe : (⇑(c • φ) : ℂ → ℝ) = c • GFF.bumpFun z (bumpRadius z n) := by
      funext y; simp [hφ, coe_bumpTestAt]
    have hdisj : Disjoint (tsupport ⇑(c • φ))
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
      rw [hτu ω hωG]
      refine Disjoint.mono_left ?_ (disjoint_locBall_fwdHull_of_safe (hGgood ω hωG).1.2.1 hz' n
        (hsafe ω hωG) (min_le_left _ _))
      rw [hcoe]
      exact (tsupport_smul_subset_right (fun _ : ℂ => c) (GFF.bumpFun z (bumpRadius z n))).trans
        (tsupport_bumpFun_subset_locBall hz' n)
    rw [hω hdisj, hcoe, integral_mul_smul, loewnerGreenEnergy_smul]
  have hA := condExp_ae_eq_of_condCharFun (hint φ) key
  have hs := condExp_smul (μ := P) (bumpNorm z n)⁻¹ (fun ω => h ω φ)
    ((hσ n).min_const t).measurableSpace
  have e2 : (fun ω => h ω φ / bumpNorm z n) = (bumpNorm z n)⁻¹ • fun ω => h ω φ := by
    funext ω; simp [div_eq_inv_mul]
  show stoppedProcess (meanProc κ W u z) (locStopL z n T ζ G W) t =ᵐ[P]
    P[fun ω => h ω φ / bumpNorm z n | ((hσ n).min_const t).measurableSpace]
  rw [e2]
  filter_upwards [hA, hs, hGae] with ω h1 h2 hωG
  obtain ⟨⟨-, hwc', hord⟩, -, -⟩ := hGgood ω hωG
  set r := locTimeL z n (T n ω) (ζ ω) (W · ω) with hr
  have hsr : min r t ≤ r := min_le_left _ _
  have hζs : ((min r t : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (by exact_mod_cast hsr) (hsafe ω hωG).1
  rw [h2, Pi.smul_apply, h1, smul_eq_mul, stoppedProcess_apply_of_eq (locStopL_of_mem hωG) t, min_comm]
  simp only [hτu ω hωG]
  have e3 : meanProc κ W u z (min r t) ω =
      couplingMean κ (rpath (W · ω)) (min r t : ℝ≥0) (u ω (min r t)) z := rfl
  rw [e3, couplingMean_eq_meanCan_of_safe (ρL := ρL) (ρR := ρR) (vL := fun i t => VL i t ω)
      (vR := fun i t => VR i t ω) hwc' hz' n (hsafe ω hωG) hsr (hord _ hζs).1 (hord _ hζs).2
      (hu ω (min r t)) (mem_closedBall_self (locRad_pos hz' n).le),
    meanCan_eq_integral_div_of_safe hwc' hz' n (hsafe ω hωG) hsr]
  have h4 := integral_couplingMean_mul_bumpFun_of_safe (κ := κ) (ρL := ρL) (ρR := ρR)
    (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hwc' hz' n (hsafe ω hωG) hsr
    (hord _ hζs).1 (hord _ hζs).2 (hu ω (min r t))
  rw [show (fun s : ℝ => W s.toNNReal ω) = rpath (W · ω) from rfl, h4, div_eq_inv_mul]

end Main

/-! ### The frozen optional hull specification -/

section Frozen

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The pairings of a coupled field are integrable**: `h = h⁰ + 𝔥₀` with `h⁰` a zero-boundary GFF, so `(h, φ)` is
Gaussian. -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.integrable_apply [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) : Integrable (fun ω => h ω φ) P := by
  obtain ⟨-, -, hgff, -⟩ := hC
  have hu0 := MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR 0 xL xR
  simp only [sub_zero] at hu0
  have hp := hgff _ hu0
  have hi := (hp.gaussian.hasGaussianLaw_eval φ).integrable
  refine (hi.add (integrable_const (∫ z, MartChar.meanExt κ ρL ρR 0 xL xR z * φ z))).congr ?_
  exact Eventually.of_forall fun ω => by simp

/-- With an infinite lifetime, the integer times announce it. -/
theorem isAnnouncingSeq_natCast {𝓖 : Filtration ℝ≥0 mΩ} (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsAnnouncingSeq 𝓖 P ζ fun n _ => (n : ℝ≥0) := by
  refine ⟨fun n => isStoppingTime_const 𝓖 (n : ℝ≥0), fun ω => fun m n hmn => by dsimp only; exact_mod_cast hmn,
    fun n => ?_, ?_⟩
  · filter_upwards [hζ] with ω hω
    rw [hω]; exact ENNReal.coe_lt_top
  · filter_upwards with ω t _
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact ⟨n, hn⟩

/-- **Martingale means of the frozen optional hull specification** (conditional helper: it assumes an announcing
sequence `T` of the lifetime in the frozen driving filtration). For every choice `u` of the bounded harmonic
extensions and every `z ∈ ℍ` there are stopping times `σ_n` of the driving filtration, almost surely below `ζ` and the
swallowing time `s(z)` and exhausting `[0, ζ ∧ s(z))`, such that each stopped coupling mean `t ↦ 𝔥_{t∧σ_n}(z)` agrees
almost surely, at every time, with a martingale of the driving filtration. -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.exists_martingale_stoppedProcess_meanProc
    [IsProbabilityMeasure P] (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : ℕ → Ω → ℝ≥0}
    (hT : IsAnnouncingSeq (drivingFiltration P hX) P ζ T) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t))
    {z : ℂ} (hz : z ∈ H) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime (drivingFiltration P hX) (σ n)) ∧
      (∀ n, ∀ᵐ ω ∂P, (σ n ω : ℝ≥0∞) < ζ ω ∧
        (σ n ω : ℝ≥0∞) ≤ QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z) ∧
      (∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω →
        (r : ℝ≥0∞) < QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z →
        ∀ᶠ n in atTop, (r : WithTop ℝ≥0) < σ n ω) ∧
      ∀ n, ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (drivingFiltration P hX) P ∧
        ∀ t, stoppedProcess (meanProc κ W u z) (σ n) t =ᵐ[P] M t := by
  have : (drivingFiltration P hX).IsRightContinuous := by
    unfold drivingFiltration usualAugmentation; infer_instance
  obtain ⟨_, hcf⟩ := hC.exists_isCouplingCharFun
  have hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω ≤ W t ω) ∧ ∀ i, W t ω ≤ VR i t ω := by
    filter_upwards [hC.1.2.2.2.2] with ω hω
    exact ⟨hω.1, hω.2.2.2.1, fun t ht => ⟨hω.2.2.2.2.2.2.2.1 t ht, hω.2.2.2.2.2.2.2.2.1 t ht⟩⟩
  exact MartMeans.exists_martingale_stoppedProcess_meanProc
    (fun s hs h0 => measurableSet_usualAugmentation_of_null hs h0 0)
    (adaptedBefore_mono (le_usualAugmentation _ P) (adaptedBefore_killedDriving_W hX)) hpath hT
    hC.integrable_apply hcf u hu hz

/-- **Martingale means of the frozen optional hull specification with an infinite lifetime** (no further input):
if `ζ = ∞` almost surely, the integer times announce the lifetime. -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.exists_martingale_stoppedProcess_meanProc_of_ae_eq_top
    [IsProbabilityMeasure P] (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t))
    {z : ℂ} (hz : z ∈ H) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime (drivingFiltration P hX) (σ n)) ∧
      (∀ n, ∀ᵐ ω ∂P, (σ n ω : ℝ≥0∞) < ζ ω ∧
        (σ n ω : ℝ≥0∞) ≤ QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z) ∧
      (∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ ω →
        (r : ℝ≥0∞) < QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z →
        ∀ᶠ n in atTop, (r : WithTop ℝ≥0) < σ n ω) ∧
      ∀ n, ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (drivingFiltration P hX) P ∧
        ∀ t, stoppedProcess (meanProc κ W u z) (σ n) t =ᵐ[P] M t :=
  hC.exists_martingale_stoppedProcess_meanProc hX (isAnnouncingSeq_natCast hζ) u hu hz

end Frozen

end MartMeans

end Coupling

end InteractingSLE
