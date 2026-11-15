/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Sec5.Aux61R45LifeLimit

/-!
# A trace continuous through a finite horizon forces a driver limit there

Packet PROVE-T15-RET2. Let `w : ℝ≥0 → ℝ` be continuous before `T > 0`, `w 0 = 0`, and let `η` be a
continuous generating trace of `w` on the closed interval `[0, T]` (the frozen `IsGeneratingTrace`
with the finite horizon `T`: no hull is asserted at `T` itself). Then `w` has a finite limit as
`t ↑ T` (`exists_tendsto_driver_of_isGeneratingTrace`). No probability is involved.

## Proof

Read everything on `ℝ` (`ηr s = η s⁺`). We verify the hypotheses of the landed
[Yua22, Theorem 1.1, (ii) ⇒ (i)] with Loewner's theorem on the CLOSED interval `[0, T]`
(`YuanCharacterisation.exists_loewner_of_hasContinuousOwnFuture`):

* `ηr` is continuous on `[0, T]`, starts at `0` and lies in `ℍ̄` (`Sec7.IsGeneratingTrace.mem_Hbar`);
* the fillings `fill(ηr[0, t])` increase strictly on `[0, T]`: before `T` they are the hulls of the driver
  frozen at a later time (`IsGeneratingTrace.isLoewnerTraceLT`), which grow strictly
  (`fwdHull_ne_of_lt`); at `T` use monotonicity of the filling;
* **continuous own futures up to `T`.** Fix `s < T`. The lift of the future after `s` is the uncentred
  shifted tip `β(u) = γ_s(u − s) + w(s)` of [Yua22] Corollary 1.3 (`futLift`). On `[s, t₂)`, `t₂ < T`, it
  agrees with the lift of the frozen driver (`futLift_eq`: the inverse maps only see the driver before
  their time), so it is continuous on `[s, T)`, lies in `ℍ̄` and satisfies `F̄_s(β(u)) = ηr(u)`
  (`IsLoewnerTraceLT.isLoewnerTraceLT_shift`, `invExt_fwdHull_eq_of_lt`). At `T` the **cluster-set lemma**
  (`YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter`, along `𝓝[<] T`) applies: `F̄_s` is the
  boundary extension of a conformal map, `β` is bounded (`F̄_s` is at bounded distance from the identity)
  and `F̄_s ∘ β = ηr → ηr(T)`; so `β` converges, to a point `ξ` of the fibre of `ηr(T)`. Setting
  `β(T) = ξ` gives a continuous lift on `[s, T]`.

The theorem gives a continuous driver `W` and a time change `σ` with `fwdHull W (σ t) = fill(ηr[0, t])`
on `[0, T]`. Comparing half-plane capacities (`hcap_fwdHull`) gives `σ t = t` for `t < T`, so `W`
generates the same trace as `w` before `T`, and driver uniqueness
(`Sec5.Aux61R45.driver_eq_before_of_common_trace`) gives `w = W` on `[0, T)`. As `W` is continuous,
`w(t) → W(T)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Restart.RetEnd

open YuanCharacterisation

/-! ### The inverse map of a trace before its horizon -/

/-- **`invExt K_s w = F̄_s(w − W(s))` on `ℍ̄`** for a continuous Loewner trace before a horizon `T > s`
(the horizon form of `IsLoewnerTrace.invExt_fwdHull_eq`, same proof). -/
theorem invExt_fwdHull_eq_of_lt {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) (hsT : s < T) {w : ℂ}
    (hw : w ∈ Hbar) : invExt (fwdHull W s) w = extendFrom H (fwdMapInv W s) (w - W s) := by
  have hwcl : w ∈ closure H := by rw [closure_H]; exact hw
  have hw' : w - W s ∈ Hbar := by
    show 0 ≤ (w - (W s : ℂ)).im
    simpa using (show 0 ≤ w.im from hw)
  have hshift : Tendsto (fun v : ℂ => v - W s) (𝓝[H] w) (𝓝[H] (w - W s)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((continuous_id.sub continuous_const).tendsto w).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    show 0 < (v - (W s : ℂ)).im
    simpa using (show 0 < v.im from hv)
  have hlim := ((hη.hasBdryLimits hW hW0 hs hsT).tendsto hw').comp hshift
  refine extendFrom_eq hwcl (hlim.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (YuanCorollary13.invFunOn_mapOut_fwdHull_eq hW hW0 hs hv).symm

/-! ### The lift of the future -/

/-- The driver read on `ℝ`: `s ↦ w(s⁺)`. -/
def realDrv (w : ℝ≥0 → ℝ) (s : ℝ) : ℝ := w s.toNNReal

/-- The trace read on `ℝ`: `s ↦ η(s⁺)`. -/
def realTr (η : ℝ≥0 → ℂ) (s : ℝ) : ℂ := η s.toNNReal

/-- **The lift of the future after `s`**: the uncentred shifted tip `u ↦ γ_s(u − s) + w(s)` of
[Yua22] Corollary 1.3, for the driver read on `ℝ`. -/
def futLift (w : ℝ≥0 → ℝ) (s u : ℝ) : ℂ :=
  loewnerTip (shiftDrive (realDrv w) s) (u - s) + (realDrv w s : ℂ)

/-- The shifted driver only sees the driver on `[s, t₂]`. -/
theorem shiftDrive_realDrv_eq {w : ℝ≥0 → ℝ} {s t₂ r : ℝ} (hs : 0 ≤ s) (hr : r ∈ Icc 0 (t₂ - s)) :
    shiftDrive (realDrv w) s r = shiftDrive (frozenDrive w t₂) s r := by
  have h1 : s + r ∈ Icc (0 : ℝ) t₂ := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have h2 : s ∈ Icc (0 : ℝ) t₂ := ⟨hs, by linarith [hr.1, hr.2]⟩
  simp only [shiftDrive, realDrv, frozenDrive_eq h1, frozenDrive_eq h2]

/-- **The lift agrees with the lift of the frozen driver** before the freezing time. -/
theorem futLift_eq {w : ℝ≥0 → ℝ} {s u t₂ : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (hut₂ : u < t₂) :
    futLift w s u = loewnerTip (shiftDrive (frozenDrive w t₂) s) (u - s) + (frozenDrive w t₂ s : ℂ) := by
  have h2 : s ∈ Icc (0 : ℝ) t₂ := ⟨hs, hsu.trans hut₂.le⟩
  unfold futLift loewnerTip
  rw [fwdMapInv_eq_of_eqOn (sub_nonneg.2 hsu) (show u - s < t₂ - s by linarith)
    (fun r hr => shiftDrive_realDrv_eq hs hr), frozenDrive_eq h2]
  rfl

/-! ### Continuous own futures up to the horizon -/

section Horizon

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0} {η : ℝ≥0 → ℂ}

theorem ofReal_lt_coe {t₂ : ℝ} (ht₂ : 0 ≤ t₂) (h : t₂ < (T : ℝ)) :
    ENNReal.ofReal t₂ < (T : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht₂).2 h

/-- The frozen driver at `t₂ < T` is continuous, starts at `0`, and has the trace (read on `ℝ`) as a
continuous Loewner trace before `t₂`. -/
theorem frozen_facts (hg : IsGeneratingTrace w (T : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)}) (hw0 : w 0 = 0) {t₂ : ℝ} (ht₂ : 0 ≤ t₂)
    (ht₂T : t₂ < (T : ℝ)) :
    IsLoewnerTraceLT (frozenDrive w t₂) t₂ (realTr η) ∧ Continuous (frozenDrive w t₂) ∧
      frozenDrive w t₂ 0 = 0 :=
  ⟨hg.isLoewnerTraceLT (ofReal_lt_coe ht₂ ht₂T),
    continuous_frozenDrive_of_lt hw (ofReal_lt_coe ht₂ ht₂T), by rw [frozenDrive_zero ht₂, hw0]⟩

theorem continuousOn_realTr (hg : IsGeneratingTrace w (T : ℝ≥0∞) η) :
    ContinuousOn (realTr η) (Icc 0 (T : ℝ)) :=
  hg.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (T : ℝ≥0∞) from
      ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)

theorem mapsTo_realTr (hg : IsGeneratingTrace w (T : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)}) (hw0 : w 0 = 0) :
    MapsTo (realTr η) (Icc 0 (T : ℝ)) Hbar := fun _ hs =>
  Sec7.IsGeneratingTrace.mem_Hbar hg hw hw0
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2))

/-- **The lift is continuous on `[s, T)`.** -/
theorem continuousOn_futLift (hg : IsGeneratingTrace w (T : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)}) (hw0 : w 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (futLift w s) (Ico s (T : ℝ)) := by
  intro u₀ hu₀
  set t₂ : ℝ := (u₀ + T) / 2 with ht₂
  have hu₀t₂ : u₀ < t₂ := by rw [ht₂]; linarith [hu₀.2]
  have ht₂T : t₂ < T := by rw [ht₂]; linarith [hu₀.2]
  have ht₂0 : 0 ≤ t₂ := by linarith [hu₀.1]
  obtain ⟨hLT, hWc, hW0⟩ := frozen_facts hg hw hw0 ht₂0 ht₂T
  have hcor := hLT.isLoewnerTraceLT_shift hWc hW0 hs
  have hcg : ContinuousOn (fun u => loewnerTip (shiftDrive (frozenDrive w t₂) s) (u - s) +
      (frozenDrive w t₂ s : ℂ)) (Ico s t₂) := by
    refine (hcor.1.2.1.comp (continuous_sub_right s).continuousOn fun u hu => ?_).add
      continuousOn_const
    exact ⟨sub_nonneg.2 hu.1, by linarith [hu.2]⟩
  have hmem : Ico s t₂ ∈ 𝓝[Ico s (T : ℝ)] u₀ :=
    mem_nhdsWithin.2 ⟨Iio t₂, isOpen_Iio, hu₀t₂, fun u hu => ⟨hu.2.1, hu.1⟩⟩
  refine ((hcg u₀ ⟨hu₀.1, hu₀t₂⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq ?_
    (futLift_eq hs hu₀.1 hu₀t₂)
  filter_upwards [hmem] with u hu
  exact futLift_eq hs hu.1 hu.2

/-- **The lift lies in `ℍ̄` and lifts the future**: `F̄_s(β(u)) = ηr(u)` for `u ∈ [s, T)`. -/
theorem futLift_spec (hg : IsGeneratingTrace w (T : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)}) (hw0 : w 0 = 0) {s u : ℝ} (hs : 0 ≤ s)
    (hu : u ∈ Ico s (T : ℝ)) :
    futLift w s u ∈ Hbar ∧ invExt (fillH (realTr η '' Icc 0 s)) (futLift w s u) = realTr η u := by
  set t₂ : ℝ := (u + T) / 2 with ht₂
  have hut₂ : u < t₂ := by rw [ht₂]; linarith [hu.2]
  have ht₂T : t₂ < T := by rw [ht₂]; linarith [hu.2]
  have ht₂0 : 0 ≤ t₂ := by linarith [hu.1]
  have hst₂ : s < t₂ := lt_of_le_of_lt hu.1 hut₂
  obtain ⟨hLT, hWc, hW0⟩ := frozen_facts hg hw hw0 ht₂0 ht₂T
  have hcor := hLT.isLoewnerTraceLT_shift hWc hW0 hs
  have hus : 0 ≤ u - s := sub_nonneg.2 hu.1
  have hus' : u - s < t₂ - s := by linarith
  have htipH : loewnerTip (shiftDrive (frozenDrive w t₂) s) (u - s) ∈ Hbar :=
    Sec7.IsLoewnerTraceLT.mem_Hbar hcor.1 (QuantumZipper.RS.continuous_shiftDrive hWc s)
      (QuantumZipper.RS.shiftDrive_zero _ s) hus hus'
  have hβH : futLift w s u ∈ Hbar := by
    rw [futLift_eq hs hu.1 hut₂]
    show 0 ≤ (loewnerTip (shiftDrive (frozenDrive w t₂) s) (u - s) +
      ((frozenDrive w t₂ s : ℝ) : ℂ)).im
    simpa using (show 0 ≤ (loewnerTip (shiftDrive (frozenDrive w t₂) s) (u - s)).im from htipH)
  refine ⟨hβH, ?_⟩
  rw [← hLT.2.2 s hs hst₂, invExt_fwdHull_eq_of_lt hLT hWc hW0 hs hst₂ hβH,
    futLift_eq hs hu.1 hut₂, add_sub_cancel_right, hcor.2 _ hus hus']
  congr 1
  ring
/-- **The lift converges at the horizon** (cluster-set lemma along `𝓝[<] T`): `β(u) → ξ` with `ξ ∈ ℍ̄`
in the fibre of `ηr(T)`. -/
theorem exists_tendsto_futLift (hg : IsGeneratingTrace w (T : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)}) (hw0 : w 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hsT : s < (T : ℝ)) :
    ∃ ξ ∈ Hbar, invExt (fillH (realTr η '' Icc 0 s)) ξ = realTr η T ∧
      Tendsto (futLift w s) (𝓝[<] (T : ℝ)) (𝓝 ξ) := by
  have hηc := continuousOn_realTr hg
  have h0 : realTr η 0 = 0 := by simpa [realTr] using hg.1
  obtain ⟨F, hext, hFfr, hFeq⟩ := exists_isBdryExt_invExt hs
    (hηc.mono (Icc_subset_Icc_right hsT.le))
    ((mapsTo_realTr hg hw hw0).mono_left (Icc_subset_Icc_right hsT.le)) h0
  obtain ⟨M, hM⟩ := hext.bdd
  obtain ⟨Rη, hRη⟩ := isCompact_Icc.exists_bound_of_continuousOn hηc
  have hinj : InjOn F H := fun a ha b hb hab => by
    rw [← (hext.mem a ha).2, ← (hext.mem b hb).2, hab]
  have hR : ∀ x : ℂ, x.im = 0 → F x ∉ F '' H := by
    rintro x hx ⟨y, hy, hxy⟩
    have hxH : x ∈ Hbar \ H := ⟨mem_Hbar_of_im_eq_zero hx, fun h => by
      have h' : (0 : ℝ) < x.im := h
      rw [hx] at h'
      exact lt_irrefl 0 h'⟩
    have hfr := hFfr hxH
    rw [hext.hull.isOpen.frontier_eq, ← hxy] at hfr
    exact hfr.2 (hext.mem y hy).1
  have hev : ∀ᶠ u in 𝓝[<] (T : ℝ), u ∈ Ioo s (T : ℝ) := Ioo_mem_nhdsLT hsT
  have hspec : ∀ᶠ u in 𝓝[<] (T : ℝ), futLift w s u ∈ Hbar ∧ F (futLift w s u) = realTr η u := by
    filter_upwards [hev] with u hu
    obtain ⟨h1, h2⟩ := futLift_spec hg hw hw0 hs ⟨hu.1.le, hu.2⟩
    exact ⟨h1, (hFeq h1).symm.trans h2⟩
  have hconn : ∀ U ∈ 𝓝[<] (T : ℝ), ∃ S ∈ 𝓝[<] (T : ℝ), S ⊆ U ∧ IsPreconnected S ∧
      ContinuousOn (futLift w s) S := by
    intro U hU
    obtain ⟨a, ha, haU⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hU
    refine ⟨Ioo (max a s) T, Ioo_mem_nhdsLT (max_lt ha hsT),
      fun u hu => haU ⟨(le_max_left _ _).trans_lt hu.1, hu.2⟩, isPreconnected_Ioo,
      (continuousOn_futLift hg hw hw0 hs).mono fun u hu => ⟨(le_max_right _ _).trans hu.1.le, hu.2⟩⟩
  have hGR : ∀ᶠ u in 𝓝[<] (T : ℝ), ‖futLift w s u‖ ≤ Rη + M := by
    filter_upwards [hspec, hev] with u hu hu'
    have h1 := hM _ hu.1
    have h2 := hRη u ⟨hs.trans hu'.1.le, hu'.2.le⟩
    rw [hu.2] at h1
    have h3 := norm_le_insert' (futLift w s u) (realTr η u)
    rw [norm_sub_rev] at h3
    linarith
  have hFG : Tendsto (fun u => F (futLift w s u)) (𝓝[<] (T : ℝ)) (𝓝 (realTr η T)) := by
    have hc : Tendsto (realTr η) (𝓝[<] (T : ℝ)) (𝓝 (realTr η T)) :=
      (hηc T ⟨T.coe_nonneg, le_rfl⟩).tendsto.mono_left (nhdsWithin_le_of_mem
        (mem_of_superset (Ioo_mem_nhdsLT hsT) fun u hu => ⟨hs.trans hu.1.le, hu.2.le⟩))
    exact hc.congr' (hspec.mono fun u hu => hu.2.symm)
  obtain ⟨ξ, hξH, hFξ, hξ⟩ := exists_tendsto_of_tendsto_comp_filter hext.differentiableOn
    hext.continuousOn hinj hR hconn (hspec.mono fun u hu => hu.1) hGR hFG
  exact ⟨ξ, hξH, (hFeq hξH).trans hFξ, hξ⟩

/-- **Property (ii) of [Yua22, Theorem 1.1] on the CLOSED interval `[0, T]`**: the lift of each
future, closed at `T` by its limit. -/
theorem hasContinuousOwnFuture_realTr (hg : IsGeneratingTrace w (T : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)}) (hw0 : w 0 = 0) :
    HasContinuousOwnFuture (realTr η) T := by
  intro s hs
  obtain ⟨ξ, hξH, hFξ, hξ⟩ := exists_tendsto_futLift hg hw hw0 hs.1 hs.2
  set β : ℝ → ℂ := fun u => if u < (T : ℝ) then futLift w s u else ξ with hβ
  have hβlt : ∀ u, u < (T : ℝ) → β u = futLift w s u := fun u hu => by simp [hβ, hu]
  have hβT : β T = ξ := by simp [hβ]
  have hlimβ : Tendsto β (𝓝[<] (T : ℝ)) (𝓝 ξ) :=
    hξ.congr' (eventually_nhdsWithin_of_forall fun u hu => (hβlt u hu).symm)
  refine ⟨β, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rcases hu.2.lt_or_eq with huT | rfl
    · have hmem : Ico s (T : ℝ) ∈ 𝓝[Icc s (T : ℝ)] u :=
        mem_nhdsWithin.2 ⟨Iio T, isOpen_Iio, huT, fun v hv => ⟨hv.2.1, hv.1⟩⟩
      refine ((continuousOn_futLift hg hw hw0 hs.1 u ⟨hu.1, huT⟩).mono_of_mem_nhdsWithin
        hmem).congr_of_eventuallyEq ?_ (hβlt u huT)
      filter_upwards [hmem] with v hv
      exact hβlt v hv.2
    · have h1 : ContinuousWithinAt β (Iio (T : ℝ)) T := by
        rw [ContinuousWithinAt, hβT]
        exact hlimβ
      exact (continuousWithinAt_Iio_iff_Iic.1 h1).mono Icc_subset_Iic_self
  · rcases hu.2.lt_or_eq with huT | rfl
    · rw [hβlt u huT]
      exact (futLift_spec hg hw hw0 hs.1 ⟨hu.1, huT⟩).1
    · rw [hβT]
      exact hξH
  · rcases hu.2.lt_or_eq with huT | rfl
    · rw [hβlt u huT]
      exact (futLift_spec hg hw hw0 hs.1 ⟨hu.1, huT⟩).2
    · rw [hβT]
      exact hFξ

/-- **Strict growth of the fillings on the closed interval `[0, T]`.** -/
theorem strictMonoOn_fillH_realTr (hg : IsGeneratingTrace w (T : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)}) (hw0 : w 0 = 0) :
    StrictMonoOn (fun t => fillH (realTr η '' Icc 0 t)) (Icc 0 (T : ℝ)) := by
  intro a ha b hb hab
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  set t₂ : ℝ := (c + T) / 2 with ht₂
  have hcT : c < T := hcb.trans_le hb.2
  have hct₂ : c < t₂ := by rw [ht₂]; linarith
  have ht₂T : t₂ < T := by rw [ht₂]; linarith
  have hc0 : 0 ≤ c := ha.1.trans hac.le
  obtain ⟨hLT, hWc, hW0⟩ := frozen_facts hg hw hw0 (hc0.trans hct₂.le) ht₂T
  have h1 : fwdHull (frozenDrive w t₂) a ⊂ fwdHull (frozenDrive w t₂) c :=
    ssubset_of_subset_of_ne (fwdHull_mono' hac.le) (fwdHull_ne_of_lt hWc hW0 ha.1 hac)
  have h2 : fwdHull (frozenDrive w t₂) c ⊆ fillH (realTr η '' Icc 0 b) := by
    rw [hLT.2.2 c hc0 hct₂]
    exact fillH_mono (image_mono (Icc_subset_Icc_right hcb.le))
  show fillH (realTr η '' Icc 0 a) ⊂ fillH (realTr η '' Icc 0 b)
  rw [← hLT.2.2 a ha.1 (hac.trans hct₂)]
  exact h1.trans_subset h2

/-- **A trace continuous through a finite horizon forces a driver limit there.** If `w` is
continuous before `T > 0`, `w 0 = 0`, and `η` is a continuous generating trace of `w` on `[0, T]`, then
`w` has a finite limit as `t ↑ T`. -/
theorem exists_tendsto_driver_of_isGeneratingTrace (hg : IsGeneratingTrace w (T : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)}) (hw0 : w 0 = 0) (hT : 0 < T) :
    ∃ c : ℝ, Tendsto w (𝓝[<] T) (𝓝 c) := by
  have hT' : (0 : ℝ) < T := NNReal.coe_pos.2 hT
  have h0 : realTr η 0 = 0 := by simpa [realTr] using hg.1
  obtain ⟨W, hWc, hW0, σ, hσ0, hσmono, -, hσK⟩ := exists_loewner_of_hasContinuousOwnFuture hT'
    (continuousOn_realTr hg) h0 (mapsTo_realTr hg hw hw0) (strictMonoOn_fillH_realTr hg hw hw0)
    (hasContinuousOwnFuture_realTr hg hw hw0)
  -- the capacity clock is the identity before `T`, so `W` has the hulls of `w` there
  have hK : ∀ t : ℝ, 0 ≤ t → t < T → fwdHull W t = fwdHull (realDrv w) t := by
    intro t ht htT
    set t₂ : ℝ := (t + T) / 2 with ht₂
    have htt₂ : t < t₂ := by rw [ht₂]; linarith
    have ht₂T : t₂ < T := by rw [ht₂]; linarith
    obtain ⟨hLT, hW₂c, hW₂0⟩ := frozen_facts hg hw hw0 (ht.trans htt₂.le) ht₂T
    have hK₂ : fwdHull W (σ t) = fwdHull (frozenDrive w t₂) t := by
      rw [hσK t ⟨ht, htT.le⟩, hLT.2.2 t ht htt₂]
    have hσt : 0 ≤ σ t := by
      have h := hσmono.monotoneOn ⟨le_rfl, hT'.le⟩ ⟨ht, htT.le⟩ ht
      rwa [hσ0] at h
    have h1 := hcap_fwdHull hWc hW0 hσt
    have h2 := hcap_fwdHull hW₂c hW₂0 ht
    have e : (⟨fwdHull W (σ t), isHPHull_fwdHull hWc hσt⟩ : HPHull) =
        ⟨fwdHull (frozenDrive w t₂) t, isHPHull_fwdHull hW₂c ht⟩ := Subtype.ext hK₂
    rw [e] at h1
    have hσt' : σ t = t := by linarith
    calc fwdHull W t = fwdHull W (σ t) := by rw [hσt']
      _ = fwdHull (frozenDrive w t₂) t := hK₂
      _ = fwdHull (realDrv w) t := fwdHull_eq_of_eqOn ht htt₂ fun r hr => frozenDrive_eq hr
  -- so `W` generates the same trace, and the drivers agree before `T`
  set W' : ℝ≥0 → ℝ := fun t => W t with hW'
  have hW'c : Continuous W' := hWc.comp NNReal.continuous_coe
  have hW'0 : W' 0 = 0 := by simp [hW', hW0]
  have hgW : IsGeneratingTrace W' (T : ℝ≥0∞) η := by
    refine ⟨hg.1, hg.2.1, fun t ht => ?_⟩
    have htT : (t : ℝ) < T := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ht)
    have e1 : QuantumZipper.fwdHull (fun s : ℝ => W' s.toNNReal) t =
        QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) t := by
      rw [fwdHull_eq_of_eqOn (W' := W) t.coe_nonneg (lt_add_one (t : ℝ)) fun r hr => by
        simp [hW', Real.coe_toNNReal _ hr.1]]
      exact hK t t.coe_nonneg htT
    rw [e1]
    exact hg.2.2 t ht
  refine ⟨W' T, ((hW'c.tendsto T).mono_left nhdsWithin_le_nhds).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (Sec5.Aux61R45.driver_eq_before_of_common_trace hw hw0 hW'c hW'0 hg hgW
    (ENNReal.coe_lt_coe.2 ht)).symm

end Horizon

end InteractingSLE.Restart.RetEnd
