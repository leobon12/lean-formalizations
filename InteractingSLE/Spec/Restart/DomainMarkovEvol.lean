/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovKernel
import InteractingSLE.Spec.Sec2.RestartEvolution

/-!
# The domain Markov step, part 3: the restarted evolution under the regular conditional law

Packet PROVE-DOMAINMARKOV2, item (E). Let `(W, V, B, ζ)` be an integrated `SLE_a(ρ)` evolution on a standard Borel
space and `T` a finite stopping time of its frozen driving filtration `𝓓`. With the progressive versions `W̃`, `Ṽ` of
the driving coordinates (`Sec2.Restart.progVersion`, built from `𝓓`), the restarted processes are
`W^T_t = W̃_{T+t} − W̃_T`, `V^T_t = Ṽ_{T+t} − W̃_T`, the restarted word is `Θ = Ṽ_T − W̃_T` and the restarted
lifetime is
`ζ − T`:

* **`isRandomWordEvolution_restart`**: the restarted processes form an integrated evolution with the random,
  `𝓓_T`-measurable initial word `Θ`, on the event `{T < ζ}` (strong Markov property under `P` itself: no
  conditioning on `{T < ζ}`, the path condition is only asked on that event);
* **`ae_isIntegratedSLEEvolution_condExpKernel_restart`**: hence (Aux. lemma 122 with every coordinate recorded,
  `exists_ae_condExpKernel_agree`) for `P`-almost every `ω₀` with `T ω₀ < ζ ω₀`, under the conditional law
  `condExpKernel P 𝓓_T ω₀` some processes equal (almost surely, at every time) to the restarted ones form an integrated
  `SLE_a(ρ)` evolution of the deterministic word `Θ ω₀`, with lifetime `ζ − T`;
* `ae_restartWord_eq`, `ae_rsW_eq_restartDrv`: `Θ = V_T − W_T` and the restarted processes agree with
  `restartDrv W T`, `restartMark V W T` before `ζ − T`, almost surely on `{T < ζ}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace DomainMarkov

open Sec2.Restart QuantumZipper.StrongMarkov Sec5.Markov

/-! ### The restarted processes -/

section Defs

variable {Ω : Type*} {nL nR : ℕ}

/-- The restarted progressive version `X̃_{T+t} − W̃_T`. -/
def rsX (ζ : Ω → ℝ≥0∞) (X W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => progVersion ζ X (T ω + t) ω - progVersion ζ W (T ω) ω

/-- The restarted word `Ṽ_T − W̃_T` (left marks). -/
def rsΘL (ζ : Ω → ℝ≥0∞) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) :
    Ω → Fin nL → ℝ :=
  fun ω i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω

/-- The restarted word `Ṽ_T − W̃_T` (right marks). -/
def rsΘR (ζ : Ω → ℝ≥0∞) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) :
    Ω → Fin nR → ℝ :=
  fun ω j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω

/-- The event `{T < ζ}` on which the restart is alive. -/
def liveSet (ζ : Ω → ℝ≥0∞) (T : Ω → ℝ≥0) : Set Ω := {ω | (T ω : ℝ≥0∞) < ζ ω}

end Defs

/-! ### Strong Markov property on the live event -/

section Restart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {a : ℝ} {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0}

omit [IsProbabilityMeasure P] in
/-- The driving coordinates are adapted before `ζ` to the frozen driving filtration. -/
theorem adaptedBefore_driving (hX : IsMeasurableKilledDriving W VL VR ζ) :
    AdaptedBefore (drivingFiltration P hX) ζ W ∧ (∀ i, AdaptedBefore (drivingFiltration P hX) ζ (VL i)) ∧
      ∀ j, AdaptedBefore (drivingFiltration P hX) ζ (VR j) := by
  have hle : killedDrivingFiltration hX ≤ drivingFiltration P hX := Ito.le_usualAugmentation _ P
  exact ⟨Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_W hX),
    fun i => Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_VL hX i),
    fun j => Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_VR hX j)⟩

omit [IsProbabilityMeasure P] in
/-- `{T < ζ}` is an event of `𝓓_T`. -/
theorem measurableSet_liveSet (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) :
    MeasurableSet[hT.measurableSpace] (liveSet ζ T) := by
  have hζ := Ito.isStoppingTime_lifetime (adaptedBefore_driving (P := P) hX).1
  have h := (IsStoppingTime.measurableSet_stopping_time_le hζ hT).compl
  have e : liveSet ζ T = {ω | (ζ ω : WithTop ℝ≥0) ≤ (T ω : WithTop ℝ≥0)}ᶜ := by
    ext ω
    exact (not_le (α := ℝ≥0∞)).symm
  rw [e]
  exact h

omit [IsProbabilityMeasure P] in
/-- The restarted word is `𝓓_T`-measurable. -/
theorem measurable_rsΘ (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) :
    Measurable[hT.measurableSpace] (rsΘL ζ VL W T) ∧ Measurable[hT.measurableSpace] (rsΘR ζ VR W T) := by
  obtain ⟨hWa, hLa, hRa⟩ := adaptedBefore_driving (P := P) hX
  have hev : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore (drivingFiltration P hX) ζ X →
      Measurable[hT.measurableSpace] fun ω => progVersion ζ X (T ω) ω := fun hXa => by
    have h := measurable_restart_eval_zero (isStronglyProgressive_progVersion hXa) hT 0
    rwa [restartFiltration_zero] at h
  exact ⟨@Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) hT.measurableSpace _ _ fun i => (hev (hLa i)).sub (hev hWa),
    @Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) hT.measurableSpace _ _ fun j => (hev (hRa j)).sub (hev hWa)⟩

/-- **Strong Markov property on the live event.** For an integrated evolution and a finite stopping time `T` of its
frozen driving filtration, the restarted progressive versions form, with the restarted Brownian motion and the
lifetime `ζ − T`, an integrated evolution of the random `𝓓_T`-measurable word `Θ = Ṽ_T − W̃_T` on `{T < ζ}`, in a
filtration whose time-`0` σ-algebra contains `𝓓_T`. -/
theorem isRandomWordEvolution_restart (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) :
    ∃ (𝓕' : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ),
      Sec7.Aux122Disint.IsRandomWordEvolution a P hT.measurableSpace (liveSet ζ T) (rsΘL ζ VL W T)
        (rsΘR ζ VR W T) ρL ρR 𝓕' (rsX ζ W W T) (fun i => rsX ζ (VL i) W T) (fun j => rsX ζ (VR j) W T) B'
        (restartLife ζ T) := by
  obtain ⟨hBF, hWad, hVLad, hVRad, hpath⟩ := hE
  obtain ⟨Bv, -, hBvc, hBvF, hBvae⟩ := exists_continuous_version hBF
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have h𝓓𝓖 : drivingFiltration P hX ≤ 𝓖 :=
    Ito.drivingFiltration_le_usualAugmentation ⟨hBF, hWad, hVLad, hVRad, hpath⟩ hX
  have hT𝓖 : IsStoppingTime 𝓖 fun ω => (T ω : WithTop ℝ≥0) := fun u => h𝓓𝓖 u _ (hT u)
  have h𝓕𝓖 : 𝓕 ≤ 𝓖 := Ito.le_usualAugmentation 𝓕 P
  have hWad' : AdaptedBefore 𝓖 ζ W := Ito.adaptedBefore_mono h𝓕𝓖 hWad
  have hζ := Ito.isStoppingTime_lifetime hWad'
  have hWp := isStronglyProgressive_progVersion hWad'
  have hLp := fun i => isStronglyProgressive_progVersion (Ito.adaptedBefore_mono h𝓕𝓖 (hVLad i))
  have hRp := fun j => isStronglyProgressive_progVersion (Ito.adaptedBefore_mono h𝓕𝓖 (hVRad j))
  have hBr : IsFilteredBrownianReal (restartFiltration 𝓖 T hT𝓖) (smShift Bv T) P := by
    have h := isFilteredBrownianReal_restart_cond hBvF hBvc hT𝓖 (A := univ) MeasurableSet.univ
      (by rw [measure_univ]; exact one_ne_zero)
    rwa [cond_univ] at h
  obtain ⟨hΘL, hΘR⟩ := measurable_rsΘ hX hT
  refine ⟨restartFiltration 𝓖 T hT𝓖, smShift Bv T, ?_, measurableSet_liveSet hX hT, hΘL, hΘR, hBr,
    adaptedBefore_restart hT𝓖 hζ hWp hWp, fun i => adaptedBefore_restart hT𝓖 hζ (hLp i) hWp,
    fun j => adaptedBefore_restart hT𝓖 hζ (hRp j) hWp, ?_⟩
  · rw [restartFiltration_zero]
    exact Ito.measurableSpace_le_of_filtration_le h𝓓𝓖 hT hT𝓖
  · filter_upwards [hpath, hBvae] with ω hp hb hωF
    have hTζ : (T ω : ℝ≥0∞) < ζ ω := hωF
    have h0 := restart_values hp hTζ
    have hr := hp.restart hTζ
    have e1 : rsΘL ζ VL W T ω = fun i => VL i (T ω) ω - W (T ω) ω := by
      funext i; simp only [rsΘL, h0.2.1 i, h0.1]
    have e2 : rsΘR ζ VR W T ω = fun j => VR j (T ω) ω - W (T ω) ω := by
      funext j; simp only [rsΘR, h0.2.2 j, h0.1]
    show IsIntegratedSLEPath a (rsΘL ζ VL W T ω) (rsΘR ζ VR W T ω) ρL ρR (fun t => rsX ζ W W T t ω)
      (fun i t => rsX ζ (VL i) W T t ω) (fun j t => rsX ζ (VR j) W T t ω) (fun t => smShift Bv T t ω)
      (ζ ω - T ω)
    rw [e1, e2]
    refine Sec2.Assembly.isIntegratedSLEPath_congr hr ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [rsX, add_zero, h0.1]
    · intro i; simp only [rsX, add_zero, h0.1, h0.2.1 i]
    · intro j; simp only [rsX, add_zero, h0.1, h0.2.2 j]
    · intro t ht
      have h1 := restart_values hp ((coe_lt_sub_iff _ _).1 ht)
      simp only [rsX, h0.1, h1.1]
    · intro t ht i
      have h1 := restart_values hp ((coe_lt_sub_iff _ _).1 ht)
      simp only [rsX, h0.1, h1.2.1 i]
    · intro t ht j
      have h1 := restart_values hp ((coe_lt_sub_iff _ _).1 ht)
      simp only [rsX, h0.1, h1.2.2 j]
    · intro t _
      simp only [smShift, hb]

omit [IsProbabilityMeasure P] in
/-- On a good path with `T < ζ`, the restarted word is `V_T − W_T` and the restarted progressive versions are
`restartDrv W T`, `restartMark V W T` before `ζ − T`. -/
theorem ae_rsX_eq (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
      (rsΘL ζ VL W T ω = fun i => VL i (T ω) ω - W (T ω) ω) ∧
      (rsΘR ζ VR W T ω = fun j => VR j (T ω) ω - W (T ω) ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω → rsX ζ W W T t ω = restartDrv W T t ω ∧
        (∀ i, rsX ζ (VL i) W T t ω = restartMark (VL i) W T t ω) ∧
        ∀ j, rsX ζ (VR j) W T t ω = restartMark (VR j) W T t ω := by
  filter_upwards [hE.2.2.2.2] with ω hp hTζ
  have h0 := restart_values hp hTζ
  refine ⟨funext fun i => by simp only [rsΘL, h0.2.1 i, h0.1],
    funext fun j => by simp only [rsΘR, h0.2.2 j, h0.1], fun t ht => ?_⟩
  have h1 := restart_values hp ((coe_lt_sub_iff _ _).1 ht)
  exact ⟨by simp only [rsX, restartDrv, h0.1, h1.1], fun i => by simp only [rsX, restartMark, h0.1, h1.2.1 i],
    fun j => by simp only [rsX, restartMark, h0.1, h1.2.2 j]⟩

/-- **The restarted evolution under the regular conditional law** (Aux. lemma 53, item (E)). On a standard Borel
space, for `P`-almost every `ω₀` with `T ω₀ < ζ ω₀`, under `condExpKernel P 𝓓_T ω₀` some processes that agree almost
surely, at every time, with the restarted progressive versions form an integrated `SLE_a(ρ)` evolution of the word
`Θ ω₀` with lifetime `ζ − T`; and the live event `{T < ζ}` has full conditional probability. -/
theorem ae_isIntegratedSLEEvolution_condExpKernel_restart [StandardBorelSpace Ω]
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) :
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
      (B' : ℝ≥0 → Ω → ℝ), ∀ᵐ ω₀ ∂P, (T ω₀ : ℝ≥0∞) < ζ ω₀ →
        IsIntegratedSLEEvolution a (rsΘL ζ VL W T ω₀) (rsΘR ζ VR W T ω₀) ρL ρR
          (condExpKernel P hT.measurableSpace ω₀) 𝓖 W' VL' VR' B' (restartLife ζ T) ∧
        ∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), ω ∈ liveSet ζ T ∧ ∀ t : ℝ≥0,
          W' t ω = rsX ζ W W T t ω ∧ (∀ i, VL' i t ω = rsX ζ (VL i) W T t ω) ∧
            ∀ j, VR' j t ω = rsX ζ (VR j) W T t ω := by
  obtain ⟨𝓕', B', hR⟩ := isRandomWordEvolution_restart hE hX hT
  obtain ⟨N, 𝓖, W', VL', VR', B'', -, hN0, hagree, hev⟩ := exists_ae_condExpKernel_agree hR
  have hle : hT.measurableSpace ≤ mΩ := hT.measurableSpace_le
  have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  refine ⟨𝓖, W', VL', VR', B'', ?_⟩
  filter_upwards [hev, Sec7.Aux122Disint.ae_ae_condExpKernel hle hNc,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem hle (measurableSet_liveSet hX hT)] with ω₀ h1 h2 h3 hω₀
  refine ⟨h1 hω₀, ?_⟩
  filter_upwards [h2, h3 hω₀] with ω hωN hωF
  exact ⟨hωF, fun t => let h := hagree ω hωN hωF t; ⟨h.1, h.2.1, h.2.2.1⟩⟩

end Restart

end DomainMarkov

end Restart

end InteractingSLE
