/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2
import InteractingSLE.Spec.Supplement.OrdAStopTransfer

/-!
# The stopped K2 with announcing stops given in transferred form

Packet PROVE-T15-ASTOP. `Restart.StoppedK2.ae_isStoppedHullCoupling_k` uses its announcing stops `σₙ` only through
`Restart.StoppedK2.ae_isStoppingTime_of_agree`: for almost every `ω₀`, each `σₙ` is a stopping time of the
`ν`-driving filtration (`ν = condExpKernel P 𝒢 ω₀`) of every version agreeing with the continuation before the stop.
This file states that property as a hypothesis (`IsCondStopSeq`) and proves:

* `isCondStopSeq_of_driving`: stopping times of the driving filtration have it (the landed case);
* `isCondStopSeq_of_sup`: so do stopping times of the driving filtration enlarged at time `0` by a `𝒢`-measurable
  real code (`OrdAStop.ae_isStoppingTime_of_agree_sup`) — the case of the A-stop, whose announcing process reads the
  chart image of the retained union;
* **`ae_isStoppedHullCoupling_k_cond`**: the stopped K2 with this hypothesis in place of the driving-filtration
  stopping times.

Provenance: the proof of `ae_isStoppedHullCoupling_k_cond` is the proof of
`Restart.StoppedK2.ae_isStoppedHullCoupling_k` (`Spec/Restart/StoppedK2.lean`, PROVE-STOPPEDK2) verbatim, with its
line `have hT := fun n => ae_isStoppingTime_of_agree … (hσ n)` removed (the hypothesis is that statement).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdAStop

open Restart Restart.StoppedK2
open Restart.DomainMarkov.Aux79 (IsForceReg)
open Coupling Ito Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7 Sec7.Aux122Disint
open QuantumZipper (H fwdHull)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- **Announcing stops in transferred form**: for every `n`, for almost every `ω₀`, `σ n` is a stopping time of the
driving filtration under `condExpKernel P 𝒢 ω₀` of every version agreeing with `(W, VL, VR)` before `V`. -/
def IsCondStopSeq {Ω : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {nL nR : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (σ : ℕ → Ω → WithTop ℝ≥0) : Prop :=
  ∀ n, ∀ᵐ ω₀ ∂P, ∀ (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
    (hX' : IsMeasurableKilledDriving W' VL' VR' V),
    (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → W' t ω = W t ω ∧
      (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω) →
    IsStoppingTime (drivingFiltration (condExpKernel P 𝒢 ω₀) hX') (σ n)

section Cond

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {nL nR : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {σ : ℕ → Ω → WithTop ℝ≥0}

/-- Stopping times of the driving filtration are announcing stops in transferred form. -/
theorem isCondStopSeq_of_driving (h𝒢 : 𝒢 ≤ mΩ) (hXP : IsMeasurableKilledDriving W VL VR V)
    (hσ : ∀ n, IsStoppingTime (drivingFiltration P hXP) (σ n)) : IsCondStopSeq 𝒢 P W VL VR V σ :=
  fun n => ae_isStoppingTime_of_agree (P := P) h𝒢 hXP (hσ n)

/-- **Stopping times of the driving filtration enlarged by a `𝒢`-measurable code are announcing stops in transferred
form.** -/
theorem isCondStopSeq_of_sup (h𝒢 : 𝒢 ≤ mΩ) {e : Ω → ℝ} (he : Measurable[𝒢] e)
    (hXP : IsMeasurableKilledDriving W VL VR V)
    (hσ : ∀ n, IsStoppingTime (drivingSupCode P hXP (he.mono h𝒢 le_rfl)) (σ n)) :
    IsCondStopSeq 𝒢 P W VL VR V σ :=
  fun n => ae_isStoppingTime_of_agree_sup (P := P) h𝒢 he hXP (hσ n)

end Cond

section Main

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {V : Ω → ℝ≥0∞} {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {𝓗 : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **The stopped K2 with announcing stops in transferred form** (`Restart.StoppedK2.ae_isStoppedHullCoupling_k`
with `IsCondStopSeq` in place of stopping times of the `P`-side driving filtration). -/
theorem ae_isStoppedHullCoupling_k_cond
    (hE : IsRandomWordEvolutionUpTo κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B V)
    (hcont : ∀ᵐ ω ∂P, ω ∈ F → V ω ≠ ⊤ → ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (VL i · ω) (Iic (V ω).toNNReal)) ∧ ∀ j, ContinuousOn (VR j · ω) (Iic (V ω).toNNReal))
    (hX : Measurable X) (hV0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < V ω)
    {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0) (hW' : AdaptedBefore 𝓗' V W)
    (hVL' : ∀ i, AdaptedBefore 𝓗' V (VL i)) (hVR' : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR X) (hmem : HasSafeMembers P 𝓗' F V W X)
    {σ : ℕ → Ω → WithTop ℝ≥0} (hT : IsCondStopSeq 𝒢 P W VL VR V σ)
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂P, ω ∈ F → ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, ω ∈ F → Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω))) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        StoppedExtend.IsStoppedHullCoupling κ (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B' V X ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω →
          W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω := by
  obtain ⟨NE, 𝓖, W'', VL'', VR'', B'', -, hNE0, hagE, hev⟩ := exists_ae_condExpKernel_agree_upTo hE
  obtain ⟨h0, hF, -, -, -, -, -, -, hpath⟩ := hE
  have h𝒢m : 𝒢 ≤ mΩ := h0.trans (𝓗.le 0)
  have hweakP : ∀ᵐ ω ∂P, ω ∈ F →
      IsWeakPath (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (V ω) := by
    filter_upwards [hpath] with ω h hωF
    have hp := h hωF
    exact ⟨hp.w_zero, hp.continuousOn_w, hp.continuousOn_vL, hp.continuousOn_vR,
      fun t ht i => hp.vL_le_w ht i, fun t ht j => hp.w_le_vR ht j⟩
  obtain ⟨N, hNm, hN0, hN, -⟩ := exists_isKGood hweakP (p := fun _ => True) (ae_of_all _ fun _ => trivial)
  have hS := ae_isDyadicSampled_k h𝒢' hF hW' hVL' hVR' hX hNm hN0 hN hlaw
  have hR := ae_hasRatMembers_k h𝒢' hF hW' hVL' hVR' hX hNm hN0 hN hmem
  filter_upwards [hev, hS, hR, ae_all_iff.2 hT,
    ae_ae_condExpKernel h𝒢m (measure_eq_zero_iff_ae_notMem.1 hN0),
    ae_ae_condExpKernel h𝒢m (measure_eq_zero_iff_ae_notMem.1 hNE0),
    ae_ae_condExpKernel_mem (P := P) h𝒢m hF, ae_ae_condExpKernel h𝒢m hV0, ae_ae_condExpKernel h𝒢m hcont,
    ae_ae_condExpKernel h𝒢m hσV, ae_ae_condExpKernel h𝒢m hσlim] with ω₀ hev0 hS0 hR0 hT0 hNν hNEν hmemF hV0ν
    hcontν hσVν hσlimν hω₀F
  set ν := condExpKernel P 𝒢 ω₀ with hν
  have hE'' := hev0 hω₀F
  have hFν : ∀ᵐ ω ∂ν, ω ∈ F := hmemF hω₀F
  have hgood : ∀ᵐ ω ∂ν, ω ∈ F ∧ ω ∉ N ∧ ω ∉ NE ∧ 0 < V ω := by
    filter_upwards [hFν, hNν, hNEν, hV0ν] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4 h1⟩
  have hWW : ∀ ω, ω ∉ NE → ω ∈ F → ∀ t, W'' t ω = W t ω ∧ (∀ i, VL'' i t ω = VL i t ω) ∧
      ∀ j, VR'' j t ω = VR j t ω := fun ω h1 h2 t => by
    obtain ⟨e1, e2, e3, -⟩ := hagE ω h1 h2 t
    exact ⟨e1, e2, e3⟩
  -- the version frozen after `V`
  set W₁ : ℝ≥0 → Ω → ℝ := frz V W'' with hW₁
  set VL₁ : Fin nL → ℝ≥0 → Ω → ℝ := fun i => frz V (VL'' i) with hVL₁
  set VR₁ : Fin nR → ℝ≥0 → Ω → ℝ := fun j => frz V (VR'' j) with hVR₁
  have hag₁ : AgreeBefore V W'' VL'' VR'' W₁ VL₁ VR₁ := agreeBefore_frz
  have hE₁ : Sec2.IsSLEEvolutionUpTo κ (ΘL ω₀) (ΘR ω₀) ρL ρR ν 𝓖 W₁ VL₁ VR₁ B'' V := by
    refine ⟨hE''.brownian, adaptedBefore_congr (fun ω t ht => (hag₁ ω t ht).1) hE''.adapted_W,
      fun i => adaptedBefore_congr (fun ω t ht => (hag₁ ω t ht).2.1 i) (hE''.adapted_VL i),
      fun j => adaptedBefore_congr (fun ω t ht => (hag₁ ω t ht).2.2 j) (hE''.adapted_VR j), ?_⟩
    filter_upwards [hE''.ae_path, hgood] with ω hp hg
    exact isSLEPathUpTo_congr hg.2.2.2 (fun t ht => (hag₁ ω t ht).1) (fun t ht i => (hag₁ ω t ht).2.1 i)
      (fun t ht j => (hag₁ ω t ht).2.2 j) hp
  have hX₁ : IsMeasurableKilledDriving W₁ VL₁ VR₁ V :=
    isMeasurableKilledDriving_of_adaptedBefore hE₁.adapted_W hE₁.adapted_VL hE₁.adapted_VR
  have hX'' : IsMeasurableKilledDriving W'' VL'' VR'' V :=
    isMeasurableKilledDriving_of_adaptedBefore hE''.adapted_W hE''.adapted_VL hE''.adapted_VR
  -- continuity of the version on `[0, V]`
  have hcont'' : ∀ᵐ ω ∂ν, V ω ≠ ⊤ → ContinuousOn (W'' · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (VL'' i · ω) (Iic (V ω).toNNReal)) ∧
        ∀ j, ContinuousOn (VR'' j · ω) (Iic (V ω).toNNReal) := by
    filter_upwards [hgood, hcontν] with ω hg hc hVt
    obtain ⟨c1, c2, c3⟩ := hc hg.1 hVt
    exact ⟨c1.congr fun t _ => (hWW ω hg.2.2.1 hg.1 t).1, fun i => (c2 i).congr fun t _ =>
      (hWW ω hg.2.2.1 hg.1 t).2.1 i, fun j => (c3 j).congr fun t _ => (hWW ω hg.2.2.1 hg.1 t).2.2 j⟩
  -- regularity of the frozen version
  have hreg : ∀ᵐ ω ∂ν, IsForceReg W₁ VL₁ VR₁ (fun _ => ⊤) ω ∧ IsForceReg W₁ VL₁ VR₁ V ω := by
    filter_upwards [hE₁.ae_path, hE''.ae_path, hgood, hcont''] with ω hp₁ hp hg hc
    have hr'' : IsForceReg W'' VL'' VR'' V ω := ⟨hp.w_zero, hp.continuousOn_w, hp.continuousOn_vL,
      hp.continuousOn_vR, fun t ht => ⟨fun i => hp.vL_le_w ht i, fun j => hp.w_le_vR ht j⟩⟩
    exact ⟨isForceReg_frz_top hg.2.2.2 hr'' (fun h => (hc h).1) (fun h => (hc h).2.1) (fun h => (hc h).2.2),
      ⟨hp₁.w_zero, hp₁.continuousOn_w, hp₁.continuousOn_vL, hp₁.continuousOn_vR,
        fun t ht => ⟨fun i => hp₁.vL_le_w ht i, fun j => hp₁.w_le_vR ht j⟩⟩⟩
  -- K2's transferred identities for the frozen version
  have hagK : ∀ᵐ ω ∂ν, ∀ t, W'' t ω = kW N F W VL VR t ω ∧ (∀ i, VL'' i t ω = kVL N F W VL VR i t ω) ∧
      ∀ j, VR'' j t ω = kVR N F W VL VR j t ω := by
    filter_upwards [hgood] with ω hg t
    obtain ⟨e1, e2, e3⟩ := hWW ω hg.2.2.1 hg.1 t
    exact ⟨by rw [e1, kW_eq hg.2.1 hg.1], fun i => by rw [e2 i, kVL_eq hg.2.1 hg.1],
      fun j => by rw [e3 j, kVR_eq hg.2.1 hg.1]⟩
  have hdy₁ : IsDyadicSampled κ W₁ (bheProc κ ρL ρR W₁ VL₁ VR₁) ν hX₁ X :=
    isDyadicSampled_congr hX'' hX₁ hag₁ (hS0 hω₀F W'' VL'' VR'' hX'' hagK)
  have hXm' : ∀ ψ, Measurable fun ω => X ω ψ := fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp hX
  have hcf : MartMeans.IsCouplingCharFun κ ρL ρR ν (drivingFiltration ν hX₁) W₁ VL₁ VR₁ V X :=
    isCouplingCharFun_of_dyadic_reg hX₁ X hXm' hdy₁ (hreg.mono fun ω h => h.2)
  have h0' : ∀ᵐ ω ∂ν, 0 < V ω ∧ ContinuousOn (fun t => W₁ t ω) {t | (t : ℝ≥0∞) < V ω} ∧ W₁ 0 ω = 0 ∧
      (∀ i, VL₁ i 0 ω = ΘL ω₀ i) ∧ ∀ j, VR₁ j 0 ω = ΘR ω₀ j := by
    filter_upwards [hE₁.ae_path, hgood] with ω hp hg
    exact ⟨hg.2.2.2, hp.continuousOn_w, hp.w_zero, hp.vL_zero, hp.vR_zero⟩
  have hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (ΘL ω₀) (ΘR ω₀))
      (forceJumpSet (ΘL ω₀) (ΘR ω₀)) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) ν :=
    fun u₀ hu₀ => Lemma71J.isZBGFFProcess_of_isCouplingCharFun hcf hX h0' hu₀
  -- the field, centred
  have hu₀ := LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR (ΘL ω₀) (ΘR ω₀)
  set u₀ := LocalExt.bheAt κ ρL ρR (ΘL ω₀) (ΘR ω₀) with hu₀def
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hXgff := isZeroBoundaryGFF_sub_smoothDist hX hu₀c (hgff u₀ hu₀)
  have hsm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H :=
    WholeField.isHarmonicDistOn_smoothDist hu₀.1
  have hagK₁ : ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → W₁ t ω = kW N F W VL VR t ω ∧
      (∀ i, VL₁ i t ω = kVL N F W VL VR i t ω) ∧ ∀ j, VR₁ j t ω = kVR N F W VL VR j t ω := by
    filter_upwards [hagK] with ω hω t ht
    obtain ⟨e1, e2, e3⟩ := hag₁ ω t ht
    obtain ⟨f1, f2, f3⟩ := hω t
    exact ⟨e1.trans f1, fun i => (e2 i).trans (f2 i), fun j => (e3 j).trans (f3 j)⟩
  have hmb₁ := hR0 hω₀F u₀ hu₀.1 (hgff u₀ hu₀) W₁ VL₁ VR₁ hX₁ hagK₁
  have hagP₁ : ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → W₁ t ω = W t ω ∧
      (∀ i, VL₁ i t ω = VL i t ω) ∧ ∀ j, VR₁ j t ω = VR j t ω := by
    filter_upwards [hgood] with ω hg t ht
    obtain ⟨e1, e2, e3⟩ := hag₁ ω t ht
    obtain ⟨f1, f2, f3⟩ := hWW ω hg.2.2.1 hg.1 t
    exact ⟨e1.trans f1, fun i => (e2 i).trans (f2 i), fun j => (e3 j).trans (f3 j)⟩
  have hσν : ∀ n, IsStoppingTime (drivingFiltration ν hX₁) (σ n) := fun n => hT0 n W₁ VL₁ VR₁ hX₁ hagP₁
  have hσVν' : ∀ᵐ ω ∂ν, ∀ n, (σ n ω : ℝ≥0∞) < V ω := by
    filter_upwards [hσVν, hFν] with ω h1 h2 using h1 h2
  have hσlimν' : ∀ᵐ ω ∂ν, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)) := by
    filter_upwards [hσlimν, hFν] with ω h1 h2 using h1 h2
  have hWa : AdaptedBefore (killedDrivingFiltration hX₁) (fun _ => ⊤) W₁ :=
    adaptedBefore_frz (adaptedBefore_congr (fun ω t ht => (hag₁ ω t ht).1.symm) (adaptedBefore_killedDriving_W hX₁))
  have hcontT : ∀ᵐ ω ∂ν, ContinuousOn (fun t => W₁ t ω) {t | (t : ℝ≥0∞) < ⊤} ∧ W₁ 0 ω = 0 :=
    hreg.mono fun ω h => ⟨h.1.2.1, h.1.1⟩
  have hpath₁ : ∀ᵐ ω ∂ν, ContinuousOn (fun t => W₁ t ω) {t | (t : ℝ≥0∞) < V ω} ∧ W₁ 0 ω = 0 :=
    hreg.mono fun ω h => ⟨h.2.2.1, h.2.1⟩
  have hV0' : ∀ᵐ ω ∂ν, 0 < V ω := hgood.mono fun ω h => h.2.2.2
  refine ⟨𝓖, W₁, VL₁, VR₁, B'', ⟨hE₁, ?_, hX, hgff, hX₁, fun τ hτ hτV => ⟨?_, fun u hu φ => ?_⟩⟩, ?_⟩
  · -- the state is continuous through a finite stop
    filter_upwards [hreg] with ω h T _
    have cW : Continuous (W₁ · ω) := continuousOn_univ.1 (h.1.2.1.mono fun t _ => ENNReal.coe_lt_top)
    have cL : ∀ i, Continuous (VL₁ i · ω) := fun i =>
      continuousOn_univ.1 ((h.1.2.2.1 i).mono fun t _ => ENNReal.coe_lt_top)
    have cR : ∀ j, Continuous (VR₁ j · ω) := fun j =>
      continuousOn_univ.1 ((h.1.2.2.2.1 j).mono fun t _ => ENNReal.coe_lt_top)
    exact (cW.prodMk ((continuous_pi cL).prodMk (continuous_pi cR))).continuousOn
  · -- locality, from below
    have h2 := IsLocalSet.add_dist (isLocalSet_hull_le_stop hX₁ hXgff hmb₁ hpath₁ hV0' hWa hcontT hσν hσm
      hσVν' hσlimν' hτ hτV) hsm
    have e : (fun ω => X ω - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) = X :=
      funext fun ω => sub_add_cancel _ _
    rw [e] at h2
    exact h2
  · -- the conditional law, from below
    exact condExp_cexp_eq_of_le_stop hX₁ hXm' hcf (hreg.mono fun ω h => h.1) hσν hσm hσVν' hσlimν' hτ hτV u hu φ
  · -- agreement on `[0, V]`
    filter_upwards [hgood, hcont''] with ω hg hc t ht
    rcases ht.lt_or_eq with htV | htV
    · obtain ⟨e1, e2, e3⟩ := hag₁ ω t htV
      obtain ⟨f1, f2, f3⟩ := hWW ω hg.2.2.1 hg.1 t
      exact ⟨e1.trans f1, fun i => (e2 i).trans (f2 i), fun j => (e3 j).trans (f3 j)⟩
    · have hVt : V ω ≠ ⊤ := htV ▸ ENNReal.coe_ne_top
      have hta : t = (V ω).toNNReal := by rw [← htV, ENNReal.toNNReal_coe]
      obtain ⟨c1, c2, c3⟩ := hc hVt
      obtain ⟨f1, f2, f3⟩ := hWW ω hg.2.2.1 hg.1 t
      have hmin : min t (V ω).toNNReal = t := by rw [← hta, min_self]
      refine ⟨?_, fun i => ?_, fun j => ?_⟩
      · rw [hW₁, frz_eq_min hg.2.2.2 hVt c1, hmin, f1]
      · simp only [hVL₁]
        rw [frz_eq_min hg.2.2.2 hVt (c2 i), hmin, f2 i]
      · simp only [hVR₁]
        rw [frz_eq_min hg.2.2.2 hVt (c3 j), hmin, f3 j]

end Main

end InteractingSLE.RLC.OrdAStop
