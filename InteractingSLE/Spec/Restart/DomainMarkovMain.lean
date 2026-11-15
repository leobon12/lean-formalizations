/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovTransferKernel
import InteractingSLE.Spec.Sec7.Lemma71Joint

/-!
# The domain Markov step, part 7: Aux. lemma 53 in kernel form from its locality half

Packet PROVE-DOMAINMARKOV2. Assembly of `KernelRestartCouplingStatement κ` (Aux. lemma 53 in kernel form,
`DomainMarkovKernel.lean`) for every `κ > 0`, from the locality of the restarted hulls under the conditional laws:

* `isDyadicSampled_of_agree`: the protected-kernel law at the dyadic times (`IsDyadicSampled`) under one conditional law
  `ν`, for any processes that agree `ν`-almost surely, at every time, with the modified restarted data, from the
  transfer
  `ae_setIntegral_cexp_eq_cfAt_restart`;
* `KernelRestartLocalityStatement κ` (**named input**): for `P`-almost every `ω₀` with `T ω₀ < ζ ω₀`, under
  `ν = condExpKernel P 𝓓_T ω₀`, for any measurable versions of the restarted driver and marks and every stopping time
  `τ' < ζ − T` of their (`ν`-augmented) driving filtration, the restarted hull `K'_{τ'}` is a local set of the restarted
  field `restartField κ (h, K)`;
* **`kernelRestartCouplingStatement_of_locality`**: `0 < κ` and the locality input give
  `KernelRestartCouplingStatement κ`.
  The evolution is item (E) (`ae_isIntegratedSLEEvolution_condExpKernel_restart`), the conditional-law clause at every
  stopping time is `condExp_cexp_eq_frozenRHS_of_dyadic` from item (S), and the Gaussian law at time `0` is the
  clause at
  `τ = 0` (`Sec7.Lemma71J.isZBGFFProcess_of_isCouplingCharFun`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace DomainMarkov

open Coupling Ito Sec7 Sec7.Aux122Disint Sec2.Restart Sec5.Markov LocalExt

/-! ### The dyadic protected-kernel law for versions of the restarted data -/

section Agree

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0} {N : Set Ω}

/-- The bounded harmonic extension of the force data of driving processes at every time. -/
def bheProc (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Ω → ℝ≥0 → ℂ → ℝ := fun ω s =>
  bheAt κ ρL ρR (fun i => VL i s ω - W s ω) (fun j => VR j s ω - W s ω)

omit mΩ in
theorem isBoundedHarmonicExtension_bheProc (ω : Ω) (s : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun j => VR j s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun j => VR j s ω - W s ω)) (bheProc κ ρL ρR W VL VR ω s) :=
  isBoundedHarmonicExtension_bheAt κ ρL ρR _ _

/-- **The dyadic protected-kernel law for versions of the modified restarted data** under one measure `ν`: if the
transferred identities hold under `ν` (`ae_setIntegral_cexp_eq_cfAt_restart` at `ω₀`) and processes `W'`, `V'` agree
`ν`-almost surely, at every time, with the modified restarted data, then `IsDyadicSampled` holds for them. -/
theorem isDyadicSampled_of_agree (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hNm : MeasurableSet N) (hN : IsGoodOff N ζ W VL VR T) {ν : Measure Ω}
    {h' : Ω → DistOn upperHalfPlaneOpens}
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) (n k : ℕ) (A : Set Ω), MeasurableSet A →
      (∃ A', MeasurableSet[dF N ζ W VL VR T (dyT n k)] A' ∧ A =ᵐ[ν] A') →
      (∀ᵐ ω ∂ν, ω ∈ A → ω ∈ avoidSet (zW N ζ W VL VR T) (restartLife ζ T) ψ (dyT n k)) →
      ∫ ω in A, Complex.exp (Complex.I * (h' ω ψ : ℂ)) ∂ν =
        ∫ ω in A, cfAt κ (zW N ζ W VL VR T) (uZ κ ρL ρR N ζ W VL VR T) ψ 1 (fun _ => dyT n k) ω ∂ν)
    {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR' : Fin nR → ℝ≥0 → Ω → ℝ}
    (hX' : IsMeasurableKilledDriving W' VL' VR' (restartLife ζ T))
    (hagree : ∀ᵐ ω ∂ν, ∀ t, W' t ω = zW N ζ W VL VR T t ω ∧ (∀ i, VL' i t ω = zVL N ζ W VL VR T i t ω) ∧
      ∀ j, VR' j t ω = zVR N ζ W VL VR T j t ω) :
    IsDyadicSampled κ W' (bheProc κ ρL ρR W' VL' VR') ν hX' h' := by
  intro ψ n k A hA hAav
  set q := dyT n k
  -- the killed driving events of the versions are `ν`-almost surely events of the data filtration
  have hZa := fun i => adaptedBefore_zData_dF hX hT hNm hN i
  have hXZ : IsMeasurableKilledDriving (zW N ζ W VL VR T) (zVL N ζ W VL VR T) (zVR N ζ W VL VR T)
      (restartLife ζ T) :=
    isMeasurableKilledDriving_of_adaptedBefore (hZa none) (fun i => hZa (some (Sum.inl i)))
      (fun j => hZa (some (Sum.inr j)))
  have hkZ := killedDrivingFiltration_le (hZa none) (fun i => hZa (some (Sum.inl i)))
    (fun j => hZa (some (Sum.inr j))) hXZ
  have hle : nullAugmented (killedDrivingFiltration hX') ν q ≤
      eventuallyMeasurableSpace (dF N ζ W VL VR T q) (ae ν) := by
    refine sup_le (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_le ?_)
    · rintro _ ⟨r, hrq, B, hB, rfl⟩
      refine ⟨{ω | (r : ℝ≥0∞) < restartLife ζ T ω ∧ (zW N ζ W VL VR T r ω, fun i => zVL N ζ W VL VR T i r ω,
        fun j => zVR N ζ W VL VR T j r ω) ∈ B}, hkZ q _ (MeasurableSpace.measurableSet_generateFrom
          ⟨r, hrq, B, hB, rfl⟩), ?_⟩
      filter_upwards [hagree] with ω hω
      obtain ⟨h1, h2, h3⟩ := hω r
      have e2 : (fun i => VL' i r ω) = fun i => zVL N ζ W VL VR T i r ω := funext h2
      have e3 : (fun j => VR' j r ω) = fun j => zVR N ζ W VL VR T j r ω := funext h3
      change ((r : ℝ≥0∞) < restartLife ζ T ω ∧ _ ∈ B) = ((r : ℝ≥0∞) < restartLife ζ T ω ∧ _ ∈ B)
      rw [h1, e2, e3]
    · rintro s ⟨-, hs0⟩
      exact ⟨∅, @MeasurableSet.empty _ (dF N ζ W VL VR T q), ae_eq_empty.2 hs0⟩
  obtain ⟨A', hA', hAA'⟩ := hle _ hA
  have hAm : MeasurableSet A := (nullAugmented (killedDrivingFiltration hX') ν).le q _ hA
  -- pathwise agreement of the avoidance events and of `cfAt`
  have hpath : ∀ᵐ ω ∂ν, (fun s : ℝ => W' s.toNNReal ω) = (fun s : ℝ => zW N ζ W VL VR T s.toNNReal ω) ∧
      bheProc κ ρL ρR W' VL' VR' ω q = uZ κ ρL ρR N ζ W VL VR T ω q := by
    filter_upwards [hagree] with ω hω
    refine ⟨funext fun s => (hω _).1, ?_⟩
    obtain ⟨h1, h2, h3⟩ := hω q
    simp only [bheProc, uZ, h1, h2, h3]
  have hAav' : ∀ᵐ ω ∂ν, ω ∈ A → ω ∈ avoidSet (zW N ζ W VL VR T) (restartLife ζ T) ψ q := by
    filter_upwards [hpath] with ω hω hωA
    have h := hAav hωA
    simp only [avoidSet, mem_ofPred_eq] at h ⊢
    rw [← hω.1]
    exact h
  rw [hS ψ n k A hAm ⟨A', hA', hAA'⟩ hAav']
  refine setIntegral_congr_ae hAm ?_
  filter_upwards [hpath] with ω hω _
  simp only [cfAt]
  rw [hω.1, hω.2]

end Agree

/-! ### The named locality input and the assembly -/

section Main

universe u

/-- **Named input (not proved here): the locality half of Aux. lemma 53 in kernel form.** For a frozen optional hull
coupling on a standard Borel space, a finite stopping time `T` of its driving filtration `𝓓` and a `𝓓_T`-measurable
version `K` of the stopped history: for `P`-almost every `ω₀` with `T ω₀ < ζ ω₀`, under `ν = condExpKernel P 𝓓_T ω₀`,
for all measurable processes `W'`, `V'` that agree `ν`-almost surely with the restarted driver and marks before the
restarted lifetime `ζ − T`, and every stopping time `τ' < ζ − T` (`ν`-almost surely) of their driving filtration
`drivingFiltration ν`, the restarted hull `K'_{τ'}` is a local set of the restarted field `restartField κ (h, K)` under
`ν`. (Specification p. 245: "History marking permits retention of the canonical germ of `K_τ` … Forgetting that germ
preserves locality.") -/
def KernelRestartLocalityStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
    ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (T : Ω → ℝ≥0)
      (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
      (K : Ω → DrivingHist nL nR), Measurable[hT.measurableSpace] K →
      (∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
        K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) →
    ∀ᵐ ω₀ ∂P, (T ω₀ : ℝ≥0∞) < ζ ω₀ →
      ∀ (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
        (hX' : IsMeasurableKilledDriving W' VL' VR' (restartLife ζ T)),
        (∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω →
          W' t ω = restartDrv W T t ω ∧ (∀ i, VL' i t ω = restartMark (VL i) W T t ω) ∧
            ∀ j, VR' j t ω = restartMark (VR j) W T t ω) →
        ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (drivingFiltration (condExpKernel P hT.measurableSpace ω₀) hX') τ →
          (∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), (τ ω : ℝ≥0∞) < restartLife ζ T ω) →
          IsLocalSet (fun ω => fwdHull (fun s : ℝ => W' s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
            (fun ω => restartField κ (h ω, K ω)) (condExpKernel P hT.measurableSpace ω₀)

/-- **Aux. lemma 53 in kernel form, from its locality half** (specification p. 245). For `κ > 0`, the locality input
`KernelRestartLocalityStatement κ` gives `KernelRestartCouplingStatement κ`: under almost every conditional law given
the stopped driving history `𝓓_T`, versions of the restarted driver and marks (equal to `restartDrv W T`,
`restartMark V W T` before `ζ − T`) and the restarted field `restartField κ (h, K)` form an optional hull coupling of
the
current word `(V_T − W_T)(ω₀)`. -/
theorem kernelRestartCouplingStatement_of_locality {κ : ℝ} (hκ : 0 < κ)
    (hloc : KernelRestartLocalityStatement.{u} κ) : KernelRestartCouplingStatement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ _ P _ 𝓕 W VL VR B ζ h hC hX T hT K hKm hK
  obtain ⟨𝓖, W', VL', VR', B', hev⟩ := ae_isIntegratedSLEEvolution_condExpKernel_restart hC.1 hX hT
  obtain ⟨N, hNm, hN0, hN⟩ := exists_isGoodOff hC.1 hX hT
  have hS := ae_setIntegral_cexp_eq_cfAt_restart hC hκ hX hT hKm hK hNm hN0 hN
  have hle : hT.measurableSpace ≤ mΩ := hT.measurableSpace_le
  have hNν := ae_ae_condExpKernel hle (measure_eq_zero_iff_ae_notMem.1 hN0)
  have hrs := ae_ae_condExpKernel hle (ae_rsX_eq (T := T) hC.1)
  have hKm' : Measurable K := hKm.mono hle le_rfl
  have hh' : Measurable fun ω => restartField κ (h ω, K ω) :=
    (measurable_restartField κ).comp (hC.2.1.prodMk hKm')
  filter_upwards [hev, hS, hNν, hrs, hloc xL xR ρL ρR P 𝓕 W VL VR B ζ h hC hX T hT K hKm hK,
    ae_rsX_eq (T := T) hC.1] with ω₀ hev0 hS0 hN0' hrs0 hloc0 hword hTζ
  obtain ⟨hE', hag⟩ := hev0 hTζ
  obtain ⟨hΘL, hΘR, -⟩ := hword hTζ
  rw [hΘL, hΘR] at hE'
  -- agreement with the modified data and with the restart
  have hagZ : ∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), ∀ t, W' t ω = zW N ζ W VL VR T t ω ∧
      (∀ i, VL' i t ω = zVL N ζ W VL VR T i t ω) ∧ ∀ j, VR' j t ω = zVR N ζ W VL VR T j t ω := by
    filter_upwards [hag, hN0'] with ω ⟨hF, h1⟩ hωN t
    obtain ⟨e1, e2, e3⟩ := h1 t
    exact ⟨by rw [e1, zW, zData_none hωN hF], fun i => by rw [e2 i, zVL, zData_inl hωN hF],
      fun j => by rw [e3 j, zVR, zData_inr hωN hF]⟩
  have hagR : ∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω →
      W' t ω = restartDrv W T t ω ∧ (∀ i, VL' i t ω = restartMark (VL i) W T t ω) ∧
        ∀ j, VR' j t ω = restartMark (VR j) W T t ω := by
    filter_upwards [hag, hrs0] with ω ⟨hF, h1⟩ h2 t ht
    obtain ⟨-, -, h3⟩ := h2 hF
    obtain ⟨f1, f2, f3⟩ := h3 t ht
    obtain ⟨e1, e2, e3⟩ := h1 t
    exact ⟨e1.trans f1, fun i => (e2 i).trans (f2 i), fun j => (e3 j).trans (f3 j)⟩
  have hX' := IsIntegratedSLEEvolution.isMeasurableKilledDriving hE'
  have hdy : ∀ hX'' : IsMeasurableKilledDriving W' VL' VR' (restartLife ζ T),
      IsDyadicSampled κ W' (bheProc κ ρL ρR W' VL' VR') (condExpKernel P hT.measurableSpace ω₀) hX''
        (fun ω => restartField κ (h ω, K ω)) := fun hX'' =>
    isDyadicSampled_of_agree hX hT hNm hN hS0 hX'' hagZ
  have hcf : MartMeans.IsCouplingCharFun κ ρL ρR (condExpKernel P hT.measurableSpace ω₀)
      (drivingFiltration (condExpKernel P hT.measurableSpace ω₀) hX') W' VL' VR' (restartLife ζ T)
      (fun ω => restartField κ (h ω, K ω)) := fun τ hτ hτζ uτ huτ φ =>
    condExp_cexp_eq_frozenRHS_of_dyadic hE' (bheProc κ ρL ρR W' VL' VR')
      (fun ω s => isBoundedHarmonicExtension_bheProc ω s) _
      (fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp hh') hX' (hdy hX') hτ hτζ uτ huτ φ
  have h0 : ∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), 0 < restartLife ζ T ω ∧
      ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < restartLife ζ T ω} ∧ W' 0 ω = 0 ∧
      (∀ i, VL' i 0 ω = VL i (T ω₀) ω₀ - W (T ω₀) ω₀) ∧ ∀ j, VR' j 0 ω = VR j (T ω₀) ω₀ - W (T ω₀) ω₀ := by
    filter_upwards [hE'.2.2.2.2, hag] with ω hp hω
    exact ⟨tsub_pos_iff_lt.2 hω.1, hp.2.2.2.1, hp.1, hp.2.1, hp.2.2.1⟩
  refine ⟨𝓖, W', VL', VR', B', restartLife ζ T, ?_, ?_⟩
  · exact isOptionalHullCoupling_of_dyadic hE' hh'
      (fun u₀ hu₀ => Lemma71J.isZBGFFProcess_of_isCouplingCharFun hcf hh' h0 hu₀)
      (bheProc κ ρL ρR W' VL' VR') (fun ω s => isBoundedHarmonicExtension_bheProc ω s) hdy
      (fun hX'' τ hτ hτζ => hloc0 hTζ W' VL' VR' hX'' hagR τ hτ hτζ)
  · filter_upwards [hagR] with ω hω
    exact ⟨rfl, hω⟩

end Main

end DomainMarkov

end Restart

end InteractingSLE
