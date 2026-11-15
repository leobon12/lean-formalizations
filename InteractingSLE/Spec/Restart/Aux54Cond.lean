/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Ext
import InteractingSLE.Spec.Restart.StoppedK2Kernel
import InteractingSLE.Spec.Restart.DomainMarkovAux79
import InteractingSLE.Spec.Supplement.Aux10FullClock
import InteractingSLE.Spec.Sec7.Lemma71BStop

/-!
# Aux. lemma 54 for general words, part 5: the conditional-law clause on the extension

Packet PROVE-AUX54. On a record extension `E` the driving process is the reference's, read through the second factor,
and the field is the stopped coupling's, read through the first. The frozen conditional-law clause on `E` follows
(`DomainMarkov.isOptionalHullCoupling_of_dyadic`) from the protected-kernel law at the dyadic times
(`DomainMarkov.IsDyadicSampled`), which splits at the stop:

* before the stop (`q < V₀`), an event of the extension's driving filtration at `q` is almost surely the first-factor
  preimage of an event of the stopped coupling's driving filtration at `q` before its stop, and the clause of the
  stopped coupling at `q ∧ V` gives the identity (specification p. 246: "For a stop that may occur before … `S`, split
  into the two stopped-history-measurable events and apply the corresponding pre-`S` … identity");
* after the stop (`V₀ ≤ q`), a test function avoiding the hull at `q` avoids the recorded hull, where the two fields
  agree, and the reference's clause at `q` gives the identity.

This file proves:

* `setIntegral_cfAt_of_ohc`: the identity at a deterministic time for any optional hull coupling (along an announcing
  sequence of the lifetime), with the almost everywhere measurability of the right-hand side.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4 StoppedExtendWF Coupling DomainMarkov

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The clause of an optional hull coupling at a deterministic time -/

section Det

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The protected-kernel law of an optional hull coupling at a deterministic time `q`**, on every event of the
driving filtration at `q` inside the avoidance event, with the almost everywhere measurability of `cfAt` there: the
frozen clause at `q ∧ Tₙ`, `Tₙ` announcing `ζ`. -/
theorem setIntegral_cfAt_of_ohc (hκ : 0 < κ) {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[drivingFiltration P hX q] A)
    (hAav : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ avoidSet W ζ ψ q) :
    AEStronglyMeasurable (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 fun _ => q) (P.restrict A) ∧
      ∫ ω in A, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P =
        ∫ ω in A, cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω ∂P := by
  classical
  obtain ⟨hE, hh, -, hX', hcl⟩ := hC
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) with hfdef
  set g : Ω → ℂ := cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 fun _ => q with hgdef
  have hfi : Integrable f P := LocalExt.integrable_cexp_field hh ψ
  have hAm : MeasurableSet A := (drivingFiltration P hX).le q _ hA
  have hpath := hE.2.2.2.2
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · have hA0 : P A = 0 := by
      have hn : ∀ᵐ ω ∂P, ¬ ((q : ℝ≥0∞) < ζ ω) := by
        filter_upwards [hpath] with ω hp hq
        obtain ⟨h0, h1, h2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, -, -⟩ := hp
        refine h17 0 (lt_of_le_of_lt zero_le hq) ?_
        rw [h0, show (fun i => VL i 0 ω) = xL from funext h1, show (fun i => VR i 0 ω) = xR from funext h2]
        exact hseed
      have hAz : ∀ᵐ ω ∂P, ω ∉ A := by
        filter_upwards [hn, hAav] with ω h1 h2 hωA
        exact h1 (h2 hωA).1
      have h' := ae_iff.1 hAz
      simp only [not_not] at h'
      exact h'
    have hr : P.restrict A = 0 := Measure.restrict_eq_zero.2 hA0
    refine ⟨by rw [hr]; exact aestronglyMeasurable_zero_measure _, ?_⟩
    rw [hr, integral_zero_measure, integral_zero_measure]
  obtain ⟨T, ⟨hTs, hTm, hTζ, hTex⟩, -⟩ := hE.exists_isAnnouncingSeq_drivingFiltration hκ hseed hX
  set An : ℕ → Set Ω := fun n => A ∩ {ω | ((q : ℝ≥0) : WithTop ℝ≥0) ≤ (T n ω : WithTop ℝ≥0)} with hAndef
  have hτ : ∀ n, IsStoppingTime (drivingFiltration P hX)
      fun ω => min ((q : ℝ≥0) : WithTop ℝ≥0) (T n ω : WithTop ℝ≥0) := fun n =>
    (isStoppingTime_const (drivingFiltration P hX) q).min (hTs n)
  have hAn : ∀ n, MeasurableSet[(hτ n).measurableSpace] (An n) := fun n =>
    IsStoppingTime.measurableSet_inter_le (isStoppingTime_const _ q) (hTs n) A
      (by rw [IsStoppingTime.measurableSpace_const]; exact hA)
  have hAnm : ∀ n, MeasurableSet (An n) := fun n => (hτ n).measurableSpace_le _ (hAn n)
  have hpiece : ∀ n, ∀ᵐ ω ∂P, ω ∈ An n → (P[f | (hτ n).measurableSpace]) ω = g ω := by
    intro n
    have hcl' := (hcl _ (hτ n) (by
      filter_upwards [hTζ n] with ω hω
      exact lt_of_le_of_lt (min_le_right _ _) hω)).2
      (fun ω => bheProc κ ρL ρR W VL VR ω ((min ((q : ℝ≥0) : WithTop ℝ≥0) (T n ω : WithTop ℝ≥0)).untopD 0))
      (fun ω => isBoundedHarmonicExtension_bheProc ω _) ψ
    filter_upwards [hcl', hAav] with ω h1 hav hω
    have hu : (min ((q : ℝ≥0) : WithTop ℝ≥0) (T n ω : WithTop ℝ≥0)).untopD 0 = q := by
      rw [min_eq_left hω.2]; rfl
    rw [h1 (by rw [hu]; exact (hav hω.1).2), hu]
    simp only [hgdef, cfAt]
    congr 1
    push_cast
    ring
  have hint : ∀ n, ∫ ω in An n, f ω ∂P = ∫ ω in An n, g ω ∂P := by
    intro n
    rw [← setIntegral_condExp (hτ n).measurableSpace_le hfi (hAn n)]
    exact setIntegral_congr_ae (hAnm n) (hpiece n)
  have hcover : (⋃ n, An n) =ᵐ[P] A := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · have : (⋃ n, An n) \ A = ∅ := Set.sdiff_eq_empty.2 (iUnion_subset fun n => inter_subset_left)
      rw [this, measure_empty]
    · rw [← nonpos_iff_eq_zero, ← ae_iff.mp (show ∀ᵐ ω ∂P, ω ∈ A → ω ∈ ⋃ n, An n from by
        filter_upwards [hTex, hAav] with ω hex hav hωA
        obtain ⟨n, hn⟩ := hex q (hav hωA).1
        exact mem_iUnion.2 ⟨n, hωA, WithTop.coe_le_coe.2 hn⟩)]
      refine measure_mono fun ω hω => ?_
      simp only [Set.mem_sdiff, mem_ofPred_eq, not_imp] at hω ⊢
      exact hω
  have hgm : AEStronglyMeasurable g (P.restrict A) := by
    rw [← Measure.restrict_congr_set hcover, aestronglyMeasurable_iUnion_iff]
    intro n
    have hc : AEStronglyMeasurable (P[f | (hτ n).measurableSpace]) (P.restrict (An n)) :=
      (stronglyMeasurable_condExp.mono (hτ n).measurableSpace_le).aestronglyMeasurable
    refine hc.congr ?_
    rw [EventuallyEq, ae_restrict_iff' (hAnm n)]
    exact hpiece n
  have hgb : ∀ᵐ ω ∂P.restrict A, ‖g ω‖ ≤ 1 := by
    rw [ae_restrict_iff' hAm]
    filter_upwards [hpath, hAav] with ω hp hav hωA
    exact Aux79.norm_cfAt_le_one_of_isForceReg _ ψ (Aux79.isForceReg_of_isIntegratedSLEPath hp) (r := fun _ => q)
      (hav hωA).1 (hav hωA).2
  have hgi : IntegrableOn g A P := Integrable.mono' (integrable_const (1 : ℝ)) hgm hgb
  have hmono : Monotone An := fun n k hnk ω hω => ⟨hω.1, hω.2.trans (WithTop.coe_le_coe.2 (hTm ω hnk))⟩
  have L1 := tendsto_setIntegral_of_monotone (μ := P) hAnm hmono hfi.integrableOn
  have L2 := tendsto_setIntegral_of_monotone (μ := P) hAnm hmono
    (hgi.mono_set (iUnion_subset fun n => inter_subset_left))
  simp_rw [hint] at L1
  refine ⟨hgm, ?_⟩
  rw [← setIntegral_congr_set hcover, ← setIntegral_congr_set hcover]
  exact tendsto_nhds_unique L1 L2

end Det

/-! ### Agreement on a record extension -/

section Agree

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {V₀ ζ₀ : Ω₀ → ℝ≥0∞}

/-- **On a record extension the driving states agree up to the stop** (before the reference's lifetime). -/
theorem IsRecExt.ae_agree {P : Measure Ω} {P₀ : Measure Ω₀} {A : HistorySpace nL nR → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens} {E : Measure (Ω × Ω₀)}
    (hE : IsRecExt P P₀ A h (killedHistory W VL VR V) h₀ (killedHistory W₀ VL₀ VR₀ V₀) E)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω} ∧
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ContinuousOn (dState W VL VR ω) (Iic T)) ∧
      dState W VL VR ω 0 = initVal xL xR)
    (hc₀ : ∀ᵐ ω₀ ∂P₀, ContinuousOn (dState W₀ VL₀ VR₀ ω₀) {t | (t : ℝ≥0∞) < ζ₀ ω₀} ∧
      dState W₀ VL₀ VR₀ ω₀ 0 = initVal xL xR)
    (hV₀ζ : ∀ ω₀, V₀ ω₀ ≤ ζ₀ ω₀) :
    ∀ᵐ p ∂E, V p.1 = V₀ p.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 → (t : ℝ≥0∞) < ζ₀ p.2 →
      dState W VL VR p.1 t = dState W₀ VL₀ VR₀ p.2 t := by
  obtain ⟨hfst, hsnd, hkh, -, -⟩ := hE
  have h1 : ∀ᵐ p ∂E, ContinuousOn (dState W VL VR p.1) {t | (t : ℝ≥0∞) < V p.1} ∧
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = V p.1 → ContinuousOn (dState W VL VR p.1) (Iic T)) ∧
      dState W VL VR p.1 0 = initVal xL xR := by
    rw [← hfst] at hc
    exact ae_of_ae_map measurable_fst.aemeasurable hc
  have h2 : ∀ᵐ p ∂E, ContinuousOn (dState W₀ VL₀ VR₀ p.2) {t | (t : ℝ≥0∞) < ζ₀ p.2} ∧
      dState W₀ VL₀ VR₀ p.2 0 = initVal xL xR := by
    rw [← hsnd] at hc₀
    exact ae_of_ae_map measurable_snd.aemeasurable hc₀
  filter_upwards [hkh, h1, h2] with p hk ⟨hf, hfv, hf0⟩ ⟨hg, hg0⟩
  obtain ⟨hVV, hsamp⟩ := of_killedHistory_eq hk
  refine ⟨hVV, fun t htv htζ => ?_⟩
  refine eq_of_dyadic_eq hf hfv hg (hVV ▸ hV₀ζ p.2) (hf0.trans hg0.symm) (fun q hq => ?_) htv htζ
  obtain ⟨e1, e2, e3⟩ := hsamp q hq
  simp only [dState, e1, Prod.mk.injEq, true_and]
  exact ⟨funext e2, funext e3⟩

end Agree

/-! ### Events of the extension's driving filtration -/

section Events

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀}
  {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞}

/-- **The killed driving filtration of a process read through `Prod.snd`** is the pullback of the original one. -/
theorem killedDrivingFiltration_snd (hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀)
    (hX : IsMeasurableKilledDriving (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2)
      (fun j t p => VR₀ j t p.2) fun p => ζ₀ p.2) (t : ℝ≥0) :
    killedDrivingFiltration hX t = (killedDrivingFiltration hX₀ t).comap Prod.snd := by
  show MeasurableSpace.generateFrom _ = (MeasurableSpace.generateFrom _).comap Prod.snd
  rw [MeasurableSpace.comap_generateFrom]
  congr 1
  ext S
  constructor
  · rintro ⟨r, hr, B, hB, rfl⟩
    exact ⟨_, ⟨r, hr, B, hB, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨r, hr, B, hB, rfl⟩, rfl⟩
    exact ⟨r, hr, B, hB, rfl⟩

/-- **Every event of the null-augmented driving filtration of the extension at `q`** is almost surely the preimage of
an event of the reference's killed driving filtration at `q`. -/
theorem exists_snd_of_nullAugmented {E : Measure (Ω × Ω₀)} (hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀)
    (hX : IsMeasurableKilledDriving (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2)
      (fun j t p => VR₀ j t p.2) fun p => ζ₀ p.2) {q : ℝ≥0} {A : Set (Ω × Ω₀)}
    (hA : MeasurableSet[Ito.nullAugmented (killedDrivingFiltration hX) E q] A) :
    ∃ A₀ : Set Ω₀, MeasurableSet[killedDrivingFiltration hX₀ q] A₀ ∧ A =ᵐ[E] Prod.snd ⁻¹' A₀ := by
  obtain ⟨A₁, hA₁, hAA₁⟩ := Ito.exists_ae_eq_of_measurableSet_nullAugmented hA
  rw [killedDrivingFiltration_snd hX₀ hX q] at hA₁
  obtain ⟨A₀, hA₀, rfl⟩ := hA₁
  exact ⟨A₀, hA₀, hAA₁⟩

/-- **Before the stop, the extension's driving events are the stopped coupling's** (Doob–Dynkin through the agreement
of the states before the stop): every event `A₀` of the reference's killed driving filtration at `q`, read on `E` and
intersected with `{q < V₀}`, is almost surely the first-factor preimage of an event of the stopped coupling's killed
driving filtration at `q`, intersected with `{q < V₀}`. -/
theorem exists_pre_transfer {E : Measure (Ω × Ω₀)} (hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀)
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR V) {V₀ : Ω₀ → ℝ≥0∞} (hV₀ζ : ∀ ω₀, V₀ ω₀ ≤ ζ₀ ω₀)
    (hag : ∀ᵐ p ∂E, V p.1 = V₀ p.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V p.1 →
      dState W VL VR p.1 t = dState W₀ VL₀ VR₀ p.2 t)
    (q : ℝ≥0) {A₀ : Set Ω₀} (hA₀ : MeasurableSet[killedDrivingFiltration hX₀ q] A₀) :
    ∃ A' : Set Ω, MeasurableSet[killedDrivingFiltration hX q] A' ∧
      Prod.snd ⁻¹' A₀ ∩ {p : Ω × Ω₀ | (q : ℝ≥0∞) < V₀ p.2} =ᵐ[E]
        Prod.fst ⁻¹' A' ∩ {p : Ω × Ω₀ | (q : ℝ≥0∞) < V₀ p.2} := by
  set pre : Set (Ω × Ω₀) := {p | (q : ℝ≥0∞) < V₀ p.2} with hpre
  refine MeasurableSpace.generateFrom_induction _
    (fun A₀ _ => ∃ A' : Set Ω, MeasurableSet[killedDrivingFiltration hX q] A' ∧
      Prod.snd ⁻¹' A₀ ∩ pre =ᵐ[E] Prod.fst ⁻¹' A' ∩ pre) ?_ ?_ ?_ ?_ A₀ hA₀
  · rintro _ ⟨r, hr, B, hB, rfl⟩ -
    refine ⟨{ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ B},
      MeasurableSpace.measurableSet_generateFrom ⟨r, hr, B, hB, rfl⟩, ?_⟩
    filter_upwards [hag] with p ⟨hVV, hst⟩
    apply propext
    simp only [hpre, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨-, hB'⟩, hq⟩
      have hr' : (r : ℝ≥0∞) < V p.1 := hVV ▸ lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hq
      refine ⟨⟨hr', ?_⟩, hq⟩
      have := hst r hr'
      simp only [dState] at this
      rw [this]
      exact hB'
    · rintro ⟨⟨hr', hB'⟩, hq⟩
      refine ⟨⟨lt_of_lt_of_le (hVV ▸ hr') (hV₀ζ p.2), ?_⟩, hq⟩
      have := hst r hr'
      simp only [dState] at this
      rw [← this]
      exact hB'
  · exact ⟨∅, @MeasurableSet.empty _ (killedDrivingFiltration hX q), by simp⟩
  · rintro t - ⟨A', hA', hAA'⟩
    refine ⟨A'ᶜ, hA'.compl, ?_⟩
    filter_upwards [hAA'] with p hp
    have hp' : (p.2 ∈ t ∧ p ∈ pre) ↔ (p.1 ∈ A' ∧ p ∈ pre) := Iff.of_eq hp
    apply propext
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (hp'.2 ⟨h, h2⟩).1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (hp'.1 ⟨h, h2⟩).1, h2⟩
  · rintro sA - hind
    choose A' hA' hAA' using hind
    refine ⟨⋃ n, A' n, MeasurableSet.iUnion hA', ?_⟩
    filter_upwards [ae_all_iff.2 hAA'] with p hp
    have hp' : ∀ n, (p.2 ∈ sA n ∧ p ∈ pre) ↔ (p.1 ∈ A' n ∧ p ∈ pre) := fun n => Iff.of_eq (hp n)
    apply propext
    simp only [mem_inter_iff, mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨⟨n, hn⟩, h2⟩
      exact ⟨⟨n, ((hp' n).1 ⟨hn, h2⟩).1⟩, h2⟩
    · rintro ⟨⟨n, hn⟩, h2⟩
      exact ⟨⟨n, ((hp' n).2 ⟨hn, h2⟩).1⟩, h2⟩

end Events

/-! ### After the stop: the recorded hull lies in the later hulls -/

section Hull

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω₀ : Type*}
  {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {ζ₀ V₀ : Ω₀ → ℝ≥0∞}

/-- **The recorded hull at a stop before the lifetime lies in the hull at every later time before the lifetime**
(the recorded hull is the closure in `ℍ` of the hull at the stop, which is relatively closed in `ℍ`). -/
theorem recHull_subset_fwdHull {ω₀ : Ω₀} {q : ℝ≥0}
    (hc : ContinuousOn (dState W₀ VL₀ VR₀ ω₀) {t | (t : ℝ≥0∞) < ζ₀ ω₀})
    (h0 : dState W₀ VL₀ VR₀ ω₀ 0 = initVal xL xR)
    (hnt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω₀ →
      ¬ ForceWord.ThresholdCondition ρL ρR (W₀ t ω₀) (fun i => VL₀ i t ω₀) (fun j => VR₀ j t ω₀))
    (hVq : V₀ ω₀ ≤ q) (hqζ : (q : ℝ≥0∞) < ζ₀ ω₀) :
    recHull ρL ρR xL xR (killedHistory W₀ VL₀ VR₀ V₀ ω₀) ⊆ fwdHull (fun s : ℝ => W₀ s.toNNReal ω₀) q := by
  have hVtop : V₀ ω₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hVq
  set T : ℝ≥0 := (V₀ ω₀).toNNReal with hTdef
  have hT : (T : ℝ≥0∞) = V₀ ω₀ := ENNReal.coe_toNNReal hVtop
  have hTq : T ≤ q := by rw [← ENNReal.coe_le_coe, hT]; exact hVq
  have hcT : ContinuousOn (dState W₀ VL₀ VR₀ ω₀) (Iic T) := hc.mono fun t ht =>
    show (t : ℝ≥0∞) < ζ₀ ω₀ from lt_of_le_of_lt (ENNReal.coe_le_coe.2 (le_trans ht hTq)) hqζ
  have hstop := stopVal_killedHistory (xL := xL) (xR := xR) hT hcT h0
  have hnm : ¬ recMask ρL ρR xL xR (killedHistory W₀ VL₀ VR₀ V₀ ω₀) := by
    rintro (h1 | h1)
    · exact hVtop h1
    · rw [hstop] at h1
      exact hnt T (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hTq) hqζ) h1
  obtain ⟨T', hqT', hT'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqζ
  have hqT : q < T' := by exact_mod_cast hqT'
  have hW' : ContinuousOn (fun t => W₀ t ω₀) (Iic T') := continuous_fst.comp_continuousOn (hc.mono fun t ht =>
    show (t : ℝ≥0∞) < ζ₀ ω₀ from lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hT'ζ)
  rw [recHull_of_not_mask hnm, regHull_recH_killedHistory hT hcT h0 (lt_of_le_of_lt hTq hqT) hW']
  set w : ℝ → ℝ := fun r => W₀ (min r.toNNReal T') ω₀ with hwdef
  have hwc : Continuous w :=
    (hW'.comp_continuous (continuous_id.min continuous_const) fun t => min_le_right t T').comp
      continuous_real_toNNReal
  have hag : ∀ r ∈ Icc (0 : ℝ) T', (fun s : ℝ => W₀ s.toNNReal ω₀) r = w r := fun r hr => by
    simp only [hwdef]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  have e1 : fwdHull (fun s : ℝ => W₀ s.toNNReal ω₀) T = fwdHull w T :=
    InteractingSLE.fwdHull_eq_of_eqOn T.coe_nonneg (by exact_mod_cast lt_of_le_of_lt hTq hqT) hag
  have e2 : fwdHull (fun s : ℝ => W₀ s.toNNReal ω₀) q = fwdHull w q :=
    InteractingSLE.fwdHull_eq_of_eqOn q.coe_nonneg (by exact_mod_cast hqT) hag
  rw [e1, e2]
  intro z hz
  exact QuantumZipper.fwdHull_mono.1 (show (T : ℝ) ≤ q by exact_mod_cast hTq)
    (Aux10.closure_fwdHull_inter_H hwc T.coe_nonneg hz)

end Hull

/-! ### The protected-kernel law on the extension at the dyadic times -/

section Dyadic

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀}

/-- **The protected-kernel law of the original field on a record extension, at the dyadic times** (for the driving
process of the reference read through `Prod.snd`): before the reference's rule stop the stopped coupling's clause at
`q ∧ V`, after it the reference's clause. -/
theorem isDyadicSampled_ext (hκ : 0 < κ)
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞}
    {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (href : WholeFieldStopped.IsFamilyRef κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    {E : Measure (Ω × Ω₀)} [IsProbabilityMeasure E]
    (hE : IsRecExt P P₀ (recHull ρL ρR xL xR) h (killedHistory W VL VR V) h₀
      (killedHistory W₀ VL₀ VR₀ (ruleStop R W₀ VL₀ VR₀ ζ₀)) E)
    (hXE : IsMeasurableKilledDriving (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2)
      (fun j t p => VR₀ j t p.2) fun p => ζ₀ p.2) :
    IsDyadicSampled κ (fun t (p : Ω × Ω₀) => W₀ t p.2)
      (bheProc κ ρL ρR (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2) (fun j t p => VR₀ j t p.2))
      E hXE (fun p => h p.1) := by
  classical
  intro ψ n k A hA hAav
  set q : ℝ≥0 := dyT n k with hqdef
  set V₀ : Ω₀ → ℝ≥0∞ := ruleStop R W₀ VL₀ VR₀ ζ₀ with hV₀def
  have hV₀ζ : ∀ ω₀, V₀ ω₀ ≤ ζ₀ ω₀ := ruleStop_le R
  set g : Ω × Ω₀ → ℂ := cfAt κ (fun t (p : Ω × Ω₀) => W₀ t p.2)
    (bheProc κ ρL ρR (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2) (fun j t p => VR₀ j t p.2))
    ψ 1 (fun _ => q) with hgdef
  have hE' := hE
  obtain ⟨hfst, hsnd, hkh, hfr, -⟩ := hE'
  obtain ⟨hEv, hcont, hh, -, hX, hcl⟩ := hSC
  have hC₀ := href.isOptionalHullCoupling hκ
  have hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀ := IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₀.1
  have hh₀ := hC₀.2.1
  have hfi : Integrable (fun p : Ω × Ω₀ => Complex.exp (Complex.I * (h p.1 ψ : ℂ))) E :=
    LocalExt.integrable_cexp_field (hh.comp measurable_fst) ψ
  have hAm : MeasurableSet A := (Ito.nullAugmented (killedDrivingFiltration hXE) E).le q _ hA
  -- path facts
  have hp₀ : ∀ᵐ ω₀ ∂P₀, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W₀ t ω₀) (fun i t => VL₀ i t ω₀)
      (fun i t => VR₀ i t ω₀) (fun t => B₀ t ω₀) (ζ₀ ω₀) := hC₀.1.2.2.2.2
  have hc₀ : ∀ᵐ ω₀ ∂P₀, ContinuousOn (dState W₀ VL₀ VR₀ ω₀) {t | (t : ℝ≥0∞) < ζ₀ ω₀} ∧
      dState W₀ VL₀ VR₀ ω₀ 0 = initVal xL xR := by
    filter_upwards [hC₀.1.isSLEEvolutionUpTo.ae_path] with ω₀ hp
    refine ⟨continuousOn_state_of_isSLEPathUpTo hp, ?_⟩
    simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
    exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
  have hc : ∀ᵐ ω ∂P, ContinuousOn (dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω} ∧
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ContinuousOn (dState W VL VR ω) (Iic T)) ∧
      dState W VL VR ω 0 = initVal xL xR := by
    filter_upwards [hEv.ae_path, hcont] with ω hp hcω
    refine ⟨continuousOn_state_of_isSLEPathUpTo hp, hcω, ?_⟩
    simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
    exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
  have hpE : ∀ᵐ p ∂E, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W₀ t p.2) (fun i t => VL₀ i t p.2)
      (fun i t => VR₀ i t p.2) (fun t => B₀ t p.2) (ζ₀ p.2) := by
    rw [← hsnd] at hp₀
    exact ae_of_ae_map measurable_snd.aemeasurable hp₀
  have hcE : ∀ᵐ p ∂E, ContinuousOn (dState W₀ VL₀ VR₀ p.2) {t | (t : ℝ≥0∞) < ζ₀ p.2} ∧
      dState W₀ VL₀ VR₀ p.2 0 = initVal xL xR := by
    rw [← hsnd] at hc₀
    exact ae_of_ae_map measurable_snd.aemeasurable hc₀
  have hag := hE.ae_agree hc hc₀ hV₀ζ
  have hag' : ∀ᵐ p ∂E, V p.1 = V₀ p.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V p.1 →
      dState W VL VR p.1 t = dState W₀ VL₀ VR₀ p.2 t := by
    filter_upwards [hag] with p ⟨hVV, hst⟩
    exact ⟨hVV, fun t ht => hst t ht.le (lt_of_lt_of_le ht (hVV ▸ hV₀ζ p.2))⟩
  -- the bound on `g` on `A`
  have hreg : ∀ᵐ p ∂E, Aux79.IsForceReg (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2)
      (fun j t p => VR₀ j t p.2) (fun p => ζ₀ p.2) p := by
    filter_upwards [hpE] with p hp
    exact ⟨hp.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, fun t ht =>
      ⟨hp.2.2.2.2.2.2.2.1 t ht, hp.2.2.2.2.2.2.2.2.1 t ht⟩⟩
  have hgb : ∀ᵐ p ∂E, p ∈ A → ‖g p‖ ≤ 1 := by
    filter_upwards [hreg] with p hrp hpA
    exact Aux79.norm_cfAt_le_one_of_isForceReg (κ := κ) _ ψ hrp (r := fun _ => q) (hAav hpA).1 (hAav hpA).2
  -- the two pieces
  set pre : Set (Ω × Ω₀) := {p | (q : ℝ≥0∞) < V₀ p.2} with hpredef
  set post : Set (Ω × Ω₀) := {p | (V₀ p.2 : WithTop ℝ≥0) ≤ ((q : ℝ≥0) : WithTop ℝ≥0)} with hpostdef
  have hV₀m : Measurable V₀ := (hRm.comp (measurable_killedHistory hX₀)).min (measurable_lifetime hX₀)
  have hprem : MeasurableSet pre := measurableSet_lt measurable_const (hV₀m.comp measurable_snd)
  have hpostc : post = preᶜ := by
    ext p
    simp only [hpostdef, hpredef, mem_ofPred_eq, mem_compl_iff, not_lt]
    rfl
  have hpostm0 : MeasurableSet post := by rw [hpostc]; exact hprem.compl
  -- the event `A` through the reference
  obtain ⟨A₀, hA₀, hAA₀⟩ := exists_snd_of_nullAugmented hX₀ hXE hA
  /- ### Before the stop -/
  obtain ⟨A', hA', hpreT⟩ := exists_pre_transfer hX₀ hX hV₀ζ hag' q hA₀
  set D : Set Ω := A' ∩ {ω | (q : ℝ≥0∞) < V ω} with hDdef
  have hApre : A ∩ pre =ᵐ[E] Prod.fst ⁻¹' D := by
    have h1 : A ∩ pre =ᵐ[E] Prod.snd ⁻¹' A₀ ∩ pre := hAA₀.inter (EventuallyEq.refl _ pre)
    have h2 : Prod.fst ⁻¹' A' ∩ pre =ᵐ[E] Prod.fst ⁻¹' D := by
      filter_upwards [hag'] with p ⟨hVV, _⟩
      apply propext
      simp only [hDdef, hpredef, mem_inter_iff, mem_preimage, mem_ofPred_eq, hVV]
    exact h1.trans (hpreT.trans h2)
  have hV := isStoppingTime_lifetime_driving (P := P) hX
  have hτ := hV.min (isStoppingTime_const (drivingFiltration P hX) q)
  have hDq : MeasurableSet[drivingFiltration P hX q] D := by
    refine (Ito.le_usualAugmentation (killedDrivingFiltration hX) P q _ hA').inter ?_
    have e : {ω | (q : ℝ≥0∞) < V ω} = {ω | (V ω : WithTop ℝ≥0) ≤ ((q : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
      ext ω
      show ((q : ℝ≥0∞) < V ω) ↔ ¬ ((V ω : WithTop ℝ≥0) ≤ ((q : ℝ≥0) : WithTop ℝ≥0))
      exact not_le.symm
    rw [e]
    exact (hV q).compl
  have hDτ : MeasurableSet[hτ.measurableSpace] D := by
    refine ⟨le_iSup (fun t => drivingFiltration P hX t) q _ hDq, fun i => ?_⟩
    by_cases hqi : q ≤ i
    · exact ((drivingFiltration P hX).mono hqi _ hDq).inter (hτ i)
    · convert @MeasurableSet.empty _ (drivingFiltration P hX i) using 1
      refine Set.eq_empty_of_forall_notMem fun ω hω => hqi ?_
      obtain ⟨⟨-, hqV⟩, hτi⟩ := hω
      have hτi' : min (V ω : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0) ≤ ((i : ℝ≥0) : WithTop ℝ≥0) := hτi
      have hqV' : ((q : ℝ≥0) : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0) := hqV
      exact WithTop.coe_le_coe.1 (le_trans (le_min hqV'.le le_rfl) hτi')
  have hDm : MeasurableSet D := hτ.measurableSpace_le _ hDτ
  set f₁ : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) with hf₁def
  have hf₁m : Measurable f₁ := Complex.continuous_exp.measurable.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp hh)))
  have hf₁i : Integrable f₁ P := LocalExt.integrable_cexp_field hh ψ
  set c : Ω → ℂ := P[f₁ | hτ.measurableSpace] with hcdef
  have hcm : StronglyMeasurable c := stronglyMeasurable_condExp.mono hτ.measurableSpace_le
  have hcl' := (hcl _ hτ (Eventually.of_forall fun ω => ⟨min_le_left _ _,
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)⟩)).2
    (fun ω => bheProc κ ρL ρR W VL VR ω ((min (V ω : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0))
    (fun ω => isBoundedHarmonicExtension_bheProc ω _) ψ
  have hclE : ∀ᵐ p ∂E, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal p.1)
      ((min (V p.1 : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) →
      c p.1 = Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal p.1)
          ((min (V p.1 : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)
          (bheProc κ ρL ρR W VL VR p.1 ((min (V p.1 : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0)) z *
            ψ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal p.1)
          ((min (V p.1 : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) ψ : ℝ) : ℂ)) := by
    have h2 : ∀ᵐ ω ∂(E.map Prod.fst), Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((min (V ω : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) →
        c ω = Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
            ((min (V ω : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)
            (bheProc κ ρL ρR W VL VR ω ((min (V ω : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0)) z *
              ψ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
            ((min (V ω : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) ψ : ℝ) : ℂ)) := by
      rw [hfst]; exact hcl'
    exact ae_of_ae_map measurable_fst.aemeasurable h2
  have hcg : ∀ᵐ p ∂E, p ∈ A ∩ pre → c p.1 = g p := by
    filter_upwards [hclE, hag'] with p h1 ⟨hVV, hst⟩ hp
    have hq : (q : ℝ≥0∞) < V p.1 := hVV ▸ hp.2
    have hu : (min (V p.1 : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0)).untopD 0 = q := by
      have hq' : ((q : ℝ≥0) : WithTop ℝ≥0) < (V p.1 : WithTop ℝ≥0) := hq
      have e : min (V p.1 : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0) = ((q : ℝ≥0) : WithTop ℝ≥0) := min_eq_right hq'.le
      exact (congrArg (WithTop.untopD 0) e).trans rfl
    have hW : ∀ t : ℝ≥0, (t : ℝ≥0∞) < V p.1 → W₀ t p.2 = W t p.1 := fun t ht =>
      (congrArg Prod.fst (hst t ht)).symm
    have hhull := Exist.Staged.fwdHull_eq_of_agree (W := fun t => W t p.1) (W' := fun t => W₀ t p.2) hW hq
    have hEq := Exist.Staged.eqOn_Icc_of_agree (W := fun t => W t p.1) (W' := fun t => W₀ t p.2) hW hq
    have hdis : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal p.1) q) := by
      rw [← hhull]; exact (hAav hp.1).2
    rw [h1 (by rw [hu]; exact hdis), hu]
    have hb : bheProc κ ρL ρR W VL VR p.1 q = bheProc κ ρL ρR (fun t (p : Ω × Ω₀) => W₀ t p.2)
        (fun i t p => VL₀ i t p.2) (fun j t p => VR₀ j t p.2) p q := by
      have e := hst q hq
      simp only [dState, Prod.mk.injEq] at e
      obtain ⟨e1, e2, e3⟩ := e
      simp only [bheProc, e1]
      congr 1
      · funext i; rw [congrFun e2 i]
      · funext j; rw [congrFun e3 j]
    have hint : (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal p.1) (q : ℝ≥0)
        (bheProc κ ρL ρR W VL VR p.1 q) z * ψ z) =
        ∫ z, couplingMean κ (fun s : ℝ => W₀ s.toNNReal p.2) (q : ℝ≥0)
          (bheProc κ ρL ρR W VL VR p.1 q) z * ψ z := by
      congr 1
      funext z
      congr 1
      exact Sec7.Lemma71B.couplingMean_congr q.2 hEq κ _ z
    simp only [hgdef, cfAt]
    rw [← hb, hint, Exist.Staged.loewnerGreenEnergy_congr hEq]
    congr 1
    push_cast
    ring
  have hpre_eq : ∫ p in A ∩ pre, Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E = ∫ p in A ∩ pre, g p ∂E := by
    have e1 : ∫ p in A ∩ pre, Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E = ∫ ω in D, f₁ ω ∂P := by
      rw [setIntegral_congr_set hApre, ← hfst,
        setIntegral_map hDm hf₁m.aestronglyMeasurable measurable_fst.aemeasurable]
    have e3 : ∫ ω in D, c ω ∂P = ∫ p in A ∩ pre, c p.1 ∂E := by
      rw [setIntegral_congr_set hApre, ← hfst,
        setIntegral_map hDm hcm.aestronglyMeasurable measurable_fst.aemeasurable]
    rw [e1, ← setIntegral_condExp hτ.measurableSpace_le hf₁i hDτ, e3]
    exact setIntegral_congr_ae (hAm.inter hprem) hcg
  have hgpre : AEStronglyMeasurable g (E.restrict (A ∩ pre)) := by
    refine (hcm.comp_measurable measurable_fst).aestronglyMeasurable.congr ?_
    rw [EventuallyEq, ae_restrict_iff' (hAm.inter hprem)]
    exact hcg
  /- ### After the stop -/
  have hgffE : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ (p : Ω × Ω₀) => h₀ p.2 φ - ∫ z, u₀ z * φ z) E := by
    intro u₀ hu₀
    have h1 := href.2.2.1 u₀ hu₀
    rw [← hsnd] at h1
    exact Restart.isZBGFFProcess_comp measurable_snd h1
  have hCE := (href.comap hκ measurable_snd hsnd (hh₀.comp measurable_snd) hgffE
    (ae_of_all _ fun p => rfl)).isOptionalHullCoupling hκ
  have hcE' : ∀ᵐ p ∂E, ContinuousOn (dState (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun i t p => VL₀ i t p.2)
      (fun j t p => VR₀ j t p.2) p) {t | (t : ℝ≥0∞) < ζ₀ p.2} := hcE.mono fun p h => h.1
  have hVE := isStoppingTime_ruleStop (P := E) hXE hRm hRg hcE'
  have hpostE : MeasurableSet[drivingFiltration E hXE q] post := hVE q
  have hApostm : MeasurableSet[drivingFiltration E hXE q] (A ∩ post) :=
    (Ito.nullAugmented_le_usualAugmentation _ E q _ hA).inter hpostE
  obtain ⟨hgpost, hintpost⟩ := setIntegral_cfAt_of_ohc hκ hCE hXE ψ q hApostm
    (ae_of_all _ fun p hp => hAav hp.1)
  have hfpost : ∀ᵐ p ∂E, p ∈ A ∩ post →
      Complex.exp (Complex.I * (h p.1 ψ : ℂ)) = Complex.exp (Complex.I * (h₀ p.2 ψ : ℂ)) := by
    filter_upwards [hfr ψ, hkh, hpE, hcE] with p hr hk hp hcp hpp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, -, -⟩ := hp
    have hav := hAav hpp.1
    have hsub := recHull_subset_fwdHull (ρL := ρL) (ρR := ρR) (V₀ := V₀) hcp.1 hcp.2 h17 hpp.2 hav.1
    have hdis : Disjoint (tsupport ψ) (recHull ρL ρR xL xR (killedHistory W₀ VL₀ VR₀ V₀ p.2)) :=
      hav.2.mono_right hsub
    have hdis1 : Disjoint (tsupport ψ) (recHull ρL ρR xL xR (killedHistory W VL VR V p.1)) := by
      rw [hk]; exact hdis
    rw [fieldRecA_of_disjoint hdis1, fieldRecA_of_disjoint hdis] at hr
    rw [hr]
  have hpost_eq : ∫ p in A ∩ post, Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E = ∫ p in A ∩ post, g p ∂E := by
    rw [setIntegral_congr_ae (hAm.inter hpostm0) hfpost]
    exact hintpost
  /- ### Assembly -/
  show ∫ p in A, Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E = ∫ p in A, g p ∂E
  have hsplit : A = (A ∩ pre) ∪ (A ∩ post) := by
    rw [← inter_union_distrib_left, hpostc, union_compl_self, inter_univ]
  have hdisj : Disjoint (A ∩ pre) (A ∩ post) := by
    rw [hpostc]; exact Disjoint.mono inter_subset_right inter_subset_right disjoint_compl_right
  have hgbr : ∀ {S : Set (Ω × Ω₀)}, MeasurableSet S → S ⊆ A → ∀ᵐ p ∂E.restrict S, ‖g p‖ ≤ 1 := by
    intro S hS hSA
    rw [ae_restrict_iff' hS]
    filter_upwards [hgb] with p hp hpS using hp (hSA hpS)
  have hgipre : IntegrableOn g (A ∩ pre) E :=
    Integrable.mono' (integrable_const (1 : ℝ)) hgpre (hgbr (hAm.inter hprem) inter_subset_left)
  have hgipost : IntegrableOn g (A ∩ post) E :=
    Integrable.mono' (integrable_const (1 : ℝ)) hgpost (hgbr (hAm.inter hpostm0) inter_subset_left)
  rw [hsplit, setIntegral_union hdisj (hAm.inter hpostm0) hfi.integrableOn hfi.integrableOn,
    setIntegral_union hdisj (hAm.inter hpostm0) hgipre hgipost, hpre_eq, hpost_eq]

end Dyadic

end Aux54

end Restart

end InteractingSLE
