/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3StopAnnounce

/-!
# K2's inputs (S) and (L) pass to image laws and to laws conditioned on a time-zero event

Packet PROVE-Q3-REL4 (plumbing for step (C)). `HasRelSafe` (the remaining input `GB6RelSafeStatement`) is stated on
the canonical space under the image law conditioned on the record event of a type. The relative chain is naturally
proved on GB6's own probability space, for the filtration pulled back from the canonical one. This file transports:

* `setIntegral_cond_eq`, `ae_imp_of_ae_cond`; **`hasSafeLaw_cond`**, **`hasSafeMembers_cond`**: (S) and (L) with live
  event `S ∈ 𝓗₀` give (S) and (L) under `μ[|S]` with live event everything;
* **`hasSafeLaw_map`**, **`hasSafeMembers_map`**: (S) and (L) on a space, for the processes read through a
  measurable map `Φ` and the pulled-back filtration, give (S) and (L) under the image law (`cfAt` is measurable on
  the safe union, `DomainMarkov.measurable_safeU_indicator_cfAt_of_weak`, and the avoidance event lies in it);
* **`hasRelSafe_of_space`**: `HasRelSafe` for GB6's image law from (S), (L) and integrability on the space itself (the
  threshold bound stays on the canonical space).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (TestOn DistOn)
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Supp8.Q3Stop

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.FCDet Exist.StagedLaw Supp8.GB6.RelDrv
  Sec7.PocketTraversal

/-! ### Conditioning on a time-zero event -/

section Cond

variable {Y : Type*} [mY : MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ] {𝓗 : Filtration ℝ≥0 mY}
  {S : Set Y} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {ζ : Y → ℝ≥0∞} {W : ℝ≥0 → Y → ℝ}
  {VL : Fin nL → ℝ≥0 → Y → ℝ} {VR : Fin nR → ℝ≥0 → Y → ℝ} {X : Y → DistOn upperHalfPlaneOpens}

omit [IsFiniteMeasure μ] in
theorem setIntegral_cond_eq {D : Set Y} (hD : MeasurableSet D) (f : Y → ℂ) :
    ∫ y in D, f y ∂μ[|S] = ((μ S)⁻¹).toReal • ∫ y in D ∩ S, f y ∂μ := by
  unfold ProbabilityTheory.cond
  rw [Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hD]

theorem ae_imp_of_ae_cond (hS : MeasurableSet S) {p : Y → Prop} (h : ∀ᵐ y ∂μ[|S], p y) :
    ∀ᵐ y ∂μ, y ∈ S → p y := by
  have hc : μ[|S] {y | ¬p y} = 0 := ae_iff.1 h
  rw [cond_apply hS] at hc
  have h2 : μ (S ∩ {y | ¬p y}) = 0 := by
    rcases mul_eq_zero.1 hc with h0 | h0
    · exact absurd h0 (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
    · exact h0
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) h2
  simp only [mem_ofPred_eq, not_imp] at hy
  exact ⟨hy.1, hy.2⟩

/-- **(S) under the law conditioned on a time-zero live event.** -/
theorem hasSafeLaw_cond (hS : MeasurableSet[𝓗 0] S) (h : HasSafeLaw κ ρL ρR μ 𝓗 S ζ W VL VR X) :
    HasSafeLaw κ ρL ρR (μ[|S]) 𝓗 univ ζ W VL VR X := by
  have hSm : MeasurableSet S := 𝓗.le 0 _ hS
  intro ψ q D hD hDae
  have hDm : MeasurableSet D := 𝓗.le q _ hD
  have hDS : MeasurableSet[𝓗 q] (D ∩ S) := hD.inter (𝓗.mono (zero_le (a := q)) _ hS)
  have hae : ∀ᵐ ω ∂μ, ω ∈ D ∩ S → ω ∈ S ∧ ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [ae_imp_of_ae_cond hSm hDae] with ω hω hωDS
    exact ⟨hωDS.2, (hω hωDS.2 hωDS.1).2⟩
  rw [setIntegral_cond_eq hDm, setIntegral_cond_eq hDm, h ψ q (D ∩ S) hDS hae]

/-- **(L) under the law conditioned on a time-zero live event.** -/
theorem hasSafeMembers_cond (hS : MeasurableSet[𝓗 0] S) (h : HasSafeMembers μ 𝓗 S ζ W X) :
    HasSafeMembers (μ[|S]) 𝓗 univ ζ W X := by
  have hSm : MeasurableSet S := 𝓗.le 0 _ hS
  intro s Fb hFb D hD hDae f Ξ
  have hDm : MeasurableSet D := 𝓗.le s _ hD
  have hDS : MeasurableSet[𝓗 s] (D ∩ S) := hD.inter (𝓗.mono (zero_le (a := s)) _ hS)
  have hae : ∀ᵐ ω ∂μ, ω ∈ D ∩ S → ω ∈ S ∧ (s : ℝ≥0∞) < ζ ω ∧
      Disjoint (Coupling.ballsK Fb) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ)) := by
    filter_upwards [ae_imp_of_ae_cond hSm hDae] with ω hω hωDS
    obtain ⟨-, h1, h2⟩ := hω hωDS.2 hωDS.1
    exact ⟨hωDS.2, h1, h2⟩
  rw [setIntegral_cond_eq hDm, setIntegral_cond_eq hDm, h s Fb hFb (D ∩ S) hDS hae f Ξ, mul_smul_comm]

end Cond

/-! ### Image laws -/

section Map

variable {Ω Y : Type*} [mΩ : MeasurableSpace Ω] [mY : MeasurableSpace Y] {P : Measure Ω} {Φ : Ω → Y}
  {𝓗 : Filtration ℝ≥0 mY} {F : Set Y} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {ζ : Y → ℝ≥0∞}
  {W : ℝ≥0 → Y → ℝ} {VL : Fin nL → ℝ≥0 → Y → ℝ} {VR : Fin nR → ℝ≥0 → Y → ℝ} {X : Y → DistOn upperHalfPlaneOpens}

theorem measurable_cexp_apply (hX : Measurable X) (φ : TestOn upperHalfPlaneOpens) :
    Measurable fun y => Complex.exp (Complex.I * (X y φ : ℂ)) :=
  Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    ((LQGMetric.measurable_distOn_apply φ).comp hX)))

/-- **(S) passes to the image law.** -/
theorem hasSafeLaw_map (hΦ : Measurable Φ)
    (hweak : ∀ y, IsWeakPath (W · y) (fun i t => VL i t y) (fun j t => VR j t y) (ζ y))
    (hWa : AdaptedBefore 𝓗 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓗 ζ (VL i))
    (hVRa : ∀ j, AdaptedBefore 𝓗 ζ (VR j)) (hX : Measurable X)
    (h : HasSafeLaw κ ρL ρR P (Coupling.filtrationComap 𝓗 hΦ) (Φ ⁻¹' F) (fun ω => ζ (Φ ω))
      (fun t ω => W t (Φ ω)) (fun i t ω => VL i t (Φ ω)) (fun j t ω => VR j t (Φ ω)) (fun ω => X (Φ ω))) :
    HasSafeLaw κ ρL ρR (P.map Φ) 𝓗 F ζ W VL VR X := by
  intro ψ q D hD hDae
  have hDm : MeasurableSet D := 𝓗.le q _ hD
  have hD' : MeasurableSet[Coupling.filtrationComap 𝓗 hΦ q] (Φ ⁻¹' D) := ⟨D, hD, rfl⟩
  have hae' : ∀ᵐ ω ∂P, ω ∈ Φ ⁻¹' D → ω ∈ Φ ⁻¹' F ∧
      ω ∈ avoidSet (fun t ω => W t (Φ ω)) (fun ω => ζ (Φ ω)) ψ q :=
    ae_of_ae_map hΦ.aemeasurable hDae
  have hid := h ψ q (Φ ⁻¹' D) hD' hae'
  set g : Y → ℂ := (safeU W ζ univ ψ q).indicator (Coupling.cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 fun _ => q)
    with hgdef
  have hgm : Measurable g := (measurable_safeU_indicator_cfAt_of_weak (κ := κ) (ρL := ρL) (ρR := ρR) hweak hWa
    MeasurableSet.univ _ (fun y s => isBoundedHarmonicExtension_bheProc y s) hVLa hVRa ψ q).mono (𝓗.le q) le_rfl
  have h1 : ∫ y in D, Coupling.cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) y ∂(P.map Φ) =
      ∫ y in D, g y ∂(P.map Φ) := by
    refine setIntegral_congr_ae hDm ?_
    filter_upwards [hDae] with y hy hyD
    rw [hgdef, indicator_of_mem (mem_safeU_of_mem_avoidSet hweak ψ (mem_univ y) (hy hyD).2)]
  rw [setIntegral_map hDm (measurable_cexp_apply hX ψ).aestronglyMeasurable hΦ.aemeasurable, h1,
    setIntegral_map hDm hgm.aestronglyMeasurable hΦ.aemeasurable, hid]
  refine setIntegral_congr_ae (hΦ hDm) ?_
  filter_upwards [hae'] with ω hω hωD
  rw [hgdef, indicator_of_mem (mem_safeU_of_mem_avoidSet hweak ψ (mem_univ (Φ ω)) (hω hωD).2)]
  rfl

/-- **(L) passes to the image law.** -/
theorem hasSafeMembers_map (hΦ : Measurable Φ) (hX : Measurable X)
    (h : HasSafeMembers P (Coupling.filtrationComap 𝓗 hΦ) (Φ ⁻¹' F) (fun ω => ζ (Φ ω)) (fun t ω => W t (Φ ω))
      (fun ω => X (Φ ω))) :
    HasSafeMembers (P.map Φ) 𝓗 F ζ W X := by
  intro s Fb hFb D hD hDae f Ξ
  have hDm : MeasurableSet D := 𝓗.le s _ hD
  have hae' := ae_of_ae_map hΦ.aemeasurable hDae
  rw [setIntegral_map hDm (measurable_cexp_apply hX _).aestronglyMeasurable hΦ.aemeasurable,
    setIntegral_map hDm (measurable_cexp_apply hX _).aestronglyMeasurable hΦ.aemeasurable]
  exact h s Fb hFb (Φ ⁻¹' D) ⟨D, hD, rfl⟩ hae' f Ξ

end Map

/-! ### `HasRelSafe` from the space itself -/

section Space

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k : ℝ} {w : WordType}
  {β : RecData → BoundaryWord} {E : Set RecData} {rec : Ω → RecData} {Hc : Ω → DistOn upperHalfPlaneOpens}
  {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

theorem measurableSet_typeEvent_canonFilt (hβ : Measurable β) (hE : MeasurableSet E) :
    MeasurableSet[canonFilt 0] (typeEvent k w β E) :=
  canonRec_le_canonFilt 0 _ ⟨_, hE.inter ((measurable_wordType k).comp hβ (measurableSet_singleton w)), rfl⟩

theorem isWeakPath_canon (xL : CanonSpace → Fin w.1 → ℝ) (xR : CanonSpace → Fin w.2.1 → ℝ) (y : CanonSpace) :
    IsWeakPath (canonDrv · y) (fun i t => geomLW canonDrv xL i t y) (fun j t => geomRW canonDrv xR j t y)
      (canonStp y) := by
  have h := isForceReg_thr canonDrv_zero continuous_canonDrv xL xR canonStp y
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun t ht i => (h.2.2.2.2 t ht).1 i, fun t ht j => (h.2.2.2.2 t ht).2 j⟩

/-- **`HasRelSafe` for GB6's image law from the relative chain on the space itself.** With
`Φ ω = (record, relVar Hc R V)`: (S) and (L) on the space, for the processes read through `Φ` (the decoded relative
driver, which is `R` for a continuous version from `0`, the flowed marks of the typed word, the stop `V` and the chart
field `Hc`), in the filtration pulled back from `canonFilt`, with live event the record event of type `w`; the chart
field integrable; and the threshold bound under the conditioned image law. -/
theorem hasRelSafe_of_space (hβ : Measurable β) (hE : MeasurableSet E) (hrec : Measurable rec)
    (hHc : Measurable Hc) (hRm : ∀ t, Measurable (R t)) (hVm : Measurable V)
    (hlaw : HasSafeLaw k (typedRhoL w) (typedRhoR w) P
      (Coupling.filtrationComap canonFilt (hrec.prodMk (measurable_relVar hHc hRm hVm)))
      ((fun ω => (rec ω, relVar Hc R V ω)) ⁻¹' typeEvent k w β E)
      (fun ω => canonStp (rec ω, relVar Hc R V ω)) (fun t ω => canonDrv t (rec ω, relVar Hc R V ω))
      (fun i t ω => geomLW canonDrv (fun y => typedXL k w (β y.1)) i t (rec ω, relVar Hc R V ω))
      (fun j t ω => geomRW canonDrv (fun y => typedXR k w (β y.1)) j t (rec ω, relVar Hc R V ω))
      (fun ω => canonFld (rec ω, relVar Hc R V ω)))
    (hmem : HasSafeMembers P (Coupling.filtrationComap canonFilt (hrec.prodMk (measurable_relVar hHc hRm hVm)))
      ((fun ω => (rec ω, relVar Hc R V ω)) ⁻¹' typeEvent k w β E)
      (fun ω => canonStp (rec ω, relVar Hc R V ω)) (fun t ω => canonDrv t (rec ω, relVar Hc R V ω))
      (fun ω => canonFld (rec ω, relVar Hc R V ω)))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => Hc ω φ) P)
    (hthr : ∀ᵐ y ∂((P.map fun ω => (rec ω, relVar Hc R V ω))[|typeEvent k w β E]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL k w (β y.1))
        (fun y => typedXR k w (β y.1)) y) :
    HasRelSafe k w β E (P.map fun ω => (rec ω, relVar Hc R V ω)) := by
  have hΦ : Measurable fun ω => (rec ω, relVar Hc R V ω) := hrec.prodMk (measurable_relVar hHc hRm hVm)
  have hS := measurableSet_typeEvent_canonFilt (k := k) (w := w) hβ hE
  have hxL : Measurable[canonFilt 0] fun y : CanonSpace => typedXL k w (β y.1) :=
    (((measurable_typedXL k w).comp hβ).comp measurable_fst_canonRec).mono (canonRec_le_canonFilt 0) le_rfl
  have hxR : Measurable[canonFilt 0] fun y : CanonSpace => typedXR k w (β y.1) :=
    (((measurable_typedXR k w).comp hβ).comp measurable_fst_canonRec).mono (canonRec_le_canonFilt 0) le_rfl
  have hVst : ∀ t : ℝ≥0, MeasurableSet[canonFilt t] {y : CanonSpace | canonStp y ≤ t} := fun t =>
    measurableSet_canonStp_le le_rfl
  have hWa : AdaptedBefore canonFilt canonStp canonDrv :=
    MartChar.adaptedBefore_of_stronglyAdapted hVst stronglyAdapted_canonDrv
  have hVLa : ∀ i, AdaptedBefore canonFilt canonStp (geomLW canonDrv (fun y => typedXL k w (β y.1)) i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst
      (stronglyAdapted_geomLW stronglyAdapted_canonDrv continuous_canonDrv hxL i)
  have hVRa : ∀ j, AdaptedBefore canonFilt canonStp (geomRW canonDrv (fun y => typedXR k w (β y.1)) j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst
      (stronglyAdapted_geomRW stronglyAdapted_canonDrv continuous_canonDrv hxR j)
  refine ⟨hasSafeLaw_cond hS (hasSafeLaw_map hΦ (isWeakPath_canon _ _) hWa hVLa hVRa measurable_canonFld hlaw),
    hasSafeMembers_cond hS (hasSafeMembers_map hΦ measurable_canonFld hmem), hthr, fun φ => ?_⟩
  have hφm : Measurable fun y : CanonSpace => canonFld y φ :=
    (LQGMetric.measurable_distOn_apply φ).comp measurable_canonFld
  have hi : Integrable (fun y => canonFld y φ) (P.map fun ω => (rec ω, relVar Hc R V ω)) :=
    (integrable_map_measure hφm.aestronglyMeasurable hΦ.aemeasurable).2 (hint φ)
  by_cases h0 : (P.map fun ω => (rec ω, relVar Hc R V ω)) (typeEvent k w β E) = 0
  · rw [cond_eq_zero_of_meas_eq_zero h0]
    exact integrable_zero_measure
  · unfold ProbabilityTheory.cond
    exact hi.restrict.smul_measure (ENNReal.inv_ne_top.2 h0)

end Space

/-! ### Pulled-back canonical events on a physical event -/

/-- **Pulled-back canonical events, traced on an event `L`, are checked on generators** (for K2's time-change
condition `h𝓗'` of `Aux79.hasSafeLaw_of_lineKernel`, with `L = {q ≤ Qc t}`): if `L ∈ 𝓖 t` and the record, the
driver at times `u ≤ q` and the stop events `{stop ≤ u}`, `u ≤ q`, all traced on `L`, are `𝓖 t`-measurable, then so
is `L ∩ D` for every event `D` of the canonical filtration at `q` pulled back through `Φ`. -/
theorem measurableSet_inter_of_canonFilt {Ω : Type*} [mΩ : MeasurableSpace Ω] {Φ : Ω → CanonSpace}
    (hΦ : Measurable Φ) {𝓖 : Filtration ℝ≥0 mΩ} {t q : ℝ≥0} {L : Set Ω} (hL : MeasurableSet[𝓖 t] L)
    (hrec : ∀ A : Set RecData, MeasurableSet A → MeasurableSet[𝓖 t] (L ∩ (fun ω => (Φ ω).1) ⁻¹' A))
    (hdrv : ∀ u ≤ q, ∀ B : Set ℝ, MeasurableSet B →
      MeasurableSet[𝓖 t] (L ∩ (fun ω => canonDrv u (Φ ω)) ⁻¹' B))
    (hstp : ∀ u ≤ q, MeasurableSet[𝓖 t] (L ∩ {ω | canonStp (Φ ω) ≤ (u : ℝ≥0∞)}))
    {D : Set Ω} (hD : MeasurableSet[Coupling.filtrationComap canonFilt hΦ q] D) :
    MeasurableSet[𝓖 t] (L ∩ D) := by
  obtain ⟨D₀, hD₀, rfl⟩ := hD
  let m' : MeasurableSpace CanonSpace :=
    { MeasurableSet' := fun D' => MeasurableSet[𝓖 t] (L ∩ Φ ⁻¹' D')
      measurableSet_empty := by
        simp only [preimage_empty, inter_empty]
        exact @MeasurableSet.empty Ω (𝓖 t)
      measurableSet_compl := fun D' h => by
        have e : L ∩ Φ ⁻¹' D'ᶜ = L \ (L ∩ Φ ⁻¹' D') := by
          ext ω
          simp only [mem_inter_iff, mem_preimage, mem_compl_iff, Set.mem_sdiff, not_and]
          tauto
        rw [e]
        exact hL.diff h
      measurableSet_iUnion := fun f hf => by
        rw [preimage_iUnion, inter_iUnion]
        exact MeasurableSet.iUnion hf }
  have hle : canonSigma q ≤ m' := by
    refine sup_le ?_ (iSup₂_le fun u hu => sup_le ?_ ?_)
    · rintro _ ⟨A, hA, rfl⟩
      exact hrec A hA
    · rintro _ ⟨B, hB, rfl⟩
      exact hdrv u hu B hB
    · refine MeasurableSpace.generateFrom_le fun _ h => ?_
      rw [mem_singleton_iff.1 h]
      exact hstp u hu
  exact hle D₀ hD₀

end InteractingSLE.Supp8.Q3Stop
