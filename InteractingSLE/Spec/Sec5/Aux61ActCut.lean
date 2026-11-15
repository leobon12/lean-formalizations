/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ActDyadic

/-!
# The restart fibre's kernel does not depend on the cutoff; the actual fibre and its cover

Packet PROVE-AUX61-ACT. `Aux61Cov.ActFibre.kernel` is stated for **every** cutoff `F` of `q` near the buffer: the mean
`meanF κ u q F = M⁰_t + G_{ℍ∖K_t}(1_ℍ gD F) + (q − F)` is the same off the hull for all of them (Aux. lemma 61's
`M⁰_t + q − 𝓗_t(q|γ)`). The difference `D = F − G` of two cutoffs of `q` is a cutoff of `0`, and (PC1) for the
reference word against itself (`q̂ = 0`, the landed `Aux61Win.isPC1_couplingMean_ref`) says exactly
`E_t(φ, D.src) = −∫ D φ` (`greenCross_src_of_zero`), i.e. `∫ meanF(F) φ = ∫ meanF(G) φ` (`integral_meanF_congr_cut`).

* `isCutoffOn_sub`, `isCutoffOn_neg'`, `exists_trace_real` (a generating trace reparametrized over `ℝ`);
* **`driving_eq_of_U_eq`**: a clock source killed at its reference clock has the reference word's completed filtration
  (discharges `DyActFibre.driving_eq` when the fibre's source is killed at the clock);
* **`hasRatMembers_of_raw`**: the member identities of `DyActFibre.members` from events of the raw killed filtration;
* **`greenCross_src_of_zero`**, **`integral_meanF_congr_cut`**;
* **`DyActFibre.kernel`**: the kernel of a `DyActFibre` for every cutoff at every stop before the clock;
* **`DyActFibre.toActFibre`**; `HasDyActFibreCover`, **`hasActFibreCover_of_dy`**; `DyActFibreCoverOn`,
  **`actFibreCoverOn_of_dy`**: PROVE-AUX61-R2C's target `Aux61Cov.ActFibreCoverOn` from fibres with the kernel only at
  the countably many stops `min(T_N, k/2ⁿ)`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Act

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (IsGreenTest greenCross cfVal)
open Restart.FlowStopIdentCMI (CMCut geomL geomR)
open Aux61Win (meanF IsCutoffOn IsPC1)
open Aux61R2 (RefExt)
open Sec7.PocketTraversal

universe u

/-! ### Cutoffs of zero -/

/-- **The difference of two cutoffs of the same function is a cutoff of `0`.** -/
theorem isCutoffOn_sub {F G : CMCut} {q : ℂ → ℝ} {N M : Set ℂ} {O₀ O₁ : Set ℝ} (hF : IsCutoffOn F q N O₀)
    (hG : IsCutoffOn G q M O₁) : IsCutoffOn (Aux61Win.CutSum.add F G.neg) (fun _ => 0) (N ∩ M) univ :=
  ⟨hF.isOpen.inter hG.isOpen, fun _ _ _ => trivial, fun z hz hzH => by
    rw [Aux61Win.CutSum.add_f, CMCut.neg_f, hF.eq z hz.1 hzH, hG.eq z hz.2 hzH, add_neg_cancel],
    fun z hz => by
      rw [Aux61Win.CutSum.greenDensity_add, CMCut.greenDensity_neg, hF.harmonic z hz.1, hG.harmonic z hz.2,
        neg_zero, add_zero]⟩

/-- The negated cutoff is a cutoff of the negated function. -/
theorem isCutoffOn_neg' {G : CMCut} {q : ℂ → ℝ} {M : Set ℂ} {O₁ : Set ℝ} (hG : IsCutoffOn G q M O₁) :
    IsCutoffOn G.neg (fun z => -q z) M O₁ :=
  ⟨hG.isOpen, hG.real, fun z hz hzH => by rw [CMCut.neg_f, hG.eq z hz hzH], fun z hz => by
    rw [CMCut.greenDensity_neg, hG.harmonic z hz, neg_zero]⟩

/-- **A generating trace reparametrized over `ℝ`**: before its lifetime the hulls are the fillings of the
reparametrized trace. -/
theorem exists_trace_real {w : ℝ≥0 → ℝ} {e : ℝ≥0∞} {Γ : ℝ≥0 → ℂ} (htr : IsGeneratingTrace w e Γ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < e) : ∃ η : ℝ → ℂ, ContinuousOn η (Icc 0 (t : ℝ)) ∧
      ∀ r ∈ Ioc (0 : ℝ) t, fwdHull (Ito.rpath w) r = fillH (η '' Icc 0 r) := by
  obtain ⟨-, hc, hfill⟩ := htr
  refine ⟨fun s => Γ s.toNNReal, ?_, fun r hr => ?_⟩
  · refine hc.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    exact le_trans (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) ht.le
  · have hr0 : (0 : ℝ) ≤ r := hr.1.le
    have hrt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < e :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht
    have himg : Γ '' Icc 0 r.toNNReal = (fun s : ℝ => Γ s.toNNReal) '' Icc 0 r := by
      ext z
      constructor
      · rintro ⟨s, hs, rfl⟩
        refine ⟨s, ⟨s.coe_nonneg, ?_⟩, by simp⟩
        have := NNReal.coe_le_coe.2 hs.2
        rwa [Real.coe_toNNReal r hr0] at this
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hs.2⟩, rfl⟩
    have hcomp : IsCompact (Γ '' Icc 0 r.toNNReal) := by
      refine isCompact_Icc.image_of_continuousOn (hc.mono fun s hs => ?_)
      exact le_trans (ENNReal.coe_le_coe.2 hs.2) hrt.le
    have h := Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling hcomp (hfill _ hrt)
    rw [Real.coe_toNNReal r hr0] at h
    rw [← himg]
    exact h

/-- **The Green cross energy against the source of a cutoff of `0`** (PC1 of the reference word against itself,
`q̂ = 0`): `E_t(φ, D.src) = −∫ D φ` for a cutoff `D` of `0` near the seed and the closed hull. -/
theorem greenCross_src_of_zero {κ : ℝ} (hκ : 0 < κ) {bR : ℝ → ℝ} {JR : Finset ℝ}
    (hbR : IsPiecewiseConstantBoundaryData bR JR) {w' : ℝ≥0 → ℝ} (hw' : Continuous w') (hw0 : w' 0 = 0)
    {t : ℝ≥0} (htr : 0 < t → ∃ η : ℝ → ℂ, ContinuousOn η (Icc 0 (t : ℝ)) ∧
      ∀ r ∈ Ioc (0 : ℝ) t, fwdHull (Ito.rpath w') r = fillH (η '' Icc 0 r)) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR JR 0 0) (flowLineRhoR κ bR JR 0 0)
        (fun i => geomL (Ito.rpath w') t (flowLineXL bR JR 0 i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR JR 0 j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL bR JR 0 i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR JR 0 j))) u)
    {D : CMCut} {N : Set ℂ} (hD : IsCutoffOn D (fun _ => 0) N univ) (h0 : (0 : ℂ) ∈ N)
    (hKN : closure (fwdHull (Ito.rpath w') t) ⊆ N) (φ : TestOn upperHalfPlaneOpens)
    (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w') t)) :
    greenCross (Ito.rpath w') t φ D.src = -∫ z, D.f z * φ z := by
  classical
  have hq : IsBoundedHarmonicExtension (fun x => bR x - bR x) ((JR ∪ JR : Finset ℝ) : Set ℝ)
      (fun _ => (0 : ℝ)) :=
    ⟨InnerProductSpace.harmonicOnNhd_const 0, ⟨0, fun _ _ => by simp⟩, fun x _ => by
      simp only [sub_self]; exact tendsto_const_nhds⟩
  have hpc : IsPC1 κ u (Ito.rpath w') t (fun _ => 0) univ (couplingMean κ (Ito.rpath w') t u) := by
    rcases eq_zero_or_pos t with rfl | hpos
    · simp only [NNReal.coe_zero] at hu ⊢
      exact Aux61Win.isPC1_couplingMean_ref_zero hκ hbR hbR isOpen_univ (fun _ _ => rfl) (mem_univ 0) 0 hq hw' hw0
        hu hu
    · obtain ⟨η, hηc, hfill⟩ := htr hpos
      exact Aux61Win.isPC1_couplingMean_ref hκ hbR hbR isOpen_univ (fun _ _ => rfl) (mem_univ 0) 0 hq hw' hw0 hpos
        hηc hfill hu hu
  have e := hpc D N hD h0 hKN φ hφ
  have hi : ∫ z, ((fun _ : ℂ => (0 : ℝ)) z - D.f z) * φ z = -∫ z, D.f z * φ z := by
    rw [← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only [zero_sub, neg_mul])
  rw [hi] at e
  linarith

/-- **The explicit mean does not depend on the cutoff** (off the hull): for two cutoffs `F`, `G` of `q` near the seed
and the closed hull, `∫ meanF κ u q F · φ = ∫ meanF κ u q G · φ`. -/
theorem integral_meanF_congr_cut {κ : ℝ} (hκ : 0 < κ) {bR : ℝ → ℝ} {JR : Finset ℝ}
    (hbR : IsPiecewiseConstantBoundaryData bR JR) {w' : ℝ≥0 → ℝ} (hw' : Continuous w') (hw0 : w' 0 = 0)
    {t : ℝ≥0} (htr : 0 < t → ∃ η : ℝ → ℂ, ContinuousOn η (Icc 0 (t : ℝ)) ∧
      ∀ r ∈ Ioc (0 : ℝ) t, fwdHull (Ito.rpath w') r = fillH (η '' Icc 0 r)) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR JR 0 0) (flowLineRhoR κ bR JR 0 0)
        (fun i => geomL (Ito.rpath w') t (flowLineXL bR JR 0 i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR JR 0 j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL bR JR 0 i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR JR 0 j))) u)
    {q : ℂ → ℝ} (hq : ContinuousOn q H) {F G : CMCut} {N M : Set ℂ} {O₀ O₁ : Set ℝ} (hF : IsCutoffOn F q N O₀)
    (hG : IsCutoffOn G q M O₁) (h0 : (0 : ℂ) ∈ N ∩ M) (hK : closure (fwdHull (Ito.rpath w') t) ⊆ N ∩ M)
    (φ : TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w') t)) :
    (∫ z, meanF κ u q F (Ito.rpath w') t z * φ z) = ∫ z, meanF κ u q G (Ito.rpath w') t z * φ z := by
  have hw : Continuous (Ito.rpath w') := hw'.comp continuous_real_toNNReal
  have hKN : closure (fwdHull (Ito.rpath w') t) ⊆ N := hK.trans inter_subset_left
  have hKM : closure (fwdHull (Ito.rpath w') t) ⊆ M := hK.trans inter_subset_right
  rw [Aux61Win.integral_meanF_eq hu.1 hq hw' (hF.isGreenTest_src hKN) φ hφ,
    Aux61Win.integral_meanF_eq hu.1 hq hw' (hG.isGreenTest_src hKM) φ hφ]
  have hgc := greenCross_src_of_zero hκ hbR hw' hw0 htr hu (isCutoffOn_sub hF hG) h0 hK φ hφ
  have hsrc : (Aux61Win.CutSum.add F G.neg).src = fun z => F.src z + G.neg.src z :=
    funext (Aux61Win.CutSum.src_add F G.neg)
  have hcross : greenCross (Ito.rpath w') t φ (Aux61Win.CutSum.add F G.neg).src =
      greenCross (Ito.rpath w') t φ F.src - greenCross (Ito.rpath w') t φ G.src := by
    rw [hsrc, Aux61Win.greenCross_add_right hw t.coe_nonneg (LocalExt.isGreenTest_of_testOn φ hφ)
      (hF.isGreenTest_src hKN) ((isCutoffOn_neg' hG).isGreenTest_src hKM),
      show G.neg.src = fun z => -G.src z from funext G.src_neg, Aux61R2.RefFibre.greenCross_neg_right]
    ring
  have i1 := LocalExt.integrable_mul_testOn (u₀ := fun z => q z - F.f z)
    (hq.sub F.smooth.continuous.continuousOn) φ
  have i2 := LocalExt.integrable_mul_testOn (u₀ := fun z => q z - G.f z)
    (hq.sub G.smooth.continuous.continuousOn) φ
  have hD : ∫ z, (Aux61Win.CutSum.add F G.neg).f z * φ z =
      (∫ z, (q z - G.f z) * φ z) - ∫ z, (q z - F.f z) * φ z := by
    rw [← integral_sub i2 i1]
    exact integral_congr_ae (ae_of_all _ fun z => by
      simp only [Aux61Win.CutSum.add_f, CMCut.neg_f]; ring)
  rw [hcross, hD] at hgc
  linarith

/-! ### A clock source killed at the clock -/

/-- **A clock source killed at its reference clock has the reference word's completed filtration** (the
`driving_eq` field of `DyActFibre`): if the source's lifetime is the clock, the source's killed driver generates, up to
null sets, the same history as the reference word's killed driver with its marks (the marks are functions of the
driver: `ReferenceClock.driving_le`; conversely the source's events are reference events up to the null set where the
two drivers disagree before the clock). -/
theorem driving_eq_of_U_eq {S : Type u} [MeasurableSpace S] {CS : Aux61R45.ClockSource S} {κ : ℝ}
    {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ} {V : Set ℂ} (RC : Aux61R45.ReferenceClock CS κ b J θ V)
    (hU : ∀ ω, CS.U ω = RC.e ω) : CS.driving = drivingFiltration CS.P RC.killed := by
  set 𝓗 := drivingFiltration CS.P RC.killed with h𝓗
  refine le_antisymm ?_ RC.driving_le
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 RC.agree)
  have hagree : ∀ ω, ω ∉ N → ∀ t : ℝ≥0, (t : ℝ≥0∞) < RC.e ω → RC.W t ω = CS.W₀ t ω := fun ω hω => by
    by_contra h
    exact hω (hNsub h)
  have hraw : killedDrivingFiltration CS.killed ≤ 𝓗 := by
    intro t
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨r, hr, A, hA, rfl⟩
    set E := {ω | (r : ℝ≥0∞) < CS.U ω ∧ (CS.W₀ r ω, fun (i : Fin 0) => (fun (_ : Fin 0) (_ : ℝ≥0) (_ : S) => (0 : ℝ))
      i r ω, fun (i : Fin 0) => (fun (_ : Fin 0) (_ : ℝ≥0) (_ : S) => (0 : ℝ)) i r ω) ∈ A} with hE
    have hEm : MeasurableSet E := CS.killed r A hA
    set A' : Set ℝ := (fun x : ℝ => (x, (fun _ : Fin 0 => (0 : ℝ)), (fun _ : Fin 0 => (0 : ℝ)))) ⁻¹' A with hA'
    have hA'm : MeasurableSet A' := hA.preimage (measurable_id.prodMk (measurable_const.prodMk measurable_const))
    set E' := {ω | (r : ℝ≥0∞) < RC.e ω ∧ (RC.W r ω,
      fun i => (geomLW RC.W fun _ => flowLineXL b J CS.y) i r ω,
      fun j => (geomRW RC.W fun _ => flowLineXR b J CS.y) j r ω) ∈ A' ×ˢ (univ ×ˢ univ)} with hE'
    have hE'm : MeasurableSet[𝓗 t] E' := by
      refine Ito.le_usualAugmentation _ _ t _ ((killedDrivingFiltration RC.killed).mono hr _ ?_)
      exact MeasurableSpace.measurableSet_generateFrom ⟨r, le_rfl, _, hA'm.prod (MeasurableSet.univ.prod
        MeasurableSet.univ), rfl⟩
    have hNt : MeasurableSet[𝓗 t] N := Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
    have hEN : MeasurableSet[𝓗 t] (E ∩ N) :=
      Ito.measurableSet_usualAugmentation_of_null (hEm.inter hNm) (measure_mono_null inter_subset_right hN0) t
    have heq : E = (E' \ N) ∪ (E ∩ N) := by
      ext ω
      by_cases hω : ω ∈ N
      · simp only [mem_union, Set.mem_sdiff, mem_inter_iff, hω, not_true_eq_false, and_false, and_true, false_or]
      · have hiff : ω ∈ E ↔ ω ∈ E' := by
          simp only [hE, hE', mem_ofPred_eq, mem_prod, mem_univ, and_true, hU ω, hA', mem_preimage]
          constructor
          · rintro ⟨hlt, hmem⟩
            refine ⟨hlt, ?_⟩
            rw [hagree ω hω r hlt]
            convert hmem using 2
          · rintro ⟨hlt, hmem⟩
            refine ⟨hlt, ?_⟩
            rw [← hagree ω hω r hlt]
            convert hmem using 2
        simp only [mem_union, Set.mem_sdiff, mem_inter_iff, hω, not_false_eq_true, and_true, and_false, or_false]
        exact hiff
    rw [heq]
    exact (hE'm.diff hNt).union hEN
  have hid : usualAugmentation 𝓗 CS.P = 𝓗 := by
    have : 𝓗.IsRightContinuous := by rw [h𝓗]; unfold drivingFiltration; infer_instance
    rw [Ito.usualAugmentation_eq_rightCont, h𝓗, drivingFiltration,
      Ito.nullAugmented_usualAugmentation (killedDrivingFiltration RC.killed) CS.P]
    rw [← drivingFiltration, ← h𝓗]
    exact Filtration.rightCont_self _
  change usualAugmentation (killedDrivingFiltration CS.killed) CS.P ≤ 𝓗
  exact (Ito.usualAugmentation_mono hraw CS.P).trans hid.le

/-! ### Member identities from the raw filtration -/

/-- **Member identities at rational times from events of the raw filtration**: if, for rational `r < s` and every
finite family `F` of rational balls in `ℍ`, some measurable version `S` of the safe event at `s` makes the law of `X`
restricted to `D ∩ S` projection-independent for every event `D` of the **raw** filtration `𝓗` at `r`, then
`DomainMarkov.HasRatMembers` holds (an event of the usual augmentation at `r` is, up to a null set, an event of `𝓗`
at any rational time in `(r, s)`). No completion or right-continuity is needed from the producer. -/
theorem hasRatMembers_of_raw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}
    (h : ∀ r s : ℚ≥0, r < s → ∀ F : Finset (ℚ × ℚ × ℚ), Coupling.ballsK F ⊆ H →
      ∃ S : Set Ω, MeasurableSet S ∧ S =ᵐ[P] Restart.DomainMarkov.safeEv W ζ F (s : ℝ≥0) ∧
        ∀ D : Set Ω, MeasurableSet[𝓗 (r : ℝ≥0)] D →
          Coupling.IsProjIndepMeasure (Restart.DomainMarkov.ballsOpen F) ((P.restrict (D ∩ S)).map X)) :
    Restart.DomainMarkov.HasRatMembers P 𝓗 W ζ X := by
  intro r s hrs F hF
  obtain ⟨r', hr', hr's⟩ := exists_between hrs
  obtain ⟨S, hSm, hSae, hS⟩ := h r' s hr's F hF
  refine ⟨S, hSm, hSae, fun D hD => ?_⟩
  have hD' : MeasurableSet[Ito.nullAugmented 𝓗 P (r' : ℝ≥0)] D :=
    Restart.DomainMarkov.usualAugmentation_le_nullAugmented 𝓗 (by exact_mod_cast hr') _ hD
  obtain ⟨D', hD'm, hDD'⟩ := Ito.exists_ae_eq_of_measurableSet_nullAugmented hD'
  have e : P.restrict (D ∩ S) = P.restrict (D' ∩ S) :=
    Measure.restrict_congr_set (hDD'.inter (ae_eq_refl S))
  rw [e]
  exact hS D' hD'm

/-! ### The kernel of a `DyActFibre` for every cutoff -/

namespace DyActFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : DyActFibre S)

/-- A reference extension in the geometric (`geomL`) form of the frozen (PC1). -/
theorem bhe_geomL_of_refExt {t : ℝ≥0} {ω : S} {u : ℂ → ℝ} (hu : RefExt D.κ D.bR D.JR D.RC.W t ω u) :
    IsBoundedHarmonicExtension
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR 0 0) (flowLineRhoR D.κ D.bR D.JR 0 0)
        (fun i => geomL (Ito.rpath (D.RC.W · ω)) t (flowLineXL D.bR D.JR 0 i))
        (fun j => geomR (Ito.rpath (D.RC.W · ω)) t (flowLineXR D.bR D.JR 0 j)))
      (forceJumpSet (fun i => geomL (Ito.rpath (D.RC.W · ω)) t (flowLineXL D.bR D.JR 0 i))
        (fun j => geomR (Ito.rpath (D.RC.W · ω)) t (flowLineXR D.bR D.JR 0 j))) u := by
  have e1 : (fun i => geomL (Ito.rpath (D.RC.W · ω)) t (flowLineXL D.bR D.JR 0 i)) =
      fun i => geomLW D.RC.W (fun _ => flowLineXL D.bR D.JR 0) i t ω - D.RC.W t ω :=
    funext fun i => Restart.FlowStopIdentCMI.geomL_rpath_eq_geomLW_sub D.RC.W _ i t ω
  have e2 : (fun j => geomR (Ito.rpath (D.RC.W · ω)) t (flowLineXR D.bR D.JR 0 j)) =
      fun j => geomRW D.RC.W (fun _ => flowLineXR D.bR D.JR 0) j t ω - D.RC.W t ω :=
    funext fun j => Restart.FlowStopIdentCMI.geomR_rpath_eq_geomRW_sub D.RC.W _ j t ω
  rw [e1, e2]
  exact hu

/-- **The kernel of a `DyActFibre` for every cutoff** of `q` near the buffer, at every stop before the clock
(`kernel_Fq` and the independence of the cutoff). -/
theorem kernel (F : CMCut) (N : Set ℂ) (hF : IsCutoffOn F D.q N D.O₀) (hbN : D.buffer ⊆ N)
    (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime D.CS.driving τ) (hτe : ∀ᵐ ω ∂D.CS.P, (τ ω : ℝ≥0∞) < D.RC.e ω)
    (u : S → ℂ → ℝ) (hu : ∀ ω, RefExt D.κ D.bR D.JR D.RC.W ((τ ω).untopD 0) ω (u ω))
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂D.CS.P, Disjoint (tsupport ψ) (fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) →
      D.CS.P[fun ω' => Complex.exp (Complex.I * (D.field ω' ψ : ℂ)) | hτ.measurableSpace] ω =
        cfVal (∫ z, meanF D.κ (u ω) D.q F (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) ψ) := by
  have hKb : ∀ᵐ ω ∂D.CS.P, closure (fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) ⊆ D.buffer :=
    D.ae_hull_buffer_of_lt (hτe.mono fun ω h => Restart.FlowStopIdentCM.coe_untopD_lt h)
  filter_upwards [D.kernel_Fq τ hτ hτe u hu ψ, hKb, hτe, D.RC.trace] with ω h1 hK hlt htr hdis
  rw [h1 hdis]
  have htr' : IsGeneratingTrace (D.RC.W · ω) (D.RC.e ω) (D.CS.Γ ω) := by
    simpa only [D.y_zero, Complex.ofReal_zero, sub_zero] using htr
  have hlt' := Restart.FlowStopIdentCM.coe_untopD_lt hlt
  have hK' : closure (fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) ⊆ D.Nq ∩ N :=
    subset_inter (hK.trans D.buffer_sub) (hK.trans hbN)
  rw [integral_meanF_congr_cut D.κ_pos D.bR_pc (D.RC.continuous ω) (D.RC.zero ω)
    (fun _ => exists_trace_real htr' hlt') (D.bhe_geomL_of_refExt (hu ω)) D.continuousOn_q D.cut_spec.2.1 hF
    ⟨D.buffer_sub D.zero_mem, hbN D.zero_mem⟩ hK' ψ hdis]

/-- **A `DyActFibre` is an actual fibre.** -/
def toActFibre : Aux61Cov.ActFibre S where
  κ := D.κ
  κ_pos := D.κ_pos
  bR := D.bR
  JR := D.JR
  CS := D.CS
  y_zero := D.y_zero
  V := D.V
  RC := D.RC
  field := D.field
  measurable_field := D.measurable_field
  q := D.q
  q_harm := D.q_harm
  O₀ := D.O₀
  O₀_open := D.O₀_open
  q_zero := D.q_zero
  buffer := D.buffer
  buffer_open := D.buffer_open
  zero_mem := D.zero_mem
  buffer_compact := D.buffer_compact
  buffer_real := D.buffer_real
  hull_buffer := D.hull_buffer
  kernel := D.kernel
  locality := D.locality
  injective := D.injective

end DyActFibre

/-! ### The cover -/

/-- **The cover by fibres with the kernel at countably many stops** (`Aux61Cov.HasActFibreCover` with `DyActFibre`). -/
def HasDyActFibreCover {X : Type u} [MeasurableSpace X] (μ : Measure X) (E : X → Prop)
    (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (A : ι → Set X) (S : Type u) (_ : MeasurableSpace S) (κ : ι → Kernel X S)
    (L : ι → Set S),
    (∀ i, MeasurableSet (A i)) ∧ (∀ᵐ x ∂μ, E x → ∃ i, x ∈ A i) ∧
    (∀ i, μ (A i ∩ {x | E x}) ≤ ∫⁻ x in A i, κ i x (L i) ∂μ) ∧
    ∀ i, ∀ᵐ x ∂μ, x ∈ A i → ∃ (D : DyActFibre S) (I : Set ℝ),
      D.CS.P = κ i x ∧ Ref D.κ D.bR D.JR I ∧
      ∀ ω ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ D.RC.e ω ∧ ∃ y ∈ I, D.CS.Γ ω v = (y : ℂ)

/-- **Fibres with the kernel at countably many stops give the actual-fibre cover.** -/
theorem hasActFibreCover_of_dy {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (hcov : HasDyActFibreCover μ E Ref) :
    Aux61Cov.HasActFibreCover μ E Ref := by
  obtain ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, hfib⟩ := hcov
  refine ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, fun i => ?_⟩
  filter_upwards [hfib i] with x hx hxA
  obtain ⟨D, I, hPx, hRef, hL⟩ := hx hxA
  exact ⟨D.toActFibre, I, hPx, hRef, hL⟩

section Glued

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop51Q CfAvoidLeftQ Prop51G Aux61Kernel
open QuantumZipper (chiC)

/-- **PROVE-AUX61-R2C's target with fibres known at countably many stops**: same binders as
`Aux61Cov.ActFibreCoverOn`, with `HasDyActFibreCover`. -/
def DyActFibreCoverOn (G : ℝ → ℝ → ℝ → Prop) (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∀ (t : ℚ) (c : WinCode), 0 < t →
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ → G κ θ₁ θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ s : ℚ, 0 < s →
            HasDyActFibreCover.{u}
              (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun u : ℝ => η p.1 u.toNNReal) t c) Ref

/-- **`Aux61Cov.ActFibreCoverOn` from fibres known at countably many stops.** -/
theorem actFibreCoverOn_of_dy {G : ℝ → ℝ → ℝ → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hcov : DyActFibreCoverOn.{u} G Ref) : Aux61Cov.ActFibreCoverOn.{u} G Ref := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  exact hasActFibreCover_of_dy (hcov t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf
    hlaw k hk s hs)

/-- **(E1) in target-component form for every angle pair**, from fibres known at countably many stops below the
critical gap, R5's negative side, and Part A's counterflow regularity. -/
theorem fwdNoEastCrosscutTgtQOn_of_dyCover_refWin (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hcov : DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin)
    (hneg : Aux61Cov.R5NegStatement.{u}) : FwdNoEastCrosscutTgtQOn.{u} fun _ _ _ => True :=
  Aux61Cov.fwdNoEastCrosscutTgtQOn_of_actCover_refWin hreg (actFibreCoverOn_of_dy hcov) hneg

end Glued

end InteractingSLE.Sec5.Aux61Act
