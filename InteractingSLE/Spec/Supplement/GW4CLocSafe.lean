/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocGeom
import InteractingSLE.Spec.Restart.RetPlumbProofLocal
import InteractingSLE.Spec.Sec5.CfRegQ

/-!
# GW4: the safe hull at one physical time is history-marked local under the conditional law

Packet PROVE-GW4-CLOC, step 5 (deterministic in the measure). Under a probability measure `Q` (in the application,
the regular conditional law given the walks) let the field have the Gaussian union kernel of
`exists_ae_condExpKernel_kernel` at one physical time `t`, with `B` almost surely the relative closure of the walks
and the counterflow hull at `t`. Then PROVE-GW4-SAFER's clipped safe hull `safeHull F Wd GT R V t` is a
history-marked local set of the centred inverted component field for the physical marks `physFilt t`
(`isHistoryAvoidanceLocal_safeHull_of_kernel`):

* the chart set of `B` is marked local for the kernel's marks (`isHistoryAvoidanceLocal_chartSet`); the frontier of the
  component in `ℍ` lies in the walks, hence in `B` (`isOpen_diff_of_mem_betweenComponents`);
* the physical marks are almost surely events of the kernel's marks (`physFilt_le_aeSigma`: the driver at times `≤ t`
  is read from the counterflow record stopped at `t`);
* the chart set lies in the safe hull (`chartSet_subset_relHullFam`, `hullAt_subset_fwdHull_of_lineClock_lt`), and the
  safe hull is physical (`Frame.measurable_safeHull`), so the criterion passes to it
  (`isHistoryAvoidanceLocal_mono_set`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets WholeField GW4Traverse GW4Rel Sec5.GlueCond Sec5.Cond44Ref Supp8.RelSafe

/-! ### The component frontier lies in the walks -/

theorem isOpen_diff_of_mem_betweenComponents {R L C : Set ℂ} (hC : C ∈ betweenComponents R L) (hCo : IsOpen C)
    {B : Set ℂ} (hB : (R ∪ L) ∩ H ⊆ B) (hBo : IsOpen (H \ B)) : IsOpen ((H \ B) \ C) := by
  obtain ⟨z₀, hz₀, -, -, rfl⟩ := hC
  have he : (H \ B) \ connectedComponentIn (H \ (R ∪ L)) z₀ =
      (H \ B) ∩ (closure (connectedComponentIn (H \ (R ∪ L)) z₀))ᶜ := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    refine ⟨fun ⟨hzB, hzC⟩ => ⟨hzB, fun hzcl => hzC ?_⟩, fun ⟨hzB, hzcl⟩ => ⟨hzB, fun hzC => hzcl (subset_closure hzC)⟩⟩
    have hzO : z ∈ H \ (R ∪ L) := ⟨hzB.1, fun hzRL => hzB.2 (hB ⟨hzRL, hzB.1⟩)⟩
    have hpre : IsPreconnected (insert z (connectedComponentIn (H \ (R ∪ L)) z₀)) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset hzcl subset_closure)
    have hsub : insert z (connectedComponentIn (H \ (R ∪ L)) z₀) ⊆ H \ (R ∪ L) :=
      insert_subset hzO (connectedComponentIn_subset _ _)
    have hz₀m : z₀ ∈ insert z (connectedComponentIn (H \ (R ∪ L)) z₀) :=
      mem_insert_of_mem _ (mem_connectedComponentIn hz₀)
    exact hpre.subset_connectedComponentIn hz₀m hsub (mem_insert _ _)
  rw [he]
  exact hBo.inter isClosed_closure.isOpen_compl

theorem disjoint_of_mem_betweenComponents {R L C : Set ℂ} (hC : C ∈ betweenComponents R L) :
    Disjoint (R ∪ L) C := by
  obtain ⟨z₀, -, -, -, rfl⟩ := hC
  exact Set.disjoint_left.2 fun z hz hzC => (connectedComponentIn_subset _ _ hzC).2 hz

theorem subset_H_of_mem_betweenComponents {R L C : Set ℂ} (hC : C ∈ betweenComponents R L) : C ⊆ H := by
  obtain ⟨z₀, -, -, -, rfl⟩ := hC
  exact (connectedComponentIn_subset _ _).trans sdiff_subset

/-! ### The physical marks are read from the counterflow record -/

theorem hDrv_stopHistory {nL nR : ℕ} (y : LawUnique.HistorySpace nL nR) {r t : ℝ≥0} (hrt : r ≤ t) :
    Sec5.CfRegQ.hDrv (Sec4.stopHistory (fun _ => t) y) r = Sec5.CfRegQ.hDrv y r := by
  rw [Sec5.CfRegQ.hDrv_apply, Sec5.CfRegQ.hDrv_apply]
  congr 1
  funext n
  have hle : LawUnique.dyadicTime (LawUnique.lowerDyadic r n) ≤ t :=
    (LawUnique.dyadicTime_lowerDyadic_le r n).trans hrt
  simp [Sec5.CfRegQ.dyVal, Sec4.stopHistory, hle]

theorem physFilt_le_aeSigma {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    {Wd W : ℝ≥0 → Ω → ℝ} (hWm : ∀ r, Measurable (Wd r)) {ζ : Ω → ℝ≥0∞} {t : ℝ≥0}
    (h𝓜 : MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t) ≤ 𝓜)
    (hgood : ∀ᵐ ω ∂Q, ζ ω = ⊤ ∧ Continuous (fun r => W r ω) ∧ ∀ r, Wd r ω = W r ω) :
    physFilt Frame.measurable_gw4Rec hWm Q t ≤ aeSigma 𝓜 Q := by
  have hmono : aeSigma (MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t)) Q ≤ aeSigma 𝓜 Q :=
    fun s ⟨s', hs', hss'⟩ => ⟨s', h𝓜 _ hs', hss'⟩
  refine sup_le (sup_le ?_ (iSup₂_le fun r hr => ?_)) ?_
  · rintro _ ⟨B, -, rfl⟩
    by_cases hB : gw4Rec ∈ B
    · exact ⟨univ, @MeasurableSet.univ _ 𝓜, by simp [preimage, hB]⟩
    · exact ⟨∅, @MeasurableSet.empty _ 𝓜, by simp [preimage, hB]⟩
  · refine (le_trans ?_ hmono)
    have hcomap : MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t) =
        MeasurableSpace.comap (fun ω => Sec4.stopHistory (fun _ => t) (cfHistory W ζ ω)) inferInstance := by
      rw [WangWu.stopSigma, MeasurableSpace.comap_comp]
      rfl
    rw [hcomap]
    refine KernelTower.comap_le_aeSigma_comap (φ := fun y => Sec5.CfRegQ.hDrv y r)
      ((measurable_pi_apply r).comp Sec5.CfRegQ.measurable_hDrv) ?_
    filter_upwards [hgood] with ω ⟨hζ, hc, hWd⟩
    show Wd r ω = Sec5.CfRegQ.hDrv (Sec4.stopHistory (fun _ => t) (cfHistory W ζ ω)) r
    rw [hDrv_stopHistory _ hr, Sec5.GlueCond.hDrv_cfHistory hζ hc, hWd]
  · refine MeasurableSpace.generateFrom_le fun s hs => ?_
    exact ⟨∅, @MeasurableSet.empty _ 𝓜, ae_eq_empty.2 hs.2⟩

/-! ### The safe hull at one physical time -/

theorem le_aeSigma_self {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) :
    m ≤ aeSigma m Q := fun s hs => ⟨s, hs, EventuallyEq.rfl⟩

/-- **The safe hull at one physical time is history-marked local** under `Q`, for the physical marks, from the
union kernel at that time. -/
theorem isHistoryAvoidanceLocal_safeHull_of_kernel {Ω : Type*} {𝓜 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] (h𝓜 : 𝓜 ≤ mΩ)
    {R L C : Set ℂ} {c : Chart} (hCb : C ∈ betweenComponents R L) (hch : IsComponentChart R L C c)
    (hCo : IsOpen C) {κ : ℝ} (hκ : 0 < κ) {h hC : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    (htr : ∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hC ω))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    {B : Ω → Set ℂ} {M : Ω → DistOn upperHalfPlaneOpens}
    (hBm : Measurable[𝓜, hittingSigma] B) (hMm : Measurable[𝓜] M)
    (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) (hMh : ∀ᵐ ω ∂Q, IsHarmonicDistOn (M ω) (H \ B ω))
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜] =ᵐ[Q] fun ω => rangeKerCF (M ω) (H \ B ω) φ)
    {S : Ω → Set ℂ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {t : ℝ≥0}
    (hcf𝓜 : MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t) ≤ 𝓜)
    (hBeq : ∀ᵐ ω ∂Q, B ω = relClosureH (S ω ∪ cfHullQ t (cfHistory W ζ ω)))
    (hS : ∀ᵐ ω ∂Q, S ω = (R ∪ L) ∩ H)
    {F : Frame} (hF : F.IsOk) (hFC : F.C = C) (hFc : F.c = c) {Wd : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂Q, ω ∈ GT) (hVW : ∀ᵐ ω ∂Q, ∀ r, Wd r ω = W r ω)
    (hζ : ∀ᵐ ω ∂Q, ζ ω = ⊤) {Rv : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGW4RelVersionR Q Wd F.c F.C Rv V) :
    IsHistoryAvoidanceLocal (physFilt Frame.measurable_gw4Rec hWm Q t) (safeHull F Wd GT Rv V t)
      (centredField (fun ω => invField κ (hC ω)) u) Q := by
  have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hCb
  have hdisj : Disjoint (R ∪ L) C := disjoint_of_mem_betweenComponents hCb
  have hBC : ∀ᵐ ω ∂Q, IsOpen ((H \ B ω) \ C) := by
    filter_upwards [hBeq, hS] with ω hB hSω
    refine isOpen_diff_of_mem_betweenComponents hCb hCo ?_ (hBc ω).2
    intro z hz
    rw [hB]
    refine ⟨hz.2, subset_closure ⟨Or.inl ?_, hz.2⟩⟩
    rw [hSω]
    exact hz
  have hloc₁ := isHistoryAvoidanceLocal_chartSet h𝓜 hch hCo hCH hκ hhm htr hu hBm hMm hBc hMh hBC hker
  have hgood : ∀ᵐ ω ∂Q, ζ ω = ⊤ ∧ Continuous (fun r => W r ω) ∧ ∀ r, Wd r ω = W r ω := by
    filter_upwards [hζ, hVW, hGTae] with ω h1 h2 h3
    refine ⟨h1, ?_, h2⟩
    have he : (fun r => W r ω) = fun r => Wd r ω := funext fun r => (h2 r).symm
    rw [he]
    exact (hGT ω h3).1
  have hmarks := physFilt_le_aeSigma hWm hcf𝓜 hgood
  have hloc₂ : IsHistoryAvoidanceLocal (𝓜 ⊔ physFilt Frame.measurable_gw4Rec hWm Q t)
      (fun ω => chartSet c (B ω)) (centredField (fun ω => invField κ (hC ω)) u) Q :=
    Restart.RetAux79.isHistoryAvoidanceLocal_of_le_aeSigma (sup_le (le_aeSigma_self Q) hmarks) hloc₁
  have hsafe : Measurable[𝓜 ⊔ physFilt Frame.measurable_gw4Rec hWm Q t, hittingSigma]
      (safeHull F Wd GT Rv V t) :=
    (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver t).mono le_sup_right le_rfl
  have hincl : ∀ᵐ ω ∂Q, chartSet c (B ω) ⊆ safeHull F Wd GT Rv V t ω := by
    filter_upwards [hBeq, hS, hgood, hGTae, hver.1.1.2.2.2.2] with ω hB hSω ⟨hζω, hcω, hWdω⟩ hω hhull
    by_cases hlt : lineClock F Wd GT V t ω < V ω
    · simp only [safeHull, hlt, ↓reduceIte]
      intro v hv
      refine ⟨chartSet_subset_H _ _ hv, ?_⟩
      have hWe : (fun r => W r ω) = fun r => Wd r ω := funext fun r => (hWdω r).symm
      have hpath := hGT ω hω
      have hy : cfHistory W ζ ω ∈ Sec5.CfRegQ.goodCfSet := by
        refine Sec5.CfRegQ.cfHistory_mem_goodCfSet hζω hcω ?_ (η := trc fun r => Wd r ω) ?_
        · rw [← hWdω 0]; exact hpath.2.1
        · rw [hWe]; exact hpath.2.2.1
      have hw : Sec5.Prop411Q.cfDrv (cfHistory W ζ ω) = fun s : ℝ => W s.toNNReal ω := by
        rw [Sec5.CfRegQ.cfDrv_eq_hDrv, Sec5.GlueCond.hDrv_cfHistory hζω hcω]
      have h1 : chartSet c (B ω) ⊆ relHullFam c C (fun r => W r ω) t := by
        rw [hB, hSω]
        exact chartSet_subset_relHullFam hch hCo hCH (hdisj.mono_left inter_subset_left) hy hw t
      have h2 : relHullFam c C (fun r => W r ω) t = F.hullAt (fun r => Wd r ω) t := by
        rw [Frame.hullAt, hFc, hFC, hWe]
      have h3 := hullAt_subset_fwdHull_of_lineClock_lt hF hGT hω (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)
        hhull hlt
      exact h3 (h2 ▸ h1 hv)
    · simp only [safeHull, hlt, ↓reduceIte]
      exact chartSet_subset_H _ _
  have hloc₃ := Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hloc₂ hsafe hincl
  exact Restart.RetAux79.isHistoryAvoidanceLocal_of_le_aeSigma (le_sup_right.trans (le_aeSigma_self Q)) hloc₃

end InteractingSLE.Theorem14.GW4Fix.CLoc
