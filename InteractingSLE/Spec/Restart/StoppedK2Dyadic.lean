/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovAux79Stop

/-!
# The stopped K2, part 5: the conditional-law clause before the stop from the dyadic times

Packet PROVE-STOPPEDK2. Under the regular conditional law, K2 transfers the protected-kernel law of the continuation
at the dyadic times (`DomainMarkov.IsDyadicSampled`); `DomainMarkov.condExp_cexp_eq_frozenRHS_of_dyadic` turns it into
the conditional-law clause at every stopping time `τ < ζ`, but assumes an integrated evolution. A coupling through a
stop `V` only has a local evolution before `V`. Here the pathwise regularity `IsForceReg` (continuity before `ζ`,
ordered force points, `W₀ = 0`) replaces the evolution, as in PROVE-DOMAINMARKOV8's
`DomainMarkov.Aux79.isCouplingCharFun_of_hasSafeLaw`:

* `setIntegral_cexp_eq_cfAt_of_dyadic_reg` (copy of `Aux79.setIntegral_cexp_eq_cfAt_of_hasSafeLaw`, with the dyadic
  identities of `IsDyadicSampled` on the null-augmented killed driving filtration in place of `HasSafeLaw`);
* **`isCouplingCharFun_of_dyadic_reg`** (copy of `Aux79.isCouplingCharFun_of_hasSafeLaw`): `IsDyadicSampled` and
  `IsForceReg` almost surely give `IsCouplingCharFun` for the driving filtration.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Restart.StoppedK2

open Coupling Ito DomainMarkov DomainMarkov.K2 DomainMarkov.Aux79

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The protected-kernel law at a stopping time `τ < ζ` from the dyadic times, with `IsForceReg`**
(`Aux79.setIntegral_cexp_eq_cfAt_of_hasSafeLaw` with `IsDyadicSampled` in place of `HasSafeLaw`). -/
theorem setIntegral_cexp_eq_cfAt_of_dyadic_reg [IsProbabilityMeasure P]
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    (hdy : IsDyadicSampled κ W (bheProc κ ρL ρR W VL VR) P hX h) (hpath : ∀ᵐ ω ∂P, IsForceReg W VL VR ζ ω)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAE : A ⊆ {ω | Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))}) :
    ∫ ω in A, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P =
      ∫ ω in A, cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun ω => (τ ω).untopD 0) ω ∂P := by
  set 𝓗 := killedDrivingFiltration hX with h𝓗
  have hWa₀ : AdaptedBefore 𝓗 ζ W := adaptedBefore_killedDriving_W hX
  have hVLa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VL i) := fun i => adaptedBefore_killedDriving_VL hX i
  have hVRa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VR i) := fun i => adaptedBefore_killedDriving_VR hX i
  classical
  set u := bheProc κ ρL ρR W VL VR with hudef
  have hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s) := fun ω s =>
    isBoundedHarmonicExtension_bheProc ω s
  set 𝓐 := nullAugmented 𝓗 P with h𝓐
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hh ψ)))
  have hfb : ∀ ω, ‖f ω‖ ≤ 1 := fun ω => (norm_cexp_I_mul_ofReal _).le
  have hfint : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ hfb)
  -- the good set
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hpath)
  set G : Set Ω := Nᶜ with hGdef
  have hGp : ∀ ω ∈ G, IsForceReg W VL VR ζ ω := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simpa [hGdef] using hN0
  have hG0 : MeasurableSet[𝓐 0] G := (measurableSet_nullAugmented_of_null hNm hN0 0).compl
  have hWa : AdaptedBefore 𝓐 ζ W :=
    adaptedBefore_mono (le_nullAugmented 𝓗 P) hWa₀
  have hVLa : ∀ i, AdaptedBefore 𝓐 ζ (VL i) := fun i =>
    adaptedBefore_mono (le_nullAugmented 𝓗 P) (hVLa₀ i)
  have hVRa : ∀ i, AdaptedBefore 𝓐 ζ (VR i) := fun i =>
    adaptedBefore_mono (le_nullAugmented 𝓗 P) (hVRa₀ i)
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGp ω hω).2.1
  -- the pieces
  set C : ℕ → ℕ → Set Ω := fun n k => piece τ A W ζ G ψ n k with hC
  have hCm𝓐 : ∀ n k, MeasurableSet[𝓐 (dyT n (k + 1))] (C n k) := fun n k => by
    have h1 : MeasurableSet[𝓐 (dyT n (k + 1))]
        (A ∩ {ω | τ ω ≠ ⊤ ∧ ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k}) :=
      usualAugmentation_le_nullAugmented (P := P) 𝓗 (dyT_lt_dyT_succ n k) _ (measurableSet_piece hτ hA n k)
    have h2 : MeasurableSet[𝓐 (dyT n (k + 1))] (safeU W ζ G ψ (dyT n (k + 1))) :=
      MeasurableSet.iUnion fun m => measurableSet_safeSet hWa hGc hG0 (tsupport_subset_H ψ) (by positivity) _
    exact h1.inter h2
  have hCm : ∀ n k, MeasurableSet (C n k) := fun n k => 𝓐.le _ _ (hCm𝓐 n k)
  have hcfint : ∀ n k, Integrable ((C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1))) P := by
    intro n k
    have e : (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) =
        (C n k).indicator ((safeU W ζ G ψ (dyT n (k + 1))).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1))) := by
      rw [indicator_indicator, inter_eq_left.2 (fun ω hω => hω.2)]
    rw [e]
    refine Integrable.of_bound (((aestronglyMeasurable_safeU_indicator_cfAt' hu ψ hGp hG0 hWa hVLa hVRa
      _).indicator (hCm n k))) 1 (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ C n k
    · rw [indicator_of_mem hω, indicator_of_mem hω.2]
      exact norm_cfAt_le_one_of_mem_safeU' ψ hGp u hω.2
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  -- the dyadic identity, summed over the pieces at level `n`
  have hGF : ∀ n, ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (C n k).indicator f ω ∂P =
      ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω ∂P := by
    intro n
    rw [integral_finsetSum _ (fun k _ => hfint.indicator (hCm n k)),
      integral_finsetSum _ (fun k _ => hcfint n k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_indicator (hCm n k), integral_indicator (hCm n k)]
    exact hdy ψ n (k + 1) _ (hCm𝓐 n k) fun ω hω => safeU_subset_avoidSet' ψ hGp _ hω.2
  -- bounds
  have hlab : ∀ n k ω, ω ∈ C n k → ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k := fun n k ω hω => hω.1.2.2
  have hGb : ∀ n ω, ‖∑ k ∈ Finset.range (4 ^ n), (C n k).indicator f ω‖ ≤ 1 := fun n ω => by
    rw [sum_indicator_eq_of_label (hlab n) ω]
    split_ifs
    · by_cases hω : ω ∈ C n ⌈2 ^ n * (τ ω).untopD 0⌉₊
      · rw [indicator_of_mem hω]; exact hfb ω
      · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
    · rw [norm_zero]; exact zero_le_one
  have hFb : ∀ n ω, ‖∑ k ∈ Finset.range (4 ^ n),
      (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω‖ ≤ 1 := fun n ω => by
    rw [sum_indicator_eq_of_label (hlab n) ω]
    split_ifs
    · by_cases hω : ω ∈ C n ⌈2 ^ n * (τ ω).untopD 0⌉₊
      · rw [indicator_of_mem hω]; exact norm_cfAt_le_one_of_mem_safeU' ψ hGp u hω.2
      · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
    · rw [norm_zero]; exact zero_le_one
  -- dominated convergence
  have hpt := ae_tendsto_sum_piece' hu ψ hGp f hAE hGae hτζ
  have hlimG := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (integrable_finsetSum _ (fun k _ => hfint.indicator (hCm n k))).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (hGb n)) (hpt.mono fun ω h => h.1)
  have hlimF := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (integrable_finsetSum _ (fun k _ => hcfint n k)).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (hFb n)) (hpt.mono fun ω h => h.2)
  have heq := tendsto_nhds_unique (hlimG.congr hGF) hlimF
  have hA'm : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter (measurableSet_eq_top_of_isStoppingTime hτ).compl
  rw [integral_indicator hA'm, integral_indicator hA'm] at heq
  have hAA' : A =ᵐ[P] (A ∩ {ω | τ ω ≠ ⊤} : Set Ω) := by
    filter_upwards [hτζ] with ω hω
    exact propext ⟨fun h => ⟨h, ne_top_of_lt_zeta hω⟩, fun h => h.1⟩
  rw [setIntegral_congr_set hAA', setIntegral_congr_set hAA']
  exact heq


/-- **The conditional-law clause before the lifetime from the dyadic times, without the driving equations**
(`Aux79.isCouplingCharFun_of_hasSafeLaw` with `setIntegral_cexp_eq_cfAt_of_dyadic_reg`). -/
theorem isCouplingCharFun_of_dyadic_reg [IsProbabilityMeasure P] (hX : IsMeasurableKilledDriving W VL VR ζ)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    (hdy : IsDyadicSampled κ W (bheProc κ ρL ρR W VL VR) P hX h) (hpath : ∀ᵐ ω ∂P, IsForceReg W VL VR ζ ω) :
    Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P (drivingFiltration P hX) W VL VR ζ h := by
  have hWa₀ := adaptedBefore_killedDriving_W hX
  have hVLa₀ := fun i => adaptedBefore_killedDriving_VL hX i
  have hVRa₀ := fun i => adaptedBefore_killedDriving_VR hX i
  intro τ hτ hτζ uτ huτ φ
  set u := bheProc κ ρL ρR W VL VR with hudef
  have hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s) := fun ω s =>
    isBoundedHarmonicExtension_bheProc ω s
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  obtain ⟨E', hE'm, hE'sub, hE'ae, hE'mean, hE'path, hE'sm⟩ :=
    exists_stopped_measurable hpath hWa₀ hVLa₀ hVRa₀ φ hτ hτζ uτ huτ
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hh φ)))
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => (norm_cexp_I_mul_ofReal _).le)
  set g : Ω → ℂ := E'.indicator (frozenRHS κ W uτ φ τ') with hg
  have hcf : ∀ ω ∈ E', frozenRHS κ W uτ φ τ' ω = cfAt κ W u φ 1 τ' ω := fun ω hω => by
    simp only [frozenRHS, cfAt]
    rw [← hE'mean ω hω (u ω (τ' ω)) (hu ω (τ' ω))]
    congr 1
    push_cast
    ring
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E'
    · rw [hg, indicator_of_mem hω, hcf ω hω]
      obtain ⟨h1, h2, h3⟩ := hE'path ω hω
      exact norm_cfAt_le_one u 1 φ (r := τ') h1 h2 h3
    · rw [hg, indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hgm : StronglyMeasurable[hτ.measurableSpace] g := hE'sm
  have hgint : Integrable g P :=
    Integrable.of_bound ((hgm.mono hτ.measurableSpace_le).aestronglyMeasurable) 1 (ae_of_all _ hgb)
  have hE'mΩ : MeasurableSet E' := hτ.measurableSpace_le _ hE'm
  have key : g =ᵐ[P] condExp hτ.measurableSpace P (E'.indicator f) := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
      (hfint.indicator hE'mΩ) (fun A _ _ => hgint.integrableOn) (fun A hA _ => ?_)
      hgm.aestronglyMeasurable
    have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
    rw [hg, setIntegral_indicator hE'mΩ, setIntegral_indicator hE'mΩ]
    have hAE : MeasurableSet[hτ.measurableSpace] (A ∩ E') :=
      @MeasurableSet.inter Ω hτ.measurableSpace _ _ hA hE'm
    have hdy' := setIntegral_cexp_eq_cfAt_of_dyadic_reg hX h hh hdy hpath φ hτ hτζ hAE
      (inter_subset_right.trans hE'sub)
    rw [hdy']
    refine setIntegral_congr_fun (hAm.inter hE'mΩ) fun ω hω => ?_
    exact hcf ω hω.2
  have hind := condExp_indicator (m := hτ.measurableSpace) (μ := P) hfint hE'm
  filter_upwards [key, hind, hE'ae] with ω h1 h2 h3 hdis
  have hω : ω ∈ E' := h3 hdis
  have e1 : condExp hτ.measurableSpace P f ω =
      E'.indicator (condExp hτ.measurableSpace P f) ω := (indicator_of_mem hω _).symm
  rw [e1, ← h2, ← h1, hg, indicator_of_mem hω]
  rfl

end InteractingSLE.Restart.StoppedK2
