/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.CouplingThrough
import InteractingSLE.Spec.Coupling.WholeField9Induct
import InteractingSLE.Spec.Restart.StoppedExtendWFDet

/-!
# WFS targets: the whole-field machinery for couplings through a stop

Packet PROVE-WFS0. The stopped kernel (K) (`Restart.StoppedExtendWF.StoppedKernelStatement`,
`planning/handoffs/PROVE-DOMAINMARKOV10.md` §4.2) is the whole-field chain WF2 → WF3Brown → WF4 → WF5 → WF6 → WF7 →
WF9 → Aux50Hit, which is proved for full couplings (`IsOptionalHullCoupling`), redone for couplings through a stop
(`WFS.IsCouplingThrough`, WFS-0). This file states the targets of the later packets, so that they can be worked on in
parallel:

* **`ThroughCmKerStatement κ`** (WFS-1…n, the endpoint of the WF7/WF9 copies): C.4, `WholeField.
  ae_condExp_exp_eq_cmKer_of_isLabel`, for a coupling through `V`, at every bounded stopping time `σ < V` of the driving
  filtration killed at `V`: off the labelled supports, the conditional characteristic function given the stopped
  σ-algebra is Gaussian with the conditional mean and the retained Green energy (`WholeField.cmKer`).
* **`ThroughKernelStatement κ`** (WFS-K and WFS-REF): (K) with its part (i) for couplings through a Galmarino stop
  `V = R(history killed at V)`, and its part (ii) for full couplings at `min (R(history), ζ)`; the thinness of part (i)
  is stated for the law of the killed history.

The substitution rule for every intermediate WF theorem (list in `planning/handoffs/PROVE-DOMAINMARKOV10.md`,
§"WF theorems taking a full `hC`"): `hC : IsOptionalHullCoupling … ζ h` becomes `hC : IsCouplingThrough … ζ V h`; the
driving filtration is the one killed at `V` (`hX : IsMeasurableKilledDriving W VL VR V`, from `hC.2.2.2.2`); every
stop condition `σ < ζ` becomes `σ < V`; path facts still come from the full evolution `hC.1`; selectors that run past
`σ` are capped at `V` and localized along an announcing sequence of `V`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace WFS

open LawUnique Restart.StoppedExtendWF WholeField LQGMetric

/-- **WFS target: C.4 for couplings through a stop** (`WholeField.ae_condExp_exp_eq_cmKer_of_isLabel` with the full
coupling replaced by a coupling through `V` and the stops `σ < ζ` by stops `σ < V` of the driving filtration killed at
`V`). -/
def ThroughCmKerStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h →
    ∀ (hX : IsMeasurableKilledDriving W VL VR V) {ι : Type} (ψ : ι → TestOn upperHalfPlaneOpens) (s : Finset ι)
      {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0)),
      (∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < V ω) → ∀ {N : ℝ≥0}, (∀ ω, σ ω ≤ N) → ∀ c : ℝ,
      ∀ᵐ ω ∂P, (∀ k ∈ s, IsLabel (W · ω) (tsupport (ψ k)) (σ ω)) →
        (P[fun ω' => cexp (Complex.I * (h ω' (c • ∑ k ∈ s, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
          cmKer P hσ.measurableSpace h W (σ ω) (c • ∑ k ∈ s, ψ k) ω

/-- **WFS target: the stopped whole-field kernel for couplings through a Galmarino stop** ((K) of
`Restart.StoppedExtendWF.StoppedKernelStatement` with part (i) for `IsCouplingThrough`; part (ii), for full couplings,
unchanged). For an ordered word and a measurable Galmarino rule `R` there are a relatively closed random set `A` of the
history with Borel avoidance events, a Borel kernel `G` and `d < 2` such that (i) for every coupling through
`V = R(history killed at V)`, off `A` the conditional characteristic function of the field given the killed history is
`G`, and the law of the killed history charges only histories with `dimH (A ∩ K) ≤ d` on compacts of `ℍ`; (ii) for
every full coupling the same kernel identity holds at `min (R(history), ζ)`. -/
def ThroughKernelStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∃ (A : HistorySpace nL nR → Set ℂ) (G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ) (d : ℝ),
      d < 2 ∧ (∀ γ, closure (A γ) ∩ (upperHalfPlaneOpens : Set ℂ) ⊆ A γ) ∧
      (∀ K : Set ℂ, IsCompact K → MeasurableSet {γ | Disjoint K (A γ)}) ∧ (∀ φ, Measurable (G φ)) ∧
      (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
        (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
        (ζ V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
        IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h →
        (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
        (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
          Disjoint (tsupport φ) (A (killedHistory W VL VR V ω)) →
            P[fun ω' => Complex.exp (↑(h ω' φ) * Complex.I) |
              MeasurableSpace.comap (killedHistory W VL VR V) inferInstance] ω =
              G φ (killedHistory W VL VR V ω)) ∧
        ∀ᵐ γ ∂(P.map (killedHistory W VL VR V)), ∀ K : Set ℂ, IsCompact K → K ⊆ upperHalfPlaneOpens →
          dimH (A γ ∩ K) ≤ ENNReal.ofReal d) ∧
      ∀ {Ω₀ : Type v} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
        (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ)
        (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞)
        (h₀ : Ω₀ → DistOn upperHalfPlaneOpens),
        IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ →
        ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω₀ ∂P₀,
          Disjoint (tsupport φ) (A (killedHistory W₀ VL₀ VR₀
            (fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀)) ω₀)) →
            P₀[fun ω' => Complex.exp (↑(h₀ ω' φ) * Complex.I) |
              MeasurableSpace.comap (killedHistory W₀ VL₀ VR₀
                (fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀))) inferInstance] ω₀ =
              G φ (killedHistory W₀ VL₀ VR₀ (fun ω₀ => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω₀)) (ζ₀ ω₀)) ω₀)

/-! ### (K) from the WFS target -/

section Reduce

/-- **Conditional expectations given a variable transfer along a measure-preserving map**: if `Y' = Y ∘ π` almost surely
and `P'.map π = P`, then `E_{P'}[g ∘ π | σ(Y')] = E_P[g | σ(Y)] ∘ π` almost surely. -/
theorem condExp_comap_comp_ae_eq {Ω Ω' Γ : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    [mΓ : MeasurableSpace Γ] {P : Measure Ω} [IsFiniteMeasure P] {P' : Measure Ω'} [IsFiniteMeasure P']
    {π : Ω' → Ω} (hπ : Measurable π) (hπP : P'.map π = P) {Y : Ω → Γ} (hY : Measurable Y) {Y' : Ω' → Γ}
    (hY' : Measurable Y') (hYY : ∀ᵐ p ∂P', Y' p = Y (π p)) {g : Ω → ℂ} (hg : Integrable g P) :
    P'[fun p => g (π p) | MeasurableSpace.comap Y' mΓ] =ᵐ[P'] fun p => P[g | MeasurableSpace.comap Y mΓ] (π p) := by
  set c := P[g | MeasurableSpace.comap Y mΓ] with hcdef
  have hc : StronglyMeasurable[MeasurableSpace.comap Y mΓ] c := stronglyMeasurable_condExp
  obtain ⟨c₀, hc₀, hcc⟩ := hc.exists_eq_measurable_comp
  have hcm : StronglyMeasurable c := hc.mono hY.comap_le
  have hcint : Integrable c P := integrable_condExp
  have hgP : Integrable (fun p => g (π p)) P' := by
    rw [← hπP] at hg; exact hg.comp_measurable hπ
  have hcP : Integrable (fun p => c (π p)) P' := by
    rw [← hπP] at hcint; exact hcint.comp_measurable hπ
  have hsets : ∀ T : Set Γ, (Y' ⁻¹' T : Set Ω') =ᵐ[P'] π ⁻¹' (Y ⁻¹' T) := fun T => by
    filter_upwards [hYY] with p hp
    change (Y' p ∈ T) = (Y (π p) ∈ T)
    rw [hp]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hY'.comap_le hgP (fun _ _ _ => hcP.integrableOn)
    (fun S hS _ => ?_) ?_).symm
  · obtain ⟨T, hT, rfl⟩ := hS
    have hYT : MeasurableSet (Y ⁻¹' T) := hY hT
    rw [setIntegral_congr_set (hsets T), setIntegral_congr_set (hsets T)]
    have h1 := MeasureTheory.setIntegral_map (μ := P') (g := π) hYT (f := c)
      (by rw [hπP]; exact hcm.aestronglyMeasurable) hπ.aemeasurable
    have h2 := MeasureTheory.setIntegral_map (μ := P') (g := π) hYT (f := g)
      (by rw [hπP]; exact hg.aestronglyMeasurable) hπ.aemeasurable
    rw [hπP] at h1 h2
    rw [← h1, ← h2, hcdef, setIntegral_condExp hY.comap_le hg ⟨T, hT, rfl⟩]
  · refine ⟨fun p => c₀ (Y' p), hc₀.comp_measurable (comap_measurable Y'), ?_⟩
    filter_upwards [hYY] with p hp
    rw [hp, hcc]
    rfl

variable {κ : ℝ}

/-- **(K) from the WFS target** (`κ > 0`): part (i) of `StoppedKernelStatement` for a stopped coupling is part (i) of
`ThroughKernelStatement` on its continuation (`exists_isCouplingThrough`), read back along `π` (the killed histories
agree almost surely, the conditional expectations transfer by `condExp_comap_comp_ae_eq`); part (ii) is the same. -/
theorem stoppedKernelStatement_of_through (hκ : 0 < κ) (hT : ThroughKernelStatement.{u, v} κ) :
    StoppedKernelStatement.{u, v} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg
  obtain ⟨A, G, d, hd, hAcl, hAm, hGm, hKS, hKF⟩ := hT xL xR ρL ρR hF R hRm hRg
  refine ⟨A, G, d, hd, hAcl, hAm, hGm, ?_, hKF⟩
  intro Ω mΩ P hP 𝓕 W VL VR B V h hSC hV
  obtain ⟨Ω', mΩ', P', hP', π, hπ, 𝓕', W', VL', VR', B', ζ', hπP, hCT, hag⟩ := exists_isCouplingThrough hκ hF hSC
  obtain ⟨-, -, hhm, -, hXV, -⟩ := hSC
  obtain ⟨hXV', -⟩ := hCT.2.2.2.2
  set V' : Ω' → ℝ≥0∞ := fun p => min (V (π p)) (ζ' p) with hV'
  have hY := measurable_killedHistory hXV
  have hY' := measurable_killedHistory hXV'
  have hYY : ∀ᵐ p ∂P', killedHistory W' VL' VR' V' p = killedHistory W VL VR V (π p) := by
    filter_upwards [hag] with p ⟨h1, h2⟩
    exact Exist.killedHistory_eq_of_agreeBefore (W₁ := fun t p => W t (π p)) (VL₁ := fun i t p => VL i t (π p))
      (VR₁ := fun j t p => VR j t (π p)) (ζ₁ := fun p => V (π p)) ⟨min_eq_left h1, h2⟩
  have hq : Measure.QuasiMeasurePreserving π P' P := ⟨hπ, hπP.le.absolutelyContinuous⟩
  have hVV : ∀ᵐ p ∂P', V' p = R (killedHistory W' VL' VR' V' p) := by
    filter_upwards [hq.ae hV, hYY, hag] with p h1 h2 ⟨h3, _⟩
    rw [h2]
    show min (V (π p)) (ζ' p) = _
    rw [min_eq_left h3]
    exact h1
  obtain ⟨hcf, hthin⟩ := hKS P' 𝓕' W' VL' VR' B' ζ' V' (fun p => h (π p)) hCT hVV
  refine ⟨fun φ => ?_, ?_⟩
  · set g : Ω → ℂ := fun ω => Complex.exp (↑(h ω φ) * Complex.I) with hgdef
    have hgm : Measurable g := Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp ((Sobolev.measurable_distOn_apply φ).comp hhm)).mul measurable_const)
    have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => by simp only [hgdef, Complex.norm_exp_ofReal_mul_I, le_refl])
    have htr := condExp_comap_comp_ae_eq hπ hπP hY hY' hYY hgi
    set Y := killedHistory W VL VR V with hYdef
    have hcm : Measurable (P[g | MeasurableSpace.comap Y inferInstance]) :=
      (stronglyMeasurable_condExp.mono hY.comap_le).measurable
    have hmeas : MeasurableSet {ω | Disjoint (tsupport φ) (A (Y ω)) →
        P[g | MeasurableSpace.comap Y inferInstance] ω = G φ (Y ω)} := by
      have h1 : MeasurableSet {ω | Disjoint (tsupport φ) (A (Y ω))} := hY (hAm _ φ.hasCompactSupport)
      have h2 : MeasurableSet {ω | P[g | MeasurableSpace.comap Y inferInstance] ω = G φ (Y ω)} :=
        measurableSet_eq_fun hcm ((hGm φ).comp hY)
      have e : {ω | Disjoint (tsupport φ) (A (Y ω)) → P[g | MeasurableSpace.comap Y inferInstance] ω = G φ (Y ω)} =
          {ω | Disjoint (tsupport φ) (A (Y ω))}ᶜ ∪
            {ω | P[g | MeasurableSpace.comap Y inferInstance] ω = G φ (Y ω)} := by
        ext ω
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
        tauto
      rw [e]
      exact h1.compl.union h2
    have key : ∀ᵐ ω ∂(P'.map π), Disjoint (tsupport φ) (A (Y ω)) →
        P[g | MeasurableSpace.comap Y inferInstance] ω = G φ (Y ω) := by
      rw [ae_map_iff hπ.aemeasurable hmeas]
      filter_upwards [hcf φ, htr, hYY] with p h1 h2 h3 hdisj
      rw [← h3] at hdisj
      rw [← h3]
      exact h2.symm.trans (h1 hdisj)
    rwa [hπP] at key
  · have hlaw : P'.map (killedHistory W' VL' VR' V') = P.map (killedHistory W VL VR V) := by
      rw [Measure.map_congr hYY, ← hπP, Measure.map_map hY hπ]
      rfl
    rw [hlaw] at hthin
    exact ae_of_ae_map hY.aemeasurable hthin

/-- **Aux. lemma 54 for Galmarino stops from the WFS target alone** (`κ > 0`): (CONT) is proved
(`Restart.StoppedCont.stoppedContinuationStatement`) and (K) follows from `ThroughKernelStatement`. -/
theorem stoppedHullExtendGKStatement_of_through (hκ : 0 < κ) (hT : ThroughKernelStatement.{u, u} κ) :
    StoppedHullExtendGKStatement.{u} κ :=
  stoppedHullExtendGKStatement_of_inputs hκ (Restart.StoppedCont.stoppedContinuationStatement hκ)
    (stoppedKernelStatement_of_through hκ hT)

/-- **`RLC.FlowLocalityStatement` from (L1G), the WFS target and Theorems 1.2–1.3** (PROVE-DOMAINMARKOV10's
`flowLocalityStatement_of_inputs` with (CONT) discharged). -/
theorem flowLocalityStatement_of_through (hL1 : FlowLineStopIdentGStatement.{u})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → ThroughKernelStatement.{u, u} κ) (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : RLC.FlowLocalityStatement.{u} :=
  flowLocalityStatement_of_inputs hL1 (fun _ hκ _ => Restart.StoppedCont.stoppedContinuationStatement hκ)
    (fun κ hκ hκ4 => stoppedKernelStatement_of_through hκ (hT κ hκ hκ4)) h12p h13

end Reduce

end WFS

end InteractingSLE
