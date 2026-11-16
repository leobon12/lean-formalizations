/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermStop
import InteractingSLE.Spec.Supplement.AStopSafePair
import InteractingSLE.Spec.Supplement.OrdModelSeed

/-!
# The source inputs of the first path in the chart of the completed second path

Packet PROVE-RC-TERM, second run (ruling R124). For one own time `N` and one force type:

* **`integrable_term`**: the pairings of the field `flowField 0 (θ₁χ) (flowField τ 0 (termField κ x₂ r h))` are
  integrable on every event of the force type. Proof: (R1) at own time `N` (`ae_condExp_recField_own`, conditional on
  the record), translated to the seed (`RLC.AStopSafe.ae_condExp_cexp_flowField_eq_gaussCF_on`), and
  `RLC.AStopSafe.integrable_flowField_of_wordCF_on` on the record event of the type, which contains the event.
* **`sourceInputs_term`**: `RLC.OrdModel.AStopSourceInputs` for the seed `τ = pSeed`, the word `shiftW τ (pWord …)`,
  the field `flowField τ 0 (termField …)`, the capacity lifetime `aLife pPath pStop` and the path `aPath + τ − τ`:
  items 2–3 from `exists_termProc`, (S) and (L) from `hasSafe_term` (field identified by `chartTransport_physChart`),
  item 6 from `ae_stopFacts_term`.
* **`ae_codeMatch_term`**: on such an event, the lifetime is at most the canonical code's lifetime and the chart path
  `aPath + τ` is the decoded canonical flow (`RLC.OrdModel.exists_seedModelTransferJ_rule_of_sourceInputs`,
  `ae_codeMatch_of_seedModelTransferJ`; Theorem 1.3 is a hypothesis, discharged by the closed theorem downstream).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Restart Restart.RetAux79 Restart.DomainMarkov Supp7 Sec7 Sec7.Lemma76F Sec7.PocketTraversal
  Exist.Staged Exist.StagedLaw Sec2.Assembly RLC.AStopProc RLC.AStopSafe
open Restart.DomainMarkov.K2
open Theorem14 Theorem14.SB
open Exist.StagedLaw.BoundaryWord (shiftW isSorted_shiftW measurable_shiftW)

section Inputs

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {κ : ℝ}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}

/-- **Integrable pairings on an event of one force type** (see the module docstring). -/
theorem integrable_term (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps)
    {c₂ : BoundaryWord} {E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE₂m : Measurable E₂) (hreg₂ : ∀ ω, IsRegularDriver (E₂ ω))
    (hfl₂ : IsFlowLineDriver κ c₂.fn c₂.jumps θ₂ P (fun ω => Exist.flowField x₂ 0 (h ω))
      (fun s ω => (E₂ ω).1 s) (fun ω => (E₂ ω).2))
    (N : ℝ≥0) (a : ForceWordType) {M : Set Ω}
    (htype : ∀ ω ∈ M, lWord κ θ₂ c₂ N E₂ x₁ x₂ ω ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
    (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Exist.flowField 0 (θ₁ * chiC κ)
      (Exist.flowField (pSeed N E₂ x₁ x₂ ω) 0 (termField κ x₂ (pRec N E₂ ω) (h ω))) φ) (P.restrict M) := by
  classical
  set 𝒢 : MeasurableSpace Ω := MeasurableSpace.comap (pRec N E₂) inferInstance with h𝒢def
  let _ : MeasurableSpace Ω := mΩ
  have hrm : Measurable (pRec N E₂) := measurable_recOf hE₂m hreg₂ _
  have h𝒢 : 𝒢 ≤ mΩ := hrm.comap_le
  have hr : Measurable[𝒢] (pRec N E₂) := comap_measurable _
  have hτ : Measurable[𝒢] (pSeed N E₂ x₁ x₂) := measurable_pSeed hr x₁ x₂
  have hβ : Measurable[𝒢] (lWord κ θ₂ c₂ N E₂ x₁ x₂) :=
    measurable_shiftW.comp (hτ.prodMk (measurable_pWord hr κ θ₂ c₂))
  set M' := {ω | lWord κ θ₂ c₂ N E₂ x₁ x₂ ω ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR} with hM'
  have hM'm : MeasurableSet[𝒢] M' := hβ (FCDet.measurableSet_typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
  have hX : Measurable fun ω => termField κ x₂ (pRec N E₂ ω) (h ω) := by
    change Measurable ((fun p : RecData × DistOn upperHalfPlaneOpens => termField κ x₂ p.1 p.2) ∘
      fun ω => (pRec N E₂ ω, h ω))
    exact (measurable_termField κ x₂).comp (hrm.prodMk hh.1)
  have hHc : Measurable fun ω => Exist.flowField (pSeed N E₂ x₁ x₂ ω) 0 (termField κ x₂ (pRec N E₂ ω) (h ω)) := by
    change Measurable ((fun p : ℝ × DistOn upperHalfPlaneOpens => Exist.flowField p.1 0 p.2) ∘
      fun ω => (pSeed N E₂ x₁ x₂ ω, termField κ x₂ (pRec N E₂ ω) (h ω)))
    exact measurable_flowField_uncurry.comp ((hτ.mono h𝒢 le_rfl).prodMk hX)
  have hcf0 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M' →
      P[fun ω => Complex.exp (Complex.I * (termField κ x₂ (pRec N E₂ ω) (h ω) φ : ℂ)) | 𝒢] ω =
        gaussCF (pWord κ θ₂ c₂ N E₂ ω) φ := fun φ => by
    filter_upwards [ae_condExp_recField_own hκ c₂ θ₂ N P (fun ω => Exist.flowField x₂ 0 (h ω)) E₂ hE₂m hreg₂
      hfl₂ φ] with ω hω _
    exact hω
  have hcf := fun φ => ae_condExp_cexp_flowField_eq_gaussCF_on h𝒢 hX hM'm hcf0 hτ φ
  have hi := integrable_flowField_of_wordCF_on h𝒢 hM'm hβ
    (Eventually.of_forall fun ω _ => isSorted_shiftW (isSorted_stopWord κ _) _) hHc hcf hκ θ₁ a
    (Eventually.of_forall fun ω hω => hω) φ
  exact hi.mono_measure (Measure.restrict_mono (fun ω hω => htype ω hω) le_rfl)

/-- **The A-stopped source inputs at one own time and one force type** (see the module docstring). -/
theorem sourceInputs_term (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hθ : θ₁ < θ₂) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {c₂ : BoundaryWord} (hcJ : c₂.jumps = jumps.image (· - x₂))
    (hcb : ∀ y ∉ jumps.image (· - x₂), c₂.fn y = b (y + x₂))
    {E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE₂m : Measurable E₂) (hreg₂ : ∀ ω, IsRegularDriver (E₂ ω))
    (hE₂2 : ∀ ω, (E₂ ω).2 = ζ₂ ω)
    (hfl₂ : IsFlowLineDriver κ c₂.fn c₂.jumps θ₂ P (fun ω => Exist.flowField x₂ 0 (h ω))
      (fun s ω => (E₂ ω).1 s) (fun ω => (E₂ ω).2))
    (htrace₂ : ∀ᵐ ω ∂P, IsGeneratingTrace (E₂ ω).1 (ζ₂ ω) (fun s => η₂ ω s - x₂))
    {N : ℝ≥0} {η₁' ηb₂ : Ω → ℝ≥0 → ℂ}
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηb₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s))
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] M)
    (hMg : ∀ ω ∈ M, IsTermGood N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω) (hMζ : ∀ ω ∈ M, 0 < ζ₁ ω)
    (ho : AObs (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂)
      (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂))
    (a : ForceWordType)
    (htype : ∀ ω ∈ M, lWord κ θ₂ c₂ N E₂ x₁ x₂ ω ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR) :
    RLC.OrdModel.AStopSourceInputs κ θ₁ P M (pSeed N E₂ x₁ x₂)
      (fun ω => shiftW (pSeed N E₂ x₁ x₂ ω) (pWord κ θ₂ c₂ N E₂ ω))
      (fun ω => Exist.flowField (pSeed N E₂ x₁ x₂ ω) 0 (termField κ x₂ (pRec N E₂ ω) (h ω)))
      (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂))
      (fun ω t => (aPath (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω t +
        (pSeed N E₂ x₁ x₂ ω : ℂ)) - (pSeed N E₂ x₁ x₂ ω : ℂ)) := by
  classical
  set Γ := pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂ with hΓ
  set L := pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂ with hL
  obtain ⟨hQa, W, h0, hWc, hW0, hWa, hV, hγm, hγc, hγ0, hgen⟩ := exists_termProc ho hMg
  obtain ⟨ηc₁, ηc₂, d⟩ := exists_isLineData hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ 0 N
  have hrecm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] (pRec N E₂) :=
    measurable_recOf_retSigma76 hκ hE₂m hreg₂ hE₂2 hfl₂ htrace₂ (measurable_lifetime_of_isFlowLine hη₂)
      d.cont₂ d.meas₂ d.ae₂
  have hτm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] (pSeed N E₂ x₁ x₂) := measurable_pSeed hrecm x₁ x₂
  have hcm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N]
      fun ω => shiftW (pSeed N E₂ x₁ x₂ ω) (pWord κ θ₂ c₂ N E₂ ω) :=
    measurable_shiftW.comp (hτm.prodMk (measurable_pWord hrecm κ θ₂ c₂))
  have hrm : Measurable (pRec N E₂) := measurable_recOf hE₂m hreg₂ _
  have hX : Measurable fun ω => termField κ x₂ (pRec N E₂ ω) (h ω) := by
    change Measurable ((fun p : RecData × DistOn upperHalfPlaneOpens => termField κ x₂ p.1 p.2) ∘
      fun ω => (pRec N E₂ ω, h ω))
    exact (measurable_termField κ x₂).comp (hrm.prodMk hh.1)
  have hHc : Measurable fun ω => Exist.flowField (pSeed N E₂ x₁ x₂ ω) 0 (termField κ x₂ (pRec N E₂ ω) (h ω)) := by
    change Measurable ((fun p : ℝ × DistOn upperHalfPlaneOpens => Exist.flowField p.1 0 p.2) ∘
      fun ω => (pSeed N E₂ x₁ x₂ ω, termField κ x₂ (pRec N E₂ ω) (h ω)))
    exact measurable_flowField_uncurry.comp ((hτm.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ 0 N) le_rfl).prodMk hX)
  obtain ⟨hS, hL'⟩ := hasSafe_term hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ hE₂m hreg₂ hE₂2 hfl₂ htrace₂ ha₁ hag₂ hM hMg ho
    a htype hWc hW0 hgen hQa
  have hXe : ∀ᵐ ω ∂P, ω ∈ M → Exist.flowField 0 (θ₁ * chiC κ)
      (Exist.flowField (pSeed N E₂ x₁ x₂ ω) 0 (termField κ x₂ (pRec N E₂ ω) (h ω))) =
        Chart.chartTransport (isConformal_lChart x₁ x₂ N E₂ ω) 1 (θ₁ * chiC κ) (chiC κ) (h ω) :=
    Eventually.of_forall fun ω _ =>
      (chartTransport_physChart κ x₂ (pRec N E₂ ω) (pSeed N E₂ x₁ x₂ ω) (θ₁ * chiC κ) (h ω)).symm
  obtain ⟨hpos, hthr, havoid, hend⟩ :=
    ae_stopFacts_term hκ hκ4 hb hh hθ hη₁ hcJ hcb ha₁ hMg hMζ a htype hWc hW0 hgen
  refine ⟨a, aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M Γ hQa, W, pEnds N E₂ x₁ x₂, M.indicator (aLife Γ L),
    aTrace M Γ L, h0 _ hM, hcm.mono h0 le_rfl, hHc, hWc, hW0, hWa, hV, hγm, hγc, hγ0,
    (measurable_pEnds hrecm x₁ x₂).mono h0 le_rfl, hτm.mono h0 le_rfl, ?_,
    Eventually.of_forall fun ω hω => htype ω hω,
    fun φ => integrable_term hκ hh hE₂m hreg₂ hfl₂ N a htype φ,
    RetFin.hasSafeLaw_congr_field hXe hS, RetFin.hasSafeMembers_congr_field hXe hL', ?_, hpos, hthr, havoid, hend⟩
  · exact Eventually.of_forall fun ω hω => ⟨indicator_of_mem hω _, fun t _ => by
      rw [aTrace_of_mem hω]
      exact (add_sub_cancel_right _ _).symm⟩
  · exact Eventually.of_forall fun ω hω => by
      rw [indicator_of_mem hω, aTrace_of_mem hω]
      exact hgen ω hω

/-- **The code match at one own time and one force type**: on an event of good samples of one force type with
positive probability, the capacity lifetime is at most the canonical code's lifetime and the chart path `aPath + τ`
is the decoded canonical flow of the chart datum (see the module docstring). -/
theorem ae_codeMatch_term (h13 : Exist.Theorem13Statement.{0}) (hL75 : Theorem15.Lemma75Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hθ : θ₁ < θ₂) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {c₂ : BoundaryWord} (hcJ : c₂.jumps = jumps.image (· - x₂))
    (hcb : ∀ y ∉ jumps.image (· - x₂), c₂.fn y = b (y + x₂))
    {E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE₂m : Measurable E₂) (hreg₂ : ∀ ω, IsRegularDriver (E₂ ω))
    (hE₂2 : ∀ ω, (E₂ ω).2 = ζ₂ ω)
    (hfl₂ : IsFlowLineDriver κ c₂.fn c₂.jumps θ₂ P (fun ω => Exist.flowField x₂ 0 (h ω))
      (fun s ω => (E₂ ω).1 s) (fun ω => (E₂ ω).2))
    (htrace₂ : ∀ᵐ ω ∂P, IsGeneratingTrace (E₂ ω).1 (ζ₂ ω) (fun s => η₂ ω s - x₂))
    {N : ℝ≥0} {η₁' ηb₂ : Ω → ℝ≥0 → ℂ}
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηb₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s))
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] M)
    (hMg : ∀ ω ∈ M, IsTermGood N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω) (hMζ : ∀ ω ∈ M, 0 < ζ₁ ω)
    (ho : AObs (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂)
      (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂))
    (a : ForceWordType)
    (htype : ∀ ω ∈ M, lWord κ θ₂ c₂ N E₂ x₁ x₂ ω ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
    (hPM : P M ≠ 0)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ₁ Fc) :
    ∀ᵐ ω ∂P, ω ∈ M → aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω ≤
        (Fc ((pWord κ θ₂ c₂ N E₂ ω, pSeed N E₂ x₁ x₂ ω), termField κ x₂ (pRec N E₂ ω) (h ω))).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω →
        aPath (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω t + (pSeed N E₂ x₁ x₂ ω : ℂ) =
          decPath (Fc ((pWord κ θ₂ c₂ N E₂ ω, pSeed N E₂ x₁ x₂ ω), termField κ x₂ (pRec N E₂ ω) (h ω))) t := by
  obtain ⟨T, hT⟩ := RLC.OrdModel.exists_seedModelTransferJ_rule_of_sourceInputs (P := P) (κ := κ) (θ := θ₁)
    (M := M) (c := pWord κ θ₂ c₂ N E₂) (τ := pSeed N E₂ x₁ x₂)
    (Hc := fun ω => termField κ x₂ (pRec N E₂ ω) (h ω))
    (V := aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂))
    (γ := fun ω t => aPath (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω t +
      (pSeed N E₂ x₁ x₂ ω : ℂ))
    (sourceInputs_term hL75 hκ hκ4 hb hθ hh hη₁ hη₂ hu₀ hcJ hcb hE₂m hreg₂ hE₂2 hfl₂ htrace₂ ha₁ hag₂ hM hMg hMζ
      ho a htype) hPM
  exact RLC.OrdModel.ae_codeMatch_of_seedModelTransferJ T (retSigma76_le P η₁ η₂ ζ₁ ζ₂ 0 N _ hM) hT h13 hκ hFc

end Inputs

end Term

end InteractingSLE.RealContact
