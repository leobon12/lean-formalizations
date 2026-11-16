/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermSafe
import InteractingSLE.Spec.Restart.FCK2TermSource
import InteractingSLE.Spec.Restart.FCK2BdryVisit
import InteractingSLE.Spec.Restart.FCK2DynCollision
import InteractingSLE.Spec.Restart.FCK2SourceCollision
import InteractingSLE.Spec.Restart.RetPlumbProofDriverModelInputs
import InteractingSLE.Spec.Supplement.RLCGJump

/-!
# The stop facts of the first path in the chart of the completed second path

Packet PROVE-RC-TERM, second run (ruling R124). Item 6 of `RLC.OrdModel.AStopSourceInputs` for the processes of
`TermProcMain` (supported lifetime `M.indicator (aLife pPath pStop)`, supported path `aTrace M pPath pStop`, stop set
`aStopSet (pEnds …)`):

* `lt_of_gap`: the angle gap `κ/2 − 2 ≤ cumWeightRight κ (−λ − θ₁χ + θ₂χ)` gives `θ₁ < θ₂`;
* **`ae_stopFacts_term`**: almost surely on a good event of one force type, the lifetime is positive, at most the
  threshold time of the typed geometric coordinates, the path avoids the stop set strictly before the lifetime, and
  a finite lifetime is the threshold time or a visit of the stop set.

Proof: the pathwise `Term.IsKSample.stop_facts` with the untouched word and the admissible seed of `TermK2Word`, the
almost-sure flow-line facts of the first path (live incident bounds `FCPlumb.ae_live_real_incident_bounds`, jump
avoidance `RLC.jumpVisitStatement`, the terminal bad incident `FCPlumb.ae_original_terminal_bad_incident`), and the
threshold-time conversion `RetAux79.life_le_thr_of_retPrelifeNonThreshold`,
`FCPlumb.prelifeNonThreshold_of_boundary_checks`, `FCPlumb.thr_le_of_force_threshold` (the pattern of
`RLC.AStopPath.ae_aStopPath_fst`).
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
  Exist.Staged Exist.StagedLaw Sec2.Assembly RLC.AStopProc
open Theorem14 Theorem14.SB
open LP (reflectC)
open PiecewiseConstantBoundaryData (leftLim rightLim)

/-- **The angle gap orders the angles.** -/
theorem lt_of_gap {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hgap : κ / 2 - 2 ≤ Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ)) : θ₁ < θ₂ := by
  have hl := Sec4.sleLambda_pos hκ
  have hc := Sec4.chiC_pos hκ hκ4
  unfold Sec4.cumWeightRight at hgap
  have h1 : κ / 2 - 1 ≤ ((-sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ) / sleLambda κ := by linarith
  rw [le_div_iff₀ hl] at h1
  have h2 : 0 < (θ₂ - θ₁) * chiC κ := by nlinarith
  by_contra hle
  have hle' : θ₂ ≤ θ₁ := not_lt.mp hle
  nlinarith

section Stop

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ : Ω → ℝ≥0 → ℂ} {ζ₁ : Ω → ℝ≥0∞} {κ : ℝ}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}

/-- **The stop facts** (see the module docstring). -/
theorem ae_stopFacts_term (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hθ : θ₁ < θ₂) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    {c₂ : BoundaryWord} (hcJ : c₂.jumps = jumps.image (· - x₂))
    (hcb : ∀ y ∉ jumps.image (· - x₂), c₂.fn y = b (y + x₂))
    {N : ℝ≥0} {E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {η₁' ηb₂ : Ω → ℝ≥0 → ℂ}
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    {M : Set Ω} (hMg : ∀ ω ∈ M, IsTermGood N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω) (hMζ : ∀ ω ∈ M, 0 < ζ₁ ω)
    (a : ForceWordType)
    (htype : ∀ ω ∈ M, lWord κ θ₂ c₂ N E₂ x₁ x₂ ω ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (hgen : ∀ ω ∈ M, IsGeneratingTrace (W · ω)
      (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω)
      (aPath (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω)) :
    (∀ᵐ ω ∂P, ω ∈ M → 0 < M.indicator (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂)) ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → M.indicator (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂)) ω ≤
      FCDet.thr a.rhoL a.rhoR W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a) (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a) ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t →
      (t : ℝ≥0∞) < M.indicator (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂)) ω →
      aTrace M (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω t ∉
        RLC.OrdModel.aStopSet (pEnds N E₂ x₁ x₂ ω)) ∧
    (∀ᵐ ω ∂P, ω ∈ M →
      M.indicator (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂)) ω ≠ ⊤ →
      M.indicator (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂)) ω =
          FCDet.thr a.rhoL a.rhoR W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a) (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a) ω ∨
        aTrace M (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω
            (M.indicator (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂)) ω).toNNReal ∈
          RLC.OrdModel.aStopSet (pEnds N E₂ x₁ x₂ ω)) := by
  classical
  set Γ := pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂ with hΓ
  set L := pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂ with hL
  set xL := lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a with hxL
  set xR := lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a with hxR
  have hv := FCPlumb.ae_live_real_incident_bounds hκ hκ4 hb hh hη₁
  have hj := RLC.jumpVisitStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁
  have hbad := FCPlumb.ae_original_terminal_bad_incident hκ hb hη₁
  have hF : ∀ᵐ ω ∂P, ω ∈ M → 0 < aLife Γ L ω ∧
      ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR 0 (xL ω) (xR ω) ∧
      (∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < aLife Γ L ω →
        ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR (W q ω)
          (fun i => geomLW W xL i q ω) (fun j => geomRW W xR j q ω)) ∧
      (∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < aLife Γ L ω →
        aPath Γ L ω q ∉ RLC.OrdModel.aStopSet (pEnds N E₂ x₁ x₂ ω)) ∧
      (aLife Γ L ω ≠ ⊤ →
        ForceWord.ThresholdCondition a.rhoL a.rhoR (W (aLife Γ L ω).toNNReal ω)
            (fun i => geomLW W xL i (aLife Γ L ω).toNNReal ω)
            (fun j => geomRW W xR j (aLife Γ L ω).toNNReal ω) ∨
          aPath Γ L ω (aLife Γ L ω).toNNReal ∈ RLC.OrdModel.aStopSet (pEnds N E₂ x₁ x₂ ω)) := by
    filter_upwards [hv, hj, hbad, ha₁] with ω hvω hjω hbω haω hω
    have g := hMg ω hω
    obtain ⟨q, w, hq, hs⟩ := g.sample
    -- the contact set: the second version up to the record time and the first seed
    set Kp : Set ℂ := ηb₂ ω '' Icc 0 (pT N E₂ ω) ∪ {(x₁ : ℂ)} with hKp
    have hKc : IsClosed Kp := (isCompact_Icc.image g.cont).isClosed.union isClosed_singleton
    have hK : ∀ z : ℂ, z ∈ Kp ↔
        reflectC (z - (x₁ : ℂ)) ∈ retSet (fun s => reflectC (pRho₂ ηb₂ x₂ ω s)) (pT N E₂ ω) (x₁ - x₂) ∨
          z = (x₁ : ℂ) := fun z => by
      rw [hKp, mem_union, mem_singleton_iff]
      exact or_congr_left (mem_retSet_iff' (ηb₂ ω) x₁ x₂ (pT N E₂ ω) z).symm
    have hu := hs.isUntouchedWord hκ (θ₂ := θ₂) (r := pRec N E₂ ω) rfl (rtime_pRec N E₂ ω) rfl hcJ hcb hK
    -- the first version is the first path through its lifetime
    have hρ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₁ ω → pRho₁ η₁' x₁ ω t + (x₁ : ℂ) = η₁ ω t := fun t ht => by
      simp only [pRho₁, sub_add_cancel, haω t ht]
    have hv' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₁ ω → ∀ y : ℝ, pRho₁ η₁' x₁ ω t + (x₁ : ℂ) = y →
        (y ≤ x₁ → leftLim b y + θ₁ * chiC κ < sleLambda κ) ∧
          (x₁ ≤ y → -sleLambda κ < rightLim b y + θ₁ * chiC κ) :=
      fun t ht y hy => hvω t ht y ((hρ t ht.le).symm.trans hy)
    have hj' : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ₁ ω → ∀ y ∈ jumps, y ≠ x₁ →
        pRho₁ η₁' x₁ ω t + (x₁ : ℂ) ≠ y :=
      fun t ht0 ht y hy hyx he => hjω t ht0 ht y hy hyx ((hρ t ht.le).symm.trans he)
    have h0 : η₁ ω 0 = (x₁ : ℂ) := by
      rw [← hρ 0 (by rw [ENNReal.coe_zero]; exact zero_le), hs.rho_zero, zero_add]
    have hv0 := hvω 0 (hMζ ω hω) x₁ h0
    have hseed := hs.isAdmissibleSeed hκ hκ4 hq (r := pRec N E₂ ω) rfl (rtime_pRec N E₂ ω) rfl hθ hcb
      ⟨hv0.1 le_rfl, hv0.2 le_rfl⟩
    have hbad' : ζ₁ ω ≠ ⊤ → (pRho₁ η₁' x₁ ω (ζ₁ ω).toNNReal + (x₁ : ℂ)).im = 0 ∧
        (((pRho₁ η₁' x₁ ω (ζ₁ ω).toNNReal + (x₁ : ℂ)).re ≤ x₁ ∧
            sleLambda κ ≤ leftLim b (pRho₁ η₁' x₁ ω (ζ₁ ω).toNNReal + (x₁ : ℂ)).re + θ₁ * chiC κ) ∨
          (x₁ ≤ (pRho₁ η₁' x₁ ω (ζ₁ ω).toNNReal + (x₁ : ℂ)).re ∧
            rightLim b (pRho₁ η₁' x₁ ω (ζ₁ ω).toNNReal + (x₁ : ℂ)).re + θ₁ * chiC κ ≤ -sleLambda κ)) := by
      intro hfin
      rw [hρ _ ENNReal.coe_toNNReal_le_self]
      exact hbω (ζ₁ ω).toNNReal (ENNReal.toNNReal_pos (hMζ ω hω).ne' hfin) (ENNReal.coe_toNNReal hfin)
    exact hs.stop_facts hq x₁ hKc hK hκ hb hu hv' hj' hseed hbad' (htype ω hω) (hWc ω) (hW0 ω) (hgen ω hω)
  have hthr : ∀ᵐ ω ∂P, ω ∈ M → M.indicator (aLife Γ L) ω ≤ FCDet.thr a.rhoL a.rhoR W xL xR ω := by
    apply RetAux79.life_le_thr_of_retPrelifeNonThreshold hWc
    refine FCPlumb.prelifeNonThreshold_of_boundary_checks (γ := aTrace M Γ L) hWc hW0
      (fun ω i => lXL_nonpos κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω i) (fun ω j => lXR_nonneg κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω j)
      (Eventually.of_forall fun ω hω => ?_) (hF.mono fun ω h hω => (h hω).2.1)
      (hF.mono fun ω h hω q hq0 hq _ => (h hω).2.2.1 q hq0 (by rwa [indicator_of_mem hω] at hq))
    rw [indicator_of_mem hω, aTrace_of_mem hω]
    exact hgen ω hω
  refine ⟨hF.mono fun ω h hω => by rw [indicator_of_mem hω]; exact (h hω).1, hthr,
    hF.mono fun ω h hω t ht0 ht => ?_, ?_⟩
  · rw [indicator_of_mem hω] at ht
    rw [aTrace_of_mem hω]
    exact (h hω).2.2.2.1 t ht0 ht
  · filter_upwards [hF, hthr] with ω h hle hω hfin
    rw [indicator_of_mem hω] at hfin hle ⊢
    rw [aTrace_of_mem hω]
    rcases (h hω).2.2.2.2 hfin with h1 | h1
    · left
      refine le_antisymm (hle hω) ?_
      have h2 := FCPlumb.thr_le_of_force_threshold (ρL := a.rhoL) (ρR := a.rhoR) (xL := xL) (xR := xR) hWc
        (ω := ω) (T := (aLife Γ L ω).toNNReal) h1
      rwa [ENNReal.coe_toNNReal hfin] at h2
    · exact Or.inr h1

end Stop

end Term

end InteractingSLE.RealContact
