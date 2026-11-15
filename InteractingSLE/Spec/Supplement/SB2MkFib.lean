/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MkPull
import InteractingSLE.Spec.Supplement.SBLuAmb
import InteractingSLE.Spec.Supplement.SB2LkFF

/-!
# SB2(2)'s stage pull-back under the left ambient bound on all of `x < 0`

Packet PROVE-SB2-LCMEAN, round 8. The one clause of `Ln.IsStagePullback` not supplied by the run-chart package is the
finiteness of the fibres of the boundary map `gf`. For the lower walk it follows from the landed path route (the
retained prefix with a bridge is the image of a path with finite fibres, `LuM.pinv_prefix_walk`, then
`Lk.finite_fibre_of_pinv`), whose almost-sure inputs (`LuM.ae_walkTipCoordinates_lower`, `LuM.ae_injOn_trOf_walk`)
need R95's `Ly.LowerLeftAdmissible` (the left bound at every `x < 0`):

* `eqOn_Hbar_of_eqOn_H`: two maps continuous on `ℍ̄` that agree on `ℍ` agree on `ℍ̄`;
* **`ae_finiteFibre_walk`**: under `Ly.LowerLeftAdmissible`, almost surely, at every stage of the lower walk that is
  not finished, every continuous extension to `ℍ̄` of the inverse run chart has finite fibres on `ℍ̄`;
* **`ae_isStagePullback_fill_adm`**: under `Ly.LowerLeftAdmissible`, SB2(2)'s stage pull-back
  (`Mk.ae_isStagePullback_fill`) holds outright almost surely on the capped launch event at an upper launch.

SB2(2)'s own setting (`Lf.SB2LowerSetting`) gives the left bound on `(u, 0)` only; there the finite fibres remain an
input.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMap fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mk

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField

/-- Two maps continuous on `ℍ̄` that agree on `ℍ` agree on `ℍ̄`. -/
theorem eqOn_Hbar_of_eqOn_H {g g' : ℂ → ℂ} (hg : ContinuousOn g Hbar) (hg' : ContinuousOn g' Hbar)
    (he : EqOn g g' H) : EqOn g g' Hbar := by
  intro q hq
  have := GW1P.neBot_nhdsWithin_H hq
  have hHHbar : H ⊆ Hbar := fun z hz => show 0 ≤ z.im from le_of_lt hz
  have t1 : Tendsto g (𝓝[H] q) (𝓝 (g q)) := (hg q hq).tendsto.mono_left (nhdsWithin_mono _ hHHbar)
  have t2 : Tendsto g (𝓝[H] q) (𝓝 (g' q)) :=
    ((hg' q hq).tendsto.mono_left (nhdsWithin_mono _ hHHbar)).congr'
      (eventually_nhdsWithin_of_forall fun w hw => (he hw).symm)
  exact tendsto_nhds_unique t1 t2

section SB2

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Finite fibres of the lower walk's boundary maps** under the left ambient bound on all of `x < 0`: almost surely,
at every stage that is not finished, every continuous extension to `ℍ̄` of the inverse run chart has finite fibres. -/
theorem ae_finiteFibre_walk (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hadm : Ly.LowerLeftAdmissible κ b jumps)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω))
    (hR : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) n) ≠
        GW1Conn.stDone →
      ∀ g : ℂ → ℂ, ContinuousOn g Hbar →
        EqOn g (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E j ω) n).2.2.2.2.1.2.1 H →
        ∀ z, (g ⁻¹' {z} ∩ Hbar).Finite := by
  filter_upwards [LuM.ae_walkTipCoordinates_lower hκ hb hh hadm hS hreg hR,
    ae_all_iff.2 fun j => LuM.ae_injOn_trOf_walk hκ hκ4 hb hS hreg hR j, hR.ae_pieceRegular]
    with ω htip hinj hr n hnot g hgc hgi
  obtain ⟨-, gc, C, hD, -, -, -, hgcc, hgci, ⟨C₁, C₂, hC₁, hgb⟩, -, -⟩ :=
    S3.Canon.runChart_package (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) hr n hnot
  have hgg : EqOn g gc Hbar := eqOn_Hbar_of_eqOn_H hgc hgcc fun w hw => (hgi hw).trans (hgci hw).symm
  have hgb' : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂ :=
    ⟨C₁, C₂, hC₁, fun w hw => by rw [hgg (show w ∈ Hbar from hw)]; exact hgb w hw⟩
  exact Lk.finite_fibre_of_pinv (LuM.pinv_prefix_walk (fun j c θ' hlj => hr j c θ' hlj)
    (fun j hlj => hinj j hlj) htip le_rfl n hnot).1 hD hgc hgi hgb'

open Mi Mf in
/-- **SB2(2)'s stage pull-back under the left ambient bound on all of `x < 0`**: `ae_isStagePullback_fill` with the
finite fibres supplied by `ae_finiteFibre_walk`. -/
theorem ae_isStagePullback_fill_adm (h13 : Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hadm : Ly.LowerLeftAdmissible κ b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) (τ : ℝ≥0) {A₁ A₂ : Ω → Set ℂ}
    (hA₁ : ∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω)
    (hA₂ : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ τ →
      (∀ v ∈ H, (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 v ∈ A₂ ω ↔
        v ∈ fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ τ ω)
          (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ τ ω)) ∧
      H \ ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).dom : Set ℂ) ⊆ A₂ ω) :
    ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ τ →
      (ExplState.run κ b jumps (Lu.upperSpec u l)
        (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none →
      ∃ g : ℂ → ℂ, Ln.IsStagePullback (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω) g (A₁ ω) (A₂ ω)
        {w | (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 w ∈ A₁ ω}
        (fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ τ ω)
          (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ τ ω)) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hRw := stagedPiecesRegular_of_regular h13 hκ hb (hE' _ hw) (hreg' _)
  filter_upwards [ae_isStagePullback_fill h13 hκ hb hE hER hlθ k ℓ hℓ τ hA₁ hA₂,
    ae_finiteFibre_walk hκ hκ4 hb hh hadm (hE' _ hw) (hreg' _) hRw] with ω hpb hfib hcap hlu
  obtain ⟨g, hgc, hgi, hpb'⟩ := hpb hcap hlu
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hcap.1
  exact ⟨g, hpb' (hfib ℓ (WalkIntRunChron.not_done_of_launch _ _ hl) g hgc hgi)⟩

end SB2

end InteractingSLE.Theorem14.SB.Mk
