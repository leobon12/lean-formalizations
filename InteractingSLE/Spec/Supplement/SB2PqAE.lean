/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2PqPull
import InteractingSLE.Spec.Supplement.SB2MlCf
import InteractingSLE.Spec.Supplement.SB2MjCorr
import InteractingSLE.Spec.Supplement.SB2WdInd
import InteractingSLE.Spec.Supplement.SB2MoHull

/-!
# D66's (P): B's own pull-back `hpb` in SB2LIFT's post-head chart, almost surely

Packet PROVE-GW2-NOTHR (round 8, decision D67 (3)). The root line mean (CONDFIN's `Cr.ae_lineMean_pos_root`) reads
B's own stage pull-back `hpb` in SB2LIFT's post-head chart
`c' = (Mi.sb2StageChart … ℓ ω).loewner (Mi.sb2StopDrv … ℓ τE ω) (Mi.sb2StopTime … ℓ τE ω)`, with driver
`shiftDrive (Mi.sb2StopDrv … ℓ t ω) τE` and time `Mi.sb2StopTime … ℓ t ω − τE` (SB2LIFT's handoff §R33.1). The
landed line family (`Ml.exists_sb2LineFamily_cf`) gives it in B's stage chart; here it is carried through the head:

* **`ae_isStagePullback_postHead`**: almost surely, wherever the stage pull-back holds at `t` (any event `G`), on the
  capped launch event at `t`, at every head time `τE ≤ t` at which the S2 record `Om.IsStageS2 c' Φ A₁ …` holds for a
  chart `Φ` covering `ℍ ∖ A₁`, there is `g'` with
  `Ln.IsStagePullback c' g' A₁ A₂ {w | c'.2.1 w ∈ A₁} K'`, `K' = fwdHull (shiftDrive (sb2StopDrv … t) τE)
  (sb2StopTime … t − τE)`;
* **`subset_image_hullChart`**: the canonical hull chart `Mo.hullChart (fill K) x₀` covers `ℍ ∖ fill K` (the `Φ` and
  `A₁ = fill K` of the root, where SB2LIFT's `Sx.ae_isStageS2_root` gives the S2 record).

The walk inputs (regular launches, injective traces, GW1's tip coordinates) hold almost surely in SB2(2)'s
counterflow setting (`GW1W.regLaunches_of_stagedPiecesRegular`, `LuM.ae_injOn_trOf_walk`,
`Ml.ae_walkTipCoordinates_amb` with `GW1Conn.ambient_bounds`). R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Pq

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide Sx

/-- **The canonical hull chart covers the complement of the hull.** -/
theorem subset_image_hullChart {A : Set ℂ} (hA : IsHPHull A) (x₀ : ℝ) :
    H \ A ⊆ (Mo.hullChart A x₀).2.1 '' H := by
  rw [← Mo.coe_dom_hullChart hA x₀, (Mo.isConformal_hullChart hA x₀).coe_dom]

/-- The stop time of the stopped piece before its lifetime is the own time. -/
theorem sb2StopTime_eq {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ}
    {right : Bool} {ℓ : ℕ} {τ : ℝ≥0}
    {ω : Ω} (hτ : (τ : ℝ≥0∞) < (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω).2) :
    Mi.sb2StopTime E b jumps θ right ℓ τ ω = (τ : ℝ) := by
  unfold Mi.sb2StopTime
  rw [min_eq_left hτ.le, ENNReal.toNNReal_coe]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **D66's (P): B's own stage pull-back in the post-head chart, almost surely.** -/
theorem ae_isStagePullback_postHead (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (ℓ : ℕ) (t : ℝ≥0) {A₁ A₂ : Ω → Set ℂ} {G : Set Ω}
    (hpull : ∀ᵐ ω ∂P, ω ∈ G → ∃ g : ℂ → ℂ,
      Ln.IsStagePullback (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω) g (A₁ ω) (A₂ ω)
        {w | (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 w ∈ A₁ ω}
        (fwdHull (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω)))
    (τE : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ G → ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t → τE ω ≤ t →
      (∃ (Φ : Chart) (wB : ℝ → ℝ) (sB : ℝ) (W : ℝ → ℝ) (u : ℝ),
        Om.IsStageS2 ((Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
          (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω)
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω)) Φ (A₁ ω) wB sB W u ∧
        H \ A₁ ω ⊆ Φ.2.1 '' H) →
      ∃ g' : ℂ → ℂ, Ln.IsStagePullback
        ((Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
          (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω)
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω)) g' (A₁ ω) (A₂ ω)
        {w | ((Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
          (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω)
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω)).2.1 w ∈ A₁ ω}
        (fwdHull (shiftDrive (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω) (τE ω))
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω - τE ω)) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hEw := hE' w hw
  have hRw := stagedPiecesRegular_of_regular h13 hκ hb hEw (hreg' w)
  have hamb := (GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hb hh hcf hζ').1
  filter_upwards [hpull, GW1W.regLaunches_of_stagedPiecesRegular hRw,
    ae_all_iff.2 fun j => LuM.ae_injOn_trOf_walk hκ hκ4 hb hEw (hreg' w) hRw j,
    Ml.ae_walkTipCoordinates_amb hκ hb hh hamb hEw (hreg' w) hRw] with ω hp hr hinj htip hG hcap hτt hS2
  obtain ⟨g, hpb⟩ := hp hG
  obtain ⟨Φ, wB, sB, W, u, hS, hΦ⟩ := hS2
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => StagedReg.regFam E w j ω with hDdef
  obtain ⟨⟨c₀, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hcap.1
  have hτ : ((τE ω : ℝ≥0) : ℝ≥0∞) < (D ℓ).2 := (ENNReal.coe_le_coe.2 hτt).trans_lt hcap.2
  obtain ⟨X, g', C, hD, hgc, hgi, hgb, hgf⟩ := postHead_chart_facts hr hinj htip hl' hτ
  -- the stopped drivers
  obtain ⟨hWc, hW0⟩ := Mj.continuous_stopDrv (hreg' w ℓ ω) hcap.2
  obtain ⟨hWτc, -⟩ := Mj.continuous_stopDrv (hreg' w ℓ ω) hτ
  have hsτ : Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω = (τE ω : ℝ) := sb2StopTime_eq hτ
  have hst : Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω = (t : ℝ) := sb2StopTime_eq hcap.2
  have hτs : Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω ≤
      Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω := by
    rw [hsτ, hst]; exact_mod_cast hτt
  have hagree : ∀ r ∈ Icc (0 : ℝ) (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω),
      Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω r =
        Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω r := by
    intro r hr
    rw [hsτ] at hr
    have hrτ : r.toNNReal ≤ τE ω := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    have h1 : min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min ((τE ω : ℝ≥0) : ℝ≥0∞) (D ℓ).2) = (r.toNNReal : ℝ≥0∞) :=
      min_eq_left (le_min (ENNReal.coe_le_coe.2 hrτ) ((ENNReal.coe_le_coe.2 hrτ).trans hτ.le))
    have h2 : min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min ((t : ℝ≥0) : ℝ≥0∞) (D ℓ).2) = (r.toNNReal : ℝ≥0∞) :=
      min_eq_left (le_min (ENNReal.coe_le_coe.2 (hrτ.trans hτt)) ((ENNReal.coe_le_coe.2 hrτ).trans hτ.le))
    show (D ℓ).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min ((τE ω : ℝ≥0) : ℝ≥0∞) (D ℓ).2)).toNNReal =
      (D ℓ).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min ((t : ℝ≥0) : ℝ≥0∞) (D ℓ).2)).toNNReal
    rw [h1, h2]
  have hτ0 : (0 : ℝ) ≤ Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω := NNReal.coe_nonneg _
  have hdom₁ := dom_compl_subset_of_stageS2 hS hD.1 hΦ
  have hres := isStagePullback_loewner hpb hWc hW0 hWτc hτ0 hτs hagree hD hgc hgi hgb hgf hdom₁
  rw [hsτ] at hres ⊢
  exact ⟨g', hres⟩

end InteractingSLE.Theorem14.SB.Pq
