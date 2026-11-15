/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfNoThr
import InteractingSLE.Spec.Supplement.SB2KdInputs
import InteractingSLE.Spec.Supplement.SB2KcPartition
import InteractingSLE.Spec.Supplement.SB2DrvCells
import InteractingSLE.Spec.Supplement.SBS3MarkedRecenter

/-!
# E7, first direction, almost surely: SB2DRV's `V_le_thr`

Packet PROVE-T14-SB2WORD (round 3, decision D18). In SB2(1)'s launch problem, almost surely at a launch and on every
force-type cell of K2's launch word, every relative driver whose read-back `g(Γ s + m)` stays off the closure of the
bad set before `V` has no continuation threshold before `V`.

* **`ae_word_eq_shift`**: K2's launch word `I.word` (the boundary data of the field read in the launch chart recentred
  at the entry) is the staged witness word shifted by the entry, off finite sets (chart transports through the
  recentred chart, `isChartTransport_recenter_word`, and GFF uniqueness);
* **`ae_le_thr_of_good`**: the almost-sure form of `Wf.le_thr_of_good` (with the second clause,
  `Lv.sb2StageActiveWord2Statement`).

R48: Theorem 1.4 only; no Theorem 1.2–1.3 here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.Staged Exist.StagedLaw Restart GW1W Lv Supp8.Q3Stop Restart.DomainMarkov.K2

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **K2's launch word is the staged witness word shifted by the entry** (off finite sets, almost surely at a
launch). -/
theorem ae_word_eq_shift (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) β Y) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      ∀ y ∉ (I.word ω₀).jumps ∪ (BoundaryWord.shiftW (launchEntry κ b jumps E (k + 1) u ω₀) (β ω₀)).jumps,
        (I.word ω₀).fn y = (β ω₀).fn (y + launchEntry κ b jumps E (k + 1) u ω₀) := by
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS := HP.staged w hw
  have h𝒢 := hS.2.1 (k + 1)
  have hrun := ae_ae_run_eq (κ := κ) runMeasStatement HP.boundary w (k := k + 1) (fun j _ => hS.1 j)
    (fun j _ => HP.drivers_regular w j) (P := P)
  have hTk := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1
  filter_upwards [hW.2.2.1, hW.2.2.2, hrun, hTk, I.field, I.chart_eq] with ω₀ hT₀ hG₀ hr₀ hTk₀ hfield hceq hF
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  have hc₀ : Lv.launchChart κ b jumps E (k + 1) ω₀ =
      stChart (ExplState.run κ b jumps w (fun j => E w j ω₀) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  obtain ⟨hpc, h', hT', hG'⟩ := hfield hF
  obtain ⟨hconf, hlift, -⟩ := hT₀ hF
  set m := launchEntry κ b jumps E (k + 1) u ω₀ with hmdef
  have hceq' := hceq hF
  rw [hc₀] at hceq'
  have hae : h' =ᵐ[condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀]
      (fun ω => flowField m 0 (Y ω)) := by
    filter_upwards [hr₀, hTk₀] with ω hω hTω
    have hl : (ExplState.run κ b jumps w (fun j => E w j ω) (k + 1 + 1)).2.2.2.1 (k + 1) ≠ none := by
      rw [launches_run_succ_of_run_eq (κ := κ) (b := b) (jumps := jumps) w hω]
      exact hF
    obtain ⟨-, -, hTY⟩ := hTω hl
    rw [hω] at hTY
    have hrec := SB.S3.isChartTransport_recenter_word hconf hlift hTY m
    have hT'' := hT' ω
    rw [hceq'] at hT''
    exact hT''.unique (hconf.recenter m) hrec
  have hG'' : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) h'
      (BoundaryWord.shiftW m (β ω₀)).fn (BoundaryWord.shiftW m (β ω₀)).jumps :=
    isGFFWithBoundaryData_congr_ae (Exist.StagedLaw.isGFFWithBoundaryData_shiftW m (hG₀ hF)) hG'.1 hae.symm
  intro y hy
  rw [eq_of_isGFFWithBoundaryData hpc (BoundaryWord.shiftW m (β ω₀)).isPiecewiseConstantBoundaryData hG' hG'' y hy,
    BoundaryWord.fn_shiftW]

/-- **E7, first direction, almost surely** (SB2DRV's `V_le_thr` for read-back stops): almost surely at a launch, on
every force-type cell of the launch word, every continuous relative driver from `0` with a generating trace up to `V`
whose read-back through any continuous boundary extension `g` of the launch chart's inverse stays off the closure of
the bad set before `V` has its continuation threshold at or after `V`. -/
theorem ae_le_thr_of_good (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (F : Set Ω) (w : WordType) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → ω ∈ wordTypeCell κ ψ I.word F w →
      ∀ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} → EqOn g (Lv.launchChart κ b jumps E (k + 1) ω).2.1 H →
      ∀ (W : ℝ≥0 → Ω → ℝ) (V : ℝ≥0∞) (Γ : ℝ≥0 → ℂ), Continuous (fun t => W t ω) → W 0 ω = 0 →
        IsGeneratingTrace (fun t => W t ω) V Γ →
        (∀ s : ℝ≥0, (s : ℝ≥0∞) < V → ∀ x : ℝ, g (Γ s + (launchEntry κ b jumps E (k + 1) u ω : ℂ)) = x →
          x ∉ closure (badSet κ ψ u b)) →
        V ≤ FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω := by
  set ws : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwsdef
  obtain ⟨β, Y, hW, hβ⟩ := sb2StageActiveWord2Statement κ HP.kappa_pos HP.kappa_lt_four b jumps HP.boundary P h
    HP.field HP.admissible E HP.staged HP.pieces_regular HP.drivers_regular k
  filter_upwards [hβ u HP.seed_nonpos, ae_word_eq_shift HP I hW, hW.2.2.1] with ω hβω heqω hTω hF hcell g hgc hgi
    W V Γ hWc hW0 hΓ hgood
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  have hc₀ : Lv.launchChart κ b jumps E (k + 1) ω =
      stChart (ExplState.run κ b jumps ws (fun j => E ws j ω) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  have hcc : (Lv.launchChart κ b jumps E (k + 1) ω).IsConformal := by rw [hc₀]; exact (hTω hF).1
  have hft : FCDet.IsFlowType κ ψ (I.word ω) (cellXL κ ψ I.word w ω) (cellXR κ ψ I.word w ω) (typedRhoL w)
      (typedRhoR w) :=
    FCDet.isFlowType_of_mem_typeSet (mem_typeSet_of_mem_wordTypeCell hcell)
  exact le_thr_of_good HP.kappa_pos HP.kappa_lt_four HP.angle HP.boundary hcc hgc hgi (hβω hF).2 (heqω hF) hft hWc
    hW0 hΓ hgood

end InteractingSLE.Theorem14.SB.Wf
