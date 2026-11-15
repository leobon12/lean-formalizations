/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfPi
import InteractingSLE.Spec.Supplement.SB2WfE7
import InteractingSLE.Spec.Supplement.SB2WfJo
import InteractingSLE.Spec.Supplement.SB2WeStmt

/-!
# The junction fact and E7, PROVED

Packet PROVE-T14-SB2WORD (round 3, decision D18). **`sb2JunctionStatement`**: the junction fact
`SB2JunctionStatement`, with no named input. At a launch `k + 1` of the lower walk the staged witness of the
induction `exists_witness_right_lwoj` has round 2's invariants and the junction invariant `JW`, and `junction_of_jw`
reads the junction fact off them; an arbitrary witness has the same word off finite sets
(`ae_eq_off_of_two_witnesses`), which moves the lower-side hypothesis over (`lowSide_of_eq_off`).

**`sb2RemainderLifeStatement`**: E7 (`Vh.SB2RemainderLifeStatement`), with no named input
(`sb2RemainderLifeStatement_of_junction`).
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

open Exist Exist.Staged Exist.StagedLaw Restart GW1W Lv
open PiecewiseConstantBoundaryData (rightLim)

/-- **Two stage witnesses have the same word off finite sets**, almost surely at a launch (both words are the
boundary data of the chart transport of `h` under the regular conditional law). -/
theorem ae_eq_off_of_two_witnesses {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ) {β β' : Ω → BoundaryWord} {Y Y' : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) (hW' : IsStageWitness κ b jumps P h spec E k β' Y') :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      ∀ y ∉ (β' ω₀).jumps ∪ (β ω₀).jumps, (β' ω₀).fn y = (β ω₀).fn y := by
  have hrun := ae_ae_run_eq (κ := κ) runMeasStatement hb spec (k := k) (fun j _ => hEm j) (fun j _ => hreg j)
    (P := P)
  have hTk := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1
  have hTk' := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW'.2.2.1
  filter_upwards [hW.2.2.1, hW.2.2.2, hW'.2.2.2, hrun, hTk, hTk'] with ω₀ hT₀ hG₀ hG₀' hr₀ hTk₀ hTk₀' hF
  obtain ⟨hconf, -, -⟩ := hT₀ hF
  have hae : Y' =ᵐ[condExpKernel P (pastSigma κ b jumps spec E k) ω₀] Y := by
    filter_upwards [hr₀, hTk₀, hTk₀'] with ω hω hTω hTω'
    have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq (κ := κ) (b := b) (jumps := jumps) spec hω]
      exact hF
    obtain ⟨-, -, hTY⟩ := hTω hl
    obtain ⟨-, -, hTY'⟩ := hTω' hl
    rw [hω] at hTY hTY'
    exact hTY'.unique hconf hTY
  have hG'' := isGFFWithBoundaryData_congr_ae (hG₀' hF) hW.2.1 hae
  exact eq_of_isGFFWithBoundaryData (β' ω₀).isPiecewiseConstantBoundaryData (β ω₀).isPiecewiseConstantBoundaryData
    hG'' (hG₀ hF)

/-- **The lower-side hypothesis ignores finite sets.** -/
theorem lowSide_of_eq_off {c c' : BoundaryWord} {v r : ℝ} (hcc : ∀ y ∉ c'.jumps ∪ c.jumps, c'.fn y = c.fn y)
    (h : ∃ ε > 0, ∀ y ∈ Ioo r (r + ε), y ∉ c.jumps → c.fn y = v) :
    ∃ ε > 0, ∀ y ∈ Ioo r (r + ε), y ∉ c'.jumps → c'.fn y = v := by
  obtain ⟨ε, hε, hv⟩ := h
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem (c'.jumps ∪ c.jumps) r
  refine ⟨min ε δ, lt_min hε hδ, fun y hy _ => ?_⟩
  have hyJ : y ∉ c'.jumps ∪ c.jumps := fun hm =>
    (hδJ y hm).1 ⟨hy.1, by linarith [hy.2, min_le_right ε δ]⟩
  rw [hcc y hyJ]
  exact hv y ⟨hy.1, by linarith [hy.2, min_le_left ε δ]⟩
    fun hm => hyJ (Finset.mem_union_right _ hm)

/-- **The junction fact, PROVED** (`SB2JunctionStatement`, no named input). -/
theorem sb2JunctionStatement : SB2JunctionStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP β Y hW
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hκ := HP.kappa_pos
  have hκ4 := HP.kappa_lt_four
  have hb := HP.boundary
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => Ly.height_lt_of_cumWeightLeft hκ (HP.admissible t ht htJ)
  obtain ⟨β', Y', hW', hae⟩ := exists_witness_right_lwoj (u := u) hκ hκ4 HP.angle hb HP.field (HP.staged w hw)
    (HP.drivers_regular w) (HP.pieces_regular w hw) hamb (k + 1)
  have hRL := regLaunches_of_stagedPiecesRegular (HP.pieces_regular w hw)
  have h𝒢 := (HP.staged w hw).2.1 (k + 1)
  have hoff := ae_eq_off_of_two_witnesses hb (HP.staged w hw).1 (HP.drivers_regular w) h𝒢 hW hW'
  filter_upwards [hae, hRL, hoff] with ω hω hr hoffω hF g hgc hgi r hrm hlow p hp
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  obtain ⟨hI, -, -, hLWO, hJW⟩ := hω hF
  have hAc := Lx.isCompact_lowerPrefix (u := u) hr hF
  have hnot := Lx.stStatus_ne_done_of_launches _ _ hcθ
  have hc₀ : Lv.launchChart κ b jumps E (k + 1) ω =
      stChart (ExplState.run κ b jumps w (fun j => E w j ω) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  rw [hc₀] at hgi
  have hrm' : Lx.leftEntry (stChart (ExplState.run κ b jumps w (fun j => E w j ω) (k + 1)))
      (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < r := by
    unfold launchEntry at hrm
    rwa [hc₀] at hrm
  exact junction_of_jw hκ hκ4 HP.angle hr hnot hI.2.1.1 hLWO hJW HP.seed_nonpos hAc hgc hgi hrm'
    (lowSide_of_eq_off (hoffω hF) hlow) hp

/-- **E7, PROVED** (`Vh.SB2RemainderLifeStatement`, no named input). -/
theorem sb2RemainderLifeStatement : Vh.SB2RemainderLifeStatement.{u} :=
  sb2RemainderLifeStatement_of_junction sb2JunctionStatement

end InteractingSLE.Theorem14.SB.Wf
