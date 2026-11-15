/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KSplit

/-!
# SB2(1)'s active word: from every witness to the staged witness word

Packet PROVE-T14-SB2FIN5, step (a) of the plan for `SB2ActiveWordAmbStatement`. The clause asks the active word for
EVERY witness `(b', jumps', h')` of the launch clause. Every such witness agrees with the staged conditional law's own
witness `(β, Y)` (`Exist.StagedLaw.IsStageWitness`; for the lower walk GW1's `GW1W.exists_witness_right`): under the
regular conditional law the run chart is constant, both `h'` and `Y` are chart transports of `h` through it, so
`h' = Y` kernel-almost surely and the data agree off finite sets.

* `isActiveLowWord_of_eq_off`: the active word passes to piecewise-constant data that agree off finite sets;
* **`activeWord_of_stageWitness`**: clause (2) at a launch `k + 1` from the active word of a staged witness word;
* `SB2StageActiveWordStatement` (named input: the staged witness at every launch `k + 1` has the active word) and
  **`sb2ActiveWordAmbStatement_of_stage`**.

No named input beyond `SB2StageActiveWordStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The active word passes to data agreeing off finite sets** (local constancy off the jumps). -/
theorem isActiveLowWord_of_eq_off {u m : ℝ} {b' β : ℝ → ℝ} {J' Jβ : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') (heq : ∀ y ∉ J' ∪ Jβ, b' y = β y)
    (hβ : IsActiveLowWord κ b jumps u β Jβ m) : IsActiveLowWord κ b jumps u b' J' m := by
  intro y hy hyJ
  have hfin : (((J' ∪ Jβ : Finset ℝ) : Set ℝ) \ {y})ᶜ ∈ 𝓝 y :=
    ((J' ∪ Jβ).finite_toSet.sdiff).isClosed.compl_mem_nhds (by simp)
  have hev : ∀ᶠ z in 𝓝[≠] y, (b' z = b' y ∧ z ∈ Ioo m 0) ∧
      (z ∈ (((J' ∪ Jβ : Finset ℝ) : Set ℝ) \ {y})ᶜ ∧ z ∈ ({y}ᶜ : Set ℝ)) :=
    Filter.Eventually.and (((hb' y hyJ).and (Ioo_mem_nhds hy.1 hy.2)).filter_mono nhdsWithin_le_nhds)
      (Filter.Eventually.and (mem_nhdsWithin_of_mem_nhds hfin) self_mem_nhdsWithin)
  obtain ⟨z, ⟨hbz, hz⟩, hzS, hzy⟩ := hev.exists
  have hzS' : z ∉ J' ∪ Jβ := fun hm => hzS ⟨by exact_mod_cast hm, hzy⟩
  have hzβ : z ∉ Jβ := fun hm => hzS' (Finset.mem_union_right _ hm)
  rw [← hbz, heq z hzS']
  exact hβ z hz hzβ

/-- **Clause (2) of SB2(1) at a launch `k + 1` from the staged witness word**: if `(β, Y)` is a staged witness of the
lower walk at instruction `k + 1` and almost surely at the launch its word has SB2(1)'s active word on
`(launchEntry, 0)`, then so does every witness of the launch clause. -/
theorem activeWord_of_stageWitness {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : ExplSpec}
    (hw : w = boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (hEm : ∀ j, Measurable (E w j))
    (hreg : ∀ j ω, IsRegularDriver (E w j ω)) {k : ℕ} (h𝒢 : pastSigma κ b jumps w (E w) (k + 1) ≤ mΩ) {u : ℝ}
    {β : Ω → Restart.BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h w (E w) (k + 1) β Y)
    (hβ : ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      IsActiveLowWord κ b jumps u (β ω₀).fn (β ω₀).jumps (launchEntry κ b jumps E (k + 1) u ω₀)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
        IsPiecewiseConstantBoundaryData b' jumps' →
        (∀ ω, IsChartTransport (launchChart κ b jumps E (k + 1) ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) h' b' jumps' →
        IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E (k + 1) u ω₀) := by
  subst hw
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hrun := ae_ae_run_eq (κ := κ) runMeasStatement hb w (k := k + 1) (fun j _ => hEm j) (fun j _ => hreg j)
    (P := P)
  have hTk := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1
  filter_upwards [hW.2.2.1, hW.2.2.2, hβ, hrun, hTk] with ω₀ hT₀ hG₀ hβ₀ hr₀ hTk₀ hF b' J' h' hb' hT' hG'
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  have hc₀ : launchChart κ b jumps E (k + 1) ω₀ =
      stChart (ExplState.run κ b jumps w (fun j => E w j ω₀) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  obtain ⟨hconf, -, -⟩ := hT₀ hF
  -- under the regular conditional law `h' = Y`
  have hae : h' =ᵐ[condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀] Y := by
    filter_upwards [hr₀, hTk₀] with ω hω hTω
    have hl : (ExplState.run κ b jumps w (fun j => E w j ω) (k + 1 + 1)).2.2.2.1 (k + 1) ≠ none := by
      rw [launches_run_succ_of_run_eq (κ := κ) (b := b) (jumps := jumps) w hω]
      exact hF
    obtain ⟨-, -, hTY⟩ := hTω hl
    rw [hω] at hTY
    have hT'' := hT' ω
    rw [hc₀] at hT''
    exact hT''.unique hconf hTY
  have hG'' : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) h'
      (β ω₀).fn (β ω₀).jumps :=
    isGFFWithBoundaryData_congr_ae (hG₀ hF) hG'.1 hae.symm
  exact isActiveLowWord_of_eq_off hb'
    (eq_of_isGFFWithBoundaryData hb' (β ω₀).isPiecewiseConstantBoundaryData hG' hG'') (hβ₀ hF)

/-- **Named input: the staged conditional word of the lower walk has SB2(1)'s active word** at every launch `k + 1`
(some staged witness `(β, Y)` of the lower walk at instruction `k + 1`, GW1's ambient setting). -/
def SB2StageActiveWordStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    Ly.LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (j : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec j ω)) →
    ∀ (k : ℕ) (u : ℝ), u ≤ 0 →
      ∃ (β : Ω → Restart.BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
        IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) β Y ∧
        ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
          IsActiveLowWord κ b jumps u (β ω₀).fn (β ω₀).jumps (launchEntry κ b jumps E (k + 1) u ω₀)

/-- **SB2(1)'s active word for every witness from the staged witness word** (`activeWord_of_stageWitness`). -/
theorem sb2ActiveWordAmbStatement_of_stage (hs : SB2StageActiveWordStatement.{u}) :
    SB2ActiveWordAmbStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg k u hu
  obtain ⟨β, Y, hW, hβ⟩ := hs κ hκ hκ4 b jumps hb P h hh hadm E hE hER hreg k u hu
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  exact activeWord_of_stageWitness hb rfl (hE _ hw).1 (hreg _) ((hE _ hw).2.1 (k + 1)) hW hβ

end InteractingSLE.Theorem14.SB.Lv
