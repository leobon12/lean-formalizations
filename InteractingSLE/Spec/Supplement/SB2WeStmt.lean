/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WeFinal

/-!
# SB2(1)'s active word with its second clause, PROVED

Packet PROVE-T14-SB2WORD (round 2, ruling R120, D10 step 3). Statements (no named input):

* **`SB2StageActiveWord2Statement`** / **`sb2StageActiveWord2Statement`**: the staged witness word of the lower walk,
  almost surely at every launch `k + 1`, has round 1's active word on `(m, 0)` and the second clause `SecondClause`
  (original-real points keep their heights through the strictly increasing, continuous, reflecting chart; all other
  points are old lower sides of height `−λ + (π/2)χ` right of `m`; the two sides of `m` are the two sides of `u`);
* `ae_eq_off_of_stageWitness`: every witness of the launch clause has the staged word's data off finite sets;
* **`SB2ActiveWord2AmbStatement`** / **`sb2ActiveWord2AmbStatement`**: both clauses for every witness of the launch
  clause (the form of `SB2ActiveWordAmbStatement`, with the second clause added).
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

open Sec4 Exist Exist.Staged Exist.StagedLaw Restart GW1W

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **SB2(1)'s stage active word with its second clause**: some staged witness `(β, Y)` of the lower walk at
instruction `k + 1` whose word, almost surely at the launches, has the active word and the second clause. -/
def SB2StageActiveWord2Statement : Prop :=
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
    ∀ k : ℕ, ∃ (β : Ω → Restart.BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) β Y ∧
      ∀ u : ℝ, u ≤ 0 → ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
        IsActiveLowWord κ b jumps u (β ω₀).fn (β ω₀).jumps (launchEntry κ b jumps E (k + 1) u ω₀) ∧
        SecondClause κ b jumps (launchChart κ b jumps E (k + 1) ω₀) u (launchEntry κ b jumps E (k + 1) u ω₀)
          (β ω₀).fn (β ω₀).jumps

/-- **SB2(1)'s stage active word with its second clause** (`SB2StageActiveWord2Statement`, no named input). -/
theorem sb2StageActiveWord2Statement : SB2StageActiveWord2Statement.{u} := by
  intro κ hκ _ b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg k
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => Ly.height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  obtain ⟨β, Y, hW, hae⟩ := GW1W.exists_witness_right_lwo hκ hb hh (hE w hw) (hreg w) (hER w hw) hamb (k + 1)
  refine ⟨β, Y, hW, fun u hu => ?_⟩
  have harc := ae_arcs_subset_Ici hκ hb hh (hE w hw) (hreg w) hamb
  have hRL := GW1W.regLaunches_of_stagedPiecesRegular (hER w hw)
  filter_upwards [hae, harc, hRL] with ω hω ha hr hF
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  obtain ⟨hI, -, -, hLWO⟩ := hω hF
  have hAc := Lx.isCompact_lowerPrefix (u := u) hr hF
  have hnot := Lx.stStatus_ne_done_of_launches _ _ hcθ
  have hspec : w.1 = 0 := by simp [hwdef, boundaryWalkSpec]
  unfold launchEntry
  rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  exact ⟨isActiveWord_of_lw hspec hr hnot hI.2.1.1 hLWO.1 (ha (k + 1)) hu hAc,
    secondClause_of_lwo rfl hspec hr hnot hI.2.1.1 hLWO (ha (k + 1)) hu hAc⟩

/-- **Every witness of the launch clause has the staged word's data off finite sets** (both are boundary data of the
chart transport of `h` under the regular conditional law; `activeWord_of_stageWitness`'s argument). -/
theorem ae_eq_off_of_stageWitness {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : ExplSpec}
    (hw : w = boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (hEm : ∀ j, Measurable (E w j))
    (hreg : ∀ j ω, IsRegularDriver (E w j ω)) {k : ℕ} (h𝒢 : pastSigma κ b jumps w (E w) (k + 1) ≤ mΩ)
    {β : Ω → Restart.BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h w (E w) (k + 1) β Y) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
        IsPiecewiseConstantBoundaryData b' jumps' →
        (∀ ω, IsChartTransport (launchChart κ b jumps E (k + 1) ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) h' b' jumps' →
        ∀ y ∉ jumps' ∪ (β ω₀).jumps, b' y = (β ω₀).fn y := by
  subst hw
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hrun := ae_ae_run_eq (κ := κ) runMeasStatement hb w (k := k + 1) (fun j _ => hEm j) (fun j _ => hreg j)
    (P := P)
  have hTk := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1
  filter_upwards [hW.2.2.1, hW.2.2.2, hrun, hTk] with ω₀ hT₀ hG₀ hr₀ hTk₀ hF b' J' h' hb' hT' hG'
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  have hc₀ : launchChart κ b jumps E (k + 1) ω₀ =
      stChart (ExplState.run κ b jumps w (fun j => E w j ω₀) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  obtain ⟨hconf, -, -⟩ := hT₀ hF
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
  exact eq_of_isGFFWithBoundaryData hb' (β ω₀).isPiecewiseConstantBoundaryData hG' hG''

/-- **SB2(1)'s active word with its second clause for every witness of the launch clause.** -/
def SB2ActiveWord2AmbStatement : Prop :=
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
      ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E (k + 1) ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E (k + 1) u ω₀) ∧
          SecondClause κ b jumps (launchChart κ b jumps E (k + 1) ω₀) u (launchEntry κ b jumps E (k + 1) u ω₀)
            b' jumps'

/-- **SB2(1)'s active word with its second clause for every witness** (`SB2ActiveWord2AmbStatement`, no named
input). -/
theorem sb2ActiveWord2AmbStatement : SB2ActiveWord2AmbStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg k u hu
  obtain ⟨β, Y, hW, hβ⟩ := sb2StageActiveWord2Statement κ hκ hκ4 b jumps hb P h hh hadm E hE hER hreg k
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have heq := ae_eq_off_of_stageWitness hb rfl (hE _ hw).1 (hreg _) ((hE _ hw).2.1 (k + 1)) hW
  filter_upwards [hβ u hu, heq] with ω₀ h1 h2 hF b' J' h' hb' hT' hG'
  have he := h2 hF b' J' h' hb' hT' hG'
  exact ⟨isActiveLowWord_of_eq_off hb' he (h1 hF).1, (h1 hF).2.of_eq_off fun y hy => he y hy⟩

end InteractingSLE.Theorem14.SB.Lv
