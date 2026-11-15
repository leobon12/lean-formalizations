/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvAssemble
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DxKAmb
import InteractingSLE.Spec.Supplement.SBS3DxKSplit
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Successor of `SB2DrvAssemble` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB2DrvAssemble` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `SB2RemainderCodeLeStatement`;
* `sb2DriverLinkAmbStatement_of_remainderCodeLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Exist.Staged Exist.StagedLaw Restart WalkInf Sec2.Assembly

/-! ### Two generic steps -/

/-! ### The per-sample identification and the assembly -/

/-- **Named input: SB2(1)'s per-sample identification of the actual remainder** (supplement
pp. 631–633: "That portion is the canonical upper flow of the conditional field in `D_A` [...] with its
original stop reconstructed"; "Integrated uniqueness and the field-determining graphs identify the
actual relative ordinary flows"). For every SB2(1) launch problem and every compatible launch chart
record, almost surely on the launch event and on the entrance event `{T_L < ζ}` (`T_L` the first visit of
the upper flow to `L = min(A ∩ ℝ)`), the actual remainder of the upper flow, read through the launch
chart, is linked (`IsRemainderLink`) to a generating trace of some driver, continuous before its
lifetime, matching the canonical code of the launch word and of the field read in the recentred
version chart. No measurability of that driver and no conditional law is asked. -/
def SB2RemainderCodeLeStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ),
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      ∃ (W : ℝ≥0 → ℝ) (V : ℝ≥0∞) (γ : ℝ≥0 → ℂ),
        ContinuousOn W {t | (t : ℝ≥0∞) < V} ∧
        IsDriverCodeMatch (driverCode h12p H.kappa_pos ψ
          (I.word ω, Chart.chartTransport (I.chart_measurable.1 ω) 1 0 (chiC κ) (h ω))) W V ∧
        IsGeneratingTrace W V γ ∧
        IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => γ t + launchEntry κ b jumps E (k + 1) u ω) V

/-- **SB2(1)'s clauses (1) and (3) at the launches after the first** (`SB2DriverLinkAmbLeStatement`)
from Theorems 1.2–1.3 and the per-sample identification `SB2RemainderCodeLeStatement`. The driver is the
landed canonical conditional driver of the launch chart; its code match comes from Theorem 1.2 under
the conditional laws; on the entrance event the identified driver is this one
(`eq_of_driverCodeMatch`), so its generating trace and link transfer; off it the link is vacuous. -/
theorem sb2DriverLinkAmbStatement_of_remainderCodeLe
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hrem : SB2RemainderCodeLeStatement h12p) : SB2DriverLinkAmbLeStatement.{u} := by
  classical
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg
    k u ψ hu hψ _ hL hH η ζ hη hS1
  let H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ :=
    ⟨hκ, hκ4, hb, hh, hadm, hE, hER, hreg, hu, hψ, hL, hH, hη, hS1⟩
  let w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS : IsStagedHistory κ b jumps P h w (E w) := hE w hprog
  have hR : StagedPiecesRegular κ b jumps P w (E w) := hER w hprog
  have hamb : ∀ t, t < 0 → t ∉ jumps →
      b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => Ly.height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  obtain ⟨m, cw, T, hm, hcw, hmc, heq, hG, hcc, hT, hcover⟩ :=
    exists_k2Launch_countable_types hκ hb hh (w := w) rfl hS hR
      (hreg w) hamb k ψ hu
  let I : K2LaunchInputs κ b jumps P h E k u ψ :=
    ⟨m, cw, T, hm, hcw, hmc, heq, hG, hcc, hT, hcover⟩
  have h𝒢 := hS.2.1 (k + 1)
  have hF : MeasurableSet[pastSigma κ b jumps w (E w) (k + 1)]
      (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma hb hS.1 (hreg w) (k + 1)
  have hr := measurable_pastMap (κ := κ) runMeasStatement hb w
    (fun j _ => hS.1 j) (fun j _ => hreg w j) (k + 1) le_rfl
  obtain ⟨D, hDm, hDr, hD⟩ := exists_condFlowLineDriverOn_of_chartField
    h12p h13 hκ ψ hr hh.1 hcw hmc hcc hG
  have hWm : ∀ t, Measurable (fun ω => (D ω).1 t) :=
    fun t => (measurable_pi_apply t).comp hDm.fst
  have hVm : Measurable (fun ω => (D ω).2) := hDm.snd
  have hcode := ae_codeMatch_of_isCondFlowLineDriverOn h12p h13 hκ ψ h𝒢 hF hh.1 hcw hmc
    (hcc.mono fun _ h _ => h) hWm hVm hD
  have hQ := hrem κ b jumps P h E k u ψ η ζ H I
  let γ : Ω → ℝ≥0 → ℂ := fun ω =>
    if hx : ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (D ω).1 (D ω).2 γ' ∧
        IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => γ' t + launchEntry κ b jumps E (k + 1) u ω) (D ω).2
    then hx.choose else 0
  have hgeom : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      IsGeneratingTrace (fun t => (D ω).1 t) (D ω).2 (γ ω) ∧
      IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
        (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
        (fun t => γ ω t + launchEntry κ b jumps E (k + 1) u ω) (D ω).2 := by
    filter_upwards [hQ, hcode] with ω hQω hcω hFω hvis
    obtain ⟨W', V', γ', hW'c, hW'code, hgen, hlink⟩ := hQω hFω hvis
    obtain ⟨hVV, hWW⟩ := eq_of_driverCodeMatch hW'c (hDr ω).1 hW'code (hcω hFω)
    have hx : ∃ γ'' : ℝ≥0 → ℂ, IsGeneratingTrace (D ω).1 (D ω).2 γ'' ∧
        IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => γ'' t + launchEntry κ b jumps E (k + 1) u ω) (D ω).2 := by
      refine ⟨γ', ?_, ?_⟩
      · rw [← hVV]
        exact StoppedK2.isGeneratingTrace_congr hWW hgen
      · rw [← hVV]
        exact hlink
    have hγ : γ ω = hx.choose := dite_eq_left_of_eq_true (eq_true hx)
    rw [hγ]
    exact hx.choose_spec
  have hDa := hD.congr_chart
    (heq.mono fun ω he hFω => ⟨(he hFω).symm, rfl, rfl⟩)
  have hfreeze : ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀),
        launchChart κ b jumps E (k + 1) ω = launchChart κ b jumps E (k + 1) ω₀ ∧
        launchEntry κ b jumps E (k + 1) u ω = launchEntry κ b jumps E (k + 1) u ω₀ := by
    filter_upwards [CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ)
      (b := b) (jumps := jumps) w (fun j _ => hreg w j) h𝒢 le_rfl]
      with ω₀ hrun _
    filter_upwards [hrun] with ω hrunω
    refine ⟨?_, (launchEntry_eq_of_run_eq (u := u) hrunω).2⟩
    unfold launchChart
    rw [launches_run_succ_of_run_eq w hrunω]
  exact ⟨fun ω => (cw ω).fn, fun ω => (cw ω).jumps,
    fun t ω => (D ω).1 t, fun ω => (D ω).2, hDa,
    ae_remainderLink_of_condDriver_trace_visit h13 hκ h𝒢 hF hDa hfreeze hDr hgeom⟩

end InteractingSLE.Theorem14.SB.Lv
