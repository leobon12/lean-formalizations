/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1TermRestart
import InteractingSLE.Spec.Supplement.KernelTower2
import InteractingSLE.Spec.Supplement.GB6PastStep
import InteractingSLE.Spec.Supplement.CondDriverBridge
import InteractingSLE.Spec.Supplement.GW1WalkExitProfile

/-!
# BW1 at a walk launch: the identification under the regular conditional laws

Packet PROVE-BW1. Fix a launch `2n` of a walk at a sample `ω₀` and let `P₀` be the regular conditional law given the
retained past before `2n`. Under `P₀` the field read in the launch chart `c` is a GFF, the launch counterflow `V` is its
centred counterflow with infinite lifetime (`IsLaunchClock`), and the piece is its flow line (`IsStagedHistory`).
Proposition BW1 (`BW1.BW1Statement`, through `bw1_termRel`) in the world `P₀` gives, for each side, a driver `Wr` which
is, conditionally on the record of the piece, the centred counterflow of the field read in the post-piece chart, and
which is `P₀`-almost surely the relative counterflow of `V` after the piece (`IsTermRelOf`).

* the conditional law of `P₀` given the record of the piece is the conditional law of `P` given the retained past
  before `2n + 1` (`KernelTower.ae_condExpKernel_comap_eq`, `KernelTower.ae_ae_condExpKernel_condExpKernel_eq`);
* the post-piece chart is the launch chart composed with `termChart` (`stChart_run_succ_eq_trans`), so the field read
  by BW1 is the field read in the post-piece chart (`IsChartTransport.trans`);
* the canonical driver `Q` (the conditional half of `IsTerminalRestart`) and `Wr` are centred counterflows of that field
  under the same conditional law, hence equal (Theorem 1.2's determination,
  `GW4Ident.ae_eq_of_isCenteredCounterflowDriver`);
* **`ae_kernel_isTermRelOf`**: for almost every launch sample `ω₀`, for `P₀`-almost every `ω₁` at a next launch whose
  piece has positive lifetime, `Q` is almost surely under the conditional law given the retained past before `2n + 1`
  at `ω₁` the relative counterflow of `V` after the piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Term

open Exist Exist.StagedLaw Exist.Staged GW1RestartPair

/-! ### Deterministic facts on the walk runs -/

section Run

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A piece of a walk followed by another launch has a finite lifetime** (the first half of `GW1Laws.post_case`). -/
theorem ne_top_of_next {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1)).2.2.2.1 (2 * n) ≠ none)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * (n + 1) + 1)).2.2.2.1
      (2 * (n + 1)) ≠ none) :
    (D (2 * n)).2 ≠ ⊤ := by
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D with hRdef
  have hn : ∀ j, 2 * n < j → j < 2 * (n + 1) → (R (j + 1)).2.2.2.1 j = none := by
    intro j hj1 hj2
    have hj : j = 2 * n + 1 := by omega
    subst hj
    exact GW1RestartPair.noLaunch_walk_odd D n
  obtain ⟨-, hrunk, r, hstk⟩ := GW1W.run_eq_of_last_launch (by omega) hk hl hn
  have hrun1 : R (2 * n + 1) = ExplState.launch (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ := GW1W.launch_walk hl
  intro htop
  have hmin : min ⊤ (D (2 * n)).2 = ⊤ := by rw [htop]; rfl
  have hd := (launch_eq_of_top (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ hmin).2.2.2.2.1
  rw [← hrun1] at hd
  have := GW1W.contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (2 * n + 1)) right (Or.inr (Or.inl hd))
  rw [← hrunk] at this
  rw [this, hd] at hstk
  exact absurd hstk (by simp [GW1W.stArcM])

/-- The launch record of a walk launch: the state chart before the piece and the walk angle. -/
theorem launch_record_walk {k : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k = some (c, θ')) :
    c = stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) ∧ θ' = θ := by
  have hrun := GW1W.launch_walk (k := k) (by rw [hl]; exact Option.some_ne_none _)
  rw [hrun, launches_launch, Function.update_self] at hl
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hl)
  exact ⟨h1.symm, h2.symm⟩

/-- **The post-piece chart is the launch chart composed with the chart of the restarted piece.** -/
theorem stChart_run_succ_eq_trans {k : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none)
    (hfin : (D k).2 ≠ ⊤) :
    stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)) =
      (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)).trans (termChart (D k)) := by
  rw [GW1W.launch_walk hl, (launch_eq_of_ne_top _ k (D k) θ ⊤ (GW1W.min_top_ne_top hfin)).1,
    Chart.loewner_eq_trans, termChart, Chart.recenter_zero]

/-- The retained record of a walk launch is the record of the restarted piece. -/
theorem retained_run_walk {k : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.1 k = retOf ⊤ (D k) := by
  rw [GW1W.launch_walk hl, retained_launch, Function.update_self]
  rfl

/-- The retained record of the restarted piece. -/
theorem retained_run_termSpec (θ' : ℝ) (D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (termSpec θ') D' 1).2.2.1 0 = retOf ⊤ (D' 0) := by
  rw [run_termSpec_one, retained_launch, Function.update_self]
  rfl

end Run

/-! ### The identification under the regular conditional laws -/

section Kernel

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **BW1's identification under the regular conditional laws at a walk launch.** For almost every sample `ω₀` at
which the piece `2n` is launched, for almost every `ω₁` under the conditional law given the retained past before `2n`
at which the next launch `2(n+1)` happens and the piece has positive lifetime, the canonical post-piece counterflow `Q`
(the conditional half of `IsTerminalRestart`) is, almost surely under the conditional law given the retained past
before `2n + 1` at `ω₁`, the relative counterflow of the launch counterflow `V` after the piece. -/
theorem ae_kernel_isTermRelOf (hBW1 : BW1.BW1Statement.{u}) (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E right n V ζV ℓ) {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞}
    (hQ : GW1Laws.IsTerminalRestartCond κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n Q ζQ) :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω₀) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
      ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀),
        (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω₁) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁).2 ≠ 0 →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
            (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω₁),
          IsTermRelOf (fun t => Q t ω) (fun t => V t ω) (E (GW1Z.walkSpec b jumps right) (2 * n) ω) := by
  classical
  have hκ := hdata.pos
  have hκ4 := hdata.lt_four
  have hb := hdata.boundary
  have hh := hdata.field
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  have hE := hdata.staged _ hprog
  have hreg := hdata.regular (GW1Z.walkSpec b jumps right)
  have hRp := hdata.pieces _ hprog
  -- the stage witness at the launch: the launch chart is conformal
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀)
    hκ hκ4 hb hh hdata.counterflow hdata.complete
  obtain ⟨β₀, Y₀, hW₀⟩ : ∃ (β : Ω → Restart.BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n) β Y := by
    cases right
    · obtain ⟨β, Y, hW, -⟩ := GW1W.exists_witness_left hκ hb hh hE hreg hambR (2 * n)
      exact ⟨β, Y, hW⟩
    · obtain ⟨β, Y, hW, -⟩ := GW1W.exists_witness_right hκ hb hh hE hreg hambL (2 * n)
      exact ⟨β, Y, hW⟩
  -- the post-piece kernel: the field read in the post-piece chart is the GFF of the post-piece word
  obtain ⟨βk, Yk, hW, hgood⟩ := GW1Laws.exists_post_witness hT13₀ hκ hκ4 hb hh hdata.counterflow
    hdata.complete right hE hreg n
  have hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    filter_upwards [hdata.stages, hRp] with ω hs hp
    apply GW1LaunchClock.previous_launch_of_next hκ hb _ (fun j => hreg j ω) hs ?_ hdata.lt_card
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches _ _ hl).1 hl
  have hK := GW1Laws.ae_terminal_kernel hb hE hreg hW hgood hprev
  have hker : ∀ ω, condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * (n + 1))) ω =
      condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω :=
    condExpKernel_walk_connector (κ := κ) (b := b) (jumps := jumps)
      (θ := if right then -(Real.pi / 2) else Real.pi / 2) (right := right) P _ n
  -- the retained pasts
  have hpm : ∀ k, Measurable[pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k]
      (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k) := fun k s hs => by
    rw [pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  have hpmΩ : ∀ k, Measurable (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k) :=
    fun k => (hpm k).mono (hE.2.1 k) le_rfl
  have hcg : @MeasurableSpace.CountablyGenerated Ω
      (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) := by
    rw [pastSigma_eq_comap]
    exact MeasurableSpace.CountablyGenerated.comap _
  have hL0 := GW1W.measurableSet_pastSigma_launch (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg (2 * n)
  have hrun0 := CondDriverBridge.ae_ae_run_eq_of_le (κ := κ) (b := b) (jumps := jumps) (P := P)
    (GW1Z.walkSpec b jumps right) (k := 2 * n) (fun j _ => hreg j) (hE.2.1 (2 * n)) le_rfl
  have hrun1 := CondDriverBridge.ae_ae_run_eq_of_le (κ := κ) (b := b) (jumps := jumps) (P := P)
    (GW1Z.walkSpec b jumps right) (k := 2 * n + 1) (fun j _ => hreg j) (hE.2.1 (2 * n + 1)) le_rfl
  filter_upwards [hE.2.2.2 (2 * n), hW₀.2.2.1, hdata.current.2.1,
    KernelTower.ae_ae_condExpKernel_condExpKernel_eq (P := P)
      (pastSigma_mono (κ := κ) (b := b) (jumps := jumps) (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (Nat.le_succ (2 * n))) (hE.2.1 (2 * n + 1)) hcg,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (hE.2.1 (2 * n)) (hpm (2 * n)), hrun0,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) (hE.2.1 (2 * n)) hL0,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 (2 * n))
      (hdata.stages.and (hRp.and (hQ.2.and (hK.and hrun1))))]
    with ω₀ hst hconf hclock hkk hpmω hrunω hLω hPas hl0
  -- the launch at `ω₀`
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl0
  obtain ⟨hc_eq, hθ_eq⟩ := launch_record_walk hcθ
  obtain ⟨b', J', hc, hb', htrc, hfl⟩ := hst c θ hcθ
  have hgff := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  obtain ⟨hcfV, hζV⟩ := hclock c θ hcθ hc htrc
  obtain ⟨hcconf, hclift, -⟩ := hconf hl0
  have hcconf' : c.IsConformal := by rw [hc_eq]; exact hcconf
  have hclift' : ContinuousOn (fun w => c.2.2 (c.2.1 w)) QuantumZipper.H := by rw [hc_eq]; exact hclift
  have hθI : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by rw [hθ_eq]; exact GW1Z.walkAngle_mem_Icc right
  have hBW := fun r : Bool => bw1_termRel hBW1 hκ hκ4 hb' hgff hcfV hζV hθI (hE.1 (2 * n)) (hreg (2 * n)) hfl r
  choose Wr ζr hcr hpr using hBW
  -- the record of the restarted piece and the retained past before `2n + 1` agree under `P₀`
  have hK2 : ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀),
      condExpKernel (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀)
          (pastSigma κ b' J' (termSpec θ) (fun _ => E (GW1Z.walkSpec b jumps right) (2 * n)) 1) ω₁ =
        condExpKernel (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀)
          (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω₁ := by
    rw [pastSigma_eq_comap, pastSigma_eq_comap]
    refine KernelTower.ae_condExpKernel_comap_eq
      (measurable_pastMap (κ := κ) runMeasStatement hb' (termSpec θ)
        (E := fun _ => E (GW1Z.walkSpec b jumps right) (2 * n)) (k := 1)
        (fun _ _ => hE.1 (2 * n)) (fun _ _ => hreg (2 * n)) 1 le_rfl)
      (hpmΩ (2 * n + 1)) (φ := fun u _ => u (Fin.last (2 * n)))
      (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
      (ψ := fun v => Fin.snoc (α := fun _ => RecData)
        (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n) ω₀) (v 0))
      ((GW2Later.measurable_snoc_const _).comp (measurable_pi_apply 0)) ?_ ?_
    · filter_upwards [hLω hl0] with ω hω
      funext i
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      simp only [pastMap, Fin.val_zero, Fin.val_last]
      rw [retained_run_termSpec, retained_run_walk hω]
    · filter_upwards [hpmω, hLω hl0] with ω hω hl
      change pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1) ω = _
      rw [GW2Later.pastMap_succ_eq_snoc _ _ (2 * n) ω, hω]
      congr 1
      simp only [pastMap, Fin.val_zero, Fin.val_last]
      rw [retained_run_termSpec, retained_run_walk hl]
  filter_upwards [hK2, ae_all_iff.2 hcr, hkk, hrunω, hLω hl0, hPas,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀) (hE.2.1 (2 * n + 1)) (ae_all_iff.2 hpr)]
    with ω₁ hK2ω hcrω hkkω hrunω₁ hl1 hPasω₁ hprω₁ hnext hpos
  obtain ⟨hstage₁, hR₁, hQ₁, hK₁, hrun₁⟩ := hPasω₁
  have hfin := ne_top_of_next hl1 hnext
  obtain ⟨hown, -, -, hCl⟩ := hstage₁ (2 * n) hl1
  rw [GW1W.launch_walk hl1] at hCl
  have hthr := GW1WalkExit.own_threshold_of_pos_classified hfin hpos hCl
  obtain ⟨r, hev⟩ := exists_endsAtThresholdSide (θ' := θ) right hown hfin hthr
  obtain ⟨h'', htr'', hcd⟩ := hcrω r hev
  have hμ := hK2ω.trans hkkω
  rw [hμ] at hcd
  -- the field read by BW1 is the field read in the post-piece chart
  have hc1 : stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω₁) (2 * n)) = c := by rw [hc_eq, hrunω₁]
  have hpr1 : GW1P.PieceRegular (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁).1
      (min ⊤ (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁).2) := by
    obtain ⟨⟨c₁, θ₁⟩, hcθ₁⟩ := Option.ne_none_iff_exists'.1 hl1
    have := hR₁ (2 * n) θ₁ _ c₁ (eq_launch_of_launches _ _ hcθ₁).1 hcθ₁
    rwa [GW1W.instrTime_walk hl1] at this
  have hU := GW2Later.continuous_stopDrv hpr1
  have hT : 0 ≤ stopTime ⊤ (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁) := stopTime_nonneg _ _
  have hc₂ : (termChart (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁)).IsConformal := by
    rw [termChart, Chart.recenter_zero]
    exact Chart.isConformal_id.loewner hU.1 hU.2 hT
  have hℓ₂ : ContinuousOn (fun w => (termChart (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁)).2.2
      ((termChart (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁)).2.1 w)) QuantumZipper.H := by
    rw [termChart, Chart.recenter_zero]
    exact (Chart.isConformal_id.loewner hU.1 hU.2 hT).continuousOn_lift_inv
      (Chart.continuousOn_lift_loewner hU.1 hU.2 hT)
  have htrd : ∀ ω, IsChartTransport (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω₁) (2 * n + 1))) 1 0 (chiC κ) (h ω) (h'' ω) := fun ω => by
    rw [stChart_run_succ_eq_trans hl1 hfin, hc1]
    exact IsChartTransport.trans hcconf' hc₂ hclift' hℓ₂ (htrc ω) (htr'' ω)
  -- `Q` is the centred counterflow of the same field under the same conditional law
  obtain ⟨hcfQ, hζQ⟩ := hQ₁ hnext h'' htrd
  obtain ⟨-, hgffp, -, hconfd, hliftd, htrans⟩ := hK₁ hnext
  have hh''m : Measurable h'' := by
    have e : h'' = fun ω => Chart.chartTransport hconfd 1 0 (chiC κ) (h ω) := funext fun ω =>
      (htrd ω).eq_chartTransport hconfd (Chart.locallyIntegrableOn_of_continuousOn hliftd)
    rw [e]
    exact (Chart.measurable_chartTransport _ _ _ _).comp hh.1
  have hgff'' := isGFFWithBoundaryData_congr_ae hgffp hh''m (htrans h'' htrd)
  rw [hker ω₁] at hgff''
  -- the restarted event holds almost surely under the conditional law given the retained past
  have hevP₁ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
      (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω₁),
      BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 (E (GW1Z.walkSpec b jumps right) (2 * n) ω)
        θ ⊤) r := by
    filter_upwards [hrun₁] with ω hω
    have hlω : (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
      rw [hω]
      exact hl1
    have hret : retOf ⊤ (E (GW1Z.walkSpec b jumps right) (2 * n) ω) =
        retOf ⊤ (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁) := by
      rw [← retained_run_walk hlω, ← retained_run_walk hl1, hω]
    have h2 : (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2 = (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁).2 := by
      have := congrArg (fun x => x.2.1) hret
      simpa [retOf] using this
    exact (stStatus_launch_congr (s := ExplState.init 0) (k := 0) (θ := θ) (congrArg Prod.fst hret) h2).trans hev
  rw [hkkω] at hprω₁
  have hζW : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
      (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω₁), ζr r ω = ⊤ := by
    filter_upwards [hprω₁, hevP₁] with ω h1 h2
    exact (h1 r h2).1
  have hdet := GW4Ident.ae_eq_of_isCenteredCounterflowDriver h12p hT13 hκ
    (GW1Laws.postWord κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n βk
      ω₁).isPiecewiseConstantBoundaryData hgff'' hcfQ hζQ hcd hζW
  filter_upwards [hdet, hprω₁, hevP₁] with ω h1 h2 h3
  rw [h1]
  exact (h2 r h3).2

end Kernel

end InteractingSLE.Theorem14.BW1Term
