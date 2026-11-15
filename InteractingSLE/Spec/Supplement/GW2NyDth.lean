/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NyKer
import InteractingSLE.Spec.Supplement.GW2NxDth

/-!
# BUF's death threshold from the death clause in the datum form (decision D60)

Packet PROVE-GW2-NOTHR (round 7, decision D60 (A)). GB6's launch datum `HasLaunchPairEq … ω₀` becomes a premise of
D46's death clause (`StageDeathExportXD`, as STAGEMEAN's `GW2Pw.StageKernelExportLD` for the main clause), and the
kernel-to-`P` step goes through the kernel chain (`GW2Ny.ae_succ_of_kernel_curS`, built on
`GW2Omx.ae_of_kernel_curS`). The chain needs an admissible root and a strictly ordered history, so BUF's statement is
proved in that guarded form (`DeathThrXStatementS`); the top reads only alive histories, which are such.

* `StageDeathExportXD`, `DeathExportFamilyD`, `DeathThrXStatementS`, `DeathThrXStatementN.toS`;
* **`ae_kernel_deathEvent_finD`**: round 5's kernel step with the datum premise;
* **`deathThrX_of_exportD_fin`**: `DeathThrXStatementS` from the datum-form clause (D27 below a finite death clock and
  the caps below the death, as before);
* **`deathThrX_stopD`**: at the stop-capped family `GW2Nx.schedVerXStopFamily`, from the datum-form clause alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Ny

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe Supp8.Q3Stop
  MartChar.RealFlow GW2Nu GW2Nv Sec5.Prop513Schedule Sec5.CrossCond.StagedRepLater

/-! ### The statements -/

section Stmt

/-- **BUF's `DeathThrXStatement` at admissible roots and strictly ordered histories** (`GW2Nv.DeathThrXStatementN`
with the guard of the kernel chain; the top reads only alive histories, which are such). -/
def DeathThrXStatementS (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (h : GoodRoot c r),
    (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
    (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ∀ Wc : ℝ≥0 → ℝ, IsCanonXN c r l a (ver Ω c r l a).R (ver Ω c r l a).V ξ Wc →
      deathClockX c r l a ξ < ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)
        (schedW c r l a · ξ) (schedTr c r l a ξ) (c.α ξ)) →
      ∀ j : ℕ, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l a).V j ξ →
        ∃ u : ℝ≥0, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) + u = deathClockX c r l a ξ ∧
          StageThresholdN c.κ ((ch Ω c r l a).β ((instX h13 ver ch Ω c r l a j h.1).srecX c r l (rootPt r.1) ξ))
            (stgDrv Wc (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
              ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ)) u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **D46's death clause with GB6's launch datum as a premise** (decision D60 (A)): `GW2Nv.StageDeathExportX` with
`HasLaunchPairEq … ω₀ →` after `∀ᵐ ω₀ ∂c.P,`, as STAGEMEAN's `GW2Pw.StageKernelExportLD` for the main clause. -/
def StageDeathExportXD (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (I : StageInst Ω) (Rf : ℕ → ℝ≥0 → Ω → ℝ) (Vf : ℕ → Ω → ℝ≥0∞) (x₀ : ℝ) : Prop :=
  ∀ᵐ ω₀ ∂c.P, HasLaunchPairEq c.κ c.b c.jumps c.P c.h c.W (GW2Olm.futSpec c r l a) (GW2Olm.futFam c r l a)
    (GW2Olm.curIdx c r l) ω₀ → ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
    ∃ (b : ℝ → ℝ) (J : Finset ℝ) (h : Ω → DistOn upperHalfPlaneOpens) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞)
      (α : Ω → ℝ≥0 → ℂ) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (cw : BoundaryWord)
      (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) (t₀ : Ω → ℝ≥0) (lam : Ω → ℝ) (F : Ω → Set ℝ),
      IsPiecewiseConstantBoundaryData b J ∧ IsPiecewiseConstantBoundaryData b' J' ∧
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC c.κ)) (chiC (16 / c.κ)) (h ω) (h' ω)) ∧
      IsFlowLineDriver c.κ b J θ (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) h Wα ζα ∧
      (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) ∧
      IsFlowLineDriver (16 / c.κ) b' J' 0 (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) h' W ζ ∧
      (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), ζ ω = ⊤ ∧
        IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) ∧
      cw.jumps = J' ∧ (∀ y ∉ J', cw.fn y = b' y) ∧
      ∀ᵐ ξ ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), ξ ∈ I.GT → oldSuccess c r l ξ →
        ((stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ξ : ℝ≥0) : ℝ≥0∞) < I.V ξ → deathClockX c r l a ξ < ⊤ →
        γ ξ (t₀ ξ) ∈ H ∧ 0 < lam ξ ∧ (F ξ).Finite ∧
        (∀ y, y ∉ F ξ → (I.β (I.srecX c r l x₀ ξ)).fn y =
          (gw2Word c.κ θ cw (gb6Rec (t₀ ξ) W ζ ξ)).fn (lam ξ * y)) ∧
        ζα ξ = candLife c r l a ξ ∧
        (0 < candLife c r l a ξ →
          (((candLife c r l a ξ).toNNReal : ℝ≥0) : ℝ≥0∞) < gb6Tc (t₀ ξ) (extTr (t₀ ξ) Wα ζα α) γ ξ ∧
          (lam ξ) ^ 2 * ((deathClockX c r l a ξ).toReal - (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ξ : ℝ)) =
            gb6Clock (t₀ ξ) (regW (t₀ ξ) Wα ζα) W ξ (candLife c r l a ξ).toNNReal ∧
          ∃ Wd : ℝ≥0 → ℝ, Continuous Wd ∧ Wd 0 = 0 ∧ (∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < Vf n ξ → Rf n q ξ = Wd q) ∧
            ∀ t : ℝ≥0, t ≤ (candLife c r l a ξ).toNNReal →
              fwdHull (scD (lam ξ) (fun q : ℝ => stgDrv Wd (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ξ)
                  q.toNNReal)) (gb6Clock (t₀ ξ) (regW (t₀ ξ) Wα ζα) W ξ t) =
                relMap (fun r : ℝ => W r.toNNReal ξ) (t₀ ξ) ''
                  fwdHull (fun r : ℝ => regW (t₀ ξ) Wα ζα r.toNNReal ξ) t)

end Stmt

/-- **D46's death clause in the datum form at every root-`x` instance** (admissible roots, strictly ordered
histories) of a version family and a choice family. -/
def DeathExportFamilyD (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
    (h : GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) → ∀ a j : ℕ,
      StageDeathExportXD c r l a (instX h13 ver ch Ω c r l a j h.1) (ver Ω c r l a).R (ver Ω c r l a).V (rootPt r.1)

/-- The unguarded statement gives the guarded one. -/
theorem DeathThrXStatementN.toS {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}}
    {ch : SchedChoiceFamily.{u}} (h : GW2Nv.DeathThrXStatementN h13 ver ch) : DeathThrXStatementS h13 ver ch :=
  fun Ω _ _ c r l a hg _ hord => h Ω c r l a hg (Gm.timeOrdered_of_pairwise_lt hord)

section Ker

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The death event of every root-`x` instance holds under the launch kernel** of a launched candidate, from
D46's death clause in the datum form, D27's exhaustion below a FINITE death clock and the caps below the death. -/
theorem ae_kernel_deathEvent_finD (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a j : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hD27 : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      deathClockX c r l a ω < ⊤ → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
        (ver Ω c r l a).V n ω)
    (hcaps : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      0 < candLife c r l a ω → ∀ n, (ver Ω c r l a).V n ω < deathClockX c r l a ω)
    (hexp : StageDeathExportXD c r l a (instX h13 ver ch Ω c r l a j hx) (ver Ω c r l a).R (ver Ω c r l a).V
      (rootPt r.1)) :
    ∀ᵐ ω₀ ∂c.P, AllSucc (specDelta (GW2Olm.futSpec c r l a)) (fun i => GW2Olm.futFam c r l a i ω₀)
        (GW2Olm.curIdx c r l) →
      HasLaunchPairEq c.κ c.b c.jumps c.P c.h c.W (GW2Olm.futSpec c r l a) (GW2Olm.futFam c r l a)
        (GW2Olm.curIdx c r l) ω₀ →
      ∀ᵐ ξ ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀),
        ξ ∈ deathEvent c r l a (instX h13 ver ch Ω c r l a j hx) (ver Ω c r l a).R (ver Ω c r l a).V
          (rootPt r.1) := by
  set I := instX h13 ver ch Ω c r l a j hx with hI
  set x := rootPt r.1 with hxdef
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ := hS.2.1 k
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hGTs := schedGTX_spec h13 c r l a
  have hGT := hGTs.1
  have hver : ∀ n, IsRelVersionX x c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α
      ((ver Ω c r l a).R n) ((ver Ω c r l a).V n) := fun n => ((ver Ω c r l a).isA hx n).1.1
  filter_upwards [hexp, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hD27,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hcaps, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hGTs.2.2,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_srecX_mem_launchBadRec_iff h13 c r l a I x)]
    with ω₀ hX hD27₀ hcaps₀ hGT₀ hbad₀ hL₀ hdat
  have hlaunch := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _) (fun i => E i ω₀) (show k < spec.2.2.length by omega)).1 hL₀
  obtain ⟨b, J, h, Wα, ζα, α, b', J', h', cw, W, ζ, γ, t₀, lam, F, hb, hb', hT, hfl, hα, hcf, hγ, hcwJ, hcwb,
    hcl⟩ := hX hdat _ _ hlaunch
  have hG := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb hfl
  have hpos := ae_stage_threshold_at_death c.hκ c.hκ4 hb hG hb' hT hfl hα hcf hγ cw hcwJ hcwb
  have hseed := ae_stage_seed_at_death c.hκ hb hG hb' hT hfl hcf hγ cw hcwJ hcwb
  filter_upwards [hcl, hpos, hseed, hD27₀, hcaps₀, hGT₀, hbad₀]
    with ξ hclξ hposξ hseedξ hD27ξ hcapsξ hGTξ hbadξ hGξ holdξ hSV hfin
  have hgood : cfRec c.s c.W c.ζ ξ ∈ goodX x c.s := hGTξ.1 hGξ
  have hd : deathClockX c r l a ξ < ⊤ := (mem_deathFin_iff c r l a hGT I rfl rfl rfl hGξ).1 hfin
  obtain ⟨hγH, hlam, hFfin, hdat, hζα, hposcl⟩ := hclξ hGξ holdξ hSV hd
  set S := stgStartX x c.s c.W c.ζ I.W I.GT I.V I.T ξ with hSdef
  refine ⟨fun hbadrec => ?_, fun hnotbad => ?_⟩
  · -- a zero lifetime: the seed threshold
    have hz : candLife c r l a ξ = 0 := (hbadξ holdξ).1 hbadrec
    have h1 := hseedξ (t₀ ξ) (hζα.trans hz) (I.β (I.srecX c r l x ξ)) (lam ξ) (F ξ) (fun _ => (0 : ℝ)) hlam hFfin
      hdat continuous_const rfl
    exact (stageThresholdN_zero_iff (I.β (I.srecX c r l x ξ)) continuous_const rfl).1 h1
  · -- a positive lifetime: the threshold at the death, read through the versions
    have hclpos : 0 < candLife c r l a ξ := pos_iff_ne_zero.2 fun hz => hnotbad ((hbadξ holdξ).2 hz)
    obtain ⟨hTc, hclk, Wd, hWdc, hWd0, hWdagree, hhull⟩ := hposcl hclpos
    obtain ⟨hSeq, hS0, -, hSlt, -⟩ := stage_start_death c r l a hGT hs hx hGξ ((ver Ω c r l a).fin j ξ) hSV hd
    have hSeq' : (S : ℝ) = clockX x c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ξ := hSeq
    have hdeq := deathClockX_eq_of_lt_top c r l a hd
    set dN := (deathClockX c r l a ξ).toNNReal with hdNdef
    have hdN : (dN : ℝ≥0∞) = deathClockX c r l a ξ := ENNReal.coe_toNNReal hd.ne_top
    have hclN : (((candLife c r l a ξ).toNNReal : ℝ≥0) : ℝ≥0∞) = candLife c r l a ξ :=
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top
        ((deathClockX_lt_top_iff c r l a ξ).1 hd).1)
    have hlt := hSlt hclpos
    have hdNr : (dN : ℝ) = clockX x c.s c.W c.ζ (schedW c r l a) (historyTime c r l +
        (candLife c r l a ξ).toNNReal) ξ := by
      rw [hdNdef, ENNReal.coe_toNNReal_eq_toReal, hdeq, ENNReal.toReal_ofReal (hS0.trans hlt.le)]
    have hSd : S < dN := by
      have h1 : (S : ℝ) < (dN : ℝ) := by rw [hSeq', hdNr]; exact hlt
      exact NNReal.coe_lt_coe.1 h1
    set u := dN - S with hudef
    have hu : 0 < u := tsub_pos_of_lt hSd
    have hSu : S + u = dN := add_tsub_cancel_of_le hSd.le
    have hucoe : (u : ℝ) = (deathClockX c r l a ξ).toReal - (S : ℝ) := by
      rw [hudef, NNReal.coe_sub hSd.le]
      rfl
    -- the versions at `ξ`
    have hcapsN : ∀ n, (ver Ω c r l a).V n ξ < (dN : ℝ≥0∞) := fun n => hdN ▸ hcapsξ hgood holdξ hclpos n
    have hexhN : ∀ q : ℝ≥0, q < dN → ∃ n, (q : ℝ≥0∞) < (ver Ω c r l a).V n ξ := fun q hq =>
      exists_cap_gt c r l a hGT hs hx hGξ hd (hD27ξ hgood holdξ hd) (hdN ▸ ENNReal.coe_lt_coe.2 hq)
    have hmono : Monotone fun n => (ver Ω c r l a).V n ξ := monotone_nat_of_le_succ fun n => (ver Ω c r l a).mono n ξ
    have hsup : (⨆ n, (ver Ω c r l a).V n ξ) = (dN : ℝ≥0∞) := by
      refine le_antisymm (iSup_le fun n => (hcapsN n).le) (ENNReal.le_of_forall_nnreal_lt fun q hq => ?_)
      obtain ⟨n, hn⟩ := hexhN q (ENNReal.coe_lt_coe.1 hq)
      exact hn.le.trans (le_iSup (fun n => (ver Ω c r l a).V n ξ) n)
    have hprox := stageProxy_eq (R := fun n q => (ver Ω c r l a).R n q ξ) (V := fun n => (ver Ω c r l a).V n ξ)
      (fun n => (hver n).2.1 ξ) (fun n => (hver n).2.2.1 ξ) hmono (fun n t ht => (hver n).2.2.2.1 ξ t ht)
      hcapsN hexhN hWdc hWd0 hWdagree hSu hu
    -- SAFE's converse at the death
    have hT0 : 0 < (candLife c r l a ξ).toNNReal :=
      ENNReal.toNNReal_pos hclpos.ne' (by rw [← hclN]; exact ENNReal.coe_ne_top)
    have hthr := hposξ (t₀ ξ) hγH (candLife c r l a ξ).toNNReal hT0 (hζα.trans hclN.symm) hTc
      (I.β (I.srecX c r l x ξ)) (lam ξ) (F ξ) (stgDrv Wd S) u hlam hFfin hdat (continuous_stgDrv hWdc S)
      (stgDrv_zero Wd S) (by rw [hucoe]; exact hclk) hhull
    show ProxThr c.κ (I.β (I.srecX c r l x ξ)) (fun n q => (ver Ω c r l a).R n q ξ) S
      ((⨆ n, (ver Ω c r l a).V n ξ).toNNReal - S)
    rw [hsup, ENNReal.toNNReal_coe, ← hudef]
    unfold ProxThr
    rw [hprox.1]
    simp only [hprox.2.1, hprox.2.2]
    exact hthr

end Ker

/-- **BUF's `DeathThrXStatement` (admissible roots, strictly ordered histories) from D46's death clause in the datum
form** (round 5's `GW2Nv.deathThrX_of_export_fin` with the kernel chain `GW2Omx.ae_of_kernel_curS`). -/
theorem deathThrX_of_exportD_fin (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u})
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (ch Ω c r l a).β ∧
        (range fun y => wordType c.κ ((ch Ω c r l a).β y)).Countable ∧ ∀ y, ((ch Ω c r l a).β y).IsSorted)
    (hD27 : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        deathClockX c r l a ω < ⊤ → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
          (ver Ω c r l a).V n ω)
    (hcaps : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        0 < candLife c r l a ω → ∀ n, (ver Ω c r l a).V n ω < deathClockX c r l a ω)
    (hexp : DeathExportFamilyD h13 ver ch) : DeathThrXStatementS h13 ver ch := by
  intro Ω mΩ' _ c r l a h hroot hord'
  have hord : GW2Sdx.HistOrdered c r l := Gm.timeOrdered_of_pairwise_lt hord'
  set x := rootPt r.1 with hxdef
  have hx : 0 ≤ x := h.1
  have hs : 0 < c.s := h.2
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ' := hS.2.1 k
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hLS : MeasurableSet[GW2Olm.pastG c r l a] {ω | AllSucc (specDelta spec) (fun j => E j ω) k} :=
    measurableSet_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl (isFlowProg_spec x true L)
      (specDelta_ne_top _) E (by rw [hlen]; omega)
  have hGTs := schedGTX_spec h13 c r l a
  have hGT := hGTs.1
  have hWm : ∀ t, Measurable (schedW c r l a t) := measurable_schedW c r l a
  have hver : ∀ n, IsRelVersionX x c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α
      ((ver Ω c r l a).R n) ((ver Ω c r l a).V n) := fun n => ((ver Ω c r l a).isA hx n).1.1
  -- the death event of every instance, `P`-almost surely
  have hZ : ∀ j : ℕ, ∀ᵐ ξ ∂c.P, ξ ∈ {ω | AllSucc (specDelta spec) (fun j => E j ω) k} →
      ξ ∈ deathEvent c r l a (instX h13 ver ch Ω c r l a j hx) (ver Ω c r l a).R (ver Ω c r l a).V x := by
    intro j
    set I := instX h13 ver ch Ω c r l a j hx with hI
    have hverR : IsRelVersionXR x c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α I.R I.V :=
      ((ver Ω c r l a).isA hx j).1
    have hpre : Measurable (stgPreRecX x c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
      (measurable_stgPreRecX hGTs.1 hs hx (measurable_gb6Rec_src c) hWm
        (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGTs.2.1 hGTs.2.2) hverR I.T).mono
        ((physFilt (measurable_gb6Rec_src c) hWm c.P).le I.T) le_rfl
    have hmeas := measurableSet_deathEvent c r l a I x hGTs.2.1 (measurable_stgStartX_of_pre hpre)
      (hver j).2.2.2.2.1 (measurableSet_deathFin h13 c r l a I rfl rfl)
      (measurable_augRec (measurable_stageEncRec c r l) hpre) (hword Ω c r l hord h a).1 (hword Ω c r l hord h a).2.1
      (fun n => (hver n).1) (fun n => (hver n).2.1) (fun n => (hver n).2.2.2.2.1)
    exact ae_succ_of_kernel_curS h12 h13 h12₀ h13₀ c r l a hroot hord' hmeas
      (ae_kernel_deathEvent_finD h13 ver ch c r l a j hx hs (hD27 Ω c r l a h hord) (hcaps Ω c r l a h hord)
        (hexp Ω c r l hord' h hroot a j))
  filter_upwards [ae_all_iff.2 hZ, hD27 Ω c r l a h hord, hcaps Ω c r l a h hord, hGTs.2.2,
    ae_all_iff.2 fun j => ae_srecX_mem_launchBadRec_iff h13 c r l a (instX h13 ver ch Ω c r l a j hx) x]
    with ξ hZξ hD27ξ hcapsξ hGTξ hbadξ hGξ hold Wc hcanon hdL j hSV
  obtain ⟨hWc, hWc0, hagree, -, -⟩ := hcanon
  set I := instX h13 ver ch Ω c r l a j hx with hI
  have hgood : cfRec c.s c.W c.ζ ξ ∈ goodX x c.s := hGTξ.1 hGξ
  have hd : deathClockX c r l a ξ < ⊤ := hdL.trans ENNReal.ofReal_lt_top
  have hfin : ξ ∈ deathFin c r l a I x := (mem_deathFin_iff c r l a hGT I rfl rfl rfl hGξ).2 hd
  have hev := hZξ j (Gm.allSucc_future_of_oldSuccess c r l a ξ hold) hGξ hold hSV hfin
  set S := stgStartX x c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j)
    (historyTime c r l) ξ with hSdef
  obtain ⟨hSeq, hS0, -, hSlt, hSeqz⟩ := stage_start_death c r l a hGT hs hx hGξ ((ver Ω c r l a).fin j ξ) hSV hd
  have hdeq := deathClockX_eq_of_lt_top c r l a hd
  by_cases hbad : I.srecX c r l x ξ ∈ launchBadRec c r l a
  · -- a zero lifetime: the death is the stage start
    have hz : candLife c r l a ξ = 0 := (hbadξ j hold).1 hbad
    refine ⟨0, ?_, ?_⟩
    · rw [ENNReal.coe_zero, add_zero, hdeq, ← hSeqz hz, ← hSeq, ENNReal.ofReal_coe_nnreal]
    · exact (stageThresholdN_zero_iff _ (continuous_stgDrv hWc S) (stgDrv_zero Wc S)).2 (hev.1 hbad)
  · -- a positive lifetime: the threshold at the death through the versions
    have hclpos : 0 < candLife c r l a ξ := pos_iff_ne_zero.2 fun hz => hbad ((hbadξ j hold).2 hz)
    have hlt := hSlt hclpos
    set dN := (deathClockX c r l a ξ).toNNReal with hdNdef
    have hdN : (dN : ℝ≥0∞) = deathClockX c r l a ξ := ENNReal.coe_toNNReal hd.ne_top
    have hdNr : (dN : ℝ) = clockX x c.s c.W c.ζ (schedW c r l a) (historyTime c r l +
        (candLife c r l a ξ).toNNReal) ξ := by
      rw [hdNdef, ENNReal.coe_toNNReal_eq_toReal, hdeq, ENNReal.toReal_ofReal (hS0.trans hlt.le)]
    have hSd : S < dN := by
      have h1 : (S : ℝ) < (dN : ℝ) := by rw [hSeq, hdNr]; exact hlt
      exact NNReal.coe_lt_coe.1 h1
    set u := dN - S with hudef
    have hu : 0 < u := tsub_pos_of_lt hSd
    have hSu : S + u = dN := add_tsub_cancel_of_le hSd.le
    have hcapsN : ∀ n, (ver Ω c r l a).V n ξ < (dN : ℝ≥0∞) := fun n => hdN ▸ hcapsξ hgood hold hclpos n
    have hexhN : ∀ q : ℝ≥0, q < dN → ∃ n, (q : ℝ≥0∞) < (ver Ω c r l a).V n ξ := fun q hq =>
      exists_cap_gt c r l a hGT hs hx hGξ hd (hD27ξ hgood hold hd) (hdN ▸ ENNReal.coe_lt_coe.2 hq)
    have hmono : Monotone fun n => (ver Ω c r l a).V n ξ := monotone_nat_of_le_succ fun n => (ver Ω c r l a).mono n ξ
    have hsup : (⨆ n, (ver Ω c r l a).V n ξ) = (dN : ℝ≥0∞) := by
      refine le_antisymm (iSup_le fun n => (hcapsN n).le) (ENNReal.le_of_forall_nnreal_lt fun q hq => ?_)
      obtain ⟨n, hn⟩ := hexhN q (ENNReal.coe_lt_coe.1 hq)
      exact hn.le.trans (le_iSup (fun n => (ver Ω c r l a).V n ξ) n)
    have hprox := stageProxy_eq (R := fun n q => (ver Ω c r l a).R n q ξ) (V := fun n => (ver Ω c r l a).V n ξ)
      (fun n => (hver n).2.1 ξ) (fun n => (hver n).2.2.1 ξ) hmono (fun n t ht => (hver n).2.2.2.1 ξ t ht)
      hcapsN hexhN hWc hWc0 hagree hSu hu
    have hP := hev.2 hbad
    change ProxThr c.κ (I.β (I.srecX c r l x ξ)) (fun n q => (ver Ω c r l a).R n q ξ) S
      ((⨆ n, (ver Ω c r l a).V n ξ).toNNReal - S) at hP
    rw [hsup, ENNReal.toNNReal_coe, ← hudef] at hP
    refine ⟨u, ?_, ?_⟩
    · rw [← ENNReal.coe_add, hSu, hdN]
    · unfold ProxThr at hP
      rw [hprox.1] at hP
      simp only [hprox.2.1, hprox.2.2] at hP
      exact hP

/-- **BUF's `DeathThrXStatement` at the stop-capped family from the datum-form death clause** (admissible roots,
strictly ordered histories). -/
theorem deathThrX_stopD (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (ch : SchedChoiceFamily.{u})
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (ch Ω c r l a).β ∧
        (range fun y => Supp8.Q3Stop.wordType c.κ ((ch Ω c r l a).β y)).Countable ∧
        ∀ y, ((ch Ω c r l a).β y).IsSorted)
    (hexp : DeathExportFamilyD h13 (GW2Nx.schedVerXStopFamily h13) ch) :
    DeathThrXStatementS h13 (GW2Nx.schedVerXStopFamily h13) ch :=
  deathThrX_of_exportD_fin h12 h13 h12₀ h13₀ (GW2Nx.schedVerXStopFamily h13) ch hword (GW2Nx.hD27_stop h13)
    (GW2Nx.hcaps_stop h13) hexp

end InteractingSLE.Theorem14.GW2Ny
