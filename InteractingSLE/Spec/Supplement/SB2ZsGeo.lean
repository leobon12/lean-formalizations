/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineGeo
import InteractingSLE.Spec.Supplement.SB2ZsAsm

/-!
# SB2ZsGeo: `SB2DrvLineGeo` for the lifetime-generic line version `SB2LineVersionG`

Packet PROVE-T14-SB2DRV (round 15, decision D4: SB2(1) at announced stops). The declarations of `SB2DrvLineGeo` that
depend on the line version, for `SB2LineVersionG` (guards `a t < Λ w` in place of `a t < thr`), with the suffix `G`.
The proofs are the landed ones with the guard replaced. No source theorem is replaced.
-/
/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/

/-!
# SB2(1)'s line geometry: `SB2LineGeomStatement` proved

Packet PROVE-T14-SB2DRV (round 4). **`sb2LineGeomStatement : SB2LineGeomStatement`**: almost surely on the live cell
at absolute physical time `T`, the union `A ∪ η([0, max(T, T_L)])` (the capped construction `D.absSet T`) misses the
chart image `c(ℍ \ K_{a T})` of the complement of the relative hull. Points of the union are

* in the retained lower prefix: outside the run chart's domain (`WalkSide.disjoint_dom_or_done`);
* on the upper flow up to `T_L`: outside `D_A` (`sb2ErasedAvoidStatement`, Lemma S2);
* on the upper flow in `(T_L, T]`: if in `D_A`, then sent by the chart into the relative hull — the hull clause
  of the relative chain in the version data's chain record (`FinRel.IsSB2RelChain`, shifted coordinates), with the
  relative hull of the chain driver equal to that of K2's driver below the lifetime (`ZhanGT4.A34.fwdHull_congr_of_lt`).

Hence the kernel half needs only the line mean: **`sb2LineKernelStatement_of_mean`**,
**`sb2DriverLinkAmbStatement_of_version_mean`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets

/-- **The line geometry.** -/
theorem sb2LineGeomStatementG : SB2LineGeomStatementG.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw t
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hwp := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hwp
  filter_upwards [Vd.chain w hw t, I.chart_eq, D.version, D.Lp_eq,
    ae_verChart_eq_runChart hR (HP.drivers_regular _) (k + 1), hR.ae_pieceRegular,
    sb2ErasedAvoidStatement κ b jumps P h E k u ψ η ζ HP, D.ae_mem_event_iff]
    with ω hch hce hv hL hver hpr hav hev hlive
  have hcell : ω ∈ seedCell κ ψ I.word D.event w := hlive.1
  have hevω : ω ∈ D.event := hcell.1.1
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hevω
  have hT : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω := (hev hl).1 hevω
  have hlt := hlive.2
  obtain ⟨p, g, β', γ, tL, S, Wr, ηr, w', ηw, htS, ⟨-, -, -, -, himgp⟩, -, ⟨-, -, -, -, hTL, -, -, -⟩, hagree,
    ⟨-, hchainAll, -⟩, -, ⟨hWWr, -, ha⟩⟩ := hch hcell hlt
  -- the charts and the domains
  have hreg' : ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c θ' hlj => hpr j c θ' hlj
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  have hdis := (WalkSide.disjoint_dom_or_done (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1)).resolve_left hnd
  have hDrun : ((I.chart ω).dom : Set ℂ) =
      (((ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)).2.2.2.2.1).dom : Set ℂ) := by
    show ((((verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (I.entry ω)).dom : Set ℂ)) = _
    rw [Chart.dom_recenter, hver]
    rfl
  have hchart : I.chart ω = (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω) :=
    hce hl
  have hDl : ((I.chart ω).dom : Set ℂ) = ((launchChart κ b jumps E (k + 1) ω).dom : Set ℂ) := by
    rw [hchart, Chart.dom_recenter]
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1) hnd
  have hdomA : ((I.chart ω).dom : Set ℂ) =
      H \ fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)) := by
    rw [hDrun]
    exact hD.1.coe_dom.trans hD.2.1
  have hz' : D.point ω = (realMin (lowerPrefix κ b jumps E (k + 1) u ω) : ℂ) := by
    simp only [EntranceUnion.point, hL hl]
  rw [Set.disjoint_left]
  intro z hz hzc
  rw [mem_chartImage_iff (isConformal_chart I ω)] at hzc
  obtain ⟨hzD₀, hzK⟩ := hzc
  have hzD : z ∈ ((I.chart ω).dom : Set ℂ) := hzD₀
  rw [EntranceUnion.absSet, limSet_eq] at hz
  rcases hz with hzA | hzR
  · rw [hDrun] at hzD
    exact Set.disjoint_left.1 hdis hzD hzA.1
  obtain ⟨n, hzn⟩ := mem_iUnion.1 hzR
  obtain ⟨⟨s', hs', rfl⟩, hzH⟩ := hzn
  have hσ := hv n s'
  set σ : ℝ≥0 := capTime (n : ℝ≥0) (ζ ω) s' with hσdef
  have hσζn := coe_capTime_le (ζ := ζ ω) (n : ℝ≥0) s'
  by_cases hσT : (σ : ℝ≥0∞) ≤ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
  · -- the erased part
    have hzD' : D.ηc n ω s' ∈ ((launchChart κ b jumps E (k + 1) ω).dom : Set ℂ) := by rw [← hDl]; exact hzD
    rw [hσ] at hzD'
    exact Set.disjoint_left.1 (hav hl) hzD' ⟨σ, le_min (hσζn.trans (min_le_left _ _)) hσT, rfl⟩
  -- the relative part: `T_L < σ ≤ T`
  push Not at hσT
  have hTn : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (n : ℝ≥0∞) :=
    hσT.trans_le (hσζn.trans (min_le_right _ _))
  have hhit := (hitQ_capped_eq (γ := η ω) (ζ := ζ ω) (γc := fun n => D.ηc n ω) (n := n) (D.paths.cont n ω) (hv n)
    (z := D.point ω) (by rw [hz']; exact hT) (by rw [hz']; exact hTn)).1
  rw [hz'] at hhit
  have hs'le : (s' : ℝ≥0∞) ≤ max (t : ℝ≥0∞) (firstVisit (η ω) (ζ ω)
      (realMin (lowerPrefix κ b jumps E (k + 1) u ω))) := by
    have := hs'
    simp only [mem_ofPred_eq, maxRule] at this
    rw [hz', hhit] at this
    exact this
  have hσs' : (σ : ℝ≥0∞) ≤ s' := ENNReal.coe_le_coe.2 (capTime_le_self _ _)
  have hσt : (σ : ℝ≥0∞) ≤ t := by
    rcases le_max_iff.1 (hσs'.trans hs'le) with h1 | h1
    · exact h1
    · exact absurd h1 (not_le.2 hσT)
  have hσt' : (σ : ℝ) ≤ t := by exact_mod_cast hσt
  have hTLσ : (tL : ℝ) < σ := by
    have h1 : (tL : ℝ≥0∞) < σ := by rw [hTL]; exact hσT
    exact_mod_cast h1
  have htL_t : (tL : ℝ) ≤ t := le_of_lt (hTLσ.trans_le hσt')
  -- the chain at `s = t − t_L`
  set sR : ℝ := (t : ℝ) - tL with hsR
  have hs0 : 0 ≤ sR := by rw [hsR]; linarith
  have hsS : sR < S := by rw [hsR]; linarith
  obtain ⟨-, -, -, -, -, -, hcl⟩ := hchainAll sR hs0 hsS
  obtain ⟨hcap0, -, -, hIn, -⟩ := hcl sR ⟨hs0, le_rfl⟩
  have hcapR : ((Vd.a t ω).toNNReal : ℝ) = Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) sR := by
    have ha' : Vd.a t ω = ((Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) ((t : ℝ) - tL)).toNNReal : ℝ≥0∞) :=
      ha t htL_t htS
    rw [ha', ENNReal.toNNReal_coe, Real.coe_toNNReal _ hcap0]
  have hhull : relHullG Vd t ω = fwdHull Wr (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) sR) := by
    unfold relHullG
    rw [hcapR]
    obtain ⟨T₀, hT₀a, hT₀V⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    refine ZhanGT4.A34.fwdHull_congr_of_lt hcap0 (T₀ := T₀) ?_ fun r hr => ?_
    · rw [← hcapR]
      have := ENNReal.toNNReal_lt_toNNReal (ne_top_of_lt hlt) ENNReal.coe_ne_top |>.2 hT₀a
      rw [ENNReal.toNNReal_coe] at this
      exact_mod_cast this
    · have hrV : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < Vd.Λ w ω := by
        refine lt_of_lt_of_le ?_ hT₀V.le
        rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1]
        exact hr.2
      show Vd.W r.toNNReal ω = Wr r
      have hW1 : Vd.W r.toNNReal ω = Wr (r.toNNReal : ℝ) := hWWr r.toNNReal hrV
      rw [hW1, Real.coe_toNNReal _ hr.1]
  have hβσ : β' σ = η ω σ - u := hagree σ (by linarith)
  have hzu : D.ηc n ω s' - (u : ℂ) ∈ fillH (β' '' Icc 0 (tL + sR.toNNReal)) := by
    refine ⟨?_, Or.inl (subset_closure ⟨σ, ⟨zero_le, ?_⟩, ?_⟩)⟩
    · show 0 < (D.ηc n ω s' - (u : ℂ)).im
      have : 0 < (D.ηc n ω s').im := hzH
      simpa using this
    · rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hs0, hsR]
      linarith
    · rw [hβσ, hσ]
  have hnot : D.ηc n ω s' - (u : ℂ) ∉ fillH (p '' Icc 0 1) := by
    rintro hm
    rw [himgp, Lw.fillH_image_sub_real] at hm
    obtain ⟨w₀, hw₀, hwz⟩ := hm
    have hw₀z : w₀ = D.ηc n ω s' := by
      have := congrArg (fun z => z + (u : ℂ)) hwz
      simpa using this
    rw [hw₀z, show fillH (lowerPrefix κ b jumps E (k + 1) u ω) =
        fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)) from
        Lw.fillH_union_real _ _] at hw₀
    rw [hdomA] at hzD
    exact hzD.2 hw₀
  have h1 := hIn _ hzu hnot
  have hfwd : (Lw.shiftChart (launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).1
      (D.ηc n ω s' - (u : ℂ)) = (I.chart ω).1 (D.ηc n ω s') := by
    rw [Lw.shiftChart_fwd, sub_add_cancel, hchart]
    rfl
  rw [hfwd, ← hhull] at h1
  exact hzK h1
end InteractingSLE.Theorem14.SB.Lv

