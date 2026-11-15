/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CwDom
import InteractingSLE.Spec.Supplement.SB2CwIdent
import InteractingSLE.Spec.Supplement.SB2MzFill
import InteractingSLE.Spec.Supplement.SB2QxCanon
import InteractingSLE.Spec.Supplement.SB2JvEnd

/-!
# The chain facts of the canonical driver at one sample

Packet PROVE-SB2-CANON, round 5 ((P4)). **`chainFacts_at`**: at one sample of a tail launch of positive lifetime,
`Qx.ChainFacts` (the identification record of `Mz.CanonIdentOn`) holds for the canonical driver `e` of
`(c, field in Mo.hullChart (fill K) x₀)`, from

* B's stage chart `cℓ` (`Mn.walkStageChart`): a domain chart of `ℍ ∖ fill B` (`B` B's prefix), normalized, with a
  bounded boundary map on `ℍ̄` (`S3.Canon.runChart_package`);
* the retained union `Y = A ∪ B` compact with `fill Y` a hull and `fill K = fill Y`;
* the canonical curve `ρ = canonCurve Y x₀ p L` driven (`p` B's physical piece, `L` its lifetime), B's stage trace
  `β' = trOf (E ℓ)` continuous and in `ℍ̄` up to `L`;
* the identification `e = segDriver ρ` below `capLife ρ = e.2` (`ident_canon_at`), and the continuity of `e` up to its
  lifetime (`SB2CqCont`: Theorem 1.3 for the conditional flow line).

The clauses: the stage chart is a domain chart (`isDomainChart_stageChartOf`), the stage complement is unfilled
(`Mz.notMem_fillH_stageRetained`), the chain clause (`chainFor_canon` with `SB2CwStage`'s inputs), positivity
(`Lk.capLife_pos_of_driven`), continuity up to the lifetime (an input).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Sec7.PocketTraversal Sec7.Lemma71C Exist Exist.Staged Exist.StagedLaw Lu Mx Mz

/-- **The chain facts of the canonical driver at one sample.** See the module docstring. -/
theorem chainFacts_at (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0))
    (k ℓ : ℕ) {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → BoundaryWord} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {ω : Ω}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
      (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hD : IsDomainChart (H \ fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) ℓ)) (Mn.walkStageChart κ b jumps E ℓ ω))
    (hN : WalkIntCanon.IsNormalized (Mn.walkStageChart κ b jumps E ℓ ω)) {gc : ℂ → ℂ}
    (hgct : ∀ q ∈ Hbar, Tendsto (Mn.walkStageChart κ b jumps E ℓ ω).2.1 (𝓝[H] q) (𝓝 (gc q))) {C : ℝ}
    (hgC : ∀ q ∈ Hbar, ‖gc q - q‖ ≤ C)
    (hYc : IsCompact (retY (κ := κ) b jumps E u l k ℓ ω)) (hA : IsHPHull (fillH (retY (κ := κ) b jumps E u l k ℓ ω)))
    (hfill : fillH (K ω) = fillH (retY (κ := κ) b jumps E u l k ℓ ω))
    (hL0 : (lowerD b jumps E ω ℓ).2 ≠ 0)
    (hpc : ContinuousOn (Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) ℓ) (lowerD b jumps E ω ℓ)) {t | (t : ℝ≥0∞) ≤ (lowerD b jumps E ω ℓ).2})
    (hdr : IsDrivenCurve (Dv.canonCurve (retY (κ := κ) b jumps E u l k ℓ ω) (x₀ ω)
      (Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ)
        (lowerD b jumps E ω ℓ)) (lowerD b jumps E ω ℓ).2))
    (hβc : ContinuousOn (LuM.trOf (lowerD b jumps E ω ℓ)) {t | (t : ℝ≥0∞) ≤ (lowerD b jumps E ω ℓ).2})
    (hβH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (lowerD b jumps E ω ℓ).2 → 0 ≤ (LuM.trOf (lowerD b jumps E ω ℓ) t).im)
    (he1 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife (Dv.canonCurve (retY (κ := κ) b jumps E u l k ℓ ω) (x₀ ω)
      (Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ)
        (lowerD b jumps E ω ℓ)) (lowerD b jumps E ω ℓ).2) →
      (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).1 t = segDriver (Dv.canonCurve (retY (κ := κ) b jumps E u l k ℓ ω)
        (x₀ ω) (Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (lowerD b jumps E ω) ℓ) (lowerD b jumps E ω ℓ)) (lowerD b jumps E ω ℓ).2) t)
    (he2 : (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).2 = capLife (Dv.canonCurve (retY (κ := κ) b jumps E u l k ℓ ω)
      (x₀ ω) (Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (lowerD b jumps E ω) ℓ) (lowerD b jumps E ω ℓ)) (lowerD b jumps E ω ℓ).2))
    (hcont : ContinuousOn (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).1
      {s | (s : ℝ≥0∞) ≤ (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).2}) :
    Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω := by
  set cℓ := Mn.walkStageChart κ b jumps E ℓ ω with hcℓ
  set Y := retY (κ := κ) b jumps E u l k ℓ ω with hY
  set B := SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ
    with hBdef
  set e := Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω with hedef
  have hBY : B ⊆ Y := subset_union_right
  have hreg : IsRegularDriver e := Mz.isRegularDriver_driverOf h12p hκ _ _
  -- the stage chart's inverse agrees with its boundary map in `ℍ`
  have hcH : ContinuousOn cℓ.2.1 H := hD.isConformal.1.continuousOn
  have hgeq : ∀ q ∈ H, gc q = cℓ.2.1 q := fun q hq => by
    have : (𝓝[H] q).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hq)
    exact tendsto_nhds_unique (hgct q (le_of_lt (show 0 < q.im from hq))) (hcH q hq).tendsto
  have hM : ∀ v ∈ H, ‖cℓ.2.1 v - v‖ ≤ C := fun v hv => by
    rw [← hgeq v hv]; exact hgC v (le_of_lt (show 0 < v.im from hv))
  have hinj : InjOn cℓ.2.1 H := fun v hv w hw hvw => by
    rw [← hD.fwd_inv hv, hvw, hD.fwd_inv hw]
  have hbl : ∀ x : ℝ, ∃ y : ℂ, Tendsto cℓ.2.1 (𝓝[H] (x : ℂ)) (𝓝 y) := fun x =>
    ⟨gc x, hgct x (by simp [Hbar])⟩
  -- the stage version of the canonical chart
  have hdomY : IsDomainChart (H \ Mn.stageRetained cℓ Y) (stageChartOf cℓ (Mo.hullChart (fillH Y) (x₀ ω))) :=
    isDomainChart_stageChartOf hD (Mo.isDomainChart_hullChart hA (x₀ ω)) (fillH_mono hBY)
  have hchain := chainFor_canon (cℓ := cℓ) hYc hA hL0 hpc hdr
    (fun z hz => mem_diff_of_notMem_fillH_stageRetained hD.isConformal hz) hinj
    (fun s hs z hz _ => mem_joint_of_mem_fillH_stage hD hM hBY
      (hβc.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hs.le)
      (fun r _ hrH => (LuM.bdVal_eq_of_mem_H hcH hrH)) hz)
    (fun t ht hp => piece_of_mem_diff hD hBY hYc.isClosed hbl (hβH t ht.le) hp)
    hreg he1 he2
  refine ⟨hl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfill]; exact hdomY
  · exact Mz.notMem_fillH_stageRetained hN hA.2.1 hdomY
  · rw [hfill]; exact hchain
  · rw [he2]; exact (Lk.capLife_pos_of_driven hdr).ne'
  · exact hcont

end InteractingSLE.Theorem14.SB.Cz
