/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEraseGeo
import InteractingSLE.Spec.Supplement.SB2DrvPath
import InteractingSLE.Spec.Supplement.SBLxStep
import InteractingSLE.Spec.Supplement.SBLwChart
import InteractingSLE.Spec.Supplement.SBLemmaS5Proof

/-!
# The erased history misses `D_A`: `SB2ErasedAvoidStatement` proved

Packet PROVE-T14-SB2DRV (round 3). **`sb2ErasedAvoidStatement : SB2ErasedAvoidStatement`** (supplement p. 632, "the
erased history lies in `K_A`"): almost surely on SB2(1)'s launch event, the launch chart's domain misses the upper flow
up to `min(ζ, T_L)`. Ingredients, at a sample of the launch event:

* the retained lower prefix with its bridge is a path `p` from the upper seed `u` (`ae_isPrefixPath_launch`), the upper
  flow starts at `u` and is one-sided for it through every available time (`SB2LaunchProblem.one_sided`);
* Lemma S2 in the coordinates shifted by `−u` (`SB.image_subset_hullK_of_isOneSided`, with
  `Lx.isOneSided_sub_real_iff`, `Lx.realMin_path_sub`, `Lw.firstVisit_sub_real`): the flow up to `min(ζ, T_L)` lies in
  the compact hull `K_{A − u}`; in `ℍ` this is the fill of `A − u` (`hullK`'s real base has no point of `ℍ`), i.e.
  `fill(A) − u` (`Lw.fillH_image_sub_real`);
* the launch chart is the run's chart (`eq_launch_of_launches`), a chart of `ℍ \ fill(prefix)`
  (`Lw.isDomainChart_runChart`), and the fill of the prefix with its real bridge is that of the prefix
  (`Lw.fillH_union_real`).

With this, SB2(1)'s erasure clause (E2) is proved from Theorems 1.2–1.3 alone (`ae_erasure`).
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

open Exist.Staged Exist.StagedLaw

/-- A point of the compact hull in `ℍ` is a point of the fill. -/
theorem mem_fillH_of_mem_hullK_of_mem_H {A : Set ℂ} {z : ℂ} (hz : z ∈ hullK A) (hzH : z ∈ H) : z ∈ fillH A := by
  rcases hz with hz | ⟨x, -, rfl⟩
  · exact hz
  · exact absurd hzH (by simp [H])

/-- **The erased history misses `D_A`** (Lemma S2's geometry). -/
theorem sb2ErasedAvoidStatement : SB2ErasedAvoidStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hw
  have hstart : ∀ᵐ ω ∂P, η ω 0 = u := by
    obtain ⟨_, _, _, _, _, _, -, -, htr⟩ := HP.flow
    filter_upwards [htr] with ω h1
    have := h1.1
    simp only at this
    exact sub_eq_zero.1 this
  filter_upwards [ae_isPrefixPath_launch HP, HP.one_sided, hR.ae_pieceRegular, hstart] with ω hpath hos hpr hη0 hl
  obtain ⟨p, hpc, hp0, -, hpH, himg⟩ := hpath hl
  have hS1 : ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E (k + 1) u ω) (η ω) a := hos hl
  -- the launch chart is a chart of `ℍ \ fill(prefix)`
  have hreg' : ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c θ' hlj => hpr j c θ' hlj
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1) hnd
  have hdom : ((launchChart κ b jumps E (k + 1) ω).dom : Set ℂ) =
      H \ fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
    exact hD.1.coe_dom.trans hD.2.1
  -- Lemma S2 in shifted coordinates
  set A : Set ℂ := lowerPrefix κ b jumps E (k + 1) u ω with hA
  set p' : ℝ → ℂ := fun s => p s - u with hp'
  have himg' : p' '' Icc 0 1 = (fun z => z - (u : ℂ)) '' A := by
    rw [← himg, image_image]
  have hreal : realMin (p' '' Icc 0 1) = realMin A - u := by
    rw [himg', ← himg]
    exact Lx.realMin_path_sub hpc hp0
  have hp'c : ContinuousOn p' (Icc 0 1) := hpc.sub continuousOn_const
  have hp'0 : p' 0 = 0 := by simp [hp', hp0]
  have hp'H : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p' s).im := fun s hs => by simpa [hp'] using hpH s hs
  have hβ0 : (fun t => η ω t - (u : ℂ)) 0 = 0 := by simp [hη0]
  have hS1' : ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (p' '' Icc 0 1) (fun t => η ω t - (u : ℂ)) a :=
    fun a ha => by rw [himg']; exact (Lx.isOneSided_sub_real_iff u).2 (hS1 a ha)
  have hfv : firstVisit (fun t => η ω t - (u : ℂ)) (ζ ω) (realMin (p' '' Icc 0 1)) =
      firstVisit (η ω) (ζ ω) (realMin A) := by
    rw [hreal]
    exact Lw.firstVisit_sub_real (η ω) (ζ ω) _ u
  have hin0 := SB.image_subset_hullK_of_isOneSided (T := ⊤) hp'c hp'0 hp'H hβ0 hS1'
  rw [Set.disjoint_right]
  rintro z ⟨s, hs, rfl⟩ hzD
  rw [hdom] at hzD
  have hmem : η ω s - (u : ℂ) ∈ hullK (p' '' Icc 0 1) := by
    refine hin0 ⟨s, ?_, rfl⟩
    show (s : ℝ≥0∞) ≤ min (min ⊤ (ζ ω)) _
    rw [hfv, min_eq_right (le_top : ζ ω ≤ ⊤)]
    exact hs
  have hH : η ω s - (u : ℂ) ∈ H := by
    have h1 : (η ω s).im > 0 := hzD.1
    show 0 < (η ω s - (u : ℂ)).im
    simpa using h1
  have hfill := mem_fillH_of_mem_hullK_of_mem_H hmem hH
  rw [himg', Lw.fillH_image_sub_real] at hfill
  obtain ⟨w, hw, hwz⟩ := hfill
  have hwz' : w = η ω s := by
    have := congrArg (fun z => z + (u : ℂ)) hwz
    simpa using this
  rw [hwz', hA] at hw
  have hfu : fillH (lowerPrefix κ b jumps E (k + 1) u ω) =
      fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)) :=
    Lw.fillH_union_real _ _
  rw [hfu] at hw
  exact hzD.2 hw

end InteractingSLE.Theorem14.SB.Lv
