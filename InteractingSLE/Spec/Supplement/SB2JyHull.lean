/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JyTip
import InteractingSLE.Spec.Supplement.SB2JiGeom
import InteractingSLE.Spec.Supplement.SB2LkCurve
import InteractingSLE.Spec.Supplement.SBLemmaS5Proof
import InteractingSLE.Spec.Supplement.WalkIntRunChronCarrier
import InteractingSLE.Spec.Supplement.SB2KEntry

/-!
# SB2(2): the upper chart's facts and the tail position of the walk's points in `D`

Packet PROVE-SB2-LIFTSET (round 14). Facts of `StageGeom` **proved outright**:

* `image_H_recenter`; **`sb2LowerUpperChart`**: almost surely at a launch, the upper chart `c` satisfies
  `UpperChartOK c` (continuity of `c⁻¹` on `ℍ`, the inverse identity, `BdryOff c` by `bdryOff_of_ext`) and its domain
  is `D = c⁻¹ '' ℍ = ℍ \ fillH A` for the retained upper history `A` (`Lf.isRightEntryChart_runChart`);
* **`sb2LowerHeadHull`**: almost surely under the retained kernel, the head `β₀ '' [0, t_L]` of every parametrization
  lies in `hullK A` (Lemma S2 reflected, `s2HullRight`);
* `subset_tail_of_hullK`, `lt_length_of_launch`, **`tipSet_subset_physSet_launch`**: hence every point of the walk in
  `D` is on the tail — in particular the `htail` field of `StageGeom` for every launched piece
  (**`tail_of_launch`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw GW1P LuM GW1W GW1Bookkeep

/-- Recentring does not change the image of `ℍ` under the inverse chart. -/
theorem image_H_recenter (c : Chart) (a : ℝ) : (c.recenter a).2.1 '' H = c.2.1 '' H := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w + a, ?_, rfl⟩
    have hw' : (0 : ℝ) < w.im := hw
    show 0 < (w + a).im
    simpa using hw'
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w - a, ?_, ?_⟩
    · have hw' : (0 : ℝ) < w.im := hw
      show 0 < (w - a).im
      simpa using hw'
    · show c.2.1 (w - a + a) = c.2.1 w
      rw [sub_add_cancel]

/-- **Points in `D` are on the tail**: if the head lies in `hullK A` and `D ⊆ ℍ \ fillH A`, every point of the range
of `β₀` in `D` is reached after `t_L`. -/
theorem subset_tail_of_hullK {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} {A : Set ℂ} {c : Chart}
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hD : c.2.1 '' H ⊆ H \ fillH A) {S : Set ℂ} (hS : S ⊆ range β₀) :
    S ∩ c.2.1 '' H ⊆ β₀ '' Ici tL := by
  rintro p ⟨hpS, hpD⟩
  obtain ⟨t, rfl⟩ := hS hpS
  refine ⟨t, mem_Ici.2 ?_, rfl⟩
  by_contra hlt
  push Not at hlt
  exact notMem_hullK_of_mem_D (hD hpD) (hK ⟨t, ⟨zero_le, hlt.le⟩, rfl⟩)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- A launch happens within the program. -/
theorem lt_length_of_launch (spec : ExplSpec) (D : ℕ → Drv) {n : ℕ}
    (hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none) : n < spec.2.2.length := by
  by_contra h
  push Not at h
  apply hl
  rw [Lv.run_eq_of_length_le spec D (by omega : spec.2.2.length ≤ n + 1),
    ← Lv.run_eq_of_length_le spec D (by omega : spec.2.2.length ≤ n)]
  exact launches_run_of_le spec D le_rfl

/-- **A launched piece lies in the walk's physical set.** -/
theorem tipSet_subset_physSet_launch {θ : ℝ} {D : ℕ → Drv} {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 ⊆
      ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D := by
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) _ D hl
  have hmem : newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) ∈
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).1 := by
    rw [GW1W.launch_walk hl, launch_pieces]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  intro z hz
  have h1 : z ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) :=
    Or.inl (Or.inr (Set.mem_biUnion hmem hz))
  exact WalkIntRunChron.prefixPhysSet_mono _ D (by omega : n + 1 ≤ _) h1

/-- **The upper chart's facts at a launch** (almost surely in the retained sample): `c` is conformal, `UpperChartOK c`
and the domain identity `c⁻¹ '' ℍ = ℍ \ fillH A`. -/
theorem sb2LowerUpperChart :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ _ _ E u l k ω₀ c _ _ _ =>
      c.IsConformal ∧ UpperChartOK c ∧ c.2.1 '' H = H \ fillH (upperPrefix κ b jumps E u l k ω₀) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hRu := hER _ hsp
  filter_upwards [hRu, ae_isRightEntryValue_upperEntry hRu k] with ω₀ hR₀ hent₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2) :=
    fun j c' θ' hl' => hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  have hc := (eq_launch_of_launches (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) hlaunch).2.2
  have hF : ω₀ ∈ upperLaunchSet κ b jumps E u l k := mem_upperLaunchSet hlaunch
  have hcc : c.IsConformal := by
    rw [hc]
    exact (GW2aCont.isConformal_runChart (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k
      fun j _ c' θ' hl' => hreg₀ j c' θ' hl').1
  have hcb : HasProperBdryExt c := by
    rw [hc]; exact (isClosed_pieces_run (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) hreg₀ k).1
  obtain ⟨g, hgc, hgi, -, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hrc : IsRightEntryChart (upperPrefix κ b jumps E u l k ω₀)
      (realMax (upperPrefix κ b jumps E u l k ω₀)) (c.recenter (upperEntry κ b jumps E u l k ω₀)) := by
    have hent := hent₀ hF
    rw [upperLaunchChart_eq hlaunch] at hent
    rw [hc]
    refine Lf.isRightEntryChart_runChart _ _ hreg₀ k (stStatus_ne_done_of_launches _ _ hlaunch)
      (isCompact_upperPrefix hreg₀ hF) (Lw.fillH_union_real _ _) ?_
    have hsc : stChart (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) k) = c :=
      hc.symm
    rw [hsc]; exact hent
  refine ⟨hcc, ⟨hcc.1.continuousOn, fun w hw => hcc.2.2 w hw, bdryOff_of_ext hcc hgc hgi hgt⟩, ?_⟩
  rw [← image_H_recenter c (upperEntry κ b jumps E u l k ω₀)]
  exact hrc.1.2.1

/-- **The head lies in the hull of the retained upper history** (Lemma S2 reflected), almost surely under the
retained kernel, for every parametrization of the lower walk and every visit time of `R`. -/
theorem sb2LowerHeadHull :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          ∀ tL : ℝ≥0, β₀ tL = realMax (upperPrefix κ b jumps E u l k ω₀) →
            β₀ '' Icc 0 tL ⊆ hullK (upperPrefix κ b jumps E u l k ω₀) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hEu := hE _ hsp
  have hRu := hER _ hsp
  have hm𝒢 := hEu.2.1 k
  have hleftQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hleft
  have hrunQ := Retain.ae_ae_run_eq (upperSpec u l) hRu hm𝒢 le_rfl
  filter_upwards [hleftQ, hrunQ, hRu] with ω₀ hleft₀ hrun₀ hR₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2) :=
    fun j c' θ' hl' => hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ :=
    Lf.exists_path_upperPrefix (κ := κ) (b := b) (jumps := jumps) hu l (fun j => E (upperSpec u l) j ω₀) hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω₀ := hpA
  filter_upwards [hrun₀, hleft₀] with ω hω hleftω
  intro β₀ hβ hβ0 hβr tL hβL
  have hlaunchω : ω ∈ upperLaunchSet κ b jumps E u l k := by
    show (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none
    rw [launches_run_succ_of_run_eq (upperSpec u l) hω, hlaunch]
    exact Option.some_ne_none _
  have hAω : upperPrefix κ b jumps E u l k ω = upperPrefix κ b jumps E u l k ω₀ := by
    show prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0 =
      prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0
    unfold prefixPhysSet; rw [hω]
  have hav := hleftω hlaunchω
  rw [hAω] at hav
  have hav' : prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∩
      rightSideOf (range β₀) = ∅ := by
    rw [hβr]
    exact eq_empty_of_subset_empty ((inter_subset_inter_left _ subset_union_left).trans hav.subset)
  have hAL : upperPrefix κ b jumps E u l k ω₀ ⊆ closedLeftSide β₀ :=
    Lf.subset_closedLeftSide_of_avoid hβ hβ0 hcl hav'
  rw [← hpA'] at hAL hβL ⊢
  obtain ⟨-, tR, htR, -, hK, -⟩ := s2HullRight hp hp0 hpH hβ hβ0 hAL
  have e : tR = tL := hβ.2.1 (htR.trans hβL.symm)
  subst e
  exact hK

/-- **The tail position of a launched piece's points in `D`** (the `htail` field of `StageGeom`), from the head
inclusion and the domain identity. -/
theorem tail_of_launch {θ : ℝ} {D : ℕ → Drv} {n : ℕ} {c : Chart} {A : Set ℂ} {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hD : c.2.1 '' H = H \ fillH A) :
    (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 ∩ c.2.1 '' H ⊆
      β₀ '' Ici tL :=
  subset_tail_of_hullK hK hD.subset ((tipSet_subset_physSet_launch hl).trans hβr.symm.subset)

end InteractingSLE.Theorem14.SB.Lk
