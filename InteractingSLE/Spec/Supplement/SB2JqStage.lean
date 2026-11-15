/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JqDense

/-!
# SB2(2): the good-time density at the concrete stages after `R` (option-independent part of D6)

Packet PROVE-SB2-LIFTSET (round 15). `hgd_of_launch` (`SB2JqDense`) at the concrete rule's stages that come after the
walk has reached `R` — every relative stage `i ≥ 2` (actual stage `i + relOff`), and stage `0` of a mark entry
(`relOff = startOff + 2`); these are the same under both options of decision D6.

* `statePhysicalSet_subset_physSet`, `exists_mem_statePhysicalSet_succ` (the walk reaches `R` at some stage);
* **`mem_statePhysicalSet_of_stage`**, **`mem_statePhysicalSet_of_mark`**: `R` lies in the launch state's physical
  part at those stages;
* **`hgd_of_launch_R`**: the density at a launch whose state holds `R` (head inside the state by `prefix_facts`);
* **`sb2LowerTailRight`**: almost surely, the tail's points of `ℍ` off `A` are in `D` (Lemma S2 reflected);
* **`sb2LowerStageDensity`**: almost surely under the retained kernel, for every parametrization and every lift curve,
  the good times are dense at every relative stage `i ≥ 2` whose actual stage launches (Theorems 1.2–1.3 for GW1's
  chain facts; **Lemma S3 for the lower pieces**, `SB2LowerNoCommonArcStatement`, as an input).
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

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- A stage's physical part lies in the walk's physical set. -/
theorem statePhysicalSet_subset_physSet {n : ℕ} (hn : n ≤ (boundaryWalkSpec b jumps θ true).2.2.length) :
    statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ⊆
      ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D :=
  WalkIntRunChron.prefixPhysSet_mono (κ := κ) (b := b) (jumps := jumps) (boundaryWalkSpec b jumps θ true) D hn

/-- A stage's physical part grows. -/
theorem statePhysicalSet_mono {n n' : ℕ} (hnn : n ≤ n') :
    statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ⊆
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n') :=
  WalkIntRunChron.prefixPhysSet_mono (κ := κ) (b := b) (jumps := jumps) (boundaryWalkSpec b jumps θ true) D hnn

/-- A point of the walk's physical set is in some stage's physical part. -/
theorem exists_mem_statePhysicalSet_succ {z : ℂ}
    (hz : z ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) :
    ∃ n, z ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) := by
  refine ⟨(boundaryWalkSpec b jumps θ true).2.2.length, ?_⟩
  rw [Lv.run_eq_of_length_le _ D (Nat.le_succ _)]
  exact hz

/-- **`R` is in the launch state's physical part at the relative stages `i ≥ 2`.** -/
theorem mem_statePhysicalSet_of_stage {R : ℝ}
    (hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {i : ℕ} (hi : 2 ≤ i) :
    (R : ℂ) ∈ statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (i + relOff κ θ b jumps R D)) := by
  obtain ⟨hin, -⟩ := entryStage_spec κ θ b jumps (exists_mem_statePhysicalSet_succ hR)
  refine statePhysicalSet_mono ?_ hin
  have h1 : entryStage κ θ b jumps R D ≤ startOff κ θ b jumps R D + 1 := by unfold startOff; omega
  have h2 : startOff κ θ b jumps R D ≤ relOff κ θ b jumps R D := by
    classical
    unfold relOff; split_ifs <;> omega
  omega

/-- **`R` is in the launch state's physical part at stage `0` of a mark entry.** -/
theorem mem_statePhysicalSet_of_mark {R : ℝ}
    (hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hM : MarkEntry κ θ b jumps R D) :
    (R : ℂ) ∈ statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D)) := by
  obtain ⟨hin, -⟩ := entryStage_spec κ θ b jumps (exists_mem_statePhysicalSet_succ hR)
  refine statePhysicalSet_mono ?_ hin
  have := (startOff_eq κ θ b jumps R D).1 hM.1
  rw [relOff_of_mark κ θ b jumps hM]
  omega

/-- **The good-time density at a launch whose state holds `R`.** -/
theorem hgd_of_launch_R (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    {c : Chart} {A : Set ℂ} (hA : IsClosed A) (hDom : c.2.1 '' H = H \ fillH A) {β₀ : ℝ≥0 → ℂ}
    (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0} {R : ℝ}
    (hβL : β₀ tL = R)
    (hR : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hright : ∀ t : ℝ≥0, tL < t → β₀ t ∈ H → β₀ t ∉ A → β₀ t ∈ H \ fillH A)
    (hS3 : ∀ s₁ s₂ : ℝ≥0, s₁ < s₂ → (s₂ : ℝ≥0∞) ≤ (D n).2 →
      ¬ pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) '' Ioo s₁ s₂ ⊆ A) :
    {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) := by
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) _ D hl
  have hsub : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ⊆ range β₀ := by
    rw [hβr]; exact statePhysicalSet_subset_physSet hlen.le
  have hhead := head_subset_of_preconnected hβ hsub (prefix_facts hW.1 hW.2 n).1
    (by rw [hβ0]; exact Or.inl (Or.inl rfl)) (by rw [hβL]; exact hR)
  exact hgd_of_launch hP hW hl hA hDom hβr hhead hright hS3

/-- **The tail's points of `ℍ` off `A` are in `D`** (Lemma S2 reflected), almost surely under the retained kernel. -/
theorem sb2LowerTailRight :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          ∀ tL : ℝ≥0, β₀ tL = realMax (upperPrefix κ b jumps E u l k ω₀) →
            ∀ t : ℝ≥0, tL < t → β₀ t ∈ H → β₀ t ∉ upperPrefix κ b jumps E u l k ω₀ →
              β₀ t ∈ H \ fillH (upperPrefix κ b jumps E u l k ω₀) := by
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
  obtain ⟨-, tR, htR, -, -, -, hright⟩ := s2HullRight hp hp0 hpH hβ hβ0 hAL
  have e : tR = tL := hβ.2.1 (htR.trans hβL.symm)
  subst e
  exact hright

/-- **The good-time density at every relative stage `i ≥ 2`, almost surely** (Theorems 1.2–1.3 for GW1's chain
facts; Lemma S3 for the lower pieces as an input). -/
theorem sb2LowerStageDensity (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hS3 : SB2LowerNoCommonArcStatement.{u}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          ∀ tL : ℝ≥0, β₀ tL = lR κ b jumps E u l k ω₀ →
            ∀ i, 2 ≤ i →
              (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
                  (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none →
              {t : ℝ≥0 | (t : ℝ≥0∞) < (lD₁ b jumps E ω
                  (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2} ⊆
                closure (goodT c (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                  (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
                  (lD₁ b jumps E ω
                    (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))) := by
  have hW := sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hRu := hER _ hsp
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hS3 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerTailRight κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hRLQ, hRu] with ω₀ hW₀ hS₀ hC₀ hT₀ hR₀ hRu₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨-, -, hDom⟩ := hC₀ c θ hlaunch b' J' h' hb' hT' hG'
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2) :=
    fun j c' θ' hl' => hRu₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  have hA : IsClosed (upperPrefix κ b jumps E u l k ω₀) :=
    (isCompact_upperPrefix hreg₀ (mem_upperLaunchSet hlaunch)).isClosed
  filter_upwards [hW₀ c θ hlaunch b' J' h' hb' hT' hG', hS₀ c θ hlaunch b' J' h' hb' hT' hG',
    hT₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀] with ω hWω hSω hTω hRω
  intro β₀ hβ hβ0 hβr tL hβL i hi hl
  have hRmem : ((lR κ b jumps E u l k ω₀ : ℝ) : ℂ) ∈ ExplState.physSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω) := by
    rw [← hβL]; exact (hβr ▸ mem_range_self tL : β₀ tL ∈ lowerWalkSet κ b jumps E ω)
  exact hgd_of_launch_R hRω hWω hl hA hDom hβ hβ0 hβr hβL (mem_statePhysicalSet_of_stage hRmem hi)
    (hTω β₀ hβ hβ0 hβr tL hβL)
    (fun s₁ s₂ h12' h2 => hSω _ hl s₁ s₂ h12' h2)

end InteractingSLE.Theorem14.SB.Lk
