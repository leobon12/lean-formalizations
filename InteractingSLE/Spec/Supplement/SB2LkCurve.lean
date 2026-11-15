/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkFF
import InteractingSLE.Spec.Supplement.SB2LkEx

/-!
# SB2(2): the actual lower tail has a proper lift (the deterministic half of the erasure)

Packet PROVE-T14-SB2LIFT, step (i) of the packet's split ("the deterministic lift of the walk tail"). SB2(2)'s
erasure identity (`Lk.SB2LowerTailLiftExStatement`) asks for a regular staged lower walk `EL` of the conditional field
and, for every proper parametrization `β₀` of the actual lower walk, a lift of `β₀`'s tail after `R` with range `EL`'s
walk. Here the lift curve itself is constructed, conditionally almost surely, for every `β₀`:

* `IsTailLiftCurve`, `isTailLiftOf_iff`: the lift datum of `Lf.IsTailLiftOf` without the identification of its range;
* **`exists_tailLiftCurve`** (deterministic): Lemma S2 reflected (`s2HullRight`, `s2LiftRight`) in the recentred launch
  chart, whose boundary map has finite fibres;
* `ae_upperPrefix_subset_closedLeftSide`: conditionally almost surely the retained upper history is on the closed left
  of every proper parametrization of the lower walk (the setting's avoidance, transported to the retained kernel);
* **`ae_exists_tailLiftCurve`**: at almost every later launch, conditionally almost surely, every proper parametrization
  of the actual lower walk has a lift curve (the launch chart's boundary map has finite fibres:
  `finite_fibre_schedule`, with the injective traces `ae_injLaunches`, Aux. lemma 25 and Theorem 1.3).

What remains of SB2(2) is the identification of the range of the lift with the walk of a regular staged lower walk of
the conditional field (`SB2LowerTailLiftExStatement` with `isTailLiftOf_iff`).
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

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw GW1P

/-! ### The lift curve -/

/-- **A lift curve of the tail of `β₀` after `R`**, read in the chart `c` recentred at its entry value `−m`. -/
def IsTailLiftCurve (c : Chart) (R m : ℝ) (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (γ : ℝ≥0 → ℂ) : Prop :=
  β₀ tL = (R : ℂ) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s : ℝ≥0, Tendsto c.2.1 (𝓝[H] (γ s - m)) (𝓝 (β₀ (tL + s)))

/-- `Lf.IsTailLiftOf` is a lift curve with the given range. -/
theorem isTailLiftOf_iff {c : Chart} {R m : ℝ} {β₀ : ℝ≥0 → ℂ} {W : Set ℂ} :
    Lf.IsTailLiftOf c R m β₀ W ↔ ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c R m β₀ tL γ ∧ range γ = W := by
  constructor
  · rintro ⟨tL, γ, h1, h2, h3, h4, h5⟩
    exact ⟨tL, γ, ⟨h1, h2, h3, h5⟩, h4⟩
  · rintro ⟨tL, γ, ⟨h1, h2, h3, h5⟩, h4⟩
    exact ⟨tL, γ, h1, h2, h3, h4, h5⟩

/-- **The lift curve exists** (Lemma S2 reflected): for a path image `A` from `0` on the closed left of a proper curve
`β₀` from `0`, and a chart `c` whose recentring at `−m` is a right entry chart of `A` at `R = max (A ∩ ℝ)` and whose
inverse has a continuous finite-fibre extension `g` to `ℍ̄`, the tail of `β₀` after its visit to `R` has a lift
curve. -/
theorem exists_tailLiftCurve {pA : ℝ → ℂ} (hp : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hA : pA '' Icc 0 1 ⊆ closedLeftSide β₀) {c : Chart} {m : ℝ}
    (hrc : IsRightEntryChart (pA '' Icc 0 1) (realMax (pA '' Icc 0 1)) (c.recenter (-m))) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgt : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (g q))) (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) :
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (pA '' Icc 0 1)) m β₀ tL γ := by
  obtain ⟨-, tR, htR, -, -, -, -⟩ := s2HullRight hp hp0 hpH hβ hβ0 hA
  set g' : ℂ → ℂ := fun w => g (w + ((-m : ℝ) : ℂ)) with hg'
  have hsh : ∀ w : ℂ, 0 ≤ w.im → 0 ≤ (w + ((-m : ℝ) : ℂ)).im := fun w hw => by simpa using hw
  have hg'c : ContinuousOn g' {z | 0 ≤ z.im} :=
    hgc.comp (continuous_id.add continuous_const).continuousOn fun w (hw : 0 ≤ w.im) => hsh w hw
  have hg'i : EqOn g' (c.recenter (-m)).2.1 H := fun w hw => by
    show g (w + ((-m : ℝ) : ℂ)) = c.2.1 (w + ((-m : ℝ) : ℂ))
    exact hgi ((Lw.add_real_mem_H_iff (-m)).2 hw)
  have hg'f : ∀ z, (g' ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite := fun z => by
    refine ((hgf z).image fun w => w - ((-m : ℝ) : ℂ)).subset fun w hw => ?_
    refine ⟨w + ((-m : ℝ) : ℂ), ⟨hw.1, hsh w hw.2⟩, ?_⟩
    simp only [add_sub_cancel_right]
  obtain ⟨γ, hγ, hγ0, hγg⟩ := s2LiftRight hp hp0 hpH hβ hβ0 hA hrc hg'c hg'i hg'f htR
  refine ⟨tR, γ, htR, hγ, hγ0, fun s => ?_⟩
  have hq : γ s - m ∈ Hbar := by
    show 0 ≤ (γ s - m).im
    simpa using hγ.2.2.1 s
  have h1 := hgt _ hq
  have h2 : g (γ s - m) = β₀ (tR + s) := by
    have := hγg s
    simp only [hg', Complex.ofReal_neg, ← sub_eq_add_neg] at this
    exact this
  rwa [h2] at h1

/-! ### The lift curve under the retained kernel -/

/-- **SB2(2)'s lift curve exists** (the deterministic half of the erasure, conditionally almost surely): at almost
every launch of the upper schedule and for every witness of the conditional launch law, with `m = −e_R`, almost surely
under the retained kernel every proper parametrization `β₀` of the actual lower walk from `0` has a lift curve of its
tail after `R` in the launch chart recentred at `−m`. -/
theorem sb2LowerTailLiftCurve (h13 : Exist.Theorem13Statement.{u}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c _ _ _ =>
      ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀ tL γ := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hEu := hE _ hsp
  have hRu := hER _ hsp
  have hm𝒢 := hEu.2.1 k
  have hleftQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hleft
  have hrunQ := Retain.ae_ae_run_eq (upperSpec u l) hRu hm𝒢 le_rfl
  filter_upwards [hleftQ, hrunQ, hRu, ae_injLaunches h13 hκ hκ4 hb hEu hRu,
    ae_isRightEntryValue_upperEntry hRu k] with ω₀ hleft₀ hrun₀ hR₀ hinj₀ hent₀
  intro c θ hlaunch b' J' h' hb' hT' hG' m hm
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2) :=
    fun j c' θ' hl' => hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ :=
    Lf.exists_path_upperPrefix (κ := κ) (b := b) (jumps := jumps) hu l (fun j => E (upperSpec u l) j ω₀) hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω₀ := hpA
  have hc := (eq_launch_of_launches (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) hlaunch).2.2
  have hF : ω₀ ∈ upperLaunchSet κ b jumps E u l k := mem_upperLaunchSet hlaunch
  have hcc : c.IsConformal := by
    rw [hc]
    exact (GW2aCont.isConformal_runChart (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k
      fun j _ c' θ' hl' => hreg₀ j c' θ' hl').1
  have hcb : HasProperBdryExt c := by
    rw [hc]; exact (isClosed_pieces_run (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) hreg₀ k).1
  obtain ⟨g, hgc, hgi, hgb, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hgf := finite_fibre_schedule hu l (fun j => E (upperSpec u l) j ω₀) hreg₀ hinj₀ hlaunch hgc hgi hgb
  have hrc : IsRightEntryChart (upperPrefix κ b jumps E u l k ω₀)
      (realMax (upperPrefix κ b jumps E u l k ω₀)) (c.recenter (-m)) := by
    have hent := hent₀ hF
    rw [upperLaunchChart_eq hlaunch] at hent
    rw [hm, neg_neg, hc]
    refine Lf.isRightEntryChart_runChart _ _ hreg₀ k (stStatus_ne_done_of_launches _ _ hlaunch)
      (isCompact_upperPrefix hreg₀ hF) (Lw.fillH_union_real _ _) ?_
    have hsc : stChart (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) k) = c :=
      hc.symm
    rw [hsc]; exact hent
  filter_upwards [hrun₀, hleft₀] with ω hω hleftω
  intro β₀ hβ hβ0 hβr
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
  rw [← hpA'] at hAL hrc ⊢
  exact exists_tailLiftCurve hp hp0 hpH hβ hβ0 hAL hrc hgc hgi hgt hgf

end InteractingSLE.Theorem14.SB.Lk
