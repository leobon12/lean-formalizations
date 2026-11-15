/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AsmLower
import InteractingSLE.Spec.Supplement.SBS3AsmRoot
import InteractingSLE.Spec.Supplement.SBS3AsmFinal

/-!
# Lemma S3 in SB2(1)'s configuration: `Tc.SB2EntranceNoCommonArcStatement`

Worker PROVE-R6-CORNER (Theorem 1.4, SB2(1), specification pp. 579–580, 632; PROVE-AUX61-NOJUMP's input). R48:
Theorems 1.2 (parametric) and 1.3 are the explicit inputs.

The comparison is made in coordinates shifted by the seed `u`: old history = the retained lower prefix (lower walk
at its launch `k + 1`, plus the real bridge `[u, 0]`; `old_sample_facts_lower`), labels `±λ + (π/2)χ` = the side
heights of the one-step schedule `[(−π/2, 0)]`; second history = the upper flow `η − u`, the first piece of
`(u, true, [(ψ, q₂)])` (`second_sample_facts_root`, exposed value `−λ − ψχ`); union means translated by
`MarkedUnionMeans.image_sub`; S1's witness shifted by `Tc.exists_shifted_witness`. The per-sample comparison is
`exists_protectedWordComparison_upper`, contradicted by `HasJointSideComparison.false` since `ψ > −π/2`.

* `prefixPhysSet_stageOne_root`: the physical set after the first piece from a real root.
* `ae_entrance_rational`, **`ae_entranceNoCommonArc_of_le`**: the conclusion for `ψ ≤ π/2`.
* `SB2EntranceWideAngleStatement` (**named residual input**, angles `ψ > π/2`: the setting's staged histories exist
  only for boundary-continued programs) and `sb2EntranceNoCommonArcStatement_of_wide`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist Exist.Staged Exist.StagedLaw Restart

/-- The physical set after the first piece of `(x, true, [(ϑ, q)])`, stopped at `q` before its lifetime, is the
generated trace translated to the root: `x + β([0, q])`. -/
theorem prefixPhysSet_stageOne_root {κ ϑ x : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {q : ℝ≥0}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDq : (q : ℝ≥0∞) < (D 0).2) {β : ℝ≥0 → ℂ}
    (hβ : IsGeneratingTrace (D 0).1 (q : ℝ≥0∞) β)
    (hDc : ContinuousOn (D 0).1 {s | (s : ℝ≥0∞) ≤ (q : ℝ≥0∞)}) (hD0 : (D 0).1 0 = 0) :
    prefixPhysSet κ b jumps (x, true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) D 1 = (fun t => β t + x) '' Icc 0 q := by
  set spec : ExplSpec := (x, true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) with hspec
  have hl := GW1.launches_run_one_of_cons κ b jumps spec (θ := ϑ) (t := (q : ℝ≥0∞)) (rest := []) rfl D
  obtain ⟨-, he, -⟩ := eq_launch_of_launches spec D hl
  have hmin : min (q : ℝ≥0∞) (D 0).2 = q := min_eq_left hDq.le
  have hpieces : (ExplState.run κ b jumps spec D 1).1 =
      [(Chart.id.recenter x, fun r : ℝ≥0 => (D 0).1 (min (r : ℝ≥0∞) (q : ℝ≥0∞)).toNNReal, (q : ℝ≥0∞))] := by
    rw [he, CounterflowRange.pieces_launch]
    show [] ++ [(Chart.id.recenter x,
      fun r : ℝ≥0 => (D 0).1 (min (r : ℝ≥0∞) (min (q : ℝ≥0∞) (D 0).2)).toNNReal, min (q : ℝ≥0∞) (D 0).2)] = _
    rw [hmin]
    rfl
  have harcs : (ExplState.run κ b jumps spec D 1).2.1 = [] := by
    rw [he, GW2aCont.arcs_launch]
    rfl
  have hid : ∀ w : ℂ, (Chart.id.recenter x).2.1 w = w + x := fun w => by simp [Chart.recenter, Chart.id]
  have hcont : Continuous fun w : ℂ => w + (x : ℂ) := continuous_id.add continuous_const
  have htip : (Chart.id.recenter x).tipSet (fun r : ℝ≥0 => (D 0).1 (min (r : ℝ≥0∞) (q : ℝ≥0∞)).toNNReal)
      (q : ℝ≥0∞) = (fun t => β t + x) '' Icc 0 q := by
    rw [CounterflowRange.tipSet_stopped_eq_of_tendsto (f := fun z => z + (x : ℂ)) hβ hDc hD0
      (fun t _ => ((hcont.tendsto _).mono_left nhdsWithin_le_nhds).congr fun w => (hid w).symm)]
    rw [image_image]
    congr 1
    ext t
    simp only [mem_setOf_eq, mem_Icc, zero_le, true_and, ENNReal.coe_le_coe]
  have h0 : ((x : ℝ) : ℂ) ∈ (fun t => β t + x) '' Icc 0 q := ⟨0, ⟨le_rfl, zero_le⟩, by simp only [hβ.1, zero_add]⟩
  show {((spec.1 : ℝ) : ℂ)} ∪ (⋃ p ∈ (ExplState.run κ b jumps spec D 1).1, p.1.tipSet p.2.1 p.2.2) ∪
    ⋃ a ∈ (ExplState.run κ b jumps spec D 1).2.1, ((↑) : ℝ → ℂ) '' a = _
  rw [hpieces, harcs]
  simp only [List.mem_singleton, List.not_mem_nil, iUnion_iUnion_eq_left, iUnion_of_empty, iUnion_empty,
    union_empty]
  rw [htip]
  exact union_eq_right.2 (singleton_subset_iff.2 h0)

/-- **Lemma S3 in SB2(1)'s configuration at a rational arc** (for `ψ ≤ π/2`). Almost surely at a launch of the lower
walk, no compact rational arc of the recentred upper flow `η − u` after the entrance lies in `(A − u) ∩ ℍ`, `A` the
retained lower prefix. -/
theorem ae_entrance_rational (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : Lv.SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hψ : ψ ≤ Real.pi / 2) (q₁ q₂ : ℚ) :
    ∀ᵐ ω ∂P, ω ∈ Lv.launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) <
        ((q₁ : ℝ).toNNReal : ℝ≥0∞) →
      (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal → ((q₂ : ℝ).toNNReal : ℝ≥0∞) < ζ ω →
      ¬ (fun t => η ω t - u) '' Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆
        (fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω ∩ H := by
  have hκ := HP.kappa_pos
  have hκ4 := HP.kappa_lt_four
  have hb := HP.boundary
  have hh := HP.field
  have hψI : ψ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨HP.angle.le, hψ⟩
  set q₁' : ℝ≥0 := (q₁ : ℝ).toNNReal with hq₁'
  set q₂' : ℝ≥0 := (q₂ : ℝ).toNNReal with hq₂'
  set sw : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hsw
  set s₂ : ExplSpec := (u, true, [Sum.inl (ψ, (q₂' : ℝ≥0∞))]) with hs₂
  set s₃ : ExplSpec := (u, true, [Sum.inl (ψ, (⊤ : ℝ≥0∞))]) with hs₃
  have hbcw : IsBoundaryContinuedProgram sw.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hbc₂ : IsBoundaryContinuedProgram s₂.2.2 := fun θ t hm => by
    have := List.mem_singleton.1 hm
    rw [(Prod.mk.inj (Sum.inl.inj this)).1]
    exact hψI
  have hbc₃ : IsBoundaryContinuedProgram s₃.2.2 := fun θ t hm => by
    have := List.mem_singleton.1 hm
    rw [(Prod.mk.inj (Sum.inl.inj this)).1]
    exact hψI
  have hEw := HP.staged sw hbcw
  have hRw := HP.pieces_regular sw hbcw
  have hE₂ := HP.staged s₂ hbc₂
  have hR₂ := HP.pieces_regular s₂ hbc₂
  have hE₃ := HP.staged s₃ hbc₃
  have hR₃ := HP.pieces_regular s₃ hbc₃
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨A₁, g₁, β₁, Y₁, hA₁m, hA₁c, hA₁eq, hg₁, -, hm₁⟩ :=
    exists_stageMean_interiorStageSides h12p h13 hκ hκ4 hb hh hEw hRw (HP.drivers_regular sw) hu₀ (k + 1)
  obtain ⟨A₂, g₂, β₂, β₀, hA₂m, hA₂c, hA₂eq, hg₂, hm₂⟩ :=
    exists_postMean_stopWord h12p h13 hκ hκ4 hb hh hE₂ hR₂ (HP.drivers_regular s₂) hu₀ 0
  have hU := ae_markedUnionMeans_stages h12p h13 hκ hκ4 hb hh hEw hE₂ hRw hR₂ hu₀ (k + 1) 1 hA₁m hA₂m
    hA₁eq hA₂eq hg₁ hg₂
  have hF₂ := ae_flowLine_eq_firstPiece_root h12p h13 h12p₀ h13₀ hκ hb hh hE₂ hR₂ (rest := []) rfl HP.flow
  have hF₃ := ae_flowLine_eq_firstPiece_root h12p h13 h12p₀ h13₀ hκ hb hh hE₃ hR₃ (rest := []) rfl HP.flow
  have hD₂₃ := ae_firstDriver_eq_root h12p h13 h12p₀ h13₀ hκ hb hh hE₂ hE₃ rfl (rest := []) (rest' := []) rfl rfl
  filter_upwards [hm₁, hg₁.2.1, hg₂.2.1, hm₂, hU, hF₂, hF₃, hD₂₃, hR₃,
    GW1W.regLaunches_of_stagedPiecesRegular hRw, GW1W.regLaunches_of_stagedPiecesRegular hR₂,
    Lv.ae_isPrefixPath_launch HP, HP.one_sided, hA₁eq, hA₂eq] with ω hm₁ω hharm₁ hharm₂ hm₂ω
    hUω hF₂ω hF₃ω hD₂₃ω hR₃ω hregw hreg₂ hpathω hS1ω hA₁ω hA₂ω
  intro hF hτ hq hζ hA
  set A := lowerPrefix κ b jumps E (k + 1) u ω with hAdef
  obtain ⟨p, hp⟩ := hpathω hF
  obtain ⟨hpc, hp0, hpf, hpH, hpA⟩ := hp
  set ηu : ℝ≥0 → ℂ := fun t => η ω t - u with hηu
  -- the recentred flow line is the first piece of both one-instruction programs from `u`
  obtain ⟨hζ₂, hD0, hDc, -⟩ := hF₂ω
  obtain ⟨hζ₃, hW0, hWc, hβtr₃⟩ := hF₃ω
  have hl₃ := GW1.launches_run_one_of_cons κ b jumps s₃ (θ := ψ) (t := ⊤) (rest := []) rfl
    (fun j => E s₃ j ω)
  obtain ⟨-, -, η₃, hη₃, -⟩ := hR₃ω 0 ψ ⊤ _ rfl hl₃
  have hmin3 : min (⊤ : ℝ≥0∞) (E s₃ 0 ω).2 = (E s₃ 0 ω).2 := min_eq_right le_top
  rw [hmin3] at hη₃ hWc hβtr₃
  have hβgen : IsGeneratingTrace (E s₃ 0 ω).1 (ζ ω) ηu := by
    rw [hζ₃]
    exact Restart.isGeneratingTrace_congr_le hη₃ fun t ht => hβtr₃ η₃ hη₃ t ht
  have hWc' : ContinuousOn (E s₃ 0 ω).1 {s | (s : ℝ≥0∞) < ζ ω} :=
    hWc.mono fun s (hs : (s : ℝ≥0∞) < ζ ω) => show (s : ℝ≥0∞) ≤ (E s₃ 0 ω).2 from hζ₃ ▸ hs.le
  have hη0 : η ω 0 = u := sub_eq_zero.1 hβgen.1
  have hinjβ : InjOn ηu {t | (t : ℝ≥0∞) ≤ ζ ω} := by
    intro t₁ ht₁ t₂ ht₂ he
    have hmax : ((max t₁ t₂ : ℝ≥0) : ℝ≥0∞) ≤ ζ ω := by
      rcases le_total t₁ t₂ with h' | h'
      · rw [max_eq_right h']; exact ht₂
      · rw [max_eq_left h']; exact ht₁
    obtain ⟨β'', hc'', -⟩ := hS1ω hF (max t₁ t₂) hmax
    apply hc''.2.1
    have he' : η ω t₁ = η ω t₂ := sub_left_inj.1 he
    rw [hc''.2.2.2.2 t₁ (le_max_left _ _), hc''.2.2.2.2 t₂ (le_max_right _ _), he']
  have hq0 : 0 < q₂' := lt_of_le_of_lt zero_le hq
  have hDq : (q₂' : ℝ≥0∞) < (E s₂ 0 ω).2 := hζ₂ ▸ hζ
  have hDW : ∀ t : ℝ≥0, t ≤ q₂' → (E s₂ 0 ω).1 t = (E s₃ 0 ω).1 t := fun t ht =>
    hD₂₃ω.2 t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hDq)
  -- the second side
  have hl₂ := GW1.launches_run_one_of_cons κ b jumps s₂ (θ := ψ) (t := (q₂' : ℝ≥0∞)) (rest := []) rfl
    (fun j => E s₂ j ω)
  have hfin₂ : min (instrTime s₂ 0) (E s₂ 0 ω).2 ≠ ⊤ :=
    ne_top_of_le_ne_top (show instrTime s₂ 0 ≠ ⊤ from ENNReal.coe_ne_top) (min_le_left _ _)
  obtain ⟨hβ₂s, hmean₂, hid₂, hcid₂⟩ := hm₂ω (by rw [hl₂]; exact Option.some_ne_none _) hfin₂
  obtain ⟨v₁, hv₁, hrep₁⟩ := hharm₁
  obtain ⟨v₂, hv₂, hrep₂⟩ := hharm₂
  obtain ⟨f, Φ, e₂, Jx, hch, hfd, hfinΦ, hDo, hmo₂, hmean₂', hexp⟩ :=
    second_sample_facts_root (x := u) (D := fun j => E s₂ j ω) hreg₂ hβgen hWc' hW0 hinjβ hζ hq0 hDq hDW hDc
      (hmean₂ v₂ hv₂ hrep₂) hid₂ hcid₂
  -- the old side
  obtain ⟨hβ₁s, hside₁, hmean₁⟩ := hm₁ω hF
  obtain ⟨c, g, e₁, word, hc, hgc, hgi, hgf, hgb, hmo₁, hws, hmean₁', hlabel⟩ :=
    old_sample_facts_lower (E := E) (n := k + 1) (u := u) (ω := ω) hregw hF ⟨hpc, hp0, hpf, hpH, hpA⟩ hβ₁s
      (hmean₁ v₁ hv₁ hrep₁) hside₁
  -- shifted prefix
  set A' : Set ℂ := (fun s => p s - u) '' Icc 0 1 with hA'def
  have hp'A : A' = (fun z => z - (u : ℂ)) '' A := by rw [hA'def, ← hpA, image_image]
  have hp'c : ContinuousOn (fun s => p s - (u : ℂ)) (Icc 0 1) := hpc.sub continuousOn_const
  have hp'0 : (fun s => p s - (u : ℂ)) 0 = 0 := by simp [hp0]
  have hp'H : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ ((fun s => p s - (u : ℂ)) s).im := fun s hs => by
    simpa using hpH s hs
  -- the witness in shifted coordinates
  obtain ⟨β', hβ'p, hβ'0, hAside, hag⟩ := Tc.exists_shifted_witness (hS1ω hF q₂' hζ.le) hη0
  have hAside' : A' ⊆ Supp9B.closedRightSide β' := hp'A ▸ hAside
  -- the explored sets in shifted coordinates
  have himgOpen : ∀ S : Set ℂ, IsOpen S → IsOpen ((fun z : ℂ => z - (u : ℂ)) '' S) := fun S hS => by
    have e : (fun z : ℂ => z - (u : ℂ)) = ⇑(Homeomorph.addRight (-(u : ℂ))) := funext fun z => by
      simp [sub_eq_add_neg]
    rw [e]
    exact (Homeomorph.addRight _).isOpenMap _ hS
  set B₁ := (fun z : ℂ => z - (u : ℂ)) '' A₁ ω with hB₁
  set B₂ := (fun z : ℂ => z - (u : ℂ)) '' A₂ ω with hB₂
  have hB₁o : IsOpen (H \ B₁) := by rw [hB₁, diff_H_image_sub]; exact himgOpen _ (hA₁c ω).2
  have hB₂o : IsOpen (H \ B₂) := by rw [hB₂, diff_H_image_sub]; exact himgOpen _ (hA₂c ω).2
  have hstage₁ : ∀ z ∈ A₁ ω, z ∈ A ∩ H := fun z hz => by
    rw [hA₁ω] at hz
    exact ⟨Or.inl (Or.inl (Or.inr hz.1)), hz.2⟩
  have hA'f : B₁ ⊆ fillH A' := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hp'A, fillH_image_sub]
    exact ⟨z, ⟨(hstage₁ z hz).2, Or.inl (subset_closure (hstage₁ z hz).1)⟩, rfl⟩
  have hA'a : A' ∩ H ⊆ B₁ := by
    rintro z ⟨hzA, hzH⟩
    rw [hp'A, mem_image_sub_iff] at hzA
    have hzH' : z + (u : ℂ) ∈ H := (add_real_mem_H_iff' u).2 hzH
    have hzP : z + (u : ℂ) ∈ prefixPhysSet κ b jumps sw (fun j => E sw j ω) (k + 1) := by
      rcases hzA with h1 | ⟨y, -, hy⟩
      · exact h1
      · exact absurd (hy ▸ hzH') (WalkPiece.ofReal_notMem_H y)
    refine mem_image_sub_iff.2 ?_
    rw [hA₁ω]
    exact WalkLeaf.mem_stageSet_of_mem_prefixPhysSet sw (E sw) (k + 1) ω hzP hzH'
  have hβq : IsGeneratingTrace (E s₂ 0 ω).1 (q₂' : ℝ≥0∞) ηu :=
    Restart.StoppedK2.isGeneratingTrace_congr (fun t ht => (hDW t (ENNReal.coe_le_coe.1 ht.le)).symm)
      (BRLeaf.isGeneratingTrace_of_le hβgen hζ.le)
  have hminq : min (q₂' : ℝ≥0∞) (E s₂ 0 ω).2 = q₂' := min_eq_left hDq.le
  have hP₂ : prefixPhysSet κ b jumps s₂ (fun j => E s₂ j ω) 1 = (fun t => ηu t + u) '' Icc 0 q₂' :=
    prefixPhysSet_stageOne_root (D := fun j => E s₂ j ω) hDq hβq (by rw [← hminq]; exact hDc) hD0
  have hB'f : B₂ ⊆ fillH (ηu '' Icc 0 q₂') := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hA₂ω] at hz
    have hzP : z ∈ prefixPhysSet κ b jumps s₂ (fun j => E s₂ j ω) 1 := Or.inl (Or.inr hz.1)
    rw [hP₂] at hzP
    obtain ⟨t, ht, hzt⟩ := hzP
    have hzH := hz.2
    rw [← hzt] at hzH ⊢
    refine ⟨(sub_real_mem_H_iff u).2 hzH, Or.inl (subset_closure ⟨t, ht, ?_⟩)⟩
    simp only [add_sub_cancel_right]
  have hB'a : ηu '' Icc 0 q₂' ∩ H ⊆ B₂ := by
    rintro _ ⟨⟨t, ht, rfl⟩, hH⟩
    refine mem_image_sub_iff.2 ?_
    rw [hA₂ω]
    have hzP : ηu t + u ∈ prefixPhysSet κ b jumps s₂ (fun j => E s₂ j ω) 1 := by
      rw [hP₂]; exact ⟨t, ht, rfl⟩
    exact WalkLeaf.mem_stageSet_of_mem_prefixPhysSet s₂ (E s₂) 1 ω hzP ((add_real_mem_H_iff' u).2 hH)
  -- the protected union means in shifted coordinates
  have hinj : Function.Injective fun z : ℂ => z - (u : ℂ) := sub_left_injective
  have hunion : ∀ x₀ : ℂ, x₀ ∈ B₁ ∪ {z : ℂ | z.im = 0} → x₀ ∈ B₂ ∪ {z : ℂ | z.im = 0} →
      ∀ rA > 0, ∀ rB > 0, MarkedUnionMeans B₁ B₂
        (FinRel.freeNear B₂ B₁ x₀ rA ∩ FinRel.freeNear B₁ B₂ x₀ rB) x₀
        (fun z => v₁ (z + u)) (fun z => v₂ (z + u)) := by
    intro x₀ hx₁ hx₂ rA hrA rB hrB
    have hre : ∀ {S : Set ℂ}, x₀ ∈ (fun z : ℂ => z - (u : ℂ)) '' S ∪ {z : ℂ | z.im = 0} →
        x₀ + (u : ℂ) ∈ S ∪ {z : ℂ | z.im = 0} := fun hx => by
      rcases hx with h' | h'
      · exact Or.inl (mem_image_sub_iff.1 h')
      · right
        show (x₀ + (u : ℂ)).im = 0
        simpa using h'
    have hM := MarkedUnionMeans.image_sub (hUω v₁ v₂ hv₁ hrep₁ hv₂ hrep₂ (x₀ + u) (hre hx₁) (hre hx₂) rA hrA rB hrB) u
    rw [image_inter hinj, image_sub_freeNear, image_sub_freeNear, add_sub_cancel_right] at hM
    exact hM
  -- the visit of `L`
  have hAcpt : IsCompact A := Lx.isCompact_lowerPrefix (u := u) hregw hF
  have huA : ((u : ℝ) : ℂ) ∈ A := hpA ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩
  have hbdd : BddBelow {x : ℝ | (x : ℂ) ∈ A} := by
    obtain ⟨R, hR⟩ := hAcpt.isBounded.subset_closedBall 0
    refine ⟨-R, fun x hx => ?_⟩
    have h1 := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [neg_abs_le x]
  have hmin : realMin A' = realMin A - u := by rw [hp'A]; exact Lw.realMin_image_sub u ⟨u, huA⟩ hbdd
  unfold firstVisit at hτ
  obtain ⟨t₀, ht₀⟩ := iInf_lt_iff.1 hτ
  obtain ⟨⟨-, ht₀eq⟩, ht₀lt⟩ := iInf_lt_iff.1 ht₀
  have ht₀q : t₀ ≤ q₁' := (ENNReal.coe_lt_coe.1 ht₀lt).le
  have ht₀' : β' t₀ = realMin A' := by
    rw [hag t₀ (ht₀q.trans hq.le), ht₀eq, hmin]
    push_cast
    ring
  -- the comparison and its contradiction
  have himg : β' '' Icc 0 q₂' = ηu '' Icc 0 q₂' := image_congr fun s hs => hag s hs.2
  have harc : ηu '' Icc q₁' q₂' ⊆ A' ∩ H := by rw [hp'A]; exact hA
  obtain ⟨d, hd⟩ := exists_protectedWordComparison_upper (ϑ := ψ) (l := [(-(Real.pi / 2), (0 : ℝ≥0))])
    hp'c hp'0 hp'H hβ'p hβ'0 hAside' hc hgc hgi hgf hgb hmo₁ hws hmean₁' hlabel (η := ηu) hag
    (Geo.IsChartCore.congr hch hag) (by rw [himg]; exact hfd) hfinΦ (by rw [himg]; exact hDo) hmo₂ hβ₂s
    hmean₂' hexp hB₁o hB₂o hA'f hB'f hA'a hB'a hunion ht₀' ht₀q hq harc
  refine (d.hasJointSideComparison hd).false hκ hκ4 fun p hp => ?_
  rw [List.mem_singleton] at hp
  rw [hp]
  exact HP.angle

/-- **Lemma S3 in SB2(1)'s configuration** (Theorems 1.2–1.3, R48), for upper flows of angle `ψ ∈ (−π/2, π/2]`:
almost surely at a launch of the lower walk, after the entrance at `L = min (A ∩ ℝ)`, the upper flow shares no open
arc with the retained lower prefix `A` (`SB2EntranceNoCommonArcStatement`'s conclusion). -/
theorem ae_entranceNoCommonArc_of_le (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : Lv.SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hψ : ψ ≤ Real.pi / 2) :
    ∀ᵐ ω ∂P, ω ∈ Lv.launchSet κ b jumps E (k + 1) →
      ∀ s₁ s₂ : ℝ≥0, firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) ≤ s₁ → s₁ < s₂ →
        (s₂ : ℝ≥0∞) ≤ ζ ω → ¬ η ω '' Ioo s₁ s₂ ⊆ lowerPrefix κ b jumps E (k + 1) u ω := by
  have hrat := fun q₁ q₂ => ae_entrance_rational h12p h13 h12p₀ h13₀ HP hψ q₁ q₂
  obtain ⟨_, _, W, _, _, _, -, hcoup, htrace⟩ := HP.flow
  filter_upwards [ae_all_iff.2 fun q₁ => ae_all_iff.2 (hrat q₁), htrace, hcoup.1.2.2.2.2]
    with ω hQ ht hw hF s₁ s₂ hτ hs hsζ hsub
  refine no_common_arc_of_rational_compact (A := (fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)
    ht hw.2.2.2.1 hw.1 (fun q₁ q₂ hτq hqq hqζ hQA => hQ q₁ q₂ hF hτq hqq hqζ hQA) s₁ s₂ hτ hs hsζ ?_
  rintro _ ⟨t, htI, rfl⟩
  exact ⟨η ω t, hsub ⟨t, htI, rfl⟩, rfl⟩

/-- **Named residual input** (not discharged here): SB2(1)'s entrance no-common-arc conclusion for upper flows of
angle `ψ > π/2`. The staged histories of the setting are only available for boundary-continued programs (angles in
`[−π/2, π/2]`), so the second history's actual mean is not constructed for such angles. -/
def SB2EntranceWideAngleStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
    Lv.SB2LaunchProblem κ b jumps P h E k u ψ η ζ → Real.pi / 2 < ψ →
    ∀ᵐ ω ∂P, ω ∈ Lv.launchSet κ b jumps E (k + 1) →
      ∀ s₁ s₂ : ℝ≥0, firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) ≤ s₁ → s₁ < s₂ →
        (s₂ : ℝ≥0∞) ≤ ζ ω → ¬ η ω '' Ioo s₁ s₂ ⊆ lowerPrefix κ b jumps E (k + 1) u ω

/-- **SB2(1)'s form of Lemma S3** (`Tc.SB2EntranceNoCommonArcStatement`) from Theorems 1.2–1.3, PROVED for
`ψ ≤ π/2` (`ae_entranceNoCommonArc_of_le`); the angles `ψ > π/2` are the named residual input. -/
theorem sb2EntranceNoCommonArcStatement_of_wide (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0})
    (hwide : SB2EntranceWideAngleStatement.{u}) : Tc.SB2EntranceNoCommonArcStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP
  rcases le_or_gt ψ (Real.pi / 2) with hψ | hψ
  · exact ae_entranceNoCommonArc_of_le h12p h13 h12p₀ h13₀ HP hψ
  · exact hwide κ b jumps P h E k u ψ η ζ HP hψ

end InteractingSLE.Theorem14.SB.S3.Asm
