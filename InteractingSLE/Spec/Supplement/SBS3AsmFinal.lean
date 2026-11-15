/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AsmPost
import InteractingSLE.Spec.Supplement.SBS3AsmOld
import InteractingSLE.Spec.Supplement.SBS3AsmChart
import InteractingSLE.Spec.Supplement.SBS3AssemblyUpper
import InteractingSLE.Spec.Supplement.SBS3TerminalUnion
import InteractingSLE.Spec.Supplement.SBS3RetainedSchedule
import InteractingSLE.Spec.Supplement.GW2Sched
import InteractingSLE.Spec.Supplement.GW2aContArc
import InteractingSLE.Spec.Supplement.SB2WdInd
import InteractingSLE.Spec.Supplement.WalkLeafChart
import InteractingSLE.Spec.Restart.FlowCodeMain
import InteractingSLE.Impl.PiecewiseConstant

/-!
# Lemma S3 (upper): the protected comparison from Theorems 1.2–1.3, hence `S3RegStatement`

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification pp. 579–580). R48: Theorems 1.2 (parametric) and 1.3
are the explicit inputs; nothing here uses Theorem 1.4.

* `ae_firstDriver_eq`: the first pieces of two staged programs from `0` with the same first angle have the same
  driver and lifetime (Theorem 1.2's determination).
* `prefixPhysSet_stageOne`: the physical set after the first piece of `(0, true, [(ϑ, q)])` is `β([0, q])`.
* `schedulePrefix_nil`: the empty schedule's prefix is the root.
* **`rationalProtectedWordStatement_of_thm12_thm13`**: PROVE-T14-S3's named input `RationalProtectedWordStatement`
  is PROVED. Old side: the schedule's run chart recentred at its left entry value with the retained mean and word
  (`exists_scheduleRetainedMean_reg`, `old_sample_facts`). Second side: the program `(0, true, [(ϑ, q₂)])`, whose
  first piece is the flow line (`ae_flowLine_eq_firstPiece`; the program `(0, true, [(ϑ, ⊤)])` supplies the driver
  beyond `q₂`), with the post-stop mean and the explicit stop word (`exists_postMean_stopWord_reg`,
  `second_sample_facts`). Union means: `ae_markedUnionMeans_stages`. Witness: S1 at `q₂`. Visit time: the first
  visit of `L`. Per-sample comparison: `exists_protectedWordComparison_upper`.
* **`s3RegStatement_of_thm12_thm13`**: `S3RegStatement` (via `s3RegStatement_of_protectedWord`).
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

/-- **The first pieces of two staged programs from `0` with the same first angle have the same driver** on their
common lifetime (Theorem 1.2's determination, `Lk.ae_eq_of_isFlowLineDriver`). -/
theorem ae_firstDriver_eq (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) {κ ϑ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {spec spec' : ExplSpec} {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) (hE' : IsStagedHistory κ b jumps P h spec' E')
    (hroot : spec.1 = 0) (hroot' : spec'.1 = 0) {τ τ' : ℝ≥0∞} {rest rest' : List Instr}
    (hp : spec.2.2 = Sum.inl (ϑ, τ) :: rest) (hp' : spec'.2.2 = Sum.inl (ϑ, τ') :: rest') :
    ∀ᵐ ω ∂P, (E 0 ω).2 = (E' 0 ω).2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E 0 ω).2 → (E 0 ω).1 t = (E' 0 ω).1 t :=
  SB.Lk.ae_eq_of_isFlowLineDriver h12p h13 h12p₀ h13₀ hκ hb hb
    (hE.isFlowLineDriver_first hκ hb hh hroot hp) (hE'.isFlowLineDriver_first hκ hb hh hroot' hp')

/-- The physical set after the first piece of `(0, true, [(ϑ, q)])`, stopped at `q` before its lifetime, is the
generated trace `β([0, q])`. -/
theorem prefixPhysSet_stageOne {κ ϑ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {q : ℝ≥0}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDq : (q : ℝ≥0∞) < (D 0).2) {β : ℝ≥0 → ℂ}
    (hβ : IsGeneratingTrace (D 0).1 (q : ℝ≥0∞) β)
    (hDc : ContinuousOn (D 0).1 {s | (s : ℝ≥0∞) ≤ (q : ℝ≥0∞)}) (hD0 : (D 0).1 0 = 0) :
    prefixPhysSet κ b jumps ((0 : ℝ), true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) D 1 = β '' Icc 0 q := by
  set spec : ExplSpec := ((0 : ℝ), true, [Sum.inl (ϑ, (q : ℝ≥0∞))]) with hspec
  have hl := GW1.launches_run_one_of_cons κ b jumps spec (θ := ϑ) (t := (q : ℝ≥0∞)) (rest := []) rfl D
  obtain ⟨-, he, -⟩ := eq_launch_of_launches spec D hl
  have hmin : min (q : ℝ≥0∞) (D 0).2 = q := min_eq_left hDq.le
  have hpieces : (ExplState.run κ b jumps spec D 1).1 =
      [(Chart.id.recenter 0, fun r : ℝ≥0 => (D 0).1 (min (r : ℝ≥0∞) (q : ℝ≥0∞)).toNNReal, (q : ℝ≥0∞))] := by
    rw [he, CounterflowRange.pieces_launch]
    show [] ++ [(Chart.id.recenter 0,
      fun r : ℝ≥0 => (D 0).1 (min (r : ℝ≥0∞) (min (q : ℝ≥0∞) (D 0).2)).toNNReal, min (q : ℝ≥0∞) (D 0).2)] = _
    rw [hmin]
    rfl
  have harcs : (ExplState.run κ b jumps spec D 1).2.1 = [] := by
    rw [he, GW2aCont.arcs_launch]
    rfl
  have hid : ∀ w : ℂ, (Chart.id.recenter 0).2.1 w = w := fun w => by simp [Chart.recenter, Chart.id]
  have htip : (Chart.id.recenter 0).tipSet (fun r : ℝ≥0 => (D 0).1 (min (r : ℝ≥0∞) (q : ℝ≥0∞)).toNNReal)
      (q : ℝ≥0∞) = β '' Icc 0 q := by
    rw [CounterflowRange.tipSet_stopped_eq_of_tendsto (f := fun z => z) hβ hDc hD0
      (fun t _ => (tendsto_id.mono_left nhdsWithin_le_nhds).congr fun w => (hid w).symm)]
    rw [image_id']
    congr 1
    ext t
    simp only [mem_setOf_eq, mem_Icc, zero_le, true_and, ENNReal.coe_le_coe]
  have h0 : (0 : ℂ) ∈ β '' Icc 0 q := ⟨0, ⟨le_rfl, zero_le⟩, hβ.1⟩
  show {((spec.1 : ℝ) : ℂ)} ∪ (⋃ p ∈ (ExplState.run κ b jumps spec D 1).1, p.1.tipSet p.2.1 p.2.2) ∪
    ⋃ a ∈ (ExplState.run κ b jumps spec D 1).2.1, ((↑) : ℝ → ℂ) '' a = _
  rw [hpieces, harcs]
  simp only [List.mem_singleton, List.not_mem_nil, iUnion_iUnion_eq_left, iUnion_of_empty, iUnion_empty,
    union_empty]
  rw [htip]
  simp only [hspec, Complex.ofReal_zero]
  exact union_eq_right.2 (singleton_subset_iff.2 h0)

/-- With an empty schedule the prefix is the root. -/
theorem schedulePrefix_nil {Ω : Type u} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω : Ω) :
    schedulePrefix κ b jumps E [] k ω = {0} := by
  have hrun : ∀ n, ExplState.run κ b jumps ((0 : ℝ), true, scheduleProgram 0 [])
      (fun j => E ((0 : ℝ), true, scheduleProgram 0 []) j ω) n = ExplState.init 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [run_succ]
      exact ih
  show {(((0 : ℝ)) : ℂ)} ∪ (⋃ p ∈ (ExplState.run κ b jumps ((0 : ℝ), true, scheduleProgram 0 [])
      (fun j => E ((0 : ℝ), true, scheduleProgram 0 []) j ω) k).1, p.1.tipSet p.2.1 p.2.2) ∪
    ⋃ a ∈ (ExplState.run κ b jumps ((0 : ℝ), true, scheduleProgram 0 [])
      (fun j => E ((0 : ℝ), true, scheduleProgram 0 []) j ω) k).2.1, ((↑) : ℝ → ℂ) '' a = _
  rw [hrun k]
  ext z
  simp [ExplState.init]

/-- **`RationalProtectedWordStatement` from Theorems 1.2–1.3** (R48), i.e. the upper half of Lemma S3's protected
comparison. At a rational common arc of the flow line `β` with the schedule prefix `A`: the old side is the run chart
of the schedule recentred at its left entry value, with PROVE-T14-S3's retained mean and word
(`exists_scheduleRetainedMean_reg`, `old_sample_facts`); the second side is the one-piece program
`(0, true, [(ϑ, q₂)])`, whose first piece is the flow line (`ae_flowLine_eq_firstPiece`, with the whole-life
program `(0, true, [(ϑ, ⊤)])` for the driver beyond `q₂`), with the post-stop mean and explicit stop word
(`exists_postMean_stopWord_reg`, `second_sample_facts`); the two explored sets carry the protected union means
(`ae_markedUnionMeans_stages`); the witness is S1's at `q₂`; the visit time is the first visit of `L`. The per-sample
comparison is `exists_protectedWordComparison_upper`. -/
theorem rationalProtectedWordStatement_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) :
    RationalProtectedWordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR l k ϑ hl hθ hϑ β ζ hβ hS1 q₁ q₂
  -- the empty schedule: the prefix is the root, the arc condition fails
  by_cases hl0 : l = []
  · subst hl0
    refine Eventually.of_forall fun ω _ _ hq _ hA => ?_
    exfalso
    have hmem := hA ⟨(q₁ : ℝ).toNNReal, ⟨le_rfl, hq.le⟩, rfl⟩
    rw [schedulePrefix_nil] at hmem
    have h0 := hmem.2
    rw [mem_singleton_iff.1 hmem.1] at h0
    exact WalkPiece.ofReal_notMem_H 0 (by rw [Complex.ofReal_zero]; exact h0)
  obtain ⟨p₀, hp₀⟩ := List.exists_mem_of_ne_nil l hl0
  have hϑI : ϑ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨(hθ p₀ hp₀).1.1.trans (hθ p₀ hp₀).2.le, hϑ⟩
  set q₁' : ℝ≥0 := (q₁ : ℝ).toNNReal with hq₁'
  set q₂' : ℝ≥0 := (q₂ : ℝ).toNNReal with hq₂'
  -- the three programs
  set s₁ : ExplSpec := Lf.sspec 0 l with hs₁
  set s₂ : ExplSpec := ((0 : ℝ), true, [Sum.inl (ϑ, (q₂' : ℝ≥0∞))]) with hs₂
  set s₃ : ExplSpec := ((0 : ℝ), true, [Sum.inl (ϑ, (⊤ : ℝ≥0∞))]) with hs₃
  have hbc₁ : IsBoundaryContinuedProgram s₁.2.2 :=
    GW2Sched.isBoundaryContinuedProgram_scheduleProgram (fun p hp => (hθ p hp).1) 0
  have hbc₂ : IsBoundaryContinuedProgram s₂.2.2 := fun θ t hm => by
    have := List.mem_singleton.1 hm
    rw [(Prod.mk.inj (Sum.inl.inj this)).1]
    exact hϑI
  have hbc₃ : IsBoundaryContinuedProgram s₃.2.2 := fun θ t hm => by
    have := List.mem_singleton.1 hm
    rw [(Prod.mk.inj (Sum.inl.inj this)).1]
    exact hϑI
  have hE₁ := hE s₁ hbc₁
  have hR₁ := hR s₁ hbc₁
  have hE₂ := hE s₂ hbc₂
  have hR₂ := hR s₂ hbc₂
  have hE₃ := hE s₃ hbc₃
  have hR₃ := hR s₃ hbc₃
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  -- the old side: retained mean and word of the schedule prefix
  obtain ⟨A₁, g₁, β₁, Y₁, hA₁m, hA₁c, hA₁eq, hg₁, hW₁, hm₁⟩ :=
    exists_scheduleRetainedMean_reg h12p h13 hκ hκ4 hb hh hE₁ hR₁ hu₀ k
  -- the second side: post-stop mean and explicit stop word of the first piece
  obtain ⟨A₂, g₂, β₂, β₀, hA₂m, hA₂c, hA₂eq, hg₂, hm₂⟩ :=
    exists_postMean_stopWord_reg h12p h13 hκ hκ4 hb hh hE₂ hR₂ hu₀ 0
  have hU := ae_markedUnionMeans_stages h12p h13 hκ hκ4 hb hh hE₁ hE₂ hR₁ hR₂ hu₀ k 1 hA₁m hA₂m hA₁eq hA₂eq
    hg₁ hg₂
  have hF₂ := ae_flowLine_eq_firstPiece h12p h13 h12p₀ h13₀ hκ hb hh hE₂ hR₂ rfl (rest := []) rfl hβ
  have hF₃ := ae_flowLine_eq_firstPiece h12p h13 h12p₀ h13₀ hκ hb hh hE₃ hR₃ rfl (rest := []) rfl hβ
  have hD₂₃ := ae_firstDriver_eq h12p h13 h12p₀ h13₀ hκ hb hh hE₂ hE₃ rfl rfl (rest := []) (rest' := []) rfl rfl
  filter_upwards [hW₁.sorted, hW₁.sides, hm₁, hg₁.2.1, hg₂.2.1, hm₂, hU, hF₂, hF₃, hD₂₃, hR₃,
    GW1W.regLaunches_of_stagedPiecesRegular hR₁, GW1W.regLaunches_of_stagedPiecesRegular hR₂,
    SB.Lk.ae_injLaunches h13 hκ hκ4 hb hE₁ hR₁, hS1, hA₁eq, hA₂eq] with ω hβ₁s hside₁ hm₁ω hharm₁ hharm₂ hm₂ω
    hUω hF₂ω hF₃ω hD₂₃ω hR₃ω hreg₁ hreg₂ hinj₁ hS1ω hA₁ω hA₂ω
  intro hpath hτ hq hζ hA
  obtain ⟨p, hpc, hp0, hpH, hpeq⟩ := hpath
  -- the S1 witness at `q₂`
  obtain ⟨β', hβ'c, hAside⟩ := hS1ω q₂' hζ.le
  have hβ'p : Supp9B.IsProperCurve β' := Supp9B.isProperCurve_of_isProperCompletion hβ'c
  have hag : ∀ s ≤ q₂', β' s = β ω s := hβ'c.2.2.2.2
  -- the flow line is the first piece of both one-instruction programs
  obtain ⟨hζ₂, hD0, hDc, -⟩ := hF₂ω
  obtain ⟨hζ₃, hW0, hWc, hβtr₃⟩ := hF₃ω
  have hl₃ := GW1.launches_run_one_of_cons κ b jumps s₃ (θ := ϑ) (t := ⊤) (rest := []) rfl
    (fun j => E s₃ j ω)
  obtain ⟨-, -, η₃, hη₃, -⟩ := hR₃ω 0 ϑ ⊤ _ rfl hl₃
  have hmin3 : min (⊤ : ℝ≥0∞) (E s₃ 0 ω).2 = (E s₃ 0 ω).2 := min_eq_right le_top
  rw [hmin3] at hη₃ hWc hβtr₃
  have hβgen : IsGeneratingTrace (E s₃ 0 ω).1 (ζ ω) (β ω) := by
    rw [hζ₃]
    exact Restart.isGeneratingTrace_congr_le hη₃ fun t ht => hβtr₃ η₃ hη₃ t ht
  have hWc' : ContinuousOn (E s₃ 0 ω).1 {s | (s : ℝ≥0∞) < ζ ω} :=
    hWc.mono fun s (hs : (s : ℝ≥0∞) < ζ ω) => show (s : ℝ≥0∞) ≤ (E s₃ 0 ω).2 from hζ₃ ▸ hs.le
  have hinjβ : InjOn (β ω) {t | (t : ℝ≥0∞) ≤ ζ ω} := by
    intro t₁ ht₁ t₂ ht₂ he
    have hmax : ((max t₁ t₂ : ℝ≥0) : ℝ≥0∞) ≤ ζ ω := by
      rcases le_total t₁ t₂ with h' | h'
      · rw [max_eq_right h']; exact ht₂
      · rw [max_eq_left h']; exact ht₁
    obtain ⟨β'', hc'', -⟩ := hS1ω (max t₁ t₂) hmax
    apply hc''.2.1
    rw [hc''.2.2.2.2 t₁ (le_max_left _ _), hc''.2.2.2.2 t₂ (le_max_right _ _), he]
  have hq0 : 0 < q₂' := lt_of_le_of_lt zero_le hq
  have hDq : (q₂' : ℝ≥0∞) < (E s₂ 0 ω).2 := hζ₂ ▸ hζ
  have hDW : ∀ t : ℝ≥0, t ≤ q₂' → (E s₂ 0 ω).1 t = (E s₃ 0 ω).1 t := fun t ht =>
    hD₂₃ω.2 t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hDq)
  -- the second side
  have hl₂ := GW1.launches_run_one_of_cons κ b jumps s₂ (θ := ϑ) (t := (q₂' : ℝ≥0∞)) (rest := []) rfl
    (fun j => E s₂ j ω)
  have hfin₂ : min (instrTime s₂ 0) (E s₂ 0 ω).2 ≠ ⊤ :=
    ne_top_of_le_ne_top (show instrTime s₂ 0 ≠ ⊤ from ENNReal.coe_ne_top) (min_le_left _ _)
  obtain ⟨hβ₂s, hmean₂, hid₂, hcid₂⟩ := hm₂ω (by rw [hl₂]; exact Option.some_ne_none _) hfin₂
  obtain ⟨v₁, hv₁, hrep₁⟩ := hharm₁
  obtain ⟨v₂, hv₂, hrep₂⟩ := hharm₂
  obtain ⟨f, Φ, e₂, Jx, hch, hfd, hfinΦ, hDo, hmo₂, hmean₂', hexp⟩ :=
    second_sample_facts (D := fun j => E s₂ j ω) hreg₂ hβgen hWc' hW0 hinjβ hζ hq0 hDq hDW hDc
      (hmean₂ v₂ hv₂ hrep₂) hid₂ hcid₂
  -- the old side
  have hpA : p '' Icc 0 1 = prefixPhysSet κ b jumps (Lf.sspec 0 l) (fun j => E s₁ j ω) k := hpeq.symm
  obtain ⟨c, g, e₁, word, hc, hgc, hgi, hgf, hgb, hmo₁, hws, hmean₁, hlabel⟩ :=
    old_sample_facts l (fun j => E s₁ j ω) hreg₁ hinj₁ k hpc hp0 hpA hβ₁s (hm₁ω v₁ hv₁ hrep₁) hside₁
  -- the physical set of the second piece
  have hβq : IsGeneratingTrace (E s₂ 0 ω).1 (q₂' : ℝ≥0∞) (β ω) :=
    Restart.StoppedK2.isGeneratingTrace_congr
      (fun t ht => (hDW t (ENNReal.coe_le_coe.1 ht.le)).symm) (BRLeaf.isGeneratingTrace_of_le hβgen hζ.le)
  have hminq : min (q₂' : ℝ≥0∞) (E s₂ 0 ω).2 = q₂' := min_eq_left hDq.le
  have hP₂ : prefixPhysSet κ b jumps s₂ (fun j => E s₂ j ω) 1 = β ω '' Icc 0 q₂' :=
    prefixPhysSet_stageOne (D := fun j => E s₂ j ω) hDq hβq (by rw [← hminq]; exact hDc) hD0
  -- the explored sets
  have hA'f : A₁ ω ⊆ fillH (p '' Icc 0 1) := by
    intro z hz
    rw [hA₁ω] at hz
    have hzA : z ∈ p '' Icc 0 1 := by rw [hpA]; exact Or.inl (Or.inr hz.1)
    exact ⟨hz.2, Or.inl (subset_closure hzA)⟩
  have hA'a : p '' Icc 0 1 ∩ H ⊆ A₁ ω := by
    rintro z ⟨hzA, hzH⟩
    rw [hA₁ω]
    rw [hpA] at hzA
    exact WalkLeaf.mem_stageSet_of_mem_prefixPhysSet s₁ (E s₁) k ω hzA hzH
  have hB'f : A₂ ω ⊆ fillH (β ω '' Icc 0 q₂') := by
    intro z hz
    rw [hA₂ω] at hz
    have hzP : z ∈ prefixPhysSet κ b jumps s₂ (fun j => E s₂ j ω) 1 := Or.inl (Or.inr hz.1)
    rw [hP₂] at hzP
    exact ⟨hz.2, Or.inl (subset_closure hzP)⟩
  have hB'a : β ω '' Icc 0 q₂' ∩ H ⊆ A₂ ω := by
    rintro z ⟨hzA, hzH⟩
    rw [hA₂ω]
    rw [← hP₂] at hzA
    exact WalkLeaf.mem_stageSet_of_mem_prefixPhysSet s₂ (E s₂) 1 ω hzA hzH
  -- the first visit of `L`
  unfold firstVisit at hτ
  obtain ⟨t₀, ht₀⟩ := iInf_lt_iff.1 hτ
  obtain ⟨⟨-, ht₀eq⟩, ht₀lt⟩ := iInf_lt_iff.1 ht₀
  have ht₀q : t₀ ≤ q₁' := (ENNReal.coe_lt_coe.1 ht₀lt).le
  have ht₀' : β' t₀ = realMin (p '' Icc 0 1) := by
    rw [hag t₀ (ht₀q.trans hq.le), ht₀eq, hpeq]
  -- assembly
  have himg : β' '' Icc 0 q₂' = β ω '' Icc 0 q₂' := image_congr fun s hs => hag s hs.2
  have hAside' : p '' Icc 0 1 ⊆ Supp9B.closedRightSide β' := hpeq ▸ hAside
  have harc : β ω '' Icc q₁' q₂' ⊆ p '' Icc 0 1 ∩ H := hpeq ▸ hA
  obtain ⟨d, hd⟩ := exists_protectedWordComparison_upper (ϑ := ϑ) (l := l) hpc hp0 hpH hβ'p
    (by rw [hag 0 zero_le]; exact hβgen.1) hAside' hc hgc hgi hgf hgb hmo₁ hws hmean₁ hlabel hag
    (Geo.IsChartCore.congr hch hag) (by rw [himg]; exact hfd) hfinΦ (by rw [himg]; exact hDo) hmo₂ hβ₂s
    hmean₂' hexp (hA₁c ω).2 (hA₂c ω).2 hA'f hB'f hA'a hB'a
    (fun x₀ hx₁ hx₂ rA hrA rB hrB => hUω v₁ v₂ hv₁ hrep₁ hv₂ hrep₂ x₀ hx₁ hx₂ rA hrA rB hrB) ht₀' ht₀q hq
    harc
  rw [hpeq]
  exact ⟨d, hd⟩

/-- **Lemma S3 (upper, regular histories) from Theorems 1.2–1.3** (R48): T14-S3's provider
`s3RegStatement_of_protectedWord` applied to `rationalProtectedWordStatement_of_thm12_thm13`. -/
theorem s3RegStatement_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Theorem13Statement.{0}) : S3RegStatement.{u} :=
  s3RegStatement_of_protectedWord (rationalProtectedWordStatement_of_thm12_thm13 h12p h13 h12p₀ h13₀)

end InteractingSLE.Theorem14.SB.S3.Asm
