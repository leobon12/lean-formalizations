/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvRule

/-!
# Iterated rule-stopped unions and their increasing limit

Packet PROVE-T14-SB2DRV (round 3). A flow line is history-sensitively local with its killing record only in capped
versions (frozen after a deterministic cap `n`, `Restart.exists_capped_version`), while SB2(1)'s entrance time `T_L`
is unbounded. The entrance σ-algebra is therefore built from the capped versions `η_n`, `n ∈ ℕ`, each stopped at the
same parameterized rule, by iterating the union step of `SB2DrvRule` and passing to the increasing union:

* `iterSet A η Y S n = A ∪ η_0([0, S(Y, η_0)]) ∪ ⋯ ∪ η_n([0, S(Y, η_n)])` and its marks `iterMarks 𝒢 η ζ Y S n`
  (`𝒢` and the killed histories of `η_0, …, η_n` through their rules);
* **`mem_complSigma_iterSet`**: every iterated union satisfies the union step's conclusion;
* **`mem_complSigma_iUnion`** (generic): increasing unions of sets with increasing marks keep it, for the marks
  `⨆ n`; **`mem_complSigma_limSet`** for the limit `⋃ n, iterSet … n`;
* `isHistoryAvoidanceLocal_limSet`, `measurableSet_disjoint_limSet`, `limMarks_le_aeSigma`, `limMarks_le`: the limit is
  a history-marked local set, its avoidance events are (a.s.) marks, its marks are a.s. events of the field and
  measurable events.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.SB.Lv

open LocalSets Sec6 Restart

/-! ### Increasing unions -/

section Limit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Increasing unions with increasing marks.** If the sets `C n` increase, their marks `M n` increase, and each
`(C n, M n)` has its marked avoidance events almost surely in the complementary projection, so does
`(⋃ n, C n, ⨆ n, M n)`. -/
theorem mem_complSigma_iUnion {C : ℕ → Ω → Set ℂ} {M : ℕ → MeasurableSpace Ω}
    (hCm : ∀ ω, Monotone fun n => C n ω) (hM : Monotone M)
    {U : Opens ℂ} {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hC : ∀ n F, MeasurableSet[M n] F →
      MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (C n ω) U} ∩ F))
    (F : Set Ω) (hF : MeasurableSet[⨆ n, M n] F) :
    MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (⋃ n, C n ω) U} ∩ F) := by
  have hE : {ω | Disjoint (⋃ n, C n ω) U} = ⋂ n, {ω | Disjoint (C n ω) U} := by
    ext ω
    simp only [mem_ofPred_eq, disjoint_iUnion_left, mem_iInter]
  have hE𝒦 : MeasurableSet[WalkLaw.complSigma P G h] (⋂ n, {ω | Disjoint (C n ω) U}) := by
    refine MeasurableSet.iInter fun n => ?_
    have h1 := hC n univ (@MeasurableSet.univ _ (M n))
    rwa [inter_univ] at h1
  rw [hE]
  have hle : (⨆ n, M n) ≤ WalkLaw.traceSigma (WalkLaw.complSigma P G h) _ hE𝒦 := by
    refine iSup_le fun m F₁ hF₁ => ?_
    change MeasurableSet[WalkLaw.complSigma P G h] ((⋂ n, {ω | Disjoint (C n ω) U}) ∩ F₁)
    have e : (⋂ n, {ω | Disjoint (C n ω) U}) ∩ F₁ = ⋂ n, ({ω | Disjoint (C (n + m) ω) U} ∩ F₁) := by
      ext ω
      simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩ n
        exact ⟨h1 (n + m), h2⟩
      · intro h1
        refine ⟨fun n => ?_, (h1 0).2⟩
        exact Set.disjoint_of_subset_left (hCm ω (Nat.le_add_right n m)) (h1 n).1
    rw [e]
    exact MeasurableSet.iInter fun n => hC (n + m) F₁ (hM (Nat.le_add_left m n) _ hF₁)
  exact hle F hF

end Limit

/-! ### Iterated unions -/

section Iter

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}
  {η : ℕ → Ω → ℝ≥0 → ℂ} {ζ : ℕ → Ω → ℝ≥0∞} {𝒴 : Type*} [MeasurableSpace 𝒴] {Y : Ω → 𝒴}
  {S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- The iterated rule-stopped union `A ∪ η_0([0, τ_0]) ∪ ⋯ ∪ η_n([0, τ_n])`, `τ_j = S(Y, η_j)`. -/
def iterSet (A : Ω → Set ℂ) (η : ℕ → Ω → ℝ≥0 → ℂ) (Y : Ω → 𝒴) (S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞) :
    ℕ → Ω → Set ℂ
  | 0 => fun ω => A ω ∪ rangeUpTo (η 0 ω) (S (Y ω) (pathCoord (η 0 ω)))
  | n + 1 => fun ω => iterSet A η Y S n ω ∪ rangeUpTo (η (n + 1) ω) (S (Y ω) (pathCoord (η (n + 1) ω)))

/-- The marks of the iterated union. -/
@[instance_reducible]
def iterMarks (𝒢 : MeasurableSpace Ω) (η : ℕ → Ω → ℝ≥0 → ℂ) (ζ : ℕ → Ω → ℝ≥0∞) (Y : Ω → 𝒴)
    (S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞) : ℕ → MeasurableSpace Ω
  | 0 => ruleMarks 𝒢 (η 0) (ζ 0) Y S
  | n + 1 => ruleMarks (iterMarks 𝒢 η ζ Y S n) (η (n + 1)) (ζ (n + 1)) Y S

omit mΩ [MeasurableSpace 𝒴] in
theorem iterSet_mono (ω : Ω) : Monotone fun n => iterSet A η Y S n ω :=
  monotone_nat_of_le_succ fun _ => subset_union_left

omit mΩ [MeasurableSpace 𝒴] in
theorem iterMarks_mono : Monotone (iterMarks 𝒢 η ζ Y S) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

omit mΩ [MeasurableSpace 𝒴] in
theorem le_iterMarks (n : ℕ) : 𝒢 ≤ iterMarks 𝒢 η ζ Y S n := by
  induction n with
  | zero => exact le_sup_left
  | succ n ih => exact ih.trans le_sup_left

/-- The paths' standing hypotheses (each capped path is continuous, measurable, field-determined, history-sensitively
local at first entrance times with its killing record, and starts on the real line). -/
structure IterPaths (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω) (η : ℕ → Ω → ℝ≥0 → ℂ)
    (ζ : ℕ → Ω → ℝ≥0∞) : Prop where
  cont : ∀ n ω, Continuous (η n ω)
  meas : ∀ n t, Measurable fun ω => η n ω t
  life_meas : ∀ n, Measurable (ζ n)
  det : ∀ n (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
    (fun ω => η n ω t) =ᵐ[P] fun ω => f (h ω)
  life_det : ∀ n, ∃ f : DistOn upperHalfPlaneOpens → ℝ≥0∞, Measurable f ∧ ζ n =ᵐ[P] fun ω => f (h ω)
  loc : ∀ n, IsEntranceKilledHistoryLocal (η n) (ζ n) h P
  start : ∀ n ω, η n ω 0 ∉ H

/-- **Every iterated union satisfies the union step's conclusion.** -/
theorem mem_complSigma_iterSet (hhm : Measurable h)
    (hA : ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ F : Set Ω, MeasurableSet[𝒢] F →
        MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (A ω) U} ∩ F))
    (hη : IterPaths h P η ζ) (hY : Measurable[𝒢] Y) (hSm : Measurable (Function.uncurry S))
    (hSg : IsParamGalmarino S) (n : ℕ) (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (F : Set Ω) (hF : MeasurableSet[iterMarks 𝒢 η ζ Y S n] F) :
    MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (iterSet A η Y S n ω) U} ∩ F) := by
  induction n generalizing U G F with
  | zero =>
    exact mem_complSigma_union_rule hhm hA (hη.cont 0) (hη.meas 0) (hη.life_meas 0) (hη.det 0) (hη.life_det 0)
      (hη.loc 0) (hη.start 0) hY hSm hSg U G hUH hG hd F hF
  | succ n ih =>
    exact mem_complSigma_union_rule (𝒢 := iterMarks 𝒢 η ζ Y S n) (A := iterSet A η Y S n) hhm
      (fun U' G' hUH' hG' hd' F' hF' => ih U' G' hUH' hG' hd' F' hF')
      (hη.cont (n + 1)) (hη.meas (n + 1)) (hη.life_meas (n + 1)) (hη.det (n + 1)) (hη.life_det (n + 1))
      (hη.loc (n + 1)) (hη.start (n + 1)) (hY.mono (le_iterMarks n) le_rfl) hSm hSg U G hUH hG hd F hF

/-- The limit of the iterated unions. -/
def limSet (A : Ω → Set ℂ) (η : ℕ → Ω → ℝ≥0 → ℂ) (Y : Ω → 𝒴) (S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞) (ω : Ω) : Set ℂ :=
  ⋃ n, iterSet A η Y S n ω

/-- The marks of the limit. -/
@[instance_reducible]
def limMarks (𝒢 : MeasurableSpace Ω) (η : ℕ → Ω → ℝ≥0 → ℂ) (ζ : ℕ → Ω → ℝ≥0∞) (Y : Ω → 𝒴)
    (S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞) : MeasurableSpace Ω :=
  ⨆ n, iterMarks 𝒢 η ζ Y S n

omit mΩ [MeasurableSpace 𝒴] in
theorem le_limMarks : 𝒢 ≤ limMarks 𝒢 η ζ Y S :=
  (le_iterMarks 0).trans (le_iSup (iterMarks 𝒢 η ζ Y S) 0)

/-- **The limit satisfies the union step's conclusion** for the joined marks of all capped paths. -/
theorem mem_complSigma_limSet (hhm : Measurable h)
    (hA : ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ F : Set Ω, MeasurableSet[𝒢] F →
        MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (A ω) U} ∩ F))
    (hη : IterPaths h P η ζ) (hY : Measurable[𝒢] Y) (hSm : Measurable (Function.uncurry S))
    (hSg : IsParamGalmarino S) (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (F : Set Ω) (hF : MeasurableSet[limMarks 𝒢 η ζ Y S] F) :
    MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (limSet A η Y S ω) U} ∩ F) :=
  mem_complSigma_iUnion iterSet_mono iterMarks_mono
    (fun n F' hF' => mem_complSigma_iterSet hhm hA hη hY hSm hSg n U G hUH hG hd F' hF') F hF

/-- **The limit is a history-marked local set** for the joined marks. -/
theorem isHistoryAvoidanceLocal_limSet (hhm : Measurable h)
    (hA : ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ F : Set Ω, MeasurableSet[𝒢] F →
        MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (A ω) U} ∩ F))
    (hη : IterPaths h P η ζ) (hY : Measurable[𝒢] Y) (hSm : Measurable (Function.uncurry S))
    (hSg : IsParamGalmarino S) :
    WholeField.IsHistoryAvoidanceLocal (limMarks 𝒢 η ζ Y S) (limSet A η Y S) h P :=
  WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF =>
    mem_complSigma_limSet hhm hA hη hY hSm hSg U G hUH hG hd F hF

omit [IsProbabilityMeasure P] [MeasurableSpace 𝒴] in
/-- **The limit's avoidance events are (almost surely) marks.** -/
theorem measurableSet_disjoint_limSet (hc : ∀ n ω, Continuous (η n ω)) (h0 : ∀ n ω, η n ω 0 ∉ H)
    {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) (hev : MeasurableSet[aeSigma 𝒢 P] {ω | Disjoint (A ω) U}) :
    MeasurableSet[aeSigma (limMarks 𝒢 η ζ Y S) P] {ω | Disjoint (limSet A η Y S ω) U} := by
  have hn : ∀ n, MeasurableSet[aeSigma (iterMarks 𝒢 η ζ Y S n) P] {ω | Disjoint (iterSet A η Y S n ω) U} := by
    intro n
    induction n with
    | zero => exact measurableSet_disjoint_union_rule (hc 0) (h0 0) hUH hev
    | succ n ih => exact measurableSet_disjoint_union_rule (hc (n + 1)) (h0 (n + 1)) hUH ih
  have e : {ω | Disjoint (limSet A η Y S ω) U} = ⋂ n, {ω | Disjoint (iterSet A η Y S n ω) U} := by
    ext ω
    simp only [limSet, mem_ofPred_eq, disjoint_iUnion_left, mem_iInter]
  rw [e]
  exact MeasurableSet.iInter fun n => WalkLaw.aeSigma_mono (le_iSup (iterMarks 𝒢 η ζ Y S) n) _ (hn n)

omit [IsProbabilityMeasure P] in
/-- **The joined marks are almost surely events of the field.** -/
theorem limMarks_le_aeSigma (h𝒢 : 𝒢 ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hη : IterPaths h P η ζ) (hY : Measurable[𝒢] Y) (hSm : Measurable (Function.uncurry S)) :
    limMarks 𝒢 η ζ Y S ≤ aeSigma (MeasurableSpace.comap h inferInstance) P := by
  refine iSup_le fun n => ?_
  induction n with
  | zero => exact ruleMarks_le_aeSigma h𝒢 (hη.det 0) (hη.life_det 0) hY hSm
  | succ n ih =>
    exact ruleMarks_le_aeSigma ih (hη.det (n + 1)) (hη.life_det (n + 1)) (hY.mono (le_iterMarks n) le_rfl) hSm

omit [IsProbabilityMeasure P] in
/-- The joined marks are measurable events. -/
theorem limMarks_le (h𝒢 : 𝒢 ≤ mΩ) (hη : IterPaths h P η ζ) (hY : Measurable[𝒢] Y)
    (hSm : Measurable (Function.uncurry S)) : limMarks 𝒢 η ζ Y S ≤ mΩ := by
  have hrule : ∀ n, Measurable (ruleHist (η n) (ζ n) Y S) := by
    intro n
    have hcm : Measurable fun ω => pathCoord (η n ω) := Measurable.of_eval fun q => hη.meas n q
    have hτ : Measurable fun ω => S (Y ω) (pathCoord (η n ω)) := hSm.comp ((hY.mono h𝒢 le_rfl).prodMk hcm)
    exact (measurable_histOf.comp (hτ.prodMk hcm)).prodMk (measurable_lifeRec.comp ((hη.life_meas n).prodMk hτ))
  refine iSup_le fun n => ?_
  induction n with
  | zero => exact sup_le h𝒢 (hrule 0).comap_le
  | succ n ih => exact sup_le ih (hrule (n + 1)).comap_le

end Iter

end InteractingSLE.Theorem14.SB.Lv
