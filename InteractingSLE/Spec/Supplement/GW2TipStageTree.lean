/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB9Cap
import InteractingSLE.Spec.Supplement.GW2TipCanonSkel

/-!
# The alternating stages along an adaptive tree of histories (GB9, p. 526; follow-up note A.5)

Packet PROVE-T14-TIP11. In GW2's exhaustion (follow-up note A.5, `source/external/AstraIG1/ig1_followup_a_e_audited.txt`
L222–L241; GB9, `source/spec/p481-528.md` L1082–L1100, p. 526) every stage chooses its angle, buffer and switching
time from the revealed history ("The selected rule is an own stopping rule", A.2; "Every successful finite history uses
only `Θ` and `Q`", A.5). The revealed history at the start of stage `j` is therefore one of countably many fixed
finite histories (a node of a tree), and the information at that stage start is a σ-algebra **of that node**: the
stage-start information is not one fixed filtration but a tree of them. This file proves the two iterations of A.5 in
that adaptive form:

* "Conditional union bounds give probability at least `1 − ε` of perpetual success"
  (`measure_diff_iInter_reachedAt_le`);
* "iterating this conditional bound shows that the probability of success through stage `2n` and increments less than
  one at all even stages `2m, …, 2n` is at most `(1 − p₀)^{n−m+1}`. Let `n → ∞`, then take the union over `m`. On
  perpetual success infinitely many increments are at least one" (`measure_reachedAt_diff_le`).

Setting: a countable node type `N` with a depth and a parent map (depth of the parent `+ 1` = depth); the event `R n`
that node `n` is reached (contained in its parent's, disjoint from the other nodes of the same depth), measurable for
the node's σ-algebra `𝓕 n` (increasing along the tree); the unit event `U c` of the stage ending at `c`. The one-stage
bounds are assumed **only on the reached node** (`B ⊆ R n`, `B ∈ 𝓕 n`), as the kernels of a stage provide them. The
stage σ-algebra at depth `j` (`stageSigma`) consists of the events whose trace on every reached node of depth `j` is in
that node's σ-algebra; it increases with `j`, and PROVE-T14-TIP6's conditional geometric estimate
(`Supp8.GB9Cap.measure_liminf_eq_zero`) applies to it.

The statements are generic (no SLE content); they serve every alternating construction of this type (GW2, CS3,
Proposition 5.9).

## Main results

* `stageSigma`, `stageSigma_le`, `monotone_stageSigma`;
* `measure_diff_reachedAt_succ_le`: one stage on the stage σ-algebra;
* **`measure_diff_iInter_reachedAt_le`**: `P(reached at 0, not perpetually reached) ≤ Σ εⱼ`;
* **`measure_reachedAt_diff_le`**: `P(reached at 0, not (perpetually reached with infinitely many units)) ≤ Σ εⱼ`;
* `StageSystem`, `StageSystem.IsValid`: a tree of histories with these bounds, an almost-sure initial cover of an event
  `G`, and a capacity along the tree that grows by one on every unit stage and is bounded by `2r²` whenever a target
  set `S ω` lies in the ball of radius `r` ("A bounded relative trace range would bound its filled hull in a rectangle,
  and hence bound its half-plane capacity", A.5);
* **`ae_not_isBounded_of_stageSystems`**: if such systems exist for every tolerance, `S ω` is almost surely unbounded on
  `G` ("Its conditional probability is at least `1 − ε`; let `ε ↓ 0`", A.5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2TipStage

section Tree

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : Type*}

/-- The event that some node of depth `j` is reached. -/
def reachedAt (depth : N → ℕ) (R : N → Set Ω) (j : ℕ) : Set Ω := ⋃ n, ⋃ (_ : depth n = j), R n

/-- The event that some node of depth `j + 1` is reached with its unit event (the stage from depth `j` consumed a
unit). -/
def unitAt (depth : N → ℕ) (R U : N → Set Ω) (j : ℕ) : Set Ω := ⋃ c, ⋃ (_ : depth c = j + 1), (R c ∩ U c)

/-- **The stage σ-algebra at depth `j`**: the events whose trace on every node `n` of depth `j` is `𝓕 n`-measurable. -/
@[instance_reducible]
def stageSigma (depth : N → ℕ) (𝓕 : N → MeasurableSpace Ω) (R : N → Set Ω)
    (hR : ∀ n, MeasurableSet[𝓕 n] (R n)) (j : ℕ) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[mΩ] A ∧ ∀ n, depth n = j → MeasurableSet[𝓕 n] (A ∩ R n)
  measurableSet_empty := ⟨MeasurableSet.empty, fun n _ => by
    rw [Set.empty_inter]; exact @MeasurableSet.empty Ω (𝓕 n)⟩
  measurableSet_compl A hA := by
    obtain ⟨h1, h2⟩ := hA
    refine ⟨h1.compl, fun n hn => ?_⟩
    have e : Aᶜ ∩ R n = R n \ (A ∩ R n) := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [e]
    exact (hR n).diff (h2 n hn)
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun n hn => by
    rw [Set.iUnion_inter]; exact MeasurableSet.iUnion fun i => (hf i).2 n hn⟩

variable {depth : N → ℕ} {par : N → N} {𝓕 : N → MeasurableSpace Ω} {R U : N → Set Ω}

theorem measurableSet_stageSigma_iff {hR : ∀ n, MeasurableSet[𝓕 n] (R n)} {j : ℕ} {A : Set Ω} :
    MeasurableSet[stageSigma depth 𝓕 R hR j] A ↔
      MeasurableSet[mΩ] A ∧ ∀ n, depth n = j → MeasurableSet[𝓕 n] (A ∩ R n) := Iff.rfl

theorem stageSigma_le (hR : ∀ n, MeasurableSet[𝓕 n] (R n)) (j : ℕ) : stageSigma depth 𝓕 R hR j ≤ mΩ :=
  fun _ hA => hA.1

/-- The stage σ-algebras increase along the tree. -/
theorem monotone_stageSigma (hpar : ∀ c, 0 < depth c → depth (par c) + 1 = depth c)
    (h𝓕par : ∀ c, 0 < depth c → 𝓕 (par c) ≤ 𝓕 c) (hR : ∀ n, MeasurableSet[𝓕 n] (R n))
    (hRpar : ∀ c, 0 < depth c → R c ⊆ R (par c)) : Monotone (stageSigma depth 𝓕 R hR) := by
  refine monotone_nat_of_le_succ fun j A hA => ⟨hA.1, fun c hc => ?_⟩
  have hc0 : 0 < depth c := by omega
  have hp : depth (par c) = j := by have := hpar c hc0; omega
  have e : A ∩ R c = (A ∩ R (par c)) ∩ R c := by
    rw [inter_assoc, inter_eq_right.2 (hRpar c hc0)]
  rw [e]
  exact (h𝓕par c hc0 _ (hA.2 _ hp)).inter (hR c)

omit mΩ in
/-- The reached sets decrease along the depth. -/
theorem reachedAt_succ_subset (hpar : ∀ c, 0 < depth c → depth (par c) + 1 = depth c)
    (hRpar : ∀ c, 0 < depth c → R c ⊆ R (par c)) (j : ℕ) :
    reachedAt depth R (j + 1) ⊆ reachedAt depth R j := by
  intro ω hω
  simp only [reachedAt, mem_iUnion] at hω ⊢
  obtain ⟨c, hc, hωc⟩ := hω
  have hc0 : 0 < depth c := by omega
  exact ⟨par c, by have := hpar c hc0; omega, hRpar c hc0 hωc⟩

theorem measurableSet_reachedAt [Countable N] (h𝓕 : ∀ n, 𝓕 n ≤ mΩ) (hR : ∀ n, MeasurableSet[𝓕 n] (R n))
    (j : ℕ) :
    MeasurableSet[stageSigma depth 𝓕 R hR j] (reachedAt depth R j) := by
  refine ⟨MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => h𝓕 n _ (hR n), fun n hn => ?_⟩
  have e : reachedAt depth R j ∩ R n = R n := by
    refine inter_eq_right.2 fun ω hω => ?_
    simp only [reachedAt, mem_iUnion]
    exact ⟨n, hn, hω⟩
  rw [e]
  exact hR n

/-- **A sum over the reached nodes of depth `j`**: if each reached node `n` of depth `j` contributes at most
`a * P (A ∩ R n)` to a set `S ⊆ A ∩ reachedAt j`, then `P S ≤ a * P A`. -/
theorem measure_le_mul_of_nodes [Countable N] {P : Measure Ω} (h𝓕 : ∀ n, 𝓕 n ≤ mΩ)
    (hR : ∀ n, MeasurableSet[𝓕 n] (R n)) (hdisj : ∀ n n', depth n = depth n' → n ≠ n' → Disjoint (R n) (R n'))
    {j : ℕ} {A S : Set Ω} (hA : MeasurableSet A) (hS : S ⊆ reachedAt depth R j) (a : ℝ≥0∞)
    (hnode : ∀ n, depth n = j → P (S ∩ R n) ≤ a * P (A ∩ R n)) : P S ≤ a * P A := by
  have hSU : S = ⋃ n, ⋃ (_ : depth n = j), S ∩ R n := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro hω
      have := hS hω
      simp only [reachedAt, mem_iUnion] at this
      obtain ⟨n, hn, hωn⟩ := this
      exact ⟨n, hn, hω, hωn⟩
    · rintro ⟨n, -, hω, -⟩
      exact hω
  have hdis : Pairwise (Function.onFun Disjoint fun n => ⋃ (_ : depth n = j), A ∩ R n) := by
    intro n n' hnn'
    simp only [Function.onFun]
    by_cases hn : depth n = j
    · by_cases hn' : depth n' = j
      · simp only [hn, hn', iUnion_true]
        exact (hdisj n n' (hn.trans hn'.symm) hnn').mono inter_subset_right inter_subset_right
      · simp only [hn', iUnion_false]; exact disjoint_empty _
    · simp only [hn, iUnion_false]; exact empty_disjoint _
  have hmeas : ∀ n, MeasurableSet (⋃ (_ : depth n = j), A ∩ R n) := fun n =>
    MeasurableSet.iUnion fun _ => hA.inter (h𝓕 n _ (hR n))
  calc P S = P (⋃ n, ⋃ (_ : depth n = j), S ∩ R n) := by rw [← hSU]
    _ ≤ ∑' n, P (⋃ (_ : depth n = j), S ∩ R n) := measure_iUnion_le _
    _ ≤ ∑' n, a * P (⋃ (_ : depth n = j), A ∩ R n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        by_cases hn : depth n = j
        · simp only [hn, iUnion_true]
          exact hnode n hn
        · simp only [hn, iUnion_false, measure_empty]; positivity
    _ = a * P (⋃ n, ⋃ (_ : depth n = j), A ∩ R n) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdis hmeas]
    _ ≤ a * P A := by
        gcongr
        exact iUnion_subset fun n => iUnion_subset fun _ => inter_subset_left

/-- **One stage on the stage σ-algebra** ("Conditional union bounds", A.5): the node bounds give
`P(A \ reachedAt (j + 1)) ≤ εⱼ P(A)` for every stage-`j` event `A` contained in `reachedAt j`. -/
theorem measure_diff_reachedAt_succ_le [Countable N] {P : Measure Ω} (h𝓕 : ∀ n, 𝓕 n ≤ mΩ)
    (hR : ∀ n, MeasurableSet[𝓕 n] (R n)) (hdisj : ∀ n n', depth n = depth n' → n ≠ n' → Disjoint (R n) (R n'))
    (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ n B, MeasurableSet[𝓕 n] B → B ⊆ R n → P (B \ reachedAt depth R (depth n + 1)) ≤ ε (depth n) * P B)
    {j : ℕ} {A : Set Ω} (hA : MeasurableSet[stageSigma depth 𝓕 R hR j] A) (hAR : A ⊆ reachedAt depth R j) :
    P (A \ reachedAt depth R (j + 1)) ≤ ε j * P A := by
  refine measure_le_mul_of_nodes h𝓕 hR hdisj hA.1 (sdiff_subset.trans hAR) (ε j) fun n hn => ?_
  have e : (A \ reachedAt depth R (j + 1)) ∩ R n = (A ∩ R n) \ reachedAt depth R (depth n + 1) := by
    rw [hn]; ext ω; simp only [mem_inter_iff, Set.mem_sdiff]; tauto
  rw [e, ← hn]
  exact hstep n _ (hA.2 n hn) inter_subset_right

/-- **Perpetual success up to `Σ εⱼ`** (A.5: "Conditional union bounds give probability at least `1 − ε` of perpetual
success"; GB9, p. 526: "Take `ε_j = ε 2^{−j}`, so all stages succeed with conditional probability at least
`1 − ε`"): the probability that a node of depth `0` is reached but not a node of every depth is at most `Σ εⱼ`. -/
theorem measure_diff_iInter_reachedAt_le [Countable N] {P : Measure Ω} [IsFiniteMeasure P]
    (h𝓕 : ∀ n, 𝓕 n ≤ mΩ) (hR : ∀ n, MeasurableSet[𝓕 n] (R n))
    (hdisj : ∀ n n', depth n = depth n' → n ≠ n' → Disjoint (R n) (R n')) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ n B, MeasurableSet[𝓕 n] B → B ⊆ R n → P (B \ reachedAt depth R (depth n + 1)) ≤ ε (depth n) * P B) :
    P (reachedAt depth R 0 \ ⋂ j, reachedAt depth R j) ≤ (∑' j, ε j) * P univ := by
  have hsub : reachedAt depth R 0 \ ⋂ j, reachedAt depth R j ⊆
      ⋃ j, (reachedAt depth R j \ reachedAt depth R (j + 1)) := by
    intro ω ⟨h0, hn⟩
    simp only [mem_iInter, not_forall] at hn
    have hex : ∃ m, ω ∉ reachedAt depth R m := hn
    classical
    have hspec := Nat.find_spec hex
    have hmin : ∀ k < Nat.find hex, ω ∈ reachedAt depth R k := fun k hk => by
      by_contra h
      exact Nat.find_min hex hk h
    have hm0 : Nat.find hex ≠ 0 := fun h => hspec (by rw [h]; exact h0)
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hm0
    rw [hj] at hspec hmin
    exact mem_iUnion.2 ⟨j, hmin j (Nat.lt_succ_self j), hspec⟩
  calc P (reachedAt depth R 0 \ ⋂ j, reachedAt depth R j)
      ≤ P (⋃ j, (reachedAt depth R j \ reachedAt depth R (j + 1))) := measure_mono hsub
    _ ≤ ∑' j, P (reachedAt depth R j \ reachedAt depth R (j + 1)) := measure_iUnion_le _
    _ ≤ ∑' j, ε j * P univ := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        calc P (reachedAt depth R j \ reachedAt depth R (j + 1))
            ≤ ε j * P (reachedAt depth R j) :=
              measure_diff_reachedAt_succ_le h𝓕 hR hdisj ε hstep (measurableSet_reachedAt h𝓕 hR j) subset_rfl
          _ ≤ ε j * P univ := by gcongr; exact subset_univ _
    _ = (∑' j, ε j) * P univ := ENNReal.tsum_mul_right

/-- **Perpetual success with infinitely many unit stages, up to `Σ εⱼ`** (A.5: "every reached even stage `j ≥ 4` has
conditional probability at least `p₀` to abort or consume at least one unit of relative capacity … iterating this
conditional bound … Let `n → ∞`, then take the union over `m`. On perpetual success infinitely many increments are at
least one"). Node bounds: every reached node `n` of depth `j` reaches a child with conditional probability at least
`1 − εⱼ` (`hstep`); every reached node of depth `2k + 4` reaches a child **without** its unit event with conditional
probability at most `1 − p₀` (`hunit`). Then, except on a set of probability at most `Σ εⱼ`, a node of depth `0` reached
means a node of every depth reached, and infinitely many stages from the even depths `2k + 4` with their unit events. -/
theorem measure_reachedAt_diff_le [Countable N] {P : Measure Ω} [IsProbabilityMeasure P]
    (hpar : ∀ c, 0 < depth c → depth (par c) + 1 = depth c) (h𝓕 : ∀ n, 𝓕 n ≤ mΩ)
    (h𝓕par : ∀ c, 0 < depth c → 𝓕 (par c) ≤ 𝓕 c) (hR : ∀ n, MeasurableSet[𝓕 n] (R n))
    (hRpar : ∀ c, 0 < depth c → R c ⊆ R (par c))
    (hdisj : ∀ n n', depth n = depth n' → n ≠ n' → Disjoint (R n) (R n')) (hU : ∀ c, MeasurableSet[𝓕 c] (U c))
    (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ n B, MeasurableSet[𝓕 n] B → B ⊆ R n → P (B \ reachedAt depth R (depth n + 1)) ≤ ε (depth n) * P B)
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hunit : ∀ (k : ℕ) n B, depth n = 2 * k + 4 → MeasurableSet[𝓕 n] B → B ⊆ R n →
      P (B ∩ (reachedAt depth R (depth n + 1) \ unitAt depth R U (depth n))) ≤ ENNReal.ofReal (1 - p₀) * P B) :
    P (reachedAt depth R 0 \ {ω | (∀ j, ω ∈ reachedAt depth R j) ∧
        ∃ᶠ k in atTop, ω ∈ unitAt depth R U (2 * k + 4)}) ≤ ∑' j, ε j := by
  -- the failures of the unit test at the even stages
  set F : ℕ → Set Ω := fun k => reachedAt depth R (2 * k + 5) \ unitAt depth R U (2 * k + 4) with hFdef
  set 𝓖 : ℕ → MeasurableSpace Ω := fun k => stageSigma depth 𝓕 R hR (2 * k + 4) with h𝓖
  have hmono := monotone_stageSigma hpar h𝓕par hR hRpar
  have h𝓖m : Monotone 𝓖 := fun k k' h => hmono (by omega)
  have hFm : ∀ k, MeasurableSet[𝓖 (k + 1)] (F k) := by
    intro k
    refine hmono (show 2 * k + 5 ≤ 2 * (k + 1) + 4 by omega) _ ⟨?_, fun c hc => ?_⟩
    · refine (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => h𝓕 n _ (hR n)).diff
        (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => (h𝓕 n _ (hR n)).inter (h𝓕 n _ (hU n)))
    · have e : F k ∩ R c = R c \ U c := by
        ext ω
        simp only [hFdef, reachedAt, unitAt, mem_inter_iff, Set.mem_sdiff, mem_iUnion, exists_prop, not_exists,
          not_and]
        constructor
        · rintro ⟨⟨-, hu⟩, hωc⟩
          exact ⟨hωc, fun hωU => hu c (by omega) hωc hωU⟩
        · rintro ⟨hωc, hωU⟩
          refine ⟨⟨⟨c, hc, hωc⟩, fun c' hc' hωc' hωU' => ?_⟩, hωc⟩
          by_cases hcc : c' = c
          · exact hωU (hcc ▸ hωU')
          · exact (hdisj c' c (by omega) hcc).le_bot ⟨hωc', hωc⟩
      rw [e]
      exact (hR c).diff (hU c)
  have hstepF : ∀ k A, MeasurableSet[𝓖 k] A → P.real (A ∩ F k) ≤ (1 - p₀) * P.real A := by
    intro k A hA
    have hle : P (A ∩ F k) ≤ ENNReal.ofReal (1 - p₀) * P A := by
      have hsub : A ∩ F k ⊆ reachedAt depth R (2 * k + 4) := fun ω hω =>
        reachedAt_succ_subset hpar hRpar (2 * k + 4) hω.2.1
      refine measure_le_mul_of_nodes h𝓕 hR hdisj hA.1 hsub _ fun n hn => ?_
      have e : A ∩ F k ∩ R n = (A ∩ R n) ∩ (reachedAt depth R (depth n + 1) \ unitAt depth R U (depth n)) := by
        rw [hn]; ext ω; simp only [hFdef, mem_inter_iff]; tauto
      rw [e]
      exact hunit k n _ hn (hA.2 n hn) inter_subset_right
    have hne : ENNReal.ofReal (1 - p₀) * P A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P A)
    calc P.real (A ∩ F k) = (P (A ∩ F k)).toReal := rfl
      _ ≤ (ENNReal.ofReal (1 - p₀) * P A).toReal := ENNReal.toReal_mono hne hle
      _ = (1 - p₀) * P.real A := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]; rfl
  have hliminf : P (⋃ m, ⋂ k ≥ m, F k) = 0 :=
    Supp8.GB9Cap.measure_liminf_eq_zero h𝓖m (fun k => stageSigma_le hR _) hFm hp₀ hp₀1 hstepF
  have hperp := measure_diff_iInter_reachedAt_le h𝓕 hR hdisj ε hstep (P := P)
  rw [measure_univ, mul_one] at hperp
  have hsub : reachedAt depth R 0 \ {ω | (∀ j, ω ∈ reachedAt depth R j) ∧
      ∃ᶠ k in atTop, ω ∈ unitAt depth R U (2 * k + 4)} ⊆
      (reachedAt depth R 0 \ ⋂ j, reachedAt depth R j) ∪ ⋃ m, ⋂ k ≥ m, F k := by
    intro ω ⟨h0, hn⟩
    by_cases hall : ∀ j, ω ∈ reachedAt depth R j
    · right
      have hnf : ¬ ∃ᶠ k in atTop, ω ∈ unitAt depth R U (2 * k + 4) := fun hf => hn ⟨hall, hf⟩
      rw [not_frequently] at hnf
      obtain ⟨m, hm⟩ := eventually_atTop.1 hnf
      exact mem_iUnion.2 ⟨m, mem_iInter₂.2 fun k hk => ⟨hall (2 * k + 5), hm k hk⟩⟩
    · left
      exact ⟨h0, fun h => hall (mem_iInter.1 h)⟩
  calc _ ≤ P ((reachedAt depth R 0 \ ⋂ j, reachedAt depth R j) ∪ ⋃ m, ⋂ k ≥ m, F k) := measure_mono hsub
    _ ≤ P (reachedAt depth R 0 \ ⋂ j, reachedAt depth R j) + P (⋃ m, ⋂ k ≥ m, F k) := measure_union_le _ _
    _ ≤ ∑' j, ε j := by rw [hliminf, add_zero]; exact hperp

end Tree

/-! ### From a stage system to unboundedness -/

/-- **A stage system** on `Ω` (the data): a countable tree of histories (`N`, `depth`, `par`), the information `𝓕 n` at
the start of the stage from `n`, the event `R n` that `n` is reached, the unit event `U c` of the stage ending at `c`,
the stage tolerances `ε`, the unit probability `p₀`, and the relative capacity `cap n` of the history `n`. -/
structure StageSystem (Ω : Type*) [MeasurableSpace Ω] where
  /-- The nodes (finite histories). -/
  N : Type
  /-- The nodes are countably many. -/
  countable : Countable N
  /-- The number of stages of a history. -/
  depth : N → ℕ
  /-- The history one stage shorter. -/
  par : N → N
  /-- The information at the start of the stage from a history. -/
  𝓕 : N → MeasurableSpace Ω
  /-- The event that a history is realized. -/
  R : N → Set Ω
  /-- The event that the stage ending at a history consumed a unit of relative capacity. -/
  U : N → Set Ω
  /-- The failure tolerance of the stage from depth `j`. -/
  ε : ℕ → ℝ≥0∞
  /-- The unit probability of the even stages. -/
  p₀ : ℝ
  /-- The relative capacity of a realized history. -/
  cap : N → Ω → ℝ

/-- **Validity of a stage system** for the target "`S ω` is unbounded on `G`", with total tolerance `ε₀`: the tree
axioms and the one-stage bounds of `measure_reachedAt_diff_le`, the initial cover of `G`, and the capacity
bookkeeping. -/
structure StageSystem.IsValid {Ω : Type*} [mΩ : MeasurableSpace Ω] (T : StageSystem Ω) (P : Measure Ω) (G : Set Ω)
    (S : Ω → Set ℂ) (ε₀ : ℝ≥0∞) : Prop where
  hpar : ∀ c, 0 < T.depth c → T.depth (T.par c) + 1 = T.depth c
  h𝓕 : ∀ n, T.𝓕 n ≤ mΩ
  h𝓕par : ∀ c, 0 < T.depth c → T.𝓕 (T.par c) ≤ T.𝓕 c
  hR : ∀ n, MeasurableSet[T.𝓕 n] (T.R n)
  hRpar : ∀ c, 0 < T.depth c → T.R c ⊆ T.R (T.par c)
  hdisj : ∀ n n', T.depth n = T.depth n' → n ≠ n' → Disjoint (T.R n) (T.R n')
  hU : ∀ c, MeasurableSet[T.𝓕 c] (T.U c)
  hstep : ∀ n B, MeasurableSet[T.𝓕 n] B → B ⊆ T.R n →
    P (B \ reachedAt T.depth T.R (T.depth n + 1)) ≤ T.ε (T.depth n) * P B
  hp₀ : 0 < T.p₀
  hp₀1 : T.p₀ ≤ 1
  hunit : ∀ (k : ℕ) n B, T.depth n = 2 * k + 4 → MeasurableSet[T.𝓕 n] B → B ⊆ T.R n →
    P (B ∩ (reachedAt T.depth T.R (T.depth n + 1) \ unitAt T.depth T.R T.U (T.depth n))) ≤
      ENNReal.ofReal (1 - T.p₀) * P B
  hε : ∑' j, T.ε j ≤ ε₀
  hcover : ∀ᵐ ω ∂P, ω ∈ G → ω ∈ reachedAt T.depth T.R 0
  hcapMono : ∀ c, 0 < T.depth c → ∀ ω ∈ T.R c, T.cap (T.par c) ω ≤ T.cap c ω
  hcapU : ∀ c, 0 < T.depth c → ∀ ω ∈ T.R c, ω ∈ T.U c → T.cap (T.par c) ω + 1 ≤ T.cap c ω
  hcapB : ∀ n, ∀ ω ∈ T.R n, ∀ r : ℝ, S ω ⊆ Metric.closedBall 0 r → T.cap n ω ≤ 2 * r ^ 2

section Systems

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **Perpetual success with infinitely many unit stages makes the target unbounded** (deterministic; A.5: "On
perpetual success infinitely many increments are at least one. Relative capacity is therefore unbounded. A bounded
relative trace range would bound … its half-plane capacity"). -/
theorem StageSystem.IsValid.not_isBounded {T : StageSystem Ω} {P : Measure Ω} {G : Set Ω} {S : Ω → Set ℂ}
    {ε₀ : ℝ≥0∞} (hv : T.IsValid P G S ε₀) {ω : Ω} (hall : ∀ j, ω ∈ reachedAt T.depth T.R j)
    (hfr : ∃ᶠ k in atTop, ω ∈ unitAt T.depth T.R T.U (2 * k + 4)) : ¬ Bornology.IsBounded (S ω) := by
  classical
  have hex : ∀ j, ∃ n, T.depth n = j ∧ ω ∈ T.R n := fun j => by
    have h := hall j
    simp only [reachedAt, mem_iUnion] at h
    obtain ⟨n, hn, h⟩ := h
    exact ⟨n, hn, h⟩
  choose b hb hbω using hex
  have huniq : ∀ n, ω ∈ T.R n → n = b (T.depth n) := fun n hn => by
    by_contra hne
    exact (hv.hdisj n (b (T.depth n)) (hb _).symm hne).le_bot ⟨hn, hbω _⟩
  have hpos : ∀ j, 0 < T.depth (b (j + 1)) := fun j => by rw [hb]; omega
  have hparb : ∀ j, T.par (b (j + 1)) = b j := fun j => by
    have hd : T.depth (T.par (b (j + 1))) = j := by
      have := hv.hpar _ (hpos j); rw [hb] at this; omega
    have h := huniq _ (hv.hRpar _ (hpos j) (hbω (j + 1)))
    rwa [hd] at h
  set c : ℕ → ℝ := fun j => T.cap (b j) ω with hc
  have hmono : Monotone c := monotone_nat_of_le_succ fun j => by
    have h := hv.hcapMono _ (hpos j) ω (hbω (j + 1))
    rwa [hparb] at h
  have hfr' : ∃ᶠ j in atTop, c j + 1 ≤ c (j + 1) := by
    rw [frequently_atTop] at hfr ⊢
    intro a
    obtain ⟨k, hk, hku⟩ := hfr a
    refine ⟨2 * k + 4, by omega, ?_⟩
    simp only [unitAt, mem_iUnion, mem_inter_iff] at hku
    obtain ⟨c', hc', hc'R, hc'U⟩ := hku
    have hc'b : c' = b (2 * k + 4 + 1) := by rw [huniq c' hc'R, hc']
    have h := hv.hcapU c' (by omega) ω hc'R hc'U
    rw [hc'b, hparb] at h
    exact h
  have htend := GW2TipSkel.tendsto_atTop_of_frequently_add_one_le hmono hfr'
  intro hbd
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hbd
  obtain ⟨j, hj⟩ := (htend.eventually (eventually_gt_atTop (2 * r ^ 2))).exists
  exact absurd (hv.hcapB (b j) ω (hbω j) r hr) (not_le.2 hj)

/-- **Unboundedness almost surely from stage systems of every tolerance** (A.5: "Its conditional probability is at
least `1 − ε`; let `ε ↓ 0` and then use the countable initial-prefix cover"). The target event need not be
measurable. -/
theorem ae_not_isBounded_of_stageSystems {P : Measure Ω} [IsProbabilityMeasure P] {G : Set Ω} {S : Ω → Set ℂ}
    (hT : ∀ ε₀ : ℝ≥0∞, 0 < ε₀ → ∃ T : StageSystem Ω, T.IsValid P G S ε₀) :
    ∀ᵐ ω ∂P, ω ∈ G → ¬ Bornology.IsBounded (S ω) := by
  rw [ae_iff]
  set bad := {ω | ¬ (ω ∈ G → ¬ Bornology.IsBounded (S ω))} with hbad
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  obtain ⟨T, hv⟩ := hT ε (by exact_mod_cast hε)
  have := T.countable
  have hmain := measure_reachedAt_diff_le hv.hpar hv.h𝓕 hv.h𝓕par hv.hR hv.hRpar hv.hdisj hv.hU T.ε hv.hstep
    hv.hp₀ hv.hp₀1 hv.hunit (P := P)
  have hcov : P (G \ reachedAt T.depth T.R 0) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hv.hcover)
    exact fun h => hω.2 (h hω.1)
  have hsub : bad ⊆ (G \ reachedAt T.depth T.R 0) ∪ (reachedAt T.depth T.R 0 \ {ω | (∀ j, ω ∈ reachedAt T.depth T.R j) ∧
      ∃ᶠ k in atTop, ω ∈ unitAt T.depth T.R T.U (2 * k + 4)}) := by
    intro ω hω
    simp only [hbad, mem_ofPred_eq, not_imp, not_not] at hω
    by_cases h0 : ω ∈ reachedAt T.depth T.R 0
    · right
      exact ⟨h0, fun ⟨hall, hfr⟩ => hv.not_isBounded hall hfr hω.2⟩
    · left
      exact ⟨hω.1, h0⟩
  calc P bad ≤ P (G \ reachedAt T.depth T.R 0) + P (reachedAt T.depth T.R 0 \ {ω | (∀ j, ω ∈ reachedAt T.depth T.R j) ∧
        ∃ᶠ k in atTop, ω ∈ unitAt T.depth T.R T.U (2 * k + 4)}) := (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ∑' j, T.ε j := add_le_add hcov.le hmain
    _ ≤ ε := by rw [zero_add]; exact hv.hε

end Systems

end GW2TipStage

end Theorem14

end InteractingSLE
