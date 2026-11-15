import InteractingSLE.Spec.Coupling.WholeFieldCoding
import InteractingSLE.Spec.Coupling.SafeFamily
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# History marking at a stopping time below a finite lifetime: exact capacity coding

Packet PROVE-WHOLEFIELD2 (ruling R36). Specification Aux. lemmas 18–19 (`source/spec/p049-096.md#aux-18`,
`p097-144.md#aux-18-proof`, `#aux-19-proof`, pp. 96–100).

Aux. lemma 18 codes a mark `H ∈ 𝓕_τ` into the hull of the stopping time `S = τ` on `H ∩ {τ ≤ b}`, `S = b + 1`
otherwise, and reads the branch from the capacity of `K_S`. Before a finite lifetime `T_*` this code is not available
(`b + 1` may exceed `T_*`), and Aux. lemma 19 instead approximates `τ` from above by grid times, which forces a limit
in the avoided open set (`U_m ↑ U`) and the Gaussian tail identity `⋂ₘ σ(h − P_{U_m} h) = σ(h − P_U h)`.

Here the code is kept **exact at `τ`**, so no limit in `U` is needed. For a grid interval `I = [a, b)` of width `δ`
put `G = H ∪ {τ ∉ I}` (an event of `𝓕_τ`) and

`S = τ` on `G`,   `S = max(τ, min(b, σ_k))` off `G`,

where `σ_k < T_*` is an announcing sequence. Then `S < T_*` is a stopping time, and with `Φ(K_t) = t` (half the
capacity):
* on `G`, `S = τ`, and `Φ(K_S) ∈ I` exactly when `τ ∈ I`;
* off `G` (so `τ ∈ I` and the mark fails), `S = b ∉ I` as soon as `σ_k ≥ b`, which holds when `σ_k ≥ τ + δ`.

Hence the recorded event `R_I = {K_S ∩ U = ∅} ∩ {Φ(K_S) ∈ I}` equals `H ∩ {τ ∈ I} ∩ {K_τ ∩ U = ∅}` outside
`{σ_k < τ + δ}`. The finite union of the `R_I` over the grid of width `δ_k = 1/(k+1)` up to `k + 1` converges almost
surely to `H ∩ {K_τ ∩ U = ∅}` (because `σ_k ↑ T_* > τ`), every `R_I` is recorded by the local set `K_S`, and the limit
step of `WholeFieldCoding` concludes.

## Main results

* `isStoppingTime_piecewise_of_le`: `s.piecewise τ η` is a stopping time for `s ∈ 𝓕_τ` and `τ ≤ η`;
* `measurableSet_markedSigma_avoid_inter_preimage`: `{A ∩ U = ∅} ∩ {A ∈ B}` is a recorded event;
* `exists_condExp_biUnion_eq_comp`: the class of events whose conditional probability given `h` is a function of
  `h − G h` is closed under almost surely disjoint finite unions;
* **`isHistoryAvoidanceLocal_of_capacity`** (Aux. lemmas 18–19, the history-marked avoidance criterion at a stopping
  time below the lifetime): for a family of random sets `K_t` with a hitting-measurable clock `Φ(K_t) = t` before the
  lifetime, an announcing sequence of the lifetime, and the marked avoidance criterion (Lemma 3.6 (ii)) for the sets
  `K_S` at every stopping time `S` below the lifetime, every version `A` of `K_τ` satisfies the history-marked
  avoidance criterion for the marks `𝓕_τ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper LQGMetric

/-! ### Stopping times built from a mark -/

section StoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- **Splicing two ordered stopping times along an event of `𝓕_τ`.** If `τ ≤ η` are stopping times and `s ∈ 𝓕_τ`,
then `τ` on `s` and `η` off `s` is a stopping time. -/
theorem isStoppingTime_piecewise_of_le {τ η : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hη : IsStoppingTime 𝓖 η) (hle : ∀ ω, τ ω ≤ η ω) {s : Set Ω} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet[hτ.measurableSpace] s) : IsStoppingTime 𝓖 (s.piecewise τ η) := by
  intro i
  have e : {ω | s.piecewise τ η ω ≤ i} =
      s ∩ {ω | τ ω ≤ i} ∪ (sᶜ ∩ {ω | τ ω ≤ i}) ∩ {ω | η ω ≤ i} := by
    ext ω
    by_cases hω : ω ∈ s
    · simp [Set.piecewise, hω]
    · simp only [Set.piecewise, hω, ite_false, mem_ofPred_eq, mem_union, mem_inter_iff, false_and,
        mem_compl_iff, not_false_eq_true, true_and, false_or]
      exact ⟨fun h => ⟨(hle ω).trans h, h⟩, fun h => h.2⟩
  rw [e]
  exact (hs.2 i).union ((hs.compl.2 i).inter (hη i))

omit mΩ in
/-- A finite `x : WithTop ℝ≥0` is the coercion of `x.untopD 0`. -/
theorem coe_untopD_of_ne_top {x : WithTop ℝ≥0} (h : x ≠ ⊤) :
    ((x.untopD 0 : ℝ≥0) : WithTop ℝ≥0) = x := by
  induction x with
  | top => exact absurd rfl h
  | coe y => rw [WithTop.untopD_coe]

/-- `{a ≤ τ < b}` is an event of `𝓕_τ`. -/
theorem measurableSet_Ico_stoppingTime {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (a b : ℝ≥0) :
    MeasurableSet[hτ.measurableSpace] {ω | (a : WithTop ℝ≥0) ≤ τ ω ∧ τ ω < b} :=
  (hτ.measurableSet_ge' a).inter (hτ.measurableSet_lt' b)

end StoppingTime

/-! ### Recorded events and finite unions -/

section Events

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

omit mΩ [IsProbabilityMeasure P] in
/-- `{A ∩ U = ∅} ∩ {A ∈ B}` is an event of the marked σ-algebra of `A` for every hitting-measurable `B`. -/
theorem measurableSet_markedSigma_avoid_inter_preimage (A : Ω → Set ℂ) (U : Set ℂ)
    {B : Set (Set ℂ)} (hB : MeasurableSet[hittingSigma] B) :
    MeasurableSet[markedSigma A U] ({ω | Disjoint (A ω) U} ∩ A ⁻¹' B) := by
  rw [markedSigma_eq_generateFrom]
  exact MeasurableSpace.measurableSet_generateFrom ⟨B, hB, Or.inl rfl⟩

/-- **Finite unions.** If the events `E j` (`j ∈ s`) are almost surely pairwise disjoint and every `P[E j | m]` is
almost surely a measurable function of `Y`, so is `P[⋃_{j ∈ s} E j | m]`. -/
theorem exists_condExp_biUnion_eq_comp {β : Type*} [MeasurableSpace β]
    {Y : Ω → β} {ι : Type*} (s : Finset ι) {E : ι → Set Ω} (hE : ∀ j, MeasurableSet (E j))
    (hd : ∀ᵐ ω ∂P, ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ (ω ∈ E i ∧ ω ∈ E j))
    (hg : ∀ j ∈ s, ∃ g : β → ℝ, Measurable g ∧ P⟦E j | m⟧ =ᵐ[P] fun ω => g (Y ω)) :
    ∃ g : β → ℝ, Measurable g ∧ P⟦⋃ j ∈ s, E j | m⟧ =ᵐ[P] fun ω => g (Y ω) := by
  classical
  choose! gs hgs hgse using hg
  refine ⟨fun y => ∑ j ∈ s, gs j y, Finset.measurable_sum _ fun j hj => hgs j hj, ?_⟩
  have hind : ((⋃ j ∈ s, E j).indicator fun _ => (1 : ℝ)) =ᵐ[P]
      ∑ j ∈ s, (E j).indicator fun _ => (1 : ℝ) := by
    filter_upwards [hd] with ω hω
    rw [Finset.sum_apply]
    by_cases hU : ω ∈ ⋃ j ∈ s, E j
    · obtain ⟨j₀, hj₀, hω₀⟩ := mem_iUnion₂.1 hU
      rw [indicator_of_mem hU, Finset.sum_eq_single j₀]
      · rw [indicator_of_mem hω₀]
      · intro j hj hne
        exact indicator_of_notMem (fun h => hω j hj j₀ hj₀ hne ⟨h, hω₀⟩) _
      · exact fun h => absurd hj₀ h
    · rw [indicator_of_notMem hU]
      refine (Finset.sum_eq_zero fun j hj => ?_).symm
      exact indicator_of_notMem (fun h => hU (mem_iUnion₂.2 ⟨j, hj, h⟩)) _
  have hint : ∀ j ∈ s, Integrable ((E j).indicator fun _ => (1 : ℝ)) P :=
    fun j _ => (integrable_const (1 : ℝ)).indicator (hE j)
  have h1 := condExp_congr_ae (m := m) hind
  have h2 := condExp_finsetSum (m := m) hint
  have h3 : ∀ᵐ ω ∂P, ∀ j ∈ s, (P⟦E j | m⟧) ω = gs j (Y ω) := by
    exact (eventually_all_finset s).2 fun j hj => hgse j hj
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1, e2, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j hj => e3 j hj

end Events

/-! ### The grid code -/

section Grid

/-- **The grid code, arithmetic part.** Let `S' = s` if the mark holds or `s ∉ [a, a + δ)`, and
`S' = max(s, min(a + δ, σ))` otherwise. Then `S' ∈ [a, a + δ)` forces `s ∈ [a, a + δ)`; if `σ ≥ s + δ`,
`S' ∈ [a, a + δ)` holds exactly when `s ∈ [a, a + δ)` and the mark holds; and under the mark `S' = s`. -/
theorem grid_code {s σ a δ : ℝ≥0} (p : Prop) [Decidable p] :
    ((if p ∨ ¬ (a ≤ s ∧ s < a + δ) then s else max s (min (a + δ) σ)) ∈ Ico a (a + δ) →
        a ≤ s ∧ s < a + δ) ∧
      (s + δ ≤ σ → ((if p ∨ ¬ (a ≤ s ∧ s < a + δ) then s else max s (min (a + δ) σ)) ∈
          Ico a (a + δ) ↔ (a ≤ s ∧ s < a + δ) ∧ p)) ∧
      (p → (if p ∨ ¬ (a ≤ s ∧ s < a + δ) then s else max s (min (a + δ) σ)) = s) := by
  split_ifs with hc
  · refine ⟨fun h => ?_, fun _ => ?_, fun _ => rfl⟩
    · exact h
    · rcases hc with hp | hI
      · exact ⟨fun h => ⟨h, hp⟩, fun h => h.1⟩
      · exact ⟨fun h => absurd h hI, fun h => absurd h.1 hI⟩
  · have hp : ¬ p := fun hp => hc (Or.inl hp)
    have hI : a ≤ s ∧ s < a + δ := by
      by_contra hI
      exact hc (Or.inr hI)
    refine ⟨fun _ => hI, fun hσ => ?_, fun h => absurd h hp⟩
    have hb : a + δ ≤ σ := by
      calc a + δ ≤ s + δ := add_le_add hI.1 le_rfl
        _ ≤ σ := hσ
    rw [min_eq_left hb, max_eq_right hI.2.le]
    simp only [mem_Ico, lt_irrefl, and_false, hp]

/-- Every `s < k + 1` lies in one of the first `(k + 1)²` grid intervals of width `1/(k + 1)`. -/
theorem exists_grid_mem {s : ℝ≥0} {k : ℕ} (hs : s < k + 1) :
    ∃ j ∈ Finset.range ((k + 1) ^ 2), (j : ℝ≥0) * (1 / ((k : ℝ≥0) + 1)) ≤ s ∧
      s < (j : ℝ≥0) * (1 / ((k : ℝ≥0) + 1)) + 1 / ((k : ℝ≥0) + 1) := by
  have hk : (0 : ℝ≥0) < (k : ℝ≥0) + 1 := by positivity
  refine ⟨⌊s * ((k : ℝ≥0) + 1)⌋₊, ?_, ?_, ?_⟩
  · rw [Finset.mem_range, Nat.floor_lt zero_le]
    push_cast
    rw [sq]
    exact mul_lt_mul_of_pos_right hs hk
  · rw [← div_eq_mul_one_div, div_le_iff₀ hk]
    exact Nat.floor_le zero_le
  · rw [← div_eq_mul_one_div, ← add_div, lt_div_iff₀ hk]
    exact_mod_cast Nat.lt_floor_add_one _

/-- The grid width `1/(k + 1)` is eventually below every positive number. -/
theorem eventually_one_div_lt {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ≥0) + 1) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hk' : (0 : ℝ≥0) < (k : ℝ≥0) + 1 := by positivity
  rw [div_lt_iff₀ hk', ← div_lt_iff₀' hε]
  calc 1 / ε < N := hN
    _ ≤ k := by exact_mod_cast hk
    _ < k + 1 := lt_add_one _

end Grid

/-! ### The main coding theorem -/

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **History marking at a stopping time below the lifetime** (Aux. lemmas 18–19, first conclusion; exact capacity
code). Let `K_t` (`t ≥ 0`) be random sets with a hitting-measurable clock `Φ(K_t) = t` before the lifetime `ζ`
(half the half-plane capacity, for Loewner hulls), let `σ_k` announce `ζ` in the filtration `𝓖`, and suppose that at
every stopping time `S < ζ` the set `K_S` has a hitting-measurable version satisfying the marked avoidance criterion
(Lemma 3.6 (ii)). Then for every stopping time `τ < ζ` and every hitting-measurable version `A` of `K_τ`, the
history-marked avoidance criterion holds for the marks `𝓕_τ`. -/
theorem isHistoryAvoidanceLocal_of_capacity {𝓖 : Filtration ℝ≥0 mΩ} {K : ℝ≥0 → Ω → Set ℂ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {Φ : Set ℂ → ℝ≥0∞} (hΦ : Measurable[hittingSigma] Φ)
    (hΦK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → Φ (K t ω) = t)
    {σ : ℕ → Ω → ℝ≥0} (hσ : Coupling.IsAnnouncingSeq 𝓖 P ζ σ)
    (hloc : ∀ S : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 S → (∀ᵐ ω ∂P, (S ω : ℝ≥0∞) < ζ ω) →
      ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧
        (∀ᵐ ω ∂P, A ω = K ((S ω).untopD 0) ω) ∧ IsMarkedAvoidanceLocal A h P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = K ((τ ω).untopD 0) ω) :
    IsHistoryAvoidanceLocal hτ.measurableSpace A h P := by
  classical
  intro U G hUH hG hMD F hF
  -- the grid of width `δ k = 1/(k+1)`
  set δ : ℕ → ℝ≥0 := fun k => 1 / ((k : ℝ≥0) + 1) with hδ
  set a : ℕ → ℕ → ℝ≥0 := fun k j => (j : ℝ≥0) * δ k with ha
  -- the coded stopping times
  set Gs : ℕ → ℕ → Set Ω := fun k j =>
    F ∪ {ω | ((a k j : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω ∧ τ ω < ((a k j + δ k : ℝ≥0) : WithTop ℝ≥0)}ᶜ
    with hGs_def
  set η : ℕ → ℕ → Ω → WithTop ℝ≥0 := fun k j ω =>
    max (τ ω) (min ((a k j + δ k : ℝ≥0) : WithTop ℝ≥0) (σ k ω : WithTop ℝ≥0)) with hη_def
  set S : ℕ → ℕ → Ω → WithTop ℝ≥0 := fun k j => (Gs k j).piecewise τ (η k j) with hS_def
  have hGs : ∀ k j, MeasurableSet[hτ.measurableSpace] (Gs k j) := fun k j =>
    hF.union (measurableSet_Ico_stoppingTime hτ _ _).compl
  have hη : ∀ k j, IsStoppingTime 𝓖 (η k j) := fun k j =>
    hτ.max ((isStoppingTime_const 𝓖 _).min (hσ.1 k))
  have hS : ∀ k j, IsStoppingTime 𝓖 (S k j) := fun k j =>
    isStoppingTime_piecewise_of_le hτ (hη k j) (fun ω => le_max_left _ _) (hGs k j)
  have hSζ : ∀ k j, ∀ᵐ ω ∂P, (S k j ω : ℝ≥0∞) < ζ ω := by
    intro k j
    filter_upwards [hτζ, hσ.2.2.1 k] with ω h1 h2
    by_cases hω : ω ∈ Gs k j
    · simpa only [hS_def, Set.piecewise, hω, ite_true] using h1
    · simp only [hS_def, Set.piecewise, hω, ite_false, hη_def]
      exact max_lt h1 ((min_le_right _ _).trans_lt h2)
  choose As hAsm hAsK hAsloc using fun k j => hloc (S k j) (hS k j) (hSζ k j)
  -- the recorded events
  set R : ℕ → ℕ → Set Ω := fun k j => {ω | Disjoint (As k j ω) U} ∩
    As k j ⁻¹' (Φ ⁻¹' Ico ((a k j : ℝ≥0) : ℝ≥0∞) ((a k j + δ k : ℝ≥0) : ℝ≥0∞)) with hR_def
  have hRm : ∀ k j, MeasurableSet[markedSigma (As k j) U] (R k j) := fun k j =>
    measurableSet_markedSigma_avoid_inter_preimage _ _ (hΦ measurableSet_Ico)
  have hRm' : ∀ k j, MeasurableSet (R k j) := fun k j =>
    markedSigma_le (hAsm k j) U.isOpen hUH _ (hRm k j)
  set Es : ℕ → Set Ω := fun k => ⋃ j ∈ Finset.range ((k + 1) ^ 2), R k j with hEs_def
  set E : Set Ω := {ω | Disjoint (A ω) U} ∩ F with hE_def
  have hEm : MeasurableSet E :=
    (hA (measurableSet_avoid U.isOpen hUH)).inter (hτ.measurableSpace_le F hF)
  -- the good event
  have hgood : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω ∧ (∀ k j, (S k j ω : ℝ≥0∞) < ζ ω) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → Φ (K t ω) = t) ∧ A ω = K ((τ ω).untopD 0) ω ∧
      (∀ k j, As k j ω = K ((S k j ω).untopD 0) ω) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ σ n ω) := by
    have h2 : ∀ᵐ ω ∂P, ∀ k j, (S k j ω : ℝ≥0∞) < ζ ω :=
      ae_all_iff.2 fun k => ae_all_iff.2 fun j => hSζ k j
    have h5 : ∀ᵐ ω ∂P, ∀ k j, As k j ω = K ((S k j ω).untopD 0) ω :=
      ae_all_iff.2 fun k => ae_all_iff.2 fun j => hAsK k j
    filter_upwards [hτζ, h2, hΦK, hAK, h5, hσ.2.2.2] with ω g1 g2 g3 g4 g5 g6
    exact ⟨g1, g2, g3, g4, g5, g6⟩
  -- pointwise analysis on the good event
  have hpt : ∀ᵐ ω ∂P, (∀ k, ∀ i ∈ Finset.range ((k + 1) ^ 2), ∀ j ∈ Finset.range ((k + 1) ^ 2),
      i ≠ j → ¬ (ω ∈ R k i ∧ ω ∈ R k j)) ∧ ∀ᶠ k in atTop, (ω ∈ Es k ↔ ω ∈ E) := by
    filter_upwards [hgood] with ω ⟨g1, g2, g3, g4, g5, g6⟩
    have hτtop : τ ω ≠ ⊤ := fun h => by rw [h] at g1; exact absurd g1 (not_lt.2 le_top)
    set s : ℝ≥0 := (τ ω).untopD 0 with hs_def
    have hτs : τ ω = (s : WithTop ℝ≥0) := (coe_untopD_of_ne_top hτtop).symm
    -- the stopped value of the code
    have hSv : ∀ k j, (S k j ω).untopD 0 = if ω ∈ F ∨ ¬ (a k j ≤ s ∧ s < a k j + δ k) then s
        else max s (min (a k j + δ k) (σ k ω)) := by
      intro k j
      have hmem : ω ∈ Gs k j ↔ ω ∈ F ∨ ¬ (a k j ≤ s ∧ s < a k j + δ k) := by
        simp only [hGs_def, mem_union, mem_compl_iff, mem_ofPred_eq, hτs, WithTop.coe_le_coe,
          WithTop.coe_lt_coe]
      by_cases hω : ω ∈ Gs k j
      · have hc := hmem.1 hω
        simp only [hS_def, Set.piecewise, hω, ite_true, hτs, WithTop.untopD_coe, hc]
      · have hc : ¬ (ω ∈ F ∨ ¬ (a k j ≤ s ∧ s < a k j + δ k)) := fun h => hω (hmem.2 h)
        simp only [hS_def, Set.piecewise, hω, ite_false, hη_def, hτs, hc]
        rw [← WithTop.coe_min, ← WithTop.coe_max, WithTop.untopD_coe]
    have hSfin : ∀ k j, S k j ω = (((S k j ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) := by
      intro k j
      refine (coe_untopD_of_ne_top fun h => ?_).symm
      have := g2 k j
      rw [h] at this
      exact absurd this (not_lt.2 le_top)
    -- membership in the recorded events
    have hRiff : ∀ k j, ω ∈ R k j ↔ Disjoint (K ((S k j ω).untopD 0) ω) U ∧
        (S k j ω).untopD 0 ∈ Ico (a k j) (a k j + δ k) := by
      intro k j
      have hlt : (((S k j ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
        have := g2 k j
        rwa [hSfin k j] at this
      simp only [hR_def, mem_inter_iff, mem_ofPred_eq, mem_preimage, g5 k j, g3 _ hlt, mem_Ico,
        ENNReal.coe_le_coe, ENNReal.coe_lt_coe]
    refine ⟨fun k i _ j _ hij hboth => ?_, ?_⟩
    · -- distinct grid intervals are disjoint
      have hi := (grid_code (s := s) (σ := σ k ω) (a := a k i) (δ := δ k) (ω ∈ F)).1
        (by rw [← hSv k i]; exact ((hRiff k i).1 hboth.1).2)
      have hj := (grid_code (s := s) (σ := σ k ω) (a := a k j) (δ := δ k) (ω ∈ F)).1
        (by rw [← hSv k j]; exact ((hRiff k j).1 hboth.2).2)
      rcases lt_or_gt_of_ne hij with h | h
      · have : a k i + δ k ≤ a k j := by
          simp only [ha]
          rw [← add_one_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) zero_le
        exact absurd (hi.2.trans_le this) (not_lt.2 hj.1)
      · have : a k j + δ k ≤ a k i := by
          simp only [ha]
          rw [← add_one_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) zero_le
        exact absurd (hj.2.trans_le this) (not_lt.2 hi.1)
    · -- eventually the code is exact
      obtain ⟨t, hst, htζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (show (s : ℝ≥0∞) < ζ ω by
        rw [← coe_untopD_of_ne_top hτtop] at g1; exact g1)
      have hst' : s < t := by exact_mod_cast hst
      obtain ⟨n₀, hn₀⟩ := g6 t htζ
      obtain ⟨N, hN⟩ := exists_nat_gt s
      filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop N,
        eventually_one_div_lt (tsub_pos_of_lt hst')] with k hk hkN hkδ
      have hσk : s + δ k ≤ σ k ω := by
        have h1 : t ≤ σ k ω := hn₀.trans (hσ.2.1 ω hk)
        have h2 : s + δ k ≤ t := by
          calc s + δ k ≤ s + (t - s) := add_le_add le_rfl hkδ.le
            _ = t := add_tsub_cancel_of_le hst'.le
        exact h2.trans h1
      have hsk : s < k + 1 := hN.trans_le (by exact_mod_cast hkN.trans (Nat.le_succ k))
      obtain ⟨j₀, hj₀, hj₀s⟩ := exists_grid_mem hsk
      have hj₀s' : a k j₀ ≤ s ∧ s < a k j₀ + δ k := hj₀s
      have hcode : ∀ j, ω ∈ R k j ↔ ((a k j ≤ s ∧ s < a k j + δ k) ∧ ω ∈ F) ∧ ω ∈ {ω | Disjoint (A ω) U} := by
        intro j
        have hc := grid_code (s := s) (σ := σ k ω) (a := a k j) (δ := δ k) (ω ∈ F)
        rw [hRiff k j, hSv k j, hc.2.1 hσk]
        constructor
        · rintro ⟨hd, hI⟩
          refine ⟨hI, ?_⟩
          rw [hc.2.2 hI.2] at hd
          rw [mem_ofPred_eq, g4]
          exact hd
        · rintro ⟨hI, hd⟩
          refine ⟨?_, hI⟩
          rw [hc.2.2 hI.2]
          rw [mem_ofPred_eq, g4] at hd
          exact hd
      simp only [hEs_def, hE_def, mem_iUnion, exists_prop, mem_inter_iff]
      constructor
      · rintro ⟨j, -, hj⟩
        have := (hcode j).1 hj
        exact ⟨this.2, this.1.2⟩
      · rintro ⟨hd, hFω⟩
        exact ⟨j₀, hj₀, (hcode j₀).2 ⟨⟨hj₀s', hFω⟩, hd⟩⟩
  -- the limit step
  have hlim : Tendsto (fun k => P (symmDiff (Es k) E)) atTop (𝓝 0) := by
    have := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := P) (L := atTop)
      (A := (∅ : Set Ω)) MeasurableSet.empty
      (fun k => (MeasurableSet.biUnion (Finset.range ((k + 1) ^ 2)).countable_toSet
        fun j _ => hRm' k j).symmDiff hEm) ?_
    · rwa [measure_empty] at this
    · filter_upwards [hpt] with ω hω
      filter_upwards [hω.2] with k hk
      refine ⟨fun h => ?_, fun h => h.elim⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 (hk.1 h1)
      · exact h2 (hk.2 h1)
  refine exists_condExp_eq_comp_of_tendsto hEm (fun k => MeasurableSet.biUnion
    (Finset.range ((k + 1) ^ 2)).countable_toSet fun j _ => hRm' k j) hlim fun k => ?_
  refine exists_condExp_biUnion_eq_comp _ (hRm' k) ?_ fun j _ =>
    IsMarkedAvoidanceLocal.exists_condExp_eq_comp (hAsm k j) hh (hAsloc k j) U hUH hG hMD (hRm k j)
  filter_upwards [hpt] with ω hω
  exact hω.1 k

end Main

end WholeField

end InteractingSLE
