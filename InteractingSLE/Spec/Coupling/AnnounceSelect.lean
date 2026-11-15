/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.SafeFamily
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Announcing a time from candidate sequences that either die or announce it

Packet PROVE-T11-ANN, Theorem 1.1 by the route of ruling R35 (`source/external/AstraIG1/ig1_formalization_proofs.pdf`
§1, (1.2): an announcing sequence `T_n < T_*`, `T_n ↑ T_*`). This file is the abstract, probabilistic half: a
countable family of nondecreasing sequences of stopping times `a p k` ("candidates") in a right-continuous filtration,
where almost surely

* a *bounded* candidate (`∃ M, ∀ k, a p k ≤ M`) stays strictly below `ζ` and announces it uniformly: every `t < ζ`
  is below `a p k` for all `k ≥ K`, with one `K` for all bounded candidates;
* some candidate is bounded whenever `ζ < ∞`,

admits an announcing sequence of `ζ` (`exists_isAnnouncingSeq_of_candidates`). An unbounded candidate may fire at
arbitrarily early times, so it cannot be used blindly. The proof selects candidates by their conditional probability
of being bounded: by Lévy's upward theorem a bounded candidate is eventually selected; by optional sampling on the
first selection time the probability that an unbounded candidate is ever selected is at most `2^{-(p+1)}`, so by
Borel–Cantelli only finitely many unbounded candidates are ever selected.

## Main results

* `measure_compl_inter_iUnion_le`: `P(Aᶜ ∩ ⋃ₖ Sₖ) ≤ ε` when `P[A | ℱₖ] > 1 − ε` on `Sₖ ∈ ℱₖ`;
* `stopFiltration`: the `ℕ`-filtration of the σ-algebras of a nondecreasing sequence of stopping times;
* **`exists_isAnnouncingSeq_le_of_candidates`**, `exists_isAnnouncingSeq_of_candidates`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### A conditional-probability bound -/

section Bound

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The measurable pieces `S k \ ⋃_{j<k} S j` of an increasing union, for sets adapted to a filtration. -/
theorem measurableSet_disjointed_filtration {ℱ : Filtration ℕ mΩ} {S : ℕ → Set Ω}
    (hS : ∀ k, MeasurableSet[ℱ k] (S k)) (k : ℕ) : MeasurableSet[ℱ k] (disjointed S k) := by
  rw [disjointed_eq_inter_compl]
  exact (hS k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj =>
    (ℱ.mono (le_of_lt hj) _ (hS j)).compl)

/-- **Optional sampling at the first selection.** If the conditional probability of `A` given `ℱ k` exceeds
`1 − ε` on `S k ∈ ℱ k`, then `P(Aᶜ ∩ ⋃ₖ S k) ≤ ε`. -/
theorem measure_compl_inter_iUnion_le {ℱ : Filtration ℕ mΩ} {A : Set Ω} (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 ≤ ε) {S : ℕ → Set Ω} (hS : ∀ k, MeasurableSet[ℱ k] (S k))
    (hSπ : ∀ k, ∀ ω ∈ S k, 1 - ε < (P[A.indicator (fun _ => (1 : ℝ)) | ℱ k]) ω) :
    P (Aᶜ ∩ ⋃ k, S k) ≤ ENNReal.ofReal ε := by
  set g : Ω → ℝ := A.indicator fun _ => 1 with hg_def
  have hg : Integrable g P := (integrable_const (1 : ℝ)).indicator hA
  set D : ℕ → Set Ω := disjointed S with hD_def
  have hD : ∀ k, MeasurableSet[ℱ k] (D k) := measurableSet_disjointed_filtration hS
  have hDm : ∀ k, MeasurableSet (D k) := fun k => ℱ.le k _ (hD k)
  have hpiece : ∀ k, P (D k \ A) ≤ ENNReal.ofReal ε * P (D k) := by
    intro k
    have h1 : ∫ x in D k, (P[g | ℱ k]) x ∂P = ∫ x in D k, g x ∂P :=
      setIntegral_condExp (ℱ.le k) hg (hD k)
    have h2 : ∫ x in D k, g x ∂P = P.real (D k ∩ A) := by
      rw [hg_def, setIntegral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
    have h3 : (1 - ε) * P.real (D k) ≤ ∫ x in D k, (P[g | ℱ k]) x ∂P :=
      setIntegral_ge_of_const_le_real (hDm k) (measure_ne_top _ _)
        (fun x hx => (hSπ k x (disjointed_subset S k hx)).le) integrable_condExp.integrableOn
    have hsplit : P.real (D k ∩ A) + P.real (D k \ A) = P.real (D k) := by
      rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_add
        (measure_ne_top _ _) (measure_ne_top _ _), measure_inter_add_sdiff _ hA]
    have hreal : P.real (D k \ A) ≤ ε * P.real (D k) := by nlinarith
    calc P (D k \ A) = ENNReal.ofReal (P.real (D k \ A)) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (ε * P.real (D k)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ε * P (D k) := by rw [ENNReal.ofReal_mul hε, ofReal_measureReal]
  have hU : Aᶜ ∩ ⋃ k, S k = ⋃ k, (D k \ A) := by
    rw [← iUnion_disjointed, inter_iUnion]
    refine iUnion_congr fun k => ?_
    rw [sdiff_eq, inter_comm]
  rw [hU, measure_iUnion (fun i j hij => ((disjoint_disjointed S hij).mono sdiff_subset sdiff_subset))
    (fun k => (hDm k).diff hA)]
  calc ∑' k, P (D k \ A) ≤ ∑' k, ENNReal.ofReal ε * P (D k) := ENNReal.tsum_le_tsum hpiece
    _ = ENNReal.ofReal ε * P (⋃ k, D k) := by
      rw [ENNReal.tsum_mul_left, measure_iUnion (disjoint_disjointed S) hDm]
    _ ≤ ENNReal.ofReal ε * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal ε := mul_one _

end Bound

/-! ### The filtration of a nondecreasing sequence of stopping times -/

section StopFiltration

variable {𝓖 : Filtration ℝ≥0 mΩ} {τ : ℕ → Ω → WithTop ℝ≥0}

/-- The `ℕ`-indexed filtration `k ↦ 𝓖_{τ k}` of a nondecreasing sequence of stopping times. -/
def stopFiltration (hτ : ∀ k, IsStoppingTime 𝓖 (τ k)) (hmono : ∀ ω, Monotone fun k => τ k ω) :
    Filtration ℕ mΩ where
  seq k := (hτ k).measurableSpace
  mono' _ _ hij := IsStoppingTime.measurableSpace_mono _ _ fun ω => hmono ω hij
  le' k := (hτ k).measurableSpace_le

theorem stopFiltration_apply (hτ : ∀ k, IsStoppingTime 𝓖 (τ k)) (hmono : ∀ ω, Monotone fun k => τ k ω)
    (k : ℕ) : stopFiltration hτ hmono k = (hτ k).measurableSpace := rfl

/-- A sequence of times is bounded at `ω` (by a natural number). -/
def BddSeq (τ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) : Prop :=
  ∃ M : ℕ, ∀ k, τ k ω ≤ ((M : ℝ≥0) : WithTop ℝ≥0)

/-- Boundedness of the sequence is an event of `⨆ k, 𝓖_{τ k}`. -/
theorem measurableSet_bddSeq_iSup (hτ : ∀ k, IsStoppingTime 𝓖 (τ k))
    (hmono : ∀ ω, Monotone fun k => τ k ω) :
    MeasurableSet[⨆ k, stopFiltration hτ hmono k] {ω | BddSeq τ ω} := by
  have h : {ω | BddSeq τ ω} = ⋃ M : ℕ, ⋂ k, {ω | τ k ω ≤ ((M : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω; simp [BddSeq]
  rw [h]
  exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun k =>
    (le_iSup (fun k => stopFiltration hτ hmono k) k) _ ((hτ k).measurableSet_le' _)

end StopFiltration

/-! ### Candidates that die or announce -/

section Candidates

variable {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {P : Measure Ω} [IsProbabilityMeasure P]
  {ζ : Ω → ℝ≥0∞}

/-- **An announcing sequence from candidates** (Astra §1 (1.2)). Let `a p k` (`p, k ∈ ℕ`) be stopping times of a
right-continuous filtration, nondecreasing in `k`. Suppose that almost surely a bounded candidate `p` (`BddSeq`)
stays strictly below `ζ`, that every `t < ζ` lies below `a p k` for all bounded `p` and all `k ≥ K` (one `K`), and
that some candidate is bounded when `ζ < ∞`. Then `ζ` has an announcing sequence with `T_n ≤ n`. -/
theorem exists_isAnnouncingSeq_le_of_candidates {a : ℕ → ℕ → Ω → WithTop ℝ≥0}
    (ha : ∀ p k, IsStoppingTime 𝓖 (a p k)) (hmono : ∀ p ω, Monotone fun k => a p k ω)
    (hlt : ∀ᵐ ω ∂P, ∀ p, BddSeq (a p) ω → ∀ k, ∃ t : ℝ≥0, a p k ω = t ∧ (t : ℝ≥0∞) < ζ ω)
    (hunif : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ K : ℕ, ∀ p, BddSeq (a p) ω → ∀ k, K ≤ k →
      (t : WithTop ℝ≥0) ≤ a p k ω)
    (hcover : ∀ᵐ ω ∂P, ζ ω ≠ ⊤ → ∃ p, BddSeq (a p) ω) :
    ∃ T : ℕ → Ω → ℝ≥0, IsAnnouncingSeq 𝓖 P ζ T ∧ ∀ n ω, T n ω ≤ n := by
  -- the selection by the conditional probability of being bounded
  set ℱ : ℕ → Filtration ℕ mΩ := fun p => stopFiltration (ha p) (hmono p) with hℱ
  set A : ℕ → Set Ω := fun p => {ω | BddSeq (a p) ω} with hA_def
  have hAi : ∀ p, MeasurableSet[⨆ k, ℱ p k] (A p) := fun p =>
    measurableSet_bddSeq_iSup (ha p) (hmono p)
  have hAm : ∀ p, MeasurableSet (A p) := fun p => (iSup_le fun k => (ℱ p).le k) _ (hAi p)
  set g : ℕ → Ω → ℝ := fun p => (A p).indicator fun _ => (1 : ℝ) with hg_def
  set ε : ℕ → ℝ := fun p => (1 / 2 : ℝ) ^ (p + 1) with hε_def
  have hε0 : ∀ p, 0 < ε p := fun p => by positivity
  set S : ℕ → ℕ → Set Ω := fun p k => {ω | 1 - ε p < (P[g p | ℱ p k]) ω} with hS_def
  have hS : ∀ p k, MeasurableSet[ℱ p k] (S p k) := fun p k =>
    measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable
  -- Lévy's upward theorem: a bounded candidate is eventually selected
  have hlevy : ∀ᵐ ω ∂P, ∀ p, Tendsto (fun k => (P[g p | ℱ p k]) ω) atTop (𝓝 (g p ω)) := by
    rw [ae_all_iff]
    intro p
    exact ((integrable_const (1 : ℝ)).indicator (hAm p)).tendsto_ae_condExp
      (stronglyMeasurable_const.indicator (hAi p))
  -- Borel–Cantelli: finitely many unbounded candidates are ever selected
  set F : ℕ → Set Ω := fun p => (A p)ᶜ ∩ ⋃ k, S p k with hF_def
  have hF : ∀ p, P (F p) ≤ ENNReal.ofReal (ε p) := fun p =>
    measure_compl_inter_iUnion_le (hAm p) (hε0 p).le (hS p) fun _ _ hω => hω
  have hsum : ∑' p, P (F p) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hF)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => (hε0 p).le)
      ((summable_geometric_two.mul_right (1 / 2 : ℝ)).congr fun p => (pow_succ _ _).symm)]
    exact ENNReal.ofReal_ne_top
  have hbc := ae_eventually_notMem hsum
  -- the selected candidates and the announcing sequence
  set b : ℕ → ℕ → Ω → WithTop ℝ≥0 := fun p k ω => if ω ∈ S p k then a p k ω else ⊤ with hb_def
  have hb : ∀ p k, IsStoppingTime 𝓖 (b p k) := by
    intro p k i
    have h : {ω | b p k ω ≤ i} = S p k ∩ {ω | a p k ω ≤ i} := by
      ext ω
      by_cases h : ω ∈ S p k
      · simp [hb_def, h]
      · simp only [hb_def, h, ite_false, mem_ofPred_eq, mem_inter_iff, false_and, iff_false]
        exact fun h => WithTop.coe_ne_top (top_le_iff.1 h)
    rw [h]
    exact (hS p k).2 i
  set Tw : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
    min ((n : ℝ≥0) : WithTop ℝ≥0) (⨅ q : ℕ × ℕ, b q.1 (n + q.2) ω) with hTw_def
  have hTw : ∀ n, IsStoppingTime 𝓖 (Tw n) := fun n =>
    (isStoppingTime_const 𝓖 (n : ℝ≥0)).min (IsStoppingTime.iInf fun q : ℕ × ℕ => hb q.1 (n + q.2))
  have hTw_ne : ∀ n ω, Tw n ω ≠ ⊤ := fun n ω =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  set T : ℕ → Ω → ℝ≥0 := fun n ω => (Tw n ω).untop (hTw_ne n ω) with hT_def
  have hTT : ∀ n ω, ((T n ω : ℝ≥0) : WithTop ℝ≥0) = Tw n ω := fun n ω => WithTop.coe_untop _ _
  have hTw_mono : ∀ ω, Monotone fun n => Tw n ω := fun ω => monotone_nat_of_le_succ fun n => by
    refine min_le_min (WithTop.coe_le_coe.2 (by exact_mod_cast n.le_succ)) (le_iInf fun q => ?_)
    refine (iInf_le _ (q.1, q.2 + 1)).trans_eq ?_
    show b q.1 (n + (q.2 + 1)) ω = b q.1 (n + 1 + q.2) ω
    rw [show n + (q.2 + 1) = n + 1 + q.2 by omega]
  refine ⟨T, ⟨fun n => ?_, fun ω n n' hnn' => ?_, fun n => ?_, ?_⟩, fun n ω => ?_⟩
  · -- stopping times
    have h : (fun ω => ((T n ω : ℝ≥0) : WithTop ℝ≥0)) = Tw n := funext (hTT n)
    rw [h]
    exact hTw n
  · -- monotone
    have h := hTw_mono ω hnn'
    simp only at h
    rw [← hTT, ← hTT] at h
    exact WithTop.coe_le_coe.1 h
  · -- strictly below the lifetime
    filter_upwards [hlt, hcover, hlevy] with ω hω hcov hlev
    by_cases hζ : ζ ω = ⊤
    · rw [hζ]; exact ENNReal.coe_lt_top
    obtain ⟨p, hp⟩ := hcov hζ
    have hgp : g p ω = 1 := by simp [hg_def, hA_def, hp]
    have hev : ∀ᶠ k in atTop, ω ∈ S p k :=
      (hlev p).eventually (lt_mem_nhds (by rw [hgp]; linarith [hε0 p]))
    obtain ⟨K, hK⟩ := eventually_atTop.1 hev
    obtain ⟨t, ht, htζ⟩ := hω p hp (n + K)
    have hb' : b p (n + K) ω = t := by
      simp only [hb_def, hK (n + K) (by omega), ite_true, ht]
    have hle : Tw n ω ≤ t := (min_le_right _ _).trans ((iInf_le _ (p, K)).trans_eq hb')
    rw [← hTT] at hle
    exact lt_of_le_of_lt (by exact_mod_cast WithTop.coe_le_coe.1 hle) htζ
  · -- exhaustion
    filter_upwards [hunif, hbc] with ω hun hbcω t ht
    obtain ⟨K₀, hK₀⟩ := hun t ht
    obtain ⟨P₀, hP₀⟩ := eventually_atTop.1 hbcω
    have hfin : ∀ᶠ n in atTop, ∀ p ∈ Finset.range P₀,
        BddSeq (a p) ω ∨ ∀ k, n ≤ k → (t : WithTop ℝ≥0) ≤ a p k ω := by
      rw [eventually_all_finset]
      intro p _
      by_cases hp : BddSeq (a p) ω
      · exact Eventually.of_forall fun _ => Or.inl hp
      · simp only [BddSeq, not_exists, not_forall, not_le] at hp
        obtain ⟨k₀, hk₀⟩ := hp ⌈t⌉₊
        refine eventually_atTop.2 ⟨k₀, fun n hn => Or.inr fun k hk => ?_⟩
        refine le_trans ?_ (hk₀.le.trans (hmono p ω (hn.trans hk)))
        exact WithTop.coe_le_coe.2 (Nat.le_ceil t)
    obtain ⟨n, hn, hnK⟩ := (hfin.and (eventually_ge_atTop (max K₀ ⌈t⌉₊))).exists
    refine ⟨n, ?_⟩
    have hle : (t : WithTop ℝ≥0) ≤ Tw n ω := by
      refine le_min (WithTop.coe_le_coe.2 ((Nat.le_ceil t).trans
        (by exact_mod_cast (le_max_right _ _).trans hnK))) (le_iInf fun q => ?_)
      obtain ⟨p, j⟩ := q
      show (t : WithTop ℝ≥0) ≤ b p (n + j) ω
      by_cases hS' : ω ∈ S p (n + j)
      · simp only [hb_def, hS', ite_true]
        by_cases hp : BddSeq (a p) ω
        · exact hK₀ p hp (n + j) (by omega)
        · by_cases hpP : p < P₀
          · rcases hn p (Finset.mem_range.2 hpP) with h | h
            · exact absurd h hp
            · exact h (n + j) (by omega)
          · exact absurd ⟨hp, mem_iUnion.2 ⟨n + j, hS'⟩⟩ (hP₀ p (not_lt.1 hpP))
      · simp only [hb_def, hS', ite_false]
        exact le_top
    rw [← hTT] at hle
    exact WithTop.coe_le_coe.1 hle
  · -- `T_n ≤ n`
    have h : Tw n ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := min_le_left _ _
    rw [← hTT] at h
    exact WithTop.coe_le_coe.1 h

/-- **An announcing sequence from candidates** (Astra §1 (1.2)): `exists_isAnnouncingSeq_le_of_candidates`
without the bound `T_n ≤ n`. -/
theorem exists_isAnnouncingSeq_of_candidates {a : ℕ → ℕ → Ω → WithTop ℝ≥0}
    (ha : ∀ p k, IsStoppingTime 𝓖 (a p k)) (hmono : ∀ p ω, Monotone fun k => a p k ω)
    (hlt : ∀ᵐ ω ∂P, ∀ p, BddSeq (a p) ω → ∀ k, ∃ t : ℝ≥0, a p k ω = t ∧ (t : ℝ≥0∞) < ζ ω)
    (hunif : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ K : ℕ, ∀ p, BddSeq (a p) ω → ∀ k, K ≤ k →
      (t : WithTop ℝ≥0) ≤ a p k ω)
    (hcover : ∀ᵐ ω ∂P, ζ ω ≠ ⊤ → ∃ p, BddSeq (a p) ω) :
    ∃ T : ℕ → Ω → ℝ≥0, IsAnnouncingSeq 𝓖 P ζ T :=
  let ⟨T, hT, _⟩ := exists_isAnnouncingSeq_le_of_candidates ha hmono hlt hunif hcover
  ⟨T, hT⟩

end Candidates

end Coupling

end InteractingSLE
