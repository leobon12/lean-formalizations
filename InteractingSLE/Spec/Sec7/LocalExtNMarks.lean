/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLLocQ

/-!
# Aux. lemma 54, (Loc) after the stop: the pre-stop marks determine a regular history

Packet PROVE-LOCEXT-N. The pre-stop marks `preMarkSet t Γ = {t < y.1, truncH t y ∈ Γ}` (`t` rational) are the history
events that a coding stop below the stop `S` can record (`LocalExtLLocQ`). They generate a σ-algebra `preMarkSigma` on
the two-seed histories. A **regular** history `tsOf S₀ X` (`0 < S₀`, `X` continuous on `[0, S₀]`) is recovered from them:
its values before `S₀` are recorded, and its value from `S₀` on is the limit of its values at the dyadic times below
`S₀`. So the reconstruction `histRecon` is `preMarkSigma`-measurable and is the identity on regular histories.

## Main results

* `preMarkSigma`, `isPiSystem_preMarkSets`;
* `measurable_fst_preMarkSigma`: the stop `y.1` is `preMarkSigma`-measurable;
* `histRecon`, `measurable_histRecon`, `histRecon_tsOf`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

/-! ### The σ-algebra of the pre-stop marks -/

/-- The pre-stop mark sets. -/
def preMarkSets : Set (Set TwoSeedHist) :=
  {M | ∃ (t : ℚ≥0) (Γ : Set TwoSeedHist), MeasurableSet Γ ∧ M = preMarkSet t Γ}

/-- **The σ-algebra of the pre-stop marks.** -/
@[instance_reducible]
def preMarkSigma : MeasurableSpace TwoSeedHist := MeasurableSpace.generateFrom preMarkSets

theorem truncH_truncH {t t' : ℚ≥0} (h : t ≤ t') (y : TwoSeedHist) : truncH t (truncH t' y) = truncH t y := by
  have h' : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ ((t' : ℝ≥0) : WithTop ℝ≥0) := by exact_mod_cast h
  refine Prod.ext ?_ (funext fun q => ?_)
  · simp only [truncH, min_assoc, min_eq_right h']
  · simp only [truncH, min_assoc, min_eq_left h]

theorem preMarkSet_inter_of_le {t t' : ℚ≥0} (h : t ≤ t') (Γ Γ' : Set TwoSeedHist) :
    preMarkSet t Γ ∩ preMarkSet t' Γ' = preMarkSet t' (truncH t ⁻¹' Γ ∩ Γ') := by
  have h' : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ ((t' : ℝ≥0) : WithTop ℝ≥0) := by exact_mod_cast h
  ext y
  simp only [preMarkSet, mem_inter_iff, mem_ofPred_eq, mem_preimage, truncH_truncH h]
  constructor
  · rintro ⟨⟨-, h1⟩, h2, h3⟩
    exact ⟨h2, h1, h3⟩
  · rintro ⟨h2, h1, h3⟩
    exact ⟨⟨lt_of_le_of_lt h' h2, h1⟩, h2, h3⟩

theorem isPiSystem_preMarkSets : IsPiSystem preMarkSets := by
  rintro _ ⟨t, Γ, hΓ, rfl⟩ _ ⟨t', Γ', hΓ', rfl⟩ -
  rcases le_total t t' with h | h
  · exact ⟨t', _, ((measurable_truncH t) hΓ).inter hΓ', preMarkSet_inter_of_le h Γ Γ'⟩
  · rw [inter_comm]
    exact ⟨t, _, ((measurable_truncH t') hΓ').inter hΓ, preMarkSet_inter_of_le h Γ' Γ⟩

theorem measurableSet_preMarkSet (t : ℚ≥0) {Γ : Set TwoSeedHist} (hΓ : MeasurableSet Γ) :
    MeasurableSet[preMarkSigma] (preMarkSet t Γ) :=
  MeasurableSpace.measurableSet_generateFrom ⟨t, Γ, hΓ, rfl⟩

theorem preMarkSigma_le : preMarkSigma ≤ (inferInstance : MeasurableSpace TwoSeedHist) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨t, Γ, hΓ, rfl⟩
  exact (measurableSet_lt measurable_const measurable_fst).inter ((measurable_truncH t) hΓ)

theorem measurableSet_lt_fst (t : ℚ≥0) :
    MeasurableSet[preMarkSigma] {y : TwoSeedHist | ((t : ℝ≥0) : WithTop ℝ≥0) < y.1} := by
  have e : {y : TwoSeedHist | ((t : ℝ≥0) : WithTop ℝ≥0) < y.1} = preMarkSet t univ := by
    ext y
    simp only [preMarkSet, mem_ofPred_eq, mem_univ, and_true]
  rw [e]
  exact measurableSet_preMarkSet t MeasurableSet.univ

/-- **The stop of a history is a function of the pre-stop marks.** -/
theorem measurable_fst_preMarkSigma : Measurable[preMarkSigma] fun y : TwoSeedHist => y.1 := by
  refine measurable_of_Ioi (mδ := preMarkSigma) fun x => ?_
  cases x with
  | top =>
    have e : (fun y : TwoSeedHist => y.1) ⁻¹' Ioi (⊤ : WithTop ℝ≥0) = ∅ := by
      ext y
      simp only [mem_preimage, mem_Ioi, not_top_lt, mem_empty_iff_false]
    rw [e]
    exact @MeasurableSet.empty _ preMarkSigma
  | coe x₀ =>
    have e : (fun y : TwoSeedHist => y.1) ⁻¹' Ioi ((x₀ : ℝ≥0) : WithTop ℝ≥0) =
        ⋃ t ∈ {t : ℚ≥0 | x₀ < (t : ℝ≥0)}, {y : TwoSeedHist | ((t : ℝ≥0) : WithTop ℝ≥0) < y.1} := by
      ext y
      simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_ofPred_eq, exists_prop]
      constructor
      · intro hy
        obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_withTop hy
        exact ⟨q, hq1, hq2⟩
      · rintro ⟨t, ht, hty⟩
        exact lt_trans (WithTop.coe_lt_coe.2 ht) hty
    rw [e]
    exact MeasurableSet.biUnion (to_countable _) fun t _ => measurableSet_lt_fst t

/-! ### Dyadic times below the stop -/

/-- The largest dyadic time `k/2ⁿ` strictly below `s > 0`. -/
def dyadicBelow (n : ℕ) (s : ℝ≥0) : ℚ≥0 := (((⌈(2 : ℝ≥0) ^ n * s⌉₊ - 1 : ℕ) : ℚ≥0)) / 2 ^ n

theorem coe_dyadicBelow (n : ℕ) (s : ℝ≥0) :
    ((dyadicBelow n s : ℚ≥0) : ℝ≥0) = ((⌈(2 : ℝ≥0) ^ n * s⌉₊ - 1 : ℕ) : ℝ≥0) / 2 ^ n := by
  simp only [dyadicBelow, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_pow, NNRat.cast_ofNat]

theorem dyadicBelow_lt {n : ℕ} {s : ℝ≥0} (hs : 0 < s) : ((dyadicBelow n s : ℚ≥0) : ℝ≥0) < s := by
  rw [coe_dyadicBelow]
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos (by norm_num) n
  rw [div_lt_iff₀ h2]
  have hpos : 0 < (2 : ℝ≥0) ^ n * s := mul_pos h2 hs
  have hc : 0 < ⌈(2 : ℝ≥0) ^ n * s⌉₊ := Nat.ceil_pos.2 hpos
  have := Nat.lt_ceil.1 (Nat.sub_lt hc one_pos)
  calc _ < (2 : ℝ≥0) ^ n * s := this
    _ = s * 2 ^ n := mul_comm _ _

theorem lt_dyadicBelow_add {n : ℕ} (s : ℝ≥0) :
    s ≤ ((dyadicBelow n s : ℚ≥0) : ℝ≥0) + 1 / 2 ^ n := by
  rw [coe_dyadicBelow]
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos (by norm_num) n
  rw [← add_div, le_div_iff₀ h2, mul_comm]
  have h1 : ((⌈(2 : ℝ≥0) ^ n * s⌉₊ - 1 : ℕ) : ℝ≥0) + 1 ≥ (⌈(2 : ℝ≥0) ^ n * s⌉₊ : ℝ≥0) := by
    have : ⌈(2 : ℝ≥0) ^ n * s⌉₊ ≤ (⌈(2 : ℝ≥0) ^ n * s⌉₊ - 1) + 1 := by omega
    exact_mod_cast this
  exact (Nat.le_ceil _).trans h1

/-- On `(k/2ⁿ, (k+1)/2ⁿ]` the dyadic time below is `k/2ⁿ`. -/
theorem dyadicBelow_eq_iff {n k : ℕ} {s : ℝ≥0} (hs : 0 < s) :
    dyadicBelow n s = (k : ℚ≥0) / 2 ^ n ↔
      ((((k : ℚ≥0) / 2 ^ n : ℚ≥0) : ℝ≥0) < s ∧ s ≤ ((((k : ℚ≥0) + 1) / 2 ^ n : ℚ≥0) : ℝ≥0)) := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos (by norm_num) n
  have h2q : (0 : ℚ≥0) < 2 ^ n := pow_pos (by norm_num) n
  have hpos : 0 < (2 : ℝ≥0) ^ n * s := mul_pos h2 hs
  have hc : ⌈(2 : ℝ≥0) ^ n * s⌉₊ ≠ 0 := (Nat.ceil_pos.2 hpos).ne'
  simp only [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_pow, NNRat.cast_ofNat, NNRat.cast_add, NNRat.cast_one]
  rw [div_lt_iff₀ h2, le_div_iff₀ h2, dyadicBelow, div_left_inj' h2q.ne', Nat.cast_inj, mul_comm s]
  have key : ⌈(2 : ℝ≥0) ^ n * s⌉₊ = k + 1 ↔ ((k : ℝ≥0) < 2 ^ n * s ∧ 2 ^ n * s ≤ (k : ℝ≥0) + 1) := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero k)]
    push_cast
    rfl
  rw [← key]
  omega

/-! ### The reconstruction of a regular history from its marks -/

/-- The value of a history at the dyadic time below its stop (`0` unless `0 < y.1 < ∞`). -/
def dyadicVal (n : ℕ) (y : TwoSeedHist) : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  if 0 < y.1 ∧ y.1 ≠ ⊤ then y.2 (dyadicBelow n (y.1.untopD 0)) else 0

theorem measurable_dyadicVal (n : ℕ) : Measurable[preMarkSigma] (dyadicVal n) := by
  classical
  intro B hB
  set c : ℕ → ℚ≥0 := fun k => (k : ℚ≥0) / 2 ^ n with hc
  set c' : ℕ → ℚ≥0 := fun k => ((k : ℚ≥0) + 1) / 2 ^ n with hc'
  have e : dyadicVal n ⁻¹' B = (⋃ k : ℕ, preMarkSet (c k) {z | z.2 (c k) ∈ B} ∩
      {y : TwoSeedHist | y.1 ≤ ((c' k : ℝ≥0) : WithTop ℝ≥0)}) ∪
      ({y : TwoSeedHist | ¬ (0 < y.1 ∧ y.1 ≠ ⊤)} ∩ {_y | (0 : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)) ∈ B}) := by
    ext y
    simp only [mem_preimage, dyadicVal, mem_union, mem_iUnion, mem_inter_iff, preMarkSet, mem_ofPred_eq, truncH,
      min_self]
    by_cases hy : 0 < y.1 ∧ y.1 ≠ ⊤
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hy.2
      have hs0 : 0 < s := by rw [← hs] at hy; exact_mod_cast hy.1
      have hy' : 0 < ((s : ℝ≥0) : WithTop ℝ≥0) ∧ ((s : ℝ≥0) : WithTop ℝ≥0) ≠ ⊤ :=
        ⟨WithTop.coe_lt_coe.2 hs0, WithTop.coe_ne_top⟩
      rw [← hs, ite_eq_left_of_eq_true _ _ (eq_true hy'), WithTop.untopD_coe, or_iff_left (fun h => h.1 hy')]
      simp only [WithTop.coe_lt_coe, WithTop.coe_le_coe]
      constructor
      · intro hB'
        refine ⟨⌈(2 : ℝ≥0) ^ n * s⌉₊ - 1, ?_⟩
        have hd : dyadicBelow n s = c (⌈(2 : ℝ≥0) ^ n * s⌉₊ - 1) := rfl
        have := (dyadicBelow_eq_iff hs0).1 hd
        exact ⟨⟨this.1, by rw [← hd]; exact hB'⟩, this.2⟩
      · rintro ⟨k, ⟨h1, h2⟩, h3⟩
        have hd : dyadicBelow n s = c k := (dyadicBelow_eq_iff hs0).2 ⟨h1, h3⟩
        rw [hd]
        exact h2
    · simp only [hy, not_false_eq_true, true_and, ↓reduceIte]
      constructor
      · intro h0
        exact Or.inr h0
      · rintro (⟨k, ⟨h1, -⟩, h3⟩ | h0)
        · exfalso
          refine hy ⟨lt_of_le_of_lt (WithTop.coe_le_coe.2 zero_le) h1, ?_⟩
          exact ne_top_of_le_ne_top WithTop.coe_ne_top h3
        · exact h0
  rw [e]
  refine MeasurableSet.union (MeasurableSet.iUnion fun k => ?_) (MeasurableSet.inter ?_ ?_)
  · refine MeasurableSet.inter (measurableSet_preMarkSet _ ?_) ?_
    · exact (measurable_snd.eval (a := c k)) hB
    · exact measurableSet_le measurable_fst_preMarkSigma measurable_const
  · refine MeasurableSet.compl (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt measurable_const measurable_fst_preMarkSigma
    · exact (measurableSet_singleton _).compl.preimage measurable_fst_preMarkSigma
  · by_cases h0 : (0 : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)) ∈ B
    · simp only [h0, ofPred_true, MeasurableSet.univ]
    · simp only [h0, ofPred_false, MeasurableSet.empty]

/-- The left limit of a history at its stop, along the dyadic times below it. -/
def histEnd (y : TwoSeedHist) : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) := limUnder atTop fun n => dyadicVal n y

theorem measurable_histEnd : Measurable[preMarkSigma] histEnd :=
  (@StronglyMeasurable.limUnder _ _ _ preMarkSigma _ _ atTop _ _ _ _
    fun n => (measurable_dyadicVal n).stronglyMeasurable).measurable

/-- **The reconstruction of a history from its pre-stop marks**: the recorded values before the stop, and the left
limit at the stop afterwards. -/
def histRecon (y : TwoSeedHist) : TwoSeedHist :=
  (y.1, fun q => if ((q : ℝ≥0) : WithTop ℝ≥0) < y.1 then y.2 q else histEnd y)

theorem measurable_histRecon :
    @Measurable _ _ preMarkSigma inferInstance histRecon := by
  classical
  refine Measurable.prodMk (m := preMarkSigma) measurable_fst_preMarkSigma ?_
  refine (@measurable_pi_iff _ _ _ preMarkSigma _ _).2 fun q => ?_
  intro B hB
  have e : (fun y : TwoSeedHist => if ((q : ℝ≥0) : WithTop ℝ≥0) < y.1 then y.2 q else histEnd y) ⁻¹' B =
      preMarkSet q {z | z.2 q ∈ B} ∪ ({y : TwoSeedHist | ((q : ℝ≥0) : WithTop ℝ≥0) < y.1}ᶜ ∩ histEnd ⁻¹' B) := by
    ext y
    simp only [mem_preimage, preMarkSet, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, truncH, min_self]
    by_cases hq : ((q : ℝ≥0) : WithTop ℝ≥0) < y.1
    · simp only [hq, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
    · simp only [hq, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
  rw [e]
  exact (measurableSet_preMarkSet q ((measurable_snd.eval (a := q)) hB)).union
    ((measurableSet_lt_fst q).compl.inter (measurable_histEnd hB))

/-- **A regular history is reconstructed from its marks.** -/
theorem histRecon_tsOf {S₀ : ℝ≥0} (hS₀ : 0 < S₀) {X : ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)}
    (hX : ContinuousOn X (Iic S₀)) : histRecon (tsOf S₀ X) = tsOf S₀ X := by
  classical
  have hval : ∀ n, dyadicVal n (tsOf S₀ X) = X (dyadicBelow n S₀) := fun n => by
    have h1 : (0 < ((S₀ : ℝ≥0) : WithTop ℝ≥0) ∧ ((S₀ : ℝ≥0) : WithTop ℝ≥0) ≠ ⊤) :=
      ⟨WithTop.coe_lt_coe.2 hS₀, WithTop.coe_ne_top⟩
    unfold dyadicVal
    split_ifs with hc
    · simp only [tsOf, WithTop.untopD_coe, min_eq_left (dyadicBelow_lt (n := n) hS₀).le]
    · exact absurd h1 hc
  have hlim : Tendsto (fun n => ((dyadicBelow n S₀ : ℚ≥0) : ℝ≥0)) atTop (𝓝[Iic S₀] S₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (dyadicBelow_lt hS₀).le⟩
    have hp : Tendsto (fun n : ℕ => (1 : ℝ≥0) / 2 ^ n) atTop (𝓝 0) := by
      have := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ≥0)) (by norm_num)
      simpa only [one_div, inv_pow] using this
    have hlow : Tendsto (fun n : ℕ => S₀ - 1 / 2 ^ n) atTop (𝓝 S₀) := by
      simpa only [tsub_zero] using (tendsto_const_nhds (x := S₀)).sub hp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
      fun n => (dyadicBelow_lt hS₀).le
    exact tsub_le_iff_right.2 (lt_dyadicBelow_add S₀)
  have hend : histEnd (tsOf S₀ X) = X S₀ := by
    refine Tendsto.limUnder_eq ?_
    simp only [hval]
    exact (hX S₀ (Set.mem_Iic.2 le_rfl)).tendsto.comp hlim
  refine Prod.ext rfl (funext fun q => ?_)
  by_cases hq : ((q : ℝ≥0) : WithTop ℝ≥0) < ((S₀ : ℝ≥0) : WithTop ℝ≥0)
  · simp only [histRecon, tsOf, hq, ↓reduceIte]
  · have hq' : S₀ ≤ (q : ℝ≥0) := by
      rw [not_lt] at hq
      exact WithTop.coe_le_coe.1 hq
    simp only [histRecon, hq, ↓reduceIte, tsOf, min_eq_right hq']
    exact hend

end LocalExt

end InteractingSLE
