/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Law

/-!
# Proposition GB6: measurability of the word conditions and of the decoded drivers

Packet PROVE-GB6D, the measurability layer of GB6's restart variable (part 1). The restart variable is
`X = (chart field, canonical driver code, junctions)`; transferring almost sure statements between `P` and the
conditional laws needs the events involved to be measurable:

* `BoundaryWord.measurable_index`, `measurable_fn`, `measurableSet_mem_jumps`: the boundary function of a word at a
  fixed point is a measurable function of the word;
* `exists_rat_fn_eq`: a piecewise-constant word takes its value at a non-jump point also at nearby rationals, which
  reduces the data conditions `IsGB6AdmData`, `IsGB6TailData` to countably many points
  (`measurableSet_isGB6AdmData`, `measurableSet_isGB6TailData`);
* the decoded drivers `drvDec`, `drvDecTop`: measurable, continuous (before the lifetime, resp. everywhere), and
  matching their codes (`isDriverCodeMatch_drvDec`, `isDriverCodeMatch_drvDecTop`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Sec2.Assembly

/-! ### The boundary function is measurable in the word -/

theorem measurable_index (y : ℝ) : Measurable fun c : BoundaryWord => c.index y := by
  have e : (fun c : BoundaryWord => c.index y) =
      fun c => ∑ i ∈ Finset.range c.1, (if c.2.1 i < y then 1 else 0 : ℕ) := by
    funext c
    simp only [BoundaryWord.index, Finset.card_filter]
  rw [e]
  refine measurable_from_prod_countable_right fun n => ?_
  show Measurable fun q : (ℕ → ℝ) × (ℕ → ℝ) => ∑ i ∈ Finset.range n, (if q.1 i < y then 1 else 0 : ℕ)
  refine Finset.measurable_sum (M := ℕ) _ fun i _ => Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt ((measurable_pi_apply i).comp measurable_fst) measurable_const

theorem measurable_fn (y : ℝ) : Measurable fun c : BoundaryWord => c.fn y := by
  have hg : Measurable fun q : (ℕ → ℝ) × ℕ => q.1 q.2 :=
    measurable_from_prod_countable_left fun k => measurable_pi_apply k
  exact hg.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_index y))

theorem measurableSet_mem_jumps (y : ℝ) : MeasurableSet {c : BoundaryWord | y ∈ c.jumps} := by
  have e : {c : BoundaryWord | y ∈ c.jumps} = ⋃ i : ℕ, {c : BoundaryWord | i < c.1 ∧ c.2.1 i = y} := by
    ext c
    simp only [mem_ofPred_eq, BoundaryWord.mem_jumps, mem_iUnion]
  rw [e]
  refine MeasurableSet.iUnion fun i => ?_
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_eq_fun ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) measurable_const)

/-- **A word takes its value at a non-jump point also at nearby rationals** (off its jumps). -/
theorem exists_rat_fn_eq (c : BoundaryWord) {y a b : ℝ} (hy : y ∉ c.jumps) (hay : a < y) (hyb : y < b) :
    ∃ q : ℚ, a < q ∧ (q : ℝ) < b ∧ (q : ℝ) ∉ c.jumps ∧ c.fn q = c.fn y := by
  have hI : ∀ᶠ y' in 𝓝 y, c.index y' = c.index y := BoundaryWord.eventually_index_eq hy
  have hJ : ∀ᶠ y' in 𝓝 y, y' ∉ c.jumps :=
    (c.jumps.finite_toSet.isClosed.isOpen_compl).mem_nhds (show y ∈ ((c.jumps : Set ℝ))ᶜ from hy)
  have hab : ∀ᶠ y' in 𝓝 y, a < y' ∧ y' < b := (Ioo_mem_nhds hay hyb)
  obtain ⟨O, hO, hOo, hyO⟩ := mem_nhds_iff.1 (hI.and (hJ.and hab))
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hOo ⟨y, hyO⟩
  obtain ⟨hqi, hqj, hqa, hqb⟩ := hO hq
  exact ⟨q, hqa, hqb, hqj, by simp only [BoundaryWord.fn, hqi]⟩

theorem measurableSet_isGB6AdmData (κ : ℝ) : MeasurableSet {c : BoundaryWord | IsGB6AdmData κ c} := by
  have e : {c : BoundaryWord | IsGB6AdmData κ c} =
      (⋂ q : ℚ, {c : BoundaryWord | 0 < (q : ℝ) → (q : ℝ) ∉ c.jumps → -bigLambda κ < c.fn q}) ∩
        ⋂ q : ℚ, {c : BoundaryWord | (q : ℝ) < 0 → (q : ℝ) ∉ c.jumps → c.fn q < bigLambda κ} := by
    ext c
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, IsGB6AdmData]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun q => h1 q, fun q => h2 q⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
      · obtain ⟨q, hq0, -, hqJ, hq⟩ := exists_rat_fn_eq c hyJ hy (lt_add_one y)
        rw [← hq]; exact h1 q hq0 hqJ
      · obtain ⟨q, -, hq0, hqJ, hq⟩ := exists_rat_fn_eq c hyJ (sub_one_lt y) hy
        rw [← hq]; exact h2 q hq0 hqJ
  rw [e]
  have hJ : ∀ q : ℚ, Measurable fun c : BoundaryWord => (q : ℝ) ∉ c.jumps := fun q =>
    measurableSet_setOfPred.1 (measurableSet_mem_jumps (q : ℝ)).compl
  refine (MeasurableSet.iInter fun q => measurableSet_setOfPred.2 ?_).inter
    (MeasurableSet.iInter fun q => measurableSet_setOfPred.2 ?_)
  · exact (measurableSet_setOfPred.1 (measurableSet_lt (measurable_const (a := (0 : ℝ)))
      (measurable_const (a := (q : ℝ))))).imp ((hJ q).imp
        (measurableSet_setOfPred.1 (measurableSet_lt measurable_const (measurable_fn _))))
  · exact (measurableSet_setOfPred.1 (measurableSet_lt (measurable_const (a := (q : ℝ)))
      (measurable_const (a := (0 : ℝ))))).imp ((hJ q).imp
        (measurableSet_setOfPred.1 (measurableSet_lt (measurable_fn _) measurable_const)))

theorem measurableSet_isGB6TailData (κ : ℝ) :
    MeasurableSet {p : BoundaryWord × ℝ × ℝ | IsGB6TailData κ p.1 p.2.1 p.2.2} := by
  have e : {p : BoundaryWord × ℝ × ℝ | IsGB6TailData κ p.1 p.2.1 p.2.2} =
      {p : BoundaryWord × ℝ × ℝ | p.2.1 < 0} ∩ {p : BoundaryWord × ℝ × ℝ | 0 < p.2.2} ∩
        (⋂ q : ℚ, {p : BoundaryWord × ℝ × ℝ | p.2.2 < q → (q : ℝ) ∉ p.1.jumps → tailLevel κ ≤ p.1.fn q}) ∩
        ⋂ q : ℚ, {p : BoundaryWord × ℝ × ℝ | (q : ℝ) < p.2.1 → (q : ℝ) ∉ p.1.jumps → p.1.fn q ≤ -tailLevel κ} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, IsGB6TailData]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨⟨h1, h2⟩, fun q => h3 q⟩, fun q => h4 q⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      refine ⟨h1, h2, fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
      · obtain ⟨q, hq0, -, hqJ, hq⟩ := exists_rat_fn_eq p.1 hyJ hy (lt_add_one y)
        rw [← hq]; exact h3 q hq0 hqJ
      · obtain ⟨q, -, hq0, hqJ, hq⟩ := exists_rat_fn_eq p.1 hyJ (sub_one_lt y) hy
        rw [← hq]; exact h4 q hq0 hqJ
  have hJ : ∀ q : ℚ, Measurable fun p : BoundaryWord × ℝ × ℝ => (q : ℝ) ∉ p.1.jumps := fun q =>
    measurableSet_setOfPred.1 (measurable_fst (measurableSet_mem_jumps (q : ℝ))).compl
  have hf : ∀ q : ℚ, Measurable fun p : BoundaryWord × ℝ × ℝ => p.1.fn q := fun q =>
    (measurable_fn _).comp measurable_fst
  rw [e]
  refine (((measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))).inter
    (MeasurableSet.iInter fun q => measurableSet_setOfPred.2 ?_)).inter
    (MeasurableSet.iInter fun q => measurableSet_setOfPred.2 ?_)
  · exact (measurableSet_setOfPred.1 (measurableSet_lt (measurable_snd.comp measurable_snd)
      measurable_const)).imp ((hJ q).imp (measurableSet_setOfPred.1 (measurableSet_le measurable_const (hf q))))
  · exact (measurableSet_setOfPred.1 (measurableSet_lt measurable_const
      (measurable_fst.comp measurable_snd))).imp ((hJ q).imp
        (measurableSet_setOfPred.1 (measurableSet_le (hf q) measurable_const)))

/-! ### Decoded drivers -/

theorem measurableSet_isGoodDrvCode : MeasurableSet {p : PCode × ℝ≥0∞ | IsGoodDrvCode p} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun n => Measurable.forall fun k => ?_)
  refine (measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_snd)).imp ?_
  exact measurableSet_setOfPred.1 (measurable_fst (measurableSet_UC (dyad n k)))

theorem measurableSet_uc_all : MeasurableSet {p : PCode × ℝ≥0∞ | ∀ N : ℕ, UC p.1 N} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun N => ?_)
  exact measurableSet_setOfPred.1 (measurable_fst (measurableSet_UC N))

theorem measurable_drvDec (t : ℝ≥0) : Measurable fun p : PCode × ℝ≥0∞ => drvDec p t := by
  unfold drvDec
  exact Measurable.ite (measurableSet_isGoodDrvCode.inter (measurableSet_lt measurable_const measurable_snd))
    (measurable_dec.comp (measurable_fst.prodMk measurable_const)) (measurable_code 0 0 |>.comp measurable_fst)

theorem measurable_drvDecTop (t : ℝ≥0) : Measurable fun p : PCode × ℝ≥0∞ => drvDecTop p t := by
  unfold drvDecTop
  exact Measurable.ite measurableSet_uc_all
    (measurable_dec.comp (measurable_fst.prodMk measurable_const)) (measurable_code 0 0 |>.comp measurable_fst)

theorem drvDec_of_good {p : PCode × ℝ≥0∞} (hp : IsGoodDrvCode p) (hp0 : 0 < p.2) (t : ℝ≥0) :
    drvDec p t = dec p.1 t := by
  simp only [drvDec, hp, hp0, and_self, ↓reduceIte]

theorem drvDecTop_of_uc {p : PCode × ℝ≥0∞} (hp : ∀ N : ℕ, UC p.1 N) (t : ℝ≥0) :
    drvDecTop p t = dec p.1 t := by
  simp only [drvDecTop, hp, implies_true, ↓reduceIte]

theorem continuousOn_drvDec (p : PCode × ℝ≥0∞) : ContinuousOn (drvDec p) {t | (t : ℝ≥0∞) < p.2} := by
  by_cases hp : IsGoodDrvCode p ∧ 0 < p.2
  · intro t ht
    obtain ⟨n, k, htd, hd⟩ := exists_dyad_btwn ht
    have hc := (hp.1 n k hd).continuousOn
    have hmem : Iic (dyad n k) ∈ 𝓝 t := Iic_mem_nhds htd
    have hca : ContinuousAt (dec p.1) t := (hc t (mem_Iic.2 htd.le)).continuousAt hmem
    rw [show drvDec p = dec p.1 from funext (drvDec_of_good hp.1 hp.2)]
    exact hca.continuousWithinAt
  · rw [show drvDec p = fun _ => p.1 0 0 from funext fun t => by simp only [drvDec, hp, ↓reduceIte]]
    exact continuousOn_const

theorem continuous_drvDecTop (p : PCode × ℝ≥0∞) : Continuous (drvDecTop p) := by
  by_cases hp : ∀ N : ℕ, UC p.1 N
  · rw [show drvDecTop p = dec p.1 from funext (drvDecTop_of_uc hp), continuous_iff_continuousAt]
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt t
    exact ((hp N).continuousOn t (mem_Iic.2 hN.le)).continuousAt (Iic_mem_nhds hN)
  · rw [show drvDecTop p = fun _ => p.1 0 0 from funext fun t => by simp only [drvDecTop, hp, ↓reduceIte]]
    exact continuous_const

theorem dyad_zero_zero' : dyad 0 0 = 0 := by simp [dyad]

/-- A good code is matched by its decoded driver, with its own lifetime. -/
theorem isDriverCodeMatch_drvDec {p : PCode × ℝ≥0∞} (hp : IsGoodDrvCode p) :
    IsDriverCodeMatch p (drvDec p) p.2 := by
  rcases eq_zero_or_pos p.2 with hp0 | hp0
  · refine ⟨rfl, ?_, fun n k hd => absurd hd (by rw [hp0]; exact not_lt_zero)⟩
    simp only [drvDec, hp0, lt_irrefl, and_false, ↓reduceIte]
  refine ⟨rfl, ?_, fun n k hd => ?_⟩
  · have h00 : ((dyad 0 0 : ℝ≥0) : ℝ≥0∞) < p.2 := by rw [dyad_zero_zero']; exact_mod_cast hp0
    rw [drvDec_of_good hp hp0, ← dyad_zero_zero']
    exact (hp 0 0 h00).dec_dyad le_rfl
  · rw [drvDec_of_good hp hp0]
    exact (hp n k hd).dec_dyad le_rfl

/-- A code with infinite lifetime, uniformly continuous on every `[0, N]`, is matched by `drvDecTop`. -/
theorem isDriverCodeMatch_drvDecTop {p : PCode × ℝ≥0∞} (hp : ∀ N : ℕ, UC p.1 N) (hp2 : p.2 = ⊤) :
    IsDriverCodeMatch p (drvDecTop p) ⊤ := by
  refine ⟨hp2.symm, ?_, fun n k _ => ?_⟩
  · rw [drvDecTop_of_uc hp, ← dyad_zero_zero']
    exact (hp 1).dec_dyad (by rw [dyad_zero_zero']; exact zero_le)
  · rw [drvDecTop_of_uc hp]
    obtain ⟨N, hN⟩ := exists_nat_ge (dyad n k)
    exact (hp N).dec_dyad (by exact_mod_cast hN)

/-- A good code with infinite lifetime is uniformly continuous on every `[0, N]`. -/
theorem uc_of_good_top {p : PCode × ℝ≥0∞} (hp : IsGoodDrvCode p) (hp2 : p.2 = ⊤) (N : ℕ) : UC p.1 N := by
  have h := hp 0 N (by rw [hp2]; exact ENNReal.coe_lt_top)
  have e : dyad 0 N = (N : ℝ≥0) := by simp [dyad]
  rwa [e] at h

/-- On a good code with infinite lifetime the two decodings agree. -/
theorem drvDecTop_eq_drvDec {p : PCode × ℝ≥0∞} (hp : IsGoodDrvCode p) (hp2 : p.2 = ⊤) :
    drvDecTop p = drvDec p := by
  funext t
  rw [drvDecTop_of_uc (uc_of_good_top hp hp2), drvDec_of_good hp (by rw [hp2]; exact ENNReal.zero_lt_top)]

end GB6

end Supp8

end InteractingSLE
