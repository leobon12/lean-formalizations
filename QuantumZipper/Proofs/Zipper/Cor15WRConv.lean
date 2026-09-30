import QuantumZipper.Proofs.Zipper.Cor15GoodWeld

/-!
# Corollary 1.5(a), `t > 0`: measurable certificates on `b1Data`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5
(pp. 17–18; no proof in the paper). Task COR15-WR.

* `bdryConvAE_fieldOf_iff`: `BdryConvAE` only sees the dyadic folded circles recorded by
  `coordsFull`, up to an additive constant, so it holds for `x` iff it holds for `fieldOf x`;
* `measurableSet_bdryConvAE_fromC`: it is a measurable condition on the coordinates;
* `AtomQ`: a countable (measurable) dyadic form of atomlessness of the boundary measure, with
  `measure_singleton_eq_zero_of_atomQ` and, conversely, `atomQ_of_atomless` (compactness).

Own elementary arguments (cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull

theorem radius_eq_int_div (k : ℕ) : radius k = ((1 : ℤ) : ℝ) / (2 : ℝ) ^ k := by
  rw [radius, inv_pow]; push_cast; rw [one_div]

theorem fieldOf_apply_fc (x : FieldSample) (n k : ℕ) (z : ℂ) :
    fieldOf x (foldedCircle (dyadicRoundC n z) (radius k)) =
      x (foldedCircle (dyadicRoundC n z) (radius k)) - x (foldedCircle 0 1) := by
  have h := coordsFull_apply_eq (E1.coordsFull_fromC (nrm x)) n z 1 one_pos k
  rw [← radius_eq_int_div] at h
  show E1.fromC (coordsFull (nrm x)) _ = _
  rw [h]
  simp [nrm, addConst, measure_univ]
  ring

theorem bdryConvAE_fieldOf_iff (x : FieldSample) : BdryConvAE (fieldOf x) ↔ BdryConvAE x := by
  unfold BdryConvAE
  simp only [fieldOf_apply_fc]
  refine forall_congr' fun k => Filter.eventually_congr (Eventually.of_forall fun s => ?_)
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l + x (foldedCircle 0 1), by simpa using hl.add_const (x (foldedCircle 0 1))⟩
  · rintro ⟨l, hl⟩
    exact ⟨_, hl.sub_const _⟩

theorem measurable_fromC_fc (k n : ℕ) : Measurable fun p : (ℕ → ℝ) × ℝ =>
    E1.fromC p.1 (foldedCircle (dyadicRoundC n (p.2 : ℂ)) (radius k)) := by
  have e : (fun p : (ℕ → ℝ) × ℝ =>
      E1.fromC p.1 (foldedCircle (dyadicRoundC n (p.2 : ℂ)) (radius k))) =
      (fun q : (ℕ → ℝ) × ℤ => E1.fromC q.1
        (foldedCircle ⟨(q.2 : ℝ) / 2 ^ n, dyadicRound n 0⟩ (radius k))) ∘
        (fun p => (p.1, ⌊(2 : ℝ) ^ n * p.2⌋)) := by
    funext p
    simp only [Function.comp, dyadicRoundC, dyadicRound, Complex.ofReal_re, Complex.ofReal_im]
  rw [e]
  refine (measurable_from_prod_countable_left fun j => ?_).comp (measurable_fst.prodMk ?_)
  · exact (measurable_pi_apply (foldedCircle ⟨(j : ℝ) / 2 ^ n, dyadicRound n 0⟩ (radius k))).comp
      measurable_fromC
  · exact Int.measurable_floor.comp (measurable_const.mul measurable_snd)

theorem measurableSet_bdryConvAE_fromC :
    MeasurableSet {c : ℕ → ℝ | BdryConvAE (E1.fromC c)} := by
  set S : ℕ → Set ((ℕ → ℝ) × ℝ) := fun k => {p | ∃ l, Tendsto (fun n =>
    E1.fromC p.1 (foldedCircle (dyadicRoundC n (p.2 : ℂ)) (radius k))) atTop (𝓝 l)}
  have hS : ∀ k, MeasurableSet (S k) := fun k =>
    StronglyMeasurable.measurableSet_exists_tendsto
      (fun n => (measurable_fromC_fc k n).stronglyMeasurable)
  have e : {c : ℕ → ℝ | BdryConvAE (E1.fromC c)} =
      ⋂ k, (fun c => volume (Prod.mk c ⁻¹' (S k)ᶜ)) ⁻¹' {0} := by
    ext c
    simp only [mem_setOf_eq, BdryConvAE, ae_iff, mem_iInter, mem_preimage, mem_singleton_iff]
    rfl
  rw [e]
  exact MeasurableSet.iInter fun k =>
    measurable_measure_prodMk_left (hS k).compl (measurableSet_singleton 0)

/-! ### Atomlessness, countably -/

/-- Countable (measurable) form of atomlessness of the boundary measure, via dyadic intervals. -/
def AtomQ (γ : ℝ) (y : FieldSample) : Prop :=
  ∀ n m : ℕ, ∃ k : ℕ, ∀ j : ℤ, |j| ≤ (m : ℤ) * 2 ^ k →
    Thm14WDG.mIcc γ ((j : ℝ) / 2 ^ k) (((j : ℝ) + 1) / 2 ^ k) y ≤ ((n : ℝ≥0∞) + 1)⁻¹

theorem measurableSet_atomQ (γ : ℝ) : MeasurableSet {y : FieldSample | AtomQ γ y} := by
  have e : {y : FieldSample | AtomQ γ y} = ⋂ n : ℕ, ⋂ m : ℕ, ⋃ k : ℕ, ⋂ j : ℤ,
      {y | |j| ≤ (m : ℤ) * 2 ^ k →
        Thm14WDG.mIcc γ ((j : ℝ) / 2 ^ k) (((j : ℝ) + 1) / 2 ^ k) y ≤ ((n : ℝ≥0∞) + 1)⁻¹} := by
    ext y; simp [AtomQ]
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun m => MeasurableSet.iUnion
    fun k => MeasurableSet.iInter fun j => ?_
  by_cases h : |j| ≤ (m : ℤ) * 2 ^ k
  · simp only [h, true_implies]
    exact measurableSet_le (Thm14WDG.measurable_mIcc _ _ _) measurable_const
  · simp [h]

theorem measure_singleton_eq_zero_of_atomQ {γ : ℝ} {y : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ y) ν) (h : AtomQ γ y) (s : ℝ) : ν {s} = 0 := by
  obtain ⟨m, hm⟩ := exists_nat_ge (|s| + 1)
  have hb : ∀ n : ℕ, ν {s} ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    obtain ⟨k, hk⟩ := h n m
    set j := ⌊(2 : ℝ) ^ k * s⌋
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hj1 : (j : ℝ) ≤ 2 ^ k * s := Int.floor_le _
    have hj2 : 2 ^ k * s < j + 1 := Int.lt_floor_add_one _
    have hjm : |j| ≤ (m : ℤ) * 2 ^ k := by
      have : |(j : ℝ)| ≤ (m : ℝ) * 2 ^ k := by
        rw [abs_le]
        have hs := abs_le.1 (le_refl |s|)
        constructor <;> nlinarith [neg_abs_le s, le_abs_self s]
      exact_mod_cast this
    have hsI : s ∈ Icc ((j : ℝ) / 2 ^ k) (((j : ℝ) + 1) / 2 ^ k) := by
      constructor
      · rw [div_le_iff₀ h2]; linarith
      · rw [le_div_iff₀ h2]; linarith
    calc ν {s} ≤ ν (Icc ((j : ℝ) / 2 ^ k) (((j : ℝ) + 1) / 2 ^ k)) :=
          measure_mono (singleton_subset_iff.2 hsI)
      _ = _ := (Thm14WDG.mIcc_eq hν _ _).symm
      _ ≤ _ := hk j hjm
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
  have := hb n
  have hle : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
  exact absurd (this.trans hle) (not_le.2 hn)

theorem atomQ_of_atomless {γ : ℝ} {y : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ y) ν) (h : ∀ s, ν {s} = 0) : AtomQ γ y := by
  have := hν.1
  intro n m
  by_contra hcon
  push Not at hcon
  choose j hj hlt using hcon
  set x : ℕ → ℝ := fun k => (j k : ℝ) / 2 ^ k
  have hx : ∀ k, x k ∈ Icc (-(m : ℝ)) m := by
    intro k
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have : |(j k : ℝ)| ≤ (m : ℝ) * 2 ^ k := by exact_mod_cast hj k
    rw [abs_le] at this
    constructor
    · show -(m : ℝ) ≤ (j k : ℝ) / 2 ^ k
      rw [le_div_iff₀ h2]; linarith
    · show (j k : ℝ) / 2 ^ k ≤ m
      rw [div_le_iff₀ h2]; linarith
  obtain ⟨a, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hx
  have hpow : Tendsto (fun l => (1 : ℝ) / 2 ^ φ l) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).comp hφ.tendsto_atTop
    refine this.congr fun l => ?_
    simp [Function.comp, one_div, inv_pow]
  have hlow : ∀ i : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ ≤
      ν (Ioo (a - 1 / ((i : ℝ) + 1)) (a + 1 / ((i : ℝ) + 1))) := by
    intro i
    have hδ : (0 : ℝ) < 1 / ((i : ℝ) + 1) / 2 := by positivity
    have e1 := (Metric.tendsto_nhds.1 hlim) _ hδ
    have e2 := (Metric.tendsto_nhds.1 hpow) _ hδ
    obtain ⟨l, hl1, hl2⟩ := (e1.and e2).exists
    rw [Real.dist_eq] at hl1 hl2
    simp only [Function.comp, sub_zero] at hl1 hl2
    have hp : (0 : ℝ) < 1 / 2 ^ φ l := by positivity
    rw [abs_of_pos hp] at hl2
    have hsub : Icc ((j (φ l) : ℝ) / 2 ^ φ l) (((j (φ l) : ℝ) + 1) / 2 ^ φ l) ⊆
        Ioo (a - 1 / ((i : ℝ) + 1)) (a + 1 / ((i : ℝ) + 1)) := by
      intro z hz
      have hxe : ((j (φ l) : ℝ) + 1) / 2 ^ φ l = x (φ l) + 1 / 2 ^ φ l := by
        simp only [x]; ring
      rw [hxe] at hz
      have := abs_lt.1 hl1
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    calc ((n : ℝ≥0∞) + 1)⁻¹ ≤ _ := (hlt (φ l)).le
      _ = ν (Icc ((j (φ l) : ℝ) / 2 ^ φ l) (((j (φ l) : ℝ) + 1) / 2 ^ φ l)) :=
          Thm14WDG.mIcc_eq hν _ _
      _ ≤ _ := measure_mono hsub
  have hinter : ν {a} = ⨅ i : ℕ, ν (Ioo (a - 1 / ((i : ℝ) + 1)) (a + 1 / ((i : ℝ) + 1))) := by
    rw [← Icc_self, ← Thm14WDG.iInter_Ioo_eq_Icc]
    refine Antitone.measure_iInter (fun p q hpq => ?_)
      (fun _ => measurableSet_Ioo.nullMeasurableSet) ⟨0, measure_Ioo_lt_top.ne⟩
    have : 1 / ((q : ℝ) + 1) ≤ 1 / ((p : ℝ) + 1) := Nat.one_div_le_one_div hpq
    exact Ioo_subset_Ioo (by linarith) (by linarith)
  have := le_iInf hlow
  rw [← hinter, h a] at this
  exact absurd this (not_le.2 (ENNReal.inv_pos.2 (by simp)))

end Cor15Group
end QuantumZipper
