/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3IDRetarget
import InteractingSLE.Spec.ZhanGT4.A2Part3IDHull

/-!
# A.2 part 3, (I1): the code event of the retargeted noncollision

Packet PROVE-ZHAN-A2P3-ID. The two conclusions (a), (b) of `ae_gap_and_newHorizon_top`, for a word of left marks
(nearest mark `i₀`, target `k`), written as a Borel event of solution codes (`idSet`), so that they pass to every
evolution of a random word through the canonical code law (`Sec7.RandRestart.lawSetS`):

* `SepQ k w v τ q`: `q < τ` and the gap `w − v_k` is bounded below on the rational times `≤ q` (for continuous
  paths: `q` is before the separation time, `sepQ_iff`);
* `clkR k w v q`: the clock `C(q) = ∫₀^q α²/q⁴` of the target change at `−v_k(0)` of the reflected path `(−w, −v_k)`;
* `IdProp i₀ k w v τ`: every rational `SepQ` time has `w − v_{i₀}` bounded below on the rational times before it
  ((a)), and the clock is unbounded over the `SepQ` times ((b));
* **`measurableSet_idSet`** (the clock is measurable in the code: `measurable_intervalIntegral_var`, a parametric
  interval integral with a variable endpoint), `idProp_congr`;
* **`idProp_of_gap`**: (a) and (b) for the reflected path give `IdProp`;
* **`gap_of_idProp`**, **`newHorizon_top_of_idProp`**: conversely, for a path continuous before `τ`, `IdProp` gives the
  gap of the nearest mark before every separated rational time and an infinite new horizon.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2P3ID

open Sec2.Assembly Zhan.Retarget Theorem14.BR3Ref

/-! ### A parametric interval integral with a variable endpoint -/

/-- `(a, b) ↦ ∫₀ᵇ g(a, s) ds` is measurable for a jointly measurable `g`. -/
theorem measurable_intervalIntegral_var {α : Type*} [MeasurableSpace α] {g : α → ℝ → ℝ}
    (hg : Measurable fun p : α × ℝ => g p.1 p.2) :
    Measurable fun p : α × ℝ => ∫ s in (0 : ℝ)..p.2, g p.1 s := by
  have key : ∀ (lo hi : α × ℝ → ℝ), Measurable lo → Measurable hi →
      Measurable fun p : α × ℝ => ∫ s in Ioc (lo p) (hi p), g p.1 s := by
    intro lo hi hlo hhi
    set E : Set ((α × ℝ) × ℝ) := {q | lo q.1 < q.2 ∧ q.2 ≤ hi q.1} with hE
    have hEm : MeasurableSet E :=
      (measurableSet_lt (hlo.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hhi.comp measurable_fst))
    have hf : Measurable fun q : (α × ℝ) × ℝ => E.indicator (fun q => g q.1.1 q.2) q :=
      (hg.comp (measurable_fst.fst.prodMk measurable_snd)).indicator hEm
    have e : (fun p : α × ℝ => ∫ s in Ioc (lo p) (hi p), g p.1 s) =
        fun p => ∫ s, E.indicator (fun q => g q.1.1 q.2) (p, s) := by
      funext p
      rw [← integral_indicator measurableSet_Ioc]
      congr 1
    rw [e]
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have e : (fun p : α × ℝ => ∫ s in (0 : ℝ)..p.2, g p.1 s) =
      fun p => (∫ s in Ioc 0 p.2, g p.1 s) - ∫ s in Ioc p.2 0, g p.1 s := rfl
  rw [e]
  exact (key (fun _ => 0) (fun p => p.2) measurable_const measurable_snd).sub
    (key (fun p => p.2) (fun _ => 0) measurable_snd measurable_const)

/-! ### The code property -/

variable {nL : ℕ}

/-- **A separated rational time**: `q < τ` and the gap `w − v_k` is bounded below on the rational times `≤ q`. -/
def SepQ (k : Fin nL) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (τ : ℝ≥0∞) (q : ℚ≥0) : Prop :=
  (((q : ℝ≥0) : ℝ≥0∞) < τ) ∧ ∃ n : ℕ, ∀ r : ℚ≥0, r ≤ q → 1 / ((n : ℝ) + 1) ≤ w r - vL k r

/-- **The clock of the target change** at the reflected target `−v_k(0)` of the reflected path `(−w, −v_k)`. -/
def clkR (k : Fin nL) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (q : ℝ≥0) : ℝ :=
  clk (rate (-vL k 0) (fun t => -w t) (fun t => -vL k t)) q

/-- **The code property of (I1)**: (a) at every separated rational time `q`, the gap `w − v_{i₀}` of the nearest mark
is bounded below on the rational times `≤ q`; (b) the clock is unbounded over the separated rational times. -/
def IdProp (i₀ k : Fin nL) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  (∀ q : ℚ≥0, SepQ k w vL τ q → ∃ n : ℕ, ∀ r : ℚ≥0, r ≤ q → 1 / ((n : ℝ) + 1) ≤ w r - vL i₀ r) ∧
    ∀ M : ℕ, ∃ q : ℚ≥0, SepQ k w vL τ q ∧ (M : ℝ) ≤ clkR k w vL q

/-- The codes with `IdProp`. -/
def idSet (i₀ k : Fin nL) : Set (XCode nL 0) := {x | IdProp i₀ k (cw x) (cvL x) (cζ x)}

theorem measurableSet_sepQ (k : Fin nL) (q : ℚ≥0) :
    MeasurableSet {x : XCode nL 0 | SepQ k (cw x) (cvL x) (cζ x) q} := by
  have e : {x : XCode nL 0 | SepQ k (cw x) (cvL x) (cζ x) q} =
      {x | (((q : ℝ≥0) : ℝ≥0∞) < cζ x)} ∩ ⋃ n : ℕ, ⋂ r : ℚ≥0,
        ({_x | ¬ r ≤ q} ∪ {x | 1 / ((n : ℝ) + 1) ≤ cw x r - cvL x k r}) := by
    ext x
    simp only [SepQ, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, mem_union]
    refine and_congr Iff.rfl (exists_congr fun n => forall_congr' fun r => ?_)
    tauto
  rw [e]
  refine (measurableSet_lt measurable_const measurable_cζ).inter
    (MeasurableSet.iUnion fun n => MeasurableSet.iInter fun r => (MeasurableSet.const _).union ?_)
  exact measurableSet_le measurable_const (measurable_gap_at k r)

/-- The clock of the target change is measurable in the code. -/
theorem measurable_clkR (k : Fin nL) (q : ℝ≥0) : Measurable fun x : XCode nL 0 => clkR k (cw x) (cvL x) q := by
  have hG : Measurable fun p : XCode nL 0 × ℝ => gap (fun t => -cw p.1 t) (fun t => -cvL p.1 k t) p.2 := by
    simp only [gap]
    exact (measurable_cvL_real k).neg.sub measurable_cw_real.neg
  have hA : Measurable fun p : XCode nL 0 × ℝ =>
      ∫ s in (0 : ℝ)..p.2, (gap (fun t => -cw p.1 t) (fun t => -cvL p.1 k t) s ^ 2)⁻¹ :=
    measurable_intervalIntegral_var (g := fun x s => (gap (fun t => -cw x t) (fun t => -cvL x k t) s ^ 2)⁻¹)
      (hG.pow_const 2).inv
  have hx : Measurable fun p : XCode nL 0 × ℝ => -cvL p.1 k 0 := ((measurable_cvL_at k 0).comp measurable_fst).neg
  have hrate : Measurable fun p : XCode nL 0 × ℝ =>
      rate (-cvL p.1 k 0) (fun t => -cw p.1 t) (fun t => -cvL p.1 k t) p.2 := by
    simp only [rate, alpha]
    exact ((hx.mul (Real.measurable_exp.comp (measurable_const.mul hA))).pow_const 2).div (hG.pow_const 4)
  exact measurable_intervalIntegral (g := fun x s => rate (-cvL x k 0) (fun t => -cw x t) (fun t => -cvL x k t) s)
    hrate q

/-- **The code event of (I1) is Borel.** -/
theorem measurableSet_idSet (i₀ k : Fin nL) : MeasurableSet (idSet i₀ k) := by
  have e : idSet i₀ k = (⋂ q : ℚ≥0, ({x : XCode nL 0 | SepQ k (cw x) (cvL x) (cζ x) q}ᶜ ∪
      ⋃ n : ℕ, ⋂ r : ℚ≥0, ({_x | ¬ r ≤ q} ∪ {x | 1 / ((n : ℝ) + 1) ≤ cw x r - cvL x i₀ r}))) ∩
      ⋂ M : ℕ, ⋃ q : ℚ≥0, ({x : XCode nL 0 | SepQ k (cw x) (cvL x) (cζ x) q} ∩
        {x | (M : ℝ) ≤ clkR k (cw x) (cvL x) q}) := by
    ext x
    simp only [idSet, IdProp, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, mem_union, mem_compl_iff]
    refine and_congr (forall_congr' fun q => ?_) Iff.rfl
    constructor
    · intro h
      by_cases hq : SepQ k (cw x) (cvL x) (cζ x) q
      · obtain ⟨n, hn⟩ := h hq
        refine Or.inr ⟨n, fun r => ?_⟩
        by_cases hr : r ≤ q
        · exact Or.inr (hn r hr)
        · exact Or.inl hr
      · exact Or.inl hq
    · rintro (h | ⟨n, hn⟩) hq
      · exact absurd hq h
      · exact ⟨n, fun r hr => (hn r).resolve_left (not_not.2 hr)⟩
  rw [e]
  refine (MeasurableSet.iInter fun q => (measurableSet_sepQ k q).compl.union
    (MeasurableSet.iUnion fun n => MeasurableSet.iInter fun r => (MeasurableSet.const _).union ?_)).inter
    (MeasurableSet.iInter fun M => MeasurableSet.iUnion fun q => (measurableSet_sepQ k q).inter ?_)
  · exact measurableSet_le measurable_const (measurable_gap_at i₀ r)
  · exact measurableSet_le measurable_const (measurable_clkR k q)

/-! ### Congruence -/

section Congr

variable {i₀ k : Fin nL} {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {τ : ℝ≥0∞}

theorem sepQ_congr (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ ∀ i, vL i t = vL' i t) {q : ℚ≥0}
    (hq : SepQ k w vL τ q) : SepQ k w' vL' τ q := by
  obtain ⟨hqτ, n, hn⟩ := hq
  refine ⟨hqτ, n, fun r hr => ?_⟩
  have hrτ : ((r : ℝ≥0) : ℝ≥0∞) < τ :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (by exact_mod_cast hr)) hqτ
  rw [← (h r hrτ).1, ← (h r hrτ).2 k]
  exact hn r hr

theorem clkR_congr (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ ∀ i, vL i t = vL' i t) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < τ) : clkR k w vL q = clkR k w' vL' q := by
  have hpt : ∀ s ∈ uIcc (0 : ℝ) q,
      gap (fun t => -w t) (fun t => -vL k t) s = gap (fun t => -w' t) (fun t => -vL' k t) s := by
    intro s hs
    rw [uIcc_of_le q.coe_nonneg] at hs
    have hs' : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < τ :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) hq
    simp only [gap, (h _ hs').1, (h _ hs').2 k]
  have hα : ∀ s ∈ uIcc (0 : ℝ) q, (∫ u in (0 : ℝ)..s, (gap (fun t => -w t) (fun t => -vL k t) u ^ 2)⁻¹) =
      ∫ u in (0 : ℝ)..s, (gap (fun t => -w' t) (fun t => -vL' k t) u ^ 2)⁻¹ := fun s hs =>
    intervalIntegral.integral_congr fun u hu => by
      have hsub : uIcc (0 : ℝ) s ⊆ uIcc 0 q := Set.uIcc_subset_uIcc Set.left_mem_uIcc hs
      show (gap (fun t => -w t) (fun t => -vL k t) u ^ 2)⁻¹ = (gap (fun t => -w' t) (fun t => -vL' k t) u ^ 2)⁻¹
      rw [hpt u (hsub hu)]
  have h0 : vL k 0 = vL' k 0 := (h 0 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 zero_le) hq)).2 k
  unfold clkR clk
  refine intervalIntegral.integral_congr fun s hs => ?_
  simp only [rate, alpha, h0, hpt s hs, hα s hs]

theorem idProp_congr (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ ∀ i, vL i t = vL' i t)
    (hP : IdProp i₀ k w vL τ) : IdProp i₀ k w' vL' τ := by
  have h' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w' t = w t ∧ ∀ i, vL' i t = vL i t := fun t ht =>
    ⟨(h t ht).1.symm, fun i => ((h t ht).2 i).symm⟩
  refine ⟨fun q hq => ?_, fun M => ?_⟩
  · obtain ⟨n, hn⟩ := hP.1 q (sepQ_congr h' hq)
    refine ⟨n, fun r hr => ?_⟩
    have hrτ : ((r : ℝ≥0) : ℝ≥0∞) < τ :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (by exact_mod_cast hr)) hq.1
    rw [← (h r hrτ).1, ← (h r hrτ).2 i₀]
    exact hn r hr
  · obtain ⟨q, hq, hM⟩ := hP.2 M
    exact ⟨q, sepQ_congr h hq, by rw [← clkR_congr h hq.1]; exact hM⟩

end Congr

/-! ### `IdProp` and the separation time along a continuous path -/

section Path

variable {i₀ k : Fin nL} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- A continuous positive function on `[0, q]` is bounded below by some `1/(n + 1)` at the rational times. -/
theorem exists_nat_le_of_pos {f : ℝ≥0 → ℝ} {q : ℝ≥0} (hf : ContinuousOn f (Icc 0 q))
    (hpos : ∀ t ∈ Icc 0 q, 0 < f t) : ∃ n : ℕ, ∀ t ∈ Icc 0 q, 1 / ((n : ℝ) + 1) ≤ f t := by
  obtain ⟨ε, hε, hle⟩ := Sec7.exists_pos_le_of_continuousOn_Icc hf hpos
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact ⟨n, fun t ht => hn.le.trans (hle t ht)⟩

theorem continuousOn_Icc_of_lt {f : ℝ≥0 → ℝ} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < τ}) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < τ) : ContinuousOn f (Icc 0 q) :=
  hf.mono fun _ ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hq

/-- **A separated rational time is before the separation time** of the reflected path. -/
theorem lt_sepTime_of_sepQ (hw : ContinuousOn w {t | (t : ℝ≥0∞) < τ})
    (hvk : ContinuousOn (vL k) {t | (t : ℝ≥0∞) < τ}) {q : ℚ≥0} (hq : SepQ k w vL τ q) :
    (((q : ℝ≥0) : ℝ≥0∞)) < sepTime (fun t => -w t) (fun t => -vL k t) τ := by
  obtain ⟨hqτ, n, hn⟩ := hq
  have hc : ContinuousOn (fun s => -vL k s - -w s) {s | (s : ℝ≥0∞) < τ} := hvk.neg.sub hw.neg
  refine lt_sepTime_of_forall hc hqτ fun s hs => ?_
  have hb := le_of_forall_rat_le (f := fun t => w t - vL k t)
    ((continuousOn_Icc_of_lt hw hqτ).sub (continuousOn_Icc_of_lt hvk hqτ))
    (fun r hr => hn r (by exact_mod_cast hr)) hs
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
  linarith

/-- **Before the separation time every rational time is separated.** -/
theorem sepQ_of_lt_sepTime (hw : ContinuousOn w {t | (t : ℝ≥0∞) < τ})
    (hvk : ContinuousOn (vL k) {t | (t : ℝ≥0∞) < τ}) {q : ℚ≥0}
    (hq : (((q : ℝ≥0) : ℝ≥0∞)) < sepTime (fun t => -w t) (fun t => -vL k t) τ) : SepQ k w vL τ q := by
  have hqτ : (((q : ℝ≥0) : ℝ≥0∞)) < τ := hq.trans_le (sepTime_le _ _ _)
  obtain ⟨n, hn⟩ := exists_nat_le_of_pos (f := fun t => w t - vL k t)
    ((continuousOn_Icc_of_lt hw hqτ).sub (continuousOn_Icc_of_lt hvk hqτ)) fun t ht => by
      have := lt_of_lt_sepTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hq)
      linarith
  exact ⟨hqτ, n, fun r hr => hn r ⟨zero_le, by exact_mod_cast hr⟩⟩

/-- `SepUpTo` for the reflected path before its separation time. -/
theorem sepUpTo_reflect (hw : ContinuousOn w {t | (t : ℝ≥0∞) < τ})
    (hvk : ContinuousOn (vL k) {t | (t : ℝ≥0∞) < τ}) :
    SepUpTo (fun t => -w t) (fun t => -vL k t) (sepTime (fun t => -w t) (fun t => -vL k t) τ) := by
  intro S hS0 hST
  have hSτ : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) < τ := hST.trans_le (sepTime_le _ _ _)
  have hsub : ∀ s ∈ Icc (0 : ℝ) S, ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < τ := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hs.2)) hSτ
  refine ⟨hS0, ?_, ?_, fun s hs => ?_⟩
  · exact (hw.neg.comp continuous_real_toNNReal.continuousOn fun s hs => hsub s hs)
  · exact (hvk.neg.comp continuous_real_toNNReal.continuousOn fun s hs => hsub s hs)
  · have := lt_of_lt_sepTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hs.2)) hST)
    simp only [gap]
    linarith

/-- A real time before a point of `ℝ≥0∞` has a rational time between them. -/
theorem exists_nnrat_btwn {S : ℝ≥0} {T : ℝ≥0∞} (h : (S : ℝ≥0∞) < T) :
    ∃ q : ℚ≥0, S < (q : ℝ≥0) ∧ (((q : ℝ≥0) : ℝ≥0∞)) < T := by
  obtain ⟨S', hSS', hS'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
  have h1 : (S : ℝ) < S' := by exact_mod_cast hSS'
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn h1
  have hr0 : (0 : ℝ) ≤ r := S.coe_nonneg.trans hr1.le
  have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast hr0
  have hq : ((r.toNNRat : ℝ≥0) : ℝ) = r := by
    rw [← cast_toNNRat' r hr0']; rfl
  refine ⟨r.toNNRat, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, hq]; exact hr1
  · refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hS'T
    rw [← NNReal.coe_le_coe, hq]; exact hr2.le

/-- **(a) and (b) give `IdProp`.** -/
theorem idProp_of_gap (hw : ContinuousOn w {t | (t : ℝ≥0∞) < τ}) (hvk : ContinuousOn (vL k) {t | (t : ℝ≥0∞) < τ})
    (hv0 : ContinuousOn (vL i₀) {t | (t : ℝ≥0∞) < τ}) (hxk : vL k 0 < 0)
    (ha : ∀ t : ℝ≥0, (t : ℝ≥0∞) < sepTime (fun t => -w t) (fun t => -vL k t) τ → vL i₀ t < w t)
    (hb : newHorizon (-vL k 0) (fun t => -w t) (fun t => -vL k t)
      (sepTime (fun t => -w t) (fun t => -vL k t) τ) = ⊤) :
    IdProp i₀ k w vL τ := by
  refine ⟨fun q hq => ?_, fun M => ?_⟩
  · have hqs := lt_sepTime_of_sepQ hw hvk hq
    have hqτ := hq.1
    obtain ⟨n, hn⟩ := exists_nat_le_of_pos (f := fun t => w t - vL i₀ t)
      ((continuousOn_Icc_of_lt hw hqτ).sub (continuousOn_Icc_of_lt hv0 hqτ)) fun t ht => by
        have := ha t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hqs)
        linarith
    exact ⟨n, fun r hr => hn r ⟨zero_le, by exact_mod_cast hr⟩⟩
  · have hxk' : 0 < -vL k 0 := by linarith
    have hM : ENNReal.ofReal ((M : ℝ) + 1) < newHorizon (-vL k 0) (fun t => -w t) (fun t => -vL k t)
        (sepTime (fun t => -w t) (fun t => -vL k t) τ) := by rw [hb]; exact ENNReal.ofReal_lt_top
    obtain ⟨S, hS⟩ := lt_iSup_iff.1 hM
    obtain ⟨hST, hS2⟩ := lt_iSup_iff.1 hS
    have hclk : (M : ℝ) + 1 < clk (rate (-vL k 0) (fun t => -w t) (fun t => -vL k t)) S :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 hS2
    obtain ⟨q, hSq, hqT⟩ := exists_nnrat_btwn hST
    refine ⟨q, sepQ_of_lt_sepTime hw hvk hqT, ?_⟩
    have hR := ((sepUpTo_reflect hw hvk).isSep_of_lt hqT).isRate hxk'
    have := hR.clk_lt ⟨S.coe_nonneg, by exact_mod_cast hSq.le⟩ ⟨(q : ℝ≥0).coe_nonneg, le_rfl⟩
      (by exact_mod_cast hSq)
    unfold clkR
    linarith

/-- **`IdProp` gives (a)**: the nearest mark stays strictly left of the driver before every separated time. -/
theorem gap_of_idProp (hw : ContinuousOn w {t | (t : ℝ≥0∞) < τ}) (hvk : ContinuousOn (vL k) {t | (t : ℝ≥0∞) < τ})
    (hv0 : ContinuousOn (vL i₀) {t | (t : ℝ≥0∞) < τ}) (hP : IdProp i₀ k w vL τ) {q : ℚ≥0}
    (hq : (((q : ℝ≥0) : ℝ≥0∞)) < sepTime (fun t => -w t) (fun t => -vL k t) τ) {t : ℝ≥0} (ht : t ≤ q) :
    vL i₀ t < w t := by
  have hsq := sepQ_of_lt_sepTime hw hvk hq
  obtain ⟨n, hn⟩ := hP.1 q hsq
  have hb := le_of_forall_rat_le (f := fun t => w t - vL i₀ t)
    ((continuousOn_Icc_of_lt hw hsq.1).sub (continuousOn_Icc_of_lt hv0 hsq.1))
    (fun r hr => hn r (by exact_mod_cast hr)) ht
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
  linarith

/-- **`IdProp` gives (b)**: the new horizon of the reflected path at its separation time is infinite. -/
theorem newHorizon_top_of_idProp (hw : ContinuousOn w {t | (t : ℝ≥0∞) < τ})
    (hvk : ContinuousOn (vL k) {t | (t : ℝ≥0∞) < τ}) (hP : IdProp i₀ k w vL τ) :
    newHorizon (-vL k 0) (fun t => -w t) (fun t => -vL k t) (sepTime (fun t => -w t) (fun t => -vL k t) τ) = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun M => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (M : ℝ)
  obtain ⟨q, hq, hMq⟩ := hP.2 n
  have hqs := lt_sepTime_of_sepQ hw hvk hq
  refine le_trans ?_ (le_iSup₂_of_le (q : ℝ≥0) hqs le_rfl)
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (hn.trans hMq)

end Path

end InteractingSLE.ZhanGT4.A2P3ID
