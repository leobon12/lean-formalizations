/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59TipsSwallow

/-!
# Proposition 5.9's one-stage construction, step 2: the far-left swallow with marks at the seed

Packet PROVE-PROP59T. Specification §5.2, proof of Proposition 5.9 (`source/spec/p097-144.md` L1002, p. 143): "At a
switch the new two force points start at the driver, with weights at least `κ/2 − 2 > −2`. All other marks are
separated from the driver; coincident initial marks, if any, are first amalgamated."

So a stage begins with seed marks, where Zhan's strip theorem (hence `ae_swallow_of_strict`) does not apply directly.
The evolution is restarted at a small positive rational time `q` at which every mark is strictly off the driver and
the positions are still distinct, by the strong Markov property in code form (`ZhanGT4.measure_restart_stateEvent`)
and the null canonical law of the no-swallow code set from such starts (`codeLaw_noSwallowSet_eq_zero`). Such a `q`
exists pathwise: distinct positions persist for a short time by continuity, and the collision sets of an integrated
path are Lebesgue-null (frozen `IsIntegratedSLEPath`), so the open set of fully separated times meets every interval
`(0, ε)`.

## Main results

* `sepFun` (continuous), `sepFun_neg_iff`: the state at a time is fully separated (distinct positions on each side,
  every mark strictly off the driver) iff `sepFun < 0`;
* `exists_rat_sepFun_neg` (pathwise): an integrated path with infinite lifetime and distinct initial positions is
  fully separated at some positive rational time;
* **`ae_swallow`**: for an integrated `SLE_κ(ρ)` evolution, `0 < κ < 4`, of a stage word with distinct positions on
  each side (seed marks allowed), almost surely the lifetime is finite or the outermost left mark meets the driver
  before it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec5

namespace Prop59Tips

open Sec2.Assembly Sec7.RandRestart Coupling

/-! ### Fully separated states -/

section Sep

variable {j n : ℕ}

/-- Indices of the separation conditions: left marks off the driver, right marks off the driver, ordered left pairs,
ordered right pairs. -/
abbrev SepIdx (j n : ℕ) : Type := Fin (j + 1) ⊕ Fin n ⊕ (Fin (j + 1) × Fin (j + 1)) ⊕ (Fin n × Fin n)

/-- The separation terms of a state (each must be negative). -/
def sepTerm (p : ℝ × (Fin (j + 1) → ℝ) × (Fin n → ℝ)) : SepIdx j n → ℝ
  | Sum.inl i => p.2.1 i - p.1
  | Sum.inr (Sum.inl k) => p.1 - p.2.2 k
  | Sum.inr (Sum.inr (Sum.inl ii)) => if ii.1 < ii.2 then p.2.1 ii.2 - p.2.1 ii.1 else -1
  | Sum.inr (Sum.inr (Sum.inr kk)) => if kk.1 < kk.2 then p.2.2 kk.1 - p.2.2 kk.2 else -1

instance (j n : ℕ) : Nonempty (SepIdx j n) := ⟨Sum.inl 0⟩

/-- The largest separation term: the state is fully separated iff it is negative. -/
def sepFun (p : ℝ × (Fin (j + 1) → ℝ) × (Fin n → ℝ)) : ℝ := univ.sup' univ_nonempty (sepTerm p)

theorem continuous_sepFun : Continuous (sepFun (j := j) (n := n)) := by
  refine Continuous.finset_sup'_apply (f := fun k p => sepTerm p k) _ fun k _ => ?_
  rcases k with i | k | ii | kk
  · exact ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).sub continuous_fst
  · exact continuous_fst.sub ((continuous_apply k).comp (continuous_snd.comp continuous_snd))
  · by_cases h : ii.1 < ii.2
    · simp only [sepTerm, h, ↓reduceIte]
      exact ((continuous_apply ii.2).comp (continuous_fst.comp continuous_snd)).sub
        ((continuous_apply ii.1).comp (continuous_fst.comp continuous_snd))
    · simp only [sepTerm, h, ↓reduceIte]
      exact continuous_const
  · by_cases h : kk.1 < kk.2
    · simp only [sepTerm, h, ↓reduceIte]
      exact ((continuous_apply kk.1).comp (continuous_snd.comp continuous_snd)).sub
        ((continuous_apply kk.2).comp (continuous_snd.comp continuous_snd))
    · simp only [sepTerm, h, ↓reduceIte]
      exact continuous_const

/-- **Full separation** of a state: distinct positions on each side, every mark strictly off the driver. -/
theorem sepFun_neg_iff (p : ℝ × (Fin (j + 1) → ℝ) × (Fin n → ℝ)) :
    sepFun p < 0 ↔ StrictAnti p.2.1 ∧ (∀ i, p.2.1 i < p.1) ∧ StrictMono p.2.2 ∧ ∀ k, p.1 < p.2.2 k := by
  rw [sepFun, sup'_lt_iff]
  constructor
  · intro h
    refine ⟨fun a b hab => ?_, fun i => ?_, fun a b hab => ?_, fun k => ?_⟩
    · have := h (Sum.inr (Sum.inr (Sum.inl (a, b)))) (mem_univ _)
      simp only [sepTerm, hab, ↓reduceIte] at this
      linarith
    · have := h (Sum.inl i) (mem_univ _)
      simp only [sepTerm] at this
      linarith
    · have := h (Sum.inr (Sum.inr (Sum.inr (a, b)))) (mem_univ _)
      simp only [sepTerm, hab, ↓reduceIte] at this
      linarith
    · have := h (Sum.inr (Sum.inl k)) (mem_univ _)
      simp only [sepTerm] at this
      linarith
  · rintro ⟨h1, h2, h3, h4⟩ k -
    rcases k with i | k | ii | kk
    · simp only [sepTerm]; linarith [h2 i]
    · simp only [sepTerm]; linarith [h4 k]
    · by_cases h : ii.1 < ii.2
      · simp only [sepTerm, h, ↓reduceIte]; linarith [h1 h]
      · simp only [sepTerm, h, ↓reduceIte]; norm_num
    · by_cases h : kk.1 < kk.2
      · simp only [sepTerm, h, ↓reduceIte]; linarith [h3 h]
      · simp only [sepTerm, h, ↓reduceIte]; norm_num

end Sep

/-! ### A fully separated positive rational time -/

section Path

variable {κ : ℝ} {j n : ℕ} {xL : Fin (j + 1) → ℝ} {xR : Fin n → ℝ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (j + 1) → ℝ≥0 → ℝ} {vR : Fin n → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- **A fully separated positive rational time** (pathwise). An integrated path with infinite lifetime and distinct
initial positions on each side has, at some positive rational time, distinct positions on each side and every mark
strictly off the driver: distinct positions persist near `0` by continuity, and the collision sets are null. -/
theorem exists_rat_sepFun_neg (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤) (hxL : StrictAnti xL)
    (hxR : StrictMono xR) :
    ∃ q : ℚ≥0, 0 < q ∧ sepFun ((w q, fun i => vL i q, fun k => vR k q)) < 0 := by
  have hpF := hp.isForcePath
  have hcw : Continuous w := continuousOn_univ.1 (hpF.continuousOn_w.mono fun _ _ => ENNReal.coe_lt_top)
  have hcL : ∀ i, Continuous (vL i) := fun i =>
    continuousOn_univ.1 ((hpF.continuousOn_vL i).mono fun _ _ => ENNReal.coe_lt_top)
  have hcR : ∀ k, Continuous (vR k) := fun k =>
    continuousOn_univ.1 ((hpF.continuousOn_vR k).mono fun _ _ => ENNReal.coe_lt_top)
  set st : ℝ≥0 → ℝ × (Fin (j + 1) → ℝ) × (Fin n → ℝ) := fun t => (w t, fun i => vL i t, fun k => vR k t)
    with hst
  have hcst : Continuous st := hcw.prodMk ((continuous_pi hcL).prodMk (continuous_pi hcR))
  -- distinct positions persist near `0`
  have hordL : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ∀ a b : Fin (j + 1), a < b → vL b t < vL a t := by
    refine eventually_all.2 fun a => eventually_all.2 fun b => ?_
    by_cases hab : a < b
    · have h0 : 0 < vL a 0 - vL b 0 := by rw [hpF.vL_zero, hpF.vL_zero, sub_pos]; exact hxL hab
      filter_upwards [(((hcL a).sub (hcL b)).tendsto 0).eventually (lt_mem_nhds h0)] with t ht _
      simp only [Pi.sub_apply] at ht
      linarith
    · exact Eventually.of_forall fun _ h => absurd h hab
  have hordR : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ∀ a b : Fin n, a < b → vR a t < vR b t := by
    refine eventually_all.2 fun a => eventually_all.2 fun b => ?_
    by_cases hab : a < b
    · have h0 : 0 < vR b 0 - vR a 0 := by rw [hpF.vR_zero, hpF.vR_zero, sub_pos]; exact hxR hab
      filter_upwards [(((hcR b).sub (hcR a)).tendsto 0).eventually (lt_mem_nhds h0)] with t ht _
      simp only [Pi.sub_apply] at ht
      linarith
    · exact Eventually.of_forall fun _ h => absurd h hab
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 (hordL.and hordR)
  -- a time in `(0, ε)` off every collision set
  set Z : Set ℝ := (⋃ i, {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ⊤ ∧ w s.toNNReal = vL i s.toNNReal}) ∪
    ⋃ k, {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ⊤ ∧ w s.toNNReal = vR k s.toNNReal} with hZ
  have hZ0 : volume Z = 0 :=
    measure_union_null (measure_iUnion_null fun i => hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)
      (measure_iUnion_null fun k => hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k)
  have hsub : ¬ Ioo (0 : ℝ) ε ⊆ Z := fun h => by
    have := measure_mono_null h hZ0
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
    linarith
  obtain ⟨s, ⟨hs0, hsε⟩, hsZ⟩ := not_subset.1 hsub
  set t₀ : ℝ≥0 := s.toNNReal with ht₀
  have ht₀s : (t₀ : ℝ) = s := Real.coe_toNNReal s hs0.le
  have ht₀pos : 0 < t₀ := Real.toNNReal_pos.2 hs0
  have hneL : ∀ i, vL i t₀ ≠ w t₀ := fun i he =>
    hsZ (Or.inl (mem_iUnion.2 ⟨i, hs0.le, ENNReal.coe_lt_top, he.symm⟩))
  have hneR : ∀ k, w t₀ ≠ vR k t₀ := fun k he =>
    hsZ (Or.inr (mem_iUnion.2 ⟨k, hs0.le, ENNReal.coe_lt_top, he⟩))
  have hdist : dist t₀ 0 < ε := by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, ht₀s, abs_of_pos hs0]
    exact hsε
  obtain ⟨hL, hR⟩ := hεP hdist
  have hneg : sepFun (st t₀) < 0 := by
    rw [sepFun_neg_iff]
    refine ⟨fun a b hab => hL a b hab, fun i => lt_of_le_of_ne (hpF.vL_le_w ENNReal.coe_lt_top i) (hneL i),
      fun a b hab => hR a b hab, fun k => lt_of_le_of_ne (hpF.w_le_vR ENNReal.coe_lt_top k) (hneR k)⟩
  -- a rational time nearby
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1
    ((continuous_sepFun.comp hcst).continuousAt.preimage_mem_nhds (Iio_mem_nhds hneg))
  obtain ⟨q, hq1, hq2⟩ := Zhan.exists_nnrat_near t₀ hδ
  have hq0 : 0 < q := by
    have h : (0 : ℝ≥0) < (q : ℝ≥0) := lt_of_lt_of_le ht₀pos hq1
    exact_mod_cast h
  refine ⟨q, hq0, hball ?_⟩
  rw [Metric.mem_ball, NNReal.dist_eq, abs_lt]
  have : (t₀ : ℝ) ≤ ((q : ℝ≥0) : ℝ) := by exact_mod_cast hq1
  constructor <;> linarith

end Path

/-! ### The swallow with seed marks -/

/-- **The far-left swallow of a stage word, seed marks allowed** (proof of Proposition 5.9, pp. 143–144: "At a switch
the new two force points start at the driver"). For an integrated `SLE_κ(ρ)` evolution, `0 < κ < 4`, of a stage word
with distinct positions on each side (`xL 0 = 0` and `xR 0 = 0` allowed), almost surely the lifetime is finite or the
outermost left mark meets the driver before it. Restart at a fully separated positive rational time and apply
`ae_swallow_of_strict` to the restarted canonical evolution. -/
theorem ae_swallow {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {j n : ℕ} {xL : Fin (j + 1) → ℝ}
    {xR : Fin n → ℝ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hxL : StrictAnti xL) (hxR : StrictMono xR) (hw : IsStageWord κ ρL ρR) :
    ∀ᵐ ω ∂P, ζ ω ≠ ⊤ ∨ ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ VL (Fin.last j) t ω = W t ω := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  -- at each positive rational `q`, the restarted no-swallow event on the separated event is null
  have hnull : ∀ q : ℚ≥0, 0 < q → P ({ω | (((q : ℝ≥0)) : ℝ≥0∞) < ζ ω ∧
      sepFun (stateAt W VL VR (q : ℝ≥0) ω) < 0} ∩
      {ω | NoSwallowQ (Fin.last j) (fun t => W ((q : ℝ≥0) + t) ω - W (q : ℝ≥0) ω)
        (fun i t => VL i ((q : ℝ≥0) + t) ω - W (q : ℝ≥0) ω)
        (fun k t => VR k ((q : ℝ≥0) + t) ω - W (q : ℝ≥0) ω) (ζ ω - (q : ℝ≥0))}) = 0 := by
    intro q hq
    have hT : IsStoppingTime 𝓕 fun _ : Ω => (((q : ℝ≥0)) : WithTop ℝ≥0) := isStoppingTime_const 𝓕 _
    set A := {ω | (((q : ℝ≥0)) : ℝ≥0∞) < ζ ω ∧ sepFun (stateAt W VL VR (q : ℝ≥0) ω) < 0} with hAdef
    have hA : MeasurableSet[hT.measurableSpace] A := by
      rw [IsStoppingTime.measurableSpace_const]
      exact measurableSet_lt_zeta_and_lt hE.2.1 hE.2.2.1 hE.2.2.2.1 continuous_sepFun 0 (q : ℝ≥0)
    have hq0 : (0 : ℝ≥0) < (q : ℝ≥0) := by exact_mod_cast hq
    rw [ZhanGT4.measure_restart_stateEvent hκ hE hT hA (fun ω hω => ⟨hω.1, Or.inl hq0⟩)
      (measurableSet_noSwallowSet (Fin.last j)) (fun x _ _ => Iff.rfl) (noSwallowQ_congr (Fin.last j))]
    have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
    rw [setLIntegral_congr_fun_ae hAm (g := fun _ => 0) ?_, lintegral_zero]
    refine Eventually.of_forall fun ω hωA => ?_
    obtain ⟨h1, h2, h3, h4⟩ := (sepFun_neg_iff _).1 hωA.2
    exact codeLaw_noSwallowSet_eq_zero hκ hκ4 hw (fun a b hab => sub_lt_sub_right (h1 hab) _)
      (fun i => sub_neg.2 (h2 i)) (fun a b hab => sub_lt_sub_right (h3 hab) _) (fun k => sub_pos.2 (h4 k))
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ≥0, 0 < q → ¬ ((((q : ℝ≥0)) : ℝ≥0∞) < ζ ω ∧
      sepFun (stateAt W VL VR (q : ℝ≥0) ω) < 0 ∧
      NoSwallowQ (Fin.last j) (fun t => W ((q : ℝ≥0) + t) ω - W (q : ℝ≥0) ω)
        (fun i t => VL i ((q : ℝ≥0) + t) ω - W (q : ℝ≥0) ω)
        (fun k t => VR k ((q : ℝ≥0) + t) ω - W (q : ℝ≥0) ω) (ζ ω - (q : ℝ≥0))) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) (hnull q hq)
      simp only [not_imp, not_not, mem_ofPred_eq] at hω
      obtain ⟨-, h1, h2, h3⟩ := hω
      exact ⟨⟨h1, h2⟩, h3⟩
    · exact Eventually.of_forall fun _ h => absurd h hq
  filter_upwards [hall, hE.2.2.2.2] with ω hω hp
  by_contra hcon
  push Not at hcon
  obtain ⟨hζ, hlt⟩ := hcon
  have hlt' : ∀ t : ℝ≥0, VL (Fin.last j) t ω < W t ω := fun t => by
    have htζ : (t : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
    exact lt_of_le_of_ne (hp.isForcePath.vL_le_w htζ (Fin.last j)) (hlt t htζ)
  rw [hζ] at hp
  obtain ⟨q, hq, hsep⟩ := exists_rat_sepFun_neg hp hxL hxR
  have hpF := hp.isForcePath
  have hcw : Continuous fun t => W t ω :=
    continuousOn_univ.1 (hpF.continuousOn_w.mono fun _ _ => ENNReal.coe_lt_top)
  have hcv : Continuous fun t => VL (Fin.last j) t ω :=
    continuousOn_univ.1 ((hpF.continuousOn_vL (Fin.last j)).mono fun _ _ => ENNReal.coe_lt_top)
  have hsh : Continuous fun t : ℝ≥0 => (q : ℝ≥0) + t := continuous_const.add continuous_id
  refine hω q hq ⟨by rw [hζ]; exact ENNReal.coe_lt_top, hsep, ?_⟩
  rw [hζ, ENNReal.top_sub_coe]
  exact noSwallowQ_of_forall_lt (vL := fun i t => VL i ((q : ℝ≥0) + t) ω - W (q : ℝ≥0) ω) _
    ((hcw.comp hsh).sub continuous_const) ((hcv.comp hsh).sub continuous_const)
    fun t => sub_lt_sub_right (hlt' _) _

end Prop59Tips

end Sec5

end InteractingSLE
