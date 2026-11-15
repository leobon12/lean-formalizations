/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9DCuts
import InteractingSLE.Spec.Supplement.S10Main
import InteractingSLE.Spec.Restart.Carrier

/-!
# Supplement §9: the empty lower rectangle of two chart continuations, measurably

Packet PROVE-W5-REST. Lemma W2's proof (p. 531): "Lemma 7.7 consequently gives a common first contact whenever the
full stopped histories have a contact. They contain both `p` and `q`. Their common first point would therefore have
first parameter at most `a` and second parameter at most `v`, contradicting (W1.1)."

For two paths `f`, `g` with available lifetimes `A`, `B`, the event `ChartLowerRect f g A B a b N` says: there is no
contact in `[0, a] × [0, b]`, but there are contacts in `[0, a] × [b, N]` and in `[a, N] × [0, b]`. A common first
contact (Lemma 7.7, `Supp10.Lemma77Statement`) excludes it (`not_chartLowerRect_of_isFirstContact`). For dyadic `a`,
`b` it is a measurable event of the restart coordinates (`measurableSet_chartLowerRect`), so that a conditional
statement under the restart kernel integrates back (`Restart.ae_mem_of_compProd_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp9D

open Sec2.Assembly

/-! ### Contacts in a rectangle -/

/-- A contact of `f` (available on `[0, A]`) and `g` (available on `[0, B]`) in the rectangle
`[x₁, x₂] × [y₁, y₂]`. -/
def HasContactIn (f g : ℝ≥0 → ℂ) (A B : ℝ≥0∞) (x₁ x₂ y₁ y₂ : ℝ≥0) : Prop :=
  ∃ x y : ℝ≥0, x₁ ≤ x ∧ x ≤ x₂ ∧ y₁ ≤ y ∧ y ≤ y₂ ∧ (x : ℝ≥0∞) ≤ A ∧ (y : ℝ≥0∞) ≤ B ∧ f x = g y

/-- **The empty lower rectangle** in the chart: no contact in `[0, a] × [0, b]`, a contact in `[0, a] × [b, N]` and a
contact in `[a, N] × [0, b]`. -/
def ChartLowerRect (f g : ℝ≥0 → ℂ) (A B : ℝ≥0∞) (a b : ℝ≥0) (N : ℕ) : Prop :=
  ¬ HasContactIn f g A B 0 a 0 b ∧ HasContactIn f g A B 0 a b N ∧ HasContactIn f g A B a N 0 b

/-- **A common first contact excludes an empty lower rectangle.** -/
theorem not_chartLowerRect_of_isFirstContact {f g : ℝ≥0 → ℂ} {A B : ℝ≥0∞} {s₀ t₀ : ℝ≥0}
    (h : IsFirstContact f A g B s₀ t₀) (a b : ℝ≥0) (N : ℕ) : ¬ ChartLowerRect f g A B a b N := by
  rintro ⟨h0, ⟨x, y, -, hxa, -, -, hxA, hyB, hxy⟩, ⟨x', y', -, -, -, hy'b, hx'A, hy'B, hxy'⟩⟩
  obtain ⟨hs₀, ht₀, he, hmin⟩ := h
  exact h0 ⟨s₀, t₀, zero_le, (hmin x y hxA hyB hxy).1.trans hxa, zero_le,
    (hmin x' y' hx'A hy'B hxy').2.trans hy'b, hs₀, ht₀, he⟩

/-- **Lemma 7.7 excludes an empty lower rectangle**: if every contact of the available paths gives a common first
contact, there is no empty lower rectangle. -/
theorem not_chartLowerRect {f g : ℝ≥0 → ℂ} {A B : ℝ≥0∞}
    (h : (∃ s t : ℝ≥0, (s : ℝ≥0∞) ≤ A ∧ (t : ℝ≥0∞) ≤ B ∧ f s = g t) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact f A g B s₀ t₀) (a b : ℝ≥0) (N : ℕ) :
    ¬ ChartLowerRect f g A B a b N := by
  intro hR
  obtain ⟨x, y, -, -, -, -, hxA, hyB, hxy⟩ := hR.2.1
  obtain ⟨s₀, t₀, hfc⟩ := h ⟨x, y, hxA, hyB, hxy⟩
  exact not_chartLowerRect_of_isFirstContact hfc a b N hR

/-! ### Dyadic approximation -/

/-- A time which is dyadic at level `p` lies below the dyadic floor at every finer level of any later time. -/
theorem le_dyad_flr {p i n : ℕ} (hpn : p ≤ n) {x : ℝ≥0} (hx : dyad p i ≤ x) : dyad p i ≤ dyad n (flr n x) := by
  have hk : dyad p i = dyad n (i * 2 ^ (n - p)) := by
    unfold dyad
    have h2 : (2 : ℝ≥0) ^ n = 2 ^ p * 2 ^ (n - p) := by rw [← pow_add, Nat.add_sub_cancel' hpn]
    rw [h2]
    push_cast
    field_simp
  rw [hk]
  unfold dyad flr
  gcongr
  refine Nat.le_floor ?_
  have : dyad n (i * 2 ^ (n - p)) * 2 ^ n = ((i * 2 ^ (n - p) : ℕ) : ℝ≥0) := by
    unfold dyad
    field_simp
  rw [← this, ← hk]
  gcongr

/-- A dyadic approximate contact in `[x₁, x₂] × [y₁, y₂]` at precision `m`. -/
def ApproxContactIn (f g : ℝ≥0 → ℂ) (A B : ℝ≥0∞) (x₁ x₂ y₁ y₂ : ℝ≥0) (m : ℕ) : Prop :=
  ∃ n k n' k' : ℕ, x₁ ≤ dyad n k ∧ dyad n k ≤ x₂ ∧ (dyad n k : ℝ≥0∞) ≤ A ∧ y₁ ≤ dyad n' k' ∧
    dyad n' k' ≤ y₂ ∧ (dyad n' k' : ℝ≥0∞) ≤ B ∧ dist (f (dyad n k)) (g (dyad n' k')) < 1 / ((m : ℝ) + 1)

/-- The closed parameter window `[x₁, x₂] ∩ [0, A]` is compact. -/
theorem isCompact_window (x₁ x₂ : ℝ≥0) (A : ℝ≥0∞) :
    IsCompact {x : ℝ≥0 | x₁ ≤ x ∧ x ≤ x₂ ∧ (x : ℝ≥0∞) ≤ A} := by
  refine (isCompact_Icc (a := x₁) (b := x₂)).of_isClosed_subset ?_ fun x hx => ⟨hx.1, hx.2.1⟩
  have he : {x : ℝ≥0 | x₁ ≤ x ∧ x ≤ x₂ ∧ (x : ℝ≥0∞) ≤ A} = Ici x₁ ∩ Iic x₂ ∩ {x | (x : ℝ≥0∞) ≤ A} := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Iic, mem_ofPred_eq, and_assoc]
  rw [he]
  exact (isClosed_Ici.inter isClosed_Iic).inter (isClosed_le ENNReal.continuous_coe continuous_const)

/-- **Contacts in a rectangle with dyadic lower corner, countably.** -/
theorem hasContactIn_iff {f g : ℝ≥0 → ℂ} {A B : ℝ≥0∞} (hf : ContinuousOn f {x | (x : ℝ≥0∞) ≤ A})
    (hg : ContinuousOn g {y | (y : ℝ≥0∞) ≤ B}) {p i p' i' : ℕ} (x₂ y₂ : ℝ≥0) :
    HasContactIn f g A B (dyad p i) x₂ (dyad p' i') y₂ ↔
      ∀ m : ℕ, ApproxContactIn f g A B (dyad p i) x₂ (dyad p' i') y₂ m := by
  constructor
  · rintro ⟨x, y, hx₁, hx₂, hy₁, hy₂, hxA, hyB, hxy⟩ m
    have hlx := ((hf x hxA).tendsto).comp (Restart.tendsto_dyad_flr_within hxA)
    have hly := ((hg y hyB).tendsto).comp (Restart.tendsto_dyad_flr_within hyB)
    have hd : Tendsto (fun n => dist (f (dyad n (flr n x))) (g (dyad n (flr n y)))) atTop (𝓝 0) := by
      have := hlx.dist hly
      rwa [hxy, dist_self] at this
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨n, hn₁, hn₂⟩ := ((hd.eventually (gt_mem_nhds hm)).and
      (eventually_ge_atTop (max p p'))).exists
    refine ⟨n, flr n x, n, flr n y, le_dyad_flr ((le_max_left _ _).trans hn₂) hx₁,
      (dyad_flr_le n x).trans hx₂, (ENNReal.coe_le_coe.2 (dyad_flr_le n x)).trans hxA,
      le_dyad_flr ((le_max_right _ _).trans hn₂) hy₁, (dyad_flr_le n y).trans hy₂,
      (ENNReal.coe_le_coe.2 (dyad_flr_le n y)).trans hyB, hn₁⟩
  · intro h
    choose n k n' k' hx₁ hx₂ hA hy₁ hy₂ hB hdist using h
    set a : ℕ → ℝ≥0 := fun m => dyad (n m) (k m)
    set b : ℕ → ℝ≥0 := fun m => dyad (n' m) (k' m)
    have hmem : ∀ m, (a m, b m) ∈ {x : ℝ≥0 | dyad p i ≤ x ∧ x ≤ x₂ ∧ (x : ℝ≥0∞) ≤ A} ×ˢ
        {y : ℝ≥0 | dyad p' i' ≤ y ∧ y ≤ y₂ ∧ (y : ℝ≥0∞) ≤ B} :=
      fun m => ⟨⟨hx₁ m, hx₂ m, hA m⟩, ⟨hy₁ m, hy₂ m, hB m⟩⟩
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, φ, hφ, hlim⟩ :=
      ((isCompact_window _ x₂ A).prod (isCompact_window _ y₂ B)).tendsto_subseq hmem
    have ha : Tendsto (fun m => a (φ m)) atTop (𝓝[{x : ℝ≥0 | (x : ℝ≥0∞) ≤ A}] x) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto _).comp hlim,
        Eventually.of_forall fun m => hA (φ m)⟩
    have hb : Tendsto (fun m => b (φ m)) atTop (𝓝[{y : ℝ≥0 | (y : ℝ≥0∞) ≤ B}] y) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_snd.tendsto _).comp hlim,
        Eventually.of_forall fun m => hB (φ m)⟩
    have hfa := ((hf x hx.2.2).tendsto).comp ha
    have hgb := ((hg y hy.2.2).tendsto).comp hb
    have hsmall : Tendsto (fun m => 1 / ((φ m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hdle : dist (f x) (g y) ≤ 0 :=
      le_of_tendsto_of_tendsto' (hfa.dist hgb) hsmall fun m => (hdist (φ m)).le
    exact ⟨x, y, hx.1, hx.2.1, hy.1, hy.2.1, hx.2.2, hy.2.2, dist_le_zero.1 hdle⟩

/-! ### Measurability -/

section Meas

variable {S : Type*} [MeasurableSpace S] {H : S → LQGMetric.DistOn upperHalfPlaneOpens}
  {Γ₁ Γ₂ : S → ℝ≥0 → ℂ} {U₁ U₂ : S → ℝ≥0∞}

theorem measurableSet_approxContactIn (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hΓ₁ : ∀ t, Measurable fun s => Γ₁ s t) (hΓ₂ : ∀ t, Measurable fun s => Γ₂ s t) (x₁ x₂ y₁ y₂ : ℝ≥0)
    (m : ℕ) : MeasurableSet {s | ApproxContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) x₁ x₂ y₁ y₂ m} := by
  unfold ApproxContactIn
  refine measurableSet_setOfPred.2 (Measurable.exists fun n => Measurable.exists fun k => Measurable.exists
    fun n' => Measurable.exists fun k' => ?_)
  refine Measurable.and measurable_const (Measurable.and measurable_const (Measurable.and
    (measurableSet_setOfPred.1 (measurableSet_le measurable_const hU₁)) (Measurable.and measurable_const
    (Measurable.and measurable_const (Measurable.and
    (measurableSet_setOfPred.1 (measurableSet_le measurable_const hU₂)) ?_)))))
  exact measurableSet_setOfPred.1 (measurableSet_lt ((hΓ₁ _).dist (hΓ₂ _)) measurable_const)

theorem measurableSet_hasContactIn (hc : Restart.IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂) (p i : ℕ) (x₂ : ℝ≥0)
    (p' i' : ℕ) (y₂ : ℝ≥0) :
    MeasurableSet {s | HasContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad p i) x₂ (dyad p' i') y₂} := by
  obtain ⟨-, hU₁, hU₂, hγ₁, hγ₂, hc₁, hc₂⟩ := hc
  have hset : {s | HasContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad p i) x₂ (dyad p' i') y₂} =
      ⋂ m : ℕ, {s | ApproxContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad p i) x₂ (dyad p' i') y₂ m} := by
    ext s
    simp only [mem_ofPred_eq, mem_iInter]
    exact hasContactIn_iff (hc₁ s) (hc₂ s) x₂ y₂
  rw [hset]
  exact MeasurableSet.iInter fun m => measurableSet_approxContactIn hU₁ hU₂ hγ₁ hγ₂ _ _ _ _ m

theorem dyad_zero_zero' : dyad 0 0 = 0 := by simp [dyad]

/-- **The empty lower rectangle at dyadic corners is a measurable event** of the restart coordinates. -/
theorem measurableSet_chartLowerRect (hc : Restart.IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂) (n k n' k' N : ℕ) :
    MeasurableSet {s | ChartLowerRect (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad n k) (dyad n' k') N} := by
  have e : ∀ s, ChartLowerRect (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad n k) (dyad n' k') N ↔
      ¬ HasContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad 0 0) (dyad n k) (dyad 0 0) (dyad n' k') ∧
      HasContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad 0 0) (dyad n k) (dyad n' k') N ∧
      HasContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad n k) N (dyad 0 0) (dyad n' k') := by
    intro s
    rw [dyad_zero_zero']
    rfl
  have hset : {s | ChartLowerRect (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad n k) (dyad n' k') N} =
      ({s | HasContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad 0 0) (dyad n k) (dyad 0 0) (dyad n' k')}ᶜ ∩
        {s | HasContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad 0 0) (dyad n k) (dyad n' k') N}) ∩
        {s | HasContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad n k) N (dyad 0 0) (dyad n' k')} := by
    ext s
    rw [mem_ofPred_eq, e s]
    simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq, and_assoc]
  rw [hset]
  exact ((measurableSet_hasContactIn hc 0 0 _ 0 0 _).compl.inter
    (measurableSet_hasContactIn hc 0 0 _ n' k' _)).inter (measurableSet_hasContactIn hc n k _ 0 0 _)

end Meas

end Supp9D

end InteractingSLE
