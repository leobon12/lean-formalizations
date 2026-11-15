/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCRef
import InteractingSLE.Spec.Theorem15D5Code
import InteractingSLE.Spec.Supplement.S9DCuts
import InteractingSLE.Spec.Restart.CondDet

/-!
# The chart completion event is universally measurable, and it integrates over the retained datum

Packet PROVE-RLC-B, step (iii) of `planning/handoffs/PROVE-RLC-A.md` ("integration over the datum"). Source:
supplement §7.1, p. 490: "The same assertion applies after conditioning on one retained initial datum. It suffices to
prove it for almost every fixed datum. The final probability-one statement is measurable in the original field and
histories, so it can then be integrated."

The final probability-one statement here is `ChartInteriorCompletion` for the chart pair, an `∃` over curves. It is
universally measurable (this file), which is exactly what the integration needs:

* `IsChartCompletable g₁ s₁ g₂ s₂` holds iff the dyadic codes of `(g₁, g₂)` lie in the projection of a Borel relation
  `CompRelS s₁ s₂` (W0's relation `Theorem15D5.CompRel` with the two seed-avoidance clauses, which are countable
  conditions since a continuous proper curve has closed range): `isChartCompletable_iff_exists`;
* for continuous chart paths, `ChartInteriorCompletion` reduces to dyadic prefixes (`chartInteriorCompletion_iff`),
  with the interior clause in a countable form (`IntC`); hence the event is universally measurable
  (`uMeasurableSet_chartInteriorCompletion`, Lusin's theorem through `LQGMetric.UMeasurableSet.setOf_exists`);
* `ae_mem_of_ae_ae_compProd_of_uMeasurable`: an event of `(datum, restart point)` which is universally measurable and
  holds for almost every datum under almost every kernel measure holds almost surely (the lift back of
  `Restart.ae_mem_of_ae_ae_compProd` without measurability of the event).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Theorem15D5 Sec2.Assembly Supp9D

/-! ### The range of a decoded proper curve -/

/-- The dyadic values of a code, as a countable family. -/
def dyadFam (q : CCode) : ℕ × ℕ → ℂ := fun p => q p.1 p.2

theorem measurable_dyadFam {X : Type*} [MeasurableSpace X] {q : X → CCode}
    (hq : ∀ n k, Measurable fun x => q x n k) (p : ℕ × ℕ) : Measurable fun x => dyadFam (q x) p :=
  hq p.1 p.2

/-- **The range of a decoded continuous proper curve is the closure of its dyadic values.** -/
theorem range_decC_eq {q : CCode} (h : GoodAll q) (hp : PropC q) :
    range (decC q) = closure (range (dyadFam q)) := by
  apply Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact mem_closure_of_tendsto (h.tendsto t) (Eventually.of_forall fun n => ⟨(n, flr n t), rfl⟩)
  · refine closure_minimal ?_ (isClosed_range_of_tendsto_norm h.continuous ((tendsto_norm_iff_propC h).mpr hp))
    rintro _ ⟨p, rfl⟩
    exact ⟨dyad p.1 p.2, h.decC_dyad p.1 p.2⟩

/-! ### The completability relation -/

/-- **The chart completability relation** between the codes `(p₁, p₂)` of two prefixes `g₁|[0, a]`, `g₂|[0, c]`
and the codes `(q₁, q₂)` of a pair of ordered proper completions avoiding each other's seeds: W0's relation
`CompRel a c` and the two seed clauses. -/
def CompRelS (a c : ℝ≥0) : Set ((CCode × CCode) × (CCode × CCode)) :=
  CompRel a c ∩ {x | x.1.1 0 0 ∉ closure (range (dyadFam x.2.2)) ∧ x.1.2 0 0 ∉ closure (range (dyadFam x.2.1))}

/-- **The chart completability relation is Borel.** -/
theorem measurableSet_compRelS (a c : ℝ≥0) : MeasurableSet (CompRelS a c) := by
  refine (measurableSet_compRel a c).inter ?_
  have m11 : ∀ n k, Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.1.1 n k :=
    fun n k => (measurable_coord n k).comp measurable_fst.fst
  have m12 : ∀ n k, Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.1.2 n k :=
    fun n k => (measurable_coord n k).comp measurable_fst.snd
  have m21 : ∀ n k, Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.2.1 n k :=
    fun n k => (measurable_coord n k).comp measurable_snd.fst
  have m22 : ∀ n k, Measurable fun x : (CCode × CCode) × (CCode × CCode) => x.2.2 n k :=
    fun n k => (measurable_coord n k).comp measurable_snd.snd
  exact (measurableSet_mem_closure_range (measurable_dyadFam m22) (m11 0 0)).compl.inter
    (measurableSet_mem_closure_range (measurable_dyadFam m21) (m12 0 0)).compl

/-- The seed of a prefix through its code. -/
theorem encC_zero_zero (g : ℝ≥0 → ℂ) : encC g 0 0 = g 0 := by
  show g (dyad 0 0) = g 0
  rw [Theorem15D5.dyad_zero_zero]

/-- **Chart completability through codes**: for prefixes continuous on `[0, s₁]`, `[0, s₂]`,
`IsChartCompletable g₁ s₁ g₂ s₂` holds iff the codes of `(g₁, g₂)` lie in the projection of `CompRelS s₁ s₂`. -/
theorem isChartCompletable_iff_exists {g₁ g₂ : ℝ≥0 → ℂ} {s₁ s₂ : ℝ≥0} (hg₁ : ContinuousOn g₁ (Iic s₁))
    (hg₂ : ContinuousOn g₂ (Iic s₂)) :
    IsChartCompletable g₁ s₁ g₂ s₂ ↔ ∃ y, ((encC g₁, encC g₂), y) ∈ CompRelS s₁ s₂ := by
  constructor
  · rintro ⟨γ₁, γ₂, hγ₁, hγ₂, hord, hs₁, hs₂⟩
    have ga₁ := goodAll_encC hγ₁.1
    have ga₂ := goodAll_encC hγ₂.1
    have pc₁ : PropC (encC γ₁) := by
      rw [← tendsto_norm_iff_propC ga₁, decC_encC_of_continuous hγ₁.1]; exact hγ₁.2.2.2.1
    have pc₂ : PropC (encC γ₂) := by
      rw [← tendsto_norm_iff_propC ga₂, decC_encC_of_continuous hγ₂.1]; exact hγ₂.2.2.2.1
    refine ⟨(encC γ₁, encC γ₂), ⟨?_, ?_⟩⟩
    · refine ⟨goodC_encC hg₁, goodC_encC hg₂, ga₁, ga₂, ?_, ?_, ?_⟩
      · rw [decC_encC_of_continuous hγ₁.1]
        exact ⟨hγ₁.1, hγ₁.2.1, hγ₁.2.2.1, hγ₁.2.2.2.1, fun t ht => by
          rw [decC_encC_of_continuousOn hg₁ ht]; exact hγ₁.2.2.2.2 t ht⟩
      · rw [decC_encC_of_continuous hγ₂.1]
        exact ⟨hγ₂.1, hγ₂.2.1, hγ₂.2.2.1, hγ₂.2.2.2.1, fun t ht => by
          rw [decC_encC_of_continuousOn hg₂ ht]; exact hγ₂.2.2.2.2 t ht⟩
      · rw [decC_encC_of_continuous hγ₁.1, decC_encC_of_continuous hγ₂.1]; exact hord
    · refine ⟨?_, ?_⟩
      · show encC g₁ 0 0 ∉ closure (range (dyadFam (encC γ₂)))
        rw [← range_decC_eq ga₂ pc₂, decC_encC_of_continuous hγ₂.1, encC_zero_zero]; exact hs₁
      · show encC g₂ 0 0 ∉ closure (range (dyadFam (encC γ₁)))
        rw [← range_decC_eq ga₁ pc₁, decC_encC_of_continuous hγ₁.1, encC_zero_zero]; exact hs₂
  · rintro ⟨y, ⟨g1, g2, ga₁, ga₂, h₁, h₂, hsub⟩, hs₁, hs₂⟩
    have pc₁ : PropC y.1 := (tendsto_norm_iff_propC ga₁).1 h₁.2.2.2.1
    have pc₂ : PropC y.2 := (tendsto_norm_iff_propC ga₂).1 h₂.2.2.2.1
    refine ⟨decC y.1, decC y.2, ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, fun t ht => ?_⟩,
      ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, fun t ht => ?_⟩, hsub, ?_, ?_⟩
    · rw [h₁.2.2.2.2 t ht]; exact decC_encC_of_continuousOn hg₁ ht
    · rw [h₂.2.2.2.2 t ht]; exact decC_encC_of_continuousOn hg₂ ht
    · rw [range_decC_eq ga₂ pc₂, ← encC_zero_zero g₁]; exact hs₁
    · rw [range_decC_eq ga₁ pc₁, ← encC_zero_zero g₂]; exact hs₂

/-- **The coded chart completability event is universally measurable** (Lusin). -/
theorem uMeasurableSet_completableCode (a c : ℝ≥0) :
    LQGMetric.UMeasurableSet {p : CCode × CCode | ∃ y, (p, y) ∈ CompRelS a c} := by
  have : StandardBorelSpace (CCode × CCode) := StandardBorelSpace.prod
  exact LQGMetric.UMeasurableSet.setOf_exists (measurableSet_compRelS a c)

/-! ### The interior clause through codes -/

/-- **The interior clause in countable form**: on every `[1/(m+1), a]` the dyadic values of the code have imaginary
part at least some `1/(j+1)`. -/
def IntC (p : CCode) (a : ℝ≥0) : Prop :=
  ∀ m : ℕ, ∃ j : ℕ, ∀ n k : ℕ, 1 / ((m : ℝ≥0) + 1) ≤ dyad n k → dyad n k ≤ a →
    1 / ((j : ℝ) + 1) ≤ (p n k).im

theorem measurable_intC (a : ℝ≥0) : Measurable fun p : CCode => IntC p a :=
  Measurable.forall fun _ => Measurable.exists fun _ => Measurable.forall fun n => Measurable.forall fun k =>
    measurable_const.imp <| measurable_const.imp <| measurableSet_setOfPred.mp
      (measurableSet_le measurable_const (Complex.measurable_im.comp (measurable_coord n k)))

/-- **The interior clause through codes**: for a prefix continuous on `[0, a]`, it stays in `ℍ` after time `0` iff
its code satisfies `IntC`. -/
theorem intC_encC_iff {g : ℝ≥0 → ℂ} {a : ℝ≥0} (hg : ContinuousOn g (Iic a)) :
    IntC (encC g) a ↔ ∀ t : ℝ≥0, 0 < t → t ≤ a → g t ∈ H := by
  constructor
  · intro hI t ht hta
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t from ht)
    obtain ⟨j, hj⟩ := hI m
    have hmt : (1 / ((m : ℝ≥0) + 1) : ℝ≥0) < t := by
      rw [← NNReal.coe_lt_coe]; push_cast; exact hm
    -- the dyadic floors of `t` eventually lie in `[1/(m+1), t]`
    have hev : ∀ᶠ n in atTop, 1 / ((j : ℝ) + 1) ≤ (g (dyad n (flr n t))).im := by
      filter_upwards [(tendsto_dyad_flr t).eventually (lt_mem_nhds hmt)] with n hn
      exact hj n (flr n t) hn.le ((dyad_flr_le n t).trans hta)
    have hcont : Tendsto (fun n => g (dyad n (flr n t))) atTop (𝓝 (g t)) := by
      have hw : ContinuousWithinAt g (Iic a) t := hg t hta
      exact hw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr t,
        Eventually.of_forall fun n => (dyad_flr_le n t).trans hta⟩)
    have hle : 1 / ((j : ℝ) + 1) ≤ (g t).im :=
      ge_of_tendsto ((Complex.continuous_im.tendsto _).comp hcont) hev
    show 0 < (g t).im
    exact lt_of_lt_of_le (by positivity) hle
  · intro hH m
    set C : Set ℝ≥0 := Icc (1 / ((m : ℝ≥0) + 1)) a with hC
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · refine ⟨0, fun n k h1 h2 => ?_⟩
      exact absurd (show dyad n k ∈ C from ⟨h1, h2⟩) (by rw [hCe]; exact notMem_empty _)
    have hCc : IsCompact C := isCompact_Icc
    have hcont : ContinuousOn (fun t => (g t).im) C :=
      Complex.continuous_im.comp_continuousOn (hg.mono fun t ht => ht.2)
    obtain ⟨t₀, ht₀, hmin⟩ := hCc.exists_isMinOn hCne hcont
    have ht₀pos : 0 < t₀ := lt_of_lt_of_le (by positivity) ht₀.1
    have hpos : 0 < (g t₀).im := hH t₀ ht₀pos ht₀.2
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
    refine ⟨j, fun n k h1 h2 => ?_⟩
    show 1 / ((j : ℝ) + 1) ≤ (g (dyad n k)).im
    exact hj.le.trans (hmin ⟨h1, h2⟩)

/-! ### The chart interior completion property through dyadic prefixes -/

/-- **`ChartInteriorCompletion` through dyadic prefixes and codes**, for chart paths continuous on their closed
available intervals. -/
theorem chartInteriorCompletion_iff {g₁ g₂ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞}
    (hc₁ : ContinuousOn g₁ {t | (t : ℝ≥0∞) ≤ U₁}) (hc₂ : ContinuousOn g₂ {t | (t : ℝ≥0∞) ≤ U₂}) :
    ChartInteriorCompletion g₁ U₁ g₂ U₂ ↔ ∀ p₁ p₂ : ℕ × ℕ, (dyad p₁.1 p₁.2 : ℝ≥0∞) < U₁ →
      (dyad p₂.1 p₂.2 : ℝ≥0∞) < U₂ → IntC (encC g₁) (dyad p₁.1 p₁.2) → IntC (encC g₂) (dyad p₂.1 p₂.2) →
      ∃ y, ((encC g₁, encC g₂), y) ∈ CompRelS (dyad p₁.1 p₁.2) (dyad p₂.1 p₂.2) := by
  have hI : ∀ {g : ℝ≥0 → ℂ} {U : ℝ≥0∞}, ContinuousOn g {t | (t : ℝ≥0∞) ≤ U} → ∀ a : ℝ≥0, (a : ℝ≥0∞) < U →
      ContinuousOn g (Iic a) := fun hc a ha =>
    hc.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans ha.le
  constructor
  · intro hC p₁ p₂ h₁ h₂ i₁ i₂
    have c₁ := hI hc₁ _ h₁
    have c₂ := hI hc₂ _ h₂
    exact (isChartCompletable_iff_exists c₁ c₂).1
      (hC _ _ h₁ h₂ ((intC_encC_iff c₁).1 i₁) ((intC_encC_iff c₂).1 i₂))
  · intro hD s₁ s₂ h₁ h₂ i₁ i₂
    -- a dyadic time `q ≥ s` before `U` up to which the path stays interior
    have key : ∀ {g : ℝ≥0 → ℂ} {U : ℝ≥0∞} {s : ℝ≥0}, ContinuousOn g {t | (t : ℝ≥0∞) ≤ U} →
        (s : ℝ≥0∞) < U → (∀ t, 0 < t → t ≤ s → g t ∈ H) →
        ∃ p : ℕ × ℕ, s ≤ dyad p.1 p.2 ∧ (dyad p.1 p.2 : ℝ≥0∞) < U ∧
          ∀ t, 0 < t → t ≤ dyad p.1 p.2 → g t ∈ H := by
      intro g U s hc hs hin
      rcases eq_zero_or_pos s with rfl | hs0
      · refine ⟨(0, 0), ?_, ?_, ?_⟩
        · exact zero_le
        · rw [Theorem15D5.dyad_zero_zero]; exact hs
        · intro t ht ht'
          rw [Theorem15D5.dyad_zero_zero] at ht'
          exact absurd ht (not_lt.2 ht')
      obtain ⟨V, hV, hVU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
      have hsV : s < V := by exact_mod_cast hV
      have hgs : g s ∈ H := hin s hs0 le_rfl
      have hcs : ContinuousWithinAt g {t | (t : ℝ≥0∞) ≤ U} s := hc s hs.le
      have hnb : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ U} ∈ 𝓝 s := by
        refine mem_of_superset (Iio_mem_nhds hsV) fun t ht => ?_
        exact (ENNReal.coe_le_coe.2 (le_of_lt ht)).trans hVU.le
      have hca : ContinuousAt g s := hcs.continuousAt hnb
      have hopen : g ⁻¹' H ∈ 𝓝 s := hca.preimage_mem_nhds
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hgs)
      obtain ⟨l, b', ⟨hl, hsb'⟩, hsub⟩ :=
        (mem_nhds_iff_exists_Ioo_subset' ⟨0, hs0⟩ ⟨s + 1, lt_add_one s⟩).1 hopen
      obtain ⟨q, ⟨⟨n, k⟩, rfl⟩, hsq, hqb⟩ := exists_dyadSet_btwn (lt_min hsb' hsV)
      refine ⟨(n, k), hsq.le, ?_, ?_⟩
      · exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (le_of_lt (lt_of_lt_of_le hqb (min_le_right _ _)))) hVU
      · intro t ht htq
        rcases le_or_gt t s with hts | hst
        · exact hin t ht hts
        · exact hsub ⟨hl.trans hst, lt_of_le_of_lt htq (lt_of_lt_of_le hqb (min_le_left _ _))⟩
    obtain ⟨p₁, hp₁, hq₁, hi₁⟩ := key hc₁ h₁ i₁
    obtain ⟨p₂, hp₂, hq₂, hi₂⟩ := key hc₂ h₂ i₂
    have c₁ := hI hc₁ _ hq₁
    have c₂ := hI hc₂ _ hq₂
    have hcomp := (isChartCompletable_iff_exists c₁ c₂).2
      (hD p₁ p₂ hq₁ hq₂ ((intC_encC_iff c₁).2 hi₁) ((intC_encC_iff c₂).2 hi₂))
    exact hcomp.mono hp₁ hp₂

/-- **The chart interior completion event is universally measurable**, for measurable chart paths continuous on
their closed available intervals with measurable lifetimes (the restart coordinates). -/
theorem uMeasurableSet_chartInteriorCompletion {S : Type*} [MeasurableSpace S] {Γ₁ Γ₂ : S → ℝ≥0 → ℂ}
    {U₁ U₂ : S → ℝ≥0∞} (hU₁ : Measurable U₁) (hU₂ : Measurable U₂) (hΓ₁ : ∀ t, Measurable fun x => Γ₁ x t)
    (hΓ₂ : ∀ t, Measurable fun x => Γ₂ x t) (hc₁ : ∀ x, ContinuousOn (Γ₁ x) {t | (t : ℝ≥0∞) ≤ U₁ x})
    (hc₂ : ∀ x, ContinuousOn (Γ₂ x) {t | (t : ℝ≥0∞) ≤ U₂ x}) :
    LQGMetric.UMeasurableSet {x | ChartInteriorCompletion (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x)} := by
  have he₁ : Measurable fun x => encC (Γ₁ x) :=
    measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k => hΓ₁ (dyad n k)
  have he₂ : Measurable fun x => encC (Γ₂ x) :=
    measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k => hΓ₂ (dyad n k)
  have hset : {x | ChartInteriorCompletion (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x)} =
      ⋂ p₁ : ℕ × ℕ, ⋂ p₂ : ℕ × ℕ,
        ({x | (dyad p₁.1 p₁.2 : ℝ≥0∞) < U₁ x ∧ (dyad p₂.1 p₂.2 : ℝ≥0∞) < U₂ x ∧
          IntC (encC (Γ₁ x)) (dyad p₁.1 p₁.2) ∧ IntC (encC (Γ₂ x)) (dyad p₂.1 p₂.2)}ᶜ ∪
        (fun x => (encC (Γ₁ x), encC (Γ₂ x))) ⁻¹'
          {p | ∃ y, (p, y) ∈ CompRelS (dyad p₁.1 p₁.2) (dyad p₂.1 p₂.2)}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, mem_preimage, not_and]
    rw [chartInteriorCompletion_iff (hc₁ x) (hc₂ x)]
    refine forall_congr' fun p₁ => forall_congr' fun p₂ => ?_
    constructor
    · intro h
      by_cases hA : (dyad p₁.1 p₁.2 : ℝ≥0∞) < U₁ x ∧ (dyad p₂.1 p₂.2 : ℝ≥0∞) < U₂ x ∧
          IntC (encC (Γ₁ x)) (dyad p₁.1 p₁.2) ∧ IntC (encC (Γ₂ x)) (dyad p₂.1 p₂.2)
      · exact Or.inr (h hA.1 hA.2.1 hA.2.2.1 hA.2.2.2)
      · left
        intro a b c d
        exact hA ⟨a, b, c, d⟩
    · rintro (h | h) a b c d
      · exact absurd d (h a b c)
      · exact h
  rw [hset]
  refine LQGMetric.UMeasurableSet.iInter fun p₁ => LQGMetric.UMeasurableSet.iInter fun p₂ => ?_
  refine LQGMetric.UMeasurableSet.union (LQGMetric.UMeasurableSet.of_measurableSet ?_).compl
    ((uMeasurableSet_completableCode _ _).preimage (he₁.prodMk he₂))
  refine (measurableSet_lt measurable_const hU₁).inter ((measurableSet_lt measurable_const hU₂).inter
    (((measurable_intC _).comp he₁).setOf.inter ((measurable_intC _).comp he₂).setOf))

/-! ### Integrating a universally measurable event over the datum -/

/-- **The lift back for universally measurable events**: an event of `(datum, restart point)` which is universally
measurable and holds for almost every datum under almost every kernel measure holds almost surely on `M`. -/
theorem ae_mem_of_ae_ae_compProd_of_uMeasurable {Ω C S : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [MeasurableSpace S] {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M) {β : Ω → C}
    {X : Ω → S} (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) {E : Set (C × S)}
    (hE : LQGMetric.UMeasurableSet E) (h : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), (c, s) ∈ E) :
    ∀ᵐ ω ∂P, ω ∈ M → (β ω, X ω) ∈ E := by
  set μ := (P.restrict M).map β ⊗ₘ K with hμ
  obtain ⟨t, hts, htm, hteq⟩ := (hE μ inferInstance).exists_measurable_subset_ae_eq
  have h1 : ∀ᵐ p ∂μ, (p ∈ t ↔ p ∈ E) := by
    filter_upwards [hteq.mem_iff] with p hp
    exact hp
  have h2 := Measure.ae_ae_of_ae_compProd h1
  have h3 : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), (c, s) ∈ t := by
    filter_upwards [h, h2] with c hc hc'
    filter_upwards [hc, hc'] with s hs hs'
    exact hs'.2 hs
  have h4 : ∀ᵐ p ∂μ, p ∈ t := Measure.ae_compProd_of_ae_ae htm h3
  rw [← hlaw] at h4
  have h5 := (ae_map_iff (hβ.prodMk hX).aemeasurable htm).1 h4
  filter_upwards [(ae_restrict_iff' hM).1 h5] with ω hω hωM
  exact hts (hω hωM)

end RLC

end InteractingSLE
