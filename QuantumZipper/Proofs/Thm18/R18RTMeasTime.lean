import QuantumZipper.Proofs.Thm18.R18RTNodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT3, part 1: the length time of the unzipping reduced to rational times

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26) treats `Z^LEN_{−ℓ}` as a measurable map of the
configuration. Its first ingredient is the time `t'` at which the length of `η[0,t']` seen from
`D₁` reaches `ℓ` (`lenTimeOpen`, an `sInf` over real times). Since the length is nondecreasing in
the time, the set of times is an up-ray of `[0,∞)` and its infimum is the infimum over its rational
points (`sInf_eq_sInf_rat_of_upClosed`); a countable infimum of measurable readings is measurable
(`measurable_sInf_ratSet`). This is the argument of `MeasUnzip.measurable_hitTime_unzip_comp`
(MeasUnzipLen.lean) without the finite horizon.

`downDataMeasCStmt_of_read`: `DownDataMeasCStmt` (`DownDataMeasStmt` for continuous drivers)
from `DownLenCapReadStmt` (measurable readings of
the lengths at rational times and monotonicity on a Borel set, and a jointly Borel reading of the
fixed-time unzipping).

Own elementary bookkeeping (measurability the paper leaves implicit).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-! ## Infimum of an up-closed set of times -/

/-- The rational points of a set of reals. -/
def ratPts (S : Set ℝ) : Set ℝ := {s | s ∈ S ∧ ∃ q : ℚ, (q : ℝ) = s}

theorem sInf_eq_sInf_rat_of_upClosed {S : Set ℝ} (h0 : ∀ s ∈ S, 0 ≤ s)
    (hup : ∀ s ∈ S, ∀ t, s ≤ t → t ∈ S) : sInf S = sInf (ratPts S) := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · have : ratPts S = ∅ := by
      ext s; simp [ratPts, hS]
    rw [this, hS]
  · have hbS : BddBelow S := ⟨0, fun s hs => h0 s hs⟩
    have hsub : ratPts S ⊆ S := fun s hs => hs.1
    obtain ⟨s₀, hs₀⟩ := hS
    obtain ⟨q₀, hq₀, -⟩ := exists_rat_btwn (lt_add_one s₀)
    have hne : (ratPts S).Nonempty := ⟨q₀, hup s₀ hs₀ _ hq₀.le, q₀, rfl⟩
    have hbR : BddBelow (ratPts S) := ⟨0, fun s hs => h0 s hs.1⟩
    refine le_antisymm (csInf_le_csInf hbS hne hsub) ?_
    refine le_of_forall_gt fun b hb => ?_
    obtain ⟨s, hs, hsb⟩ := (csInf_lt_iff hbS ⟨s₀, hs₀⟩).1 hb
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hsb
    exact lt_of_le_of_lt (csInf_le hbR ⟨hup s hs _ hq1.le, q, rfl⟩) hq2

/-- The rational times read by measurable functions. -/
def ratSet {α : Type*} (c : ℝ≥0∞) (L : ℚ → α → ℝ≥0∞) (x : α) : Set ℝ :=
  {s | ∃ q : ℚ, 0 ≤ q ∧ c ≤ L q x ∧ (q : ℝ) = s}

theorem measurable_sInf_ratSet {α : Type*} [MeasurableSpace α] (c : ℝ≥0∞) {L : ℚ → α → ℝ≥0∞}
    (hL : ∀ q, Measurable (L q)) : Measurable fun x => sInf (ratSet c L x) := by
  refine measurable_of_Iio fun a => ?_
  have hset : (fun x => sInf (ratSet c L x)) ⁻¹' Iio a =
      ((⋂ q : ℚ, {x | ¬ (0 ≤ q ∧ c ≤ L q x)}) ∩ {_x | 0 < a}) ∪
        ⋃ q : ℚ, {x | 0 ≤ q ∧ c ≤ L q x ∧ (q : ℝ) < a} := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_setOf_eq, mem_iUnion,
      mem_iInter]
    by_cases hx : ∃ q : ℚ, 0 ≤ q ∧ c ≤ L q x
    · obtain ⟨q₀, hq₀⟩ := hx
      have hne : (ratSet c L x).Nonempty := ⟨q₀, q₀, hq₀.1, hq₀.2, rfl⟩
      have hbd : BddBelow (ratSet c L x) := ⟨0, by
        rintro s ⟨q, hq, -, rfl⟩; exact_mod_cast hq⟩
      rw [csInf_lt_iff hbd hne]
      constructor
      · rintro ⟨b, ⟨q, hq, hcq, rfl⟩, hb⟩
        exact Or.inr ⟨q, hq, hcq, hb⟩
      · rintro (⟨h, -⟩ | ⟨q, hq, hcq, hb⟩)
        · exact absurd hq₀ (h q₀)
        · exact ⟨q, ⟨q, hq, hcq, rfl⟩, hb⟩
    · push Not at hx
      have hem : ratSet c L x = ∅ := by
        ext s; simp only [ratSet, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨q, hq, hcq, -⟩; exact absurd hcq (not_le.2 (hx q hq))
      rw [hem, Real.sInf_empty]
      constructor
      · intro ha; exact Or.inl ⟨fun q hq => absurd hq.2 (not_le.2 (hx q hq.1)), ha⟩
      · rintro (⟨-, ha⟩ | ⟨q, hq, hcq, -⟩)
        · exact ha
        · exact absurd hcq (not_le.2 (hx q hq))
  rw [hset]
  refine ((MeasurableSet.iInter fun q : ℚ => ?_).inter ?_).union (MeasurableSet.iUnion fun q : ℚ => ?_)
  · by_cases hq : (0 : ℚ) ≤ q
    · have : {x | ¬ (0 ≤ q ∧ c ≤ L q x)} = {x | L q x < c} := by
        ext x; simp [hq]
      rw [this]; exact measurableSet_lt (hL q) measurable_const
    · have : {x | ¬ (0 ≤ q ∧ c ≤ L q x)} = univ := by
        ext x; simp [hq]
      rw [this]; exact MeasurableSet.univ
  · by_cases ha : (0 : ℝ) < a
    · simp [ha]
    · simp [ha]
  · by_cases hq : (0 : ℚ) ≤ q ∧ (q : ℝ) < a
    · have : {x | 0 ≤ q ∧ c ≤ L q x ∧ (q : ℝ) < a} = {x | c ≤ L q x} := by
        ext x; simp [hq.1, hq.2]
      rw [this]; exact measurableSet_le measurable_const (hL q)
    · have : {x | 0 ≤ q ∧ c ≤ L q x ∧ (q : ℝ) < a} = ∅ := by
        ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, -, h3⟩; exact hq ⟨h1, h3⟩
      rw [this]; exact MeasurableSet.empty

/-- **The length time on rational readings.** If the length is nondecreasing on `[0,∞)` and read
by `L q` at the rational times `q ≥ 0`, then `lenTimeOpen` is the infimum of the rational set. -/
theorem lenTimeOpen_eq_sInf_ratSet {α : Type*} {γ ℓ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    {L : ℚ → α → ℝ≥0∞} {x : α}
    (hL : ∀ q : ℚ, 0 ≤ q → (unzipLengthsOpen γ c q).1 = L q x)
    (hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (unzipLengthsOpen γ c s).1 ≤ (unzipLengthsOpen γ c t).1) :
    lenTimeOpen γ ℓ c = sInf (ratSet (ENNReal.ofReal ℓ) L x) := by
  unfold lenTimeOpen
  rw [sInf_eq_sInf_rat_of_upClosed
    (S := {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsOpen γ c s).1}) (fun s hs => hs.1)
    (fun s hs t hst => ⟨hs.1.trans hst, hs.2.trans (hmono s t hs.1 hst)⟩)]
  congr 1
  ext s
  simp only [ratPts, ratSet, mem_setOf_eq]
  constructor
  · rintro ⟨⟨hs0, hs⟩, q, rfl⟩
    exact ⟨q, by exact_mod_cast hs0, by rw [← hL q (by exact_mod_cast hs0)]; exact hs, rfl⟩
  · rintro ⟨q, hq, hcq, rfl⟩
    exact ⟨⟨by exact_mod_cast hq, by rw [hL q hq]; exact hcq⟩, q, rfl⟩

/-! ## `DownDataMeasCStmt` from rational length readings and a fixed-time reading -/

/-- **`DownDataMeasStmt` for continuous drivers.** `DownDataMeasStmt` with the deterministic
equation required only for data whose driver is continuous. (As stated, `DownDataMeasStmt` asks the
equation also at data whose driver is discontinuous, and there its driver component evaluates the
driver at the data-dependent time `t' + a² s`, which no Borel `Dm` can do on a Borel `G` of positive
law: see the RT3 report.) The data of `Z^LEN_ℓ c₀`, where the node is applied, have continuous
drivers. -/
def DownDataMeasCStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ →
      ∃ (G : Set ((ℕ → ℝ) × (ℝ≥0 → ℝ)))
        (Dm : (ℕ → ℝ) × (ℝ≥0 → ℝ) → (ℕ → ℝ) × (ℝ≥0 → ℝ)),
        MeasurableSet G ∧ Measurable Dm ∧
        (∀ d : E6.FullData, πd d ∈ G → Continuous d.2 →
          Dm (πd d) = πd (offData (zipLenDownA γ ℓ (configOfData γ d)).toPair)) ∧
        ∀ᵐ ω ∂P, πd (offData (wedgeAConfig γ B Y ω).toPair) ∈ G

/-- **RT3 remainder** (for continuous drivers): on a Borel set `G` of masked data carrying the
wedge data a.s., the open-arc length of the unzipping of the pieces is nondecreasing in the time
and read by Borel functions `L q` at the rational times; and the unzipping of the pieces at a
fixed time `t`, followed by the rescaling (1.8), is read by one jointly Borel function `Ψ` of
`(πd d, t)` on a Borel set `G₂` that a.s. contains the wedge data paired with its length time. -/
def DownLenCapReadStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ →
      ∃ (G : Set ((ℕ → ℝ) × (ℝ≥0 → ℝ))) (L : ℚ → (ℕ → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
        (G₂ : Set (((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ))
        (Ψ : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ → (ℕ → ℝ) × (ℝ≥0 → ℝ)),
        MeasurableSet G ∧ (∀ q, Measurable (L q)) ∧ MeasurableSet G₂ ∧ Measurable Ψ ∧
        (∀ d : E6.FullData, πd d ∈ G → Continuous d.2 →
          (∀ q : ℚ, 0 ≤ q → (unzipLengthsOpen γ (configOfData γ d).toPair q).1 = L q (πd d)) ∧
          ∀ s t : ℝ, 0 ≤ s → s ≤ t → (unzipLengthsOpen γ (configOfData γ d).toPair s).1 ≤
            (unzipLengthsOpen γ (configOfData γ d).toPair t).1) ∧
        (∀ (d : E6.FullData) (t : ℝ), (πd d, t) ∈ G₂ → Continuous d.2 →
          Ψ (πd d, t) = πd (offData (canonAConfig γ (zipCapDownA γ t (configOfData γ d))).toPair)) ∧
        ∀ᵐ ω ∂P, πd (offData (wedgeAConfig γ B Y ω).toPair) ∈ G ∧
          (πd (offData (wedgeAConfig γ B Y ω).toPair),
            lenTimeOpen γ ℓ (configOfData γ (offData (wedgeAConfig γ B Y ω).toPair)).toPair) ∈ G₂

/-- **RT3 (continuous drivers) from its remainder**: the length time is the Borel infimum of the
rational readings. -/
theorem downDataMeasCStmt_of_read (h : DownLenCapReadStmt) : DownDataMeasCStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  obtain ⟨G, L, G₂, Ψ, hG, hL, hG₂, hΨ, hlen, hcap, hae⟩ := h γ P B Y hS hIn ℓ hℓ
  set τ : (ℕ → ℝ) × (ℝ≥0 → ℝ) → ℝ := fun x => sInf (ratSet (ENNReal.ofReal ℓ) L x) with hτdef
  have hτ : Measurable τ := measurable_sInf_ratSet _ hL
  have hpair : Measurable fun x : (ℕ → ℝ) × (ℝ≥0 → ℝ) => (x, τ x) := measurable_id.prodMk hτ
  have hτeq : ∀ d : E6.FullData, πd d ∈ G → Continuous d.2 →
      lenTimeOpen γ ℓ (configOfData γ d).toPair = τ (πd d) := fun d hd hc =>
    lenTimeOpen_eq_sInf_ratSet (hlen d hd hc).1 (hlen d hd hc).2
  refine ⟨G ∩ (fun x => (x, τ x)) ⁻¹' G₂, fun x => Ψ (x, τ x), hG.inter (hpair hG₂),
    hΨ.comp hpair, ?_, ?_⟩
  · intro d hd hc
    show Ψ (πd d, τ (πd d)) = _
    rw [hcap d _ hd.2 hc, ← hτeq d hd.1 hc]
    rfl
  · filter_upwards [hae, D74.ae_wedgeConfig_snd_good hS] with ω hω hgood
    refine ⟨hω.1, ?_⟩
    have hc : Continuous (offData (wedgeAConfig γ B Y ω).toPair).2 :=
      hgood.1.comp NNReal.continuous_coe
    show (πd (offData (wedgeAConfig γ B Y ω).toPair),
      τ (πd (offData (wedgeAConfig γ B Y ω).toPair))) ∈ G₂
    rw [← hτeq _ hω.1 hc]
    exact hω.2

end R18
end QuantumZipper
