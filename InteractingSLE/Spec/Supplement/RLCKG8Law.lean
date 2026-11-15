/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCKG8
import InteractingSLE.Spec.Supplement.RLCFAvgCode
import InteractingSLE.Spec.Sec7.Prop74Order
import InteractingSLE.Spec.Sec7.InteractionProbLemma77

/-!
# Lemma G8's reference property passes from one coupling to every coupling

Packet PROVE-RLC-K, item (h) of `planning/handoffs/PROVE-RLC-G.md` ("From the restart kernel's coupling to all
couplings via canonical flow codes; the completable event must be universally measurable in the codes, and the field
law must be fixed by `IsGFFWithBoundaryData`"). Source: Lemma G8 is stated for "the conditional pair" of one datum,
and the frozen flow-line notion is universal: Lemma 7.5's determining functions make both flows Borel functions of the
field in every coupling, and the field law is fixed by its boundary data.

* `lowSet v`: the closed set `{Im ≤ 0, Re ≤ v}`; a point of `ℍ̄` avoids it iff it is in `ℍ` or real beyond `v`;
* `RefC v q₁ U₁ q₂ U₂`: the countable form of `RefCompletable (Ioi v)` on dyadic codes;
  **`refCompletable_iff`** (for paths continuous in `ℍ̄` up to their lifetimes) and
  **`uMeasurableSet_refC`** (universal measurability, Lusin, through `uMeasurableSet_completableCode`);
* **`isRefFrame_of_one`**: if one coupling of the GFF with data `c` and the two flows satisfies `RefCompletable` almost
  surely, every coupling does (`IsRefFrame`), by Lemma 7.5 (`Theorem15.Lemma75Statement`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Theorem15D5 Sec2.Assembly

/-! ### The admissible region through a closed set -/

/-- The closed set `{Im ≤ 0, Re ≤ v}`: a point of `ℍ̄` avoids it iff it is in `ℍ` or real beyond `v`. -/
def lowSet (v : ℝ) : Set ℂ := {z | z.im ≤ 0 ∧ z.re ≤ v}

theorem isClosed_lowSet (v : ℝ) : IsClosed (lowSet v) :=
  (isClosed_le Complex.continuous_im continuous_const).inter (isClosed_le Complex.continuous_re continuous_const)

theorem lowSet_nonempty (v : ℝ) : (lowSet v).Nonempty := ⟨(v : ℂ), by simp [lowSet]⟩

theorem notMem_lowSet_iff {v : ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    z ∉ lowSet v ↔ z ∈ H ∨ (z.im = 0 ∧ z.re ∈ Ioi v) := by
  simp only [lowSet, mem_ofPred_eq, not_and_or, not_le, mem_Ioi]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · rcases hz.lt_or_eq with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.symm, h⟩
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl h
    · exact Or.inr h

/-! ### The countable form of the reference property -/

/-- **The reference property in countable form**: for every pair of dyadic times before the lifetimes, if both coded
prefixes avoid `lowSet v` after time `0` and have a common point after time `0`, the codes are completable. -/
def RefC (v : ℝ) (q₁ : CCode) (U₁ : ℝ≥0∞) (q₂ : CCode) (U₂ : ℝ≥0∞) : Prop :=
  ∀ p₁ p₂ : ℕ × ℕ, (dyad p₁.1 p₁.2 : ℝ≥0∞) < U₁ → (dyad p₂.1 p₂.2 : ℝ≥0∞) < U₂ →
    AvoidC q₁ (dyad p₁.1 p₁.2) (lowSet v) → AvoidC q₂ (dyad p₂.1 p₂.2) (lowSet v) →
    CommonC q₁ (dyad p₁.1 p₁.2) q₂ (dyad p₂.1 p₂.2) →
    ∃ y, ((q₁, q₂), y) ∈ CompRelS (dyad p₁.1 p₁.2) (dyad p₂.1 p₂.2)

/-- **The countable reference property is universally measurable.** -/
theorem uMeasurableSet_refC (v : ℝ) : LQGMetric.UMeasurableSet
    {x : (CCode × ℝ≥0∞) × (CCode × ℝ≥0∞) | RefC v x.1.1 x.1.2 x.2.1 x.2.2} := by
  set X := (CCode × ℝ≥0∞) × (CCode × ℝ≥0∞)
  have mq₁ : Measurable fun x : X => x.1.1 := measurable_fst.comp measurable_fst
  have mq₂ : Measurable fun x : X => x.2.1 := measurable_fst.comp measurable_snd
  have mU₁ : Measurable fun x : X => x.1.2 := measurable_snd.comp measurable_fst
  have mU₂ : Measurable fun x : X => x.2.2 := measurable_snd.comp measurable_snd
  refine uMeasurableSet_setOf_forall fun p₁ => uMeasurableSet_setOf_forall fun p₂ => ?_
  refine uMeasurableSet_setOf_imp (measurableSet_lt measurable_const mU₁) <|
    uMeasurableSet_setOf_imp (measurableSet_lt measurable_const mU₂) <|
    uMeasurableSet_setOf_imp ((measurable_avoidC _ _).comp mq₁).setOf <|
    uMeasurableSet_setOf_imp ((measurable_avoidC _ _).comp mq₂).setOf <|
    uMeasurableSet_setOf_imp ((measurable_commonC _ _).comp (mq₁.prodMk mq₂)).setOf ?_
  exact (uMeasurableSet_completableCode _ _).preimage (mq₁.prodMk mq₂)

/-- A path continuous up to `U` is continuous on `[0, a]` for `a < U`. -/
theorem continuousOn_Iic_of_lt {g : ℝ≥0 → ℂ} {U : ℝ≥0∞} (hc : ContinuousOn g {t | (t : ℝ≥0∞) ≤ U}) {a : ℝ≥0}
    (ha : (a : ℝ≥0∞) < U) : ContinuousOn g (Iic a) :=
  hc.mono fun _ ht => (ENNReal.coe_le_coe.2 ht).trans ha.le

/-- **A dyadic extension of an admissible prefix**: a path continuous in `ℍ̄` up to `U`, admissible (off `lowSet v`)
on `(0, s]` with `0 < s < U`, stays admissible up to some dyadic time `d ≥ s` with `d < U`. -/
theorem exists_dyad_adm {g : ℝ≥0 → ℂ} {U : ℝ≥0∞} {v : ℝ} (hc : ContinuousOn g {t | (t : ℝ≥0∞) ≤ U})
    {s : ℝ≥0} (hs0 : 0 < s) (hs : (s : ℝ≥0∞) < U) (hadm : ∀ t, 0 < t → t ≤ s → g t ∉ lowSet v) :
    ∃ p : ℕ × ℕ, s ≤ dyad p.1 p.2 ∧ (dyad p.1 p.2 : ℝ≥0∞) < U ∧ ∀ t, 0 < t → t ≤ dyad p.1 p.2 → g t ∉ lowSet v := by
  obtain ⟨y, hsy, hyU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hsy' : s < y := ENNReal.coe_lt_coe.1 hsy
  -- continuity at `s` within `[0, y]`
  have hcy : ContinuousOn g (Iic y) := continuousOn_Iic_of_lt hc hyU
  have hgs : g s ∈ (lowSet v)ᶜ := hadm s hs0 le_rfl
  have hev : ∀ᶠ t in 𝓝 s, g t ∈ (lowSet v)ᶜ := by
    have hca : ContinuousAt g s := hcy.continuousAt (Iic_mem_nhds hsy')
    exact hca.preimage_mem_nhds ((isClosed_lowSet v).isOpen_compl.mem_nhds hgs)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set z : ℝ≥0 := min y (s + ⟨δ, hδ.le⟩) with hz
  have hsz : s < z := lt_min hsy' (lt_add_of_pos_right _ (by exact_mod_cast hδ))
  obtain ⟨r, ⟨p, hp⟩, hsr, hrz⟩ := Supp9D.exists_dyadSet_btwn hsz
  simp only at hp
  refine ⟨p, hp ▸ hsr.le, hp ▸ lt_of_le_of_lt (ENNReal.coe_le_coe.2 ((hrz.le).trans (min_le_left _ _))) hyU, ?_⟩
  intro t ht htr
  rw [hp] at htr
  rcases le_or_gt t s with hts | hts
  · exact hadm t ht hts
  · refine hball ?_
    have htz : t < s + ⟨δ, hδ.le⟩ := lt_of_le_of_lt htr (lt_of_lt_of_le hrz (min_le_right _ _))
    have h1 : (t : ℝ) < s + δ := by
      have e : ((s + ⟨δ, hδ.le⟩ : ℝ≥0) : ℝ) = (s : ℝ) + δ := rfl
      rw [← e]
      exact NNReal.coe_lt_coe.2 htz
    have h7 : (s : ℝ) < t := by exact_mod_cast hts
    rw [NNReal.dist_eq, abs_lt]
    constructor <;> linarith

/-- The reference property sees the paths only through their values before the lifetimes. -/
theorem RefCompletable.congr {K : Set ℝ} {g₁ g₂ g₁' g₂' : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞}
    (h : RefCompletable K g₁ U₁ g₂ U₂) (e₁ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U₁ → g₁ t = g₁' t)
    (e₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U₂ → g₂ t = g₂' t) : RefCompletable K g₁' U₁ g₂' U₂ := by
  intro s₁ s₂ hs₁ hs₂ hp₁ hp₂ hcom
  have f₁ : ∀ t ≤ s₁, g₁ t = g₁' t := fun t ht => e₁ t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hs₁)
  have f₂ : ∀ t ≤ s₂, g₂ t = g₂' t := fun t ht => e₂ t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hs₂)
  refine (h s₁ s₂ hs₁ hs₂ (fun t ht hts => ?_) (fun t ht hts => ?_) ?_).congr f₁ f₂
  · rw [f₁ t hts]; exact hp₁ t ht hts
  · rw [f₂ t hts]; exact hp₂ t ht hts
  · obtain ⟨t₁, t₂, a1, a2, a3, a4, he⟩ := hcom
    exact ⟨t₁, t₂, a1, a2, a3, a4, by rw [f₁ t₁ a2, f₂ t₂ a4]; exact he⟩

/-- **The reference property through codes**: for paths continuous in `ℍ̄` up to their lifetimes,
`RefCompletable (Ioi v)` is equivalent to its countable form on the codes. -/
theorem refCompletable_iff {g₁ g₂ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞} {v : ℝ}
    (hc₁ : ContinuousOn g₁ {t | (t : ℝ≥0∞) ≤ U₁}) (hc₂ : ContinuousOn g₂ {t | (t : ℝ≥0∞) ≤ U₂})
    (hm₁ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U₁ → 0 ≤ (g₁ t).im) (hm₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U₂ → 0 ≤ (g₂ t).im) :
    RefCompletable (Ioi v) g₁ U₁ g₂ U₂ ↔ RefC v (encC g₁) U₁ (encC g₂) U₂ := by
  have hadm : ∀ {g : ℝ≥0 → ℂ} {U : ℝ≥0∞}, (∀ t : ℝ≥0, (t : ℝ≥0∞) < U → 0 ≤ (g t).im) → ∀ a : ℝ≥0,
      (a : ℝ≥0∞) < U → ((∀ t, 0 < t → t ≤ a → g t ∉ lowSet v) ↔
        ∀ t : ℝ≥0, 0 < t → t ≤ a → g t ∈ H ∨ ((g t).im = 0 ∧ (g t).re ∈ Ioi v)) := by
    intro g U hm a ha
    refine forall_congr' fun t => imp_congr_right fun _ => forall_congr' fun hta => ?_
    exact notMem_lowSet_iff (hm t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hta) ha))
  constructor
  · intro hR p₁ p₂ h₁ h₂ a₁ a₂ hcm
    have c₁ := continuousOn_Iic_of_lt hc₁ h₁
    have c₂ := continuousOn_Iic_of_lt hc₂ h₂
    have b₁ := (avoidC_encC_iff c₁ (isClosed_lowSet v) (lowSet_nonempty v)).1 a₁
    have b₂ := (avoidC_encC_iff c₂ (isClosed_lowSet v) (lowSet_nonempty v)).1 a₂
    exact (isChartCompletable_iff_exists c₁ c₂).1 (hR _ _ h₁ h₂ ((hadm hm₁ _ h₁).1 b₁) ((hadm hm₂ _ h₂).1 b₂)
      ((commonC_encC_iff c₁ c₂).1 hcm))
  · intro hD s₁ s₂ h₁ h₂ p₁ p₂ hcom
    obtain ⟨t₁, t₂, a1, a2, a3, a4, he⟩ := hcom
    have hs₁ : 0 < s₁ := lt_of_lt_of_le a1 a2
    have hs₂ : 0 < s₂ := lt_of_lt_of_le a3 a4
    obtain ⟨q₁, hq₁s, hq₁U, hq₁a⟩ := exists_dyad_adm hc₁ hs₁ h₁ ((hadm hm₁ _ h₁).2 p₁)
    obtain ⟨q₂, hq₂s, hq₂U, hq₂a⟩ := exists_dyad_adm hc₂ hs₂ h₂ ((hadm hm₂ _ h₂).2 p₂)
    have c₁ := continuousOn_Iic_of_lt hc₁ hq₁U
    have c₂ := continuousOn_Iic_of_lt hc₂ hq₂U
    have hcm : CommonC (encC g₁) (dyad q₁.1 q₁.2) (encC g₂) (dyad q₂.1 q₂.2) :=
      (commonC_encC_iff c₁ c₂).2 ⟨t₁, t₂, a1, a2.trans hq₁s, a3, a4.trans hq₂s, he⟩
    have hC := (isChartCompletable_iff_exists c₁ c₂).2 (hD q₁ q₂ hq₁U hq₂U
      ((avoidC_encC_iff c₁ (isClosed_lowSet v) (lowSet_nonempty v)).2 hq₁a)
      ((avoidC_encC_iff c₂ (isClosed_lowSet v) (lowSet_nonempty v)).2 hq₂a) hcm)
    exact hC.mono hq₁s hq₂s

/-! ### From one coupling to every coupling -/

/-- An almost-sure property of a universally measurable kind passes along equal laws. -/
theorem ae_mem_of_map_eq_of_uMeasurable {F : Type*} [MeasurableSpace F] {G : Set F}
    (hG : LQGMetric.UMeasurableSet G) {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {P₀ : Measure Ω₀}
    {P : Measure Ω} [IsFiniteMeasure P₀] {h₀ : Ω₀ → F} {h : Ω → F} (hh₀ : Measurable h₀) (hh : Measurable h)
    (hlaw : P.map h = P₀.map h₀) (h0 : ∀ᵐ x ∂P₀, h₀ x ∈ G) : ∀ᵐ x ∂P, h x ∈ G := by
  obtain ⟨t, hts, htm, hteq⟩ := (hG (P₀.map h₀) inferInstance).exists_measurable_subset_ae_eq
  have hnull : (P₀.map h₀) (G \ t) = 0 := (ae_eq_set.1 hteq).2
  obtain ⟨N, hNs, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  have hN : ∀ᵐ x ∂P₀, h₀ x ∉ N := by
    have : P₀ (h₀ ⁻¹' N) = 0 := by rw [← Measure.map_apply hh₀ hNm]; exact hN0
    exact measure_eq_zero_iff_ae_notMem.1 this
  have h1 : ∀ᵐ x ∂P₀, h₀ x ∈ t := by
    filter_upwards [h0, hN] with x hx hxN
    by_contra hxt
    exact hxN (hNs ⟨hx, hxt⟩)
  have h2 : ∀ᵐ y ∂(P₀.map h₀), y ∈ t := (ae_map_iff hh₀.aemeasurable htm).2 h1
  rw [← hlaw] at h2
  filter_upwards [ae_of_ae_map hh.aemeasurable h2] with x hx
  exact hts hx

/-- **The reference property passes from one coupling to every coupling** (Lemma 7.5's universal determination and
the uniqueness of the field law). -/
theorem isRefFrame_of_one (h75 : Theorem15.Lemma75Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {θ₁ θ₂ : ℝ} {c : ℝ → ℝ} {Ĵ : Finset ℝ} (hc : IsPiecewiseConstantBoundaryData c Ĵ) {w₁ w₂ v : ℝ}
    {S₀ : Type u} [MeasurableSpace S₀] (Q₀ : Measure S₀) [IsProbabilityMeasure Q₀]
    (H₀ : S₀ → LQGMetric.DistOn upperHalfPlaneOpens) (hH₀ : IsGFFWithBoundaryData Q₀ H₀ c Ĵ)
    (Γ₁ Γ₂ : S₀ → ℝ≥0 → ℂ) (U₁ U₂ : S₀ → ℝ≥0∞) (h₁ : IsFlowLine κ c Ĵ w₁ θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c Ĵ w₂ θ₂ Q₀ H₀ Γ₂ U₂)
    (href : ∀ᵐ x ∂Q₀, RefCompletable (Ioi v) (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x)) :
    IsRefFrame.{u} κ θ₁ θ₂ c Ĵ w₁ w₂ (Ioi v) := by
  obtain ⟨Φ₁, hΦ₁m, hΦ₁⟩ := h75 κ hκ hκ4 c Ĵ hc w₁ θ₁
  obtain ⟨Φ₂, hΦ₂m, hΦ₂⟩ := h75 κ hκ hκ4 c Ĵ hc w₂ θ₂
  set F : LQGMetric.DistOn upperHalfPlaneOpens → (CCode × ℝ≥0∞) × (CCode × ℝ≥0∞) :=
    fun f => ((encC (Φ₁ f).2, (Φ₁ f).1), (encC (Φ₂ f).2, (Φ₂ f).1)) with hF
  have hFm : Measurable F :=
    ((Sec5.Prop55Half.measurable_encC_comp fun t => (measurable_pi_apply t).comp (measurable_snd.comp hΦ₁m)).prodMk
      (measurable_fst.comp hΦ₁m)).prodMk
    ((Sec5.Prop55Half.measurable_encC_comp fun t => (measurable_pi_apply t).comp (measurable_snd.comp hΦ₂m)).prodMk
      (measurable_fst.comp hΦ₂m))
  set G : Set (LQGMetric.DistOn upperHalfPlaneOpens) :=
    F ⁻¹' {x | RefC v x.1.1 x.1.2 x.2.1 x.2.2} with hG
  have hGu : LQGMetric.UMeasurableSet G := (uMeasurableSet_refC v).preimage hFm
  -- the property of the Borel paths, given a coupling
  have key : ∀ {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
      (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q Ĥ c Ĵ →
      ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      IsFlowLine κ c Ĵ w₁ θ₁ Q Ĥ α₁ ζ₁ → IsFlowLine κ c Ĵ w₂ θ₂ Q Ĥ α₂ ζ₂ →
      ∀ᵐ x ∂Q, (Ĥ x ∈ G ↔ RefCompletable (Ioi v) (α₁ x) (ζ₁ x) (α₂ x) (ζ₂ x)) := by
    intro S _ Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ k₁ k₂
    filter_upwards [hΦ₁ Q Ĥ hĤ α₁ ζ₁ k₁, hΦ₂ Q Ĥ hĤ α₂ ζ₂ k₂, Sec7.ae_continuousOn_of_isFlowLine k₁,
      Sec7.ae_continuousOn_of_isFlowLine k₂, Supp7.ae_im_nonneg_of_isFlowLine k₁,
      Supp7.ae_im_nonneg_of_isFlowLine k₂] with x e₁ e₂ c₁ c₂ m₁ m₂
    obtain ⟨l₁, p₁⟩ := e₁
    obtain ⟨l₂, p₂⟩ := e₂
    have c₁' : ContinuousOn (Φ₁ (Ĥ x)).2 {t | (t : ℝ≥0∞) ≤ (Φ₁ (Ĥ x)).1} := by
      rw [l₁]; exact c₁.congr fun t ht => p₁ t ht
    have c₂' : ContinuousOn (Φ₂ (Ĥ x)).2 {t | (t : ℝ≥0∞) ≤ (Φ₂ (Ĥ x)).1} := by
      rw [l₂]; exact c₂.congr fun t ht => p₂ t ht
    have m₁' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (Φ₁ (Ĥ x)).1 → 0 ≤ ((Φ₁ (Ĥ x)).2 t).im := fun t ht => by
      rw [l₁] at ht; rw [p₁ t ht.le]; exact m₁ t ht.le
    have m₂' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (Φ₂ (Ĥ x)).1 → 0 ≤ ((Φ₂ (Ĥ x)).2 t).im := fun t ht => by
      rw [l₂] at ht; rw [p₂ t ht.le]; exact m₂ t ht.le
    show RefC v (encC (Φ₁ (Ĥ x)).2) (Φ₁ (Ĥ x)).1 (encC (Φ₂ (Ĥ x)).2) (Φ₂ (Ĥ x)).1 ↔ _
    rw [← refCompletable_iff c₁' c₂' m₁' m₂', l₁, l₂]
    constructor
    · intro h
      exact h.congr (fun t ht => p₁ t ht.le) (fun t ht => p₂ t ht.le)
    · intro h
      exact h.congr (fun t ht => (p₁ t ht.le).symm) (fun t ht => (p₂ t ht.le).symm)
  have h0 : ∀ᵐ x ∂Q₀, H₀ x ∈ G := by
    filter_upwards [key Q₀ H₀ hH₀ Γ₁ Γ₂ U₁ U₂ h₁ h₂, href] with x hx hr
    exact hx.2 hr
  intro S _ Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ k₁ k₂
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hc
  have hlaw : Q.map Ĥ = Q₀.map H₀ := Exist.map_eq_of_isGFFWithBoundaryData hĤ hH₀ hu₀
  filter_upwards [ae_mem_of_map_eq_of_uMeasurable hGu hH₀.1 hĤ.1 hlaw h0,
    key Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ k₁ k₂] with x hx hk
  exact hk.1 hx

end RLC

end InteractingSLE
