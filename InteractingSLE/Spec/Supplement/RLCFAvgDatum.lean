/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCFG2a
import InteractingSLE.Spec.Supplement.RLCFAvgPath

/-!
# The real completion event at one retained datum, almost surely

Packet PROVE-RLC-F, piece (iv) (Astra's Prop. 5.2 with its countable witness construction, R52; W5's real local
frame, pp. 535–536). For a datum with the canonical seed germs, almost surely the countable-form event
`RLC.RealEventC` holds for the chart pair:

* the jump part from `JumpVisitStatement` (**named input**: a flow line visits no boundary jump other than its seed
  strictly before its lifetime — W5, p. 535: "For real `p`, G12 excludes an original jump, since both paths continue");
* for every strip family satisfying the datum condition, by region: right of `w` the G8 frame
  (`RLC.ae_isChartCompletable_of_frame`) when the lower-angle right weight of the height is in `(−2, κ/2 − 2)`, and
  otherwise no visit (`RLC.ae_frameWeight_of_visit_right`); between the seeds the G2a word
  (`RLC.ae_isChartCompletable_of_mid`) when the height is admissible, and otherwise no visit (Lemma 5.1,
  `RLC.ae_admissible_of_visit'`); left of `0` the reflected G8 frame (`RLC.ae_isChartCompletable_of_frame_left`) or no
  visit (`RLC.ae_frameWeight_of_visit_left`). The countably many rational buffers are intersected
  (`RLC.exists_ae_of_ref`).

Main result: **`RLC.ae_realEventC`**. Conditional on G2a, G3, G8 (named, PROVE-RLC-C / -A / this packet) and
`JumpVisitStatement`; replaces no source theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Theorem15D5 Sec2.Assembly Restart

/-! ### Jump visits -/

/-- **Named input: no visit of a boundary jump other than the seed strictly before the lifetime** (W5's real local
frame, p. 535: "For real `p`, G12 excludes an original jump, since both paths continue"; Lemma G12, p. 504). For the
angle-`θ` flow line from `x` of a GFF with piecewise constant data `b` (jumps `J`), `0 < κ < 4`, almost surely it does
not meet any `y ∈ J`, `y ≠ x`, at a time in `(0, ζ)`. **Not proved in Lean.** Proof route: at the first visit of `y`
the marks up to `y` merge with the driver, so a visit strictly before the lifetime forces their cumulative weight to
exceed `−2` (the continuation threshold, as in `RLC.exists_merge_of_visit_right` but at the mark itself), hence
`> κ/2 − 4`, and then Lemma G12 (`Supp7.g12FlowStatement`, proved) excludes the visit. -/
def JumpVisitStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → ∀ y ∈ jumps, y ≠ x → η ω t ≠ y

/-! ### Helpers -/

/-- **A path inside an open set up to `s < U` exits it strictly after `s`.** -/
theorem lt_exitTime_of_mem {V : Set ℂ} {g : ℝ≥0 → ℂ} {U : ℝ≥0∞} {s : ℝ≥0} (hV : IsOpen V)
    (hsU : (s : ℝ≥0∞) < U) (hc : ContinuousOn g {t | (t : ℝ≥0∞) ≤ U}) (hin : ∀ t ≤ s, g t ∈ V) :
    (s : ℝ≥0∞) < exitTime V g U := by
  obtain ⟨V', hV', hVU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsU
  have hsV' : s < V' := by exact_mod_cast hV'
  have hnb : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ U} ∈ 𝓝 s :=
    mem_of_superset (Iio_mem_nhds hsV') fun t ht => (ENNReal.coe_le_coe.2 (le_of_lt ht)).trans hVU.le
  have hca : ContinuousAt g s := (hc s hsU.le).continuousAt hnb
  have hpre : g ⁻¹' V ∈ 𝓝 s := hca.preimage_mem_nhds (hV.mem_nhds (hin s le_rfl))
  obtain ⟨b', hb', hsub⟩ := exists_Ico_subset_of_mem_nhds hpre ⟨V', hsV'⟩
  obtain ⟨s', hss', hs'b⟩ := exists_between (lt_min hb' hsV')
  have hle : (s' : ℝ≥0∞) ≤ exitTime V g U := by
    refine le_exitTime (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (lt_of_lt_of_le hs'b (min_le_right _ _))) hVU.le)
      fun t ht => ?_
    rcases le_or_gt t s with h | h
    · exact hin t h
    · exact hsub ⟨h.le, lt_of_le_of_lt ht (lt_of_lt_of_le hs'b (min_le_left _ _))⟩
  exact lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hss') hle

/-- **The pathwise content of the countable prefix conditions** at a dyadic time `s` before the lifetime: the prefix
lies in the strip buffer (so `s` is strictly before the exit time), its points after time `0` are interior or real
in the open strips, and it visits a real point (in an open strip) after time `0`. -/
theorem path_of_codes {g : ℝ≥0 → ℂ} {U : ℝ≥0∞} {s : ℝ≥0} (hsU : (s : ℝ≥0∞) < U)
    (hc : ContinuousOn g {t | (t : ℝ≥0∞) ≤ U}) (hm : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U → 0 ≤ (g t).im)
    {S : List (ℚ × ℚ)} {ε' ε R ω : ℝ} (hIn : InC (encC g) s (stripBuffer S ε' ε R ω)ᶜ)
    (hAv : AvoidC (encC g) s (offStrips S)) (hHit : HitC (encC g) s realAxis) :
    (s : ℝ≥0∞) < exitTime (stripBuffer S ε' ε R ω) g U ∧
      (∀ t : ℝ≥0, 0 < t → t ≤ s → g t ∈ H ∨ ((g t).im = 0 ∧ (g t).re ∈ StripSet S)) ∧
      ∃ t : ℝ≥0, 0 < t ∧ t ≤ s ∧ (g t).im = 0 ∧ (g t).re ∈ StripSet S := by
  have hcs : ContinuousOn g (Iic s) := hc.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hsU.le
  have hin := (inC_encC_iff hcs (isClosed_compl_stripBuffer S ε' ε R ω) (compl_stripBuffer_nonempty S ε' ε R ω)).1
    hIn
  have hav := (avoidC_encC_iff hcs (isClosed_offStrips S) (offStrips_nonempty S)).1 hAv
  obtain ⟨t, ht, hts, hreal⟩ := (hitC_encC_iff hcs isClosed_realAxis realAxis_nonempty).1 hHit
  have hpt : ∀ t : ℝ≥0, 0 < t → t ≤ s → g t ∈ H ∨ ((g t).im = 0 ∧ (g t).re ∈ StripSet S) := by
    intro t ht hts
    have h0 := hm t ((ENNReal.coe_le_coe.2 hts).trans hsU.le)
    rcases h0.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq.symm, ?_⟩
      by_contra hno
      exact hav t ht hts ⟨heq.symm, hno⟩
  refine ⟨lt_exitTime_of_mem (isOpen_stripBuffer S ε' ε R ω) hsU hc fun t ht => ?_, hpt, t, ht, hts, hreal, ?_⟩
  · by_contra hno; exact hin t ht hno
  · rcases hpt t ht hts with h | h
    · exact absurd hreal (ne_of_gt h)
    · exact h.2

/-! ### Bounds for finite strip families -/

theorem exists_lt_list_fst (S : List (ℚ × ℚ)) : ∃ a : ℝ, ∀ ab ∈ S, a < ab.1 := by
  induction S with
  | nil => exact ⟨0, fun ab hab => absurd hab List.not_mem_nil⟩
  | cons ab S ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨min a ab.1 - 1, fun ab' hab' => ?_⟩
    rcases List.mem_cons.1 hab' with rfl | h
    · linarith [min_le_right a (ab'.1 : ℝ)]
    · linarith [min_le_left a (ab.1 : ℝ), ha ab' h]

theorem exists_gt_list_snd (S : List (ℚ × ℚ)) : ∃ b : ℝ, ∀ ab ∈ S, (ab.2 : ℝ) < b := by
  induction S with
  | nil => exact ⟨0, fun ab hab => absurd hab List.not_mem_nil⟩
  | cons ab S ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨max b ab.2 + 1, fun ab' hab' => ?_⟩
    rcases List.mem_cons.1 hab' with rfl | h
    · linarith [le_max_right b (ab'.2 : ℝ)]
    · linarith [le_max_left b (ab.2 : ℝ), hb ab' h]

theorem exists_between_list_fst {S : List (ℚ × ℚ)} {w : ℝ} (h : ∀ ab ∈ S, w < ab.1) :
    ∃ a : ℝ, w < a ∧ ∀ ab ∈ S, a < ab.1 := by
  induction S with
  | nil => exact ⟨w + 1, by linarith, fun ab hab => absurd hab List.not_mem_nil⟩
  | cons ab S ih =>
    obtain ⟨a, hwa, ha⟩ := ih fun ab' h' => h ab' (List.mem_cons_of_mem _ h')
    have hab := h ab List.mem_cons_self
    refine ⟨min a ((w + ab.1) / 2), lt_min hwa (by linarith), fun ab' hab' => ?_⟩
    rcases List.mem_cons.1 hab' with rfl | h'
    · linarith [min_le_right a ((w + (ab'.1 : ℝ)) / 2)]
    · linarith [min_le_left a ((w + (ab.1 : ℝ)) / 2), ha ab' h']

theorem exists_between_list_snd {S : List (ℚ × ℚ)} {w : ℝ} (h : ∀ ab ∈ S, (ab.2 : ℝ) < w) :
    ∃ b : ℝ, b < w ∧ ∀ ab ∈ S, (ab.2 : ℝ) < b := by
  induction S with
  | nil => exact ⟨w - 1, by linarith, fun ab hab => absurd hab List.not_mem_nil⟩
  | cons ab S ih =>
    obtain ⟨b, hbw, hb⟩ := ih fun ab' h' => h ab' (List.mem_cons_of_mem _ h')
    have hab := h ab List.mem_cons_self
    refine ⟨max b ((w + ab.2) / 2), max_lt hbw (by linarith), fun ab' hab' => ?_⟩
    rcases List.mem_cons.1 hab' with rfl | h'
    · linarith [le_max_right b ((w + (ab'.2 : ℝ)) / 2)]
    · linarith [le_max_left b ((w + (ab.2 : ℝ)) / 2), hb ab' h']

/-! ### The strip event for one strip family -/

/-- The part of `RLC.RealEventC` for one strip family and one collar threshold `1/(k+1)`. -/
def StripEventC (S : List (ℚ × ℚ)) (w : ℝ) (k : ℕ) (q₁ : CCode) (U₁ : ℝ≥0∞) (q₂ : CCode) (U₂ : ℝ≥0∞) : Prop :=
  ∀ ε' ε R ω : ℚ, 0 < (ε' : ℝ) → 0 < (ε : ℝ) → (ε : ℝ) < 1 / ((k : ℝ) + 1) → |w - ω| < ε → ∀ p₁ p₂ : ℕ × ℕ,
    (dyad p₁.1 p₁.2 : ℝ≥0∞) < U₁ → (dyad p₂.1 p₂.2 : ℝ≥0∞) < U₂ →
    InC q₁ (dyad p₁.1 p₁.2) (stripBuffer S ε' ε R ω)ᶜ → InC q₂ (dyad p₂.1 p₂.2) (stripBuffer S ε' ε R ω)ᶜ →
    AvoidC q₁ (dyad p₁.1 p₁.2) (offStrips S) → AvoidC q₂ (dyad p₂.1 p₂.2) (offStrips S) →
    HitC q₁ (dyad p₁.1 p₁.2) realAxis → HitC q₂ (dyad p₂.1 p₂.2) realAxis →
    CommonC q₁ (dyad p₁.1 p₁.2) q₂ (dyad p₂.1 p₂.2) →
    ∃ y, ((q₁, q₂), y) ∈ CompRelS (dyad p₁.1 p₁.2) (dyad p₂.1 p₂.2)

theorem realEventC_iff {c : BoundaryWord} {w : ℝ} {q₁ q₂ : CCode} {U₁ U₂ : ℝ≥0∞} :
    RealEventC c w q₁ U₁ q₂ U₂ ↔
      JumpFreeC c w q₁ U₁ ∧ ∀ S : List (ℚ × ℚ), StripCond c w S → ∃ k : ℕ, StripEventC S w k q₁ U₁ q₂ U₂ :=
  Iff.rfl

section Strip

variable {S' : Type*} [MeasurableSpace S'] {Q₀ : Measure S'} {Γ₁ Γ₂ : S' → ℝ≥0 → ℂ} {U₁ U₂ : S' → ℝ≥0∞}

/-- **The strip event from a reference frame lemma** (the countable intersection over rational buffers). -/
theorem exists_ae_of_ref (hc₁ : ∀ᵐ x ∂Q₀, ContinuousOn (Γ₁ x) {t | (t : ℝ≥0∞) ≤ U₁ x})
    (hc₂ : ∀ᵐ x ∂Q₀, ContinuousOn (Γ₂ x) {t | (t : ℝ≥0∞) ≤ U₂ x})
    (hm₁ : ∀ᵐ x ∂Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U₁ x → 0 ≤ (Γ₁ x t).im)
    (hm₂ : ∀ᵐ x ∂Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U₂ x → 0 ≤ (Γ₂ x t).im)
    {c : BoundaryWord} {w a₀ b₀ C : ℝ} {S : List (ℚ × ℚ)} (hSC : StripCond c w S)
    (hab : ∀ ab ∈ S, a₀ < ab.1 ∧ (ab.2 : ℝ) < b₀) (hC : ∀ ab ∈ S, c.fn ab.1 = C)
    (hL : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (G : Set ℝ) (V : Set ℂ), IsOpen G → G ⊆ Icc a₀ b₀ →
      (∀ x ∈ G, c.fn x = C ∧ x ∉ c.jumps) → IsOpen V → Bornology.IsBounded V →
      (∀ z ∈ closure V, z.im = 0 → |z.re| < ε₀ ∨ |z.re - w| < ε₀ ∨ z.re ∈ G) →
      ∀ᵐ x ∂Q₀, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < exitTime V (Γ₁ x) (U₁ x) →
        (s₂ : ℝ≥0∞) < exitTime V (Γ₂ x) (U₂ x) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → Γ₁ x t ∈ H ∨ ((Γ₁ x t).im = 0 ∧ (Γ₁ x t).re ∈ G)) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → Γ₂ x t ∈ H ∨ ((Γ₂ x t).im = 0 ∧ (Γ₂ x t).re ∈ G)) →
        (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ Γ₁ x t₁ = Γ₂ x t₂) →
        IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂) :
    ∃ k : ℕ, ∀ᵐ x ∂Q₀, StripEventC S w k (encC (Γ₁ x)) (U₁ x) (encC (Γ₂ x)) (U₂ x) := by
  obtain ⟨ε₀, hε₀, hL⟩ := hL
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε₀)
  set G : Set ℝ := {x | x ∈ Ioo a₀ b₀ ∧ (x ∉ c.jumps ∧ c.fn x = C)} with hG
  have hGo : IsOpen G := isOpen_Ioo.inter (isOpen_setOf_fn_eq c C)
  have hGab : G ⊆ Icc a₀ b₀ := fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩
  have hGC : ∀ x ∈ G, c.fn x = C ∧ x ∉ c.jumps := fun x hx => ⟨hx.2.2, hx.2.1⟩
  have hstrip : ∀ x ∈ StripSet S, x ∈ G := by
    rintro x ⟨ab, hab', h1, h2⟩
    have hf := hSC.fn_eq hab' ⟨h1.le, h2.le⟩
    exact ⟨⟨(hab ab hab').1.trans h1, h2.trans (hab ab hab').2⟩, hf.1, hf.2.trans (hC ab hab')⟩
  have hall : ∀ᵐ x ∂Q₀, ∀ r : ℚ × ℚ × ℚ × ℚ, 0 < (r.1 : ℝ) → 0 < (r.2.1 : ℝ) →
      (r.2.1 : ℝ) < 1 / ((k : ℝ) + 1) → |w - r.2.2.2| < r.2.1 →
      ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < exitTime (stripBuffer S r.1 r.2.1 r.2.2.1 r.2.2.2) (Γ₁ x) (U₁ x) →
        (s₂ : ℝ≥0∞) < exitTime (stripBuffer S r.1 r.2.1 r.2.2.1 r.2.2.2) (Γ₂ x) (U₂ x) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → Γ₁ x t ∈ H ∨ ((Γ₁ x t).im = 0 ∧ (Γ₁ x t).re ∈ G)) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → Γ₂ x t ∈ H ∨ ((Γ₂ x t).im = 0 ∧ (Γ₂ x t).re ∈ G)) →
        (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ Γ₁ x t₁ = Γ₂ x t₂) →
        IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
    refine ae_all_iff.2 fun r => ?_
    by_cases hr : 0 < (r.1 : ℝ) ∧ 0 < (r.2.1 : ℝ) ∧ (r.2.1 : ℝ) < 1 / ((k : ℝ) + 1) ∧ |w - r.2.2.2| < r.2.1
    · obtain ⟨h1, h2, h3, h4⟩ := hr
      have hVO : ∀ z ∈ closure (stripBuffer S r.1 r.2.1 r.2.2.1 r.2.2.2), z.im = 0 →
          |z.re| < ε₀ ∨ |z.re - w| < ε₀ ∨ z.re ∈ G := by
        intro z hz hz0
        rcases re_mem_of_mem_closure_stripBuffer h1 hz hz0 with h | h | h
        · left; linarith
        · right; left
          have := abs_sub_le z.re (r.2.2.2 : ℝ) w
          rw [abs_sub_comm (r.2.2.2 : ℝ) w] at this
          linarith
        · right; right
          obtain ⟨ab, hab', hx1, hx2⟩ := h
          have hf := hSC.fn_eq hab' ⟨hx1, hx2⟩
          exact ⟨⟨lt_of_lt_of_le (hab ab hab').1 hx1, lt_of_le_of_lt hx2 (hab ab hab').2⟩, hf.1,
            hf.2.trans (hC ab hab')⟩
      filter_upwards [hL G _ hGo hGab hGC (isOpen_stripBuffer _ _ _ _ _) (isBounded_stripBuffer _ _ _ _ _) hVO]
        with x hx _ _ _ _
      exact hx
    · exact Eventually.of_forall fun x h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hr
  refine ⟨k, ?_⟩
  filter_upwards [hall, hc₁, hc₂, hm₁, hm₂] with x hx c₁ c₂ m₁ m₂
  intro ε' ε R ω h1 h2 h3 h4 p₁ p₂ hp₁ hp₂ i₁ i₂ a₁ a₂ t₁ t₂ hcom
  obtain ⟨e₁, f₁, -⟩ := path_of_codes hp₁ c₁ m₁ i₁ a₁ t₁
  obtain ⟨e₂, f₂, -⟩ := path_of_codes hp₂ c₂ m₂ i₂ a₂ t₂
  have cs₁ : ContinuousOn (Γ₁ x) (Iic (dyad p₁.1 p₁.2)) :=
    c₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hp₁.le
  have cs₂ : ContinuousOn (Γ₂ x) (Iic (dyad p₂.1 p₂.2)) :=
    c₂.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hp₂.le
  have hcomp := hx (ε', ε, R, ω) h1 h2 h3 h4 _ _ e₁ e₂
    (fun t ht hts => (f₁ t ht hts).imp id fun h => ⟨h.1, hstrip _ h.2⟩)
    (fun t ht hts => (f₂ t ht hts).imp id fun h => ⟨h.1, hstrip _ h.2⟩)
    ((commonC_encC_iff cs₁ cs₂).1 hcom)
  exact (isChartCompletable_iff_exists cs₁ cs₂).1 hcomp

/-- **The strip event when one of the two paths almost surely visits no strip before its lifetime** (the
inadmissible or nonhitting heights). -/
theorem exists_ae_of_noVisit (hc₁ : ∀ᵐ x ∂Q₀, ContinuousOn (Γ₁ x) {t | (t : ℝ≥0∞) ≤ U₁ x})
    (hc₂ : ∀ᵐ x ∂Q₀, ContinuousOn (Γ₂ x) {t | (t : ℝ≥0∞) ≤ U₂ x})
    (hm₁ : ∀ᵐ x ∂Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U₁ x → 0 ≤ (Γ₁ x t).im)
    (hm₂ : ∀ᵐ x ∂Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U₂ x → 0 ≤ (Γ₂ x t).im) {w : ℝ} {S : List (ℚ × ℚ)}
    (hno : ∀ᵐ x ∂Q₀, (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < U₁ x → (Γ₁ x t).im = 0 → (Γ₁ x t).re ∉ StripSet S) ∨
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < U₂ x → (Γ₂ x t).im = 0 → (Γ₂ x t).re ∉ StripSet S)) :
    ∃ k : ℕ, ∀ᵐ x ∂Q₀, StripEventC S w k (encC (Γ₁ x)) (U₁ x) (encC (Γ₂ x)) (U₂ x) := by
  refine ⟨0, ?_⟩
  filter_upwards [hno, hc₁, hc₂, hm₁, hm₂] with x hx c₁ c₂ m₁ m₂
  intro ε' ε R ω _ _ _ _ p₁ p₂ hp₁ hp₂ i₁ i₂ a₁ a₂ t₁ t₂ _
  obtain ⟨-, -, s, hs, hsp, hs0, hsS⟩ := path_of_codes hp₁ c₁ m₁ i₁ a₁ t₁
  obtain ⟨-, -, s', hs', hsp', hs0', hsS'⟩ := path_of_codes hp₂ c₂ m₂ i₂ a₂ t₂
  exfalso
  rcases hx with h | h
  · exact h s hs ((ENNReal.coe_le_coe.2 hsp).trans_lt hp₁) hs0 hsS
  · exact h s' hs' ((ENNReal.coe_le_coe.2 hsp').trans_lt hp₂) hs0' hsS'

end Strip

/-- A family of almost-sure "a visit of a strip implies `P`" with `¬ P` gives almost surely no visit of the strips. -/
theorem ae_noVisit_of_strips {S' : Type*} [MeasurableSpace S'] {Q₀ : Measure S'} {Γ : S' → ℝ≥0 → ℂ}
    {U : S' → ℝ≥0∞} {S : List (ℚ × ℚ)} {P : Prop} (hP : ¬ P)
    (h : ∀ ab ∈ S, ∀ᵐ x ∂Q₀, (∃ t : ℝ≥0, (t : ℝ≥0∞) < U x ∧ ∃ y ∈ Ioo (ab.1 : ℝ) ab.2, Γ x t = y) → P) :
    ∀ᵐ x ∂Q₀, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < U x → (Γ x t).im = 0 → (Γ x t).re ∉ StripSet S := by
  have h' : ∀ᵐ x ∂Q₀, ∀ ab : ℚ × ℚ, ab ∈ S →
      (∃ t : ℝ≥0, (t : ℝ≥0∞) < U x ∧ ∃ y ∈ Ioo (ab.1 : ℝ) ab.2, Γ x t = y) → P := by
    refine ae_all_iff.2 fun ab => ?_
    by_cases hab : ab ∈ S
    · filter_upwards [h ab hab] with x hx _ using hx
    · exact Eventually.of_forall fun x h => absurd h hab
  filter_upwards [h'] with x hx t _ htU him hre
  obtain ⟨ab, hab, h1, h2⟩ := hre
  exact hP (hx ab hab ⟨t, htU, (Γ x t).re, ⟨h1, h2⟩, Complex.ext (by simp) (by simp [him])⟩)

/-! ### The per-datum event almost surely -/

/-- **The real completion event at one datum holds almost surely** (Astra's Prop. 5.2 and its countable witness
construction, with the G8/G2a/reflected-G8 frames by region; see the module docstring). -/
theorem ae_realEventC (hG2a : G2aReferenceStatement.{u}) (hG3 : G3ChartComparisonStatement.{u})
    (hG8 : G8FrameStatement.{u}) (hJV : JumpVisitStatement.{u}) {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ : θ₁ < θ₂) {c : BoundaryWord × ℝ} (hc : c ∈ HasSeedGerms κ θ₁ θ₂) {S' : Type u} [MeasurableSpace S']
    (Q₀ : Measure S') [IsProbabilityMeasure Q₀] (H₀ : S' → LQGMetric.DistOn upperHalfPlaneOpens)
    (hH : IsGFFWithBoundaryData Q₀ H₀ c.1.fn c.1.jumps) (Γ₁ Γ₂ : S' → ℝ≥0 → ℂ) (U₁ U₂ : S' → ℝ≥0∞)
    (h₁ : IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ Q₀ H₀ Γ₁ U₁) (h₂ : IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∀ᵐ x ∂Q₀, RealEventC c.1 c.2 (encC (Γ₁ x)) (U₁ x) (encC (Γ₂ x)) (U₂ x) := by
  obtain ⟨q, q₁, q₂, hSg⟩ := hc
  obtain ⟨c, w⟩ := c
  simp only at hSg hH h₁ h₂ ⊢
  have hw : 0 < w := hSg.w_pos
  have hc₁ := Sec7.ae_continuousOn_of_isFlowLine h₁
  have hc₂ := Sec7.ae_continuousOn_of_isFlowLine h₂
  have hm₁ := Supp7.ae_im_nonneg_of_isFlowLine h₁
  have hm₂ := Supp7.ae_im_nonneg_of_isFlowLine h₂
  have hlam := Sec4.sleLambda_pos hκ
  -- the jump part
  have hjump : ∀ᵐ x ∂Q₀, JumpFreeC c w (encC (Γ₁ x)) (U₁ x) := by
    filter_upwards [hJV κ hκ hκ4 c.fn c.jumps c.isPiecewiseConstantBoundaryData w θ₁ Q₀ H₀ hH Γ₁ U₁ h₁, hc₁]
      with x hx cx i hi hiw pp hpp
    have cs : ContinuousOn (Γ₁ x) (Iic (dyad pp.1 pp.2)) :=
      cx.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hpp.le
    rw [avoidPtC_iff, avoidC_encC_iff cs isClosed_singleton (singleton_nonempty _)]
    intro t ht hts he
    exact hx t ht ((ENNReal.coe_le_coe.2 hts).trans_lt hpp) (c.2.1 i) (BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩) hiw he
  -- the strip part
  have key : ∀ S : List (ℚ × ℚ), StripCond c w S →
      ∃ k : ℕ, ∀ᵐ x ∂Q₀, StripEventC S w k (encC (Γ₁ x)) (U₁ x) (encC (Γ₂ x)) (U₂ x) := by
    intro S hSC
    rcases S with _ | ⟨ab₀, S₀⟩
    · refine exists_ae_of_noVisit hc₁ hc₂ hm₁ hm₂ (Eventually.of_forall fun x => Or.inl ?_)
      rintro t - - - ⟨ab, hab, -⟩
      exact absurd hab List.not_mem_nil
    set S := ab₀ :: S₀ with hSdef
    set C := c.fn ab₀.1 with hCdef
    have hC : ∀ ab ∈ S, c.fn ab.1 = C := fun ab hab => hSC.2.2 ab hab ab₀ List.mem_cons_self
    have hcC : ∀ ab ∈ S, ∀ y ∈ Ioo (ab.1 : ℝ) ab.2, y ∉ c.jumps → c.fn y = C := fun ab hab y hy _ =>
      ((hSC.fn_eq hab ⟨hy.1.le, hy.2.le⟩).2).trans (hC ab hab)
    rcases hSC.1 with hL | hM | hR
    · -- left of the second seed: the reflected G8 frame, or no visit by the higher-angle flow
      obtain ⟨b₀, hb₀, hb⟩ := exists_between_list_snd hL
      obtain ⟨a₁, ha₁⟩ := exists_lt_list_fst S
      have hab : ∀ ab ∈ S, min a₁ b₀ - 1 < ab.1 ∧ (ab.2 : ℝ) < b₀ := fun ab h =>
        ⟨by linarith [min_le_left a₁ b₀, ha₁ ab h], hb ab h⟩
      by_cases hwt : -2 < Sec4.cumWeightLeft κ (C + θ₂ * QuantumZipper.chiC κ) ∧
          Sec4.cumWeightLeft κ (C + θ₂ * QuantumZipper.chiC κ) < κ / 2 - 2
      · exact exists_ae_of_ref hc₁ hc₂ hm₁ hm₂ hSC hab hC
          (ae_isChartCompletable_of_frame_left hG8 hG3 hκ hκ4 hθ hSg (by linarith [min_le_right a₁ b₀]) hb₀
            hwt.1 hwt.2 Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂)
      · refine exists_ae_of_noVisit hc₁ hc₂ hm₁ hm₂ ?_
        filter_upwards [ae_noVisit_of_strips hwt fun ab hab =>
          ae_frameWeight_of_visit_left hκ hκ4 c.isPiecewiseConstantBoundaryData (hL ab hab).le (hcC ab hab)
            Q₀ H₀ hH Γ₂ U₂ h₂] with x hx using Or.inr hx
    · -- between the seeds: the G2a word, or no visit (Lemma 5.1)
      obtain ⟨a₂, ha₂, ha⟩ := exists_between_list_fst (w := 0) fun ab h => (hM ab h).1
      obtain ⟨b₁, hb₁, hb⟩ := exists_between_list_snd (w := w) fun ab h => (hM ab h).2
      set a₀ := min a₂ (w / 2) with ha₀def
      have ha₀ : 0 < a₀ := lt_min ha₂ (half_pos hw)
      have ha₀w : a₀ < w := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hw)
      have hab : ∀ ab ∈ S, a₀ < ab.1 ∧ (ab.2 : ℝ) < max b₁ a₀ := fun ab h =>
        ⟨lt_of_le_of_lt (min_le_left _ _) (ha ab h), lt_of_lt_of_le (hb ab h) (le_max_left _ _)⟩
      by_cases hadm : -sleLambda κ - θ₂ * QuantumZipper.chiC κ < C ∧ C < sleLambda κ - θ₁ * QuantumZipper.chiC κ
      · exact exists_ae_of_ref hc₁ hc₂ hm₁ hm₂ hSC hab hC
          (ae_isChartCompletable_of_mid hG2a hG3 hκ hκ4 hθ hSg ha₀ (le_max_right _ _) (max_lt hb₁ ha₀w) hadm
            Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂)
      · refine exists_ae_of_noVisit hc₁ hc₂ hm₁ hm₂ ?_
        filter_upwards [ae_noVisit_of_strips hadm fun ab hab => by
          filter_upwards [ae_admissible_of_visit' hκ hκ4 hθ c.isPiecewiseConstantBoundaryData (hM ab hab).1.le
            (hM ab hab).2.le (hcC ab hab) Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂] with x hx hv using hx (Or.inl hv)]
          with x hx using Or.inl hx
    · -- right of the first seed: the G8 frame, or no visit by the lower-angle flow
      obtain ⟨a₀, ha₀, ha⟩ := exists_between_list_fst hR
      obtain ⟨b₁, hb⟩ := exists_gt_list_snd S
      have hab : ∀ ab ∈ S, a₀ < ab.1 ∧ (ab.2 : ℝ) < max b₁ a₀ := fun ab h =>
        ⟨ha ab h, lt_of_lt_of_le (hb ab h) (le_max_left _ _)⟩
      by_cases hwt : -2 < Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) ∧
          Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) < κ / 2 - 2
      · exact exists_ae_of_ref hc₁ hc₂ hm₁ hm₂ hSC hab hC
          (ae_isChartCompletable_of_frame hG8 hG3 hκ hκ4 hθ hSg ha₀ (le_max_right _ _) hwt.1 hwt.2
            Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂)
      · refine exists_ae_of_noVisit hc₁ hc₂ hm₁ hm₂ ?_
        filter_upwards [ae_noVisit_of_strips hwt fun ab hab =>
          ae_frameWeight_of_visit_right hκ hκ4 c.isPiecewiseConstantBoundaryData (hR ab hab).le (hcC ab hab)
            Q₀ H₀ hH Γ₁ U₁ h₁] with x hx using Or.inl hx
  have hstrips : ∀ᵐ x ∂Q₀, ∀ S : List (ℚ × ℚ), StripCond c w S →
      ∃ k : ℕ, StripEventC S w k (encC (Γ₁ x)) (U₁ x) (encC (Γ₂ x)) (U₂ x) := by
    refine ae_all_iff.2 fun S => ?_
    by_cases hSC : StripCond c w S
    · obtain ⟨k, hk⟩ := key S hSC
      filter_upwards [hk] with x hx _ using ⟨k, hx⟩
    · exact Eventually.of_forall fun x h => absurd h hSC
  filter_upwards [hjump, hstrips] with x h1 h2
  exact realEventC_iff.2 ⟨h1, h2⟩

end RLC

end InteractingSLE
