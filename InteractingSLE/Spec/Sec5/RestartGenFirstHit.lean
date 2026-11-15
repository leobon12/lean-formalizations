/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop411QOrder

/-!
# The first-contact property of Lemma 4.7 as a Borel event of the two paths

Packet PROVE-RESTART-GEN. Lemma 4.7's first-contact property in the chart `Q` (`Prop411Q.IsFirstHitQ η β q`: the
counterflow `η′ = R ∘ β`, `R(z) = −1/z`, visits `η(q)` at a time `u > 0` and avoids `η((0, q])` before `u`) quantifies
over all real times. To transfer it between probability spaces (from the glued space of `Prop411Q.CfGlueAE`, where
Lemma 4.7 is proved, to a space carrying the field, a flow line and a counterflow of the same field), it is rewritten as
a countable condition on the values of the two paths at rational times (`FirstHitCode`), which is a measurable event
of any measurable family of paths (`measurableSet_firstHitCode`), and which is equivalent to the first-contact
property for continuous paths:

* `firstHitCode_of_isFirstHitQ`: if `β` is continuous and `η` is continuous and nonzero on `(0, q]`, the first-contact
  property gives the code;
* `isFirstHitQ_of_firstHitCode`: if moreover `β(0) = 0`, the code gives the first-contact property.

The code says: (A) some time `u ∈ (0, b]` has `η′(u) = η(q)`, and (B) whenever the counterflow on `[a, b]` meets
`η([ε, q])` (`0 < a`, `0 < ε`), some time `u ∈ (0, b]` already has `η′(u) = η(q)`. Each clause is countable by
compactness of the time intervals and continuity (`hitBy`, `meetsQ`). Deterministic; no probability.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H)

namespace InteractingSLE.Sec5.RestartGen

open WangWu (negInv negInv_negInv' continuousAt_negInv)
open Prop411Q (IsFirstHitQ)

/-! ### The countable code -/

/-- **Some counterflow time in `(0, b]` visits `η(q)`**, countable form: there is a rational `δ ∈ (0, b]` such that
at rational times of `[δ, b]` the counterflow comes arbitrarily close to `η(q)`. -/
def hitBy (q : ℚ) (γ β : ℝ → ℂ) (b : ℚ) : Prop :=
  ∃ δ : ℚ, 0 < δ ∧ δ ≤ b ∧ ∀ m : ℕ, ∃ u : ℚ, δ ≤ u ∧ u ≤ b ∧ ‖negInv (β u) - γ q‖ < 1 / ((m : ℝ) + 1)

/-- **The counterflow on `[a, b]` meets `η([ε, q])`**, countable form: rational times of `[a, b]` and `[ε, q]` at
which the two paths come arbitrarily close. -/
def meetsQ (q ε a b : ℚ) (γ β : ℝ → ℂ) : Prop :=
  ∀ m : ℕ, ∃ v s : ℚ, a ≤ v ∧ v ≤ b ∧ ε ≤ s ∧ s ≤ q ∧ ‖negInv (β v) - γ s‖ < 1 / ((m : ℝ) + 1)

/-- **The first-contact code at the flow time `q`**: (A) the counterflow visits `η(q)` at some positive time, and
(B) whenever it meets `η([ε, q])` during `[a, b]` (`0 < ε`, `0 < a ≤ b`), it has already visited `η(q)` by time `b`. -/
def FirstHitCode (q : ℚ) (γ β : ℝ → ℂ) : Prop :=
  (∃ b : ℚ, 0 < b ∧ hitBy q γ β b) ∧
    ∀ ε a b : ℚ, 0 < ε → ε ≤ q → 0 < a → a ≤ b → meetsQ q ε a b γ β → hitBy q γ β b

/-! ### Measurability -/

section Meas

variable {X : Type*} [MeasurableSpace X] {γ β : X → ℝ → ℂ}

theorem measurable_dist_lt (hγ : ∀ s, Measurable fun x => γ x s) (hβ : ∀ s, Measurable fun x => β x s)
    (u s : ℝ) (c : ℝ) : Measurable fun x => ‖negInv (β x u) - γ x s‖ < c :=
  measurableSet_setOfPred.1
    (measurableSet_lt (((hβ u).inv.neg.sub (hγ s)).norm) measurable_const)

theorem measurable_hitBy (hγ : ∀ s, Measurable fun x => γ x s) (hβ : ∀ s, Measurable fun x => β x s) (q b : ℚ) :
    Measurable fun x => hitBy q (γ x) (β x) b := by
  unfold hitBy
  refine Measurable.exists fun δ => Measurable.and measurable_const (Measurable.and measurable_const
    (Measurable.forall fun m => Measurable.exists fun u => Measurable.and measurable_const
      (Measurable.and measurable_const ?_)))
  exact measurable_dist_lt hγ hβ _ _ _

theorem measurable_meetsQ (hγ : ∀ s, Measurable fun x => γ x s) (hβ : ∀ s, Measurable fun x => β x s)
    (q ε a b : ℚ) : Measurable fun x => meetsQ q ε a b (γ x) (β x) := by
  unfold meetsQ
  refine Measurable.forall fun m => Measurable.exists fun v => Measurable.exists fun s =>
    Measurable.and measurable_const (Measurable.and measurable_const (Measurable.and measurable_const
      (Measurable.and measurable_const ?_)))
  exact measurable_dist_lt hγ hβ _ _ _

/-- **The first-contact code is a measurable event of any measurable family of paths.** -/
theorem measurableSet_firstHitCode (hγ : ∀ s, Measurable fun x => γ x s)
    (hβ : ∀ s, Measurable fun x => β x s) (q : ℚ) : MeasurableSet {x | FirstHitCode q (γ x) (β x)} := by
  refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · exact Measurable.exists fun b => Measurable.and measurable_const (measurable_hitBy hγ hβ q b)
  · exact Measurable.forall fun ε => Measurable.forall fun a => Measurable.forall fun b =>
      Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const
        (Measurable.imp measurable_const (Measurable.imp (measurable_meetsQ hγ hβ q ε a b)
          (measurable_hitBy hγ hβ q b)))))

end Meas

/-! ### From the code to real times (compactness) -/

section Real

variable {γ β : ℝ → ℂ}

/-- If `R(β(uₙ)) → c ≠ 0` along times `uₙ → u` and `β` is continuous, then `R(β(u)) = c`. -/
theorem negInv_eq_of_tendsto (hβ : Continuous β) {c : ℂ} (hc : c ≠ 0) {u : ℝ} {x : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 u)) (hlim : Tendsto (fun n => negInv (β (x n))) atTop (𝓝 c)) :
    negInv (β u) = c := by
  have h1 : Tendsto (fun n => β (x n)) atTop (𝓝 (negInv c)) := by
    have := ((continuousAt_negInv hc).tendsto).comp hlim
    simpa only [Function.comp_def, negInv_negInv'] using this
  have h2 : Tendsto (fun n => β (x n)) atTop (𝓝 (β u)) := (hβ.tendsto u).comp hx
  rw [tendsto_nhds_unique h2 h1, negInv_negInv']

theorem one_div_succ_tendsto : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- **`hitBy` gives a real visit** in `[δ, b]` for some `δ > 0`. -/
theorem exists_eq_of_hitBy (hβ : Continuous β) {q b : ℚ} (hq : γ q ≠ 0) (h : hitBy q γ β b) :
    ∃ u : ℝ, 0 < u ∧ u ≤ b ∧ negInv (β u) = γ q := by
  obtain ⟨δ, hδ, hδb, hm⟩ := h
  choose x hx1 hx2 hx3 using hm
  have hmem : ∀ n, ((x n : ℚ) : ℝ) ∈ Icc (δ : ℝ) b := fun n => ⟨by exact_mod_cast hx1 n, by exact_mod_cast hx2 n⟩
  obtain ⟨u, hu, φ, hφ, hlim⟩ := (isCompact_Icc (a := (δ : ℝ)) (b := b)).tendsto_subseq hmem
  refine ⟨u, lt_of_lt_of_le (by exact_mod_cast hδ) hu.1, hu.2, negInv_eq_of_tendsto hβ hq hlim ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => (hx3 (φ n)).le) ?_
  exact one_div_succ_tendsto.comp hφ.tendsto_atTop

/-- **`meetsQ` gives a real meeting** `R(β(v)) = η(s)`, `v ∈ [a, b]`, `s ∈ [ε, q]`. -/
theorem exists_eq_of_meetsQ (hβ : Continuous β) {q ε a b : ℚ} (hε : 0 < ε) (hγc : ContinuousOn γ (Ioc 0 q))
    (hγ0 : ∀ s ∈ Ioc (0 : ℝ) q, γ s ≠ 0) (h : meetsQ q ε a b γ β) :
    ∃ v s : ℝ, (a : ℝ) ≤ v ∧ v ≤ b ∧ (ε : ℝ) ≤ s ∧ s ≤ q ∧ negInv (β v) = γ s := by
  choose v s hv1 hv2 hs1 hs2 hd using h
  have hmem : ∀ n, (((v n : ℚ) : ℝ), ((s n : ℚ) : ℝ)) ∈ Icc (a : ℝ) b ×ˢ Icc (ε : ℝ) q := fun n =>
    ⟨⟨show (a : ℝ) ≤ (v n : ℝ) by exact_mod_cast hv1 n, show (v n : ℝ) ≤ b by exact_mod_cast hv2 n⟩,
      ⟨show (ε : ℝ) ≤ (s n : ℝ) by exact_mod_cast hs1 n, show (s n : ℝ) ≤ q by exact_mod_cast hs2 n⟩⟩
  obtain ⟨⟨v₀, s₀⟩, ⟨hv₀, hs₀⟩, φ, hφ, hlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hmem
  have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
  have hs₀' : s₀ ∈ Ioc (0 : ℝ) q := ⟨lt_of_lt_of_le hεpos hs₀.1, hs₀.2⟩
  have hvlim : Tendsto (fun n => ((v (φ n) : ℚ) : ℝ)) atTop (𝓝 v₀) := (continuous_fst.tendsto _).comp hlim
  have hslim : Tendsto (fun n => ((s (φ n) : ℚ) : ℝ)) atTop (𝓝 s₀) := (continuous_snd.tendsto _).comp hlim
  have hγlim : Tendsto (fun n => γ (s (φ n))) atTop (𝓝 (γ s₀)) := by
    have hw : Tendsto (fun n => ((s (φ n) : ℚ) : ℝ)) atTop (𝓝[Ioc 0 q] s₀) :=
      tendsto_nhdsWithin_iff.2 ⟨hslim, Eventually.of_forall fun n =>
        ⟨lt_of_lt_of_le hεpos (by exact_mod_cast hs1 (φ n)), by exact_mod_cast hs2 (φ n)⟩⟩
    exact (hγc s₀ hs₀').tendsto.comp hw
  have hdiff : Tendsto (fun n => negInv (β (v (φ n))) - γ (s (φ n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hd (φ n)).le) (one_div_succ_tendsto.comp hφ.tendsto_atTop)
  have hcomb : Tendsto (fun n => negInv (β (v (φ n)))) atTop (𝓝 (γ s₀)) := by
    have := hdiff.add hγlim
    simpa only [sub_add_cancel, zero_add] using this
  exact ⟨v₀, s₀, hv₀.1, hv₀.2, hs₀.1, hs₀.2, negInv_eq_of_tendsto hβ (hγ0 s₀ hs₀') hvlim hcomb⟩

end Real

/-! ### From real times to the code (approximation by rationals) -/

section Approx

variable {γ β : ℝ → ℂ}

/-- `R ∘ β` is continuous at a time where `β ≠ 0`. -/
theorem continuousAt_negInv_comp (hβ : Continuous β) {u : ℝ} (hu : β u ≠ 0) :
    ContinuousAt (fun t => negInv (β t)) u :=
  (continuousAt_negInv hu).comp hβ.continuousAt

theorem ne_zero_of_negInv_eq {z w : ℂ} (hw : w ≠ 0) (h : negInv z = w) : z ≠ 0 := by
  rintro rfl
  simp [negInv] at h
  exact hw h.symm

/-- **A real visit gives `hitBy`.** -/
theorem hitBy_of_eq (hβ : Continuous β) {q b : ℚ} {u : ℝ} (hu0 : 0 < u) (hub : u ≤ b) (hq : γ q ≠ 0)
    (he : negInv (β u) = γ q) : hitBy q γ β b := by
  obtain ⟨δ, hδ0, hδu⟩ := exists_rat_btwn hu0
  have hδ0' : (0 : ℚ) < δ := by exact_mod_cast hδ0
  have hc := continuousAt_negInv_comp hβ (ne_zero_of_negInv_eq hq he)
  refine ⟨δ, hδ0', by exact_mod_cast hδu.le.trans hub, fun m => ?_⟩
  have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 hc _ hm
  obtain ⟨u', hu'1, hu'2⟩ := exists_rat_btwn (max_lt hδu (show u - η < u by linarith))
  refine ⟨u', ?_, ?_, ?_⟩
  · exact_mod_cast (le_max_left _ _).trans hu'1.le
  · exact_mod_cast hu'2.le.trans hub
  · have hd : dist (u' : ℝ) u < η := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [le_max_right (δ : ℝ) (u - η), hu'1, hu'2]
    have := hball hd
    rwa [dist_eq_norm, he] at this

/-- **A real meeting in the interior of `[a, b] × (ε, q]` gives `meetsQ`.** -/
theorem meetsQ_of_eq (hβ : Continuous β) {q ε a b : ℚ} (hγc : ContinuousOn γ (Ioc 0 q)) {v s : ℝ}
    (hav : (a : ℝ) < v) (hvb : v < b) (hεs : (ε : ℝ) < s) (hsq : s ≤ q) (hε : 0 < ε) (hs0 : γ s ≠ 0)
    (he : negInv (β v) = γ s) : meetsQ q ε a b γ β := by
  intro m
  have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) / 2 := by positivity
  have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
  have hs : s ∈ Ioc (0 : ℝ) q := ⟨lt_trans hεpos hεs, hsq⟩
  obtain ⟨η₁, hη₁, hb₁⟩ := Metric.continuousAt_iff.1 (continuousAt_negInv_comp hβ (ne_zero_of_negInv_eq hs0 he)) _ hm
  obtain ⟨η₂, hη₂, hb₂⟩ := Metric.continuousWithinAt_iff.1 (hγc s hs) _ hm
  obtain ⟨v', hv'1, hv'2⟩ := exists_rat_btwn (max_lt hav (show v - η₁ < v by linarith))
  obtain ⟨s', hs'1, hs'2⟩ := exists_rat_btwn (max_lt hεs (show s - η₂ < s by linarith))
  have hv'a : (a : ℝ) ≤ v' := (le_max_left _ _).trans hv'1.le
  have hs'ε : (ε : ℝ) ≤ s' := (le_max_left _ _).trans hs'1.le
  refine ⟨v', s', by exact_mod_cast hv'a, by exact_mod_cast hv'2.le.trans hvb.le, by exact_mod_cast hs'ε,
    by exact_mod_cast hs'2.le.trans hsq, ?_⟩
  have hd1 : dist (v' : ℝ) v < η₁ := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [le_max_right (a : ℝ) (v - η₁)]
  have hd2 : dist (s' : ℝ) s < η₂ := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [le_max_right (ε : ℝ) (s - η₂)]
  have h1 := hb₁ hd1
  have h2 := hb₂ ⟨lt_of_lt_of_le hεpos hs'ε, hs'2.le.trans hsq⟩ hd2
  rw [dist_eq_norm, he] at h1
  rw [dist_eq_norm] at h2
  calc ‖negInv (β v') - γ s'‖ = ‖(negInv (β v') - γ s) - (γ s' - γ s)‖ := by ring_nf
    _ ≤ ‖negInv (β v') - γ s‖ + ‖γ s' - γ s‖ := norm_sub_le _ _
    _ < 1 / ((m : ℝ) + 1) / 2 + 1 / ((m : ℝ) + 1) / 2 := add_lt_add h1 h2
    _ = 1 / ((m : ℝ) + 1) := by ring

end Approx

/-! ### The equivalence -/

section Equiv

variable {γ β : ℝ → ℂ}

/-- **The first-contact property gives the code** (`β` continuous, `η` continuous and nonzero on `(0, q]`). -/
theorem firstHitCode_of_isFirstHitQ (hβ : Continuous β) {q : ℚ} (hq : 0 < q) (hγc : ContinuousOn γ (Ioc 0 q))
    (hγ0 : ∀ s ∈ Ioc (0 : ℝ) q, γ s ≠ 0) (h : IsFirstHitQ γ β q) : FirstHitCode q γ β := by
  obtain ⟨u, hu0, hu, hbefore⟩ := h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hγq : γ q ≠ 0 := hγ0 q ⟨hqpos, le_rfl⟩
  refine ⟨?_, fun ε a b hε hεq ha hab hmeet => ?_⟩
  · obtain ⟨b, hb⟩ := exists_rat_gt u
    exact ⟨b, by exact_mod_cast hu0.trans hb, hitBy_of_eq hβ hu0 hb.le hγq hu⟩
  · obtain ⟨v, s, hav, hvb, hεs, hsq, he⟩ := exists_eq_of_meetsQ hβ hε hγc hγ0 hmeet
    have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
    have hapos : (0 : ℝ) < a := by exact_mod_cast ha
    have huv : u ≤ v := by
      by_contra hlt
      rw [not_le] at hlt
      exact hbefore v ⟨lt_of_lt_of_le hapos hav, hlt⟩ ⟨s, ⟨lt_of_lt_of_le hεpos hεs, hsq⟩, he.symm⟩
    exact hitBy_of_eq hβ hu0 (huv.trans hvb) hγq hu

/-- **The code gives the first-contact property** (`β` continuous with `β(0) = 0`, `η` continuous and nonzero on
`(0, q]`). The first visit of `η(q)` exists (closed set of visits, bounded away from `0` because `R(β(t)) → ∞` as
`t → 0`), and clause (B) excludes an earlier contact with `η((0, q])`. -/
theorem isFirstHitQ_of_firstHitCode (hβ : Continuous β) (hβ0 : β 0 = 0) {q : ℚ} (hq : 0 < q)
    (hγc : ContinuousOn γ (Ioc 0 q)) (hγ0 : ∀ s ∈ Ioc (0 : ℝ) q, γ s ≠ 0) (h : FirstHitCode q γ β) :
    IsFirstHitQ γ β q := by
  obtain ⟨⟨b₀, -, hb₀⟩, hB⟩ := h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hγq : γ q ≠ 0 := hγ0 q ⟨hqpos, le_rfl⟩
  set c : ℂ := negInv (γ q) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    intro h0
    apply hγq
    rw [← negInv_negInv' (γ q), h0]
    simp [negInv]
  have hvis : ∀ u, negInv (β u) = γ q ↔ β u = c := fun u => by
    constructor
    · intro e; rw [hc, ← e, negInv_negInv']
    · intro e; rw [e, hc, negInv_negInv']
  -- the visits are bounded away from `0`
  obtain ⟨δ₀, hδ₀, hsmall⟩ := Metric.continuousAt_iff.1 hβ.continuousAt (‖c‖) (norm_pos_iff.2 hc0)
  have hlow : ∀ u, β u = c → δ₀ ≤ |u| := by
    intro u hu
    by_contra hlt
    rw [not_le] at hlt
    have := hsmall (show dist u 0 < δ₀ by rwa [Real.dist_eq, sub_zero])
    rw [dist_eq_norm, hβ0, sub_zero, hu] at this
    exact lt_irrefl _ this
  set S : Set ℝ := β ⁻¹' {c} ∩ Ici δ₀ with hSdef
  have hScl : IsClosed S := (isClosed_singleton.preimage hβ).inter isClosed_Ici
  obtain ⟨u₁, hu₁0, -, hu₁⟩ := exists_eq_of_hitBy hβ hγq hb₀
  have hu₁S : u₁ ∈ S := ⟨(hvis u₁).1 hu₁, by
    have := hlow u₁ ((hvis u₁).1 hu₁); rwa [abs_of_pos hu₁0] at this⟩
  have hSne : S.Nonempty := ⟨u₁, hu₁S⟩
  have hSbdd : BddBelow S := ⟨δ₀, fun u hu => hu.2⟩
  set u := sInf S with hudef
  have huS : u ∈ S := hScl.csInf_mem hSne hSbdd
  have hu0 : 0 < u := lt_of_lt_of_le hδ₀ huS.2
  refine ⟨u, hu0, (hvis u).2 huS.1, fun v hv hmem => ?_⟩
  obtain ⟨s, hs, hse⟩ := hmem
  -- a rational window around the earlier contact
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hv.1
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hv.2
  obtain ⟨ε, hε1, hε2⟩ := exists_rat_btwn hs.1
  have ha : (0 : ℚ) < a := by exact_mod_cast ha1
  have hε : (0 : ℚ) < ε := by exact_mod_cast hε1
  have hγs : γ s ≠ 0 := hγ0 s hs
  have hmeet : meetsQ q ε a b γ β := meetsQ_of_eq hβ hγc ha2 hb1 hε2 hs.2 hε hγs hse.symm
  have hεq : ε ≤ q := by exact_mod_cast hε2.le.trans hs.2
  have hab : a ≤ b := by exact_mod_cast (ha2.trans hb1).le
  obtain ⟨w, hw0, hwb, hw⟩ := exists_eq_of_hitBy hβ hγq (hB ε a b hε hεq ha hab hmeet)
  have hwS : w ∈ S := ⟨(hvis w).1 hw, by
    have := hlow w ((hvis w).1 hw); rwa [abs_of_pos hw0] at this⟩
  have : u ≤ w := csInf_le hSbdd hwS
  linarith

/-- **The first-contact property and the code agree for continuous paths.** -/
theorem isFirstHitQ_iff_firstHitCode (hβ : Continuous β) (hβ0 : β 0 = 0) {q : ℚ} (hq : 0 < q)
    (hγc : ContinuousOn γ (Ioc 0 q)) (hγ0 : ∀ s ∈ Ioc (0 : ℝ) q, γ s ≠ 0) :
    IsFirstHitQ γ β q ↔ FirstHitCode q γ β :=
  ⟨firstHitCode_of_isFirstHitQ hβ hq hγc hγ0, isFirstHitQ_of_firstHitCode hβ hβ0 hq hγc hγ0⟩

end Equiv

end InteractingSLE.Sec5.RestartGen
