/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibDataGood

/-!
# The glued-space fibre objects, VI: the path facts are a measurable set of codes

Packet PROVE-AUX61-FIBDATA. `Aux61Fib.hasDyActFibreCover_of_fib` needs a **measurable** set `G i` of (history, code)
pairs on which `PathGood` holds. For fibre data whose clearance is that of the window (`d.ℓ = clr d.V`, `d.V` open with
nonempty complement), `PathGood d s` only reads the decoded continuous path and its lifetime, through countably many
conditions:

* `forall_mem_open_iff`: a continuous path stays in an open set on `(0, L)` iff on every rational `[a, b] ⊆ (0, L)` it
  keeps a positive rational distance from the complement;
* `injOn_iff`: a continuous path is injective on `[0, L]` iff for every horizon `N` and separation `1/(m+1)` some
  `1/(n+1)` separates its values at separated times of the countable set `{rationals ≤ min(L, N)} ∪ {min(L, N)}`;
* **`measurableSet_pathGood`**: `{s | PathGood d s}` is measurable.

Generic in the data; nothing here uses Theorem 1.2/1.3 (R48).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61FibData

open Aux61Fib

/-! ### Rational approximation in `ℝ≥0` -/

/-- Every point of `(a, b)` is approached by rational points of `(a, b)`. -/
theorem exists_rat_near {a b t : ℝ} (hat : a < t) (htb : t < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, a < q ∧ (q : ℝ) < b ∧ |(q : ℝ) - t| < ε := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show max a (t - ε) < min b (t + ε) from
    max_lt_iff.2 ⟨lt_min (hat.trans htb) (by linarith), lt_min (by linarith) (by linarith)⟩)
  refine ⟨q, (le_max_left _ _).trans_lt h1, h2.trans_le (min_le_left _ _), abs_lt.2 ⟨?_, ?_⟩⟩
  · linarith [(le_max_right a (t - ε)).trans_lt h1]
  · linarith [h2.trans_le (min_le_right b (t + ε))]

/-! ### Staying in an open set -/

/-- **A continuous path stays in an open set on `(0, L)`** iff on every rational `[a, b] ⊆ (0, L)` it keeps a positive
rational distance from the complement. -/
theorem forall_mem_open_iff {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {O : Set ℂ} (hO : IsOpen O) (hne : Oᶜ.Nonempty)
    (L : ℝ≥0∞) :
    (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < L → γ t ∈ O) ↔
      ∀ a b : ℚ, 0 < a → a ≤ b → (((b : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < L → ∃ n : ℕ, ∀ q : ℚ, a ≤ q → q ≤ b →
        1 / ((n : ℝ) + 1) ≤ infDist (γ (q : ℝ).toNNReal) Oᶜ := by
  have hpos : ∀ z ∈ O, 0 < infDist z Oᶜ := fun z hz =>
    (hO.isClosed_compl.notMem_iff_infDist_pos hne).1 (by simpa using hz)
  constructor
  · intro h a b ha hab hbL
    set K : Set ℝ≥0 := Icc (a : ℝ).toNNReal (b : ℝ).toNNReal with hK
    have hKc : IsCompact K := isCompact_Icc
    have hKne : K.Nonempty := nonempty_Icc.2 (Real.toNNReal_le_toNNReal (by exact_mod_cast hab))
    have hf : ContinuousOn (fun t => infDist (γ t) Oᶜ) K :=
      ((continuous_infDist_pt _).comp hγ).continuousOn
    obtain ⟨t₀, ht₀, hmin⟩ := hKc.exists_isMinOn hKne hf
    have ht₀pos : 0 < t₀ := lt_of_lt_of_le (Real.toNNReal_pos.2 (by exact_mod_cast ha)) ht₀.1
    have ht₀L : (t₀ : ℝ≥0∞) < L := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₀.2) hbL
    have hδ := hpos _ (h t₀ ht₀pos ht₀L)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine ⟨n, fun q haq hqb => ?_⟩
    have hq0 : (0 : ℝ) ≤ q :=
      (show (0 : ℝ) ≤ (a : ℝ) by exact_mod_cast ha.le).trans (show (a : ℝ) ≤ q by exact_mod_cast haq)
    have hqK : (q : ℝ).toNNReal ∈ K :=
      ⟨Real.toNNReal_le_toNNReal (by exact_mod_cast haq), Real.toNNReal_le_toNNReal (by exact_mod_cast hqb)⟩
    exact hn.le.trans (hmin hqK)
  · intro h t ht0 htL
    -- rationals `a < t < b < L`
    obtain ⟨a, ha0, hat⟩ := exists_rat_btwn (show (0 : ℝ) < t from ht0)
    obtain ⟨b, htb, hbL⟩ : ∃ b : ℚ, (t : ℝ) < b ∧ (((b : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < L := by
      by_cases hL : L = ⊤
      · obtain ⟨b, hb⟩ := exists_rat_gt (t : ℝ)
        exact ⟨b, hb, by rw [hL]; exact ENNReal.coe_lt_top⟩
      · have htL' : (t : ℝ) < L.toReal := by
          have := ENNReal.toReal_strict_mono hL htL
          simpa using this
        obtain ⟨b, h1, h2⟩ := exists_rat_btwn htL'
        refine ⟨b, h1, ?_⟩
        show ENNReal.ofReal b < L
        exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [t.2]) hL).2 h2
    obtain ⟨n, hn⟩ := h a b (by exact_mod_cast ha0) (by exact_mod_cast (hat.trans htb).le) hbL
    -- the bound passes to `t` by continuity
    have hge : 1 / ((n : ℝ) + 1) ≤ infDist (γ t) Oᶜ := by
      by_contra hlt
      push Not at hlt
      have hc : ContinuousAt (fun t => infDist (γ t) Oᶜ) t := ((continuous_infDist_pt _).comp hγ).continuousAt
      obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hc _ (sub_pos.2 hlt)
      obtain ⟨q, haq, hqb, hqt⟩ := exists_rat_near hat htb hε
      have hq0 : (0 : ℝ) ≤ q := (show (0 : ℝ) ≤ a by exact_mod_cast ha0.le).trans haq.le
      have hd : dist (q : ℝ).toNNReal t < ε := by
        rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0]; exact hqt
      have h1 := hball hd
      have h2 := hn q (by exact_mod_cast haq.le) (by exact_mod_cast hqb.le)
      rw [Real.dist_eq, abs_lt] at h1
      linarith [h1.2]
    have hpos' : 0 < infDist (γ t) Oᶜ := lt_of_lt_of_le (by positivity) hge
    by_contra hnot
    exact absurd (infDist_zero_of_mem hnot) hpos'.ne'

/-! ### Injectivity -/

/-- The countable dense set `{min(q, M) | q ∈ ℚ} ∪ {M}` of `[0, M]`. -/
def dPt (M : ℝ≥0) : Option ℚ → ℝ≥0
  | none => M
  | some q => min (q : ℝ).toNNReal M

theorem dPt_le (M : ℝ≥0) (o : Option ℚ) : dPt M o ≤ M := by
  cases o with
  | none => exact le_rfl
  | some q => exact min_le_right _ _

theorem exists_dPt_near {M t : ℝ≥0} (ht : t ≤ M) {ε : ℝ} (hε : 0 < ε) : ∃ o, dist (dPt M o) t < ε := by
  rcases eq_or_lt_of_le ht with rfl | htM
  · exact ⟨none, by simp [dPt, hε]⟩
  · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (t : ℝ) < min (t + ε) M from
      lt_min (by linarith) (by exact_mod_cast htM))
    have hq0 : (0 : ℝ) ≤ q := t.2.trans h1.le
    have hqM : (q : ℝ).toNNReal ≤ M := by
      rw [Real.toNNReal_le_iff_le_coe]; exact (h2.trans_le (min_le_right _ _)).le
    refine ⟨some q, ?_⟩
    simp only [dPt, min_eq_left hqM, NNReal.dist_eq, Real.coe_toNNReal _ hq0]
    rw [abs_lt]
    constructor <;> linarith [h2.trans_le (min_le_left _ _)]

/-- **A continuous path is injective on `[0, M]`** iff for every separation `1/(m+1)` some `1/(n+1)` separates its
values at `1/(m+1)`-separated points of the countable set `dPt M`. -/
theorem injOn_Iic_iff {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (M : ℝ≥0) :
    InjOn γ (Iic M) ↔ ∀ m : ℕ, ∃ n : ℕ, ∀ o o' : Option ℚ, 1 / ((m : ℝ) + 1) ≤ dist (dPt M o) (dPt M o') →
      1 / ((n : ℝ) + 1) ≤ dist (γ (dPt M o)) (γ (dPt M o')) := by
  constructor
  · intro hi m
    set K : Set (ℝ≥0 × ℝ≥0) := (Icc 0 M ×ˢ Icc 0 M) ∩ {p | 1 / ((m : ℝ) + 1) ≤ dist p.1 p.2} with hK
    have hKc : IsCompact K := (IsCompact.prod isCompact_Icc isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨0, fun o o' hd => absurd (show (dPt M o, dPt M o') ∈ K from
        ⟨⟨⟨zero_le, dPt_le M o⟩, ⟨zero_le, dPt_le M o'⟩⟩, hd⟩) (by rw [hKe]; exact notMem_empty _)⟩
    have hf : ContinuousOn (fun p : ℝ≥0 × ℝ≥0 => dist (γ p.1) (γ p.2)) K :=
      ((hγ.comp continuous_fst).dist (hγ.comp continuous_snd)).continuousOn
    obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKne hf
    have hne : p₀.1 ≠ p₀.2 := fun h => by
      have : 1 / ((m : ℝ) + 1) ≤ dist p₀.1 p₀.2 := hp₀.2
      rw [h, dist_self] at this
      linarith [show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity]
    have hδ : 0 < dist (γ p₀.1) (γ p₀.2) :=
      dist_pos.2 fun h => hne (hi (mem_Iic.2 hp₀.1.1.2) (mem_Iic.2 hp₀.1.2.2) h)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    exact ⟨n, fun o o' hd => hn.le.trans
      (isMinOn_iff.1 hmin (dPt M o, dPt M o') ⟨⟨⟨zero_le, dPt_le M o⟩, ⟨zero_le, dPt_le M o'⟩⟩, hd⟩)⟩
  · intro h t ht t' ht' heq
    by_contra hne
    have hd : 0 < dist t t' := dist_pos.2 hne
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < dist t t' / 3 by positivity)
    obtain ⟨n, hn⟩ := h m
    have hη : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 3 := by positivity
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuous_iff.1 hγ t _ hη
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuous_iff.1 hγ t' _ hη
    set δ := min (min δ₁ δ₂) (dist t t' / 3) with hδ
    have hδpos : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (by positivity)
    obtain ⟨o, ho⟩ := exists_dPt_near (mem_Iic.1 ht) hδpos
    obtain ⟨o', ho'⟩ := exists_dPt_near (mem_Iic.1 ht') hδpos
    have hsep : 1 / ((m : ℝ) + 1) ≤ dist (dPt M o) (dPt M o') := by
      have h3 := dist_triangle4 t (dPt M o) (dPt M o') t'
      have e1 : dist t (dPt M o) = dist (dPt M o) t := dist_comm _ _
      have : δ ≤ dist t t' / 3 := min_le_right _ _
      linarith
    have hval := hn o o' hsep
    have ha := h₁ _ (ho.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    have hb := h₂ _ (ho'.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
    have h4 := dist_triangle4 (γ (dPt M o)) (γ t) (γ t') (γ (dPt M o'))
    rw [heq, dist_self, dist_comm (γ t')] at h4
    rw [heq] at ha
    linarith

/-- **Injectivity on `[0, L]`** (`L` possibly infinite) is injectivity on every `[0, min(L, N)]`. -/
theorem injOn_le_iff {γ : ℝ≥0 → ℂ} (L : ℝ≥0∞) :
    InjOn γ {t | (t : ℝ≥0∞) ≤ L} ↔ ∀ N : ℕ, InjOn γ (Iic (min L (N : ℝ≥0∞)).toNNReal) := by
  have hsub : ∀ N : ℕ, Iic (min L (N : ℝ≥0∞)).toNNReal ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} := fun N t ht => by
    have hfin : min L (N : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (min_le_right _ _)
    have := ENNReal.coe_le_coe.2 (mem_Iic.1 ht)
    rw [ENNReal.coe_toNNReal hfin] at this
    exact this.trans (min_le_left _ _)
  have hmem : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ L → ∃ N : ℕ, t ∈ Iic (min L (N : ℝ≥0∞)).toNNReal := fun t ht => by
    obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
    refine ⟨N, mem_Iic.2 ?_⟩
    have hfin : min L (N : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (min_le_right _ _)
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
    exact le_min ht (by exact_mod_cast (show t ≤ (N : ℝ≥0) by exact_mod_cast hN))
  constructor
  · exact fun h N => h.mono (hsub N)
  · intro h t ht t' ht' heq
    obtain ⟨N, hN⟩ := hmem t ht
    obtain ⟨N', hN'⟩ := hmem t' ht'
    have hmono : ∀ {A B : ℕ}, A ≤ B → Iic (min L (A : ℝ≥0∞)).toNNReal ⊆ Iic (min L (B : ℝ≥0∞)).toNNReal :=
      fun {A B} hAB => Iic_subset_Iic.2 (ENNReal.toNNReal_mono (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
        (min_le_right _ _)) (min_le_min_left _ (by exact_mod_cast hAB)))
    exact h (max N N') (hmono (le_max_left _ _) hN) (hmono (le_max_right _ _) hN') heq

/-! ### The path facts as a measurable set -/

/-- **The path facts form a measurable set of codes** for data whose clearance is that of the window. -/
theorem measurableSet_pathGood (d : FibData) (hℓ : d.ℓ = clr d.V) (hV : IsOpen d.V) (hne : d.Vᶜ.Nonempty) :
    MeasurableSet {s : FibCode | PathGood d s} := by
  classical
  have hjt : Measurable fun p : ℝ≥0 × FibCode => FibCode.trace p.2 p.1 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun t s => FibCode.trace s t)
      FibCode.continuous_trace FibCode.measurable_trace
  have hevt : ∀ {τ : FibCode → ℝ≥0}, Measurable τ → Measurable fun s => FibCode.trace s (τ s) :=
    fun hτ => hjt.comp (hτ.prodMk measurable_id)
  have hHo : IsOpen H := QuantumZipper.isOpen_H
  have hHne : Hᶜ.Nonempty := ⟨0, by simp [QuantumZipper.H]⟩
  have hd : ∀ {O : Set ℂ}, Measurable fun z : ℂ => infDist z O := fun {O} => (continuous_infDist_pt O).measurable
  -- the run condition in an open set
  have hrun : ∀ {O : Set ℂ}, IsOpen O → Oᶜ.Nonempty →
      MeasurableSet {s : FibCode | ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < s.life → FibCode.trace s t ∈ O} := by
    intro O hO hOne
    have e : {s : FibCode | ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < s.life → FibCode.trace s t ∈ O} =
        ⋂ a : ℚ, ⋂ b : ℚ, {s | 0 < a → a ≤ b → (((b : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < s.life →
          ∃ n : ℕ, ∀ q : ℚ, a ≤ q → q ≤ b → 1 / ((n : ℝ) + 1) ≤ infDist (FibCode.trace s (q : ℝ).toNNReal) Oᶜ} := by
      ext s
      simp only [mem_ofPred_eq, mem_iInter]
      exact forall_mem_open_iff (FibCode.continuous_trace s) hO hOne s.life
    rw [e]
    refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
    refine (MeasurableSet.const _).imp ((MeasurableSet.const _).imp
      ((measurableSet_lt measurable_const FibCode.measurable_life).imp ?_))
    have e2 : {s : FibCode | ∃ n : ℕ, ∀ q : ℚ, a ≤ q → q ≤ b →
        1 / ((n : ℝ) + 1) ≤ infDist (FibCode.trace s (q : ℝ).toNNReal) Oᶜ} =
        ⋃ n : ℕ, ⋂ q : ℚ, {s | a ≤ q → q ≤ b →
          1 / ((n : ℝ) + 1) ≤ infDist (FibCode.trace s (q : ℝ).toNNReal) Oᶜ} := by
      ext s; simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    rw [e2]
    refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q =>
      (MeasurableSet.const _).imp ((MeasurableSet.const _).imp ?_)
    exact measurableSet_le measurable_const (hd.comp (FibCode.measurable_trace _))
  -- the set of path facts
  have e : {s : FibCode | PathGood d s} = GoodTrace ∩
      ({s | 0 < s.life → FibCode.trace s 0 ∈ d.V} ∩
        {s | ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < s.life → FibCode.trace s t ∈ d.V}) ∩
      {s | s.life = ⊤ ∨ FibCode.trace s s.life.toNNReal ∉ d.V} ∩
      {s | ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < s.life → FibCode.trace s t ∈ H} ∩
      ⋂ N : ℕ, ⋂ m : ℕ, ⋃ n : ℕ, ⋂ o : Option ℚ, ⋂ o' : Option ℚ,
        {s | 1 / ((m : ℝ) + 1) ≤ dist (dPt (min s.life (N : ℝ≥0∞)).toNNReal o)
            (dPt (min s.life (N : ℝ≥0∞)).toNNReal o') →
          1 / ((n : ℝ) + 1) ≤ dist (FibCode.trace s (dPt (min s.life (N : ℝ≥0∞)).toNNReal o))
            (FibCode.trace s (dPt (min s.life (N : ℝ≥0∞)).toNNReal o'))} := by
    ext s
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
    have hinj : InjOn (FibCode.trace s) {t | (t : ℝ≥0∞) ≤ s.life} ↔ ∀ N : ℕ, ∀ m : ℕ, ∃ n : ℕ,
        ∀ o o' : Option ℚ, 1 / ((m : ℝ) + 1) ≤ dist (dPt (min s.life (N : ℝ≥0∞)).toNNReal o)
            (dPt (min s.life (N : ℝ≥0∞)).toNNReal o') →
          1 / ((n : ℝ) + 1) ≤ dist (FibCode.trace s (dPt (min s.life (N : ℝ≥0∞)).toNNReal o))
            (FibCode.trace s (dPt (min s.life (N : ℝ≥0∞)).toNNReal o')) := by
      rw [injOn_le_iff]
      exact forall_congr' fun N => injOn_Iic_iff (FibCode.continuous_trace s) _
    have hpos : ∀ z, 0 < d.ℓ z ↔ z ∈ d.V := fun z => by rw [hℓ]; exact clr_pos_iff hV hne
    constructor
    · rintro ⟨hg, hin, hout, -, hH, hi⟩
      refine ⟨⟨⟨⟨hg, fun h0 => (hpos _).1 (hin 0 h0), fun t _ ht => (hpos _).1 (hin t ht)⟩, ?_⟩, hH⟩,
        hinj.1 hi⟩
      by_cases hL : s.life = ⊤
      · exact Or.inl hL
      · refine Or.inr fun hmem => ?_
        have := hout _ (ENNReal.coe_toNNReal hL)
        rw [hℓ] at this
        exact absurd this (not_le.2 ((clr_pos_iff hV hne).2 hmem))
    · rintro ⟨⟨⟨⟨hg, h0, hin⟩, hout⟩, hH⟩, hi⟩
      have hin' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < s.life → FibCode.trace s t ∈ d.V := fun t ht => by
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with rfl | ht0
        · exact h0 (by simpa using ht)
        · exact hin t ht0 ht
      refine pathGood_of_clr d hℓ hV hne hg hin' (fun T hT => ?_) hH (hinj.2 hi)
      rcases hout with hL | hnot
      · exact absurd hT (by rw [hL]; exact ENNReal.coe_ne_top)
      · have hTe : T = s.life.toNNReal := by rw [← hT]; rfl
        rw [hTe]; exact hnot
  rw [e]
  have hlifeN : ∀ N : ℕ, Measurable fun s : FibCode => (min s.life (N : ℝ≥0∞)).toNNReal := fun N =>
    ENNReal.measurable_toNNReal.comp (FibCode.measurable_life.min measurable_const)
  have hdPt : ∀ (N : ℕ) (o : Option ℚ), Measurable fun s : FibCode => dPt (min s.life (N : ℝ≥0∞)).toNNReal o :=
    fun N o => by
      cases o with
      | none => exact hlifeN N
      | some q => exact measurable_const.min (hlifeN N)
  have hA : MeasurableSet {s : FibCode | 0 < s.life → FibCode.trace s 0 ∈ d.V} :=
    (measurableSet_lt measurable_const FibCode.measurable_life).imp
      (FibCode.measurable_trace 0 hV.measurableSet)
  have hB : MeasurableSet {s : FibCode | s.life = ⊤ ∨ FibCode.trace s s.life.toNNReal ∉ d.V} :=
    (measurableSet_eq_fun FibCode.measurable_life measurable_const).union
      (hevt (ENNReal.measurable_toNNReal.comp FibCode.measurable_life) hV.measurableSet.compl)
  have hI : MeasurableSet (⋂ N : ℕ, ⋂ m : ℕ, ⋃ n : ℕ, ⋂ o : Option ℚ, ⋂ o' : Option ℚ,
        {s : FibCode | 1 / ((m : ℝ) + 1) ≤ dist (dPt (min s.life (N : ℝ≥0∞)).toNNReal o)
            (dPt (min s.life (N : ℝ≥0∞)).toNNReal o') →
          1 / ((n : ℝ) + 1) ≤ dist (FibCode.trace s (dPt (min s.life (N : ℝ≥0∞)).toNNReal o))
            (FibCode.trace s (dPt (min s.life (N : ℝ≥0∞)).toNNReal o'))}) :=
    MeasurableSet.iInter fun N => MeasurableSet.iInter fun m => MeasurableSet.iUnion fun n =>
      MeasurableSet.iInter fun o => MeasurableSet.iInter fun o' =>
        (measurableSet_le measurable_const ((hdPt N o).dist (hdPt N o'))).imp
          (measurableSet_le measurable_const ((hevt (hdPt N o)).dist (hevt (hdPt N o'))))
  exact (((measurableSet_goodTrace.inter (hA.inter (hrun hV hne))).inter hB).inter (hrun hHo hHne)).inter hI

end InteractingSLE.Sec5.Aux61FibData
