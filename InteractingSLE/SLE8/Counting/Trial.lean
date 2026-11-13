import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Order.Compact

/-!
# Trial intervals and occupation (SLE₈ note, proof of Proposition 4.1, (4.17)–(4.22))

SLE₈ note `source/sle8-continuity.pdf`, §4, pp. 9–10 (transcription `source/sle8/sle8-continuity.md`,
anchor `prop-4.1-proof`, Steps 3–4).

For a path `f : ℝ → ℝ` (in the proof: the height-parameter process `v ↦ J_{u₀ + v}` of (3.1), or a
Brownian motion of variance rate `4`), a level `c` (`= 2r`), a half-length `L` (`= r⁵`) and a search
horizon `K`, the note's successive entrance times (4.17)
`σ₁ = u₀`, `σ_{j+1} = inf {u ≥ σ_j + 2L : |J_u| ≤ 2r}` are, shifted to start at `0` and indexed from `0`,
`entrance f c L K j`. A first visit is searched only in `[b, K]`; if there is none the value is `K + 1`
(`firstVisit`). The occupation of `[-1, 1]` during `[b, b + ℓ]` is `occupation f b ℓ`.

Everything here is deterministic. The main results are:

* `firstVisit_spec`, `firstVisit_le_iff`: the first visit of a continuous path;
* `entrance_congr_of_le`, `trialEvent_congr`: locality (only the path up to the last trial interval
  matters), used for the completion condition of (4.22) and for stopping-time arguments;
* `measurable_entrance`, `measurable_occupation`, `measurableSet_trialEvent`: measurability for a
  random continuous path, with respect to any σ-algebra for which the coordinates are measurable;
* `exists_lt_entrance_of_visit`: every visit before `σ_m` lies in one of the first `m` trial windows
  (the core of (4.18)–(4.19)).
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace InteractingSLE.SLE8

/-! ## Definitions -/

/-- The first visit of `f` to `[-c, c]` during `[b, K]`, or `K + 1` if there is none. -/
def firstVisit (f : ℝ → ℝ) (c K b : ℝ) : ℝ :=
  open Classical in
  if ∃ u ∈ Icc b K, |f u| ≤ c then sInf {u | u ∈ Icc b K ∧ |f u| ≤ c} else K + 1

/-- The successive entrance times (4.17) of the SLE₈ note, shifted to start at `0` and indexed from
`0`: `entrance f c L K 0 = 0` and `entrance f c L K (j + 1)` is the first visit of `f` to `[-c, c]`
at or after `entrance f c L K j + 2L` (searched up to `K`; `K + 1` if there is none). -/
def entrance (f : ℝ → ℝ) (c L K : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => firstVisit f c K (entrance f c L K j + 2 * L)

/-- The occupation `∫_b^{b+ℓ} 1{|f(u)| ≤ 1} du` of `[-1, 1]` by `f` during `[b, b + ℓ]`. -/
def occupation (f : ℝ → ℝ) (b ℓ : ℝ) : ℝ≥0∞ :=
  volume {u | u ∈ Icc b (b + ℓ) ∧ |f u| ≤ 1}

/-- The trial event of (4.22): the first `m` trial intervals `[σ_j, σ_j + 2L]` (`j < m`) are found
and end by `K`, and each has occupation of `[-1, 1]` at most `r`. -/
def TrialEvent (f : ℝ → ℝ) (c L K r : ℝ) (m : ℕ) : Prop :=
  ∀ j < m, entrance f c L K j + 2 * L ≤ K ∧
    occupation f (entrance f c L K j) (2 * L) ≤ ENNReal.ofReal r

/-- The weaker event used in the Brownian estimate (4.23): the first `m` entrance times are found
(at most `K`) and each trial interval has occupation of `[-1, 1]` at most `r`. -/
def TrialFound (f : ℝ → ℝ) (c L K r : ℝ) (m : ℕ) : Prop :=
  ∀ j < m, entrance f c L K j ≤ K ∧ occupation f (entrance f c L K j) (2 * L) ≤ ENNReal.ofReal r

/-! ## The first visit -/

variable {f g : ℝ → ℝ} {c K b : ℝ}

theorem isClosed_visitSet (hf : Continuous f) (c b K : ℝ) :
    IsClosed {u | u ∈ Icc b K ∧ |f u| ≤ c} :=
  isClosed_Icc.inter (isClosed_le (continuous_abs.comp hf) continuous_const)

/-- The first visit of a continuous path, when there is a visit in `[b, K]`. -/
theorem firstVisit_spec (hf : Continuous f) (h : ∃ u ∈ Icc b K, |f u| ≤ c) :
    firstVisit f c K b ∈ Icc b K ∧ |f (firstVisit f c K b)| ≤ c ∧
      ∀ u ∈ Icc b K, |f u| ≤ c → firstVisit f c K b ≤ u := by
  have hne : {u | u ∈ Icc b K ∧ |f u| ≤ c}.Nonempty := by
    obtain ⟨u, hu, hfu⟩ := h; exact ⟨u, hu, hfu⟩
  have hbdd : BddBelow {u | u ∈ Icc b K ∧ |f u| ≤ c} := ⟨b, fun u hu => hu.1.1⟩
  have hmem := (isClosed_visitSet hf c b K).csInf_mem hne hbdd
  have heq : firstVisit f c K b = sInf {u | u ∈ Icc b K ∧ |f u| ≤ c} := by
    simp only [firstVisit, h, ↓reduceIte]
  rw [heq]
  exact ⟨hmem.1, hmem.2, fun u hu hfu => csInf_le hbdd ⟨hu, hfu⟩⟩

theorem firstVisit_of_not (h : ¬∃ u ∈ Icc b K, |f u| ≤ c) : firstVisit f c K b = K + 1 := by
  simp only [firstVisit, h, ↓reduceIte]

/-- The first visit lies in `[b, K] ∪ {K + 1}`. -/
theorem firstVisit_mem (hf : Continuous f) :
    firstVisit f c K b ∈ Icc b K ∨ firstVisit f c K b = K + 1 := by
  by_cases h : ∃ u ∈ Icc b K, |f u| ≤ c
  · exact Or.inl (firstVisit_spec hf h).1
  · exact Or.inr (firstVisit_of_not h)

/-- `firstVisit ≤ K` exactly when there is a visit in `[b, K]`. -/
theorem firstVisit_le_horizon_iff (hf : Continuous f) :
    firstVisit f c K b ≤ K ↔ ∃ u ∈ Icc b K, |f u| ≤ c := by
  constructor
  · intro hle
    by_contra h
    rw [firstVisit_of_not h] at hle
    linarith
  · intro h
    exact (firstVisit_spec hf h).1.2

/-- **The first-visit event.** For a continuous path, `firstVisit f c K b ≤ t` if and only if there is
a visit in `[b, min t K]`, or there is no visit in `[b, K]` and `K + 1 ≤ t`. -/
theorem firstVisit_le_iff (hf : Continuous f) (t : ℝ) :
    firstVisit f c K b ≤ t ↔
      (∃ u ∈ Icc b (min t K), |f u| ≤ c) ∨ ((¬∃ u ∈ Icc b K, |f u| ≤ c) ∧ K + 1 ≤ t) := by
  by_cases h : ∃ u ∈ Icc b K, |f u| ≤ c
  · obtain ⟨hmem, hval, hmin⟩ := firstVisit_spec hf h
    constructor
    · intro hle
      exact Or.inl ⟨firstVisit f c K b, ⟨hmem.1, le_min hle hmem.2⟩, hval⟩
    · rintro (⟨u, hu, hfu⟩ | ⟨hn, -⟩)
      · exact (hmin u ⟨hu.1, hu.2.trans (min_le_right _ _)⟩ hfu).trans
          (hu.2.trans (min_le_left _ _))
      · exact absurd h hn
  · rw [firstVisit_of_not h]
    constructor
    · intro hle; exact Or.inr ⟨h, hle⟩
    · rintro (⟨u, hu, hfu⟩ | ⟨-, hle⟩)
      · exact absurd ⟨u, ⟨hu.1, hu.2.trans (min_le_right _ _)⟩, hfu⟩ h
      · exact hle

/-- Locality of the first visit: if `f = g` on `[b, K']` and the first visit of `f` is at most `K'`,
then `g` has the same first visit, for any horizon `K₂ ≥ K'`. -/
theorem firstVisit_congr (hf : Continuous f) (hg : Continuous g) {K' K₂ : ℝ} (hK₂ : K' ≤ K₂)
    (hfg : ∀ u ∈ Icc b K', f u = g u) (hle : firstVisit f c K b ≤ K') (hK : K' ≤ K) :
    firstVisit g c K₂ b = firstVisit f c K b := by
  have hex : ∃ u ∈ Icc b K, |f u| ≤ c := (firstVisit_le_horizon_iff hf).1 (hle.trans hK)
  obtain ⟨hmem, hval, hmin⟩ := firstVisit_spec hf hex
  set u₀ := firstVisit f c K b
  have hu₀ : u₀ ∈ Icc b K' := ⟨hmem.1, hle⟩
  have hexg : ∃ u ∈ Icc b K₂, |g u| ≤ c :=
    ⟨u₀, ⟨hmem.1, hle.trans hK₂⟩, by rw [← hfg u₀ hu₀]; exact hval⟩
  obtain ⟨hmemg, hvalg, hming⟩ := firstVisit_spec hg hexg
  refine le_antisymm (hming u₀ ⟨hmem.1, hle.trans hK₂⟩ (by rw [← hfg u₀ hu₀]; exact hval)) ?_
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hgK' : firstVisit g c K₂ b ∈ Icc b K' := ⟨hmemg.1, hlt.le.trans hle⟩
  have := hmin (firstVisit g c K₂ b) ⟨hmemg.1, hgK'.2.trans hK⟩
    (by rw [hfg _ hgK']; exact hvalg)
  linarith

/-! ## Entrance times -/

variable {L : ℝ}

theorem entrance_zero (f : ℝ → ℝ) (c L K : ℝ) : entrance f c L K 0 = 0 := rfl

theorem entrance_succ (f : ℝ → ℝ) (c L K : ℝ) (j : ℕ) :
    entrance f c L K (j + 1) = firstVisit f c K (entrance f c L K j + 2 * L) := rfl

/-- A found entrance time is at least the previous one plus `2L`. -/
theorem entrance_succ_ge (hf : Continuous f) {j : ℕ} (hle : entrance f c L K (j + 1) ≤ K) :
    entrance f c L K j + 2 * L ≤ entrance f c L K (j + 1) := by
  rw [entrance_succ] at hle ⊢
  rcases firstVisit_mem hf (f := f) (c := c) (K := K) (b := entrance f c L K j + 2 * L) with h | h
  · exact h.1
  · rw [h] at hle; linarith

theorem entrance_nonneg (hf : Continuous f) (hL : 0 ≤ L) (hK : 0 ≤ K) (j : ℕ) :
    0 ≤ entrance f c L K j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [entrance_succ]
    rcases firstVisit_mem hf (f := f) (c := c) (K := K) (b := entrance f c L K j + 2 * L) with h | h
    · linarith [h.1]
    · rw [h]; linarith

theorem entrance_le_succ_horizon (hf : Continuous f) (hK : 0 ≤ K) (j : ℕ) :
    entrance f c L K j ≤ K + 1 := by
  cases j with
  | zero => rw [entrance_zero]; linarith
  | succ j =>
    rw [entrance_succ]
    rcases firstVisit_mem hf (f := f) (c := c) (K := K) (b := entrance f c L K j + 2 * L) with h | h
    · linarith [h.2]
    · rw [h]

/-- The entrance times are nondecreasing. -/
theorem entrance_le_succ (hf : Continuous f) (hL : 0 ≤ L) (hK : 0 ≤ K) (j : ℕ) :
    entrance f c L K j ≤ entrance f c L K (j + 1) := by
  by_cases h : entrance f c L K (j + 1) ≤ K
  · linarith [entrance_succ_ge hf h]
  · have h' := h
    rw [entrance_succ] at h' ⊢
    rcases firstVisit_mem hf (f := f) (c := c) (K := K) (b := entrance f c L K j + 2 * L) with h2 | h2
    · exact absurd h2.2 h'
    · rw [h2]; exact entrance_le_succ_horizon hf hK j

theorem entrance_mono (hf : Continuous f) (hL : 0 ≤ L) (hK : 0 ≤ K) :
    Monotone (entrance f c L K) :=
  monotone_nat_of_le_succ (entrance_le_succ hf hL hK)

/-- A found entrance time is a visit: `|f(σ_j)| ≤ c` for `j ≥ 1`. -/
theorem abs_entrance_le (hf : Continuous f) {j : ℕ} (hle : entrance f c L K (j + 1) ≤ K) :
    |f (entrance f c L K (j + 1))| ≤ c := by
  rw [entrance_succ] at hle ⊢
  exact (firstVisit_spec hf ((firstVisit_le_horizon_iff hf).1 hle)).2.1

/-- **Locality of the entrance times.** If `f = g` on `[0, K']`, `K' ≤ K`, `K' ≤ K₂`, and the `j`-th
entrance time of `f` (horizon `K`) is at most `K'`, then it is also the `j`-th entrance time of `g`
(horizon `K₂`). -/
theorem entrance_congr_of_le (hf : Continuous f) (hg : Continuous g) (hL : 0 ≤ L) {K' K₂ : ℝ}
    (hK'0 : 0 ≤ K') (hK : K' ≤ K) (hK₂ : K' ≤ K₂) (hfg : ∀ u ∈ Icc 0 K', f u = g u) :
    ∀ j, entrance f c L K j ≤ K' → entrance g c L K₂ j = entrance f c L K j := by
  have hK0 : 0 ≤ K := hK'0.trans hK
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hle
    have hprev : entrance f c L K j ≤ K' := by
      have := entrance_succ_ge hf (hle.trans hK) (c := c)
      linarith
    rw [entrance_succ, entrance_succ, ih hprev]
    have hb0 : 0 ≤ entrance f c L K j + 2 * L := by
      linarith [entrance_nonneg hf hL hK0 j (c := c)]
    exact firstVisit_congr hf hg hK₂ (fun u hu => hfg u ⟨hb0.trans hu.1, hu.2⟩) hle hK

/-- Occupation depends only on the path on the window. -/
theorem occupation_congr {b ℓ : ℝ} (hfg : ∀ u ∈ Icc b (b + ℓ), f u = g u) :
    occupation f b ℓ = occupation g b ℓ := by
  unfold occupation
  congr 1
  ext u
  constructor
  · rintro ⟨hu, h⟩; exact ⟨hu, by rw [← hfg u hu]; exact h⟩
  · rintro ⟨hu, h⟩; exact ⟨hu, by rw [hfg u hu]; exact h⟩

/-- An entrance time is found (at most `K`) or equals `K + 1`. -/
theorem entrance_le_or_eq (hf : Continuous f) (hK : 0 ≤ K) (j : ℕ) :
    entrance f c L K j ≤ K ∨ entrance f c L K j = K + 1 := by
  cases j with
  | zero => exact Or.inl (by rw [entrance_zero]; exact hK)
  | succ j =>
    rw [entrance_succ]
    rcases firstVisit_mem hf (f := f) (c := c) (K := K) (b := entrance f c L K j + 2 * L) with h | h
    · exact Or.inl h.2
    · exact Or.inr h

/-- **Locality of `TrialFound`.** If `f = g` on `[0, K']` with `K' ≤ K` and the `m`-th entrance time
of `f` is at most `K'`, the first `m` trials of `f` and `g` coincide. -/
theorem trialFound_congr (hf : Continuous f) (hg : Continuous g) (hL : 0 ≤ L) {K' r : ℝ} {m : ℕ}
    (hK'0 : 0 ≤ K') (hK : K' ≤ K) (hfg : ∀ u ∈ Icc 0 K', f u = g u)
    (hm : entrance f c L K m ≤ K') (h : TrialFound f c L K r m) :
    TrialFound g c L K r m ∧ entrance g c L K m = entrance f c L K m := by
  have hK0 : 0 ≤ K := hK'0.trans hK
  have hmono := entrance_mono hf hL hK0 (c := c)
  have he : ∀ j ≤ m, entrance g c L K j = entrance f c L K j := fun j hj =>
    entrance_congr_of_le hf hg hL hK'0 hK hK hfg j ((hmono hj).trans hm)
  refine ⟨fun j hj => ?_, he m le_rfl⟩
  obtain ⟨h1, h2⟩ := h j hj
  rw [he j hj.le]
  refine ⟨h1, ?_⟩
  have hjm : entrance f c L K (j + 1) ≤ K' := (hmono (Nat.succ_le_of_lt hj)).trans hm
  have hwin : entrance f c L K j + 2 * L ≤ K' := (entrance_succ_ge hf (hjm.trans hK)).trans hjm
  rw [← occupation_congr fun u hu =>
    hfg u ⟨(entrance_nonneg hf hL hK0 j).trans hu.1, hu.2.trans hwin⟩]
  exact h2

/-- **Locality, completion form.** If the first `m` trial intervals of `f` end by `K' ≤ K`, each with
occupation at most `r`, and `f = g` on `[0, K']`, then the first `m` trials of `g` are found with the
same occupations. -/
theorem trialFound_of_congr (hf : Continuous f) (hg : Continuous g) (hL : 0 ≤ L) {K' r : ℝ} {m : ℕ}
    (hK'0 : 0 ≤ K') (hK : K' ≤ K) (hfg : ∀ u ∈ Icc 0 K', f u = g u)
    (h : ∀ j < m, entrance f c L K j + 2 * L ≤ K' ∧
      occupation f (entrance f c L K j) (2 * L) ≤ ENNReal.ofReal r) :
    TrialFound g c L K r m := by
  have hK0 : 0 ≤ K := hK'0.trans hK
  intro j hj
  obtain ⟨h1, h2⟩ := h j hj
  have hle : entrance f c L K j ≤ K' := by linarith
  rw [entrance_congr_of_le hf hg hL hK'0 hK hK hfg j hle]
  refine ⟨hle.trans hK, ?_⟩
  rw [← occupation_congr fun u hu =>
    hfg u ⟨(entrance_nonneg hf hL hK0 j).trans hu.1, hu.2.trans h1⟩]
  exact h2

/-- `TrialEvent` implies `TrialFound` (for `L ≥ 0`). -/
theorem TrialEvent.trialFound {r : ℝ} {m : ℕ} (hL : 0 ≤ L) (h : TrialEvent f c L K r m) :
    TrialFound f c L K r m :=
  fun j hj => ⟨by linarith [(h j hj).1], (h j hj).2⟩

/-- **Locality of the trial event.** If `f = g` on `[0, K]`, the trial event of `f` with horizon `K`
gives the trial event of `g` with any horizon `K₂ ≥ K` (the completion condition of (4.22)). -/
theorem trialEvent_congr (hf : Continuous f) (hg : Continuous g) (hL : 0 ≤ L) {r K₂ : ℝ} {m : ℕ}
    (hK0 : 0 ≤ K) (hK₂ : K ≤ K₂) (hfg : ∀ u ∈ Icc 0 K, f u = g u) (h : TrialEvent f c L K r m) :
    TrialEvent g c L K₂ r m := by
  intro j hj
  obtain ⟨h1, h2⟩ := h j hj
  have hle : entrance f c L K j ≤ K := by linarith
  have he := entrance_congr_of_le hf hg hL hK0 le_rfl hK₂ hfg j hle
  rw [he]
  refine ⟨h1.trans hK₂, ?_⟩
  rw [← occupation_congr fun u hu => hfg u ⟨(entrance_nonneg hf hL hK0 j).trans hu.1, hu.2.trans h1⟩]
  exact h2

/-! ## Visits and trial windows -/

/-- **Every visit before `σ_m` lies in an earlier trial window** (proof of (4.19)): if `v ∈ [0, K]`
is a visit (`|f v| ≤ c`) and `v < σ_m`, then `σ_j ≤ v < σ_j + 2L` for some `j < m`. -/
theorem exists_lt_entrance_of_visit (hf : Continuous f) {v : ℝ} (hv0 : 0 ≤ v) (hvK : v ≤ K)
    (hfv : |f v| ≤ c) :
    ∀ m, v < entrance f c L K m → ∃ j < m, entrance f c L K j ≤ v ∧ v < entrance f c L K j + 2 * L := by
  intro m
  induction m with
  | zero => intro h; rw [entrance_zero] at h; linarith
  | succ m ih =>
    intro hlt
    by_cases hm : v < entrance f c L K m
    · obtain ⟨j, hj, h⟩ := ih hm
      exact ⟨j, by omega, h⟩
    · replace hm := not_lt.1 hm
      by_cases h2 : v < entrance f c L K m + 2 * L
      · exact ⟨m, by omega, hm, h2⟩
      · replace h2 := not_lt.1 h2
        have hex : ∃ u ∈ Icc (entrance f c L K m + 2 * L) K, |f u| ≤ c := ⟨v, ⟨h2, hvK⟩, hfv⟩
        have := (firstVisit_spec hf hex).2.2 v ⟨h2, hvK⟩ hfv
        rw [entrance_succ] at hlt
        linarith

/-- A finite set of naturals of diameter at most `R` has at most `R + 1` elements. -/
theorem card_le_of_diam_le {S : Finset ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ k ∈ S, ∀ k' ∈ S, (k : ℝ) - k' ≤ R) : (S.card : ℝ) ≤ R + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp; linarith
  set k₀ := S.min' hne
  have hsub : S ⊆ Finset.Icc k₀ (k₀ + ⌊R⌋₊) := by
    intro k hk
    have h0 : k₀ ≤ k := S.min'_le k hk
    have h1 : ((k - k₀ : ℕ) : ℝ) ≤ R := by
      rw [Nat.cast_sub h0]; exact h k hk k₀ (S.min'_mem hne)
    have h2 : k - k₀ ≤ ⌊R⌋₊ := Nat.le_floor h1
    exact Finset.mem_Icc.2 ⟨h0, by omega⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hc' : (S.card : ℝ) ≤ (⌊R⌋₊ : ℝ) + 1 := by
    have : S.card ≤ ⌊R⌋₊ + 1 := by omega
    exact_mod_cast this
  linarith [Nat.floor_le hR]

/-- **The scale count against trial windows** ((4.18)–(4.19)). Let `I` be a finite set of indices with
visit times `φ k ∈ [0, K₀]`, `K₀ ≤ K`, such that two indices whose visit times lie in a common window
`[b, b + 2L)` differ by at most `R`. If `σ_m > K₀`, then `|I| ≤ m (R + 1)`. -/
theorem card_le_of_entrance_gt (hf : Continuous f) {R K₀ : ℝ} (hR : 0 ≤ R) (hK₀ : K₀ ≤ K)
    {I : Finset ℕ} {φ : ℕ → ℝ} (hφ0 : ∀ k ∈ I, 0 ≤ φ k) (hφK : ∀ k ∈ I, φ k ≤ K₀)
    (hφv : ∀ k ∈ I, |f (φ k)| ≤ c)
    (hwin : ∀ k ∈ I, ∀ k' ∈ I, ∀ b, φ k ∈ Ico b (b + 2 * L) → φ k' ∈ Ico b (b + 2 * L) →
      (k : ℝ) - k' ≤ R)
    {m : ℕ} (hm : K₀ < entrance f c L K m) : (I.card : ℝ) ≤ m * (R + 1) := by
  classical
  set Ij : ℕ → Finset ℕ := fun j =>
    I.filter fun k => φ k ∈ Ico (entrance f c L K j) (entrance f c L K j + 2 * L)
  have hsub : I ⊆ (Finset.range m).biUnion Ij := by
    intro k hk
    obtain ⟨j, hj, h1, h2⟩ := exists_lt_entrance_of_visit hf (hφ0 k hk) ((hφK k hk).trans hK₀)
      (hφv k hk) m ((hφK k hk).trans_lt hm)
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, Finset.mem_filter.2 ⟨hk, h1, h2⟩⟩
  have hcard : I.card ≤ ∑ j ∈ Finset.range m, (Ij j).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hj : ∀ j ∈ Finset.range m, ((Ij j).card : ℝ) ≤ R + 1 := by
    intro j _
    refine card_le_of_diam_le hR fun k hk k' hk' => ?_
    obtain ⟨hkI, hkw⟩ := Finset.mem_filter.1 hk
    obtain ⟨hk'I, hk'w⟩ := Finset.mem_filter.1 hk'
    exact hwin k hkI k' hk'I _ hkw hk'w
  calc (I.card : ℝ) ≤ ∑ j ∈ Finset.range m, ((Ij j).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _j ∈ Finset.range m, (R + 1) := Finset.sum_le_sum hj
    _ = m * (R + 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Measurability for random continuous paths -/

section Measurability

variable {Ω : Type*} {m𝓖 : MeasurableSpace Ω} {F : Ω → ℝ → ℝ}

/-- A random continuous path with measurable coordinates is jointly measurable. -/
theorem measurable_uncurry_path (hc : ∀ ω, Continuous (F ω)) (hm : ∀ u, Measurable fun ω => F ω u) :
    Measurable fun p : Ω × ℝ => F p.1 p.2 :=
  (measurable_uncurry_of_continuous_of_measurable (u := fun u ω => F ω u) hc hm).comp measurable_swap

/-- Evaluation of a random continuous path at a random time. -/
theorem measurable_path_apply (hc : ∀ ω, Continuous (F ω)) (hm : ∀ u, Measurable fun ω => F ω u)
    {a : Ω → ℝ} (ha : Measurable a) : Measurable fun ω => F ω (a ω) :=
  (measurable_uncurry_path hc hm).comp (measurable_id.prodMk ha)

/-- A visit of a continuous path to `[-c, c]` during `[a, b]`, through countably many points. -/
theorem exists_visit_iff (hf : Continuous f) {a b c : ℝ} :
    (∃ u ∈ Icc a b, |f u| ≤ c) ↔
      a ≤ b ∧ ∀ n : ℕ, (|f a| < c + 1 / (n + 1) ∨
        ∃ q : ℚ, a < q ∧ (q : ℝ) < b ∧ |f q| < c + 1 / (n + 1)) := by
  have hfa : Continuous fun u => |f u| := continuous_abs.comp hf
  constructor
  · rintro ⟨u, hu, hfu⟩
    refine ⟨hu.1.trans hu.2, fun n => ?_⟩
    have hn : (0 : ℝ) < 1 / (n + 1) := by positivity
    rcases hu.1.eq_or_lt with rfl | hau
    · exact Or.inl (by linarith)
    · right
      have hev : ∀ᶠ v in 𝓝 u, |f v| < c + 1 / (n + 1) :=
        hfa.continuousAt.eventually (gt_mem_nhds (by linarith))
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hau (sub_lt_self u hε))
      refine ⟨q, (le_max_left _ _).trans_lt hq1, hq2.trans_le hu.2, hball ?_⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right a (u - ε)]
  · rintro ⟨hab, h⟩
    by_contra hno
    have hpos : ∀ u ∈ Icc a b, c < |f u| := fun u hu => not_le.1 fun h' => hno ⟨u, hu, h'⟩
    obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hfa.continuousOn
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hpos u₀ hu₀))
    rcases h n with h1 | ⟨q, hq1, hq2, hq3⟩
    · have : |f u₀| ≤ |f a| := hmin (left_mem_Icc.2 hab)
      linarith
    · have : |f u₀| ≤ |f q| := hmin (show (q : ℝ) ∈ Icc a b from ⟨hq1.le, hq2.le⟩)
      linarith

/-- The event that a random continuous path visits `[-c, c]` during a random interval. -/
theorem measurableSet_exists_visit (hc : ∀ ω, Continuous (F ω))
    (hm : ∀ u, Measurable fun ω => F ω u) {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b)
    (c : ℝ) : MeasurableSet {ω | ∃ u ∈ Icc (a ω) (b ω), |F ω u| ≤ c} := by
  have heq : {ω | ∃ u ∈ Icc (a ω) (b ω), |F ω u| ≤ c} =
      {ω | a ω ≤ b ω} ∩ ⋂ n : ℕ, ({ω | |F ω (a ω)| < c + 1 / (n + 1)} ∪
        ⋃ q : ℚ, ({ω | a ω < q} ∩ {ω | (q : ℝ) < b ω} ∩ {ω | |F ω q| < c + 1 / (n + 1)})) := by
    ext ω
    simp only [mem_inter_iff, mem_iInter, mem_union, mem_iUnion]
    rw [mem_ofPred_eq, exists_visit_iff (hc ω)]
    simp only [mem_ofPred_eq, and_assoc]
  rw [heq]
  have hFa : Measurable fun ω => |F ω (a ω)| :=
    continuous_abs.measurable.comp (measurable_path_apply hc hm ha)
  refine (measurableSet_le ha hb).inter (MeasurableSet.iInter fun n => ?_)
  refine (measurableSet_lt hFa measurable_const).union (MeasurableSet.iUnion fun q => ?_)
  exact ((measurableSet_lt ha measurable_const).inter (measurableSet_lt measurable_const hb)).inter
    (measurableSet_lt (continuous_abs.measurable.comp (hm q)) measurable_const)

theorem measurable_firstVisit (hc : ∀ ω, Continuous (F ω)) (hm : ∀ u, Measurable fun ω => F ω u)
    {b : Ω → ℝ} (hb : Measurable b) (c K : ℝ) :
    Measurable fun ω => firstVisit (F ω) c K (b ω) := by
  refine measurable_of_Iic fun t => ?_
  have heq : (fun ω => firstVisit (F ω) c K (b ω)) ⁻¹' Iic t =
      {ω | ∃ u ∈ Icc (b ω) (min t K), |F ω u| ≤ c} ∪
        ({ω | ∃ u ∈ Icc (b ω) K, |F ω u| ≤ c}ᶜ ∩ {_ω | K + 1 ≤ t}) := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_compl_iff]
    exact firstVisit_le_iff (hc ω) t
  rw [heq]
  exact (measurableSet_exists_visit hc hm hb measurable_const c).union
    ((measurableSet_exists_visit hc hm hb measurable_const c).compl.inter
      (MeasurableSet.const (K + 1 ≤ t)))

theorem measurable_entrance (hc : ∀ ω, Continuous (F ω)) (hm : ∀ u, Measurable fun ω => F ω u)
    (c L K : ℝ) (j : ℕ) : Measurable fun ω => entrance (F ω) c L K j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [entrance_succ]
    exact measurable_firstVisit hc hm (ih.add_const _) c K

theorem measurable_occupation (hc : ∀ ω, Continuous (F ω)) (hm : ∀ u, Measurable fun ω => F ω u)
    {b : Ω → ℝ} (hb : Measurable b) (ℓ : ℝ) : Measurable fun ω => occupation (F ω) (b ω) ℓ := by
  have hS : MeasurableSet {p : Ω × ℝ | p.2 ∈ Icc (b p.1) (b p.1 + ℓ) ∧ |F p.1 p.2| ≤ 1} := by
    have h1 : Measurable fun p : Ω × ℝ => b p.1 := hb.comp measurable_fst
    refine ((measurableSet_le h1 measurable_snd).inter
      (measurableSet_le measurable_snd (h1.add_const ℓ))).inter ?_
    exact measurableSet_le (continuous_abs.measurable.comp (measurable_uncurry_path hc hm))
      measurable_const
  exact measurable_measure_prodMk_left hS

theorem measurableSet_trialEvent (hc : ∀ ω, Continuous (F ω))
    (hm : ∀ u, Measurable fun ω => F ω u) (c L K r : ℝ) (m : ℕ) :
    MeasurableSet {ω | TrialEvent (F ω) c L K r m} := by
  have heq : {ω | TrialEvent (F ω) c L K r m} = ⋂ j ∈ Finset.range m,
      ({ω | entrance (F ω) c L K j + 2 * L ≤ K} ∩
        {ω | occupation (F ω) (entrance (F ω) c L K j) (2 * L) ≤ ENNReal.ofReal r}) := by
    ext ω
    simp [TrialEvent]
  rw [heq]
  refine Finset.measurableSet_biInter _ fun j _ => ?_
  exact (measurableSet_le ((measurable_entrance hc hm c L K j).add_const _) measurable_const).inter
    (measurableSet_le (measurable_occupation hc hm (measurable_entrance hc hm c L K j) _)
      measurable_const)

theorem measurableSet_trialFound (hc : ∀ ω, Continuous (F ω))
    (hm : ∀ u, Measurable fun ω => F ω u) (c L K r : ℝ) (m : ℕ) :
    MeasurableSet {ω | TrialFound (F ω) c L K r m} := by
  have heq : {ω | TrialFound (F ω) c L K r m} = ⋂ j ∈ Finset.range m,
      ({ω | entrance (F ω) c L K j ≤ K} ∩
        {ω | occupation (F ω) (entrance (F ω) c L K j) (2 * L) ≤ ENNReal.ofReal r}) := by
    ext ω
    simp [TrialFound]
  rw [heq]
  refine Finset.measurableSet_biInter _ fun j _ => ?_
  exact (measurableSet_le (measurable_entrance hc hm c L K j) measurable_const).inter
    (measurableSet_le (measurable_occupation hc hm (measurable_entrance hc hm c L K j) _)
      measurable_const)

end Measurability

end InteractingSLE.SLE8
