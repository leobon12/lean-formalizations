import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# THM11-EXT-MEASLIM: left limits from vanishing oscillation at rational points

Own elementary proof (standard real analysis): the left limit at `τ` exists iff the oscillation
over the rational points of the windows `[τ − 1/(m+1), τ)` vanishes.  No source needed; recorded
as an own argument.

For `f : ℝ → ℝ` continuous on every `[a,b] ⊆ [0,τ)` with `τ > 0`:

* `ratOsc_of_tendsto`: if `f s → L` as `s ↑ τ`, then for every `n` there is `m` such that `f` has
  oscillation `≤ 1/(n+1)` over the rational points of `[τ − 1/(m+1), τ)` (`RatOsc f τ m n`).
* `exists_tendsto_of_ratOsc`: conversely, if `RatOsc f τ m n` holds for some `m` for every `n`,
  then `lim_{s↑τ} f s` exists: the left approach `u j = τ − 1/(j+1)` is such that `f (u j)` is
  Cauchy, and any point close to `τ` from the left is trapped by the oscillation bound.
* `tendsto_iff_ratOsc`: the two are equivalent.

Rational points suffice by continuity and density of `ℚ`; the windows `[τ−1/(m+1), τ)` form a
basis of the filter `𝓝[<] τ`.

Used by `QuantumZipper.Proofs.Thm11.ExtMeas` for the pointwise left limits appearing in the
extended field of the Theorem 1.1 addendum.
-/

noncomputable section

open Filter Set

open scoped Topology

namespace QuantumZipper.Thm11Asm.MeasLimit

/-- `RatOsc f τ m n` says that the oscillation of `f` over the rational points of the window
`[τ - 1/(m+1), τ)` is at most `1/(n+1)`. -/
def RatOsc (f : ℝ → ℝ) (τ : ℝ) (m n : ℕ) : Prop :=
  ∀ q q' : ℚ, (0 : ℝ) ≤ q → (q : ℝ) < τ → τ - 1 / ((m : ℝ) + 1) ≤ (q : ℝ) →
    (0 : ℝ) ≤ q' → (q' : ℝ) < τ → τ - 1 / ((m : ℝ) + 1) ≤ (q' : ℝ) →
    |f q - f q'| ≤ 1 / ((n : ℝ) + 1)

/-- The left approach sequence `u j = τ - 1/(j+1)`, which increases to `τ`. -/
def tauSeq (τ : ℝ) (j : ℕ) : ℝ := τ - 1 / ((j : ℝ) + 1)

lemma tauSeq_lt (τ : ℝ) (j : ℕ) : tauSeq τ j < τ := by
  have h : 0 < 1 / ((j : ℝ) + 1) := by positivity
  simp only [tauSeq]
  linarith

lemma tauSeq_ge (τ : ℝ) {m j : ℕ} (h : m ≤ j) : τ - 1 / ((m : ℝ) + 1) ≤ tauSeq τ j := by
  have hcast : (m : ℝ) + 1 ≤ (j : ℝ) + 1 := by
    have h' : (m : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr h
    linarith
  have h1 : 1 / ((j : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hcast
  simp only [tauSeq]
  linarith

lemma tauSeq_nonneg (τ : ℝ) (hτ : 0 < τ) {j : ℕ} (h : 1 / τ ≤ (j : ℝ)) : 0 ≤ tauSeq τ j := by
  simp only [tauSeq, sub_nonneg]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
  have h1 : 1 ≤ (j : ℝ) * τ := (div_le_iff₀ hτ).mp h
  nlinarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j]

/-- `a ≤ b` as soon as `a ≤ b + ε` for every `ε > 0`. -/
lemma measLimit_le_of_forall_pos_le_add {a b : ℝ} (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := by
  by_contra hlt
  have hba : b < a := lt_of_not_ge hlt
  have hε : 0 < (a - b) / 2 := by linarith
  linarith [h _ hε]

/-- Density of the rationals inside a nondegenerate interval: every point `x ∈ [a,b]` has
rational points of `[a,b]` arbitrarily close to it. -/
lemma exists_rat_mem_Icc_abs_sub_lt {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ q : ℚ, ((q : ℝ) ∈ Icc a b) ∧ |(q : ℝ) - x| < ρ := by
  have hmax : max a (x - ρ) < min b (x + ρ) := by
    refine max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨hab, by linarith [hx.1, hρ]⟩,
      lt_min_iff.mpr ⟨by linarith [hx.2, hρ], by linarith⟩⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hmax
  have h1 : x - ρ < (q : ℝ) := lt_of_le_of_lt (le_max_right a (x - ρ)) hq1
  have h2 : (q : ℝ) < x + ρ := lt_of_lt_of_le hq2 (min_le_right b (x + ρ))
  refine ⟨q, ⟨le_of_lt (lt_of_le_of_lt (le_max_left a (x - ρ)) hq1),
    le_of_lt (lt_of_lt_of_le hq2 (min_le_left b (x + ρ)))⟩, ?_⟩
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- Near a point of continuity inside `[a,b]` (`a < b`), the values of `f` at rational points of
`[a,b]` approximate `f x` arbitrarily well. -/
lemma exists_rat_abs_sub_lt_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hab : a < b) {x : ℝ} (hx : x ∈ Icc a b) {η : ℝ}
    (hη : 0 < η) : ∃ q : ℚ, ((q : ℝ) ∈ Icc a b) ∧ |f (q : ℝ) - f x| < η := by
  have hmem : f ⁻¹' Metric.ball (f x) η ∈ 𝓝[Icc a b] x :=
    (ContinuousOn.continuousWithinAt hcont hx).tendsto (Metric.ball_mem_nhds (f x) hη)
  rw [Metric.mem_nhdsWithin_iff] at hmem
  obtain ⟨δ, hδ0, hδ⟩ := hmem
  obtain ⟨q, hq, hqd⟩ :=
    exists_rat_mem_Icc_abs_sub_lt hab hx (ρ := min δ η) (lt_min_iff.mpr ⟨hδ0, hη⟩)
  refine ⟨q, hq, ?_⟩
  have hqδ : dist (q : ℝ) x < δ := by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hqd (min_le_left δ η)
  have hfin := hδ ⟨hqδ, hq⟩
  simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hfin
  exact hfin

/-- The oscillation bound `1/(n+1)` of `RatOsc f τ m n`, extended from the rational points to all
real points of `[max 0 (τ - 1/(m+1)), τ)`: rational points of a window are dense in it and `f` is
continuous there. -/
lemma abs_sub_le_of_ratOsc {f : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hcont : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < τ → ContinuousOn f (Icc a b))
    {m n : ℕ} (hosc : RatOsc f τ m n) :
    ∀ s t : ℝ, s < τ → t < τ → max 0 (τ - 1 / ((m : ℝ) + 1)) ≤ s →
      max 0 (τ - 1 / ((m : ℝ) + 1)) ≤ t → |f s - f t| ≤ 1 / ((n : ℝ) + 1) := by
  intro s t hsτ htτ hs ht
  have hmaxst : max s t < τ := max_lt_iff.mpr ⟨hsτ, htτ⟩
  set hi : ℝ := (max s t + τ) / 2 with hhi
  have hshi : s ≤ hi := by rw [hhi]; linarith [le_max_left s t, hmaxst]
  have hthi : t ≤ hi := by rw [hhi]; linarith [le_max_right s t, hmaxst]
  have hhiτ : hi < τ := by rw [hhi]; linarith
  rcases lt_or_eq_of_le (le_trans hs hshi) with hlt | heq
  · -- nondegenerate case: approximate `s` and `t` by rationals of the window
    have hsI : s ∈ Icc (max 0 (τ - 1 / ((m : ℝ) + 1))) hi := ⟨hs, hshi⟩
    have htI : t ∈ Icc (max 0 (τ - 1 / ((m : ℝ) + 1))) hi := ⟨ht, hthi⟩
    have hcont' : ContinuousOn f (Icc (max 0 (τ - 1 / ((m : ℝ) + 1))) hi) :=
      hcont _ _ (le_max_left _ _) (le_of_lt hlt) hhiτ
    refine measLimit_le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨q, hqI, hq⟩ :=
      exists_rat_abs_sub_lt_of_continuousOn hcont' hlt hsI (η := δ / 2) (by linarith)
    obtain ⟨q', hq'I, hq'⟩ :=
      exists_rat_abs_sub_lt_of_continuousOn hcont' hlt htI (η := δ / 2) (by linarith)
    have hqτ : (q : ℝ) < τ := lt_of_le_of_lt hqI.2 hhiτ
    have hq'τ : (q' : ℝ) < τ := lt_of_le_of_lt hq'I.2 hhiτ
    have hqq' : |f (q : ℝ) - f (q' : ℝ)| ≤ 1 / ((n : ℝ) + 1) :=
      hosc q q' (le_trans (le_max_left _ _) hqI.1) hqτ (le_trans (le_max_right _ _) hqI.1)
        (le_trans (le_max_left _ _) hq'I.1) hq'τ (le_trans (le_max_right _ _) hq'I.1)
    have h1 : |f s - f (q : ℝ)| < δ / 2 := by rw [abs_sub_comm]; exact hq
    calc |f s - f t| ≤ |f s - f (q : ℝ)| + |f (q : ℝ) - f (q' : ℝ)| + |f (q' : ℝ) - f t| := by
          have hA := abs_sub_le (f s) (f (q : ℝ)) (f t)
          have hB := abs_sub_le (f (q : ℝ)) (f (q' : ℝ)) (f t)
          linarith
      _ ≤ δ / 2 + 1 / ((n : ℝ) + 1) + δ / 2 := by linarith
      _ = 1 / ((n : ℝ) + 1) + δ := by ring
  · -- degenerate case `hi` is already the left endpoint: then `s = t`
    have hshi' : s ≤ max 0 (τ - 1 / ((m : ℝ) + 1)) := by rw [heq, hhi]; linarith [le_max_left s t]
    have hthi' : t ≤ max 0 (τ - 1 / ((m : ℝ) + 1)) := by
      rw [heq, hhi]; linarith [le_max_right s t]
    rw [le_antisymm hshi' hs, le_antisymm hthi' ht, sub_self, abs_zero]
    positivity

theorem ratOsc_of_tendsto {f : ℝ → ℝ} {τ L : ℝ} (hτ : 0 < τ)
    (h : Tendsto f (𝓝[<] τ) (𝓝 L)) : ∀ n : ℕ, ∃ m : ℕ, RatOsc f τ m n := by
  intro n
  have hε : 0 < 1 / ((n : ℝ) + 1) / 2 := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp h _ hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ0
  refine ⟨m, fun q q' hq0 hqτ hqm hq'0 hq'τ hq'm => ?_⟩
  have hq : |f (q : ℝ) - L| < 1 / ((n : ℝ) + 1) / 2 := by
    have hdist : dist (q : ℝ) τ < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      linarith
    rw [← Real.dist_eq]
    exact hδ hqτ hdist
  have hq' : |L - f (q' : ℝ)| < 1 / ((n : ℝ) + 1) / 2 := by
    have hdist : dist (q' : ℝ) τ < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      linarith
    have h1 := hδ hq'τ hdist
    rw [Real.dist_eq] at h1
    rwa [abs_sub_comm]
  calc |f (q : ℝ) - f (q' : ℝ)| ≤ |f (q : ℝ) - L| + |L - f (q' : ℝ)| := abs_sub_le _ _ _
    _ ≤ 1 / ((n : ℝ) + 1) / 2 + 1 / ((n : ℝ) + 1) / 2 := by linarith
    _ = 1 / ((n : ℝ) + 1) := by ring

theorem exists_tendsto_of_ratOsc {f : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hcont : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < τ → ContinuousOn f (Icc a b))
    (h : ∀ n : ℕ, ∃ m : ℕ, RatOsc f τ m n) :
    ∃ L : ℝ, Tendsto f (𝓝[<] τ) (𝓝 L) := by
  -- indices `j ≥ J` give `tauSeq τ j ≥ 0`
  obtain ⟨J, hJ⟩ := exists_nat_ge (1 / τ)
  have hzero : ∀ j : ℕ, J ≤ j → 0 ≤ tauSeq τ j := fun j hj =>
    tauSeq_nonneg τ hτ (le_trans hJ (Nat.cast_le.mpr hj))
  -- the oscillation bound for two sequence indices above `max m J`
  have hkey : ∀ m n : ℕ, RatOsc f τ m n → ∀ j k : ℕ, max m J ≤ j → max m J ≤ k →
      |f (tauSeq τ j) - f (tauSeq τ k)| ≤ 1 / ((n : ℝ) + 1) := by
    intro m n hosc j k hj hk
    refine abs_sub_le_of_ratOsc hτ hcont hosc _ _ (tauSeq_lt τ j) (tauSeq_lt τ k)
      (max_le_iff.mpr ⟨hzero j (le_trans (le_max_right m J) hj),
        tauSeq_ge τ (le_trans (le_max_left m J) hj)⟩)
      (max_le_iff.mpr ⟨hzero k (le_trans (le_max_right m J) hk),
        tauSeq_ge τ (le_trans (le_max_left m J) hk)⟩)
  have hcauchy : CauchySeq fun j : ℕ => f (tauSeq τ j) := by
    rw [cauchySeq_iff]
    intro V hV
    obtain ⟨ε, hε, hVε⟩ := Metric.mem_uniformity_dist.mp hV
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨m, hosc⟩ := h n
    refine ⟨max m J, fun k hk l hl => hVε ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hkey m n hosc k l hk hl) hn
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, ?_⟩
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by linarith)
  obtain ⟨m, hosc⟩ := h n
  refine ⟨min (1 / ((m : ℝ) + 1)) (τ / 2), lt_min_iff.mpr ⟨by positivity, by linarith⟩, ?_⟩
  intro s hs hdist
  have hsτ : s < τ := hs
  have hslt : τ - min (1 / ((m : ℝ) + 1)) (τ / 2) < s := by
    rw [Real.dist_eq, abs_of_neg (by linarith : s - τ < 0)] at hdist
    linarith
  have hs0 : 0 ≤ s := by
    have := min_le_right (1 / ((m : ℝ) + 1)) (τ / 2)
    linarith
  have hsm : τ - 1 / ((m : ℝ) + 1) ≤ s := by
    have := min_le_left (1 / ((m : ℝ) + 1)) (τ / 2)
    linarith
  -- the bound against the sequence point `tauSeq τ (max m J)`
  have hM : |f s - f (tauSeq τ (max m J))| ≤ 1 / ((n : ℝ) + 1) :=
    abs_sub_le_of_ratOsc hτ hcont hosc s (tauSeq τ (max m J)) hsτ
      (tauSeq_lt τ (max m J)) (max_le_iff.mpr ⟨hs0, hsm⟩)
      (max_le_iff.mpr ⟨hzero (max m J) (le_max_right m J), tauSeq_ge τ (le_max_left m J)⟩)
  have hML : |f (tauSeq τ (max m J)) - L| ≤ 1 / ((n : ℝ) + 1) := by
    have hpt : ∀ j : ℕ, max m J ≤ j →
        f (tauSeq τ (max m J)) - 1 / ((n : ℝ) + 1) ≤ f (tauSeq τ j) ∧
          f (tauSeq τ j) ≤ f (tauSeq τ (max m J)) + 1 / ((n : ℝ) + 1) := by
      intro j hj
      have h1 := hkey m n hosc (max m J) j le_rfl hj
      rw [abs_sub_le_iff] at h1
      exact ⟨by linarith [h1.2], by linarith [h1.1]⟩
    have hlow : f (tauSeq τ (max m J)) - 1 / ((n : ℝ) + 1) ≤ L :=
      ge_of_tendsto hL (eventually_atTop.mpr ⟨max m J, fun j hj => (hpt j hj).1⟩)
    have hup : L ≤ f (tauSeq τ (max m J)) + 1 / ((n : ℝ) + 1) :=
      le_of_tendsto hL (eventually_atTop.mpr ⟨max m J, fun j hj => (hpt j hj).2⟩)
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  rw [Real.dist_eq]
  have hfin : |f s - L| ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) :=
    calc |f s - L| ≤ |f s - f (tauSeq τ (max m J))| + |f (tauSeq τ (max m J)) - L| :=
          abs_sub_le _ _ _
      _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by linarith
  linarith

theorem tendsto_iff_ratOsc {f : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hcont : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < τ → ContinuousOn f (Icc a b)) :
    (∃ L : ℝ, Tendsto f (𝓝[<] τ) (𝓝 L)) ↔ ∀ n : ℕ, ∃ m : ℕ, RatOsc f τ m n :=
  ⟨fun ⟨_, hL⟩ => ratOsc_of_tendsto hτ hL, exists_tendsto_of_ratOsc hτ hcont⟩

end QuantumZipper.Thm11Asm.MeasLimit
