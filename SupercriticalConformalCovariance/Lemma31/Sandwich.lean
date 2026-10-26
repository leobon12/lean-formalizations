import SupercriticalConformalCovariance.Compact.Lemma31Core

/-!
# Epigraph convergence: eventual congruence and the eventual multiplicative sandwich

`LSCTendsto` (DG Definition 1.2, frozen `Frozen/LSCTendsto.lean`) only
depends on the tail of the sequence (`lscTendsto_congr_eventually`). Hence the multiplicative
sandwich of `SupercriticalConformalCovariance.Compact.lscTendsto_of_multiplicative_sandwich` (`SupercriticalConformalCovariance/Compact/Lemma31Core.lean`) only
needs to hold for all large `n` (`lscTendsto_of_eventually_multiplicative_sandwich`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.Lemma31

open SupercriticalLQGUniqueness (LSCTendsto)

/-- `LSCTendsto` only depends on the tail of the sequence. -/
theorem lscTendsto_congr_eventually {α : Type*} [TopologicalSpace α]
    {F G : ℕ → α × α → EReal} {f : α × α → EReal} (hFG : ∀ᶠ n in atTop, F n = G n)
    (hF : LSCTendsto F f) : LSCTendsto G f := by
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · refine (hF.1 p q hp).trans_eq (liminf_congr ?_)
    filter_upwards [hFG] with n hn
    rw [hn]
  · obtain ⟨p, hp, hlim⟩ := hF.2 q
    refine ⟨p, hp, hlim.congr' ?_⟩
    filter_upwards [hFG] with n hn
    rw [hn]

/-- **Multiplicative sandwich, eventual form.** If `F` is lower semicontinuous, `a n, b n → 1`
and for all large `n`, `a n * F ≤ G n ≤ b n * F` everywhere, then `G n → F` in the sense of DG
Definition 1.2; `∞` values of `F` are allowed. -/
theorem lscTendsto_of_eventually_multiplicative_sandwich
    {α : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    (F : α × α → ℝ≥0∞) (hF : LowerSemicontinuous F)
    (G : ℕ → α × α → ℝ≥0∞) (a b : ℕ → ℝ≥0∞)
    (ha : Tendsto a atTop (𝓝 1)) (hb : Tendsto b atTop (𝓝 1))
    (hbound : ∀ᶠ n in atTop, ∀ p, a n * F p ≤ G n p ∧ G n p ≤ b n * F p) :
    LSCTendsto (fun n p => (G n p : EReal)) (fun p => (F p : EReal)) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  -- modify the first `N` terms so that the sandwich holds everywhere
  set G' : ℕ → α × α → ℝ≥0∞ := fun n => if N ≤ n then G n else F with hG'
  set a' : ℕ → ℝ≥0∞ := fun n => if N ≤ n then a n else 1 with ha'
  set b' : ℕ → ℝ≥0∞ := fun n => if N ≤ n then b n else 1 with hb'
  have hev : ∀ᶠ n in atTop, N ≤ n := eventually_ge_atTop N
  have ha'' : Tendsto a' atTop (𝓝 1) :=
    ha.congr' (by filter_upwards [hev] with n hn; simp [ha', hn])
  have hb'' : Tendsto b' atTop (𝓝 1) :=
    hb.congr' (by filter_upwards [hev] with n hn; simp [hb', hn])
  have hbound' : ∀ n p, a' n * F p ≤ G' n p ∧ G' n p ≤ b' n * F p := by
    intro n p
    by_cases hn : N ≤ n
    · simpa [hG', ha', hb', hn] using hN n hn p
    · simp [hG', ha', hb', hn]
  have h := SupercriticalConformalCovariance.Compact.lscTendsto_of_multiplicative_sandwich F hF G' a' b' ha'' hb'' hbound'
  refine lscTendsto_congr_eventually ?_ h
  filter_upwards [hev] with n hn
  funext p
  simp [hG', hn]

end SupercriticalConformalCovariance.Lemma31
