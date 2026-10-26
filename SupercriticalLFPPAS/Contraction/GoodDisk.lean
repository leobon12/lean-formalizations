import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLFPPAS.Contraction.Times
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PaidTraces
import SupercriticalLQGUniqueness.B2.Polylog.P3PaidGeometry

/-!
# One good disk along the source geodesic (Lemma 4.1, SB2 D6 steps 3–5 and 7)

For a time `τ` of a unit-speed source geodesic `P : [0, L] → ℂ` and a good disk `(c, r)` (`Core.GoodDiskIn`, SB2 D6
(a)–(c)) with `|P τ − c| < r` and both endpoints of `P` outside `B_{8r}(c)`:
* the excursion `I = [α, β]` and its crossing `G = [s, t]` (`l41_excursion`);
* `|I| ≤ d(around A_{7r,8r}(c))` by the source separator shortcut (`separator_twoSidedShortcut_around`, paper
  l. 416–417);
* `|G| ≥ acrossIn(d; c, r, 2r) ≥ |I|/A` (`acrossIn_le_len_of_crossing` and (a); paper (4.2));
* the target crossing bound of (b) for `G`, and the two target separators of (c) at `P s` and `P t` with `[α, β] = I`
  (the ends of `I` are at distance `≥ 4r ≥ 2√η r` from both points).

The output is recorded in the `Prop`-structure `L41Exc`.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Contraction

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn annAt closedAnn acrossIn_le_len_of_crossing)
open LQGMetric.MetricGeometry (IsGeodesicCurve)

/-- The length of a unit-speed curve on a subinterval is the length of the subinterval. -/
theorem l41_len_eq {d : LSCMetric} {P : ℝ → ℂ} {L s t : ℝ}
    (hu : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 L)) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) :
    d.len P s t = ENNReal.ofReal (t - s) := by
  have h := hu ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩
  rw [inter_eq_right.mpr (Icc_subset_Icc hs ht)] at h
  unfold LSCMetric.len
  simpa only [NNReal.coe_one, one_mul] using h

/-- The data produced by one good disk `(c, r)` along `P` (SB2 D6 steps 3–5, 7): the excursion `[α, β]` inside
`B̄_{6r}(c)`, the crossing `[s, t]` of `Ā_{r,2r}(c)`, `|I| ≤ A|G|`, the target crossing bound for `G`, and target
separators around `P s` and `P t` paid by `(d₀/10) K |I|`. -/
structure L41Exc (d' : LSCMetric) (W : Set ℂ) (P : ℝ → ℂ) (L η d₀ A Kf : ℝ) (c : ℂ)
    (r α β s t : ℝ) : Prop where
  r_pos : 0 < r
  α_pos : 0 < α
  α_lt_s : α < s
  s_lt_t : s < t
  t_lt_β : t < β
  β_lt : β < L
  frac : β - α ≤ A * (t - s)
  in6 : ∀ u ∈ Icc α β, dist (P u) c ≤ 6 * r
  s_dist : dist (P s) c = r
  t_dist : dist (P t) c = 2 * r
  cross : d'.internalSetDist W {y | (y : ℂ) ∈ ball (P s) (η * r / 2)}
      {y | (y : ℂ) ∈ ball (P t) (η * r / 2)} ≤ ENNReal.ofReal ((1 + d₀ / 10) * Kf * (t - s))
  sep_s : ∃ (σ : ℝ → ℂ) (a' b' : ℝ), d'.IsCurve σ a' b' ∧ ContinuousOn σ (Icc a' b') ∧
      σ '' Icc a' b' ⊆ ball (P s) (r / 10) ∧ σ '' Icc a' b' ⊆ W ∧ P s ∉ σ '' Icc a' b' ∧
      ball (P s) (η * r) ⊆ connectedComponentIn (σ '' Icc a' b')ᶜ (P s) ∧
      Bornology.IsBounded (connectedComponentIn (σ '' Icc a' b')ᶜ (P s)) ∧
      d'.len σ a' b' ≤ ENNReal.ofReal (d₀ / 10 * Kf * (β - α))
  sep_t : ∃ (σ : ℝ → ℂ) (a' b' : ℝ), d'.IsCurve σ a' b' ∧ ContinuousOn σ (Icc a' b') ∧
      σ '' Icc a' b' ⊆ ball (P t) (r / 10) ∧ σ '' Icc a' b' ⊆ W ∧ P t ∉ σ '' Icc a' b' ∧
      ball (P t) (η * r) ⊆ connectedComponentIn (σ '' Icc a' b')ᶜ (P t) ∧
      Bornology.IsBounded (connectedComponentIn (σ '' Icc a' b')ᶜ (P t)) ∧
      d'.len σ a' b' ≤ ENNReal.ofReal (d₀ / 10 * Kf * (β - α))

/-- **One good disk** (SB2 D6 steps 3–5 and the junction loops of step 7). -/
theorem l41_goodDisk_exc {d d' : LSCMetric} {W : Set ℂ} {P : ℝ → ℂ} {L η d₀ A Kf : ℝ}
    {c : ℂ} {r : ℝ} (hg : Core.GoodDiskIn d d' W P L η d₀ A Kf c r)
    (hgeo : IsGeodesicCurve (d.pt ∘ P) 0 L) (hunit : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 L))
    (hPc : ContinuousOn P (Icc 0 L)) (hη' : 2 * Real.sqrt η < 1 / 10) (hA : 0 ≤ A)
    {τ : ℝ} (hτ : τ ∈ Icc 0 L) (hτc : dist (P τ) c < r) (h0 : 8 * r ≤ dist (P 0) c)
    (hLc : 8 * r ≤ dist (P L) c) :
    ∃ α β s t : ℝ, α < τ ∧ τ ≤ s ∧ L41Exc d' W P L η d₀ A Kf c r α β s t := by
  have hr : 0 < r := hg.pos
  obtain ⟨α, β, s, t, hαpos, hατ, hτs, hst, htβ, hβL, hαeq, hβeq, hseq, hteq, hin6, hann⟩ :=
    l41_excursion hPc hr hτ hτc h0 hLc
  have hs0 : 0 ≤ s := hτ.1.trans hτs
  have htL : t ≤ L := htβ.le.trans hβL.le
  have hαs : α < s := hατ.trans_le hτs
  -- `|I| ≤ d(around A_{7r,8r}(c))` (SB2 D6 step 4)
  have hI : ENNReal.ofReal (β - α) ≤
      aroundDist d (annAt c (7 * r) (8 * r) (by positivity) (by linarith)) := by
    refine Uniqueness.Toolkit.PlanarSeparation.separator_twoSidedShortcut_around d
      (annAt c (7 * r) (8 * r) (by positivity) (by linarith)) le_rfl hαpos
      (hαs.trans (hst.trans htβ)).le hβL le_rfl hPc hgeo hunit ?_ ?_ ?_ ?_
    · show 8 * r ≤ dist (P 0) c
      exact h0
    · show dist (P α) c ≤ 7 * r
      linarith
    · show dist (P β) c ≤ 7 * r
      linarith
    · show 8 * r ≤ dist (P L) c
      exact hLc
  -- `|G| ≥ acrossIn(d; c, r, 2r)` (SB2 D6 step 5)
  have hlen : d.len P s t = ENNReal.ofReal (t - s) := l41_len_eq hunit hs0 hst.le htL
  have hG : acrossIn d c r (2 * r) ≤ ENNReal.ofReal (t - s) := by
    rw [← hlen]
    refine acrossIn_le_len_of_crossing d c hr ⟨hst.le, hgeo.2.1.mono (Icc_subset_Icc hs0 htL)⟩
      (hPc.mono (Icc_subset_Icc hs0 htL)) ?_ ?_
    · rw [← dist_eq_norm, hseq]
    · rw [← dist_eq_norm, hteq]
  have hfrac : β - α ≤ A * (t - s) := by
    have hchain : ENNReal.ofReal (β - α) ≤ ENNReal.ofReal (A * (t - s)) := by
      calc ENNReal.ofReal (β - α)
          ≤ aroundDist d (annAt c (7 * r) (8 * r) (by positivity) (by linarith)) := hI
        _ ≤ ENNReal.ofReal A * acrossIn d c r (2 * r) := hg.ratio
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal (t - s) := by gcongr
        _ = ENNReal.ofReal (A * (t - s)) := (ENNReal.ofReal_mul hA).symm
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA (sub_nonneg.mpr hst.le))).mp hchain
  have hGI : ENNReal.ofReal (t - s) ≤
      aroundDist d (annAt c (7 * r) (8 * r) (by positivity) (by linarith)) :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hI
  -- the target crossing bound (b)
  have hcross := hg.cross s t hs0 hst.le htL hseq hteq
    (fun u hu => by
      have h := hann u hu
      rw [dist_eq_norm] at h
      exact h) hGI
  -- the target separators (c) at `P s` and `P t`, with `[α, β] = I`
  have hsqrt : 2 * Real.sqrt η * r ≤ 4 * r := by nlinarith
  have hαβ : α ≤ β := (hαs.trans (hst.trans htβ)).le
  have hfar_s : ∀ x, dist (P x) c = 6 * r → 2 * Real.sqrt η * r ≤ dist (P x) (P s) := by
    intro x hx
    have htri := dist_triangle (P x) (P s) c
    linarith
  have hfar_t : ∀ x, dist (P x) c = 6 * r → 2 * Real.sqrt η * r ≤ dist (P x) (P t) := by
    intro x hx
    have htri := dist_triangle (P x) (P t) c
    linarith
  have hsep_s := hg.surround α β (P s) hαpos.le hαβ hβL.le ⟨s, ⟨hαs.le, (hst.trans htβ).le⟩, rfl⟩
    (Or.inl hseq) (hfar_s α hαeq) (hfar_s β hβeq)
  have hsep_t := hg.surround α β (P t) hαpos.le hαβ hβL.le ⟨t, ⟨(hαs.trans hst).le, htβ.le⟩, rfl⟩
    (Or.inr hteq) (hfar_t α hαeq) (hfar_t β hβeq)
  exact ⟨α, β, s, t, hατ, hτs, ⟨hr, hαpos, hαs, hst, htβ, hβL, hfrac, hin6, hseq, hteq, hcross,
    hsep_s, hsep_t⟩⟩

end SupercriticalLFPPAS.Contraction
