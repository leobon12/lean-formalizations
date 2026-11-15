/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB10ProofDet
import InteractingSLE.Spec.Dimension.Finite
import InteractingSLE.Foundations.SLE.All

/-!
# Lemma GB10: no simple-arc time interval for a finite-force counterflow (proof)

Packet PROVE-T14-GW4S. **Lemma GB10** (`source/spec/p529-576.md` L629–L635, p. 555), the named input
`GB10.GB10Statement` of PROVE-T14-GW4R, is proved here for every `k > 4` and every integrated `SLE_k(ρ)` evolution.

Source proof, first paragraph: "At a deterministic rational own time whose tip is in the original open half-plane,
every force gap is nonzero […] On the countable bounded time/driver/gap localizations, deletion of the bounded force
drift therefore gives local absolute continuity with ordinary `SLE_k`. Ordinary `SLE_k` has real contacts
arbitrarily soon after time zero […] Consequently the own-mapped future at each of the just described rational
restarts cannot stay in the open half-plane for a positive time interval. Intersect these events countably."

* nonzero gaps at interior tips: `IsIntegratedSLEEvolution.ae_forall_ne_of_mem_H` (Aux. lemma 15's (O2), landed);
* the localizations: `Dimension.exists_brownian_localization` (Aux. lemma 15's (O1), landed) at every rational start
  `q` and gap size `1/(n + 1)`: a random path `X` with law absolutely continuous w.r.t. Wiener measure and
  `W_{q+t} − W_q = √k X_t` while the gaps stay `≥ 1/(n+1)`;
* ordinary `SLE_k`, `k > 4`: "real contacts arbitrarily soon" in the stronger form of [RS05, Lemma 7.3], every
  positive-time hull contains a half-neighbourhood of `0` (`ae_forall_sleHull_halfBall_of_four_lt`, landed), moved to
  `X` by absolute continuity (no measurability of the event needed);
* the deterministic contradiction (`GB10ProofDet.lean`, `noSimpleArcInterval_of_halfBall`).

The hypothesis `IsOrderedForceWord` of the statement is not needed.

## Main result

* **`gb10Statement`** : `GB10.GB10Statement.{u}` (unconditional).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull drive sleHull)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GB10

open Dimension QuantumZipper.RS

/-- **Lemma GB10** (supplement p. 555): for `k > 4` and every integrated `SLE_k(ρ)` evolution, almost surely every
continuous generating trace up to the lifetime has no nontrivial time interval inside a compact simple arc. -/
theorem gb10Statement : GB10Statement.{u} := by
  intro k hk nL nR xL xR ρL ρR _ Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hk0 : 0 < k := by linarith
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hloc := fun p : ℚ × ℕ =>
    exists_brownian_localization hk0 hE ((p.1 : ℝ).toNNReal) (p.2 : ℝ≥0) (hδ p.2)
  choose X hXm μ hμprob hμBM hac hXeq using hloc
  have hgood : ∀ p : ℚ × ℕ, ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε →
      z ∈ sleHull k canonBM (X p ω) t := fun p => by
    have := hμprob p
    exact ae_of_ae_map (hXm p).aemeasurable ((hac p).ae_le (ae_forall_sleHull_halfBall_of_four_lt (hμBM p) hk))
  filter_upwards [ae_all_iff.2 hgood, ae_all_iff.2 hXeq, hE.ae_forall_ne_of_mem_H, hE.2.2.2.2]
    with ω hg hx hgap hp γ hγ
  have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
  refine noSimpleArcInterval_of_halfBall hγ hw hp.1 fun q hq0 hqζ hqH => ?_
  set a : ℝ≥0 := (q : ℝ).toNNReal with ha
  obtain ⟨hgL, hgR⟩ := hgap γ hγ a hqζ hqH
  obtain ⟨ε, hε, hεgap⟩ := exists_gap_half_lt hw hp.2.2.2.2.1 hp.2.2.2.2.2.1 hqζ
  -- the gap threshold `1/(n+1)` below half the gaps at `a`, and the horizon `n ≥ 1`
  have hevn : ∀ᶠ n : ℕ in atTop, ((∀ i, 1 / ((n : ℝ) + 1) < |W a ω - VL i a ω| / 2) ∧
      ∀ i, 1 / ((n : ℝ) + 1) < |W a ω - VR i a ω| / 2) ∧ 1 ≤ n := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine ((Filter.eventually_all.2 fun i => h0.eventually (gt_mem_nhds ?_)).and
      (Filter.eventually_all.2 fun i => h0.eventually (gt_mem_nhds ?_))).and (eventually_ge_atTop 1)
    · exact half_pos (abs_pos.2 (sub_ne_zero.2 (hgL i)))
    · exact half_pos (abs_pos.2 (sub_ne_zero.2 (hgR i)))
  obtain ⟨n, ⟨hnL, hnR⟩, hn1⟩ := hevn.exists
  -- a margin before the lifetime
  obtain ⟨r, har, hrζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqζ
  have har' : (a : ℝ) < r := by exact_mod_cast ENNReal.coe_lt_coe.1 har
  set t₁ : ℝ := min (min (ε / 2) 1) ((r : ℝ) - a) with ht₁
  have ht₁0 : 0 < t₁ := lt_min (lt_min (by linarith) one_pos) (by linarith)
  have ht₁ε : t₁ ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have ht₁1 : t₁ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have ht₁r : t₁ ≤ (r : ℝ) - a := min_le_right _ _
  refine ⟨t₁, ht₁0, fun t ht => ?_⟩
  set t₄ : ℝ := (t + t₁) / 2 with ht₄
  have htt₄ : t < t₄ := by rw [ht₄]; linarith [ht.2]
  have ht₄t₁ : t₄ < t₁ := by rw [ht₄]; linarith [ht.2]
  have hagree : ∀ s ∈ Icc (0 : ℝ) t₄,
      (fun s : ℝ => Sec7.shiftNN (fun t => W t ω) a s.toNNReal) s = drive k canonBM (X (q, n) ω) s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hsN : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0
    have hst₁ : s < t₁ := lt_of_le_of_lt hs.2 ht₄t₁
    have hsn : s.toNNReal ≤ ((q, n).2 : ℝ≥0) := by
      rw [← NNReal.coe_le_coe, hsN]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      push_cast
      linarith
    have hsζ : ((a + s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hrζ
      rw [← NNReal.coe_le_coe, NNReal.coe_add, hsN]
      linarith
    have hgaps : ∀ s' : ℝ≥0, a ≤ s' → s' ≤ a + s.toNNReal →
        GapsGE (1 / (((q, n).2 : ℕ) + 1 : ℝ)) (W s' ω) (fun i => VL i s' ω) (fun i => VR i s' ω) := by
      intro s' hs'1 hs'2
      have hd : dist s' a < ε := by
        rw [NNReal.dist_eq, abs_lt]
        have h1 : (a : ℝ) ≤ s' := by exact_mod_cast hs'1
        have h2 : (s' : ℝ) ≤ a + s := by
          have := NNReal.coe_le_coe.2 hs'2
          rwa [NNReal.coe_add, hsN] at this
        constructor <;> linarith
      obtain ⟨hL, hR⟩ := hεgap s' hd
      constructor
      · intro i
        rcases hL i with h | h
        · exact (hnL i).le.trans h.le
        · exact absurd h (hgL i)
      · intro i
        rcases hR i with h | h
        · exact (hnR i).le.trans h.le
        · exact absurd h (hgR i)
    have h := hx (q, n) s.toNNReal hsn hsζ hgaps
    simp only [Sec7.shiftNN, drive, canonBM]
    rw [h]
  obtain ⟨ε', hε', hball⟩ := hg (q, n) t ht.1
  have hK : fwdHull (fun s : ℝ => Sec7.shiftNN (fun t => W t ω) a s.toNNReal) t =
      fwdHull (drive k canonBM (X (q, n) ω)) t :=
    fwdHull_eq_of_eqOn ht.1.le htt₄ hagree
  exact ⟨ε', hε', fun z hz hzε => hK ▸ hball z hz hzε⟩

end GB10

end Theorem14

end InteractingSLE
