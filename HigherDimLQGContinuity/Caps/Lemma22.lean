import HigherDimLQGContinuity.Caps.GridGrowth
import HigherDimLQGContinuity.Caps.Variance
import HigherDimLQGContinuity.Caps.Gaussian
import HigherDimLQGContinuity.Caps.Scale
import HigherDimLQGContinuity.Caps.PinChange

/-!
# Lemma 2.2: finite scale and pin caps (packet P4)

The Gaussian union estimate controls all inspected sphere averages, and the
pointwise scale-ratio lemma applies on its complement, including at `ξ=0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory ProbabilityTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The probabilistic cap of Lemma 2.2(a), uniformly for a fixed pair of pin
radii in `[1,10]`. The decay exponent can be taken to be `1`. -/
theorem lemma22_cap {d : ℕ} (hd : 2 ≤ d) {lam κ c₀ s s₀ : ℝ}
    (hlam : 1 < lam) (hκ : 0 < κ) (hc₀ : 0 < c₀)
    (hs : 1 ≤ s) (hs10 : s ≤ 10) (hs₀ : 1 ≤ s₀) (hs₀10 : s₀ ≤ 10) :
    ∃ Ccap C : ℝ, 0 < Ccap ∧ 0 < C ∧
      ∀ {n : ℕ} {W : ℝ}, 1 ≤ n → 0 ≤ W → Real.log (1 + W) ≤ c₀ * n →
        pinLaw d s₀ {g | ∃ p ∈ gridPairs d lam κ n W,
          Ccap * n < |sphereAvg g (s * p.1) p.2|} ≤
          ENNReal.ofReal (C * Real.exp (-(n : ℝ))) := by
  classical
  obtain ⟨C₁, hC₁, hvar⟩ := p4_exists_grid_variance_bound hd hc₀.le
  obtain ⟨A, hA, hcard⟩ := p4_grid_card_exp (d := d) hlam hκ hc₀.le
  let B : ℝ := d * (c₀ + 1)
  let Ccap : ℝ := C₁ + (B + 2) / 2
  let C : ℝ := 2 * A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCcap : 0 < Ccap := by dsimp [Ccap]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨Ccap, C, hCcap, hC, ?_⟩
  intro n W hn hW hWlog
  let F : Finset (ℝ × Rd d) :=
    (p4_gridPairsFinset d lam κ n W).filter (fun p => p ∈ gridPairs d lam κ n W)
  have hFgrid : ∀ p ∈ F, p ∈ gridPairs d lam κ n W := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hFpos : ∀ p ∈ F, 0 < s * p.1 := by
    intro p hp
    obtain ⟨k, hk, -, -, -, -⟩ := hFgrid p hp
    rw [hk]
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
  have hFvar : ∀ p ∈ F,
      Var[fun g : DistRd d => sphereAvg g (s * p.1) p.2; pinLaw d s₀] ≤ C₁ * n := by
    intro p hp
    obtain ⟨k, hk, hr, j, hz, hnorm⟩ := hFgrid p hp
    have hrpos : 0 < p.1 := by rw [hk]; exact Real.rpow_pos_of_pos (by linarith) _
    have hr1 : p.1 ≤ 1 := by
      rw [hk]
      exact Real.rpow_le_one_of_one_le_of_nonpos hlam.le (neg_nonpos.mpr (Nat.cast_nonneg k))
    exact hvar hs hs10 hs₀ hs₀10 hn hW hWlog hrpos hr hr1 p.2 hnorm
  have hevent : {g : DistRd d | ∃ p ∈ gridPairs d lam κ n W,
      Ccap * n < |sphereAvg g (s * p.1) p.2|} =
      {g | ∃ p ∈ F, Ccap * n < |sphereAvg g (s * p.1) p.2|} := by
    ext g
    constructor
    · rintro ⟨p, hp, hgp⟩
      exact ⟨p, Finset.mem_filter.mpr
        ⟨gridPairs_subset_finset hlam hκ hW hp, hp⟩, hgp⟩
    · rintro ⟨p, hp, hgp⟩
      exact ⟨p, hFgrid p hp, hgp⟩
  have ht := p4_cap_finite hd (by linarith : 0 < s₀) F hFpos hFvar
    (by norm_num : (0 : ℝ) ≤ 2)
    (s := s) (V := C₁ * n) (T := Ccap * n) (t := 2)
  rw [hevent]
  have hcardF : (F.card : ℝ) ≤ A * n * Real.exp (B * n) := by
    have hle : F.card ≤ (p4_gridPairsFinset d lam κ n W).card :=
      Finset.card_filter_le _ _
    exact (by exact_mod_cast hle : (F.card : ℝ) ≤
      (p4_gridPairsFinset d lam κ n W).card).trans (hcard hn hW hWlog)
  have hexp : -(2 : ℝ) * (Ccap * n) + (2 : ℝ) ^ 2 * (C₁ * n) / 2 = -(B + 2) * n := by
    dsimp [Ccap]
    ring
  have hnR : (n : ℝ) ≤ Real.exp n := by
    linarith [Real.add_one_le_exp (n : ℝ)]
  have hreal : (F.card : ℝ) *
      (2 * Real.exp (-(2 : ℝ) * (Ccap * n) + (2 : ℝ) ^ 2 * (C₁ * n) / 2)) ≤
      C * Real.exp (-(n : ℝ)) := by
    rw [hexp]
    calc
      (F.card : ℝ) * (2 * Real.exp (-(B + 2) * n)) ≤
          (A * n * Real.exp (B * n)) * (2 * Real.exp (-(B + 2) * n)) := by
            gcongr
      _ = C * (n : ℝ) * Real.exp (-(2 : ℝ) * n) := by
        dsimp [C]
        calc
          _ = 2 * A * n * (Real.exp (B * n) * Real.exp (-(B + 2) * n)) := by ring_nf
          _ = 2 * A * n * Real.exp (-(2 : ℝ) * n) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      _ ≤ C * Real.exp n * Real.exp (-(2 : ℝ) * n) := by gcongr
      _ = C * Real.exp (-(n : ℝ)) := by
        calc
          _ = C * (Real.exp n * Real.exp (-(2 : ℝ) * n)) := by ring_nf
          _ = C * Real.exp (-(n : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
  exact ht.trans (ENNReal.ofReal_le_ofReal hreal)

/-- Lemma 2.2(a,b): high-probability caps, followed by the physical scale
ratio bound on every capped inspected pair, uniformly through `ξ=0`. -/
theorem lemma22 {d : ℕ} (hd : 2 ≤ d) {lam κ c₀ s s₀ : ℝ}
    (hlam : 1 < lam) (hκ : 0 < κ) (hc₀ : 0 < c₀)
    (hs : 1 ≤ s) (hs10 : s ≤ 10) (hs₀ : 1 ≤ s₀) (hs₀10 : s₀ ≤ 10) :
    ∃ Ccap C c : ℝ, 0 < Ccap ∧ 0 < C ∧ 0 < c ∧
      ∀ {n : ℕ} {W : ℝ}, 1 ≤ n → 0 ≤ W → Real.log (1 + W) ≤ c₀ * n →
        pinLaw d s₀ {g | ∃ p ∈ gridPairs d lam κ n W,
          Ccap * n < |sphereAvg g (s * p.1) p.2|} ≤
          ENNReal.ofReal (C * Real.exp (-c * n)) ∧
        (∀ g : DistRd d, (∀ p ∈ gridPairs d lam κ n W,
            |sphereAvg g (s * p.1) p.2| ≤ Ccap * n) →
          ∀ ξ η : ℝ, 0 ≤ ξ → 0 ≤ η →
          ∀ p ∈ gridPairs d lam κ n W,
            |Real.log (scaleS d η s p.1 p.2 g / scaleS d ξ s p.1 p.2 g)| ≤
              (Real.sqrt (2 * d) + Ccap) * |η - ξ| * n) := by
  obtain ⟨Ccap, C, hCcap, hC, hcap⟩ := lemma22_cap hd hlam hκ hc₀ hs hs10 hs₀ hs₀10
  refine ⟨Ccap, C, 1, hCcap, hC, one_pos, ?_⟩
  intro n W hn hW hWlog
  constructor
  · simpa only [neg_one_mul] using hcap hn hW hWlog
  · intro g hg ξ η hξ hη p hp
    have hpgrid := hp
    obtain ⟨k, hk, hr, -, -, -⟩ := hp
    have hrpos : 0 < p.1 := by rw [hk]; exact Real.rpow_pos_of_pos (by linarith) _
    have hr1 : p.1 ≤ 1 := by
      rw [hk]
      exact Real.rpow_le_one_of_one_le_of_nonpos hlam.le (neg_nonpos.mpr (Nat.cast_nonneg k))
    have hlog : -Real.log p.1 ≤ n := by
      have h := Real.log_le_log (Real.exp_pos _) hr
      rw [Real.log_exp] at h
      linarith
    exact scale_ratio_cap hd g p.2 hξ hη hrpos hr1 hlog (hg p hpgrid)
      (by exact_mod_cast Nat.zero_le n) hCcap.le

end HigherDimLQGContinuity
