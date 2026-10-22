import HigherDimLQGMetric.Growth.BlockContinuity

/-!
# Almost-sure large-radius dyadic growth

Packet L2a, Lemma 2.14. Borel--Cantelli combines the point and block tails.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistRd d}

/-- A normalized LGF obeys the square-root-logarithm bound on all sufficiently large
dyadic blocks. This is the Borel--Cantelli core of Lemma 2.14. -/
theorem l2a_ae_eventually_large_dyadic (hd : 2 ≤ d) (hh : IsNormalizedLGF h P)
    (R : ℝ) :
    ∃ c C M : ℝ, 0 < c ∧ 0 < C ∧ 0 < M ∧
      ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
        ∀ r : ℝ, (2 : ℝ) ^ k / 2 ≤ r → r ≤ (2 : ℝ) ^ k →
          ∀ z ∈ closedBall (0 : Rd d) R,
            |sphereAvg (h ω) r z| ≤
              Real.sqrt (4 * M * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) +
                Real.sqrt ((2 / c) * Real.log ((k : ℝ) + 1)) := by
  obtain ⟨c, C, hc, hC, hblock⟩ := l2a_exists_large_block_tail hd R
  obtain ⟨M, hM, hpoint⟩ := l2a_exists_large_point_tail hd
  have := hh.1.gaussian.isProbabilityMeasure
  let blockLevel (k : ℕ) : ℝ := Real.sqrt ((2 / c) * Real.log ((k : ℝ) + 1))
  let pointLevel (k : ℕ) : ℝ :=
    Real.sqrt (4 * M * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1))
  let Eb (k : ℕ) : Set Ω := {ω | blockLevel k ≤ ⨆ p : l2a_largeBlock R,
      |sphereAvg (h ω) ((2 : ℝ) ^ k * p.1.1) (((2 : ℝ) ^ k) • p.1.2) -
        sphereAvg (h ω) ((2 : ℝ) ^ k) 0|}
  let Ep (k : ℕ) : Set Ω := {ω | pointLevel k ≤
    |sphereAvg (h ω) ((2 : ℝ) ^ k) 0 - sphereAvg (h ω) 1 0|}
  have hb : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ Eb k :=
    l2a_ae_eventually_of_le_inv_sq hC.le (fun k => hblock hh.1 k)
  have hp : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ Ep k :=
    l2a_ae_eventually_of_le_inv_sq (by norm_num : (0 : ℝ) ≤ 2) (fun k => hpoint hh.1 k)
  refine ⟨c, C, M, hc, hC, hM, ?_⟩
  filter_upwards [hb, hp, hh.1.ae_continuousOn_sphereAvg hd, hh.2] with ω hb hp hcont hn
  filter_upwards [hb, hp] with k hbk hpk r hrlo hrhi z hz
  have ha : 0 < (2 : ℝ) ^ k := by positivity
  have ha1 : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  obtain ⟨hmem, hrad, hspace⟩ := l2a_large_cell ha ha1 hrlo hrhi hz
  let p : l2a_largeBlock R := ⟨(r / (2 : ℝ) ^ k, ((2 : ℝ) ^ k)⁻¹ • z), hmem⟩
  have hbk' : ¬ blockLevel k ≤ ⨆ p : l2a_largeBlock R,
      |sphereAvg (h ω) ((2 : ℝ) ^ k * p.1.1) (((2 : ℝ) ^ k) • p.1.2 + 0) -
        sphereAvg (h ω) ((2 : ℝ) ^ k) 0| := by
    simpa only [Eb, mem_ofPred_eq, add_zero] using hbk
  have hbnd := l2a_block_point_le_of_sup_lt (h ω) hcont.2
    (l2a_isCompact_largeBlock R) (l2a_largeBlock_pos R) ha (0 : Rd d) hbk' p
  simp only [p, hrad, hspace, add_zero] at hbnd
  have hpnd : |sphereAvg (h ω) ((2 : ℝ) ^ k) 0| ≤ pointLevel k := by
    have hpk' : ¬ pointLevel k ≤
        |sphereAvg (h ω) ((2 : ℝ) ^ k) 0 - sphereAvg (h ω) 1 0| := by
      simpa only [Ep, mem_ofPred_eq] using hpk
    rw [hn, sub_zero] at hpk'
    exact (lt_of_not_ge hpk').le
  have htri : |sphereAvg (h ω) r z| ≤
      |sphereAvg (h ω) r z - sphereAvg (h ω) ((2 : ℝ) ^ k) 0| +
        |sphereAvg (h ω) ((2 : ℝ) ^ k) 0| := by
    have := abs_add_le (sphereAvg (h ω) r z - sphereAvg (h ω) ((2 : ℝ) ^ k) 0)
      (sphereAvg (h ω) ((2 : ℝ) ^ k) 0)
    simpa only [sub_add_cancel] using this
  dsimp [blockLevel, pointLevel] at hbnd hpnd
  linarith only [htri, hbnd, hpnd]

end HigherDimLQGMetric
