import HigherDimLQGMetric.ShellDec.Tail
import HigherDimLQGMetric.ShellDec.Bridge

/-!
# Shell independence for the recentred LGF

The paper's shell-independence lemma is an adapter from the host library's
Gaussian shell-decoupling theorem to events measurable from a recentred
restriction on an open annulus.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLFPPAS

/-- The number of successful events among the first `n`, expressed as the
finite sum of their indicator functions. -/
noncomputable def shellSuccessCount {Ω : Type*} (E : ℕ → Set Ω)
    (n : ℕ) (ω : Ω) : ℝ := by
  classical
  exact ∑ i ∈ Finset.range n, if ω ∈ E i then (1 : ℝ) else 0

/-- Paper Lemma 2.6: among exponentially shrinking annuli, a linearly large
fraction of high-probability events occur, except with exponentially small
probability. Events are measurable from the restriction of the LGF after
subtracting its sphere average. -/
theorem lemma26_shell_independence {d : ℕ} (hd : 2 ≤ d)
    (q qPrime : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hqPrime : 1 < qPrime) :
    ∀ A₀ b₀ : ℝ, 0 < A₀ → 0 < b₀ → b₀ < 1 →
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → HigherDimLQGMetric.DistRd d),
        HigherDimLQGMetric.IsNormalizedLGF h P →
        ∀ (z : Rd d) (r : ℕ → ℝ), (∀ i, 0 < r i) →
          (∀ i, r (i + 1) ≤ q * r i) →
          ∀ E : ℕ → Set Ω,
            (∀ i, MeasurableSet[
              HigherDimLQGMetric.fieldSigmaRd
                (fun ω => HigherDimLQGMetric.addConst (h ω)
                  (-HigherDimLQGMetric.sphereAvg (h ω) (r i) z))
                (HigherDimLQGMetric.shellOpen z (qPrime⁻¹ * r i)
                  (qPrime * r i))] (E i)) →
            (∀ i, ENNReal.ofReal p ≤ P (E i)) →
            ∀ n : ℕ,
              P {ω | shellSuccessCount E n ω < b₀ * n} ≤
      ENNReal.ofReal (Real.exp (-A₀ * n)) := by
  classical
  intro A₀ b₀ hA₀ hb₀ hb₀1
  let a : ℝ := qPrime⁻¹
  have hqPrime0 : 0 < qPrime := lt_trans zero_lt_one hqPrime
  have ha0 : 0 < a := by
    dsimp [a]
    exact inv_pos.mpr hqPrime0
  have ha1 : a < 1 := by
    dsimp [a]
    rw [inv_lt_one₀ hqPrime0]
    exact hqPrime
  obtain ⟨p₀, hp₀, hA1⟩ := HigherDimLQGMetric.lemmaA1
    (show 1 ≤ d by omega) a qPrime q ha0 ha1 hqPrime hq0 hq1
    A₀ b₀ hA₀ hb₀ hb₀1
  let p : ℝ := max p₀ 0
  have hp0 : 0 ≤ p := le_max_right p₀ 0
  have hp1 : p < 1 := by
    dsimp [p]
    exact max_lt hp₀ (by norm_num)
  refine ⟨p, hp0, hp1, ?_⟩
  intro Ω mΩ P hP h hh z r hr hstep E hE hprob n
  have hE₀ : ∀ i, HigherDimLQGMetric.AEEventIn P
      (HigherDimLQGMetric.fieldSigma0 h
        (HigherDimLQGMetric.ann z (a * r i) (qPrime * r i))) (E i) := by
    intro i
    have hdet := HigherDimLQGMetric.shellBridge_aeDeterminedSigma hd hh.1 z
      ha1 hqPrime (hr i)
    exact hdet (E i) (hE i)
  have hprob₀ : ∀ i, ENNReal.ofReal p₀ ≤ P (E i) := by
    intro i
    exact (ENNReal.ofReal_le_ofReal (le_max_left p₀ 0)).trans (hprob i)
  have hbound := hA1 P h hh.1 z r hr hstep E hE₀ hprob₀ n
  have hcount (ω : Ω) : shellSuccessCount E n ω =
        (((Finset.range n).filter (fun i => ω ∈ E i)).card : ℝ) := by
    simp [shellSuccessCount, Finset.sum_boole]
  have hset :
      {ω | shellSuccessCount E n ω < b₀ * n} =
        {ω | (((Finset.range n).filter (fun i => ω ∈ E i)).card : ℝ) < b₀ * n} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [hcount ω]
  rw [hset]
  exact hbound

end HigherDimLFPPAS
