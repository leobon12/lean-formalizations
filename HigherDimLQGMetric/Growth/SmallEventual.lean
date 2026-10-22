import HigherDimLQGMetric.Growth.GridSum

/-!
# Almost-sure grid bounds at small radii

Packet L2a. Union over the finite Osc grid at each dyadic level, then Borel--Cantelli.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistRd d}

/-- On almost every sample, all sufficiently fine spatial grid points and their
adjacent scale-space blocks obey linear bounds in the dyadic level. -/
theorem l2a_ae_eventually_small_grid (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ Ap Ab : ℝ, 0 < Ap ∧ 0 < Ab ∧
      ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
        ∀ g ∈ HigherDimLFPP.Osc.grid 0 R (l2a_smallScale k),
          |sphereAvg (h ω) (l2a_smallScale k) g - sphereAvg (h ω) 1 0| ≤
            Ap * ((k : ℝ) + 1) ∧
          ∀ p : l2a_largeBlock (Real.sqrt (d : ℝ)),
            |sphereAvg (h ω) (l2a_smallScale k * p.1.1)
              (l2a_smallScale k • p.1.2 + g) -
              sphereAvg (h ω) (l2a_smallScale k) g| ≤
              Ab * ((k : ℝ) + 1) := by
  obtain ⟨Ap, Ab, C, hAp, hAb, hC, htail⟩ := l2a_exists_small_grid_tails hd hR
  have := hh.gaussian.isProbabilityMeasure
  let G (k : ℕ) : Finset (Rd d) := HigherDimLFPP.Osc.grid 0 R (l2a_smallScale k)
  let Ep (k : ℕ) (g : Rd d) : Set Ω := {ω | Ap * ((k : ℝ) + 1) ≤
    |sphereAvg (h ω) (l2a_smallScale k) g - sphereAvg (h ω) 1 0|}
  let Eb (k : ℕ) (g : Rd d) : Set Ω := {ω | Ab * ((k : ℝ) + 1) ≤
    ⨆ p : l2a_largeBlock (Real.sqrt (d : ℝ)),
      |sphereAvg (h ω) (l2a_smallScale k * p.1.1)
        (l2a_smallScale k • p.1.2 + g) -
        sphereAvg (h ω) (l2a_smallScale k) g|}
  let E (k : ℕ) : Set Ω := ⋃ g ∈ G k, Ep k g ∪ Eb k g
  have hE : ∀ k, P.real (E k) ≤
      (2 + C) * ((G k).card : ℝ) *
        Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1)) := by
    intro k
    have hEach : ∀ g ∈ G k, P.real (Ep k g ∪ Eb k g) ≤
        (2 + C) * Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1)) := by
      intro g hg
      obtain ⟨hp, hb⟩ := htail hh k g hg
      have hU := measureReal_union_le (μ := P) (Ep k g) (Eb k g)
      dsimp [Ep, Eb] at hU
      linarith only [hU, hp, hb]
    calc P.real (E k)
        ≤ ∑ g ∈ G k, P.real (Ep k g ∪ Eb k g) := by
          exact measureReal_biUnion_finset_le (G k) (fun g => Ep k g ∪ Eb k g)
      _ ≤ ∑ _g ∈ G k,
          (2 + C) * Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1)) :=
        Finset.sum_le_sum fun g hg => hEach g hg
      _ = (2 + C) * ((G k).card : ℝ) *
          Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hs : Summable fun k : ℕ =>
      (2 + C) * ((G k).card : ℝ) *
        Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1)) := by
    have hgs := (l2a_summable_grid_tail (d := d) hR).mul_left (2 + C)
    simpa only [G, mul_assoc] using hgs
  have hBC : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ E k :=
    l2a_ae_eventually_of_summable_bound
      (fun k => by positivity) hs hE
  refine ⟨Ap, Ab, hAp, hAb, ?_⟩
  filter_upwards [hBC, hh.ae_continuousOn_sphereAvg hd] with ω hBC hcont
  filter_upwards [hBC] with k hk g hg
  have hnot : ω ∉ Ep k g ∪ Eb k g := by
    intro hx
    exact hk (mem_iUnion₂.2 ⟨g, hg, hx⟩)
  have hp : ¬ Ap * ((k : ℝ) + 1) ≤
      |sphereAvg (h ω) (l2a_smallScale k) g - sphereAvg (h ω) 1 0| := by
    change ω ∉ Ep k g
    exact fun hx => hnot (Or.inl hx)
  have hb : ¬ Ab * ((k : ℝ) + 1) ≤
      ⨆ p : l2a_largeBlock (Real.sqrt (d : ℝ)),
        |sphereAvg (h ω) (l2a_smallScale k * p.1.1)
          (l2a_smallScale k • p.1.2 + g) -
          sphereAvg (h ω) (l2a_smallScale k) g| := by
    change ω ∉ Eb k g
    exact fun hx => hnot (Or.inr hx)
  refine ⟨(lt_of_not_ge hp).le, fun p => ?_⟩
  exact l2a_block_point_le_of_sup_lt (h ω) hcont.2
    (l2a_isCompact_largeBlock (Real.sqrt (d : ℝ)))
    (l2a_largeBlock_pos (Real.sqrt (d : ℝ)))
    (l2a_smallScale_pos k) g hb p

end HigherDimLQGMetric
