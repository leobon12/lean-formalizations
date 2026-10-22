import HigherDimLQGMetric.Sec8b.Prop86FixedRate
import HigherDimLQGMetric.Sec9.Interfaces

/-! Proposition 8.6 and its closed interface statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory Set
open HigherDimLFPP (Rd)

theorem prop86 (d : ℕ) (hd : 3 ≤ d) {ξ Q : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {cs Cs : ℝ} (hcs : 0 < cs) (hcsCs : cs ≤ Cs)
    (hcomp : ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ᵐ ω ∂P, ∀ u v : Rd d,
          cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
          (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt) {B : ℝ} (hB : 0 < B) :
    Prop86Shape d ξ Q D Dt cs Cs T B := by
  intro η hη hη1 N hN
  by_cases hJ : 0 < T.J
  · obtain ⟨hκpos, _⟩ := s7b_pruning_fraction_bounds T hξ hJ
    obtain ⟨pH, hpH, k, hk, he⟩ :=
      s7b_rate_parameters d (by omega : 1 ≤ d) hκpos hN
    obtain ⟨M0, hM0, hcm⟩ := s7b_exists_cm_uniform
      (by omega : 1 ≤ d) T.f
      (fun label hlabel => ⟨(T.bumps label hlabel).1,
        (T.bumps label hlabel).2.1⟩)
    obtain ⟨εs, hεs, hsample⟩ :=
      s7b_exists_sampling_threshold d (B := B) hη
    obtain ⟨εk, hεk, hkthreshold⟩ := s7b_exists_k_threshold k
    let ε₁ : ℝ := min εs (min εk (1 / 3))
    let C : ℝ := s7b_classConst d B *
      s7b_oneClassConst d T.J k Cs T.H T.c' T.c T.g M0 pH
    have hε₁ : 0 < ε₁ := by dsimp [ε₁]; positivity
    refine ⟨C, ε₁, hε₁, ?_⟩
    intro Ω _ P _ h hh R hR x y hx hy hxy ε hε hεlt
    have hεs' : ε < εs := lt_of_lt_of_le hεlt (min_le_left _ _)
    have hεk' : ε < εk :=
      lt_of_lt_of_le hεlt ((min_le_right _ _).trans (min_le_left _ _))
    have hεthird : ε ≤ 1 / 3 :=
      (le_of_lt hεlt).trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hεη, hεhalf, hclass⟩ :=
      hsample hε hεs' hR hB.le
    have hkup := hkthreshold hε hεk'
    exact s7b_prop86_fixed_rate P h hh hd hξ hQ hcs hcsCs
      hB hη hη1 hε hεη hεhalf hεthird hR hclass
      hD hDt hcomp T x y hx hy hxy k hk hkup
      hM0 hcm hpH he
  · refine ⟨0, 1, by norm_num, ?_⟩
    intro Ω _ P _ h hh R hR x y hx hy hxy ε hε hε1
    have hempty :
        {ω | h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
          sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y (h ω)} = ∅ := by
      apply Set.eq_empty_of_subset_empty
      intro ω hω
      exact (hJ (s7b_cover_implies_Jpos hR (h ω) hω.1.1)).elim
    simp only [hempty, measure_empty, zero_mul, ENNReal.ofReal_zero,
      le_refl]

theorem prop86Stmt : Prop86Stmt := by
  intro d hd ξ Q hξ hQ D Dt hD hDt cs Cs hcs hcsCs hcomp T B hB
  exact prop86 d hd hξ hQ hD hDt hcs hcsCs hcomp T hB

end HigherDimLQGMetric
