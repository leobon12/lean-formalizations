import HigherDimLQGMetric.Sec8b.Prop86Families

/-! Normalize the whole-space LGF once and transfer all finite class counts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

def s7b_normalizedField {Ω : Type} (h : Ω → DistRd d) :
    Ω → DistRd d :=
  fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)

theorem s7b_normalized_lgf
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d) :
    IsNormalizedLGF (s7b_normalizedField h) P := by
  have hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d := by
    change ∀ᵐ ω ∂P, ∃ a,
      Filter.Tendsto (sphereAvgSeq (h ω) 1 0) Filter.atTop (nhds a)
    exact hh.ae_exists_tendsto_sphereAvgSeq (by omega : 2 ≤ d)
      (by norm_num : (0 : ℝ) < 1) 0
  exact hh.isNormalizedLGF_normalize (by omega : 1 ≤ d) hconv

theorem s7b_all_candidate_counts_normalize_ae
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d) {ξ Q cs Cs R : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hR : 0 < R)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (x y : Rd d) :
    ∀ᵐ ω ∂P,
      ∀ j i : ℤ, ∀ colour : Fin d → ℤ, ∀ k : ℕ,
        let r := (64 : ℝ) ^ j
        let q := (2 : ℝ) ^ i
        let S := s7b_candidateFamily d T.J r R x y colour k
        (S.filter fun Z => h ω ∈
          FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z).card =
        (S.filter fun Z => (s7b_normalizedField h) ω ∈
          FavEventBorel D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z).card := by
  classical
  apply ae_all_iff.mpr; intro j
  apply ae_all_iff.mpr; intro i
  apply ae_all_iff.mpr; intro colour
  apply ae_all_iff.mpr; intro k
  dsimp only
  let r : ℝ := (64 : ℝ) ^ j
  let q : ℝ := (2 : ℝ) ^ i
  let S := s7b_candidateFamily d T.J r R x y colour k
  have hr : 0 < r := by dsimp [r]; positivity
  have hS : ∀ Z ∈ S,
      IsSec8LabeledSet d T.J r R x y colour Z :=
    fun Z hZ => (s7b_candidate_valid d T.J r R x y colour k hZ).1
  have hf : ∀ t < T.J, (∀ u, 0 ≤ T.f t u) ∧
      (∀ u, T.f t u ≤ T.Mf) :=
    fun t ht => ⟨(T.bumps t ht).2.2.2.1,
      (T.bumps t ht).2.2.2.2.2⟩
  filter_upwards [s7b_fav_count_ae_equiv P h hd hh hξ hQ hD hDt
    Cs q R r T.b hr T.N T.V T.openV T.closureV T.f T.Mf hf
    x y colour S hS,
    s7b_fav_count_normalize_ae P h hd hh hξ hQ hD hDt
    Cs q R r T.b hr hR T.N T.V T.openV T.closureV T.f T.Mf hf
    x y colour S hS] with ω hraw hnorm
  exact hraw.symm.trans hnorm

end HigherDimLQGMetric
