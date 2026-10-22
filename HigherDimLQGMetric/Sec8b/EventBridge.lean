import HigherDimLQGMetric.Sec8.AeFav
import HigherDimLQGMetric.Sec8.Const
import HigherDimLQGMetric.LGF.Normalized

/-! Finite-count versions of the Section 8 favorable-event equivalences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

open Classical in
/-- The Borel and geometric favorable counts agree almost surely on a finite class. -/
theorem s7b_fav_count_ae_equiv {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hd : 3 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (Cstar q R r b : ℝ) (hr : 0 < r)
    {J : ℕ} (N : ℕ → Set (Config d))
    (V : Set (Rd d)) (hV : IsOpen V)
    (hVA : closure V ⊆ ann (0 : Rd d) 1 3)
    (f : ℕ → C(Rd d, ℝ)) (Mf : ℝ)
    (hf : ∀ j < J, (∀ u, 0 ≤ f j u) ∧ (∀ u, f j u ≤ Mf))
    (x y : Rd d) (colour : Fin d → ℤ)
    (S : Finset (Finset (Rd d × ℕ)))
    (hS : ∀ Z ∈ S, IsSec8LabeledSet d J r R x y colour Z) :
    ∀ᵐ ω ∂P,
      (S.filter fun Z => h ω ∈
        FavEventBorel D Dt ξ Q Cstar q R r b J N V f x y Z).card =
      (S.filter fun Z => h ω ∈
        FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z).card := by
  have hpoint : ∀ᵐ ω ∂P, ∀ Z ∈ S,
      (h ω ∈ FavEventBorel D Dt ξ Q Cstar q R r b J N V f x y Z ↔
       h ω ∈ FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z) := by
    refine (Filter.eventually_all_finset S).2 fun Z hZ => ?_
    exact lemma82_favEvent_ae_equiv P h hd hh hξ hQ hD hDt
      Cstar q R r b hr N V hV hVA f Mf hf x y (hS Z hZ)
  filter_upwards [hpoint] with ω hω
  congr 1
  exact Finset.filter_congr (fun Z hZ => hω Z hZ)

open Classical in
/-- The geometric favorable count is invariant under an arbitrary common additive constant
on a finite class, almost surely. -/
theorem s7b_fav_count_addConst_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hd : 3 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (Cstar q R r b : ℝ) (hr : 0 < r) (hR : 0 < R)
    (J : ℕ) (N : ℕ → Set (Config d))
    (V : Set (Rd d)) (f : ℕ → C(Rd d, ℝ)) (Mf : ℝ)
    (hf : ∀ j < J, (∀ u, 0 ≤ f j u) ∧ (∀ u, f j u ≤ Mf))
    (x y : Rd d) (S : Finset (Finset (Rd d × ℕ)))
    (hS : ∀ Z ∈ S, ∀ site ∈ Z, site.2 < J) :
    ∀ᵐ ω ∂P, ∀ c : ℝ,
      (S.filter fun Z => h ω ∈
        FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z).card =
      (S.filter fun Z => addConst (h ω) c ∈
        FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z).card := by
  have hpoint : ∀ᵐ ω ∂P, ∀ Z ∈ S, ∀ c : ℝ,
      (h ω ∈ FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z ↔
       addConst (h ω) c ∈ FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z) := by
    refine (Filter.eventually_all_finset S).2 fun Z hZ => ?_
    exact lemma82_favEvent_addConst_ae P h hd hh hξ hQ hD hDt
      Cstar q R r b hr hR J N V f Mf hf x y Z (hS Z hZ)
  filter_upwards [hpoint] with ω hω
  intro c
  congr 1
  exact Finset.filter_congr (fun Z hZ => hω Z hZ c)

open Classical in
/-- The Borel favorable count is unchanged by normalizing a whole-space LGF. -/
theorem s7b_fav_count_normalize_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hd : 3 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (Cstar q R r b : ℝ) (hr : 0 < r) (hR : 0 < R)
    {J : ℕ} (N : ℕ → Set (Config d))
    (V : Set (Rd d)) (hV : IsOpen V)
    (hVA : closure V ⊆ ann (0 : Rd d) 1 3)
    (f : ℕ → C(Rd d, ℝ)) (Mf : ℝ)
    (hf : ∀ j < J, (∀ u, 0 ≤ f j u) ∧ (∀ u, f j u ≤ Mf))
    (x y : Rd d) (colour : Fin d → ℤ)
    (S : Finset (Finset (Rd d × ℕ)))
    (hS : ∀ Z ∈ S, IsSec8LabeledSet d J r R x y colour Z) :
    ∀ᵐ ω ∂P,
      (S.filter fun Z => h ω ∈
        FavEventBorel D Dt ξ Q Cstar q R r b J N V f x y Z).card =
      (S.filter fun Z => addConst (h ω) (-sphereAvg (h ω) 1 0) ∈
        FavEventBorel D Dt ξ Q Cstar q R r b J N V f x y Z).card := by
  let hn : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  have hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d := by
    change ∀ᵐ ω ∂P, ∃ a, Filter.Tendsto (sphereAvgSeq (h ω) 1 0)
      Filter.atTop (nhds a)
    exact hh.ae_exists_tendsto_sphereAvgSeq (by omega : 2 ≤ d)
      (by norm_num : (0 : ℝ) < 1) 0
  have hhn : IsNormalizedLGF hn P := hh.isNormalizedLGF_normalize (by omega) hconv
  have hJ : ∀ Z ∈ S, ∀ site ∈ Z, site.2 < J := by
    intro Z hZ site hsite
    obtain ⟨_, _, _, _, _, _, hj⟩ := (hS Z hZ).1 site hsite
    exact hj
  filter_upwards [s7b_fav_count_ae_equiv P h hd hh hξ hQ hD hDt
      Cstar q R r b hr N V hV hVA f Mf hf x y colour S hS,
    s7b_fav_count_addConst_ae P h hd hh hξ hQ hD hDt
      Cstar q R r b hr hR J N V f Mf hf x y S hJ,
    s7b_fav_count_ae_equiv P hn hd hhn.1 hξ hQ hD hDt
      Cstar q R r b hr N V hV hVA f Mf hf x y colour S hS]
    with ω hraw hconst hnorm
  exact hraw.trans ((hconst (-sphereAvg (h ω) 1 0)).trans hnorm.symm)

end HigherDimLQGMetric
