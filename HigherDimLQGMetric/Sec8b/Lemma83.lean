import HigherDimLQGMetric.Sec8b.StartDropFinite
import HigherDimLQGMetric.Sec8b.CollectorWindow
import HigherDimLQGMetric.Count.Pruning
import HigherDimLQGMetric.Sec8.Events

/-! Pruning a fixed labeled class using the geometric estimates (26) and (T4). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric MeasureTheory unitInterval
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The color separation implies pairwise disjoint radius-four trap balls. -/
theorem s7b_labeled_disjoint {J : ℕ} (hd : 1 ≤ d)
    {r R : ℝ} (hr : 0 < r) {x y : Rd d} {colour : Fin d → ℤ}
    {Z : Finset (Rd d × ℕ)}
    (hZ : IsSec8LabeledSet d J r R x y colour Z) :
    (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (ball q.1 (4 * r)) (ball q'.1 (4 * r))) := by
  intro q hq q' hq' hne
  apply Metric.ball_disjoint_ball
  have hdist := hZ.separated hd hr hq hq' hne
  rw [dist_eq_norm]
  nlinarith only [hdist, hr]

/-- The deterministic content of [S] Lemma 8.3 at a field realization on
which the weak-metric, Weyl, and selected-geodesic properties hold. -/
theorem lemma83 {ξ Q cs Cs q R r : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hq : 0 < q)
    (hR : 0 < R) (hr : 0 < r)
    (g : DistRd d) (x y : Rd d) (colour : Fin d → ℤ)
    (Z : Finset (Rd d × ℕ))
    (hZ : IsSec8LabeledSet d T.J r R x y colour Z)
    (hlen : (D g).IsLength) (htlen : (Dt g).IsLength)
    (hcomp : ∀ u v : Rd d,
      cs * (D g).1 (u, v) ≤ (Dt g).1 (u, v) ∧
      (Dt g).1 (u, v) ≤ Cs * (D g).1 (u, v))
    (hsel0 : IsConstSpeedGeod (D g) x y (sec8Sel x y (D g).1))
    (hweyl : ∀ Z' ⊆ Z,
      IsWeylOf ξ (-F_Z T.f r Z') (D g) (D (addFun g (-F_Z T.f r Z'))))
    (hsel : ∀ Z' ⊆ Z,
      IsConstSpeedGeod (D (addFun g (-F_Z T.f r Z'))) x y
        (sec8Sel x y (D (addFun g (-F_Z T.f r Z'))).1))
    (hC1 : sec8C1 D Dt ξ Q Cs q R x y g)
    (hC2 : sec8C2 D Dt ξ Q q R r T.J T.N Z g)
    (hC3 : sec8C3 D x y r Z g) :
    ∃ Z' ⊆ Z,
      T.g / (4 * T.H) * Z.card ≤ Z'.card ∧
      g ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z' := by
  classical
  let s : Rd d × ℕ → ℝ := fun site => sNorm ξ Q g r site.1
  let S := macroS ξ Q g R
  let Δ : Finset (Rd d × ℕ) → ℝ :=
    fun t => (D g).1 (x, y) - (D (addFun g (-F_Z T.f r t))).1 (x, y)
  let good : Finset (Rd d × ℕ) → Rd d × ℕ → Prop :=
    fun t site => Exc (sec8Sel x y (D (addFun g (-F_Z T.f r t))).1)
      (D g) (sec8Collector T.V r site.1) site.1 r (T.b * s site)
  have hJ : ∀ site ∈ Z, site.2 < T.J := by
    intro site hsite
    exact (hC2 site hsite).1
  have hdisj := s7b_labeled_disjoint (by omega : 1 ≤ d) hr hZ
  have hS : 0 < S := by dsimp [S, macroS]; positivity
  have hqS : 0 < q * S := mul_pos hq hS
  have hs : ∀ site ∈ Z, q * S ≤ s site ∧ s site ≤ 2 * (q * S) := by
    intro site hsite
    obtain ⟨_, _, hlo, hhi⟩ := hC2 site hsite
    exact ⟨hlo, by simpa only [mul_assoc] using hhi⟩
  have hspos : ∀ site ∈ Z, 0 < s site := by
    intro site hsite
    exact lt_of_lt_of_le hqS (hs site hsite).1
  have htrap : ∀ site ∈ Z,
      TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c'
        (D g) (Dt g) (s site) r site.1 site.2 := by
    intro site hsite
    exact T.traps (D g) (Dt g) hlen htlen hcomp (s site) r site.1 site.2
      (hspos site hsite) hr (hJ site hsite) (hC2 site hsite).2.1
  have hstart : T.g * ∑ site ∈ Z, s site ≤ Δ Z := by
    have haway : ∀ site ∈ Z,
        sec8Sel x y (D g).1 0 ∉ closedBall site.1 (4 * r) ∧
        sec8Sel x y (D g).1 1 ∉ closedBall site.1 (4 * r) := by
      intro site hsite
      obtain ⟨_, _, _, _, hx, hy, _⟩ := hZ.1 site hsite
      simpa only [hsel0.1, hsel0.2.1] using And.intro hx hy
    have hdrop := s7b_start_drop T hξ hr Z hJ hdisj (D g) (Dt g)
      (D (addFun g (-F_Z T.f r Z))) hlen (hweyl Z (Finset.Subset.refl Z))
      s hspos htrap x y (sec8Sel x y (D g).1) hsel0 haway hC3
    dsimp only [Δ]
    linarith only [hdrop]
  have hundo : ∀ t ⊆ Z, ∀ site ∈ t, ¬ good t site →
      Δ t - T.b * s site ≤ Δ (t.erase site) := by
    intro t htZ site hsite hbad
    have hsiteZ := htZ hsite
    have hJt : ∀ p ∈ t, p.2 < T.J := fun p hp => hJ p (htZ hp)
    have hdisjt : (t : Set (Rd d × ℕ)).Pairwise
        (fun p p' => Disjoint (ball p.1 (4 * r)) (ball p'.1 (4 * r))) :=
      fun p hp p' hp' hne => hdisj (htZ hp) (htZ hp') hne
    have heraseZ : t.erase site ⊆ Z :=
      (Finset.erase_subset _ _).trans htZ
    have hbad' : ¬ Exc (sec8Sel x y (D (addFun g (-F_Z T.f r t))).1)
        (D g) (sec8Collector T.V r site.1) site.1 r (T.b * s site) := hbad
    obtain ⟨_, _, _, _, hx, hy, _⟩ := hZ.1 site hsiteZ
    have hstep := s7b_undo_bad_site T (hspos site hsiteZ) hr hJt hdisjt hsite
      (D g) (Dt g) (D (addFun g (-F_Z T.f r t)))
      (D (addFun g (-F_Z T.f r (t.erase site))))
      (htrap site hsiteZ) (hweyl t htZ) (hweyl (t.erase site) heraseZ)
      x y (sec8Sel x y (D (addFun g (-F_Z T.f r t))).1)
      (hsel t htZ) (notMem_subset ball_subset_closedBall hx)
      (notMem_subset ball_subset_closedBall hy) hbad'
    dsimp only [Δ]
    linarith only [hstep]
  have hocc : ∀ t ⊆ Z, Δ t ≤ T.H * ∑ site ∈ t, s site := by
    intro t htZ
    have hJt : ∀ p ∈ t, p.2 < T.J := fun p hp => hJ p (htZ hp)
    have hst : ∀ p ∈ t, 0 ≤ s p := fun p hp => (hspos p (htZ hp)).le
    have hdisjt : (t : Set (Rd d × ℕ)).Pairwise
        (fun p p' => Disjoint (ball p.1 (4 * r)) (ball p'.1 (4 * r))) :=
      fun p hp p' hp' hne => hdisj (htZ hp) (htZ hp') hne
    let η := sec8Sel x y (D (addFun g (-F_Z T.f r t))).1
    have hη := hsel t htZ
    let P := s7b_realPath η
    have hP := s7b_constSpeed_isGeod (D (addFun g (-F_Z T.f r t))) x y η hη
    have hdrop := s7b_delta_le_of_traps T hξ r hr (D g) (Dt g)
      (D (addFun g (-F_Z T.f r t))) s t hJt hst hdisjt
      (fun p hp => htrap p (htZ hp)) (hweyl t htZ) x y P hP
      (by simpa only [P, s7b_realPath_zero] using hη.1)
      (by simpa only [P, s7b_realPath_one] using hη.2.1)
    exact hdrop
  have hg : 0 < T.g := by rw [T.constants.2.2.2.1]; exact T.constants.1
  have hprune := pruning Z s hqS hs hg
    T.constants.2.1.le T.constants.2.2.2.2.2.2
    (by
      have heq := T.constants.2.2.2.2.1
      rw [heq]
      exact mul_pos T.constants.1 (Real.exp_pos _))
    Δ good hstart hundo hocc
  obtain ⟨Z', hsub, hgood, hcard⟩ := hprune
  refine ⟨Z', hsub, hcard, ?_⟩
  change sec8C1 D Dt ξ Q Cs q R x y g ∧
    sec8C2 D Dt ξ Q q R r T.J T.N Z' g ∧
    sec8C3 D x y r Z' g ∧ sec8C4 D ξ Q T.b r T.V T.f x y Z' g
  exact ⟨hC1, (fun site hsite => hC2 site (hsub hsite)),
    (fun site hsite => hC3 site (hsub hsite)), hgood⟩

/-- Lemma 8.3 on the common almost-sure event for all subsets of one finite
labeled class. -/
theorem lemma83_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P)
    {ξ Q cs Cs q R r : ℝ}
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hq : 0 < q) (hR : 0 < R) (hr : 0 < r)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (x y : Rd d) (colour : Fin d → ℤ)
    (Z : Finset (Rd d × ℕ))
    (hZ : IsSec8LabeledSet d T.J r R x y colour Z) :
    ∀ᵐ ω ∂P,
      sec8C1 D Dt ξ Q Cs q R x y (h ω) →
      sec8C2 D Dt ξ Q q R r T.J T.N Z (h ω) →
      sec8C3 D x y r Z (h ω) →
      ∃ Z' ⊆ Z,
        T.g / (4 * T.H) * Z.card ≤ Z'.card ∧
        h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z' := by
  have hf : ∀ j < T.J, (∀ u, 0 ≤ T.f j u) ∧
      (∀ u, T.f j u ≤ T.Mf) :=
    fun j hj => ⟨(T.bumps j hj).2.2.2.1,
      (T.bumps j hj).2.2.2.2.2⟩
  have hJ : ∀ site ∈ Z, site.2 < T.J := by
    intro site hsite
    obtain ⟨_, _, _, _, _, _, hj⟩ := hZ.1 site hsite
    exact hj
  have hshift : ∀ᵐ ω ∂P,
      ∀ t ∈ Z.powerset,
        ∃ η : C(unitInterval, Rd d),
          IsConstSpeedGeod (D (addFun (h ω) (-F_Z T.f r t))) x y η := by
    refine (Filter.eventually_all_finset Z.powerset).2 ?_
    intro t ht
    exact lemma82_shifted_geod_exists P h hd hh hξ hQ hD hf r
      (fun site hsite => hJ site (Finset.mem_powerset.mp ht hsite)) x y
  filter_upwards [hD.length P h hh.isLGFPlusCont,
    hDt.length P h hh.isLGFPlusCont, hcomp,
    hD.weyl P h hh.isLGFPlusCont,
    lemma27_proper hd hξ hQ hD P h hh,
    hshift] with ω hlen htlen hcmp hweyl hproper hsh
  letI : ProperSpace (D (h ω)).Space := hproper
  have hsel0 : IsConstSpeedGeod (D (h ω)) x y (sec8Sel x y (D (h ω)).1) :=
    ((exists_measurable_geodSelector x y).choose_spec.2 _
      (sec8_exists_constSpeedGeod (D (h ω)) hlen x y)).1
  have hW : ∀ t ⊆ Z,
      IsWeylOf ξ (-F_Z T.f r t) (D (h ω))
        (D (addFun (h ω) (-F_Z T.f r t))) := by
    intro t _ u v
    exact (hweyl (-F_Z T.f r t) u v).symm
  have hsel : ∀ t ⊆ Z,
      IsConstSpeedGeod (D (addFun (h ω) (-F_Z T.f r t))) x y
        (sec8Sel x y (D (addFun (h ω) (-F_Z T.f r t))).1) := by
    intro t ht
    exact ((exists_measurable_geodSelector x y).choose_spec.2 _
      (hsh t (Finset.mem_powerset.mpr ht))).1
  intro hC1 hC2 hC3
  exact lemma83 T hd hξ hq hR hr (h ω) x y colour Z hZ hlen htlen
    hcmp hsel0 hW hsel hC1 hC2 hC3

end HigherDimLQGMetric
