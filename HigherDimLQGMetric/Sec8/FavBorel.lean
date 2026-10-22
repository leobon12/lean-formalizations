import HigherDimLQGMetric.Sec8.ExcursionEquiv
import HigherDimLQGMetric.Sec8.ConfigBorel

/-!
# Borel favorable events

The event is encoded by the chain formula and dense-time excursions. On the
almost-sure domain of length metrics and selected geodesics it has exactly the
four source conditions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric Topology unitInterval
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Borel encoding of (C4), with the path and threshold exactly as in (C4). -/
def sec8C4Borel (D : DistRd d → ContMetric d) (ξ Q b r : ℝ)
    (V : Set (Rd d)) (f : ℕ → C(Rd d, ℝ))
    (x y : Rd d) (Z : Finset (Rd d × ℕ)) (g : DistRd d) : Prop :=
  ∀ site ∈ Z,
    ExcBorel (sec8Sel x y (D (addFun g (-F_Z f r Z))).1)
      (D g) (sec8Collector V r site.1) site.1 r
      (b * sNorm ξ Q g r site.1)

theorem measurableSet_sec8C4Borel {D : DistRd d → ContMetric d}
    (hD : Measurable D) (ξ Q b r : ℝ) (hr : 0 < r)
    (V : Set (Rd d)) (hV : IsOpen V)
    (f : ℕ → C(Rd d, ℝ)) (x y : Rd d)
    (Z : Finset (Rd d × ℕ)) :
    MeasurableSet {g : DistRd d | sec8C4Borel D ξ Q b r V f x y Z g} := by
  let η : DistRd d → C(unitInterval, Rd d) :=
    fun g => sec8Sel x y (D (addFun g (-F_Z f r Z))).1
  have hη : Measurable η :=
    (measurable_sec8Sel x y).comp
      (measurable_subtype_coe.comp (hD.comp (measurable_addFun_left _)))
  have hsite (site : Rd d × ℕ) :
      MeasurableSet {g : DistRd d |
        ExcBorel (η g) (D g) (sec8Collector V r site.1) site.1 r
          (b * sNorm ξ Q g r site.1)} := by
    have hθ : Measurable fun g : DistRd d => b * sNorm ξ Q g r site.1 :=
      measurable_const.mul (measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (measurable_sphereAvg_left r site.1))))
    exact measurableSet_ExcBorel_comp hη hD hθ _
      (S6a.isOpen_collector hr.ne' site.1 hV) site.1 r
  have heq : {g : DistRd d | sec8C4Borel D ξ Q b r V f x y Z g} =
      ⋂ site : {site : Rd d × ℕ // site ∈ Z},
        {g | ExcBorel (η g) (D g) (sec8Collector V r site.1.1) site.1.1 r
          (b * sNorm ξ Q g r site.1.1)} := by
    ext g
    simp only [sec8C4Borel, mem_ofPred_eq, mem_iInter]
    constructor
    · intro hg site
      exact hg site.1 site.2
    · intro hg site hmem
      exact hg ⟨site, hmem⟩
  rw [heq]
  exact MeasurableSet.iInter fun site => hsite site.1

/-- The original and Borel (C4) conditions coincide whenever the selected
path has the stated endpoints and the base metric is a length metric. -/
theorem sec8C4Borel_iff_sec8C4 (D : DistRd d → ContMetric d)
    (ξ Q b r : ℝ) (hr : 0 < r) (V : Set (Rd d))
    (hV : IsOpen V) (hVA : closure V ⊆ ann (0 : Rd d) 1 3)
    (f : ℕ → C(Rd d, ℝ)) (x y : Rd d)
    (Z : Finset (Rd d × ℕ)) (g : DistRd d)
    (hD : (D g).IsLength)
    (hZ : ∀ site ∈ Z, x ∉ closedBall site.1 (4 * r) ∧
      y ∉ closedBall site.1 (4 * r))
    (hη0 : sec8Sel x y (D (addFun g (-F_Z f r Z))).1 0 = x)
    (hη1 : sec8Sel x y (D (addFun g (-F_Z f r Z))).1 1 = y) :
    sec8C4Borel D ξ Q b r V f x y Z g ↔ sec8C4 D ξ Q b r V f x y Z g := by
  unfold sec8C4Borel sec8C4
  constructor
  · intro h site hsite
    have hxy := hZ site hsite
    have h0 : sec8Sel x y (D (addFun g (-F_Z f r Z))).1 0 ∉
        ball site.1 (4 * r) := by
      rw [hη0]
      exact fun hm => hxy.1 (ball_subset_closedBall hm)
    have h1 : sec8Sel x y (D (addFun g (-F_Z f r Z))).1 1 ∉
        ball site.1 (4 * r) := by
      rw [hη1]
      exact fun hm => hxy.2 (ball_subset_closedBall hm)
    have hclose : closure (sec8Collector V r site.1) ⊆ ball site.1 (4 * r) :=
      (S6a.closure_collector_subset hr site.1 hVA).trans
        (S6a.ann_subset_ball hr site.1)
    exact (ExcBorel_iff_Exc _ _ _ _ _ _ h0 h1
      (S6a.isOpen_collector hr.ne' site.1 hV) hclose hD).mp (h site hsite)
  · intro h site hsite
    have hxy := hZ site hsite
    have h0 : sec8Sel x y (D (addFun g (-F_Z f r Z))).1 0 ∉
        ball site.1 (4 * r) := by
      rw [hη0]
      exact fun hm => hxy.1 (ball_subset_closedBall hm)
    have h1 : sec8Sel x y (D (addFun g (-F_Z f r Z))).1 1 ∉
        ball site.1 (4 * r) := by
      rw [hη1]
      exact fun hm => hxy.2 (ball_subset_closedBall hm)
    have hclose : closure (sec8Collector V r site.1) ⊆ ball site.1 (4 * r) :=
      (S6a.closure_collector_subset hr site.1 hVA).trans
        (S6a.ann_subset_ball hr site.1)
    exact (ExcBorel_iff_Exc _ _ _ _ _ _ h0 h1
      (S6a.isOpen_collector hr.ne' site.1 hV) hclose hD).mpr (h site hsite)

/-- The four favorable conditions with Borel extensions of the two internal
metric observables. -/
def FavEventBorel (D Dt : DistRd d → ContMetric d) (ξ Q Cstar q R r b : ℝ)
    (J : ℕ) (N : ℕ → Set (Config d)) (V : Set (Rd d))
    (f : ℕ → C(Rd d, ℝ)) (x y : Rd d)
    (Z : Finset (Rd d × ℕ)) : Set (DistRd d) :=
  {g | sec8C1 D Dt ξ Q Cstar q R x y g ∧
    sec8C2Borel D Dt ξ Q q R r J N Z g ∧
    sec8C3 D x y r Z g ∧ sec8C4Borel D ξ Q b r V f x y Z g}

theorem measurableSet_FavEventBorel {D Dt : DistRd d → ContMetric d}
    (hD : Measurable D) (hDt : Measurable Dt)
    (ξ Q Cstar q R r b : ℝ) (hr : 0 < r)
    (J : ℕ) (N : ℕ → Set (Config d))
    (hN : ∀ j < J, MeasurableSet (N j))
    (V : Set (Rd d)) (hV : IsOpen V)
    (f : ℕ → C(Rd d, ℝ)) (x y : Rd d)
    (Z : Finset (Rd d × ℕ)) :
    MeasurableSet (FavEventBorel D Dt ξ Q Cstar q R r b J N V f x y Z) := by
  change MeasurableSet {g : DistRd d |
    sec8C1 D Dt ξ Q Cstar q R x y g ∧
    sec8C2Borel D Dt ξ Q q R r J N Z g ∧
    sec8C3 D x y r Z g ∧ sec8C4Borel D ξ Q b r V f x y Z g}
  exact (measurableSet_sec8C1 hD hDt ξ Q Cstar q R x y).inter
    ((measurableSet_sec8C2Borel hD hDt ξ Q q R r J N hN Z).inter
      ((measurableSet_sec8C3 hD x y r Z).inter
        (measurableSet_sec8C4Borel hD ξ Q b r hr V hV f x y Z)))

/-- The Borel event agrees pointwise with the four source conditions on the
length-metric and selected-geodesic domain. -/
theorem FavEventBorel_iff_FavEvent
    (D Dt : DistRd d → ContMetric d) (ξ Q Cstar q R r b : ℝ)
    (hr : 0 < r) (J : ℕ) (N : ℕ → Set (Config d))
    (V : Set (Rd d)) (hV : IsOpen V)
    (hVA : closure V ⊆ ann (0 : Rd d) 1 3)
    (f : ℕ → C(Rd d, ℝ)) (x y : Rd d)
    (Z : Finset (Rd d × ℕ)) (g : DistRd d)
    (hD : (D g).IsLength) (hDt : (Dt g).IsLength)
    (hZ : ∀ site ∈ Z, x ∉ closedBall site.1 (4 * r) ∧
      y ∉ closedBall site.1 (4 * r))
    (hη0 : sec8Sel x y (D (addFun g (-F_Z f r Z))).1 0 = x)
    (hη1 : sec8Sel x y (D (addFun g (-F_Z f r Z))).1 1 = y) :
    g ∈ FavEventBorel D Dt ξ Q Cstar q R r b J N V f x y Z ↔
      g ∈ FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z := by
  simp only [FavEventBorel, FavEvent, mem_ofPred_eq,
    sec8C2Borel_iff (g := g) hD hDt,
    sec8C4Borel_iff_sec8C4 D ξ Q b r hr V hV hVA f x y Z g hD hZ hη0 hη1]

end HigherDimLQGMetric
