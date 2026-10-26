import SupercriticalConformalCovariance.BiLip.L51.Shield
import SupercriticalConformalCovariance.Root.Forward
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.SaturationE

/-!
# Lemma 5.1: deterministic saturation of the literal good event

`good_transfer`: let `D₁, D₂` be two length-space source samples with the barrier, finite middle-to-boundary
distance, and equal internal metrics on an open `U ⊇ cl A_{r/2,2r}(z)`. Let `e₁, e₂` be any two target
functions that agree on pairs of points of `cl A_{r/2,2r}(z)`. Then the literal `SupercriticalConformalCovariance.Improve.Good` (G1–G5,
paper l. 386–410) transfers from `(D₁, e₁)` to `(D₂, e₂)`, for the same circle-average value `c` and
shield coefficient `k ≤ 1/2`.

Every clause is a function of the internal data on `U`:
* G1, G4: small-annulus `around`/`across` (S36 `around_transfer`, `across_transfer`);
* G2, (9): `around` plus the internal barrier `S` of the carrier;
* G3: internal boundary geodesics (`ibg_transfer`);
* G5: on (9) the source shield (S36 `shield_internal_eq` applied with `e := d`, `C₋ = C₊ = 1`, using
  `k ≤ 1/2` and `S = d(M, ∂A)`) makes `D(u, v)` the internal distance of `A_{r/2,2r}(z)`. Then the regular-pair
  tests transfer (geodesic via `curve_len_transfer_eq`, endpoint costs via `pointSphere_transfer` and
  `around_transfer`), and the conclusion uses `e₁ = e₂` on carrier pairs.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip.L51

open SupercriticalLQGUniqueness (LSCMetric EuclideanAnnulus aroundDist acrossDist)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events (eventCarrier eventMiddle eventBoundary
  eventOpen InternalBoundaryGeodesic pointSphereDist)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36 (intExt around_transfer across_transfer
  ibg_transfer pointSphere_transfer middle_transfer intExt_transfer internal_transfer
  curve_len_transfer_eq small_annulus_subset small_across_subset closedBall_point_subset
  sphere_subset_middle outerAnn shortAnn E4Prop toSet_subset_shell shortCarrier_subset_carrier
  eventOpen_subset_carrier' shield_internal_eq)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated (aroundRat aroundAt)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist Geodesic)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (Barrier)

/-- the sample properties used for a source metric -/
def SrcOK (D : LSCMetric) (z : ℂ) (r : ℝ) : Prop :=
  Barrier D ∧ D.IsLengthSpace ∧ setDist D (eventMiddle z r) (eventBoundary z r) < ⊤

theorem SrcOK.curve_cont {D : LSCMetric} {z : ℂ} {r : ℝ} (h : SrcOK D z r) :
    ∀ (γ : ℝ → ℂ) (a b : ℝ), D.IsCurve γ a b → ContinuousOn γ (Icc a b) := fun _ _ _ hγ =>
  SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.continuousOn_of_barrier_of_length _
    h.1 h.2.1 hγ

/-- the internal barrier transfers -/
theorem barrier_transfer {D₁ D₂ : LSCMetric} {U : Set ℂ} {z : ℂ} {r : Ioi (0 : ℝ)}
    (hYU : eventCarrier z r ⊆ U) (hId : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) :
    SupercriticalConformalCovariance.GoodAnnulus.barrier D₁ z r = SupercriticalConformalCovariance.GoodAnnulus.barrier D₂ z r := by
  unfold SupercriticalConformalCovariance.GoodAnnulus.barrier LSCMetric.internalSetDist
  rw [internal_transfer hYU hId]

theorem pointSphereDist_eq_setDist (D : LSCMetric) (x : ℂ) (ρ : ℝ) :
    pointSphereDist D x ρ = setDist D {x} (sphere x ρ) := by
  unfold pointSphereDist SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.spherePairInf setDist
  rw [sphere_zero]

section Geometry

variable {z : ℂ} {r : ℝ}

/-- the annulus `A_{δr, √δ r}(x)` -/
def annAt (x : ℂ) (ρ σ : ℝ) (h : 0 < ρ ∧ ρ < σ) : EuclideanAnnulus := ⟨(x, (ρ, σ)), h⟩

/-- small annuli around points of the middle region lie in the carrier -/
theorem small_ann_toSet_subset {x : ℂ} (hr : 0 < r) (hx : x ∈ eventMiddle z r) {δ : ℝ}
    (hδ0 : 0 < δ) (hδq : δ < 1 / 100) (h : 0 < δ * r ∧ δ * r < Real.sqrt δ * r) :
    (annAt x (δ * r) (Real.sqrt δ * r) h).toSet ⊆ eventCarrier z r := by
  refine small_annulus_subset (A := annAt x (δ * r) (Real.sqrt δ * r) h) hr hx rfl ?_
  have := sqrt_mul_lt_tenth hr hδ0 hδq
  change Real.sqrt δ * r ≤ r / 5
  linarith

theorem aroundRat_eq_annAt (D : LSCMetric) (x : ℂ) (ρ σ : ℝ) (h : 0 < ρ ∧ ρ < σ) :
    aroundRat (D, (x, ρ, σ)) = aroundDist D (annAt x ρ σ h) :=
  (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.aroundDist_eq_aroundRat D
    (annAt x ρ σ h)).symm

end Geometry

/-- **Transfer of the literal good event** under equal internal data. -/
theorem good_transfer {D₁ D₂ : LSCMetric} {e₁ e₂ : ℂ × ℂ → ℝ≥0∞} {ξ Q : ℝ} {z : ℂ}
    {r : Ioi (0 : ℝ)} {q : Ioo (0 : ℝ) (1 / 100)} {a : Ioo (1 - (q : ℝ)) 1} {K : Ioi (1 : ℝ)}
    {θ : Ioi (0 : ℝ)} {k c η : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 2)
    (h₁ : SrcOK D₁ z r) (h₂ : SrcOK D₂ z r) {U : Set ℂ} (hYU : eventCarrier z r ⊆ U)
    (hId : ∀ x y, intExt D₁ U x y = intExt D₂ U x y)
    (he : ∀ x ∈ eventCarrier z r, ∀ y ∈ eventCarrier z r, e₁ (x, y) = e₂ (x, y))
    (hG : SupercriticalConformalCovariance.Improve.Good D₁ e₁ ξ Q z r q a K θ k c η) :
    SupercriticalConformalCovariance.Improve.Good D₂ e₂ ξ Q z r q a K θ k c η := by
  have hr : (0 : ℝ) < r := r.2
  have hq0 : (0 : ℝ) < q := q.2.1
  have hq1 : (q : ℝ) < 1 / 100 := q.2.2
  have ha1 : (a : ℝ) < 1 := a.2.2
  have haq : 1 - (q : ℝ) < a := a.2.1
  have hId' : ∀ x y, intExt D₂ U x y = intExt D₁ U x y := fun x y => (hId x y).symm
  have hbar := barrier_transfer (r := r) hYU hId
  obtain ⟨⟨g1, g2, g3, g4⟩, g5⟩ := hG
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- G1
    intro P s t hibg n hn x hx hhit
    obtain ⟨A, hc, hi, ho, hAle⟩ := g1 P s t (ibg_transfer hYU hId' hibg) n hn x hx hhit
    refine ⟨A, hc, hi, ho, ?_⟩
    have hδ0 : (0 : ℝ) < (1 / 2) ^ n := pow_pos (by norm_num) n
    have hsqδ : Real.sqrt ((1 / 2 : ℝ) ^ n) ≤ Real.sqrt q := Real.sqrt_le_sqrt hn
    have hsq := sqrt_mul_lt_tenth hr hq0 hq1
    have hoR : A.outerRadius ≤ (r : ℝ) / 5 := by rw [ho]; nlinarith
    have hoR' : A.outerRadius < (r : ℝ) / 5 := by rw [ho]; nlinarith
    rw [← around_transfer hId ((small_annulus_subset hr hx hc hoR).trans hYU),
      ← across_transfer h₁.1 h₂.1 h₁.2.1 h₂.2.1 hId hoR'
        ((small_across_subset hr hx hc).trans hYU)]
    exact hAle
  · -- G2
    have hout : (outerAnn z r).toSet ⊆ U := by
      refine (toSet_subset_shell _).trans (fun y hy => hYU ?_)
      obtain ⟨hy1, hy2⟩ := hy
      change 3 * (r : ℝ) / 2 ≤ dist y z at hy1
      change dist y z < 2 * (r : ℝ) at hy2
      refine ⟨mem_closedBall.mpr hy2.le, ?_⟩
      rw [mem_ball, not_lt]
      linarith
    unfold SupercriticalConformalCovariance.GoodAnnulus.G2 at g2 ⊢
    rw [← around_transfer hId hout, ← hbar]
    exact g2
  · -- G3
    intro P σ τ hP s t hs hσs htτ hseg
    exact g3 P σ τ (ibg_transfer hYU hId' hP) s t hs hσs htτ hseg
  · -- G4
    have hsh : (shortAnn z r a).toSet ⊆ U := by
      refine (toSet_subset_shell _).trans (fun y hy => hYU ?_)
      obtain ⟨hy1, hy2⟩ := hy
      change (a : ℝ) * r ≤ dist y z at hy1
      change dist y z < (r : ℝ) at hy2
      refine ⟨mem_closedBall.mpr (by linarith), ?_⟩
      rw [mem_ball, not_lt]
      nlinarith
    have hR : (shortAnn z r a).outerRadius < 3 * (r : ℝ) / 2 := by
      change (r : ℝ) < 3 * (r : ℝ) / 2
      linarith
    have hsub : {y : ℂ | (shortAnn z r a).innerRadius < ‖y - (shortAnn z r a).center‖ ∧
        ‖y - (shortAnn z r a).center‖ < 3 * (r : ℝ) / 2} ⊆ U := by
      intro y hy
      apply hYU
      obtain ⟨hy1, hy2⟩ := hy
      change (a : ℝ) * r < ‖y - z‖ at hy1
      change ‖y - z‖ < 3 * (r : ℝ) / 2 at hy2
      rw [← dist_eq_norm] at hy1 hy2
      refine ⟨mem_closedBall.mpr (by linarith), ?_⟩
      rw [mem_ball, not_lt]
      nlinarith
    unfold SupercriticalConformalCovariance.GoodAnnulus.G4 E4Prop at g4 ⊢
    rw [← around_transfer hId hsh, ← across_transfer h₁.1 h₂.1 h₁.2.1 h₂.2.1 hId hR hsub]
    exact g4
  · -- G5, through the source shield
    intro u v hreg huv h9
    obtain ⟨⟨P, s, t, hgeo, htr⟩, hu, hv, h7, h8u, h8v⟩ := hreg
    have hq1' : (q : ℝ) < 1 := by linarith
    have hvalid := SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.loop_annulus_valid
      hr hq0 hq1'
    have hvM : v ∈ eventMiddle z r := sphere_subset_middle hr (by linarith) (by linarith) hv
    have huM : u ∈ eventMiddle z r := sphere_subset_middle hr (by nlinarith) (by nlinarith) hu
    -- (9) transfers
    have hAv : (annAt v ((q : ℝ) * r) (Real.sqrt q * r) hvalid).toSet ⊆ U :=
      (small_ann_toSet_subset hr hvM hq0 hq1 hvalid).trans hYU
    have hareq : aroundRat (D₁, (v, (q : ℝ) * r, Real.sqrt q * r)) =
        aroundRat (D₂, (v, (q : ℝ) * r, Real.sqrt q * r)) := by
      rw [aroundRat_eq_annAt D₁ v _ _ hvalid, aroundRat_eq_annAt D₂ v _ _ hvalid,
        around_transfer hId hAv]
    have h9₁ : aroundRat (D₁, (v, (q : ℝ) * r, Real.sqrt q * r)) ≤
        ENNReal.ofReal k * SupercriticalConformalCovariance.GoodAnnulus.barrier D₁ z r := by
      rw [hareq, hbar]; exact h9
    -- the source shield for both samples
    have hshield : ∀ (D : LSCMetric), SrcOK D z r →
        aroundRat (D, (v, (q : ℝ) * r, Real.sqrt q * r)) ≤
          ENNReal.ofReal k * SupercriticalConformalCovariance.GoodAnnulus.barrier D z r →
        intExt D (eventOpen z r) u v = D (u, v) := by
      intro D hD h9D
      have hbe := barrier_eq_ambient D hD.curve_cont hD.2.1 z r
      have hsh : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.aroundAt D v (q * r)
          (Real.sqrt q * r) ≤ ENNReal.ofReal (1 / (2 * 1)) *
          setDist D (eventMiddle z r) (eventBoundary z r) := by
        refine h9D.trans ?_
        rw [hbe]
        gcongr
        norm_num
        exact hk
      have hcmp : ∀ x y, ENNReal.ofReal 1 * D (x, y) ≤ D (x, y) ∧
          D (x, y) ≤ ENNReal.ofReal 1 * D (x, y) := fun x y => by
        simp only [ENNReal.ofReal_one, one_mul, le_refl, and_self]
      exact (shield_internal_eq hD.curve_cont hD.curve_cont hD.2.1 hD.2.1 one_pos le_rfl hcmp hr
        hq0 hq1 hv huv hD.2.2 hsh).1
    have hVU : eventOpen z r ⊆ U := (eventOpen_subset_carrier' z hr).trans hYU
    have hduv : D₁ (u, v) = D₂ (u, v) := by
      rw [← hshield D₁ h₁ h9₁, ← hshield D₂ h₂ h9, intExt_transfer hVU hId]
    -- the regular-pair tests transfer
    obtain ⟨hcP, hPs, hPt, hlenP, hfinP⟩ := hgeo
    have hY : SupercriticalConformalCovariance.Regular.closedAnnulus z ((a : ℝ) * r) r ⊆ eventCarrier z r := by
      intro y hy
      refine shortCarrier_subset_carrier (a := (a : ℝ)) hr (by linarith) ?_
      exact hy
    have htrU : ∀ τ ∈ Icc s t, P τ ∈ U := fun τ hτ => hYU (hY (htr ⟨τ, hτ, rfl⟩))
    obtain ⟨hcP₁, hlenP₁⟩ := curve_len_transfer_eq hId' hcP htrU (by rw [hlenP]; exact hfinP.ne)
    have hgeo₁ : Geodesic D₁ P s t u v :=
      ⟨hcP₁, hPs, hPt, by rw [hlenP₁, hlenP, hduv], by rw [hduv]; exact hfinP⟩
    have hend : ∀ x ∈ eventMiddle z r, ∀ j : ℕ, 0 < SupercriticalConformalCovariance.Regular.dyadic j →
        SupercriticalConformalCovariance.Regular.dyadic j ≤ (1 - (a : ℝ)) ^ 2 →
        pointSphereDist D₁ x (SupercriticalConformalCovariance.Regular.dyadic j * r) = pointSphereDist D₂ x (SupercriticalConformalCovariance.Regular.dyadic j * r) ∧
        aroundRat (D₁, (x, SupercriticalConformalCovariance.Regular.dyadic j * r, Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j) * r)) =
          aroundRat (D₂, (x, SupercriticalConformalCovariance.Regular.dyadic j * r, Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j) * r)) := by
      intro x hxM j hj0 hja
      have h1a : 0 < 1 - (a : ℝ) := by linarith
      have h1a' : 1 - (a : ℝ) < q := by linarith
      have hδq : SupercriticalConformalCovariance.Regular.dyadic j < 1 / 100 := by nlinarith
      have hδ1 : SupercriticalConformalCovariance.Regular.dyadic j < 1 := by linarith
      have hρ : 0 < SupercriticalConformalCovariance.Regular.dyadic j * r := mul_pos hj0 hr
      have hcb : closedBall x (SupercriticalConformalCovariance.Regular.dyadic j * r) ⊆ U :=
        (closedBall_point_subset hr hxM (by nlinarith)).trans hYU
      have hvalidj := SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.loop_annulus_valid
        hr hj0 hδ1
      constructor
      · rw [pointSphereDist_eq_setDist, pointSphereDist_eq_setDist,
          pointSphere_transfer h₁.1 h₂.1 h₁.2.1 h₂.2.1 hId hρ hcb]
      · rw [aroundRat_eq_annAt D₁ x _ _ hvalidj, aroundRat_eq_annAt D₂ x _ _ hvalidj,
          around_transfer hId ((small_ann_toSet_subset hr hxM hj0 hδq hvalidj).trans hYU)]
    have hreg₁ : SupercriticalConformalCovariance.Regular.SourceRegularPair D₁ z u v r a θ
        ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)) := by
      refine ⟨⟨P, s, t, hgeo₁, htr⟩, hu, hv, by rw [hduv]; exact h7, fun j hj0 hja => ?_,
        fun j hj0 hja => ?_⟩
      · obtain ⟨e1, e2⟩ := hend u huM j hj0 hja
        rw [e1, e2, hduv]; exact h8u j hj0 hja
      · obtain ⟨e1, e2⟩ := hend v hvM j hj0 hja
        rw [e1, e2, hduv]; exact h8v j hj0 hja
    have hconc := g5 u v hreg₁ huv h9₁
    have huY : u ∈ eventCarrier z r := middle_subset_carrier huM
    have hvY : v ∈ eventCarrier z r := middle_subset_carrier hvM
    rw [← he u huY v hvY, ← hduv]
    exact hconc

end SupercriticalConformalCovariance.BiLip.L51
