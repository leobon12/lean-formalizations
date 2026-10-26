import SupercriticalConformalCovariance.BiLip.Core
import SLUMetricAPI2
import SupercriticalLQGUniqueness.B2.PfeLocal.Length
import SupercriticalLQGUniqueness.B2.PfeLocal.AnnulusEvent
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1Crossing
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate

/-!
# Lemma 2.1: the whole-plane `LSCMetric` instances of the deterministic core

For one sample, `D₀ = D_h` with `(ℂ, D_h) → ℂ` continuous (a.s. for a GFF plus a continuous function,
`SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont`):
* **as a source** (the `d` side of `e ≤ C d`, l. 139–141): admissible paths are `D₀`-curves, the length is
  `D₀.len`, the crossing cost of `A_{r/2,r}(z)` is `D₀(across A_{r/2,r}(z))` (`acrossAt`), and the curves in
  `U` approximate `d = D₀(·,·;U)` (`pathInf D₀ U`, equal to `D₀.internal U` by `rfl`);
* **as a target** (the `d` side of `d ≤ C e`, "interchanging the two metrics", l. 147): the confined metric
  on a compact `C` is `D₀(·,·;C)` (`pathInf D₀ C`), Lemma 1.2's lower semicontinuous object
  (`internal_compact_joint_lsc`), and a `D₀`-around loop gives a good loop (`isGoodLoop_of_aroundDist_lt`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric acrossDist aroundDist EuclideanAnnulus Disconnects)
open SupercriticalLQGUniqueness.B2.PfeLocal (innerAnnulus outerAnnulus lsc_len_add internal_le_len
  l4Fill)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)

/-- The internal metric `D(x, y; Y)` at points of `ℂ`: the infimum of the `D`-lengths of `D`-curves in `Y`
from `x` to `y`. For `x, y ∈ Y` it is `D.internal Y` (`internal_eq_pathInf`). -/
def pathInf (D : LSCMetric) (Y : Set ℂ) (x y : ℂ) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b) (_ : ∀ t ∈ Icc a b, P t ∈ Y)
    (_ : P a = x) (_ : P b = y), D.len P a b

theorem internal_eq_pathInf (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) :
    D.internal Y p = pathInf D Y p.1 p.2 := rfl

/-- `D(across A_{r/2,r}(z))` (`0` for `r ≤ 0`, a junk value never used). -/
def acrossAt (D : LSCMetric) (z : ℂ) (r : ℝ) : ℝ≥0∞ :=
  if hr : 0 < r then acrossDist D (innerAnnulus z r hr) else 0

/-- `D(around A_{r,2r}(z))` (`∞` for `r ≤ 0`, a junk value never used). -/
def aroundAt (D : LSCMetric) (z : ℂ) (r : ℝ) : ℝ≥0∞ :=
  if hr : 0 < r then aroundDist D (outerAnnulus z r hr) else ⊤

/-! ## Source -/

theorem curve_continuousOn {D : LSCMetric} (hf : Continuous (forget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) : ContinuousOn P (Icc a b) :=
  hf.comp_continuousOn hP.2

theorem len_add3 (D : LSCMetric) (P : ℝ → ℂ) (s t u : ℝ) (hst : s ≤ t) (htu : t ≤ u) :
    D.len P s u = D.len P s t + D.len P t u :=
  lsc_len_add D P hst htu

/-- The crossing charge (l. 141): a `D`-curve running from `B̄_{r/2}(w)` to `ℂ ∖ B_r(w)` has length at least
`D(across A_{r/2,r}(w))`. -/
theorem acrossAt_le_len {D : LSCMetric} (hf : Continuous (forget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (w : ℂ) (r τ t : ℝ) (haτ : a ≤ τ) (hτt : τ ≤ t) (htb : t ≤ b)
    (h1 : dist (P τ) w ≤ r / 2) (h2 : r ≤ dist (P t) w) : acrossAt D w r ≤ D.len P τ t := by
  unfold acrossAt
  split_ifs with hr
  · exact SupercriticalLQGUniqueness.B2.PfeWeyl.acrossDist_le_len_of_crossing D
      (innerAnnulus w r hr) hτt ((curve_continuousOn hf hP).mono (Icc_subset_Icc haτ htb)) h1 h2
  · exact zero_le

/-- Curves approximate the internal metric from above. -/
theorem exists_curve_le_pathInf_add (D : LSCMetric) (Y : Set ℂ) (u v : ℂ)
    (hfin : pathInf D Y u v < ∞) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ P a b, D.IsCurve P a b ∧ (∀ t ∈ Icc a b, P t ∈ Y) ∧ P a = u ∧ P b = v ∧
      D.len P a b ≤ pathInf D Y u v + δ := by
  have hlt : pathInf D Y u v < pathInf D Y u v + δ := ENNReal.lt_add_right hfin.ne hδ.ne'
  conv_lhs at hlt => rw [pathInf]
  simp only [iInf_lt_iff] at hlt
  obtain ⟨P, a, b, hP, hY, ha, hb, hlen⟩ := hlt
  exact ⟨P, a, b, hP, hY, ha, hb, hlen.le⟩

/-! ## Target -/

theorem pathInf_le_len (D : LSCMetric) (Y : Set ℂ) {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hY : ∀ t ∈ Icc a b, P t ∈ Y) : pathInf D Y (P a) (P b) ≤ D.len P a b :=
  internal_le_len D Y P a b hP hY

theorem isPMetricOn_pathInf (D : LSCMetric) (C : Set ℂ) : IsPMetricOn (pathInf D C) C := by
  have hE := SupercriticalLQGUniqueness.LSCMetric.isExtMetric_internal D C
  refine ⟨fun x hx => hE.1 ⟨x, hx⟩, fun x hx y hy => hE.2.2.1 ⟨x, hx⟩ ⟨y, hy⟩,
    fun x hx y hy z hz => hE.2.2.2 ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩⟩

theorem pathInf_mono (D : LSCMetric) {C C' : Set ℂ} (hCC : C ⊆ C') (x y : ℂ) :
    pathInf D C' x y ≤ pathInf D C x y := by
  unfold pathInf
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPC => le_iInf fun ha => le_iInf fun hb => ?_
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hP <|
    iInf_le_of_le (fun t ht => hCC (hPC t ht)) <| iInf_le_of_le ha <| iInf_le_of_le hb le_rfl

/-- Lemma 1.2 (l. 85–87): the internal metric of a compact set is lower semicontinuous, here in the
sequential form consumed by the core. -/
theorem pathInf_lsc_seq (D : LSCMetric) {C : Set ℂ} (hC : IsCompact C) (x : ℂ) (hx : x ∈ C)
    (y : ℂ) (hy : y ∈ C) (xs ys : ℕ → ℂ) (hxs : ∀ j, xs j ∈ C) (hys : ∀ j, ys j ∈ C)
    (hxt : Tendsto xs atTop (𝓝 x)) (hyt : Tendsto ys atTop (𝓝 y)) (M : ℝ≥0∞)
    (hM : ∀ j, pathInf D C (xs j) (ys j) ≤ M) : pathInf D C x y ≤ M := by
  have hlsc := SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.internal_compact_joint_lsc
    hC
  have ht : Tendsto (fun j => (D, ((⟨xs j, hxs j⟩ : C), (⟨ys j, hys j⟩ : C)))) atTop
      (𝓝 (D, ((⟨x, hx⟩ : C), (⟨y, hy⟩ : C)))) :=
    tendsto_const_nhds.prodMk_nhds ((tendsto_subtype_rng.2 hxt).prodMk_nhds
      (tendsto_subtype_rng.2 hyt))
  by_contra hlt
  push Not at hlt
  have hev := ht.eventually (hlsc _ M hlt)
  obtain ⟨j, hj⟩ := hev.exists
  exact absurd (hM j) (not_le.2 hj)

/-- A `D`-around loop of `A_{r,2r}(z)` of length `< M` is a good loop for `D(·,·;B̄_{2r}(z))`. -/
theorem isGoodLoop_of_aroundDist_lt {D : LSCMetric} (hf : Continuous (forget D)) (z : ℂ) {r : ℝ}
    (hr : 0 < r) {M : ℝ≥0∞} (hM : aroundDist D (outerAnnulus z r hr) < M) :
    IsGoodLoop (pathInf D (closedBall z (2 * r))) (closedBall z (2 * r)) z r M := by
  unfold aroundDist at hM
  simp only [iInf_lt_iff] at hM
  obtain ⟨γ, s₀, s₁, hγ, hγA, hdisc, hlen⟩ := hM
  have hA : ∀ t ∈ Icc s₀ s₁, r < dist (γ t) z ∧ dist (γ t) z < 2 * r := by
    intro t ht
    have := hγA t ht
    rw [SupercriticalLQGUniqueness.EuclideanAnnulus.toSet_eq] at this
    exact this
  have hγc : ContinuousOn γ (Icc s₀ s₁) := curve_continuousOn hf hγ
  have hsub : ∀ t ∈ Icc s₀ s₁, γ t ∈ closedBall z (2 * r) := fun t ht =>
    mem_closedBall.2 (hA t ht).2.le
  have hdiam : ∀ s ∈ Icc s₀ s₁, ∀ t ∈ Icc s₀ s₁, s ≤ t →
      pathInf D (closedBall z (2 * r)) (γ s) (γ t) ≤ D.len γ s₀ s₁ := by
    intro s hs t ht hst
    have hc : D.IsCurve γ s t := ⟨hst, hγ.2.mono (Icc_subset_Icc hs.1 ht.2)⟩
    exact (pathInf_le_len D _ hc fun u hu => hsub u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩).trans
      (SupercriticalLQGUniqueness.B2.PfeWeyl.len_mono_Icc D γ hs.1 ht.2)
  refine ⟨γ '' Icc s₀ s₁, ⟨γ s₀, s₀, ⟨le_rfl, hγ.1⟩, rfl⟩, isPreconnected_Icc.image _ hγc, ?_, ?_,
    ?_, SupercriticalLQGUniqueness.B2.PfeLocal.l4_closedBall_subset_fill hdisc, D.len γ s₀ s₁, hlen,
    ?_⟩
  · rintro _ ⟨t, ht, rfl⟩; exact hsub t ht
  · rintro _ ⟨t, ht, rfl⟩; exact hsub t ht
  · rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ hb
    exact absurd (mem_ball.1 hb) (not_lt.2 (hA t ht).1.le)
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rcases le_total s t with hst | hts
    · exact hdiam s hs t ht hst
    · rw [(isPMetricOn_pathInf D _).2.1 _ (hsub s hs) _ (hsub t ht)]
      exact hdiam t ht s hs hts

/-! ## The closed-annulus crossing cost and the path-hit around cost (SupercriticalLQGUniqueness objects)

The sealed tail bounds (`Objects.AnnulusTails.around_upper_tail`, `acr_lower_tail`) are stated
for `Objects.CorrectedEvent.acr` (crossings of the closed annulus between its boundary circles) and
`Objects.CorrectedEvent.around` (loops in the open annulus hit by every path between its boundary circles).
These are the source quantities of (4). -/

open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent (acr around cann ann)

/-- `D(across A_{r/2,r}(z))` as a closed-annulus crossing cost -/
def acrAt (D : LSCMetric) (z : ℂ) (r : ℝ) : ℝ≥0∞ := acr D z (r / 2) r

/-- `D(around A_{r,2r}(z))` as a path-hit around cost -/
def aroundHit (D : LSCMetric) (z : ℂ) (r : ℝ) : ℝ≥0∞ := around D z r (2 * r)

/-- **The crossing charge** (l. 141) for the closed-annulus cost. -/
theorem acrAt_le_len {D : LSCMetric} (hf : Continuous (forget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (w : ℂ) (r τ t : ℝ) (haτ : a ≤ τ) (hτt : τ ≤ t) (htb : t ≤ b)
    (h1 : dist (P τ) w ≤ r / 2) (h2 : r ≤ dist (P t) w) : acrAt D w r ≤ D.len P τ t := by
  have hPc : ContinuousOn P (Icc τ t) := (curve_continuousOn hf hP).mono (Icc_subset_Icc haτ htb)
  have hf' : ContinuousOn (fun u => dist (P u) w) (Icc τ t) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  have hr : r / 2 ≤ r := by have := dist_nonneg (x := P τ) (y := w); linarith
  obtain ⟨s, s', hτs, hss', hs't, hs, hs', hmid⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hτt hf' hr h1 h2
  have hc : D.IsCurve P s s' := ⟨hss', hP.2.mono (Icc_subset_Icc (haτ.trans hτs) (hs't.trans htb))⟩
  have hacr : acrAt D w r ≤ D.len P s s' := by
    unfold acrAt acr
    refine iInf_le_of_le P <| iInf_le_of_le s <| iInf_le_of_le s' <| iInf_le_of_le hc <|
      iInf_le_of_le ?_ <| iInf_le_of_le (mem_sphere.2 hs) <| iInf_le_of_le (mem_sphere.2 hs') le_rfl
    rintro _ ⟨u, hu, rfl⟩
    exact hmid u hu
  exact hacr.trans (SupercriticalLQGUniqueness.B2.PfeWeyl.len_mono_Icc D P hτs hs't)

/-- A path-hit around loop of `A_{r,2r}(z)` of length `< M` is a good loop for `D(·,·;B̄_{2r}(z))`. -/
theorem isGoodLoop_of_aroundHit_lt {D : LSCMetric} (hf : Continuous (forget D)) (z : ℂ) {r : ℝ}
    {M : ℝ≥0∞} (hM : aroundHit D z r < M) :
    IsGoodLoop (pathInf D (closedBall z (2 * r))) (closedBall z (2 * r)) z r M := by
  unfold aroundHit around at hM
  simp only [iInf_lt_iff] at hM
  obtain ⟨γ, s₀, s₁, hγ, hγA, hdisc, hlen⟩ := hM
  have hγc : ContinuousOn γ (Icc s₀ s₁) := curve_continuousOn hf hγ
  have hcl : IsClosed (γ '' Icc s₀ s₁) := (isCompact_Icc.image_of_continuousOn hγc).isClosed
  have hdisc' : Disconnects (γ '' Icc s₀ s₁) (sphere z r) (sphere z (2 * r)) :=
    (SupercriticalLQGUniqueness.disconnects_iff_lqgMetric_disconnects hcl).2 hdisc
  have hA : ∀ t ∈ Icc s₀ s₁, r < dist (γ t) z ∧ dist (γ t) z < 2 * r := fun t ht =>
    hγA ⟨t, ht, rfl⟩
  have hsub : ∀ t ∈ Icc s₀ s₁, γ t ∈ closedBall z (2 * r) := fun t ht =>
    mem_closedBall.2 (hA t ht).2.le
  have hdiam : ∀ s ∈ Icc s₀ s₁, ∀ t ∈ Icc s₀ s₁, s ≤ t →
      pathInf D (closedBall z (2 * r)) (γ s) (γ t) ≤ D.len γ s₀ s₁ := by
    intro s hs t ht hst
    have hc : D.IsCurve γ s t := ⟨hst, hγ.2.mono (Icc_subset_Icc hs.1 ht.2)⟩
    exact (pathInf_le_len D _ hc fun u hu => hsub u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩).trans
      (SupercriticalLQGUniqueness.B2.PfeWeyl.len_mono_Icc D γ hs.1 ht.2)
  refine ⟨γ '' Icc s₀ s₁, ⟨γ s₀, s₀, ⟨le_rfl, hγ.1⟩, rfl⟩, isPreconnected_Icc.image _ hγc, ?_, ?_,
    ?_, SupercriticalLQGUniqueness.B2.PfeLocal.l4_closedBall_subset_fill hdisc', D.len γ s₀ s₁, hlen,
    ?_⟩
  · rintro _ ⟨t, ht, rfl⟩; exact hsub t ht
  · rintro _ ⟨t, ht, rfl⟩; exact hsub t ht
  · rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ hb
    exact absurd (mem_ball.1 hb) (not_lt.2 (hA t ht).1.le)
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rcases le_total s t with hst | hts
    · exact hdiam s hs t ht hst
    · rw [(isPMetricOn_pathInf D _).2.1 _ (hsub s hs) _ (hsub t ht)]
      exact hdiam t ht s hs hts

end SupercriticalConformalCovariance.BiLip
