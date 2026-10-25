import SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery.Surgery
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor




 






set_option autoImplicit false
noncomputable section

open Set Metric Finset LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Spent

 
private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 
theorem continuous_euclidForget_of_barrier (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace) :
    Continuous (euclidForget D) :=
  BiLipschitz.Barrier.continuous_forget_of_barrier D hB hL

 
theorem continuousOn_euclid_of_barrier (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    ContinuousOn P (Icc a b) :=
  BiLipschitz.Barrier.continuousOn_of_barrier_of_length D hB hL hP

 

theorem ae_topology_bridge {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : LQGMetric.DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D) (hQ : 0 < Q)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h μ) :
    ∀ᵐ ω ∂μ, Continuous (euclidForget (D (h ω))) ∧
      (∀ (γ : ℝ → ℂ) (a b : ℝ),
        (D (h ω)).IsCurve γ a b → ContinuousOn γ (Icc a b)) := by
  filter_upwards [BiLipschitz.Barrier.ae_curves_continuous hD hQ μ h hh] with ω hω
  exact ⟨hω.1, hω.2.1⟩

 
theorem weyl_len_le_exp_bound (Dminus Dfull : LSCMetric)
    (ξ Cmax : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget Dminus))
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    {P : ℝ → ℂ} {a b : ℝ} (hP : Dminus.IsCurve P a b)
    (hfn : ∀ u ∈ Icc a b, 0 ≤ f (P u))
    (hf : ∀ u ∈ Icc a b, f (P u) ≤ Cmax) :
    Dfull.len P a b ≤ ENNReal.ofReal (Real.exp (ξ * Cmax)) * Dminus.len P a b := by
  have hfactor := (Toolkit.WeylLength.weylCurveLength_factor_bounds Dminus ξ hξ f hforget hP
    0 Cmax hfn hf).2
  have hlen : Dfull.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : ℂ => Dfull (x, y)) P a b := by
    rw [Dfull.len_eq_curveLength,
      ← HigherDimLQGMetric.curveLengthWith_edist]
    rfl
  rw [hlen]
  have heq : (fun x y : ℂ => Dfull (x, y)) =
      (fun x y : ℂ => weylScale ξ f Dminus (x, y)) := by
    funext x y
    exact hWeyl (x, y)
  rw [heq]
  exact hfactor

 

theorem metric_le_weyl (Dminus Dfull : LSCMetric)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget Dminus))
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x) (x y : ℂ) :
    Dminus (x, y) ≤ Dfull (x, y) := by
  let w : Dminus.Space → ℝ := fun z => Real.exp (ξ * f (z : ℂ))
  have hw : ∀ z : Dminus.Space, 1 ≤ w z := by
    intro z
    change 1 ≤ Real.exp (ξ * f (z : ℂ))
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hξ (hfn z))
  rw [hWeyl (x, y), Toolkit.WeylLength.weylScale_eq_weylDistOn Dminus ξ f hforget]
  change edist (Dminus.pt x) (Dminus.pt y) ≤
    HigherDimLQGMetric.weylDistOn w univ (Dminus.pt x) (Dminus.pt y)
  apply HigherDimLQGMetric.le_weylDistOn
  intro Q hQ hQ0 hQ1 _
  calc
    edist (Dminus.pt x) (Dminus.pt y) = edist (Q 0) (Q 1) := by
      rw [hQ0, hQ1]
    _ ≤ curveLength Q 0 1 := edist_le_curveLength Q zero_le_one
    _ = ENNReal.ofReal 1 * curveLength Q 0 1 := by simp
    _ ≤ HigherDimLQGMetric.weightedLength w Q 0 1 :=
      HigherDimLQGMetric.ofReal_mul_curveLength_le_weightedLength
        zero_le_one (fun z _ => hw (Q z))

 

theorem aroundDist_le_of_metric_le (Dminus Dfull : LSCMetric)
    (hcomp : ∀ x y : ℂ, Dminus (x, y) ≤ Dfull (x, y))
    (A : EuclideanAnnulus) : aroundDist Dminus A ≤ aroundDist Dfull A := by
  unfold aroundDist
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hCurve => le_iInf fun hTrace => le_iInf fun hSep => ?_
  have hcomp' : ∀ x y : ℂ,
      Dminus (x, y) ≤ ((1 : NNReal) : ℝ≥0∞) * Dfull (x, y) := by
    intro x y
    simpa using hcomp x y
  have hCurveMinus : Dminus.IsCurve P a b :=
    EndSaving.PathSurgery.isCurve_of_metric_le Dfull Dminus 1 hcomp' hCurve
  have hLength : Dminus.len P a b ≤ Dfull.len P a b := by
    simpa using EndSaving.PathSurgery.curve_length_le_of_metric_le
      Dfull Dminus 1 hcomp' P a b
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hCurveMinus <| iInf_le_of_le hTrace <|
    iInf_le_of_le hSep hLength

 


theorem spent_closed_window
    (Dminus Dfull : LSCMetric) (ξ Cmax : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hB : BiLipschitz.Barrier.Barrier Dminus)
    (hL : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x) (hfmax : ∀ x : ℂ, f x ≤ Cmax)
    (P : ℝ → ℂ) {L S T : ℝ}
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 L)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 L))
    (hS : 0 ≤ S) (hST : S ≤ T) (hT : T ≤ L)
    (Caround N B : ℝ≥0∞)
    (hAround : ENNReal.ofReal (T - S) ≤ Caround * N)
    (hCompare : N ≤ 2 * B) :
    Dfull.len P S T ≤
      (ENNReal.ofReal (Real.exp (ξ * Cmax)) * Caround * 2) * B := by
  have hP : Dminus.IsCurve P S T :=
    ⟨hST, hG.2.1.mono (Icc_subset_Icc hS hT)⟩
  have hunit : Dminus.len P S T = ENNReal.ofReal (T - S) := by
    exact curveLength_of_hasUnitSpeedOn hu
      ⟨hS, hST.trans hT⟩ ⟨hS.trans hST, hT⟩
  calc
    Dfull.len P S T ≤
        ENNReal.ofReal (Real.exp (ξ * Cmax)) * Dminus.len P S T :=
      weyl_len_le_exp_bound Dminus Dfull ξ Cmax hξ f
        (continuous_euclidForget_of_barrier Dminus hB hL) hWeyl hP
        (fun u _ => hfn (P u)) (fun u _ => hfmax (P u))
    _ = ENNReal.ofReal (Real.exp (ξ * Cmax)) * ENNReal.ofReal (T - S) := by
      rw [hunit]
    _ ≤ ENNReal.ofReal (Real.exp (ξ * Cmax)) * (Caround * N) := by
      gcongr
    _ ≤ ENNReal.ofReal (Real.exp (ξ * Cmax)) * (Caround * (2 * B)) := by
      gcongr
    _ = (ENNReal.ofReal (Real.exp (ξ * Cmax)) * Caround * 2) * B := by
      ring

 
def closedContactTimes (P : ℝ → ℂ) (V : Set ℂ) (L : ℝ) : Set ℝ :=
  Icc 0 L ∩ P ⁻¹' closure V

def firstClosedContact (P : ℝ → ℂ) (V : Set ℂ) (L : ℝ) : ℝ :=
  sInf (closedContactTimes P V L)

def lastClosedContact (P : ℝ → ℂ) (V : Set ℂ) (L : ℝ) : ℝ :=
  sSup (closedContactTimes P V L)

 

theorem closed_contact_extrema (P : ℝ → ℂ) (V : Set ℂ) {L : ℝ}
    (hP : ContinuousOn P (Icc 0 L))
    (hne : (closedContactTimes P V L).Nonempty) :
    let S := sInf (closedContactTimes P V L)
    let T := sSup (closedContactTimes P V L)
    S ∈ closedContactTimes P V L ∧
      T ∈ closedContactTimes P V L ∧
      ∀ t ∈ closedContactTimes P V L, S ≤ t ∧ t ≤ T := by
  have hclosed : IsClosed (closedContactTimes P V L) := by
    unfold closedContactTimes
    exact hP.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  have hbbelow : BddBelow (closedContactTimes P V L) :=
    ⟨0, fun t ht => ht.1.1⟩
  have hbabove : BddAbove (closedContactTimes P V L) :=
    ⟨L, fun t ht => ht.1.2⟩
  exact ⟨hclosed.csInf_mem hne hbbelow,
    hclosed.csSup_mem hne hbabove,
    fun t ht => ⟨csInf_le hbbelow ht, le_csSup hbabove ht⟩⟩

 

theorem closed_contact_time_le_around
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (P : ℝ → ℂ) (V : Set ℂ) (z : ℂ) {r L : ℝ} (hr : 0 < r)
    (hG : IsGeodesicCurve (D.pt ∘ P) 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hV : closure V ⊆ ball z (3 * r))
    (hP0 : 4 * r ≤ dist (P 0) z)
    (hPL : 4 * r ≤ dist (P L) z)
    (hne : (closedContactTimes P V L).Nonempty) :
    ENNReal.ofReal
      (lastClosedContact P V L - firstClosedContact P V L) ≤
      aroundDist D ⟨(z, (3 * r, 4 * r)), by constructor <;> nlinarith⟩ := by
  let A : EuclideanAnnulus :=
    ⟨(z, (3 * r, 4 * r)), by constructor <;> nlinarith⟩
  have hP : D.IsCurve P 0 L := ⟨hG.1, hG.2.1⟩
  have hcont : ContinuousOn P (Icc 0 L) :=
    continuousOn_euclid_of_barrier D hB hL hP
  obtain ⟨hfirst, hlast, horder⟩ := closed_contact_extrema P V hcont hne
  have hSrad : dist (P (firstClosedContact P V L)) z < 3 * r := by
    have hm := hV hfirst.2
    simpa only [Metric.mem_ball, dist_comm, firstClosedContact] using hm
  have hTrad : dist (P (lastClosedContact P V L)) z < 3 * r := by
    have hm := hV hlast.2
    simpa only [Metric.mem_ball, dist_comm, lastClosedContact] using hm
  have hSpos : 0 < firstClosedContact P V L := by
    by_contra hnot
    have hSzero : firstClosedContact P V L = 0 :=
      le_antisymm (le_of_not_gt hnot) hfirst.1.1
    rw [hSzero] at hSrad
    linarith
  have hTlt : lastClosedContact P V L < L := by
    by_contra hnot
    have hTeq : lastClosedContact P V L = L :=
      le_antisymm hlast.1.2 (le_of_not_gt hnot)
    rw [hTeq] at hTrad
    linarith
  have hST : firstClosedContact P V L ≤ lastClosedContact P V L :=
    (horder _ hlast).1
  change ENNReal.ofReal _ ≤ aroundDist D A
  exact Toolkit.PlanarSeparation.separator_twoSidedShortcut_around D A
    le_rfl hSpos hST hTlt le_rfl hcont hG hu
    hP0 hSrad.le hTrad.le hPL

 
theorem spent_first_last_closed_contacts
    (Dminus Dfull : LSCMetric) (ξ Cmax : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hB : BiLipschitz.Barrier.Barrier Dminus)
    (hL : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x) (hfmax : ∀ x : ℂ, f x ≤ Cmax)
    (P : ℝ → ℂ) (V : Set ℂ) {L : ℝ}
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 L)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 L))
    (hne : (closedContactTimes P V L).Nonempty)
    (Caround N B : ℝ≥0∞)
    (hAround : ENNReal.ofReal
      (lastClosedContact P V L - firstClosedContact P V L) ≤ Caround * N)
    (hCompare : N ≤ 2 * B) :
    Dfull.len P (firstClosedContact P V L) (lastClosedContact P V L) ≤
      (ENNReal.ofReal (Real.exp (ξ * Cmax)) * Caround * 2) * B := by
  have hP : Dminus.IsCurve P 0 L := ⟨hG.1, hG.2.1⟩
  have hcont : ContinuousOn P (Icc 0 L) :=
    continuousOn_euclid_of_barrier Dminus hB hL hP
  obtain ⟨hfirst, hlast, horder⟩ := closed_contact_extrema P V hcont hne
  have hST : firstClosedContact P V L ≤ lastClosedContact P V L :=
    (horder _ hlast).1
  exact spent_closed_window Dminus Dfull ξ Cmax hξ f hB hL hWeyl
    hfn hfmax P hG hu hfirst.1.1 hST hlast.1.2 Caround N B
    hAround hCompare

 

theorem spent_first_last_of_around_event
    (Dminus Dfull : LSCMetric) (ξ Cmax : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hB : BiLipschitz.Barrier.Barrier Dminus)
    (hL : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x) (hfmax : ∀ x : ℂ, f x ≤ Cmax)
    (P : ℝ → ℂ) (V : Set ℂ) (z : ℂ) {r L : ℝ} (hr : 0 < r)
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 L)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 L))
    (hV : closure V ⊆ ball z (3 * r))
    (hP0 : 4 * r ≤ dist (P 0) z)
    (hPL : 4 * r ≤ dist (P L) z)
    (hne : (closedContactTimes P V L).Nonempty)
    (Caround N B : ℝ≥0∞)
    (hAroundFull : aroundDist Dfull
      ⟨(z, (3 * r, 4 * r)), by constructor <;> nlinarith⟩ ≤ Caround * N)
    (hCompare : N ≤ 2 * B) :
    Dfull.len P (firstClosedContact P V L) (lastClosedContact P V L) ≤
      (ENNReal.ofReal (Real.exp (ξ * Cmax)) * Caround * 2) * B := by
  let A : EuclideanAnnulus :=
    ⟨(z, (3 * r, 4 * r)), by constructor <;> nlinarith⟩
  have hMetric : ∀ x y : ℂ, Dminus (x, y) ≤ Dfull (x, y) :=
    metric_le_weyl Dminus Dfull ξ hξ f
      (continuous_euclidForget_of_barrier Dminus hB hL) hWeyl hfn
  have hAround : ENNReal.ofReal
      (lastClosedContact P V L - firstClosedContact P V L) ≤ Caround * N := by
    calc
      ENNReal.ofReal _ ≤ aroundDist Dminus A :=
        closed_contact_time_le_around Dminus hB hL P V z hr hG hu
          hV hP0 hPL hne
      _ ≤ aroundDist Dfull A := aroundDist_le_of_metric_le Dminus Dfull hMetric A
      _ ≤ Caround * N := hAroundFull
  exact spent_first_last_closed_contacts Dminus Dfull ξ Cmax hξ f hB hL
    hWeyl hfn hfmax P V hG hu hne Caround N B hAround hCompare

 

theorem closed_contact_pair_distance_le_window (D : LSCMetric)
    (P : ℝ → ℂ) (V : Set ℂ) {L u v : ℝ}
    (hP : ContinuousOn P (Icc 0 L))
    (hne : (closedContactTimes P V L).Nonempty)
    (hu : u ∈ closedContactTimes P V L)
    (hv : v ∈ closedContactTimes P V L) :
    D (P u, P v) ≤
      D.len P (firstClosedContact P V L) (lastClosedContact P V L) := by
  obtain ⟨_, _, horder⟩ := closed_contact_extrema P V hP hne
  have hu' := horder u hu
  have hv' := horder v hv
  rcases le_total u v with huv | hvu
  · have hpoint : D (P u, P v) ≤ D.len P u v := by
      have := eVariationOn.edist_le (D.pt ∘ P)
        (Set.left_mem_Icc.mpr huv) (Set.right_mem_Icc.mpr huv)
      exact this
    exact hpoint.trans (eVariationOn.mono (D.pt ∘ P)
      (Icc_subset_Icc hu'.1 hv'.2))
  · have hpoint : D (P v, P u) ≤ D.len P v u := by
      have := eVariationOn.edist_le (D.pt ∘ P)
        (Set.left_mem_Icc.mpr hvu) (Set.right_mem_Icc.mpr hvu)
      exact this
    rw [D.isExtMetric.2.2.1] 
    exact hpoint.trans (eVariationOn.mono (D.pt ∘ P)
      (Icc_subset_Icc hv'.1 hu'.2))

 


theorem bump_zero_outside_closed_window
    (P : ℝ → ℂ) (V : Set ℂ) (f : C(ℂ, ℝ)) {L : ℝ}
    (hP : ContinuousOn P (Icc 0 L))
    (hne : (closedContactTimes P V L).Nonempty)
    (hP0 : P 0 ∉ closure V) (hPL : P L ∉ closure V)
    (hf : ∀ x : ℂ, x ∉ V → f x = 0) :
    ∀ u ∈ Icc 0 L,
      u ≤ firstClosedContact P V L ∨ lastClosedContact P V L ≤ u →
      f (P u) = 0 := by
  obtain ⟨hfirst, hlast, horder⟩ := closed_contact_extrema P V hP hne
  let S := firstClosedContact P V L
  let T := lastClosedContact P V L
  have hSpos : 0 < S := by
    by_contra hnot
    have heq : S = 0 := le_antisymm (le_of_not_gt hnot) hfirst.1.1
    exact hP0 (heq ▸ hfirst.2)
  have hTlt : T < L := by
    by_contra hnot
    have heq : T = L := le_antisymm hlast.1.2 (le_of_not_gt hnot)
    exact hPL (heq ▸ hlast.2)
  let Z : Set ℝ := Icc 0 L ∩ (fun u => f (P u)) ⁻¹' {0}
  have hZclosed : IsClosed Z := by
    exact (f.continuous.comp_continuousOn hP).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hbefore : Ico 0 S ⊆ Z := by
    intro u hu
    have huI : u ∈ Icc 0 L := ⟨hu.1, hu.2.le.trans hfirst.1.2⟩
    have hno : P u ∉ closure V := by
      intro hmem
      exact (not_le.mpr hu.2) (horder u ⟨huI, hmem⟩).1
    exact ⟨huI, hf (P u) (fun hv => hno (subset_closure hv))⟩
  have hafter : Ioc T L ⊆ Z := by
    intro u hu
    have huI : u ∈ Icc 0 L := ⟨hlast.1.1.trans hu.1.le, hu.2⟩
    have hno : P u ∉ closure V := by
      intro hmem
      exact (not_le.mpr hu.1) (horder u ⟨huI, hmem⟩).2
    exact ⟨huI, hf (P u) (fun hv => hno (subset_closure hv))⟩
  have hSzero : f (P S) = 0 := by
    have hcl : S ∈ closure (Ico 0 S) := by
      rw [closure_Ico hSpos.ne]
      exact ⟨hSpos.le, le_rfl⟩
    exact (hZclosed.closure_subset_iff.mpr hbefore hcl).2
  have hTzero : f (P T) = 0 := by
    have hcl : T ∈ closure (Ioc T L) := by
      rw [closure_Ioc hTlt.ne]
      exact ⟨le_rfl, hTlt.le⟩
    exact (hZclosed.closure_subset_iff.mpr hafter hcl).2
  intro u huI hu
  rcases hu with hleft | hright
  · rcases hleft.eq_or_lt with heq | hlt
    · exact heq ▸ hSzero
    · exact (hbefore ⟨huI.1, hlt⟩).2
  · rcases hright.eq_or_lt with heq | hlt
    · exact heq.symm ▸ hTzero
    · exact (hafter ⟨hlt, huI.2⟩).2

 


theorem bump_zero_on_ordered_gaps
    (P : ℝ → ℂ) (V : ℕ → Set ℂ) (g : ℕ → C(ℂ, ℝ))
    (f : C(ℂ, ℝ)) (τ σ : ℕ → ℝ) {T : ℝ} (n : ℕ)
    (hP : ContinuousOn P (Icc 0 T))
    (hbound : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (horder : ∀ i j, i < j → j < n → σ i < τ j)
    (hne : ∀ i < n, (closedContactTimes P (V i) T).Nonempty)
    (hτ : ∀ i < n, τ i = firstClosedContact P (V i) T)
    (hσ : ∀ i < n, σ i = lastClosedContact P (V i) T)
    (hP0 : ∀ i < n, P 0 ∉ closure (V i))
    (hPT : ∀ i < n, P T ∉ closure (V i))
    (hg : ∀ i < n, ∀ x : ℂ, x ∉ V i → g i x = 0)
    (hDecomp : ∀ x : ℂ, f x = ∑ i ∈ range n, g i x) :
    (∀ i < n, ∀ u ∈ Icc (EndSaving.PathSurgery.gapStart σ i) (τ i), f (P u) = 0) ∧
      (∀ u ∈ Icc (EndSaving.PathSurgery.gapStart σ n) T, f (P u) = 0) := by
  have hleft : ∀ i, i ≤ n → ∀ j, j < i → σ j ≤ EndSaving.PathSurgery.gapStart σ i := by
    intro i hi j hj
    cases i with
    | zero => omega
    | succ k =>
        change σ j ≤ σ k
        by_cases heq : j = k
        · rw [heq]
        · have hjk : j < k := by omega
          exact (horder j k hjk (by omega)).le.trans
            (hbound k (by omega)).2.1
  have hright : ∀ i < n, ∀ j < n, i ≤ j → τ i ≤ τ j := by
    intro i hi j hj hij
    rcases hij.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (hbound i hi).2.1.trans (horder i j hlt hj).le
  have hSite : ∀ j < n, ∀ u ∈ Icc 0 T,
      u ≤ τ j ∨ σ j ≤ u → g j (P u) = 0 := by
    intro j hj u hu hside
    apply bump_zero_outside_closed_window P (V j) (g j)
      hP (hne j hj) (hP0 j hj) (hPT j hj) (hg j hj) u hu
    simpa only [← hτ j hj, ← hσ j hj] using hside
  constructor
  · intro i hi u hu
    have hstart : 0 ≤ EndSaving.PathSurgery.gapStart σ i := by
      cases i with
      | zero => exact le_rfl
      | succ k =>
          change 0 ≤ σ k
          exact (hbound k (by omega)).1.trans
            (hbound k (by omega)).2.1
    have huI : u ∈ Icc 0 T :=
      ⟨hstart.trans hu.1,
        hu.2.trans ((hbound i hi).2.1.trans (hbound i hi).2.2)⟩
    rw [hDecomp (P u)]
    apply sum_eq_zero
    intro j hj
    have hjn : j < n := mem_range.mp hj
    apply hSite j hjn u huI
    by_cases hji : j < i
    · right
      exact (hleft i hi.le j hji).trans hu.1
    · left
      exact hu.2.trans (hright i hi j hjn (by omega))
  · intro u hu
    have hstart : 0 ≤ EndSaving.PathSurgery.gapStart σ n := by
      cases n with
      | zero => exact le_rfl
      | succ k =>
          change 0 ≤ σ k
          exact (hbound k (by omega)).1.trans
            (hbound k (by omega)).2.1
    have huI : u ∈ Icc 0 T := ⟨hstart.trans hu.1, hu.2⟩
    rw [hDecomp (P u)]
    apply sum_eq_zero
    intro j hj
    have hjn : j < n := mem_range.mp hj
    apply hSite j hjn u huI
    right
    exact (hleft n le_rfl j hjn).trans hu.1

 

theorem aggregate_spent_of_windows
    (Dminus Dfull : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hB : BiLipschitz.Barrier.Barrier Dminus) (hL : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (P : ℝ → ℂ) (τ σ : ℕ → ℝ) {T : ℝ} (n : ℕ)
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 T))
    (hbound : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (horder : ∀ i j, i < j → j < n → σ i < τ j)
    (hfGap : ∀ i < n, ∀ u ∈ Icc (EndSaving.PathSurgery.gapStart σ i) (τ i),
      f (P u) = 0)
    (hfTail : ∀ u ∈ Icc (EndSaving.PathSurgery.gapStart σ n) T, f (P u) = 0)
    (Cspent B : ℝ≥0∞)
    (hWindow : ∀ i < n, Dfull.len P (τ i) (σ i) ≤ Cspent * B) :
    Dfull.len P 0 T ≤ Dminus.len P 0 T + Cspent * B * n := by
  let hforget := continuous_euclidForget_of_barrier Dminus hB hL
  have hminus : Dminus.IsCurve P 0 T := ⟨hG.1, hG.2.1⟩
  have hfull : Dfull.IsCurve P 0 T :=
    EndSaving.PathSurgery.weyl_geodesic_isCurve_of_continuous Dminus Dfull ξ f
      hforget hWeyl P hG hu
  have hgap : ∀ i < n,
      Dfull.len P (EndSaving.PathSurgery.gapStart σ i) (τ i) =
        Dminus.len P (EndSaving.PathSurgery.gapStart σ i) (τ i) := by
    intro i hi
    have hb := hbound i hi
    have hstart : 0 ≤ EndSaving.PathSurgery.gapStart σ i := by
      cases i with
      | zero => exact le_rfl
      | succ j =>
          change 0 ≤ σ j
          exact (hbound j (by omega)).1.trans
            (hbound j (by omega)).2.1
    have hstartτ : EndSaving.PathSurgery.gapStart σ i ≤ τ i := by
      cases i with
      | zero => exact hb.1
      | succ j =>
          change σ j ≤ τ (j + 1)
          exact (horder j (j + 1) (by omega) hi).le
    have hP : Dminus.IsCurve P (EndSaving.PathSurgery.gapStart σ i) (τ i) :=
      ⟨hstartτ, hG.2.1.mono (Icc_subset_Icc hstart (hb.2.1.trans hb.2.2))⟩
    exact EndSaving.PathSurgery.weyl_len_eq_of_zero_trace Dminus Dfull ξ f
      hforget hWeyl hP (hfGap i hi)
  have htailStart : 0 ≤ EndSaving.PathSurgery.gapStart σ n := by
    cases n with
    | zero => exact le_rfl
    | succ j =>
        change 0 ≤ σ j
        exact (hbound j (by omega)).1.trans
          (hbound j (by omega)).2.1
  have htailLE : EndSaving.PathSurgery.gapStart σ n ≤ T := by
    cases n with
    | zero => exact hG.1
    | succ j =>
        change σ j ≤ T
        exact (hbound j (by omega)).2.2
  have htailP : Dminus.IsCurve P (EndSaving.PathSurgery.gapStart σ n) T :=
    ⟨htailLE, hG.2.1.mono (Icc_subset_Icc htailStart le_rfl)⟩
  have htail : Dfull.len P (EndSaving.PathSurgery.gapStart σ n) T =
      Dminus.len P (EndSaving.PathSurgery.gapStart σ n) T :=
    EndSaving.PathSurgery.weyl_len_eq_of_zero_trace Dminus Dfull ξ f
      hforget hWeyl htailP hfTail
  have hdecompFull := EndSaving.PathSurgery.finite_splice_length Dfull P (fun _ => P)
    τ σ n T hfull hbound horder
    (fun i hi => ⟨(hbound i hi).2.1,
      hfull.2.mono (Icc_subset_Icc (hbound i hi).1 (hbound i hi).2.2)⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  have hdecompMinus := EndSaving.PathSurgery.finite_splice_length Dminus P (fun _ => P)
    τ σ n T hminus hbound horder
    (fun i hi => ⟨(hbound i hi).2.1,
      hminus.2.mono (Icc_subset_Icc (hbound i hi).1 (hbound i hi).2.2)⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  rw [EndSaving.PathSurgery.spliceN_self] at hdecompFull hdecompMinus
  have hsum : ∑ i ∈ range n,
      (Dfull.len P (EndSaving.PathSurgery.gapStart σ i) (τ i) + Dfull.len P (τ i) (σ i)) ≤
      ∑ i ∈ range n,
      (Dminus.len P (EndSaving.PathSurgery.gapStart σ i) (τ i) + Cspent * B) := by
    apply sum_le_sum
    intro i hi
    rw [hgap i (mem_range.mp hi)]
    exact add_le_add_right (hWindow i (mem_range.mp hi)) _
  calc
    Dfull.len P 0 T =
        (∑ i ∈ range n,
          (Dfull.len P (EndSaving.PathSurgery.gapStart σ i) (τ i) +
            Dfull.len P (τ i) (σ i))) +
          Dfull.len P (EndSaving.PathSurgery.gapStart σ n) T := hdecompFull
    _ ≤ (∑ i ∈ range n,
          (Dminus.len P (EndSaving.PathSurgery.gapStart σ i) (τ i) + Cspent * B)) +
          Dminus.len P (EndSaving.PathSurgery.gapStart σ n) T := by
            rw [htail]
            exact add_le_add_left hsum _
    _ = (∑ i ∈ range n, Dminus.len P (EndSaving.PathSurgery.gapStart σ i) (τ i)) +
          Dminus.len P (EndSaving.PathSurgery.gapStart σ n) T + Cspent * B * n := by
            rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
            ring
    _ ≤ Dminus.len P 0 T + Cspent * B * n := by
      rw [hdecompMinus, sum_add_distrib]
      gcongr
      exact le_add_right le_rfl

 

theorem aggregate_spent_of_around_event
    (Dminus Dfull : LSCMetric) (ξ Cmax : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hB : BiLipschitz.Barrier.Barrier Dminus)
    (hL : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x) (hfmax : ∀ x : ℂ, f x ≤ Cmax)
    (P : ℝ → ℂ) (V : ℕ → Set ℂ) (z : ℕ → ℂ)
    (r : ℝ) (τ σ : ℕ → ℝ) {T : ℝ} (n : ℕ)
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 T))
    (hbound : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (horder : ∀ i j, i < j → j < n → σ i < τ j)
    (hr : 0 < r)
    (hV : ∀ i < n, closure (V i) ⊆ ball (z i) (3 * r))
    (hP0 : ∀ i < n, 4 * r ≤ dist (P 0) (z i))
    (hPT : ∀ i < n, 4 * r ≤ dist (P T) (z i))
    (hne : ∀ i < n, (closedContactTimes P (V i) T).Nonempty)
    (hτ : ∀ i < n, τ i = firstClosedContact P (V i) T)
    (hσ : ∀ i < n, σ i = lastClosedContact P (V i) T)
    (hfGap : ∀ i < n, ∀ u ∈ Icc (EndSaving.PathSurgery.gapStart σ i) (τ i),
      f (P u) = 0)
    (hfTail : ∀ u ∈ Icc (EndSaving.PathSurgery.gapStart σ n) T, f (P u) = 0)
    (Caround B : ℝ≥0∞) (N : ℕ → ℝ≥0∞)
    (hAround : ∀ i < n, aroundDist Dfull
      ⟨(z i, (3 * r, 4 * r)), by
        constructor <;> nlinarith [hr]⟩ ≤ Caround * N i)
    (hCompare : ∀ i < n, N i ≤ 2 * B) :
    Dfull.len P 0 T ≤ Dminus.len P 0 T +
      (ENNReal.ofReal (Real.exp (ξ * Cmax)) * Caround * 2) * B * n := by
  apply aggregate_spent_of_windows Dminus Dfull ξ f hB hL hWeyl
    P τ σ n hG hu hbound horder hfGap hfTail
  intro i hi
  rw [hτ i hi, hσ i hi]
  exact spent_first_last_of_around_event Dminus Dfull ξ Cmax hξ f
    hB hL hWeyl hfn hfmax P (V i) (z i) hr hG hu
    (hV i hi) (hP0 i hi) (hPT i hi) (hne i hi)
    Caround (N i) B (hAround i hi) (hCompare i hi)


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Spent
