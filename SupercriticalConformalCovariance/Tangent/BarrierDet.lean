import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.GeoCompact
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA6
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas

/-!
# Lemma 3.2's barrier, deterministic surgery for internal metrics

Paper l. 182–188 (proof of Lemma 3.2): "there exists a loop separating `B_R` from infinity whose
`D_h`-length is strictly less than half the cost of crossing a farther surrounding annulus. Any path
between two points of `B_R` that exits that outer annulus hits the loop before and after the
excursion; replacing the excursion by the shorter arc of the loop strictly decreases its length."

`internal_eq_of_around_lt_across`: for any lower semicontinuous metric whose curves are Euclidean
continuous and concentric annuli `A` (inner) and `B` (outer) with `around(A) < across(B)`, the
internal metric on **every** `Y ⊇ B̄_S` (`S ≥` outer radius of `B`) agrees with the internal metric
on `B̄_S` for endpoints inside the inner circle of `A`. The printed factor "half" is not needed:
the excursion between the first and the last hit contains one crossing of `B`, and the arc of the
loop costs at most its length (reading note `lem-3.2#barrier-event`; harmless). The surgery is on
near-minimizing curves, not geodesics, so it applies to internal metrics of arbitrary sets.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCMetric EuclideanAnnulus aroundDist acrossDist Disconnects)
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation (pathHit_time annularPath_hit
  annularPath_hit_reverse candidate_disconnects_implies_path_hit)

/-- The internal metric only depends on the underlying points. -/
theorem internal_congr (d : LSCMetric) (Y : Set ℂ) {p q : Y × Y}
    (h1 : (p.1 : ℂ) = q.1) (h2 : (p.2 : ℂ) = q.2) : d.internal Y p = d.internal Y q := by
  obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := p
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := q
  simp only at h1 h2
  subst h1 h2
  rfl

/-- Monotonicity of internal metrics in the set. -/
theorem internal_le_of_subset (d : LSCMetric) {K Y : Set ℂ} (hKY : K ⊆ Y) (p : K × K) :
    d.internal Y (⟨p.1, hKY p.1.2⟩, ⟨p.2, hKY p.2.2⟩) ≤ d.internal K p := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP => le_iInf fun hK =>
    le_iInf fun ha => le_iInf fun hb => ?_
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hP <|
    iInf_le_of_le (fun t ht => hKY (hK t ht)) <| iInf_le_of_le ha <| iInf_le_of_le hb le_rfl

/-- `internal_le_len` with prescribed endpoint membership proofs. -/
theorem internal_le_len' (d : LSCMetric) (Y : Set ℂ) {P : ℝ → ℂ} {a b : ℝ}
    (hP : d.IsCurve P a b) (hY : ∀ t ∈ Icc a b, P t ∈ Y) {x y : ℂ} (hx : x ∈ Y) (hy : y ∈ Y)
    (hPa : P a = x) (hPb : P b = y) :
    d.internal Y (⟨x, hx⟩, ⟨y, hy⟩) ≤ d.len P a b := by
  rw [internal_congr d Y (q := (⟨P a, hY a ⟨le_rfl, hP.1⟩⟩, ⟨P b, hY b ⟨hP.1, le_rfl⟩⟩))
    hPa.symm hPb.symm]
  exact d.internal_le_len Y P a b hP hY

/-- **The surgery.** -/
theorem internal_eq_of_around_lt_across (d : LSCMetric)
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), d.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (A B : EuclideanAnnulus) (hAc : A.center = 0) (hBc : B.center = 0)
    (hAB : A.outerRadius ≤ B.innerRadius) {r S : ℝ} (hrA : r ≤ A.innerRadius)
    (hBS : B.outerRadius ≤ S) (hlt : aroundDist d A < acrossDist d B)
    {Y : Set ℂ} (hY : closedBall (0 : ℂ) S ⊆ Y) {x y : ℂ} (hx : x ∈ closedBall (0 : ℂ) r)
    (hy : y ∈ closedBall (0 : ℂ) r) (hxK : x ∈ closedBall (0 : ℂ) S)
    (hyK : y ∈ closedBall (0 : ℂ) S) :
    d.internal Y (⟨x, hY hxK⟩, ⟨y, hY hyK⟩) = d.internal (closedBall 0 S) (⟨x, hxK⟩, ⟨y, hyK⟩) := by
  set K : Set ℂ := closedBall (0 : ℂ) S with hK
  refine le_antisymm (internal_le_of_subset d hY (⟨x, hxK⟩, ⟨y, hyK⟩)) ?_
  have hA0 : 0 < A.innerRadius := A.2.1
  have hA1 : A.innerRadius < A.outerRadius := A.2.2
  have hB1 : B.innerRadius < B.outerRadius := B.2.2
  -- a separator of `A` cheaper than the crossing of `B`
  obtain ⟨π, s, s', hπ, hπA, hsep, hlen⟩ : ∃ (π : ℝ → ℂ) (s s' : ℝ), d.IsCurve π s s' ∧
      (∀ τ ∈ Icc s s', π τ ∈ A.toSet) ∧
      Disconnects (π '' Icc s s') A.innerBoundary A.outerBoundary ∧
      d.len π s s' < acrossDist d B := by
    unfold aroundDist at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨π, s, s', hπ, hY', hsep, hlen⟩ := hlt
    exact ⟨π, s, s', hπ, hY', hsep, hlen⟩
  set tr : Set ℂ := π '' Icc s s' with htr
  have htrc : IsClosed tr :=
    (isCompact_Icc.image_of_continuousOn (hcont π s s' hπ)).isClosed
  have hsep' : LQGMetric.Disconnects tr (sphere 0 A.innerRadius) (sphere 0 A.outerRadius) := by
    have := candidate_disconnects_implies_path_hit hsep
    simpa [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.outerBoundary, hAc] using this
  have hhit := annularPath_hit hA0 hA1 hsep'
  have hhitR := annularPath_hit_reverse hA0 hA1 hsep'
  have htrA : ∀ z ∈ tr, z ∈ ball (0 : ℂ) A.outerRadius := by
    rintro _ ⟨τ, hτ, rfl⟩
    have := (hπA τ hτ).1
    simpa [hAc] using this
  have hAK : A.outerRadius ≤ S := hAB.trans (hB1.le.trans hBS)
  have htrK : ∀ z ∈ tr, z ∈ K := fun z hz =>
    ball_subset_closedBall (ball_subset_ball hAK (htrA z hz))
  -- the main inequality, for every curve in `Y`
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a' => le_iInf fun b' => le_iInf fun hP =>
    le_iInf fun hPY => le_iInf fun ha => le_iInf fun hb => ?_
  have hPc : ContinuousOn P (Icc a' b') := hcont P a' b' hP
  have hab : a' ≤ b' := hP.1
  change d.internal K (⟨x, hxK⟩, ⟨y, hyK⟩) ≤ d.len P a' b'
  by_cases hstay : ∀ t ∈ Icc a' b', P t ∈ K
  · exact internal_le_len' d K hP hstay hxK hyK ha hb
  simp only [not_forall, exists_prop] at hstay
  obtain ⟨ts, hts, htsK⟩ := hstay
  have hfar : S < ‖P ts‖ := by
    simpa [hK, mem_closedBall, dist_zero_right] using htsK
  have hxA : P a' ∈ closedBall (0 : ℂ) A.innerRadius := by
    rw [ha]; exact closedBall_subset_closedBall hrA hx
  have hyA : P b' ∈ closedBall (0 : ℂ) A.innerRadius := by
    rw [hb]; exact closedBall_subset_closedBall hrA hy
  have hfarA : P ts ∈ (ball (0 : ℂ) A.outerRadius)ᶜ := by
    simp only [mem_compl_iff, mem_ball, dist_zero_right, not_lt]
    linarith
  -- the first hit before the far visit
  set T₁ : Set ℝ := Icc a' ts ∩ P ⁻¹' tr with hT₁
  have hT₁c : IsClosed T₁ := (hPc.mono (Icc_subset_Icc le_rfl hts.2)).preimage_isClosed_of_isClosed
    isClosed_Icc htrc
  have hT₁ne : T₁.Nonempty := by
    obtain ⟨u, hu, huK⟩ := pathHit_time hts.1 (hPc.mono (Icc_subset_Icc le_rfl hts.2)) hhit hxA
      hfarA
    exact ⟨u, hu, huK⟩
  have hT₁b : BddBelow T₁ := ⟨a', fun u hu => hu.1.1⟩
  set t₁ := sInf T₁ with ht₁
  have ht₁T : t₁ ∈ T₁ := hT₁c.csInf_mem hT₁ne hT₁b
  have hbefore : ∀ t ∈ Icc a' t₁, P t ∈ K := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; exact htrK _ ht₁T.2
    · by_contra hnot
      have hout : P t ∈ (ball (0 : ℂ) A.outerRadius)ᶜ := by
        intro hin
        exact hnot (ball_subset_closedBall (ball_subset_ball hAK hin))
      obtain ⟨u, hu, huK⟩ := pathHit_time ht.1 (hPc.mono (Icc_subset_Icc le_rfl
        (ht.2.trans (ht₁T.1.2.trans hts.2)))) hhit hxA hout
      have hle : t₁ ≤ u := csInf_le hT₁b ⟨⟨hu.1, hu.2.trans (ht.2.trans ht₁T.1.2)⟩, huK⟩
      linarith [hu.2]
  -- the last hit after the far visit
  set T₂ : Set ℝ := Icc ts b' ∩ P ⁻¹' tr with hT₂
  have hT₂c : IsClosed T₂ := (hPc.mono (Icc_subset_Icc hts.1 le_rfl)).preimage_isClosed_of_isClosed
    isClosed_Icc htrc
  have hT₂ne : T₂.Nonempty := by
    obtain ⟨u, hu, huK⟩ := pathHit_time hts.2 (hPc.mono (Icc_subset_Icc hts.1 le_rfl)) hhitR
      hfarA hyA
    exact ⟨u, hu, huK⟩
  have hT₂b : BddAbove T₂ := ⟨b', fun u hu => hu.1.2⟩
  set t₂ := sSup T₂ with ht₂
  have ht₂T : t₂ ∈ T₂ := hT₂c.csSup_mem hT₂ne hT₂b
  have hafter : ∀ t ∈ Icc t₂ b', P t ∈ K := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact htrK _ ht₂T.2
    · by_contra hnot
      have hout : P t ∈ (ball (0 : ℂ) A.outerRadius)ᶜ := by
        intro hin
        exact hnot (ball_subset_closedBall (ball_subset_ball hAK hin))
      obtain ⟨u, hu, huK⟩ := pathHit_time ht.2 (hPc.mono (Icc_subset_Icc
        ((hts.1.trans ht₂T.1.1).trans ht.1) le_rfl)) hhitR hout hyA
      have hle : u ≤ t₂ := le_csSup hT₂b ⟨⟨(ht₂T.1.1.trans ht.1).trans hu.1, hu.2⟩, huK⟩
      linarith [hu.1]
  have ht₁ts : t₁ ≤ ts := ht₁T.1.2
  have htst₂ : ts ≤ t₂ := ht₂T.1.1
  have ha't₁ : a' ≤ t₁ := ht₁T.1.1
  have ht₂b' : t₂ ≤ b' := ht₂T.1.2
  -- the three pieces
  have hP₁ : d.IsCurve P a' t₁ := ⟨ha't₁, hP.2.mono (Icc_subset_Icc le_rfl (ht₁ts.trans
    (htst₂.trans ht₂b')))⟩
  have hP₃ : d.IsCurve P t₂ b' := ⟨ht₂b', hP.2.mono (Icc_subset_Icc (ha't₁.trans (ht₁ts.trans
    htst₂)) le_rfl)⟩
  have hPt₁K : P t₁ ∈ K := htrK _ ht₁T.2
  have hPt₂K : P t₂ ∈ K := htrK _ ht₂T.2
  have e1 : d.internal K (⟨x, hxK⟩, ⟨P t₁, hPt₁K⟩) ≤ d.len P a' t₁ :=
    internal_le_len' d K hP₁ hbefore hxK hPt₁K ha rfl
  have e3 : d.internal K (⟨P t₂, hPt₂K⟩, ⟨y, hyK⟩) ≤ d.len P t₂ b' :=
    internal_le_len' d K hP₃ hafter hPt₂K hyK rfl hb
  -- the arc of the separator
  have e2 : d.internal K (⟨P t₁, hPt₁K⟩, ⟨P t₂, hPt₂K⟩) ≤ d.len π s s' := by
    obtain ⟨τ₁, hτ₁, hτ₁e⟩ := ht₁T.2
    obtain ⟨τ₂, hτ₂, hτ₂e⟩ := ht₂T.2
    have hπK : ∀ τ ∈ Icc s s', π τ ∈ K := fun τ hτ => htrK _ ⟨τ, hτ, rfl⟩
    rcases le_total τ₁ τ₂ with h12 | h21
    · have hc : d.IsCurve π τ₁ τ₂ := ⟨h12, hπ.2.mono (Icc_subset_Icc hτ₁.1 hτ₂.2)⟩
      calc d.internal K (⟨P t₁, hPt₁K⟩, ⟨P t₂, hPt₂K⟩)
          ≤ d.len π τ₁ τ₂ := internal_le_len' d K hc (fun τ hτ => hπK τ
              ⟨hτ₁.1.trans hτ.1, hτ.2.trans hτ₂.2⟩) hPt₁K hPt₂K hτ₁e hτ₂e
        _ ≤ d.len π s s' := LQGMetric.MetricGeometry.curveLength_mono _ hτ₁.1 hτ₂.2
    · have hc : d.IsCurve π τ₂ τ₁ := ⟨h21, hπ.2.mono (Icc_subset_Icc hτ₂.1 hτ₁.2)⟩
      rw [SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.internal_symm]
      calc d.internal K (⟨P t₂, hPt₂K⟩, ⟨P t₁, hPt₁K⟩)
          ≤ d.len π τ₂ τ₁ := internal_le_len' d K hc (fun τ hτ => hπK τ
              ⟨hτ₂.1.trans hτ.1, hτ.2.trans hτ₁.2⟩) hPt₂K hPt₁K hτ₂e hτ₁e
        _ ≤ d.len π s s' := LQGMetric.MetricGeometry.curveLength_mono _ hτ₂.1 hτ₁.2
  -- the excursion contains a crossing of `B`
  have e4 : acrossDist d B ≤ d.len P t₁ t₂ := by
    have hf : ContinuousOn (fun t => dist (P t) 0) (Icc t₁ ts) :=
      continuous_dist.comp_continuousOn
        ((hPc.mono (Icc_subset_Icc ha't₁ hts.2)).prodMk continuousOn_const)
    have hPt₁r : dist (P t₁) 0 ≤ B.innerRadius :=
      (le_of_lt (by simpa [mem_ball] using htrA _ ht₁T.2)).trans hAB
    have hPtsr : B.outerRadius ≤ dist (P ts) 0 := by
      rw [dist_zero_right]; linarith
    obtain ⟨σ, τ, h1σ, hστ, hτs, hσr, hτr, -⟩ :=
      LQGMetric.RectCross.exists_sub_crossing ht₁ts hf hB1.le hPt₁r hPtsr
    have hcross : acrossDist d B ≤ d (P σ, P τ) := by
      refine iInf₂_le_of_le (P σ) ?_ (iInf₂_le (P τ) ?_)
      · change P σ ∈ sphere B.center B.innerRadius
        rw [mem_sphere, hBc]; exact hσr
      · change P τ ∈ sphere B.center B.outerRadius
        rw [mem_sphere, hBc]; exact hτr
    calc acrossDist d B ≤ d (P σ, P τ) := hcross
      _ ≤ d.len P σ τ := d.edist_le_len P hστ
      _ ≤ d.len P t₁ t₂ := LQGMetric.MetricGeometry.curveLength_mono _ h1σ (hτs.trans htst₂)
  -- assembly
  have htri : d.internal K (⟨x, hxK⟩, ⟨y, hyK⟩) ≤
      d.internal K (⟨x, hxK⟩, ⟨P t₁, hPt₁K⟩) + (d.internal K (⟨P t₁, hPt₁K⟩, ⟨P t₂, hPt₂K⟩) +
        d.internal K (⟨P t₂, hPt₂K⟩, ⟨y, hyK⟩)) :=
    (SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.internal_triangle d K
      ⟨x, hxK⟩ ⟨P t₁, hPt₁K⟩ ⟨y, hyK⟩).trans (by
        gcongr
        exact SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.internal_triangle d K
          ⟨P t₁, hPt₁K⟩ ⟨P t₂, hPt₂K⟩ ⟨y, hyK⟩)
  have hsplit : d.len P a' b' = d.len P a' t₁ + d.len P t₁ t₂ + d.len P t₂ b' := by
    change LQGMetric.MetricGeometry.curveLength _ a' b' = LQGMetric.MetricGeometry.curveLength _ a' t₁ +
      LQGMetric.MetricGeometry.curveLength _ t₁ t₂ + LQGMetric.MetricGeometry.curveLength _ t₂ b'
    rw [LQGMetric.MetricGeometry.curveLength_add _ ha't₁ (ht₁ts.trans htst₂),
      LQGMetric.MetricGeometry.curveLength_add _ (ha't₁.trans (ht₁ts.trans htst₂)) ht₂b']
  calc d.internal K (⟨x, hxK⟩, ⟨y, hyK⟩)
      ≤ d.internal K (⟨x, hxK⟩, ⟨P t₁, hPt₁K⟩) + (d.internal K (⟨P t₁, hPt₁K⟩, ⟨P t₂, hPt₂K⟩) +
          d.internal K (⟨P t₂, hPt₂K⟩, ⟨y, hyK⟩)) := htri
    _ ≤ d.len P a' t₁ + (d.len P t₁ t₂ + d.len P t₂ b') := by
        gcongr
        exact e2.trans (hlen.le.trans e4)
    _ = d.len P a' b' := by rw [hsplit, add_assoc]

end SupercriticalConformalCovariance.Tangent
