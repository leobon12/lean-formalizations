import SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.RatioRadial




 






set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings

 


theorem internal_hit_separator_prefix_on_trace
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    {P π : ℝ → ℂ} {T q s t r R L : ℝ} {z : ℂ}
    (hq0 : 0 < q) (hqT : q < T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (hrR : r < R)
    (h0 : R ≤ dist (P 0) z) (hq : dist (P q) z ≤ r)
    (hT : R ≤ dist (P T) z)
    (hπ : D.IsCurve π s t) (hπK : MapsTo π (Icc s t) K)
    (hsep : Disconnects (π '' Icc s t) (sphere z r) (sphere z R))
    (hL : 0 ≤ L) (hlen : D.len π s t = ENNReal.ofReal L) :
    ∃ u v : ℝ, 0 ≤ u ∧ u ≤ q ∧ q ≤ v ∧ v ≤ T ∧
      P u ∈ π '' Icc s t ∧ P v ∈ π '' Icc s t ∧ q - u ≤ L := by
  have hpc : ContinuousOn P (Icc 0 T) :=
    hP.continuousOn_of_mapsTo hK hPK
  have hsep' : LQGMetric.Disconnects (π '' Icc s t)
      (sphere z r) (sphere z R) :=
    (disconnects_iff_lqgMetric_disconnects hπ.isClosed_image).1 hsep
  have hfor : LQGMetric.Disconnects (π '' Icc s t)
      (closedBall z r) (ball z R)ᶜ :=
    LQGMetric.Disconnects.closedBall_compl_ball hrR.le hsep'
  have h0q : Icc (0 : ℝ) q ⊆ Icc 0 T :=
    Icc_subset_Icc le_rfl hqT.le
  have hqT' : Icc q T ⊆ Icc 0 T :=
    Icc_subset_Icc hq0.le le_rfl
  have h0out : P 0 ∈ (ball z R)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, not_lt] using h0
  have hTout : P T ∈ (ball z R)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, not_lt] using hT
  have hqin : P q ∈ closedBall z r := by
    simpa only [mem_closedBall] using hq
  obtain ⟨u, hu, huJ⟩ :=
    TwoScale.Mesh.pathHit_time hq0.le (hpc.mono h0q) hfor.symm h0out hqin
  obtain ⟨v, hv, hvJ⟩ :=
    TwoScale.Mesh.pathHit_time hqT.le (hpc.mono hqT') hfor hqin hTout
  have huT : u ∈ Icc 0 T := h0q hu
  have hvT : v ∈ Icc 0 T := hqT' hv
  have huv : u ≤ v := hu.2.trans hv.1
  have hcost := TwoScale.Mesh.internal_trace_le_len D K π hπ hπK huJ hvJ
  rw [hgeo u v huT hvT huv, hlen] at hcost
  have hreal : v - u ≤ L := (ENNReal.ofReal_le_ofReal_iff hL).mp hcost
  exact ⟨u, v, hu.1, hu.2, hv.1, hv.2, huJ, hvJ,
    by linarith [hu.2, hv.1]⟩

 


theorem sum_inner_acrossDist_le_aroundDist
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    (A : EuclideanAnnulus) (hAK : A.toSet ⊆ K)
    (base : Ioi (0 : ℝ)) (n k : ℕ)
    {P : ℝ → ℂ} {T q : ℝ}
    (hq0 : 0 < q) (hqT : q < T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (h0 : A.outerRadius ≤ dist (P 0) A.center)
    (hqA : dist (P q) A.center ≤ A.innerRadius)
    (hT : A.outerRadius ≤ dist (P T) A.center)
    (hfirst : 2 * (TwoScale.Ratio.ratioRadius base k : ℝ) ≤ A.innerRadius)
    (hlast : dist (P q) A.center ≤
      (TwoScale.Ratio.ratioRadius base (k + n - 1) : ℝ)) :
    (∑ j ∈ Finset.Ico k (k + n),
      acrossDist D (BiLipschitz.OneScale.crossingAt A.center (TwoScale.Ratio.ratioRadius base j))) ≤
      aroundDist D A := by
  unfold aroundDist
  apply le_iInf
  intro π
  apply le_iInf
  intro s
  apply le_iInf
  intro t
  apply le_iInf
  intro hπ
  apply le_iInf
  intro hY
  apply le_iInf
  intro hsep
  by_cases hfin : D.len π s t = ∞
  · simp only [hfin, le_top]
  · have hann : π '' Icc s t ⊆
        {w | A.innerRadius < dist w A.center ∧
          dist w A.center < A.outerRadius} := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := hw
      have hA : π v ∈ A.toSet := hY v hv
      change π v ∈ ball A.center A.outerRadius ∧
        π v ∉ closure (ball A.center A.innerRadius) at hA
      have hr : 0 < A.innerRadius := A.2.1
      rw [closure_ball A.center (ne_of_gt hr)] at hA
      exact ⟨lt_of_not_ge (by simpa only [mem_closedBall] using hA.2),
        by simpa only [mem_ball] using hA.1⟩
    have hπK : MapsTo π (Icc s t) K :=
      fun v hv => hAK (hY v hv)
    have hlen : D.len π s t =
        ENNReal.ofReal (D.len π s t).toReal :=
      (ENNReal.ofReal_toReal hfin).symm
    obtain ⟨u, v, hu0, huq, _, _, huJ, _, hcost⟩ :=
      internal_hit_separator_prefix_on_trace D K hK
        hq0 hqT hP hPK hgeo A.2.2 h0 hqA hT
        hπ hπK hsep ENNReal.toReal_nonneg hlen
    have huAnn := hann huJ
    have hrad : 2 * (TwoScale.Ratio.ratioRadius base k : ℝ) ≤
        dist (P u) A.center := hfirst.trans huAnn.1.le
    have hsum := sum_ratio_acrossDist_le_internal_geodesic_time
      D K hK A.center base n k hu0 huq hqT.le hP hPK hgeo hrad hlast
    calc
      (∑ j ∈ Finset.Ico k (k + n),
        acrossDist D (BiLipschitz.OneScale.crossingAt A.center (TwoScale.Ratio.ratioRadius base j)))
          ≤ ENNReal.ofReal (q - u) := hsum
      _ ≤ ENNReal.ofReal (D.len π s t).toReal :=
        ENNReal.ofReal_le_ofReal hcost
      _ = D.len π s t := ENNReal.ofReal_toReal hfin

 

theorem ratio_across_tail_le_aroundDist
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    (z : ℂ) (base : Ioi (0 : ℝ))
    (i N : ℕ) (hiN : i < N)
    (hAK : (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)).toSet ⊆ K)
    {P : ℝ → ℂ} {T q : ℝ}
    (hq0 : 0 < q) (hqT : q < T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (h0 : 2 * (TwoScale.Ratio.ratioRadius base i : ℝ) ≤ dist (P 0) z)
    (hq : dist (P q) z ≤ (TwoScale.Ratio.ratioRadius base N : ℝ))
    (hT : 2 * (TwoScale.Ratio.ratioRadius base i : ℝ) ≤ dist (P T) z) :
    (∑ j ∈ Finset.Ioc i N,
      acrossDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j))) ≤
      aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)) := by
  let A := BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)
  have hcenter : A.center = z := by
    simp only [A, BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape,
      Positivity.Witnesses.annulusTranslate, EuclideanAnnulus.dilate,
      EuclideanAnnulus.center, smul_zero, zero_add]
  have hinner : A.innerRadius = (TwoScale.Ratio.ratioRadius base i : ℝ) := by
    simp only [A, BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape,
      Positivity.Witnesses.annulusTranslate, EuclideanAnnulus.dilate,
      EuclideanAnnulus.innerRadius, mul_one]
  have houter : A.outerRadius = 2 * (TwoScale.Ratio.ratioRadius base i : ℝ) := by
    simp only [A, BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape,
      Positivity.Witnesses.annulusTranslate, EuclideanAnnulus.dilate,
      EuclideanAnnulus.outerRadius, mul_comm]
  have hqA : dist (P q) A.center ≤ A.innerRadius := by
    have hm := ratioRadius_antitone base (Nat.le_of_lt hiN)
    rw [hcenter, hinner]
    exact hq.trans hm
  have hfirst : 2 * (TwoScale.Ratio.ratioRadius base (i + 1) : ℝ) ≤ A.innerRadius :=
    hinner ▸ ratioRadius_sep base i
  have hlast : dist (P q) A.center ≤
      (TwoScale.Ratio.ratioRadius base ((i + 1) + (N - i) - 1) : ℝ) := by
    rw [hcenter]
    simpa only [show (i + 1) + (N - i) - 1 = N by omega] using hq
  have h0A : A.outerRadius ≤ dist (P 0) A.center := by
    simpa only [houter, hcenter] using h0
  have hTA : A.outerRadius ≤ dist (P T) A.center := by
    simpa only [houter, hcenter] using hT
  have hsum := sum_inner_acrossDist_le_aroundDist D K hK A hAK
    base (N - i) (i + 1) hq0 hqT hP hPK hgeo h0A hqA hTA
    hfirst hlast
  have htop : (i + 1) + (N - i) = N + 1 := by omega
  have hset : Finset.Ico (i + 1) ((i + 1) + (N - i)) =
      Finset.Ioc i N := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_Ioc, htop]
    omega
  rw [hset, hcenter] at hsum
  exact hsum

 


theorem selected_ratio_around_sum_le_outer
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    (z : ℂ) (base : Ioi (0 : ℝ))
    (i N : ℕ) (hiN : i < N)
    (hAK : (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)).toSet ⊆ K)
    {P : ℝ → ℂ} {T q : ℝ}
    (hq0 : 0 < q) (hqT : q < T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (h0 : 2 * (TwoScale.Ratio.ratioRadius base i : ℝ) ≤ dist (P 0) z)
    (hq : dist (P q) z ≤ (TwoScale.Ratio.ratioRadius base N : ℝ))
    (hT : 2 * (TwoScale.Ratio.ratioRadius base i : ℝ) ≤ dist (P T) z)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ioc i N) (c : ℝ≥0∞)
    (hgood : ∀ j ∈ S,
      aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)) ≤
        c * acrossDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j))) :
    (∑ j ∈ S,
      aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j))) ≤
      c * aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)) := by
  calc
    (∑ j ∈ S,
      aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)))
        ≤ ∑ j ∈ S, c *
          acrossDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)) :=
            Finset.sum_le_sum hgood
    _ = c * ∑ j ∈ S,
          acrossDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)) := by
            rw [Finset.mul_sum]
    _ ≤ c * ∑ j ∈ Finset.Ioc i N,
          acrossDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base j)) := by
            gcongr
    _ ≤ c * aroundDist D (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)) := by
          gcongr
          exact ratio_across_tail_le_aroundDist D K hK z base i N hiN hAK
            hq0 hqT hP hPK hgeo h0 hq hT


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings
