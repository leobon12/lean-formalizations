import SupercriticalLFPPAS.Det.SeparatingPaths
import SupercriticalLQGUniqueness.B2.Polylog.P3PaidGeometry

/-!
# Lemma 3.4′ with field-local across costs

The form of Lemma 3.4 consumed by Lemma 3.5 (packet P35; planning audit SB2, Details D1 and
item M1). Compared with the landed `SupercriticalLFPPAS.d1_lemma_3_4`:

* the across costs are the field-local `B2.Polylog.acrossIn` costs (curves in the closed annulus
  `Ā_{r,2r}(c)`), which dominate the ambient ones; the one-annulus events of Lemma 3.5 bound
  exactly these local costs from below, so this is the form whose hypotheses those events give;
* the geodesic is a Euclidean-continuous curve on an arbitrary parameter interval `[a, b]`; the
  separating curves are Euclidean-continuous because their images are bounded, so no continuity of
  the identity map from the metric topology is needed;
* only the source metric enters the ratio hypotheses `W_i ≤ C Y_i` (`i < n - 1`), and the target
  metric enters only through the innermost around cost, with its own constant `B`
  (SB2 M1: the remaining hypotheses of the printed lemma are unused).

Conclusion: `Z ≤ (B / 2) (1 + 2/C)^{-(n-1)} len(I; d)`, written `B / (2 (1 + 2/C)^(n-1))`.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Separating

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn acrossIn_le_len_of_crossing)

/-- Reversing the parameter of a metric curve on `[s, t]` gives a metric curve. -/
theorem p35_isCurve_reverse (D : LSCMetric) {P : ℝ → ℂ} {s t : ℝ} (hP : D.IsCurve P s t) :
    D.IsCurve (fun u => P (s + t - u)) s t := by
  refine ⟨hP.1, ?_⟩
  have hφ : ContinuousOn (fun u : ℝ => s + t - u) (Icc s t) := by fun_prop
  have hmaps : MapsTo (fun u : ℝ => s + t - u) (Icc s t) (Icc s t) := by
    intro u hu
    simp only [mem_Icc] at hu ⊢
    constructor <;> linarith
  exact hP.2.comp hφ hmaps

/-- Reversing the parameter of a Euclidean-continuous curve on `[s, t]`. -/
theorem p35_continuousOn_reverse {P : ℝ → ℂ} {s t : ℝ} (hP : ContinuousOn P (Icc s t)) :
    ContinuousOn (fun u => P (s + t - u)) (Icc s t) := by
  have hφ : ContinuousOn (fun u : ℝ => s + t - u) (Icc s t) := by fun_prop
  have hmaps : MapsTo (fun u : ℝ => s + t - u) (Icc s t) (Icc s t) := by
    intro u hu
    simp only [mem_Icc] at hu ⊢
    constructor <;> linarith
  exact hP.comp hφ hmaps

/-- **An outer-to-inner crossing pays the local across cost.** -/
theorem p35_acrossIn_le_len_of_crossing_rev (D : LSCMetric) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    {P : ℝ → ℂ} {s t : ℝ} (hP : D.IsCurve P s t) (hPc : ContinuousOn P (Icc s t))
    (hs : 2 * ρ ≤ dist (P s) c) (ht : dist (P t) c ≤ ρ) :
    acrossIn D c ρ (2 * ρ) ≤ D.len P s t := by
  have hQ := p35_isCurve_reverse D hP
  have hQc := p35_continuousOn_reverse hPc
  have h := acrossIn_le_len_of_crossing D c hρ hQ hQc
    (by simp only [add_sub_cancel_left, ← dist_eq_norm]; exact ht)
    (by simp only [add_sub_cancel_right, ← dist_eq_norm]; exact hs)
  rwa [d1_len_reverse D P hP.1] at h

/-- Nested crossing annuli (all indices separated by a factor two) are paid by the length of a
curve running from the outer circle of the first to the inner circle of the last, with local
across costs. -/
theorem p35_across_sum_le_len (D : LSCMetric) (P : ℝ → ℂ) (c : ℂ) (r : ℕ → ℝ)
    (hr : ∀ j, 0 < r j) (hsep : ∀ j, 2 * r (j + 1) ≤ r j) {n k : ℕ} {a b : ℝ}
    (hab : a ≤ b) (hP : D.IsCurve P a b) (hPc : ContinuousOn P (Icc a b))
    (ha : 2 * r k ≤ dist (P a) c) (hb : dist (P b) c ≤ r (k + n - 1)) :
    (∑ j ∈ Finset.Ico k (k + n), acrossIn D c (r j) (2 * r j)) ≤ D.len P a b := by
  let g : ℝ → ℝ := fun t => dist (P t) c
  have hmono : Antitone r := by
    apply antitone_nat_of_succ_le
    intro j
    have hj := hr (j + 1)
    linarith [hsep j]
  have hg : ContinuousOn g (Icc a b) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  have hcross :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.ordered_crossings_of_nested
      g r b hr hsep hmono n k a hab hg ha hb
  apply d1_sum_cost_le_len_of_ordered D P g r b a b
    (fun j => acrossIn D c (r j) (2 * r j)) _ n k a le_rfl le_rfl hcross
  intro j s t has hst htb hs ht
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  exact p35_acrossIn_le_len_of_crossing_rev D c (hr j) ⟨hst, hP.2.mono hsub⟩
    (hPc.mono hsub) hs.ge ht.le

/-- The finite radii of the lemma form an initial segment of the geometric extension used by
`p35_across_sum_le_len`. -/
theorem p35_finite_across_sum_le_len (D : LSCMetric) (P : ℝ → ℂ) (c : ℂ) (n : ℕ) (r : ℕ → ℝ)
    (hn : 0 < n) (hr : ∀ j, 0 < r j) (hstep : ∀ j, j + 1 < n → r (j + 1) < r j / 4)
    {k m : ℕ} {a b : ℝ} (hkm : k + m ≤ n) (hm : 0 < m) (hab : a ≤ b)
    (hP : D.IsCurve P a b) (hPc : ContinuousOn P (Icc a b))
    (ha : 2 * r k ≤ dist (P a) c) (hb : dist (P b) c ≤ r (k + m - 1)) :
    (∑ j ∈ Finset.Ico k (k + m), acrossIn D c (r j) (2 * r j)) ≤ D.len P a b := by
  let R := d1ExtendRadii n r hn
  have hRpos : ∀ j, 0 < R j := d1ExtendRadii_pos n r hn (fun j _ => hr j)
  have hRsep : ∀ j, 2 * R (j + 1) ≤ R j :=
    d1ExtendRadii_sep n r hn (fun j _ => hr j) hstep
  have hk : k < n := by omega
  have hlast : k + m - 1 < n := by omega
  have haR : 2 * R k ≤ dist (P a) c := by
    have hRk : R k = r k := d1ExtendRadii_eq n r hn hk
    rw [hRk]
    exact ha
  have hbR : dist (P b) c ≤ R (k + m - 1) := by
    have hRlast : R (k + m - 1) = r (k + m - 1) := d1ExtendRadii_eq n r hn hlast
    rw [hRlast]
    exact hb
  have hsum := p35_across_sum_le_len D P c R hRpos hRsep hab hP hPc haR hbR
  calc
    (∑ j ∈ Finset.Ico k (k + m), acrossIn D c (r j) (2 * r j))
        = ∑ j ∈ Finset.Ico k (k + m), acrossIn D c (R j) (2 * R j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjn : j < n := by
            simp only [Finset.mem_Ico] at hj
            omega
          have hRj : R j = r j := d1ExtendRadii_eq n r hn hjn
          rw [hRj]
    _ ≤ D.len P a b := hsum

/-- The part of the geodesic between two hits of a separating curve of the `i`th outer annulus
pays twice the local across costs of every strictly inner crossing annulus; hence that sum is at
most the around cost. -/
theorem p35_twice_inner_across_sum_le_aroundDist (D : LSCMetric) (c : ℂ) (n : ℕ) (hn : 0 < n)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hstep : ∀ j, j + 1 < n → r (j + 1) < r j / 4)
    (i : ℕ) (hi : i + 1 < n) {P : ℝ → ℂ} {a b q : ℝ} (haq : a < q) (hqb : q < b)
    (hP : D.IsCurve P a b) (hPc : ContinuousOn P (Icc a b))
    (hgeo : ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b → u ≤ v → D.len P u v = D (P u, P v))
    (h0 : 3 * r i ≤ dist (P a) c) (hq : dist (P q) c ≤ r (n - 1))
    (hT : 3 * r i ≤ dist (P b) c) :
    (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico (i + 1) n, acrossIn D c (r j) (2 * r j)) ≤
      aroundDist D (d1OuterAnnulus c r hr i) := by
  let A := d1OuterAnnulus c r hr i
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
  intro hπA
  apply le_iInf
  intro hsep
  have hsep' : LQGMetric.Disconnects (π '' Icc s t)
      (Metric.sphere c (2 * r i)) (Metric.sphere c (3 * r i)) := by
    have hsepL : LQGMetric.Disconnects (π '' Icc s t)
        A.innerBoundary A.outerBoundary :=
      (SupercriticalLQGUniqueness.disconnects_iff_lqgMetric_disconnects
        hπ.isClosed_image).1 hsep
    simpa [A, d1OuterAnnulus, d1Annulus,
      SupercriticalLQGUniqueness.EuclideanAnnulus.center,
      SupercriticalLQGUniqueness.EuclideanAnnulus.innerRadius,
      SupercriticalLQGUniqueness.EuclideanAnnulus.outerRadius,
      SupercriticalLQGUniqueness.EuclideanAnnulus.innerBoundary,
      SupercriticalLQGUniqueness.EuclideanAnnulus.outerBoundary] using hsepL
  have hqInner : dist (P q) c ≤ 2 * r i := by
    have hri : r (n - 1) ≤ r i :=
      d1_radius_le_prefix n r hr hstep (by omega) (by omega)
    have hipos := hr i
    linarith
  have h0Outer : P a ∉ Metric.ball c (3 * r i) := by
    simpa only [Metric.mem_ball, not_lt] using h0
  have hqClosed : P q ∈ Metric.closedBall c (2 * r i) := by
    simpa only [Metric.mem_closedBall] using hqInner
  have hTOuter : P b ∉ Metric.ball c (3 * r i) := by
    simpa only [Metric.mem_ball, not_lt] using hT
  have hPleft : ContinuousOn P (Icc a q) := hPc.mono (Icc_subset_Icc le_rfl hqb.le)
  have hPright : ContinuousOn P (Icc q b) := hPc.mono (Icc_subset_Icc haq.le le_rfl)
  -- the two hits of the separating curve, on `[a, q]` and on `[q, b]`
  obtain ⟨u, hu, huTrace⟩ :=
    SupercriticalLQGUniqueness.B2.PfeWeyl.outside_to_inside_hits_separator
      haq.le hPleft (by linarith [hr i]) hsep' h0Outer hqClosed
  obtain ⟨v, hv, hvTrace⟩ :=
    SupercriticalLQGUniqueness.B2.PfeWeyl.inside_to_outside_hits_separator
      hqb.le hPright (by linarith [hr i]) hsep' hqClosed hTOuter
  have huT : u ∈ Icc a b := ⟨hu.1, hu.2.trans hqb.le⟩
  have hvT : v ∈ Icc a b := ⟨haq.le.trans hv.1, hv.2⟩
  have huv : u ≤ v := hu.2.trans hv.1
  have huTraceMem : P u ∈ π '' Icc s t := huTrace
  have hvTraceMem : P v ∈ π '' Icc s t := hvTrace
  obtain ⟨su, hsu, hPu⟩ := huTrace
  obtain ⟨sv, hsv, hPv⟩ := hvTrace
  have hPuA : P u ∈ A.toSet := by rw [← hPu]; exact hπA su hsu
  have hPvA : P v ∈ A.toSet := by rw [← hPv]; exact hπA sv hsv
  have hPuRadius : 2 * r i ≤ dist (P u) c := by
    rw [SupercriticalLQGUniqueness.EuclideanAnnulus.toSet_eq] at hPuA
    simpa [A, d1OuterAnnulus, d1Annulus,
      SupercriticalLQGUniqueness.EuclideanAnnulus.innerRadius,
      SupercriticalLQGUniqueness.EuclideanAnnulus.center] using hPuA.1.le
  have hPvRadius : 2 * r i ≤ dist (P v) c := by
    rw [SupercriticalLQGUniqueness.EuclideanAnnulus.toSet_eq] at hPvA
    simpa [A, d1OuterAnnulus, d1Annulus,
      SupercriticalLQGUniqueness.EuclideanAnnulus.innerRadius,
      SupercriticalLQGUniqueness.EuclideanAnnulus.center] using hPvA.1.le
  let Q : ℝ → ℂ := fun t => P (q + v - t)
  have hQcurve : D.IsCurve Q q v :=
    p35_isCurve_reverse D ⟨hv.1, hP.2.mono (Icc_subset_Icc haq.le hv.2)⟩
  have hQcont : ContinuousOn Q (Icc q v) :=
    p35_continuousOn_reverse (hPc.mono (Icc_subset_Icc haq.le hv.2))
  have hQq : Q q = P v := by
    dsimp [Q]
    congr 1
    ring
  have hQv : Q v = P q := by
    dsimp [Q]
    congr 1
    ring
  have hscale : 2 * r (i + 1) ≤ 2 * r i := by
    have hs := hstep i hi
    have hp := hr i
    nlinarith
  have hcount : i + 1 + (n - (i + 1)) = n := by omega
  have htailIdx : i + 1 + (n - (i + 1)) - 1 = n - 1 := by omega
  have hPsegLeft : ContinuousOn P (Icc u q) := hPc.mono (Icc_subset_Icc hu.1 hqb.le)
  have hPcurveLeft : D.IsCurve P u q := ⟨hu.2, hP.2.mono (Icc_subset_Icc hu.1 hqb.le)⟩
  have hleft := p35_finite_across_sum_le_len D P c n r hn hr hstep
    (k := i + 1) (m := n - (i + 1)) (by omega) (by omega)
    hu.2 hPcurveLeft hPsegLeft
    (hscale.trans hPuRadius) (by simpa [htailIdx] using hq)
  have hright := p35_finite_across_sum_le_len D Q c n r hn hr hstep
    (k := i + 1) (m := n - (i + 1)) (by omega) (by omega)
    hv.1 hQcurve hQcont
    (by simpa [hQq] using hscale.trans hPvRadius)
    (by simpa [hQv, htailIdx] using hq)
  have hrightLen : D.len Q q v = D.len P q v := by
    dsimp [Q]
    exact d1_len_reverse D P hv.1
  have htwice :
      (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico (i + 1) n, acrossIn D c (r j) (2 * r j)) ≤
        D.len P u v := by
    have hleft' :
        (∑ j ∈ Finset.Ico (i + 1) n, acrossIn D c (r j) (2 * r j)) ≤ D.len P u q := by
      simpa [hcount] using hleft
    have hright' :
        (∑ j ∈ Finset.Ico (i + 1) n, acrossIn D c (r j) (2 * r j)) ≤ D.len P q v := by
      simpa [hrightLen, hcount] using hright
    calc
      _ = (∑ j ∈ Finset.Ico (i + 1) n, acrossIn D c (r j) (2 * r j)) +
          (∑ j ∈ Finset.Ico (i + 1) n, acrossIn D c (r j) (2 * r j)) := by
            rw [two_mul]
      _ ≤ D.len P u q + D.len P q v := add_le_add hleft' hright'
      _ = D.len P u v :=
        (SupercriticalLQGUniqueness.B2.PfeLocal.lsc_len_add D P hu.2 hv.1).symm
  have htrace := SupercriticalLQGUniqueness.Uniqueness.TwoScale.Transfer.trace_pair_le_len
    D π huTraceMem hvTraceMem
  have hgeoUV := hgeo u v huT hvT huv
  have hlenBound : D.len P u v ≤ D.len π s t := hgeoUV ▸ htrace
  exact htwice.trans hlenBound

/-- **Lemma 3.4′ (separating paths, local across costs).** Let `r₀ > 4 r₁ > ⋯ > 4^{n-1} r_{n-1}`
(0-indexed), `Y_i := acrossIn d c r_i (2 r_i)` the local across cost of `Ā_{r_i,2r_i}(c)` and
`W_i := d(around A_{2r_i,3r_i}(c))`. If `W_i ≤ C Y_i` for `i < n - 1` and the target around cost of
the innermost annulus satisfies `Z ≤ B Y_{n-1}`, then for every Euclidean-continuous `d`-geodesic
segment `P` on `[a, b]` with endpoints outside `B_{3r₀}(c)` which visits `B̄_{r_{n-1}}(c)`,
`Z ≤ (B / 2) (1 + 2/C)^{-(n-1)} len(P; d)`. -/
theorem p35_lemma_3_4_in (d d' : LSCMetric) (c : ℂ) (n : ℕ) (hn : 0 < n) (C B : ℝ)
    (hC : 0 < C) (hB : 0 < B) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hstep : ∀ i, i + 1 < n → r (i + 1) < r i / 4)
    (hW : ∀ i, i + 1 < n →
      aroundDist d (d1OuterAnnulus c r hr i) ≤ ENNReal.ofReal C * acrossIn d c (r i) (2 * r i))
    (hZ : aroundDist d' (d1OuterAnnulus c r hr (n - 1)) ≤
      ENNReal.ofReal B * acrossIn d c (r (n - 1)) (2 * r (n - 1)))
    {P : ℝ → ℂ} {a b : ℝ} (hP : d.IsCurve P a b) (hPc : ContinuousOn P (Icc a b))
    (hgeo : ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b → u ≤ v → d.len P u v = d (P u, P v))
    (hlen : d.len P a b < ⊤)
    (h0 : 3 * r 0 ≤ dist (P a) c) (hT : 3 * r 0 ≤ dist (P b) c)
    (hvisit : ∃ q ∈ Icc a b, dist (P q) c ≤ r (n - 1)) :
    aroundDist d' (d1OuterAnnulus c r hr (n - 1)) ≤
      ENNReal.ofReal (B / (2 * (1 + 2 / C) ^ (n - 1))) * d.len P a b := by
  let Y : ℕ → ℝ≥0∞ := fun i => acrossIn d c (r i) (2 * r i)
  let S : ℕ → ℝ := fun i => ∑ j ∈ Finset.Ico i n, (Y j).toReal
  let y : ℕ → ℝ := fun i => (Y i).toReal
  obtain ⟨q, hq, hqRadius⟩ := hvisit
  have hlast0 : r (n - 1) ≤ r 0 := d1_radius_le_prefix n r hr hstep (by omega) (by omega)
  have hr0 : 0 < r 0 := hr 0
  have haq : a < q := by
    rcases lt_or_eq_of_le hq.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hqRadius
      linarith
  have hqb : q < b := by
    rcases lt_or_eq_of_le hq.2 with h | h
    · exact h
    · exfalso
      rw [h] at hqRadius
      linarith
  have hleft := p35_finite_across_sum_le_len d P c n r hn hr hstep
    (k := 0) (m := n) (by omega) hn hq.1
    ⟨hq.1, hP.2.mono (Icc_subset_Icc le_rfl hq.2)⟩
    (hPc.mono (Icc_subset_Icc le_rfl hq.2))
    (by linarith) (by rw [zero_add]; exact hqRadius)
  let Q : ℝ → ℂ := fun t => P (q + b - t)
  have hQcurve : d.IsCurve Q q b :=
    p35_isCurve_reverse d ⟨hq.2, hP.2.mono (Icc_subset_Icc hq.1 le_rfl)⟩
  have hQcont : ContinuousOn Q (Icc q b) :=
    p35_continuousOn_reverse (hPc.mono (Icc_subset_Icc hq.1 le_rfl))
  have hQq : Q q = P b := by
    dsimp [Q]
    congr 1
    ring
  have hQb : Q b = P q := by
    dsimp [Q]
    congr 1
    ring
  have hright := p35_finite_across_sum_le_len d Q c n r hn hr hstep
    (k := 0) (m := n) (by omega) hn hq.2 hQcurve hQcont
    (by rw [hQq]; linarith) (by rw [hQb, zero_add]; exact hqRadius)
  have hbaseEn : (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico 0 n, Y j) ≤ d.len P a b := by
    have hleft' : (∑ j ∈ Finset.Ico 0 n, Y j) ≤ d.len P a q := by
      simpa [Y] using hleft
    have hright' : (∑ j ∈ Finset.Ico 0 n, Y j) ≤ d.len P q b := by
      have hrev : d.len Q q b = d.len P q b := by
        dsimp [Q]
        exact d1_len_reverse d P hq.2
      simpa [Y, hrev] using hright
    calc
      (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico 0 n, Y j) =
          (∑ j ∈ Finset.Ico 0 n, Y j) + (∑ j ∈ Finset.Ico 0 n, Y j) := by rw [two_mul]
      _ ≤ d.len P a q + d.len P q b := add_le_add hleft' hright'
      _ = d.len P a b :=
        (SupercriticalLQGUniqueness.B2.PfeLocal.lsc_len_add d P hq.1 hq.2).symm
  have hsumFinite0 : (∑ j ∈ Finset.Ico 0 n, Y j) < ⊤ := by
    have h2 : (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico 0 n, Y j) < ⊤ := lt_of_le_of_lt hbaseEn hlen
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at h2
    simp at h2
  have hYfinite : ∀ i < n, Y i < ⊤ := by
    intro i hi
    exact ENNReal.sum_lt_top.1 hsumFinite0 i (by simp only [Finset.mem_Ico]; omega)
  have hYsumFinite : ∀ a b : ℕ, b ≤ n → (∑ j ∈ Finset.Ico a b, Y j) < ⊤ := by
    intro a b hb
    apply ENNReal.sum_lt_top.2
    intro j hj
    have hjn : j < n := by
      simp only [Finset.mem_Ico] at hj
      omega
    exact hYfinite j hjn
  have hsumToReal : ∀ a b : ℕ, b ≤ n →
      (∑ j ∈ Finset.Ico a b, Y j).toReal = ∑ j ∈ Finset.Ico a b, (Y j).toReal := by
    intro a b hb
    rw [ENNReal.toReal_sum]
    intro j hj
    have hjn : j < n := by
      simp only [Finset.mem_Ico] at hj
      omega
    exact (hYfinite j hjn).ne
  have hbaseReal : 2 * S 0 ≤ (d.len P a b).toReal := by
    have hbaseFinite : (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico 0 n, Y j) < ⊤ :=
      ENNReal.mul_lt_top (by simp) (hYsumFinite 0 n le_rfl)
    have hreal := (ENNReal.toReal_le_toReal hbaseFinite.ne hlen.ne).2 hbaseEn
    have hprod : ((2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico 0 n, Y j)).toReal = 2 * S 0 := by
      rw [ENNReal.toReal_mul, hsumToReal 0 n le_rfl]
      simp [S]
    rw [hprod] at hreal
    exact hreal
  have hSsplit : ∀ i < n - 1, S i = y i + S (i + 1) := by
    intro i hi
    have hsum := Finset.sum_eq_sum_Ico_succ_bot (show i < n by omega) (fun j => (Y j).toReal)
    simpa [S, y] using hsum
  have hrealTail : ∀ i < n - 1, 2 * S (i + 1) ≤ C * y i := by
    intro i hi
    have hi' : i < n := by omega
    have hri0 : r i ≤ r 0 := d1_radius_le_prefix n r hr hstep (Nat.zero_le i) hi'
    have htailEn := p35_twice_inner_across_sum_le_aroundDist d c n hn r hr hstep
      i (by omega) haq hqb hP hPc hgeo (by linarith) hqRadius (by linarith)
    have htail : (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico (i + 1) n, Y j) ≤ ENNReal.ofReal C * Y i :=
      htailEn.trans (hW i (by omega))
    have htailFinite := hYsumFinite (i + 1) n (by omega)
    have htailLeftFinite : (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico (i + 1) n, Y j) < ⊤ :=
      ENNReal.mul_lt_top (by simp) htailFinite
    have hprodFinite : ENNReal.ofReal C * Y i < ⊤ :=
      ENNReal.mul_lt_top (by simp) (hYfinite i hi')
    have hreal := (ENNReal.toReal_le_toReal htailLeftFinite.ne hprodFinite.ne).2 htail
    have hrealSum : (∑ j ∈ Finset.Ico (i + 1) n, Y j).toReal = S (i + 1) := by
      rw [hsumToReal (i + 1) n le_rfl]
    have hrealProd : (ENNReal.ofReal C * Y i).toReal = C * y i := by
      dsimp [y]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]
    rw [ENNReal.toReal_mul, hrealSum, hrealProd] at hreal
    exact hreal
  have hterminal : S (n - 1) = y (n - 1) := by
    have hset : Finset.Ico (n - 1) n = {n - 1} := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    simp [S, y, hset]
  have hcontract : ∀ i < n - 1, (1 + 2 / C) * S (i + 1) ≤ S i := by
    intro i hi
    have hsplit := hSsplit i hi
    have htail := hrealTail i hi
    have hdiv : (2 / C) * S (i + 1) ≤ y i := by
      have hdiv' : (2 * S (i + 1)) / C ≤ y i := (div_le_iff₀ hC).2 (by nlinarith [htail])
      calc
        (2 / C) * S (i + 1) = (2 * S (i + 1)) / C := by ring
        _ ≤ y i := hdiv'
    calc
      (1 + 2 / C) * S (i + 1) = S (i + 1) + (2 / C) * S (i + 1) := by ring
      _ ≤ S (i + 1) + y i := add_le_add le_rfl hdiv
      _ = S i := by rw [hsplit]; ring
  have hnum := d1_geometric_tail_bound (N := n - 1) (C := B)
    (L := (d.len P a b).toReal) (R := 1 + 2 / C) (S := S) (y := y)
    hB (by positivity) hbaseReal hterminal hcontract
  let coeff : ℝ := B / (2 * (1 + 2 / C) ^ (n - 1))
  have hcoeff : 0 < coeff := by
    dsimp [coeff]
    positivity
  have hnum' : B * y (n - 1) ≤ coeff * (d.len P a b).toReal := by
    simpa [coeff] using hnum
  have hprodY : ENNReal.ofReal B * Y (n - 1) = ENNReal.ofReal (B * y (n - 1)) := by
    have hYeq : Y (n - 1) = ENNReal.ofReal (y (n - 1)) := by
      dsimp [y]
      exact (ENNReal.ofReal_toReal (hYfinite (n - 1) (by omega)).ne).symm
    calc
      ENNReal.ofReal B * Y (n - 1) = ENNReal.ofReal B * ENNReal.ofReal (y (n - 1)) := by
        rw [hYeq]
      _ = ENNReal.ofReal (B * y (n - 1)) := (ENNReal.ofReal_mul hB.le).symm
  have hprodLen : ENNReal.ofReal coeff * d.len P a b =
      ENNReal.ofReal (coeff * (d.len P a b).toReal) := by
    calc
      ENNReal.ofReal coeff * d.len P a b =
          ENNReal.ofReal coeff * ENNReal.ofReal ((d.len P a b).toReal) :=
            congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal coeff * x)
              (ENNReal.ofReal_toReal hlen.ne).symm
      _ = ENNReal.ofReal (coeff * (d.len P a b).toReal) := (ENNReal.ofReal_mul hcoeff.le).symm
  calc
    aroundDist d' (d1OuterAnnulus c r hr (n - 1)) ≤ ENNReal.ofReal B * Y (n - 1) := hZ
    _ = ENNReal.ofReal (B * y (n - 1)) := hprodY
    _ ≤ ENNReal.ofReal (coeff * (d.len P a b).toReal) := ENNReal.ofReal_le_ofReal hnum'
    _ = ENNReal.ofReal coeff * d.len P a b := hprodLen.symm

end SupercriticalLFPPAS.Separating
