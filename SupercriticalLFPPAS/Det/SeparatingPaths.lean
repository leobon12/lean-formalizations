import SupercriticalLFPPAS.Det.Numerical
import SupercriticalLQGUniqueness.B2.PfeLocal.Length
import SupercriticalLQGUniqueness.B2.PfeWeyl.AnnularJoining
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1Crossing
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3CircleTools
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.OrderedCrossings
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Transfer.Transfer

/-! Deterministic annular crossing and separator estimates for Lemma 3.4. -/

set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLFPPAS

/-- A Euclidean annulus with explicitly supplied radii. -/
def d1Annulus (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    SupercriticalLQGUniqueness.EuclideanAnnulus :=
  ⟨(c, r, R), hr, hrR⟩

/-- The crossing annulus at one of a positive sequence of radii. -/
def d1InnerAnnulus (c : ℂ) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (j : ℕ) :
    SupercriticalLQGUniqueness.EuclideanAnnulus :=
  d1Annulus c (r j) (2 * r j) (hr j) (by linarith [hr j])

/-- The annulus supporting a separating path at a given radius. -/
def d1OuterAnnulus (c : ℂ) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (j : ℕ) :
    SupercriticalLQGUniqueness.EuclideanAnnulus :=
  d1Annulus c (2 * r j) (3 * r j) (by linarith [hr j]) (by linarith [hr j])

/-- Extend finitely many nested radii by a geometric tail, so they can be used
with the host library's all-indices ordered-crossing theorem. -/
def d1ExtendRadii (n : ℕ) (r : ℕ → ℝ) (_hn : 0 < n) (k : ℕ) : ℝ :=
  if k < n then r k else r (n - 1) * (1 / 8 : ℝ) ^ (k + 1 - n)

theorem d1ExtendRadii_eq (n : ℕ) (r : ℕ → ℝ) (hn : 0 < n) {k : ℕ}
    (hk : k < n) : d1ExtendRadii n r hn k = r k := by
  simp [d1ExtendRadii, hk]

theorem d1ExtendRadii_pos (n : ℕ) (r : ℕ → ℝ) (hn : 0 < n)
    (hr : ∀ k < n, 0 < r k) (k : ℕ) :
    0 < d1ExtendRadii n r hn k := by
  by_cases hk : k < n
  · rw [d1ExtendRadii_eq n r hn hk]
    exact hr k hk
  · have hn' : 0 < r (n - 1) := hr (n - 1) (by omega)
    simp only [d1ExtendRadii, if_neg hk]
    exact mul_pos hn' (pow_pos (by norm_num) _)

theorem d1ExtendRadii_sep (n : ℕ) (r : ℕ → ℝ) (hn : 0 < n)
    (hr : ∀ k < n, 0 < r k)
    (hstep : ∀ k, k + 1 < n → r (k + 1) < r k / 4) (k : ℕ) :
    2 * d1ExtendRadii n r hn (k + 1) ≤ d1ExtendRadii n r hn k := by
  by_cases hk : k + 1 < n
  · rw [d1ExtendRadii_eq n r hn hk, d1ExtendRadii_eq n r hn (by omega)]
    have h := hstep k hk
    linarith [hr k (by omega)]
  · by_cases hk' : k < n
    · have hkn : k + 1 = n := by omega
      have hleft : d1ExtendRadii n r hn k = r k := d1ExtendRadii_eq n r hn hk'
      have hright : d1ExtendRadii n r hn (k + 1) = r k / 8 := by
        rw [d1ExtendRadii, if_neg hk]
        have hidx : n - 1 = k := by omega
        rw [hkn, hidx]
        simp [show k + 2 - (k + 1) = 1 by omega]
        ring
      rw [hleft, hright]
      have hrk : 0 < r k := hr k hk'
      nlinarith
    · have hpow : (1 / 8 : ℝ) ^ (k + 2 - n) =
          (1 / 8 : ℝ) ^ (k + 1 - n) * (1 / 8 : ℝ) := by
        congr 1
        have : k + 2 - n = (k + 1 - n) + 1 := by omega
        rw [this, pow_succ]
      have hk1 : ¬ k + 1 < n := by omega
      rw [d1ExtendRadii, if_neg hk1, d1ExtendRadii, if_neg hk']
      rw [hpow]
      have htail : 0 < r (n - 1) * (1 / 8 : ℝ) ^ (k + 1 - n) := by
        have hn' : 0 < r (n - 1) := hr (n - 1) (by omega)
        positivity
      nlinarith

/-- Nested crossing intervals pay for any costs bounded by their metric lengths. -/
theorem d1_sum_cost_le_len_of_ordered
    (D : SupercriticalLQGUniqueness.LSCMetric) (P : ℝ → ℂ)
    (g : ℝ → ℝ) (r : ℕ → ℝ) (b : ℝ) (lo hi : ℝ)
    (cost : ℕ → ℝ≥0∞)
    (hcost : ∀ (k : ℕ) (s t : ℝ), lo ≤ s → s ≤ t → t ≤ hi →
      g s = 2 * r k → g t = r k → cost k ≤ D.len P s t)
    (n k : ℕ) (a : ℝ) (hloa : lo ≤ a) (hbhi : b ≤ hi)
    (h : SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.OrderedCrossings
      g r b n k a) :
    (∑ j ∈ Finset.Ico k (k + n), cost j) ≤ D.len P a b := by
  induction n generalizing k a with
  | zero =>
      simp only [Nat.add_zero, Finset.Ico_self, Finset.sum_empty]
      exact bot_le
  | succ n ih =>
      obtain ⟨s, t, has, hst, htb, hs, ht, _, htail⟩ := h
      have hfirst := hcost k s t (hloa.trans has) hst (htb.trans hbhi) hs ht
      have hrest := ih (k + 1) t (hloa.trans (has.trans hst)) htail
      have hsum : (∑ j ∈ Finset.Ico k (k + (n + 1)), cost j) =
          cost k + ∑ j ∈ Finset.Ico (k + 1) ((k + 1) + n), cost j := by
        rw [show k + (n + 1) = (k + 1) + n by omega]
        exact Finset.sum_eq_sum_Ico_succ_bot (by omega) cost
      rw [hsum]
      calc
        cost k + (∑ j ∈ Finset.Ico (k + 1) ((k + 1) + n), cost j)
            ≤ D.len P s t + D.len P t b := add_le_add hfirst hrest
        _ = D.len P s b :=
          (SupercriticalLQGUniqueness.B2.PfeLocal.lsc_len_add D P hst htb).symm
        _ ≤ D.len P a b :=
          eVariationOn.mono (D.pt ∘ P) (Icc_subset_Icc has le_rfl)

/-- The host ordered-crossing extraction, with each annular across cost paid
by the corresponding subpath length. -/
theorem d1_across_sum_le_len
    (D : SupercriticalLQGUniqueness.LSCMetric) (P : ℝ → ℂ)
    (c : ℂ) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j)
    (hsep : ∀ j, 2 * r (j + 1) ≤ r j)
    {n k : ℕ} {a b : ℝ}
    (hab : a ≤ b) (hPc : ContinuousOn P (Icc a b))
    (ha : 2 * r k ≤ dist (P a) c)
    (hb : dist (P b) c ≤ r (k + n - 1)) :
    (∑ j ∈ Finset.Ico k (k + n),
      SupercriticalLQGUniqueness.acrossDist D
        (SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.radialAnnulus
          c r hr j)) ≤ D.len P a b := by
  let g : ℝ → ℝ := fun t => dist (P t) c
  have hmono : Antitone r := by
    apply antitone_nat_of_succ_le
    intro j
    have hj := hr (j + 1)
    linarith [hsep j]
  have hg : ContinuousOn g (Icc a b) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  have hcross := SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.ordered_crossings_of_nested
    g r b hr hsep hmono n k a hab hg ha hb
  apply d1_sum_cost_le_len_of_ordered D P g r b a b
    (fun j => SupercriticalLQGUniqueness.acrossDist D
      (SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.radialAnnulus
        c r hr j))
    _ n k a le_rfl le_rfl hcross
  intro j s t has hst htb hs ht
  have hcrossing :=
    SupercriticalLQGUniqueness.B2.PfeWeyl.acrossDist_le_len_of_crossing_rev D
      (SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.radialAnnulus
        c r hr j) hst (hPc.mono (Icc_subset_Icc has htb))
      (by simpa only [g,
        SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.radialAnnulus,
        SupercriticalLQGUniqueness.EuclideanAnnulus.center,
        SupercriticalLQGUniqueness.EuclideanAnnulus.outerRadius] using hs.ge)
      (by simpa only [g,
        SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.radialAnnulus,
        SupercriticalLQGUniqueness.EuclideanAnnulus.center,
        SupercriticalLQGUniqueness.EuclideanAnnulus.innerRadius] using ht.le)
  exact hcrossing

/-- The finite radii in the paper form an initial segment of the extension
used by `d1_across_sum_le_len`. -/
theorem d1_finite_across_sum_le_len
    (D : SupercriticalLQGUniqueness.LSCMetric) (P : ℝ → ℂ)
    (c : ℂ) (n : ℕ) (r : ℕ → ℝ) (hn : 0 < n)
    (hr : ∀ j, 0 < r j)
    (hstep : ∀ j, j + 1 < n → r (j + 1) < r j / 4)
    {k m : ℕ} {a b : ℝ}
    (hkm : k + m ≤ n) (hm : 0 < m) (hab : a ≤ b)
    (hPc : ContinuousOn P (Icc a b))
    (ha : 2 * r k ≤ dist (P a) c)
    (hb : dist (P b) c ≤ r (k + m - 1)) :
    (∑ j ∈ Finset.Ico k (k + m),
      SupercriticalLQGUniqueness.acrossDist D
        (d1Annulus c (r j) (2 * r j) (hr j) (by linarith [hr j])) ) ≤
      D.len P a b := by
  let R := d1ExtendRadii n r hn
  have hRpos : ∀ j, 0 < R j := d1ExtendRadii_pos n r hn (fun j _ => hr j)
  have hRsep : ∀ j, 2 * R (j + 1) ≤ R j :=
    d1ExtendRadii_sep n r hn (fun j _ => hr j) hstep
  have hk : k < n := by omega
  have hlast : k + m - 1 < n := by omega
  have haR : 2 * R k ≤ dist (P a) c := by
    have hRk : R k = r k := by
      dsimp [R]
      exact d1ExtendRadii_eq n r hn hk
    rw [hRk]
    exact ha
  have hbR : dist (P b) c ≤ R (k + m - 1) := by
    have hRlast : R (k + m - 1) = r (k + m - 1) := by
      dsimp [R]
      exact d1ExtendRadii_eq n r hn hlast
    rw [hRlast]
    exact hb
  have hsum := d1_across_sum_le_len D P c R hRpos hRsep hab hPc haR hbR
  calc
    (∑ j ∈ Finset.Ico k (k + m),
      SupercriticalLQGUniqueness.acrossDist D
        (d1Annulus c (r j) (2 * r j) (hr j) (by linarith [hr j])) )
        = ∑ j ∈ Finset.Ico k (k + m),
          SupercriticalLQGUniqueness.acrossDist D
            (SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.radialAnnulus
              c R hRpos j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjn : j < n := by
            simp only [Finset.mem_Ico] at hj
            omega
          have hRj : R j = r j := d1ExtendRadii_eq n r hn hjn
          have hA : d1Annulus c (r j) (2 * r j) (hr j) (by linarith [hr j]) =
              SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.radialAnnulus
                c R hRpos j := by
            apply Subtype.ext
            simp only [d1Annulus,
              SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings.radialAnnulus]
            rw [hRj]
          rw [hA]
    _ ≤ D.len P a b := hsum

/-- Length is invariant under reversing the orientation of a parameter
interval. -/
theorem d1_len_reverse (D : SupercriticalLQGUniqueness.LSCMetric)
    (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    D.len (fun t => P (a + b - t)) a b = D.len P a b := by
  change LQGMetric.MetricGeometry.curveLength
      (D.pt ∘ fun t => P (a + b - t)) a b =
    LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) a b
  exact LQGMetric.MetricGeometry.curveLength_reverse (D.pt ∘ P) hab

/-- Finite nested radii are antitone on the indices that occur in the
statement. -/
theorem d1_radius_le_prefix (n : ℕ) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j)
    (hstep : ∀ j, j + 1 < n → r (j + 1) < r j / 4)
    {i j : ℕ} (hij : i ≤ j) (hj : j < n) : r j ≤ r i := by
  induction j generalizing i with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      by_cases heq : i = j + 1
      · subst i
        exact le_rfl
      · have hij' : i ≤ j := by omega
        have hmono : r (j + 1) ≤ r j := by
          have hs := hstep j hj
          have hp := hr j
          linarith
        exact hmono.trans (ih hij' (by omega))

/-- The part of the geodesic between two hits of an annular separator pays
twice the across costs of every strictly inner annulus. -/
theorem d1_twice_inner_across_sum_le_aroundDist
    (D : SupercriticalLQGUniqueness.LSCMetric)
    (hforget : Continuous (SupercriticalLQGUniqueness.B2.PfeWeyl.euclidForget D))
    (c : ℂ) (n : ℕ) (hn : 0 < n) (r : ℕ → ℝ)
    (hr : ∀ j, 0 < r j)
    (hstep : ∀ j, j + 1 < n → r (j + 1) < r j / 4)
    (i : ℕ) (hi : i + 1 < n)
    {P : ℝ → ℂ} {T q : ℝ}
    (hq0 : 0 < q) (hqT : q < T)
    (hP : D.IsCurve P 0 T)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      D.len P u v = D (P u, P v))
    (h0 : 3 * r i ≤ dist (P 0) c)
    (hq : dist (P q) c ≤ r (n - 1))
    (hT : 3 * r i ≤ dist (P T) c) :
    (2 : ℝ≥0∞) *
      (∑ j ∈ Finset.Ico (i + 1) n,
        SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr j)) ≤
      SupercriticalLQGUniqueness.aroundDist D (d1OuterAnnulus c r hr i) := by
  let A := d1OuterAnnulus c r hr i
  have hPcont : ContinuousOn P (Icc 0 T) :=
    SupercriticalLQGUniqueness.B2.PfeWeyl.continuousOn_of_isCurve_of_forget D hforget hP
  unfold SupercriticalLQGUniqueness.aroundDist
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
  have hπcont : ContinuousOn π (Icc s t) :=
    SupercriticalLQGUniqueness.B2.PfeWeyl.continuousOn_of_isCurve_of_forget D hforget hπ
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
  have h0Outer : P 0 ∉ Metric.ball c (3 * r i) := by
    simpa only [Metric.mem_ball, not_lt] using h0
  have hqClosed : P q ∈ Metric.closedBall c (2 * r i) := by
    simpa only [Metric.mem_closedBall] using hqInner
  have hTOuter : P T ∉ Metric.ball c (3 * r i) := by
    simpa only [Metric.mem_ball, not_lt] using hT
  have hPleft : ContinuousOn P (Icc (0 : ℝ) q) :=
    hPcont.mono (Icc_subset_Icc le_rfl hqT.le)
  have hPright : ContinuousOn P (Icc q T) :=
    hPcont.mono (Icc_subset_Icc hq0.le le_rfl)
  obtain ⟨u, hu, huTrace⟩ :=
    SupercriticalLQGUniqueness.B2.PfeWeyl.outside_to_inside_hits_separator
      hq0.le hPleft (by linarith [hr i]) hsep' h0Outer hqClosed
  obtain ⟨v, hv, hvTrace⟩ :=
    SupercriticalLQGUniqueness.B2.PfeWeyl.inside_to_outside_hits_separator
      hqT.le hPright
      (by linarith [hr i]) hsep' hqClosed hTOuter
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans hqT.le⟩
  have hvT : v ∈ Icc (0 : ℝ) T := ⟨hq0.le.trans hv.1, hv.2⟩
  have huv : u ≤ v := hu.2.trans hv.1
  have huTraceMem := huTrace
  have hvTraceMem := hvTrace
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
  have hQcont : ContinuousOn Q (Icc q v) := by
    let φ : ℝ → ℝ := fun t => q + v - t
    have hφcont : ContinuousOn φ (Icc q v) := by fun_prop
    have hφmaps : MapsTo φ (Icc q v) (Icc 0 T) := by
      intro t ht
      constructor <;> simp only [mem_Icc] at ht ⊢ <;> dsimp [φ] <;> linarith [hvT.2]
    change ContinuousOn (P ∘ φ) (Icc q v)
    exact hPcont.comp hφcont hφmaps
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
  have hPsegLeft : ContinuousOn P (Icc u q) :=
    hPcont.mono (Icc_subset_Icc hu.1 hqT.le)
  have hleft := d1_finite_across_sum_le_len D P c n r hn hr hstep
    (k := i + 1) (m := n - (i + 1)) (by omega) (by omega)
    hu.2 hPsegLeft
    (hscale.trans hPuRadius) (by simpa [htailIdx] using hq)
  have hright := d1_finite_across_sum_le_len D Q c n r hn hr hstep
    (k := i + 1) (m := n - (i + 1)) (by omega) (by omega)
    hv.1 hQcont
    (by simpa [hQq] using hscale.trans hPvRadius)
    (by simpa [hQv, htailIdx] using hq)
  have hrightLen : D.len Q q v = D.len P q v := by
    dsimp [Q]
    exact d1_len_reverse D P hv.1
  have htwice :
      (2 : ℝ≥0∞) *
        (∑ j ∈ Finset.Ico (i + 1) n,
          SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr j)) ≤
        D.len P u v := by
    have hleft' :
        (∑ j ∈ Finset.Ico (i + 1) n,
          SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr j)) ≤
          D.len P u q := by
      simpa [d1InnerAnnulus, hcount] using hleft
    have hright' :
        (∑ j ∈ Finset.Ico (i + 1) n,
          SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr j)) ≤
          D.len P q v := by
      simpa [d1InnerAnnulus, hrightLen, hcount] using hright
    calc
      _ = (∑ j ∈ Finset.Ico (i + 1) n,
          SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr j)) +
          (∑ j ∈ Finset.Ico (i + 1) n,
          SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr j)) := by
            rw [two_mul]
      _ ≤ D.len P u q + D.len P q v := add_le_add hleft' hright'
      _ = D.len P u v :=
        (SupercriticalLQGUniqueness.B2.PfeLocal.lsc_len_add D P hu.2 hv.1).symm
  have htrace := SupercriticalLQGUniqueness.Uniqueness.TwoScale.Transfer.trace_pair_le_len
    D π huTraceMem hvTraceMem
  have hgeoUV := hgeo u v huT hvT huv
  have hlenBound : D.len P u v ≤ D.len π s t := hgeoUV ▸ htrace
  exact htwice.trans hlenBound

/-- **Lemma 3.4 (separating paths).** For a geodesic with endpoints outside
the outermost disk and a visit to the innermost disk, bounded around-to-across
ratios force geometric decay of the final around cost. The finite radius list
is represented by a positive sequence; only its first `n` entries occur. -/
theorem d1_lemma_3_4
    (D D' : SupercriticalLQGUniqueness.LSCMetric)
    (hforget : Continuous (SupercriticalLQGUniqueness.B2.PfeWeyl.euclidForget D))
    (c : ℂ) (n : ℕ) (hn : 0 < n) (C : ℝ) (hC : 0 < C)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hstep : ∀ i, i + 1 < n → r (i + 1) < r i / 4)
    (_hYpos : ∀ i < n,
      0 < SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr i))
    (hYfinite : ∀ i < n,
      SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr i) < ⊤)
    (hW : ∀ i < n,
      SupercriticalLQGUniqueness.aroundDist D (d1OuterAnnulus c r hr i) ≤
        ENNReal.ofReal C *
          SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr i))
    (hZ : ∀ i < n,
      SupercriticalLQGUniqueness.aroundDist D' (d1OuterAnnulus c r hr i) ≤
        ENNReal.ofReal C *
          SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr i))
    {P : ℝ → ℂ} {T : ℝ} (hP : D.IsCurve P 0 T)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      D.len P u v = D (P u, P v))
    (hlen : D.len P 0 T < ⊤)
    (h0 : P 0 ∉ Metric.ball c (3 * r 0))
    (hTend : P T ∉ Metric.ball c (3 * r 0))
    (hvisit : ∃ q ∈ Icc (0 : ℝ) T,
      P q ∈ Metric.closedBall c (r (n - 1))) :
    SupercriticalLQGUniqueness.aroundDist D' (d1OuterAnnulus c r hr (n - 1)) ≤
      ENNReal.ofReal (C / (2 * (1 + 2 / C) ^ (n - 1))) * D.len P 0 T := by
  let Y : ℕ → ℝ≥0∞ := fun i =>
    SupercriticalLQGUniqueness.acrossDist D (d1InnerAnnulus c r hr i)
  let S : ℕ → ℝ := fun i => ∑ j ∈ Finset.Ico i n, (Y j).toReal
  let y : ℕ → ℝ := fun i => (Y i).toReal
  have hPcont : ContinuousOn P (Icc (0 : ℝ) T) :=
    SupercriticalLQGUniqueness.B2.PfeWeyl.continuousOn_of_isCurve_of_forget D hforget hP
  obtain ⟨q, hq, hqmem⟩ := hvisit
  have hq0 : 0 < q := by
    by_contra hnot
    have hqzero : q = 0 := by
      have hqnonneg := hq.1
      have hqle : q ≤ 0 := le_of_not_gt hnot
      linarith
    subst q
    have hqpos := hr (n - 1)
    have hmem : dist (P 0) c ≤ r (n - 1) := by
      simpa only [Metric.mem_closedBall] using hqmem
    have hleft : dist (P 0) c < 3 * r 0 := by
      have hlast : r (n - 1) ≤ r 0 :=
        d1_radius_le_prefix n r hr hstep (by omega) (by omega)
      have hzero : 0 < r 0 := hr 0
      linarith
    have h0far : 3 * r 0 ≤ dist (P 0) c := by
      simpa only [Metric.mem_ball, not_lt] using h0
    linarith
  have hqT : q < T := by
    by_contra hnot
    have hTle : T ≤ q := le_of_not_gt hnot
    have hqleT := hq.2
    have hqeq : q = T := by linarith
    subst q
    have hlast : r (n - 1) ≤ r 0 :=
      d1_radius_le_prefix n r hr hstep (by omega) (by omega)
    have hmem : dist (P T) c ≤ r (n - 1) := by
      simpa only [Metric.mem_closedBall] using hqmem
    have hleft : dist (P T) c < 3 * r 0 := by
      have hzero : 0 < r 0 := hr 0
      linarith
    have hTfar : 3 * r 0 ≤ dist (P T) c := by
      simpa only [Metric.mem_ball, not_lt] using hTend
    linarith
  have hqRadius : dist (P q) c ≤ r (n - 1) := by
    simpa only [Metric.mem_closedBall] using hqmem
  have h0far : 3 * r 0 ≤ dist (P 0) c := by
    simpa only [Metric.mem_ball, not_lt] using h0
  have hTfar : 3 * r 0 ≤ dist (P T) c := by
    simpa only [Metric.mem_ball, not_lt] using hTend
  have hleft := d1_finite_across_sum_le_len D P c n r hn hr hstep
    (k := 0) (m := n) (by omega) hn hq.1
    (hPcont.mono (Icc_subset_Icc le_rfl hq.2))
    (by calc 2 * r 0 ≤ 3 * r 0 := by nlinarith [hr 0]
            _ ≤ dist (P 0) c := h0far)
    (by convert hqRadius using 1 <;> congr 1 <;> omega)
  let Q : ℝ → ℂ := fun t => P (q + T - t)
  have hQcont : ContinuousOn Q (Icc q T) := by
    let φ : ℝ → ℝ := fun t => q + T - t
    have hφcont : ContinuousOn φ (Icc q T) := by fun_prop
    have hφmaps : MapsTo φ (Icc q T) (Icc 0 T) := by
      intro t ht
      constructor <;> simp only [mem_Icc] at ht ⊢ <;> dsimp [φ] <;> linarith [hq.1]
    change ContinuousOn (P ∘ φ) (Icc q T)
    exact hPcont.comp hφcont hφmaps
  have hQq : Q q = P T := by
    dsimp [Q]
    congr 1
    ring
  have hQT : Q T = P q := by
    dsimp [Q]
    congr 1
    ring
  have hright := d1_finite_across_sum_le_len D Q c n r hn hr hstep
    (k := 0) (m := n) (by omega) hn hq.2 hQcont
    (by simpa [hQq] using (by nlinarith [hr 0, hTfar] : 2 * r 0 ≤ dist (P T) c))
    (by simpa [hQT] using hqRadius)
  have hbaseEn :
      (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico 0 n, Y j) ≤ D.len P 0 T := by
    have hleft' : (∑ j ∈ Finset.Ico 0 n, Y j) ≤ D.len P 0 q := by
      simpa [Y, d1InnerAnnulus] using hleft
    have hright' : (∑ j ∈ Finset.Ico 0 n, Y j) ≤ D.len P q T := by
      have hrev : D.len Q q T = D.len P q T := by
        dsimp [Q]
        exact d1_len_reverse D P hq.2
      simpa [Y, d1InnerAnnulus, hrev] using hright
    calc
      (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico 0 n, Y j) =
          (∑ j ∈ Finset.Ico 0 n, Y j) + (∑ j ∈ Finset.Ico 0 n, Y j) := by rw [two_mul]
      _ ≤ D.len P 0 q + D.len P q T := add_le_add hleft' hright'
      _ = D.len P 0 T :=
        (SupercriticalLQGUniqueness.B2.PfeLocal.lsc_len_add D P hq.1 hq.2).symm
  have hYsumFinite : ∀ a b : ℕ, b ≤ n →
      (∑ j ∈ Finset.Ico a b, Y j) < ⊤ := by
    intro a b hb
    apply ENNReal.sum_lt_top.2
    intro j hj
    have hjn : j < n := by
      simp only [Finset.mem_Ico] at hj
      omega
    exact hYfinite j hjn
  have hsumToReal : ∀ a b : ℕ, b ≤ n →
      (∑ j ∈ Finset.Ico a b, Y j).toReal =
        ∑ j ∈ Finset.Ico a b, (Y j).toReal := by
    intro a b hb
    rw [ENNReal.toReal_sum]
    intro j hj
    have hjn : j < n := by
      simp only [Finset.mem_Ico] at hj
      omega
    exact (hYfinite j hjn).ne
  have hbaseReal : 2 * S 0 ≤ (D.len P 0 T).toReal := by
    have hbaseFinite :
        (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico 0 n, Y j) < ⊤ :=
      ENNReal.mul_lt_top (by simp) (hYsumFinite 0 n le_rfl)
    have hreal :=
      (ENNReal.toReal_le_toReal hbaseFinite.ne hlen.ne).2 hbaseEn
    have hprod : ((2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico 0 n, Y j)).toReal = 2 * S 0 := by
      rw [ENNReal.toReal_mul, hsumToReal 0 n le_rfl]
      simp [S]
    rw [hprod] at hreal
    exact hreal
  have hSsplit : ∀ i < n - 1, S i = y i + S (i + 1) := by
    intro i hi
    have hsum := Finset.sum_eq_sum_Ico_succ_bot (show i < n by omega)
      (fun j => (Y j).toReal)
    simpa [S, y] using hsum
  have hrealTail : ∀ i < n - 1, 2 * S (i + 1) ≤ C * y i := by
    intro i hi
    have hi' : i < n := by omega
    have hri0 : r i ≤ r 0 :=
      d1_radius_le_prefix n r hr hstep (Nat.zero_le i) hi'
    have htailEn := d1_twice_inner_across_sum_le_aroundDist D hforget c n hn r hr hstep
      i (by omega) hq0 hqT hP hgeo
      (by
        have hi0 : 3 * r i ≤ 3 * r 0 := by nlinarith
        exact hi0.trans h0far)
      hqRadius
      (by
        have hi0 : 3 * r i ≤ 3 * r 0 := by nlinarith
        exact hi0.trans hTfar)
    have htail :
        (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico (i + 1) n, Y j) ≤
          ENNReal.ofReal C * Y i := by
      exact htailEn.trans (hW i hi')
    have htailFinite := hYsumFinite (i + 1) n (by omega)
    have htailLeftFinite :
        (2 : ℝ≥0∞) * (∑ j ∈ Finset.Ico (i + 1) n, Y j) < ⊤ :=
      ENNReal.mul_lt_top (by simp) htailFinite
    have hprodFinite : ENNReal.ofReal C * Y i < ⊤ := by
      exact ENNReal.mul_lt_top (by simp) (hYfinite i hi')
    have hreal :=
      (ENNReal.toReal_le_toReal htailLeftFinite.ne hprodFinite.ne).2 htail
    have hrealSum :
        (∑ j ∈ Finset.Ico (i + 1) n, Y j).toReal = S (i + 1) := by
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
  have hcontract : ∀ i < n - 1,
      (1 + 2 / C) * S (i + 1) ≤ S i := by
    intro i hi
    have hsplit := hSsplit i hi
    have htail := hrealTail i hi
    have hdiv : (2 / C) * S (i + 1) ≤ y i := by
      have hdiv' : (2 * S (i + 1)) / C ≤ y i :=
        (div_le_iff₀ hC).2 (by nlinarith [htail])
      calc
        (2 / C) * S (i + 1) = (2 * S (i + 1)) / C := by ring
        _ ≤ y i := hdiv'
    calc
      (1 + 2 / C) * S (i + 1) = S (i + 1) + (2 / C) * S (i + 1) := by ring
      _ ≤ S (i + 1) + y i := add_le_add le_rfl hdiv
      _ = S i := by rw [hsplit]; ring
  have hnum := d1_geometric_tail_bound (N := n - 1) (C := C)
    (L := (D.len P 0 T).toReal) (R := 1 + 2 / C) (S := S) (y := y)
    hC (by positivity)
    hbaseReal hterminal hcontract
  let coeff : ℝ := C / (2 * (1 + 2 / C) ^ (n - 1))
  have hcoeff : 0 < coeff := by
    dsimp [coeff]
    positivity
  have hnum' : C * y (n - 1) ≤ coeff * (D.len P 0 T).toReal := by
    simpa [coeff] using hnum
  have hprodY : ENNReal.ofReal C * Y (n - 1) =
      ENNReal.ofReal (C * y (n - 1)) := by
    have hYeq : Y (n - 1) = ENNReal.ofReal (y (n - 1)) := by
      dsimp [y]
      exact (ENNReal.ofReal_toReal (hYfinite (n - 1) (by omega)).ne).symm
    calc
      ENNReal.ofReal C * Y (n - 1) =
          ENNReal.ofReal C * ENNReal.ofReal (y (n - 1)) := by rw [hYeq]
      _ = ENNReal.ofReal (C * y (n - 1)) := (ENNReal.ofReal_mul hC.le).symm
  have hprodLen : ENNReal.ofReal coeff * D.len P 0 T =
      ENNReal.ofReal (coeff * (D.len P 0 T).toReal) := by
    calc
      ENNReal.ofReal coeff * D.len P 0 T =
          ENNReal.ofReal coeff * ENNReal.ofReal ((D.len P 0 T).toReal) :=
            congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal coeff * x)
              (ENNReal.ofReal_toReal hlen.ne).symm
      _ = ENNReal.ofReal (coeff * (D.len P 0 T).toReal) :=
        (ENNReal.ofReal_mul hcoeff.le).symm
  calc
    SupercriticalLQGUniqueness.aroundDist D' (d1OuterAnnulus c r hr (n - 1)) ≤
        ENNReal.ofReal C * Y (n - 1) := hZ (n - 1) (by omega)
    _ = ENNReal.ofReal (C * y (n - 1)) := hprodY
    _ ≤ ENNReal.ofReal (coeff * (D.len P 0 T).toReal) :=
      ENNReal.ofReal_le_ofReal hnum'
    _ = ENNReal.ofReal coeff * D.len P 0 T := hprodLen.symm

end SupercriticalLFPPAS
