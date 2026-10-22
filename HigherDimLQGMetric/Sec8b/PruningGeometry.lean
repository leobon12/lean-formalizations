import HigherDimLQGMetric.Sec8.Cover
import HigherDimLQGMetric.Sec8.OccupationT4
import HigherDimLQGMetric.Count.Pruning
import HigherDimLQGMetric.Sec6.Geometry

/-!
# Section 8: deterministic length-to-distance bounds used by pruning

The integrated trap occupation estimate gives an upper bound on the real
distance drop when the discounted metric has a geodesic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open Set
open Metric
open scoped ENNReal

variable {d : ℕ}

/-- Removing a bump leaves the finite perturbation unchanged outside that bump's
collector. -/
theorem s7b_F_erase_eq_outside {f : ℕ → C(Rd d, ℝ)} {V : Set (Rd d)}
    (hf : ∀ j, ∀ u, u ∉ V → f j u = 0)
    {r : ℝ} (hr : r ≠ 0) {Z : Finset (Rd d × ℕ)}
    {site : Rd d × ℕ} (hsite : site ∈ Z) {u : Rd d}
    (hout : u ∉ sec8Collector V r site.1) :
    F_Z f r Z u = F_Z f r (Z.erase site) u := by
  classical
  have hzero : bumpAt (f site.2) r site.1 u = 0 :=
    S6a.bumpAt_eq_zero_of_notMem (hf site.2) hr site.1 hout
  have hsum := Finset.sum_erase_add Z (fun q => bumpAt (f q.2) r q.1 u) hsite
  simp only [F_Z, ContinuousMap.sum_apply]
  rw [← hsum, hzero, add_zero]

/-- The trap datum's positivity and support property gives the preceding
identity for every label in the permitted range. -/
theorem s7b_trap_F_erase_eq_outside {ξ cs Cs : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    {r : ℝ} (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    {site : Rd d × ℕ} (hsite : site ∈ Z) {u : Rd d}
    (hout : u ∉ sec8Collector T.V r site.1) :
    F_Z T.f r Z u = F_Z T.f r (Z.erase site) u := by
  classical
  have hf : ∀ v : Rd d, v ∉ T.V → T.f site.2 v = 0 := by
    intro v hv
    have hpos := (T.bumps site.2 (hJ site hsite)).2.2.2.2.1 v
    exact le_antisymm (le_of_not_gt (fun hp => hv (hpos.mp hp)))
      (((T.bumps site.2 (hJ site hsite)).2.2.2.1) v)
  have hzero : bumpAt (T.f site.2) r site.1 u = 0 :=
    S6a.bumpAt_eq_zero_of_notMem hf hr.ne' site.1 hout
  have hsum := Finset.sum_erase_add Z (fun q => bumpAt (T.f q.2) r q.1 u) hsite
  simp only [F_Z, ContinuousMap.sum_apply]
  rw [← hsum, hzero, add_zero]

/-- Erasing a site leaves no perturbation at all inside its radius-four ball,
because the color-class trap balls are disjoint. -/
theorem s7b_F_erase_zero_on_ball {ξ cs Cs : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    {r : ℝ} (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (Metric.ball q.1 (4 * r))
        (Metric.ball q'.1 (4 * r))))
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    {u : Rd d} (hu : u ∈ Metric.ball site.1 (4 * r)) :
    F_Z T.f r (Z.erase site) u = 0 := by
  classical
  have hsupp : ∀ j < T.J, tsupport (T.f j) ⊆ ann (0 : Rd d) 1 3 :=
    fun j hj => (T.bumps j hj).2.2.1
  have hsingle : F_Z T.f r Z u = bumpAt (T.f site.2) r site.1 u :=
    F_Z_eq_bumpAt hsupp hr hsite hJ hdisj hu
  have hsum := Finset.sum_erase_add Z (fun q => bumpAt (T.f q.2) r q.1 u) hsite
  have heq : F_Z T.f r Z u =
      F_Z T.f r (Z.erase site) u + bumpAt (T.f site.2) r site.1 u := by
    simpa only [F_Z, ContinuousMap.sum_apply] using hsum.symm
  rw [hsingle] at heq
  linarith only [heq]

/-- Local metric equality after a site is erased: on its ball, all remaining
weights vanish, so the erased metric is exactly the base internal metric. -/
theorem s7b_erase_internal_eq_on_ball {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    {r : ℝ} (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (Metric.ball q.1 (4 * r))
        (Metric.ball q'.1 (4 * r))))
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    (D E' : ContMetric d)
    (hE' : IsWeylOf ξ (-F_Z T.f r (Z.erase site)) D E')
    (u v : Rd d) :
    E'.internal (Metric.ball site.1 (4 * r)) u v =
      D.internal (Metric.ball site.1 (4 * r)) u v := by
  have hf : ∀ w ∈ Metric.ball site.1 (4 * r),
      ξ * (-F_Z T.f r (Z.erase site)) w = 0 := by
    intro w hw
    simp only [ContinuousMap.neg_apply, s7b_F_erase_zero_on_ball T hr hJ hdisj hsite hw,
      neg_zero, mul_zero]
  have h := internal_eq_of_eq_const (D' := E') hE' isOpen_ball hf u v
  simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using h

/-- A nonnegative finite trap perturbation can only shorten curve lengths. -/
theorem s7b_discount_len_le {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun) (hξ : 0 < ξ)
    {r : ℝ} {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (D E : ContMetric d) (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (P : ℝ → Rd d) {a b : ℝ} (hP : ContinuousOn P (Icc a b)) :
    E.len P a b ≤ D.len P a b := by
  have hf0 : ∀ j < T.J, (∀ u, 0 ≤ T.f j u) ∧
      (∀ u, T.f j u ≤ T.Mf) :=
    fun j hj => ⟨(T.bumps j hj).2.2.2.1,
      (T.bumps j hj).2.2.2.2.2⟩
  have hF0 : ∀ u, 0 ≤ F_Z T.f r Z u :=
    fun u => (F_Z_nonneg_le hf0 r hJ u).1
  have hweight : ∀ t ∈ Icc a b,
      D.weylWeight ξ (-F_Z T.f r Z) (D.pt (P t)) ≤ 1 := by
    intro t _
    rw [D.weylWeight_pt]
    exact Real.exp_le_one_iff.mpr (by
      simp only [ContinuousMap.neg_apply]
      nlinarith [mul_nonneg hξ.le (hF0 (P t))])
  rw [E.len_def, D.len_def, curveLength_eq_weightedLength_of_weyl hE hP]
  simpa only [ENNReal.ofReal_one, one_mul] using
    (weightedLength_le_ofReal_mul_curveLength (P := D.pt ∘ P)
      (w := D.weylWeight ξ (-F_Z T.f r Z)) (a := a) (b := b)
      (M := 1) hweight)

/-- Convert an occupation bound on a discounted geodesic into the real
`Δ` inequality required by the abstract pruning lemma. -/
theorem s7b_delta_le_of_occ {α : Type*}
    (D E : ContMetric d) (x y : Rd d) (P : ℝ → Rd d)
    (hP : IsGeod E P) (hP0 : P 0 = x) (hP1 : P 1 = y)
    (Z : Finset α) (s : α → ℝ) {H : ℝ}
    (hH : 0 ≤ H) (hs : ∀ i ∈ Z, 0 ≤ s i)
    (hocc : D.len P 0 1 ≤ E.len P 0 1 +
      ∑ i ∈ Z, ENNReal.ofReal (H * s i)) :
    D.1 (x, y) - E.1 (x, y) ≤ H * ∑ i ∈ Z, s i := by
  have hDxy : ENNReal.ofReal (D.1 (x, y)) ≤ D.len P 0 1 := by
    simpa only [hP0, hP1] using D.ofReal_le_len P (by norm_num : (0 : ℝ) ≤ 1)
  have hsum : (∑ i ∈ Z, ENNReal.ofReal (H * s i)) =
      ENNReal.ofReal (H * ∑ i ∈ Z, s i) := by
    rw [Finset.mul_sum]
    exact (ENNReal.ofReal_sum_of_nonneg
      (fun i hi => mul_nonneg hH (hs i hi))).symm
  have hright : 0 ≤ E.1 (x, y) + H * ∑ i ∈ Z, s i :=
    add_nonneg (E.nonneg x y) (mul_nonneg hH (Finset.sum_nonneg hs))
  have hreal : D.1 (x, y) ≤ E.1 (x, y) + H * ∑ i ∈ Z, s i := by
    apply (ENNReal.ofReal_le_ofReal_iff hright).mp
    rw [ENNReal.ofReal_add (E.nonneg x y)
      (mul_nonneg hH (Finset.sum_nonneg hs))]
    calc
      ENNReal.ofReal (D.1 (x, y)) ≤ D.len P 0 1 := hDxy
      _ ≤ E.len P 0 1 + ∑ i ∈ Z, ENNReal.ofReal (H * s i) := hocc
      _ = ENNReal.ofReal (E.1 (x, y)) +
            ENNReal.ofReal (H * ∑ i ∈ Z, s i) := by rw [hP.2, hP0, hP1, hsum]
  linarith only [hreal]

/-- The actual (T4b) trap estimate supplies pruning's upper bound on `Δ`.
The comparison metric appears only through `TrapProps`. -/
theorem s7b_delta_le_of_traps {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    (hξ : 0 < ξ) (r : ℝ) (hr : 0 < r)
    (D Dt E : ContMetric d) (s : Rd d × ℕ → ℝ)
    (Z : Finset (Rd d × ℕ))
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (hs : ∀ q ∈ Z, 0 ≤ s q)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (Metric.ball q.1 (4 * r)) (Metric.ball q'.1 (4 * r))))
    (htrap : ∀ q ∈ Z,
      TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c' D Dt
        (s q) r q.1 q.2)
    (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (x y : Rd d) (P : ℝ → Rd d) (hP : IsGeod E P)
    (hP0 : P 0 = x) (hP1 : P 1 = y) :
    D.1 (x, y) - E.1 (x, y) ≤ T.H * ∑ q ∈ Z, s q := by
  have hf0 : ∀ j < T.J, ∀ u, 0 ≤ T.f j u :=
    fun j hj u => (T.bumps j hj).2.2.2.1 u
  have hfV : ∀ j < T.J, ∀ u, 0 < T.f j u → u ∈ T.V :=
    fun j hj u hu => ((T.bumps j hj).2.2.2.2.1 u).mp hu
  have hH : 0 ≤ T.H := by
    have ha := T.constants.1
    have heq := T.constants.2.2.2.2.1
    rw [heq]
    exact mul_nonneg ha.le (Real.exp_pos _).le
  exact s7b_delta_le_of_occ D E x y P hP hP0 hP1 Z s hH hs
    (lemma82_T4b D Dt E ξ hξ r hr T.V T.f T.J hf0 hfV
      T.a T.b T.c T.g T.H T.c' s Z hJ hdisj htrap hE P hP)

/-- Weyl-scaled curve length depends only on the weight along the curve.
This identifies the two lengths outside a removed bump during pruning. -/
theorem s7b_len_eq_of_weyl_weights (D E E' : ContMetric d)
    (ξ : ℝ) (f g : C(Rd d, ℝ))
    (hE : IsWeylOf ξ f D E) (hE' : IsWeylOf ξ g D E')
    (P : ℝ → Rd d) {a b : ℝ} (hP : ContinuousOn P (Icc a b))
    (hfg : ∀ t ∈ Icc a b, f (P t) = g (P t)) :
    E.len P a b = E'.len P a b := by
  rw [E.len_def, E'.len_def, curveLength_eq_weightedLength_of_weyl hE hP,
    curveLength_eq_weightedLength_of_weyl hE' hP]
  apply weightedLength_congr_weight
  intro t ht
  change Real.exp (ξ * f (P t)) = Real.exp (ξ * g (P t))
  rw [hfg t ht]

/-- Erasing one trap does not change the length of a path segment which never
visits its collector. -/
theorem s7b_erase_len_eq_outside {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    {r : ℝ} (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    (D E E' : ContMetric d)
    (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (hE' : IsWeylOf ξ (-F_Z T.f r (Z.erase site)) D E')
    (P : ℝ → Rd d) {a b : ℝ} (hP : ContinuousOn P (Icc a b))
    (havoid : ∀ t ∈ Icc a b, P t ∉ sec8Collector T.V r site.1) :
    E.len P a b = E'.len P a b := by
  apply s7b_len_eq_of_weyl_weights D E E' ξ _ _ hE hE' P hP
  intro t ht
  simp only [ContinuousMap.neg_apply]
  rw [s7b_trap_F_erase_eq_outside T hr hJ hsite (havoid t ht)]

/-- One-site undoing: replace the middle of a discounted geodesic by an
`E'`-internal competitor, while its two outside pieces keep their lengths. -/
theorem s7b_undo_distance_le (E E' : ContMetric d)
    (x y : Rd d) (P : ℝ → Rd d) (hP : IsGeod E P)
    (hP0 : P 0 = x) (hP1 : P 1 = y)
    {σ₁ σ₂ b : ℝ} (h0 : 0 ≤ σ₁) (h12 : σ₁ ≤ σ₂) (h2 : σ₂ ≤ 1)
    (hb : 0 ≤ b)
    (hleft : E'.len P 0 σ₁ = E.len P 0 σ₁)
    (hright : E'.len P σ₂ 1 = E.len P σ₂ 1)
    (U : Set (Rd d))
    (hshort : E'.internal U (P σ₁) (P σ₂) ≤ ENNReal.ofReal b) :
    E'.1 (x, y) ≤ E.1 (x, y) + b := by
  have htri : E'.1 (x, y) ≤
      E'.1 (x, P σ₁) + E'.1 (P σ₁, P σ₂) + E'.1 (P σ₂, y) := by
    have h1 := E'.apply_triangle x (P σ₂) y
    have h2' := E'.apply_triangle x (P σ₁) (P σ₂)
    linarith only [h1, h2']
  have hE' : ENNReal.ofReal (E'.1 (x, y)) ≤
      E'.len P 0 σ₁ + E'.internal U (P σ₁) (P σ₂) + E'.len P σ₂ 1 := by
    have hle := ENNReal.ofReal_le_ofReal htri
    rw [ENNReal.ofReal_add (add_nonneg (E'.nonneg x (P σ₁))
      (E'.nonneg (P σ₁) (P σ₂))) (E'.nonneg (P σ₂) y),
      ENNReal.ofReal_add (E'.nonneg x (P σ₁))
        (E'.nonneg (P σ₁) (P σ₂))] at hle
    exact hle.trans (add_le_add
      (add_le_add (by simpa only [hP0] using E'.ofReal_le_len P h0)
        (E'.ofReal_le_internal U (P σ₁) (P σ₂)))
      (by simpa only [hP1] using E'.ofReal_le_len P h2))
  have hsplit : E.len P 0 1 =
      E.len P 0 σ₁ + E.len P σ₁ σ₂ + E.len P σ₂ 1 := by
    calc
      E.len P 0 1 = E.len P 0 σ₂ + E.len P σ₂ 1 :=
        (E.len_add P (h0.trans h12) h2).symm
      _ = E.len P 0 σ₁ + E.len P σ₁ σ₂ + E.len P σ₂ 1 := by
        rw [E.len_add P h0 h12]
  have hsumle : E.len P 0 σ₁ + E.len P σ₂ 1 ≤ E.len P 0 1 := by
    calc
      E.len P 0 σ₁ + E.len P σ₂ 1 ≤
          (E.len P 0 σ₁ + E.len P σ₁ σ₂) + E.len P σ₂ 1 := by
            exact add_le_add (le_add_of_nonneg_right (by exact bot_le)) le_rfl
      _ = E.len P 0 1 := hsplit.symm
  have hfinal : ENNReal.ofReal (E'.1 (x, y)) ≤
      ENNReal.ofReal (E.1 (x, y) + b) := by
    rw [ENNReal.ofReal_add (E.nonneg x y) hb]
    calc
      ENNReal.ofReal (E'.1 (x, y)) ≤
          E'.len P 0 σ₁ + E'.internal U (P σ₁) (P σ₂) + E'.len P σ₂ 1 := hE'
      _ ≤ E.len P 0 σ₁ + ENNReal.ofReal b + E.len P σ₂ 1 := by
        rw [hleft, hright]
        gcongr
      _ = E.len P 0 σ₁ + E.len P σ₂ 1 + ENNReal.ofReal b := by ac_rfl
      _ ≤ E.len P 0 1 + ENNReal.ofReal b := add_le_add hsumle le_rfl
      _ = ENNReal.ofReal (E.1 (x, y)) + ENNReal.ofReal b := by rw [hP.2, hP0, hP1]
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (E.nonneg x y) hb)).mp hfinal

/-- The complete one-site undo estimate once the closed-collector window and
its internal competitor have been located. -/
theorem s7b_erase_distance_le_of_window {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    {r : ℝ} (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    (D E E' : ContMetric d)
    (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (hE' : IsWeylOf ξ (-F_Z T.f r (Z.erase site)) D E')
    (x y : Rd d) (P : ℝ → Rd d) (hP : IsGeod E P)
    (hP0 : P 0 = x) (hP1 : P 1 = y)
    {σ₁ σ₂ b : ℝ} (h0 : 0 ≤ σ₁) (h12 : σ₁ ≤ σ₂) (h2 : σ₂ ≤ 1)
    (hb : 0 ≤ b)
    (hleft : ∀ t ∈ Icc (0 : ℝ) σ₁,
      P t ∉ sec8Collector T.V r site.1)
    (hright : ∀ t ∈ Icc σ₂ (1 : ℝ),
      P t ∉ sec8Collector T.V r site.1)
    (hshort : E'.internal (Metric.ball site.1 (4 * r))
      (P σ₁) (P σ₂) ≤ ENNReal.ofReal b) :
    E'.1 (x, y) ≤ E.1 (x, y) + b := by
  have hleftEq := s7b_erase_len_eq_outside T hr hJ hsite D E E' hE hE' P
    (hP.1.mono (Icc_subset_Icc le_rfl (h12.trans h2))) hleft
  have hrightEq := s7b_erase_len_eq_outside T hr hJ hsite D E E' hE hE' P
    (hP.1.mono (Icc_subset_Icc (h0.trans h12) le_rfl)) hright
  exact s7b_undo_distance_le E E' x y P hP hP0 hP1 h0 h12 h2 hb
    hleftEq.symm hrightEq.symm _ hshort

/-- If a discounted geodesic never enters the erased collector, undoing the
site cannot increase the endpoint distance. -/
theorem s7b_erase_distance_le_no_visit {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    {r : ℝ} (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    (D E E' : ContMetric d)
    (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (hE' : IsWeylOf ξ (-F_Z T.f r (Z.erase site)) D E')
    (x y : Rd d) (P : ℝ → Rd d) (hP : IsGeod E P)
    (hP0 : P 0 = x) (hP1 : P 1 = y)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1,
      P t ∉ sec8Collector T.V r site.1) :
    E'.1 (x, y) ≤ E.1 (x, y) := by
  have hlen := s7b_erase_len_eq_outside T hr hJ hsite D E E' hE hE' P hP.1 havoid
  have hmetric : ENNReal.ofReal (E'.1 (x, y)) ≤
      ENNReal.ofReal (E.1 (x, y)) := by
    calc
      ENNReal.ofReal (E'.1 (x, y)) ≤ E'.len P 0 1 := by
        simpa only [hP0, hP1] using E'.ofReal_le_len P zero_le_one
      _ = E.len P 0 1 := hlen.symm
      _ = ENNReal.ofReal (E.1 (x, y)) := by rw [hP.2, hP0, hP1]
  exact (ENNReal.ofReal_le_ofReal_iff (E.nonneg x y)).mp hmetric

end HigherDimLQGMetric
