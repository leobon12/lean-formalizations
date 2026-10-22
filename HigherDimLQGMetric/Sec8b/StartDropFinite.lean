import HigherDimLQGMetric.Sec8b.StartDrop

/-! Finite simultaneous trap shortcuts along the original geodesic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric Topology unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- A visit to the inner ball determines a radius-two window on the path. -/
theorem s7b_window_of_visit (η : C(unitInterval, Rd d))
    (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hx : η 0 ∉ closedBall z (4 * r))
    (hy : η 1 ∉ closedBall z (4 * r))
    (hvisit : ∃ τ : unitInterval, η τ ∈ ball z r) :
    ∃ p : ℝ × ℝ,
      0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧
      s7b_realPath η p.1 ∈ sphere z (2 * r) ∧
      s7b_realPath η p.2 ∈ sphere z (2 * r) ∧
      (∀ t ∈ Ioo p.1 p.2, s7b_realPath η t ∈ ball z (2 * r)) ∧
      ∃ τ : ℝ, p.1 ≤ τ ∧ τ ≤ p.2 ∧ s7b_realPath η τ ∈ ball z r := by
  obtain ⟨τ, hτ⟩ := hvisit
  have hx2 : η 0 ∉ ball z (2 * r) := by
    intro h
    exact hx (mem_closedBall.mpr ((mem_ball.mp h).le.trans (by linarith)))
  have hy2 : η 1 ∉ ball z (2 * r) := by
    intro h
    exact hy (mem_closedBall.mpr ((mem_ball.mp h).le.trans (by linarith)))
  have hτ2 : η τ ∈ ball z (4 * (r / 2)) := by
    rw [show 4 * (r / 2) = 2 * r by ring]
    exact Metric.ball_subset_ball (by linarith : r ≤ 2 * r) hτ
  have hcomp := s7b_component_sphere η z (r / 2) τ
    (by simpa only [show 4 * (r / 2) = 2 * r by ring] using hx2)
    (by simpa only [show 4 * (r / 2) = 2 * r by ring] using hy2) hτ2
  let α := sec8Alpha η z (r / 2) τ
  let β := sec8Beta η z (r / 2) τ
  refine ⟨((α : ℝ), (β : ℝ)), α.property.1, hcomp.1.trans hcomp.2.1,
    β.property.2, ?_, ?_, ?_, (τ : ℝ), hcomp.1.le, hcomp.2.1.le, ?_⟩
  · simpa only [s7b_realPath_coe, show 4 * (r / 2) = 2 * r by ring] using
      hcomp.2.2.1
  · simpa only [s7b_realPath_coe, show 4 * (r / 2) = 2 * r by ring] using
      hcomp.2.2.2.1
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 :=
      ⟨α.property.1.trans_lt ht.1 |>.le, ht.2.le.trans β.property.2⟩
    let u : unitInterval := ⟨t, ht'⟩
    have hu : u ∈ Ioo α β := ht
    simpa only [s7b_realPath, u, projIcc_of_mem _ ht',
      show 4 * (r / 2) = 2 * r by ring] using
      hcomp.2.2.2.2 u hu
  · simpa only [s7b_realPath_coe] using hτ

/-- Disjoint Euclidean trap balls yield disjoint path windows. -/
theorem s7b_windows_disjoint {ι : Type*} (Z : Finset ι)
    (center : ι → Rd d) (win : ι → ℝ × ℝ) (P : ℝ → Rd d)
    {r : ℝ}
    (hballs : (Z : Set ι).Pairwise
      (fun q q' => Disjoint (ball (center q) (4 * r))
        (ball (center q') (4 * r))))
    (hinside : ∀ q ∈ Z, ∀ t ∈ Ioo (win q).1 (win q).2,
      P t ∈ ball (center q) (2 * r))
    (hr : 0 ≤ r) :
    (Z : Set ι).PairwiseDisjoint (fun q => Ioo (win q).1 (win q).2) := by
  intro q hq q' hq' hne
  apply disjoint_left.mpr
  intro t ht ht'
  have hqball : P t ∈ ball (center q) (4 * r) :=
    Metric.ball_subset_ball (by linarith) (hinside q hq t ht)
  have hq'ball : P t ∈ ball (center q') (4 * r) :=
    Metric.ball_subset_ball (by linarith) (hinside q' hq' t ht')
  exact disjoint_left.mp (hballs hq hq' hne) hqball hq'ball

/-- Equation (26): every visited trap ball contributes its own `g s` saving
to the fully discounted distance. -/
theorem s7b_start_drop {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun) (hξ : 0 < ξ)
    {r : ℝ} (hr : 0 < r) (Z : Finset (Rd d × ℕ))
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (ball q.1 (4 * r)) (ball q'.1 (4 * r))))
    (D Dt E : ContMetric d) (hDlen : D.IsLength)
    (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (s : Rd d × ℕ → ℝ) (hs : ∀ q ∈ Z, 0 < s q)
    (htrap : ∀ q ∈ Z,
      TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c'
        D Dt (s q) r q.1 q.2)
    (x y : Rd d) (η : C(unitInterval, Rd d))
    (hη : IsConstSpeedGeod D x y η)
    (haway : ∀ q ∈ Z,
      η 0 ∉ closedBall q.1 (4 * r) ∧ η 1 ∉ closedBall q.1 (4 * r))
    (hvisit : ∀ q ∈ Z, ∃ τ : unitInterval, η τ ∈ ball q.1 r) :
    E.1 (x, y) + T.g * ∑ q ∈ Z, s q ≤ D.1 (x, y) := by
  classical
  let P := s7b_realPath η
  have hPgeod : IsGeod D P := s7b_constSpeed_isGeod D x y η hη
  have hPcont : Continuous P := η.continuous.comp continuous_projIcc
  have hP0 : P 0 = x := by simpa only [P, s7b_realPath_zero] using hη.1
  have hP1 : P 1 = y := by simpa only [P, s7b_realPath_one] using hη.2.1
  have hex : ∀ q ∈ Z, ∃ w : ℝ × ℝ,
      0 ≤ w.1 ∧ w.1 < w.2 ∧ w.2 ≤ 1 ∧
      P w.1 ∈ sphere q.1 (2 * r) ∧ P w.2 ∈ sphere q.1 (2 * r) ∧
      (∀ t ∈ Ioo w.1 w.2, P t ∈ ball q.1 (2 * r)) ∧
      ∃ τ : ℝ, w.1 ≤ τ ∧ τ ≤ w.2 ∧ P τ ∈ ball q.1 r := by
    intro q hq
    exact s7b_window_of_visit η q.1 hr (haway q hq).1
      (haway q hq).2 (hvisit q hq)
  let win : Rd d × ℕ → ℝ × ℝ :=
    fun q => if hq : q ∈ Z then Classical.choose (hex q hq) else (0, 0)
  have hwin : ∀ q ∈ Z,
      0 ≤ (win q).1 ∧ (win q).1 < (win q).2 ∧ (win q).2 ≤ 1 ∧
      P (win q).1 ∈ sphere q.1 (2 * r) ∧
      P (win q).2 ∈ sphere q.1 (2 * r) ∧
      (∀ t ∈ Ioo (win q).1 (win q).2, P t ∈ ball q.1 (2 * r)) ∧
      ∃ τ : ℝ, (win q).1 ≤ τ ∧ τ ≤ (win q).2 ∧
        P τ ∈ ball q.1 r := by
    intro q hq
    simpa only [win, dite_eq_left hq] using Classical.choose_spec (hex q hq)
  have htimeDisj : (Z : Set (Rd d × ℕ)).PairwiseDisjoint
      (fun q => Ioo (win q).1 (win q).2) :=
    s7b_windows_disjoint Z Prod.fst win P hdisj
      (fun q hq => (hwin q hq).2.2.2.2.2.1) hr.le
  have hlocal : ∀ q ∈ Z,
      ENNReal.ofReal (2 * T.a * s q) ≤
        D.len P (win q).1 (win q).2 := by
    intro q hq
    obtain ⟨-, -, -, hα, hβ, -, ⟨τ, hατ, hτβ, hτ⟩⟩ := hwin q hq
    exact s7b_two_crossings T (hs q hq).le hr (htrap q hq)
      P hατ hτβ hPcont.continuousOn hα hβ hτ
  have hshort : ∀ q ∈ Z,
      ENNReal.ofReal (E.1 (P (win q).1, P (win q).2)) ≤
        ENNReal.ofReal ((2 * T.a - T.g) * s q) := by
    intro q hq
    obtain ⟨-, -, -, hα, hβ, -, -⟩ := hwin q hq
    have hconn := s7b_T2_connection T hr hJ hdisj hq D Dt E hDlen
      (htrap q hq) hE (P (win q).1) (P (win q).2)
      (subset_closure (s7b_sphere2_mem_collector T hr q.1 _ hα))
      (subset_closure (s7b_sphere2_mem_collector T hr q.1 _ hβ))
    exact (E.ofReal_le_internal _ _ _).trans hconn
  have hglobal : ∀ a b : ℝ, a ≤ b → E.len P a b ≤ D.len P a b := by
    intro a b _
    exact s7b_discount_len_le T hξ hJ D E hE P hPcont.continuousOn
  have hmany := s7b_many_window_drop D E P Z win
    (fun q => 2 * T.a * s q) (fun q => (2 * T.a - T.g) * s q)
    htimeDisj (fun q hq => (hwin q hq).2.1) hlocal hshort hglobal
    0 1 (fun q hq => ⟨(hwin q hq).1, (hwin q hq).2.2.1⟩) zero_le_one
  rw [hPgeod.2, hP0, hP1] at hmany
  have hLpos : ∀ q ∈ Z, 0 ≤ 2 * T.a * s q := by
    intro q hq
    exact mul_nonneg (mul_nonneg (by norm_num) T.constants.1.le) (hs q hq).le
  have hCpos : ∀ q ∈ Z, 0 ≤ (2 * T.a - T.g) * s q := by
    intro q hq
    have hg := T.constants.2.2.2.1
    rw [hg]
    nlinarith [T.constants.1, hs q hq]
  have hsumL : (∑ q ∈ Z, ENNReal.ofReal (2 * T.a * s q)) =
      ENNReal.ofReal (∑ q ∈ Z, 2 * T.a * s q) :=
    (ENNReal.ofReal_sum_of_nonneg hLpos).symm
  have hsumC : (∑ q ∈ Z, ENNReal.ofReal ((2 * T.a - T.g) * s q)) =
      ENNReal.ofReal (∑ q ∈ Z, (2 * T.a - T.g) * s q) :=
    (ENNReal.ofReal_sum_of_nonneg hCpos).symm
  rw [hsumL, hsumC] at hmany
  have hLsum : 0 ≤ ∑ q ∈ Z, 2 * T.a * s q := Finset.sum_nonneg hLpos
  have hCsum : 0 ≤ ∑ q ∈ Z, (2 * T.a - T.g) * s q :=
    Finset.sum_nonneg hCpos
  have hreal : E.1 (x, y) + ∑ q ∈ Z, 2 * T.a * s q ≤
      D.1 (x, y) + ∑ q ∈ Z, (2 * T.a - T.g) * s q := by
    apply (ENNReal.ofReal_le_ofReal_iff (add_nonneg (D.nonneg x y) hCsum)).mp
    rw [ENNReal.ofReal_add (E.nonneg x y) hLsum,
      ENNReal.ofReal_add (D.nonneg x y) hCsum]
    exact hmany
  simp only [← Finset.mul_sum] at hreal
  nlinarith only [hreal]

end HigherDimLQGMetric
