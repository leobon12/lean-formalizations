import QuantumZipper.Loewner.Curves
import QuantumZipper.Proofs.Complex.TopoEilenberg
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JORDAN-CHORD: the two sides of a simple chord are disjoint

* `chordSides_disjoint`: for a simple chord `η` from `0` to `∞` in `ℍ` (`IsSimpleChord`),
  `leftComponent η` and `rightComponent η` are disjoint.

**Source.** This is the separation of a domain by a cross-cut: M. H. A. Newman, *Elements of the
Topology of Plane Sets of Points* (2nd ed. 1964), Ch. V, Theorem 11.7 (printed p. 118, PDF
p. 63) (a cross-cut of a Jordan domain whose end-points separate the boundary separates the
domain); cf. Pommerenke, *Boundary Behaviour of Conformal Maps*, §1.3. The proof goes through
Eilenberg's criterion (R. B. Burckel, *Classical Analysis in the Complex Plane*, Exercise
4.37(i), printed p. 215; node T2 of this repository, `CA.Topo.hasLogOn_of_not_separates`), as in
the proof of Janiszewski's theorem there. The concrete computation below is an **own elementary
argument** (cost rule: short, standard).

**Proof.** Suppose `z` lies in both sides: paths `p` from `z` to `x < 0` and `q` from `z` to
`y > 0` run in `ℍ \ η` except at their ends. Let `Q = range p ∪ range q` (compact, connected,
`0 ∉ Q`), `m = min_Q ‖·‖ > 0`, `ε = m/2`, `S = [x, y] ⊆ ℝ`, `J = Q ∪ S`.
1. `a = iε` and `b = -iε` lie in the same component of `ℂ \ J`: `b` is in the lower half plane
   (unbounded, connected, off `J`), `a` is in `(ball 0 m ∩ ℍ) ∪ η((0,∞))` (unbounded since
   `‖η t‖ → ∞`, connected since `η t → 0`, off `J`); both lie in the unbounded component (T6).
2. By Eilenberg, `f z = (z - iε)/(z + iε)` has a continuous logarithm `G` on `J`.
3. On `Q`, `Re f > 0` (`‖z‖ > ε`), so `G - Log f` is constant on `Q`; on `S`,
   `f t = e^{-2i arg(t + iε)}`, so `G + 2i arg(· + iε)` is constant on `S`. At `y > 0`,
   `Log f y = -2i arg(y + iε)`; at `x < 0`, `Log f x = -2i arg(x + iε) + 2πi`. Comparing the two
   constants at `x` and `y` gives `2πi = 0`.
-/

noncomputable section

open Set Filter Topology Metric Complex Real

namespace QuantumZipper
namespace JordanChord

open QuantumZipper.CA.Topo

/-- Two continuous logarithms of the same function on a preconnected set differ by a constant. -/
theorem log_sub_eq_of_isPreconnected {S : Set ℂ} (hS : IsPreconnected S) {L₁ L₂ : ℂ → ℂ}
    (h₁ : ContinuousOn L₁ S) (h₂ : ContinuousOn L₂ S)
    (he : ∀ z ∈ S, exp (L₁ z) = exp (L₂ z)) {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) :
    L₁ u - L₂ u = L₁ v - L₂ v := by
  have h2 := two_pi_I_ne_zero'
  have hmaps : MapsTo (fun z => (L₁ z - L₂ z) / (2 * π * I)) S (range ((↑) : ℤ → ℂ)) := by
    intro z hz
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 (he z hz)
    exact ⟨n, by simp only [hn, add_sub_cancel_left, mul_div_cancel_right₀ _ h2]⟩
  have hc := hS.constant_of_mapsTo Complex.isClosedEmbedding_intCast.isInducing.isDiscrete_range
    ((h₁.sub h₂).div_const _) hmaps hu hv
  exact (div_left_inj' h2).1 hc

/-- Two numbers with the same exponential and imaginary parts closer than `2π` are equal. -/
theorem eq_of_exp_eq_of_abs_im_sub_lt {A B : ℂ} (h : exp A = exp B)
    (hi : |A.im - B.im| < 2 * π) : A = B := by
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
  have him : A.im - B.im = n * (2 * π) := by rw [hn]; simp
  have hn0 : n = 0 := by
    rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hi
    have h1 : |(n : ℝ)| * (2 * π) < 1 * (2 * π) := by linarith
    have h3 := abs_lt.1 (lt_of_mul_lt_mul_right h1 (by positivity))
    have h4 : -1 < n := by exact_mod_cast h3.1
    have h5 : n < 1 := by exact_mod_cast h3.2
    omega
  rw [hn, hn0]; simp

/-- The Möbius function `z ↦ (z - iε)/(z + iε)` (Eilenberg's function for `a = iε`, `b = -iε`). -/
def chordF (ε : ℝ) (z : ℂ) : ℂ := (z - ε * I) / (z + ε * I)

/-- The continuous logarithm of `chordF ε` along the real line. -/
def chordL (ε : ℝ) (z : ℂ) : ℂ := -2 * (arg (z + ε * I) : ℂ) * I

theorem exp_chordL {ε : ℝ} (hε : 0 < ε) (t : ℝ) : exp (chordL ε t) = chordF ε t := by
  set w : ℂ := (t : ℂ) + ε * I with hw
  have hw0 : w ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp [hw] at this
    linarith
  have hc : (starRingEnd ℂ) w = (t : ℂ) - ε * I := Complex.ext (by simp [hw]) (by simp [hw])
  have h1 := norm_mul_exp_arg_mul_I w
  have h2 : (starRingEnd ℂ) w = ‖w‖ * exp (-(arg w : ℂ) * I) := by
    conv_lhs => rw [← h1]
    rw [map_mul, ← exp_conj, conj_ofReal, map_mul, conj_ofReal, conj_I]
    ring_nf
  unfold chordL chordF
  rw [← hw, ← hc, eq_div_iff hw0, h2]
  calc exp (-2 * (arg w : ℂ) * I) * w
      = exp (-2 * (arg w : ℂ) * I) * (‖w‖ * exp (arg w * I)) := by rw [h1]
    _ = ‖w‖ * exp (-2 * (arg w : ℂ) * I + arg w * I) := by rw [Complex.exp_add]; ring
    _ = ‖w‖ * exp (-(arg w : ℂ) * I) := by ring_nf

theorem chordF_ne_zero {ε : ℝ} (hε : 0 < ε) (t : ℝ) : chordF ε t ≠ 0 := by
  rw [← exp_chordL hε]; exact exp_ne_zero _

theorem chordL_im (ε t : ℝ) : (chordL ε t).im = -2 * arg ((t : ℂ) + ε * I) := by
  simp [chordL]

/-- Junction at a positive real point. -/
theorem log_chordF_of_pos {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    log (chordF ε t) = chordL ε t := by
  refine eq_of_exp_eq_of_abs_im_sub_lt ?_ ?_
  · rw [exp_log (chordF_ne_zero hε t), exp_chordL hε]
  · rw [log_im, chordL_im]
    have h1 := neg_pi_lt_arg (chordF ε t)
    have h2 := arg_le_pi (chordF ε t)
    have h3 : 0 ≤ arg ((t : ℂ) + ε * I) := arg_nonneg_iff.2 (by simp; linarith)
    have h4 := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simpa using ht) :
      0 < ((t : ℂ) + ε * I).re ∨ _))
    rw [abs_lt]; constructor <;> linarith [Real.pi_pos]

/-- Junction at a negative real point. -/
theorem log_chordF_of_neg {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t < 0) :
    log (chordF ε t) = chordL ε t + 2 * π * I := by
  refine eq_of_exp_eq_of_abs_im_sub_lt ?_ ?_
  · rw [exp_log (chordF_ne_zero hε t), Complex.exp_add, exp_chordL hε, exp_two_pi_mul_I, mul_one]
  · have hi : (chordL ε t + 2 * π * I).im = -2 * arg ((t : ℂ) + ε * I) + 2 * π := by
      rw [add_im, chordL_im]; simp
    rw [log_im, hi]
    have h1 := neg_pi_lt_arg (chordF ε t)
    have h2 := arg_le_pi (chordF ε t)
    have h3 : 0 ≤ arg ((t : ℂ) + ε * I) := arg_nonneg_iff.2 (by simp; linarith)
    have h5 := arg_le_pi ((t : ℂ) + ε * I)
    have h4 : π / 2 < |arg ((t : ℂ) + ε * I)| := by
      rw [← not_le, abs_arg_le_pi_div_two_iff]; simp; linarith
    rw [abs_of_nonneg h3] at h4
    rw [abs_lt]; constructor <;> linarith [Real.pi_pos]

/-- Off the disc of radius `ε`, `chordF ε` takes values in the right half plane. -/
theorem chordF_mem_slitPlane {ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : ε < ‖w‖) :
    chordF ε w ∈ slitPlane := by
  have hd : w + ε * I ≠ 0 := fun h => by
    have : w = -(ε * I) := eq_neg_of_add_eq_zero_left h
    rw [this, norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hε.le] at hw
    exact lt_irrefl _ hw
  have hn : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by rw [Complex.sq_norm, normSq_apply]
  have hεw : ε ^ 2 < ‖w‖ ^ 2 := by nlinarith
  refine mem_slitPlane_iff.2 (Or.inl ?_)
  unfold chordF
  rw [Complex.div_re, ← add_div]
  refine div_pos ?_ (normSq_pos.2 hd)
  simp
  nlinarith

theorem continuousAt_chordF {ε : ℝ} {w : ℂ} (hd : w + ε * I ≠ 0) :
    ContinuousAt (chordF ε) w :=
  (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const) hd

theorem continuousAt_chordL {ε : ℝ} {c : ℂ} (hc : c + ε * I ∈ slitPlane) :
    ContinuousAt (chordL ε) c := by
  have h1 : ContinuousAt (fun z : ℂ => arg (z + ε * I)) c :=
    ContinuousAt.comp (g := arg) (f := fun z : ℂ => z + ε * I) (continuousAt_arg hc) (by fun_prop)
  have h2 : ContinuousAt (fun z : ℂ => ((arg (z + ε * I) : ℝ) : ℂ)) c :=
    continuous_ofReal.continuousAt.comp h1
  exact (h2.const_mul (-2)).mul continuousAt_const

theorem not_isBounded_of_forall {S : Set ℂ} (h : ∀ C : ℝ, ∃ s ∈ S, C < ‖s‖) :
    ¬ Bornology.IsBounded S := fun hb => by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  obtain ⟨s, hs, hlt⟩ := h C
  exact lt_irrefl _ (hlt.trans_le (hC s hs))

/-- **The two sides of a simple chord are disjoint** (Newman 1964, Ch. V, Thm 11.7; proof via
Eilenberg's criterion, see the module docstring). -/
theorem chordSides_disjoint {η : ℝ → ℂ} (hη : IsSimpleChord η) :
    Disjoint (leftComponent η) (rightComponent η) := by
  obtain ⟨h00, hcont, -, hH, hinf⟩ := hη
  rw [Set.disjoint_left]
  rintro z ⟨-, x, hx, p, hp⟩ ⟨-, y, hy, q, hq⟩
  set Q : Set ℂ := range p ∪ range q with hQdef
  have hQc : IsCompact Q := (isCompact_range p.continuous).union (isCompact_range q.continuous)
  have hQp : IsPreconnected Q := (isPreconnected_range p.continuous).union z ⟨0, p.source⟩
    ⟨0, q.source⟩ (isPreconnected_range q.continuous)
  have hQmem : ∀ w ∈ Q, w ∈ H \ η '' Ici 0 ∨ w = x ∨ w = y := by
    rintro w (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · by_cases hs : s = 1
      · subst hs; exact Or.inr (Or.inl p.target)
      · exact Or.inl (hp s hs)
    · by_cases hs : s = 1
      · subst hs; exact Or.inr (Or.inr q.target)
      · exact Or.inl (hq s hs)
  have hQim : ∀ w ∈ Q, 0 ≤ w.im := fun w hw => by
    rcases hQmem w hw with h | rfl | rfl
    · exact le_of_lt h.1
    · simp
    · simp
  have hxQ : (x : ℂ) ∈ Q := Or.inl ⟨1, p.target⟩
  have hyQ : (y : ℂ) ∈ Q := Or.inr ⟨1, q.target⟩
  have hQ0 : (0 : ℂ) ∉ Q := fun h => by
    rcases hQmem 0 h with h | h | h
    · exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h.1)
    · have : x = 0 := by exact_mod_cast h.symm
      linarith
    · have : y = 0 := by exact_mod_cast h.symm
      linarith
  obtain ⟨w₀, hw₀Q, hw₀min⟩ := hQc.exists_isMinOn ⟨x, hxQ⟩ continuous_norm.continuousOn
  set m := ‖w₀‖ with hmdef
  have hm : 0 < m := norm_pos_iff.2 fun h => hQ0 (h ▸ hw₀Q)
  have hQm : ∀ w ∈ Q, m ≤ ‖w‖ := fun w hw => hw₀min hw
  set ε := m / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hεm : ε < m := by linarith
  set S : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc x y with hSdef
  have hSc : IsCompact S := isCompact_Icc.image continuous_ofReal
  have hSp : IsPreconnected S := isPreconnected_Icc.image _ continuous_ofReal.continuousOn
  have hSim : ∀ c ∈ S, c.im = 0 := by rintro c ⟨t, -, rfl⟩; simp
  set J := Q ∪ S with hJdef
  have hJc : IsCompact J := hQc.union hSc
  obtain ⟨R, -, hR⟩ := hJc.isBounded.subset_ball_lt 0 0
  set wf : ℂ := ((|R| + 1 : ℝ) : ℂ) with hwf
  have hwfR : R < ‖wf‖ := by
    rw [hwf, norm_real, Real.norm_of_nonneg (by positivity)]
    linarith [le_abs_self R]
  -- the lower half plane lies in the unbounded component
  set S₁ : Set ℂ := {c : ℂ | c.im < 0} with hS₁
  have hS₁J : Disjoint S₁ J := Set.disjoint_left.2 fun c hc hcJ => by
    rcases hcJ with hcQ | hcS
    · exact absurd (hQim c hcQ) (not_le.2 hc)
    · have h1 := hSim c hcS
      have h2 : c.im < 0 := hc
      linarith
  have hS₁u : ¬ Bornology.IsBounded S₁ := not_isBounded_of_forall fun C =>
    ⟨((-(|C| + 1) : ℝ) : ℂ) * I, by
      show (((-(|C| + 1) : ℝ) : ℂ) * I).im < 0
      have : (((-(|C| + 1) : ℝ) : ℂ) * I).im = -(|C| + 1) := by simp
      rw [this]; linarith [abs_nonneg C], by
      rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by positivity)]
      linarith [le_abs_self C]⟩
  have hb := subset_connectedComponentIn_compl_of_unbounded hR
    (convex_halfSpace_im_lt 0).isPreconnected hS₁u hS₁J hwfR
    (show -((ε : ℂ) * I) ∈ S₁ by show (-((ε : ℂ) * I)).im < 0; simp; exact hε)
  -- the upper small half disc together with the chord lies in the unbounded component
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuousWithinAt_iff.1 (hcont 0 (mem_Ici.2 le_rfl)) m hm
  have ht₀ : η (δ / 2) ∈ ball (0 : ℂ) m ∩ H := by
    refine ⟨?_, hH _ (by positivity)⟩
    have := hδη (show δ / 2 ∈ Ici (0 : ℝ) from mem_Ici.2 (by positivity))
      (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    rwa [h00] at this
  set S₂ : Set ℂ := (ball (0 : ℂ) m ∩ H) ∪ η '' Ioi 0 with hS₂
  have hS₂p : IsPreconnected S₂ :=
    IsPreconnected.union (η (δ / 2)) ht₀ ⟨δ / 2, show (0 : ℝ) < δ / 2 by positivity, rfl⟩
      ((convex_ball (0 : ℂ) m).inter (convex_halfSpace_im_gt 0)).isPreconnected
      (isPreconnected_Ioi.image η (hcont.mono Ioi_subset_Ici_self))
  have hS₂u : ¬ Bornology.IsBounded S₂ := not_isBounded_of_forall fun C => by
    obtain ⟨t, h1, h2⟩ := ((hinf.eventually_gt_atTop C).and (eventually_gt_atTop 0)).exists
    exact ⟨η t, Or.inr ⟨t, h2, rfl⟩, h1⟩
  have hS₂J : Disjoint S₂ J := Set.disjoint_left.2 fun c hc hcJ => by
    rcases hc with ⟨hcb, hcH⟩ | ⟨t, ht, rfl⟩
    · rcases hcJ with hcQ | hcS
      · rw [mem_ball_zero_iff] at hcb
        exact absurd (hQm c hcQ) (not_le.2 hcb)
      · have h1 := hSim c hcS
        have h2 : 0 < c.im := hcH
        linarith
    · have hηH : 0 < (η t).im := hH t ht
      rcases hcJ with hcQ | hcS
      · rcases hQmem _ hcQ with h | h | h
        · exact h.2 ⟨t, mem_Ici.2 (le_of_lt (mem_Ioi.1 ht)), rfl⟩
        · have : (η t).im = 0 := by rw [h]; simp
          linarith
        · have : (η t).im = 0 := by rw [h]; simp
          linarith
      · have := hSim _ hcS
        linarith
  have ha := subset_connectedComponentIn_compl_of_unbounded hR hS₂p hS₂u hS₂J hwfR
    (show (ε : ℂ) * I ∈ S₂ from Or.inl ⟨by
      rw [mem_ball_zero_iff, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_of_nonneg hε.le]; exact hεm, by show (0 : ℝ) < ((ε : ℂ) * I).im; simpa⟩)
  have hab : -((ε : ℂ) * I) ∈ connectedComponentIn Jᶜ ((ε : ℂ) * I) := by
    rw [← connectedComponentIn_eq ha]; exact hb
  -- Eilenberg: a continuous logarithm of `chordF ε` on `J`
  obtain ⟨G, hGc, hG⟩ := hasLogOn_of_not_separates hJc hab
  have hG' : ∀ w ∈ J, exp (G w) = chordF ε w := fun w hw => by
    rw [hG w hw]; simp only [chordF, sub_neg_eq_add]
  -- comparison on `Q`
  have hfQ : ∀ w ∈ Q, chordF ε w ∈ slitPlane := fun w hw =>
    chordF_mem_slitPlane hε (hεm.trans_le (hQm w hw))
  have hLQ : ContinuousOn (fun w => log (chordF ε w)) Q := fun w hw => by
    have hd : w + ε * I ≠ 0 := fun h => by
      have := chordF_mem_slitPlane hε (hεm.trans_le (hQm w hw))
      have h' : chordF ε w = (w - ε * I) / 0 := by rw [chordF, h]
      rw [h', div_zero] at this
      exact slitPlane_ne_zero this rfl
    exact ((continuousAt_clog (hfQ w hw)).comp (continuousAt_chordF hd)).continuousWithinAt
  have e2 := log_sub_eq_of_isPreconnected hQp (hGc.mono subset_union_left) hLQ
    (fun w hw => by rw [hG' w (Or.inl hw), exp_log (slitPlane_ne_zero (hfQ w hw))]) hyQ hxQ
  -- comparison on `S`
  have hLS : ContinuousOn (chordL ε) S := by
    rintro c ⟨t, -, rfl⟩
    refine (continuousAt_chordL (mem_slitPlane_iff.2 (Or.inr ?_))).continuousWithinAt
    simp; exact hε.ne'
  have hxS : (x : ℂ) ∈ S := ⟨x, left_mem_Icc.2 (hx.le.trans hy.le), rfl⟩
  have hyS : (y : ℂ) ∈ S := ⟨y, right_mem_Icc.2 (hx.le.trans hy.le), rfl⟩
  have e1 := log_sub_eq_of_isPreconnected hSp (hGc.mono subset_union_right) hLS
    (by rintro c ⟨t, ht, rfl⟩; rw [hG' _ (Or.inr ⟨t, ht, rfl⟩), exp_chordL hε]) hyS hxS
  have j1 := log_chordF_of_pos hε hy
  have j2 := log_chordF_of_neg hε hx
  exact two_pi_I_ne_zero' (by linear_combination e2 - e1 + j1 - j2)

end JordanChord
end QuantumZipper
