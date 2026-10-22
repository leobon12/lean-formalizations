import HigherDimLQGMetric.Sec8.Perturb
import HigherDimLFPP.Perc.Peierls
import HigherDimLFPP.Exist.Discretize

/-!
# Section 8: lattice colours and labeled perturbation sites

At a fixed scale the lattice is coloured by its coordinate residues modulo
`1000d`. Distinct sites of the same colour are separated by at least `10r`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open Set Metric

/-- The coordinatewise residue colour of a lattice index. -/
def sec8Color (d : ℕ) (k : Fin d → ℤ) : Fin d → ℤ :=
  fun i => k i % (1000 * (d : ℤ))

/-- The finite palette of all possible residue colours. -/
def sec8Colors (d : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Ico 0 (1000 * (d : ℤ))

theorem sec8Color_mem_colors {d : ℕ} (hd : 1 ≤ d) (k : Fin d → ℤ) :
    sec8Color d k ∈ sec8Colors d := by
  have hn : (0 : ℤ) < 1000 * (d : ℤ) := by exact_mod_cast (by omega : 0 < 1000 * d)
  simp only [sec8Colors, sec8Color, Fintype.mem_piFinset, Finset.mem_Ico]
  intro i
  exact ⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩

theorem sec8Colors_card (d : ℕ) : (sec8Colors d).card = (1000 * d) ^ d := by
  rw [sec8Colors, Fintype.card_piFinset, Int.card_Ico]
  have hn : ((1000 * (d : ℤ) - 0).toNat) = 1000 * d := by omega
  rw [hn, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Two distinct lattice indices in one colour give centers at least `10r`
apart. This is the separation behind the disjoint radius-`4r` balls. -/
theorem sec8_sameColor_dist {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    {k l : Fin d → ℤ} (hne : k ≠ l) (hc : sec8Color d k = sec8Color d l) :
    10 * r ≤ ‖latPt (r / (100 * d)) k - latPt (r / (100 * d)) l‖ := by
  let n : ℕ := 1000 * d
  have hn : 0 < n := by dsimp [n]; omega
  have heq : ((n - 1 : ℕ) : ℤ) + 1 = 1000 * (d : ℤ) := by
    dsimp [n]
    omega
  have hres : ∀ i, k i % (((n - 1 : ℕ) : ℤ) + 1) =
      l i % (((n - 1 : ℕ) : ℤ) + 1) := by
    intro i
    have h := congrFun hc i
    simpa only [sec8Color, heq] using h
  have hnot := HigherDimLFPP.Perc.not_withinInf_of_emod
    (r := n - 1) hne hres
  change ¬ ∀ i, |k i - l i| ≤ ((n - 1 : ℕ) : ℤ) at hnot
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hi' : ((n - 1 : ℕ) : ℤ) < |k i - l i| := lt_of_not_ge hi
  have hdiffZ : (1000 * (d : ℤ)) ≤ |k i - l i| := by
    rw [← heq]
    omega
  have hdiffR : 1000 * (d : ℝ) ≤ |(k i : ℝ) - (l i : ℝ)| := by
    exact_mod_cast hdiffZ
  let s : ℝ := r / (100 * d)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hs : 0 < s := by dsimp [s]; positivity
  have hcoord := PiLp.norm_apply_le (latPt s k - latPt s l) i
  have hcoord' : |s * (k i : ℝ) - s * (l i : ℝ)| ≤
      ‖latPt s k - latPt s l‖ := by
    simpa only [PiLp.sub_apply, HigherDimLFPP.DGZ.latPt_apply, Real.norm_eq_abs] using hcoord
  have hval : |s * (k i : ℝ) - s * (l i : ℝ)| =
      s * |(k i : ℝ) - (l i : ℝ)| := by
    rw [← mul_sub, abs_mul, abs_of_pos hs]
  calc
    10 * r = s * (1000 * (d : ℝ)) := by dsimp [s]; field_simp; ring
    _ ≤ s * |(k i : ℝ) - (l i : ℝ)| := mul_le_mul_of_nonneg_left hdiffR hs.le
    _ = |s * (k i : ℝ) - s * (l i : ℝ)| := hval.symm
    _ ≤ ‖latPt s k - latPt s l‖ := hcoord'

/-- A finite set of labels in one colour, inside `B_{5R}` and away from both
endpoints.  The final clause says that two labels never share a center. -/
def IsSec8LabeledSet (d J : ℕ) (r R : ℝ) (x y : Rd d)
    (colour : Fin d → ℤ) (Z : Finset (Rd d × ℕ)) : Prop :=
  (∀ q ∈ Z, ∃ k : Fin d → ℤ,
    q.1 = latPt (r / (100 * d)) k ∧ sec8Color d k = colour ∧
    ‖q.1‖ < 5 * R ∧ x ∉ closedBall q.1 (4 * r) ∧
    y ∉ closedBall q.1 (4 * r) ∧ q.2 < J) ∧
  ∀ q ∈ Z, ∀ q' ∈ Z, q.1 = q'.1 → q = q'

/-- The selected labels have the separation used by `lemma82`. -/
theorem IsSec8LabeledSet.separated {d J : ℕ} (hd : 1 ≤ d)
    {r R : ℝ} (hr : 0 < r) {x y : Rd d} {colour : Fin d → ℤ}
    {Z : Finset (Rd d × ℕ)} (hZ : IsSec8LabeledSet d J r R x y colour Z)
    {q q₀ : Rd d × ℕ} (hq : q ∈ Z) (hq₀ : q₀ ∈ Z) (hne : q ≠ q₀) :
    10 * r ≤ ‖q.1 - q₀.1‖ := by
  obtain ⟨k, hk, hc, -, -, -, -⟩ := hZ.1 q hq
  obtain ⟨k₀, hk₀, hc₀, -, -, -, -⟩ := hZ.1 q₀ hq₀
  have hcenters : q.1 ≠ q₀.1 := fun heq => hne (hZ.2 q hq q₀ hq₀ heq)
  have hkk : k ≠ k₀ := by
    intro heq
    apply hcenters
    rw [hk, hk₀, heq]
  have hdist := sec8_sameColor_dist hd hr hkk (hc.trans hc₀.symm)
  simpa only [← hk, ← hk₀] using hdist

end HigherDimLQGMetric
