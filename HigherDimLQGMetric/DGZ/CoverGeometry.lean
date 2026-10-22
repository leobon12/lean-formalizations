import HigherDimLQGMetric.DGZ.NiceBoxOscBound
import HigherDimLQGMetric.DGZ.BypassDefs

/-!
# Lattice geometry for the DGZ bypass cover

The parent box is chosen coordinatewise, with a margin from every interior face.  This is used
in the one-centre-at-a-time construction of Proposition 5.10.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

/-- Integer parent selection.  `M = NT` is the big-box radius in fine lattice units. -/
private theorem exists_coverParentCoord {N T : ℕ} (hN : 1 ≤ N) (hT : 1 ≤ T)
    {y : ℤ} (hy : |y| ≤ (N * T : ℕ) - 1) :
    ∃ u : ℤ, |u| ≤ (T : ℤ) - 1 ∧ |y - (N : ℤ) * u| ≤ (N : ℤ) - 1 ∧
      ∀ y' : ℤ, |y'| ≤ (N * T : ℕ) - 1 → (N : ℤ) ≤ |y' - (N : ℤ) * u| →
        (N : ℤ) ≤ 2 * |y - y'| := by
  let M : ℤ := (N * T : ℕ)
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hT' : (0 : ℤ) < T := by exact_mod_cast hT
  have hM : M = (N : ℤ) * T := by simp [M]
  have hy' : |y| ≤ M - 1 := by simpa [M] using hy
  have hylo : -M + 1 ≤ y := by
    have := (abs_le.mp hy').1
    omega
  have hyhi : y ≤ M - 1 := (abs_le.mp hy').2
  by_cases hleft : y < -M + N
  · refine ⟨-T + 1, ?_, ?_, ?_⟩
    · rw [abs_of_nonpos (by omega : -((T : ℤ)) + 1 ≤ 0)]
      omega
    · have heq : (N : ℤ) * (-T + 1) = -M + N := by rw [hM]; ring
      rw [heq]
      rw [abs_of_nonpos (by omega : y - (-M + (N : ℤ)) ≤ 0)]
      omega
    · intro y' hy'' hfar
      have heq : (N : ℤ) * (-T + 1) = -M + N := by rw [hM]; ring
      rw [heq] at hfar
      have hyy : |y'| ≤ M - 1 := by simpa [M] using hy''
      have hyylo : -M + 1 ≤ y' := by have := (abs_le.mp hyy).1; omega
      rcases le_total (y' - (-M + (N : ℤ))) 0 with hneg | hpos
      · rw [abs_of_nonpos hneg] at hfar
        omega
      · rw [abs_of_nonneg hpos] at hfar
        have hdiff : y ≤ y' := by omega
        rw [abs_of_nonpos (by omega : y - y' ≤ 0)]
        omega
  · by_cases hright : M - N < y
    · refine ⟨T - 1, ?_, ?_, ?_⟩
      · rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ T - 1)]
      · have heq : (N : ℤ) * (T - 1) = M - N := by rw [hM]; ring
        rw [heq]
        rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ y - (M - N))]
        omega
      · intro y' hy'' hfar
        have heq : (N : ℤ) * (T - 1) = M - N := by rw [hM]; ring
        rw [heq] at hfar
        have hyy : |y'| ≤ M - 1 := by simpa [M] using hy''
        have hyyhi : y' ≤ M - 1 := (abs_le.mp hyy).2
        rcases le_total (y' - (M - (N : ℤ))) 0 with hneg | hpos
        · rw [abs_of_nonpos hneg] at hfar
          have hdiff : y' ≤ y := by omega
          rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ y - y')]
          omega
        · rw [abs_of_nonneg hpos] at hfar
          omega
    · let q : ℤ := y / (N : ℤ)
      let r : ℤ := y % (N : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
      have hrN : r < N := Int.emod_lt_of_pos _ hN'
      have hdiv : (N : ℤ) * q + r = y := by
        dsimp [q, r]
        simpa [add_comm, mul_comm] using (Int.emod_add_mul_ediv y (N : ℤ))
      have hqlo : -T + 1 ≤ q := by
        by_contra h
        have hq : q ≤ -T := by omega
        have hm := mul_le_mul_of_nonneg_left hq hN'.le
        have heq : (N : ℤ) * -T = -M := by rw [hM]; ring
        rw [heq] at hm
        omega
      have hqhi : q ≤ T - 1 := by
        by_contra h
        have hq : T ≤ q := by omega
        have hm := mul_le_mul_of_nonneg_left hq hN'.le
        rw [← hM] at hm
        omega
      by_cases hnear : 2 * r ≤ N
      · refine ⟨q, ?_, ?_, ?_⟩
        · rw [abs_le]; constructor <;> omega
        · have heq : y - (N : ℤ) * q = r := by omega
          rw [heq, abs_of_nonneg hr0]
          omega
        · intro y' _ hfar
          have heq : y - (N : ℤ) * q = r := by omega
          have htri := abs_sub_le y' y ((N : ℤ) * q)
          rw [heq, abs_of_nonneg hr0] at htri
          rw [abs_sub_comm y' y] at htri
          omega
      · have hrpos : 0 < r := by omega
        have hqhi' : q + 1 ≤ T - 1 := by
          by_contra h
          have hq : T - 1 ≤ q := by omega
          have hm := mul_le_mul_of_nonneg_left hq hN'.le
          have heq : (N : ℤ) * (T - 1) = M - N := by rw [hM]; ring
          rw [heq] at hm
          omega
        refine ⟨q + 1, ?_, ?_, ?_⟩
        · rw [abs_le]; constructor <;> omega
        · have hmul : (N : ℤ) * (q + 1) = N * q + N := by ring
          have heq : y - (N : ℤ) * (q + 1) = r - N := by rw [hmul]; omega
          rw [heq, abs_of_nonpos (by omega : r - (N : ℤ) ≤ 0)]
          omega
        · intro y' _ hfar
          have hmul : (N : ℤ) * (q + 1) = N * q + N := by ring
          have heq : y - (N : ℤ) * (q + 1) = r - N := by rw [hmul]; omega
          have htri := abs_sub_le y' y ((N : ℤ) * (q + 1))
          rw [heq, abs_of_nonpos (by omega : r - (N : ℤ) ≤ 0)] at htri
          rw [abs_sub_comm y' y] at htri
          omega

variable {d : ℕ}

/-- An `s`-box in `B₂(0)` has a containing `Ns`-box in `B₂(0)`.  If another `s`-box
in `B₂(0)` leaves this parent, its centre is at least `N/2` fine lattice units away. -/
theorem exists_coverParent {s : ℝ} (hs : 0 < s) {N T : ℕ} (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hscale : s * (N * T : ℕ) = 2) (y : Zd d)
    (hy : obox (latPt s y) s ⊆ obox (0 : Rd d) 2) :
    ∃ u : Zd d,
      obox (latPt s y) s ⊆ obox (latPt (N * s) u) (N * s) ∧
      obox (latPt (N * s) u) (N * s) ⊆ obox (0 : Rd d) 2 ∧
      ∀ y' : Zd d, obox (latPt s y') s ⊆ obox (0 : Rd d) 2 →
        ¬ obox (latPt s y') s ⊆ obox (latPt (N * s) u) (N * s) →
          ∃ i : Fin d, (N : ℤ) ≤ 2 * |y i - y' i| := by
  let M := N * T
  have hscale' : s * M = 2 := hscale
  have hY (v : Zd d) (hv : obox (latPt s v) s ⊆ obox (0 : Rd d) 2) :
      ∀ i, |v i| ≤ (M : ℤ) - 1 := by
    have h : obox (latPt s v) s ⊆ obox (latPt s (0 : Zd d)) (s * M) := by
      simpa only [hscale', HigherDimLFPP.DGZ.latPt_zero] using hv
    intro i
    simpa only [Pi.zero_apply, sub_zero] using ((obox_latPt_subset_iff hs).mp h i)
  choose u hu using fun i : Fin d => exists_coverParentCoord hN hT (hY y hy i)
  refine ⟨u, ?_, ?_, ?_⟩
  · exact (obox_latPt_subset_scale_iff hs N u y).2 fun i => (hu i).2.1
  · have hsub : obox (latPt (N * s) u) (N * s) ⊆
        obox (latPt (N * s) (0 : Zd d)) ((N * s) * T) :=
      (obox_latPt_subset_iff (by positivity : 0 < (N : ℝ) * s)).2
        (fun i => by simpa [WithinInf] using (hu i).1)
    have heq : (N : ℝ) * s * T = 2 := by
      rw [mul_comm (N : ℝ) s, mul_assoc]
      convert hscale using 1
      push_cast
      ring
    simpa only [heq, HigherDimLFPP.DGZ.latPt_zero] using hsub
  · intro y' hy' hnot
    have hnot' : ¬ ∀ i, |y' i - (N : ℤ) * u i| ≤ (N : ℤ) - 1 := by
      intro h
      exact hnot ((obox_latPt_subset_scale_iff hs N u y').2 h)
    push Not at hnot'
    obtain ⟨i, hi⟩ := hnot'
    refine ⟨i, (hu i).2.2 (y' i) (hY y' hy' i) ?_⟩
    omega

/-- Dyadic specialization of the parent choice to the scales of `NiceParams`. -/
theorem exists_niceParent (p : NiceParams) (hmono : Monotone p.a) {j : ℕ}
    (hjn : p.a (j + 1) ≤ p.n) (y : Zd d)
    (hy : obox (latPt (p.s j) y) (p.s j) ⊆ obox (0 : Rd d) 2) :
    ∃ u : Zd d,
      obox (latPt (p.s j) y) (p.s j) ⊆
        obox (latPt (p.s (j + 1)) u) (p.s (j + 1)) ∧
      obox (latPt (p.s (j + 1)) u) (p.s (j + 1)) ⊆ obox (0 : Rd d) 2 ∧
      ∀ y' : Zd d, obox (latPt (p.s j) y') (p.s j) ⊆ obox (0 : Rd d) 2 →
        ¬ obox (latPt (p.s j) y') (p.s j) ⊆
          obox (latPt (p.s (j + 1)) u) (p.s (j + 1)) →
          ∃ i : Fin d, ((2 ^ (p.a (j + 1) - p.a j) : ℕ) : ℤ) ≤ 2 * |y i - y' i| := by
  let N := 2 ^ (p.a (j + 1) - p.a j)
  let T := 2 ^ (p.n - p.a (j + 1) + 1)
  have hN : 1 ≤ N := by dsimp [N]; exact Nat.one_le_pow _ _ (by omega)
  have hT : 1 ≤ T := by dsimp [T]; exact Nat.one_le_pow _ _ (by omega)
  have hsucc := p.s_succ_eq (hmono (Nat.le_succ j)) hjn
  have hscale : p.s j * (N * T : ℕ) = 2 := by
    have htop := p.s_mul_two_pow (j + 1)
    have hpow : (N : ℝ) * p.s j = p.s (j + 1) := by
      rw [hsucc]
      simp only [N, Nat.cast_pow, Nat.cast_ofNat]
    calc p.s j * ((N * T : ℕ) : ℝ) = ((N : ℝ) * p.s j) * T := by push_cast; ring
      _ = p.s (j + 1) * T := by rw [hpow]
      _ = 2 := htop
  obtain ⟨u, hsub, hbig, hmargin⟩ := exists_coverParent (p.s_pos j) hN hT hscale y hy
  have heq : (N : ℝ) * p.s j = p.s (j + 1) := by
    rw [hsucc]
    simp only [N, Nat.cast_pow, Nat.cast_ofNat]
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa only [heq] using hsub
  · simpa only [heq] using hbig
  · intro y' hy' hnot
    exact hmargin y' hy' (by simpa only [heq] using hnot)

/-- Inclusion of fine lattice boxes is an integer bound on their centres. -/
theorem cover_fine_close {s : ℝ} (hs : 0 < s) {R : ℕ} {y z : Zd d}
    (h : obox (latPt s y) s ⊆ obox (latPt s z) (R * s)) :
    ∀ i, |y i - z i| ≤ (R : ℤ) - 1 := by
  have h' : obox (latPt s y) s ⊆ obox (latPt s z) (s * R) := by
    simpa only [mul_comm (R : ℝ) s] using h
  exact (obox_latPt_subset_iff hs).mp h'

/-- The integer parent margin and the two `R`-box inclusions imply the separation in
`IsBypassCover`. -/
theorem cover_sep_of_margin {s : ℝ} (hs : 0 < s) {R N : ℕ}
    (hR : 1 ≤ R) (hgap : (40 : ℝ) * R ≤ N)
    {y y' z z' : Zd d}
    (hmargin : ∃ i : Fin d, (N : ℤ) ≤ 2 * |y i - y' i|)
    (hz : ∀ i, |y i - z i| ≤ (R : ℤ) - 1)
    (hz' : ∀ i, |y' i - z' i| ≤ (R : ℤ) - 1) :
    latPt s z' ∉ cbox (latPt s z) ((N * s) / 4) := by
  intro hc
  obtain ⟨i, hm⟩ := hmargin
  have hm' : (N : ℝ) ≤ 2 * |(y i : ℝ) - (y' i : ℝ)| := by
    exact_mod_cast hm
  have hz0 : |(y i : ℝ) - (z i : ℝ)| ≤ (R : ℝ) - 1 := by
    exact_mod_cast hz i
  have hz1 : |(y' i : ℝ) - (z' i : ℝ)| ≤ (R : ℝ) - 1 := by
    exact_mod_cast hz' i
  have hzz : |(z' i : ℝ) - (z i : ℝ)| ≤ (N : ℝ) / 4 := by
    have hi := hc i
    rw [latPt_apply, latPt_apply, ← mul_sub, abs_mul, abs_of_pos hs] at hi
    apply le_of_mul_le_mul_right (a0 := hs)
    calc |(z' i : ℝ) - (z i : ℝ)| * s = s * |(z' i : ℝ) - (z i : ℝ)| := by ring
      _ ≤ (N : ℝ) * s / 4 := hi
      _ = ((N : ℝ) / 4) * s := by ring
  have htri : |(y i : ℝ) - (y' i : ℝ)| ≤
      |(y i : ℝ) - (z i : ℝ)| + |(z i : ℝ) - (z' i : ℝ)| +
        |(z' i : ℝ) - (y' i : ℝ)| := by
    have h1 := abs_sub_le (y i : ℝ) (z i : ℝ) (y' i : ℝ)
    have h2 := abs_sub_le (z i : ℝ) (z' i : ℝ) (y' i : ℝ)
    linarith
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  rw [abs_sub_comm (z i : ℝ) (z' i : ℝ)] at htri
  rw [abs_sub_comm (z' i : ℝ) (y' i : ℝ)] at htri
  linarith

end HigherDimLQGMetric.DGZ
