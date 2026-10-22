import HigherDimLQGMetric.Sec8b.Lemma85RealWindow
import HigherDimLQGMetric.Sec8b.Lemma83

/-! The finite occupation estimate for the chosen shifted favorable set. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_occ_fav_real {ξ Q cs Cs q R r : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hq : 0 < q) (hR : 0 < R) (hr : 0 < r)
    (g : DistRd d) (x y : Rd d) (colour : Fin d → ℤ)
    (Z : Finset (Rd d × ℕ)) (k : ℕ)
    (hZ : IsSec8LabeledSet d T.J r R x y colour Z)
    (hk : Z.card ≤ k)
    (hFav : g ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z)
    (hDlen : (D g).IsLength) (hDtlen : (Dt g).IsLength)
    (hcomp : ∀ u v : Rd d,
      cs * (D g).1 (u, v) ≤ (Dt g).1 (u, v) ∧
      (Dt g).1 (u, v) ≤ Cs * (D g).1 (u, v))
    (hweyl : IsWeylOf ξ (-F_Z T.f r Z) (D g)
      (D (addFun g (-F_Z T.f r Z))))
    (P : ℝ → Rd d)
    (hP : IsGeod (D (addFun g (-F_Z T.f r Z))) P)
    (hP0 : P 0 = x) (hP1 : P 1 = y) :
    let S := macroS ξ Q g R
    let total := ((D g).len P 0 1).toReal
    ENNReal.ofReal total = (D g).len P 0 1 ∧
      total ≤ (D (addFun g (-F_Z T.f r Z))).1 (x, y) +
        2 * T.H * k * q * S := by
  classical
  let E := D (addFun g (-F_Z T.f r Z))
  let s : Rd d × ℕ → ℝ := fun site => sNorm ξ Q g r site.1
  let S := macroS ξ Q g R
  have hS : 0 < S := by dsimp [S, macroS]; positivity
  have hqS : 0 < q * S := mul_pos hq hS
  have hH : 0 < T.H := by
    rw [T.constants.2.2.2.2.1]
    exact mul_pos T.constants.1 (Real.exp_pos _)
  have hC2 := hFav.2.1
  have hJ : ∀ site ∈ Z, site.2 < T.J :=
    fun site hs => (hC2 site hs).1
  have hs : ∀ site ∈ Z, 0 ≤ s site ∧ s site ≤ 2 * q * S := by
    intro site hsite
    obtain ⟨_, _, hlo, hhi⟩ := hC2 site hsite
    exact ⟨(hqS.trans_le hlo).le, hhi⟩
  have htrap : ∀ site ∈ Z,
      TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c'
        (D g) (Dt g) (s site) r site.1 site.2 := by
    intro site hsite
    exact T.traps (D g) (Dt g) hDlen hDtlen hcomp
      (s site) r site.1 site.2
      (lt_of_lt_of_le hqS (hC2 site hsite).2.2.1)
      hr (hJ site hsite) (hC2 site hsite).2.1
  have hocc := lemma82_T4b (D g) (Dt g) E ξ hξ r hr
    T.V T.f T.J
    (fun j hj u => (T.bumps j hj).2.2.2.1 u)
    (fun j hj u hu => ((T.bumps j hj).2.2.2.2.1 u).mp hu)
    T.a T.b T.c T.g T.H T.c' s Z hJ
    (s7b_labeled_disjoint (by omega : 1 ≤ d) hr hZ)
    htrap hweyl P hP
  have hsum : ∑ site ∈ Z, s site ≤ 2 * q * S * k := by
    have hpoint := Finset.sum_le_sum (fun site hsite => (hs site hsite).2)
    have hnonneg : 0 ≤ 2 * q * S := by positivity
    have hcard : (Z.card : ℝ) ≤ k := by exact_mod_cast hk
    have hmul := mul_le_mul_of_nonneg_left hcard hnonneg
    calc
      ∑ site ∈ Z, s site ≤ ∑ site ∈ Z, 2 * q * S := hpoint
      _ = (Z.card : ℝ) * (2 * q * S) := by simp
      _ ≤ 2 * q * S * k := by nlinarith only [hmul]
  have hsumOfReal : (∑ site ∈ Z, ENNReal.ofReal (T.H * s site)) =
      ENNReal.ofReal (T.H * ∑ site ∈ Z, s site) := by
    rw [Finset.mul_sum]
    exact (ENNReal.ofReal_sum_of_nonneg
      (fun site hsite => mul_nonneg hH.le (hs site hsite).1)).symm
  have hupper : (D g).len P 0 1 ≤
      ENNReal.ofReal (E.1 (x, y) + T.H * ∑ site ∈ Z, s site) := by
    rw [ENNReal.ofReal_add (E.nonneg x y)
      (mul_nonneg hH.le (Finset.sum_nonneg fun site hs' => (hs site hs').1))]
    calc
      (D g).len P 0 1 ≤ E.len P 0 1 +
        ∑ site ∈ Z, ENNReal.ofReal (T.H * s site) := hocc
      _ = ENNReal.ofReal (E.1 (x, y)) +
        ENNReal.ofReal (T.H * ∑ site ∈ Z, s site) := by
          rw [hP.2, hP0, hP1, hsumOfReal]
  have hfin : (D g).len P 0 1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  let total := ((D g).len P 0 1).toReal
  have htotal : ENNReal.ofReal total = (D g).len P 0 1 :=
    ENNReal.ofReal_toReal hfin
  have hreal : total ≤ E.1 (x, y) + T.H * ∑ site ∈ Z, s site := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg (E.nonneg x y)
        (mul_nonneg hH.le (Finset.sum_nonneg fun site hs' => (hs site hs').1)))).mp
    rw [htotal]
    exact hupper
  dsimp only
  refine ⟨htotal, ?_⟩
  have hprod := mul_le_mul_of_nonneg_left hsum hH.le
  dsimp only [E, S] at hreal ⊢
  nlinarith only [hreal, hprod]

end HigherDimLQGMetric
