import HigherDimLQGMetric.Sec8b.Lemma85CenterFromGood
import HigherDimLQGMetric.Sec8b.Lemma85Comb

/-! Deterministic form of Lemma 8.5 on the common regularity event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_few_shifted_fav_deterministic {ξ Q cs Cs q R r : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hCs : 0 < Cs)
    (hq : 0 < q) (hR : 0 < R) (hr : 0 < r)
    (g : DistRd d) (x y : Rd d) (colour : Fin d → ℤ)
    (k : ℕ) (hk : 1 ≤ k)
    (S : Finset (Finset (Rd d × ℕ)))
    (hS : ∀ Z ∈ S,
      IsSec8LabeledSet d T.J r R x y colour Z ∧ Z.card ≤ k)
    (hmacro : ∀ Z ∈ S,
      macroS ξ Q (addFun g (F_Z T.f r Z)) R = macroS ξ Q g R)
    (hvery : ∀ Z ∈ S,
      addFun g (F_Z T.f r Z) ∈
        FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z →
      ∀ site ∈ Z, S7bVeryGood T Q q R r x y g site)
    (hmetric : ∀ f : C(Rd d, ℝ),
      (D (addFun g f)).IsLength ∧ (Dt (addFun g f)).IsLength ∧
      (∀ u v : Rd d,
        cs * (D (addFun g f)).1 (u, v) ≤ (Dt (addFun g f)).1 (u, v) ∧
        (Dt (addFun g f)).1 (u, v) ≤ Cs * (D (addFun g f)).1 (u, v)) ∧
      IsWeylOf ξ (-f) (D (addFun g f)) (D g) ∧
      IsWeylOf ξ (-f) (Dt (addFun g f)) (Dt g))
    (P : ℝ → Rd d) (hP : IsGeod (D g) P)
    (hPeq : P = s7b_realPath (sec8Sel x y (D g).1))
    (hP0 : P 0 = x) (hP1 : P 1 = y) :
    (S.filter fun Z => addFun g (F_Z T.f r Z) ∈
      FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z).card ≤
      (2 ^ (T.J * (1 + ⌈(2 * Cs * T.H + 1) /
        ((Cs - max T.c' 0) * T.c)⌉₊))) ^ k := by
  classical
  let family := S.filter fun Z => addFun g (F_Z T.f r Z) ∈
    FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z
  let good : Finset (Rd d × ℕ) := family.biUnion id
  have hgood (Z : Finset (Rd d × ℕ)) (hZ : Z ∈ family) : Z ⊆ good := by
    intro site hsite
    exact Finset.mem_biUnion.mpr ⟨Z, hZ, hsite⟩
  have hJgood : ∀ site ∈ good, site.2 < T.J := by
    intro site hsite
    obtain ⟨Z, hZfam, hsiteZ⟩ := Finset.mem_biUnion.mp hsite
    obtain ⟨_, _, _, _, _, _, hj⟩ :=
      (hS Z (Finset.mem_filter.mp hZfam).1).1.1 site hsiteZ
    exact hj
  have hgeom : ∀ site ∈ good, ∃ index : Fin d → ℤ,
      site.1 = HigherDimLFPP.DGZ.latPt (r / (100 * d)) index ∧
        sec8Color d index = colour := by
    intro site hsite
    obtain ⟨Z, hZfam, hsiteZ⟩ := Finset.mem_biUnion.mp hsite
    obtain ⟨index, hidx, hcol, _, _, _, _⟩ :=
      (hS Z (Finset.mem_filter.mp hZfam).1).1.1 site hsiteZ
    exact ⟨index, hidx, hcol⟩
  have hveryGood : ∀ site ∈ good,
      S7bVeryGood T Q q R r x y g site := by
    intro site hsite
    obtain ⟨Z, hZfam, hsiteZ⟩ := Finset.mem_biUnion.mp hsite
    obtain ⟨hZS, hFavZ⟩ := Finset.mem_filter.mp hZfam
    exact hvery Z hZS hFavZ site hsiteZ
  by_cases hzero : family.Nonempty
  · obtain ⟨Z0, hZ0fam⟩ := hzero
    obtain ⟨hZ0S, hFav0⟩ := Finset.mem_filter.mp hZ0fam
    have hZ0geom := (hS Z0 hZ0S).1
    have hZ0k := (hS Z0 hZ0S).2
    let gplus := addFun g (F_Z T.f r Z0)
    let Dplus := D gplus
    let Dtplus := Dt gplus
    have hmetric0 := hmetric (F_Z T.f r Z0)
    have hcancel := addFun_F_Z_sub g T.f r Z0
    have hweyl0 : IsWeylOf ξ (-F_Z T.f r Z0) Dplus
        (D (addFun gplus (-F_Z T.f r Z0))) := by
      simpa only [gplus, Dplus, hcancel] using hmetric0.2.2.2.1
    have hPminus : IsGeod (D (addFun gplus (-F_Z T.f r Z0))) P := by
      simpa only [gplus, hcancel] using hP
    have hocc0 := s7b_occ_fav_real T hd hξ hq hR hr gplus x y
      colour Z0 k hZ0geom hZ0k hFav0
      hmetric0.1 hmetric0.2.1 hmetric0.2.2.1
      hweyl0 P hPminus hP0 hP1
    let total := (Dplus.len P 0 1).toReal
    have htotal : Dplus.len P 0 1 = ENNReal.ofReal total :=
      hocc0.1.symm
    have htotal0 : 0 ≤ total := ENNReal.toReal_nonneg
    have hocc : total ≤ (D g).1 (x, y) +
        2 * T.H * k * q * macroS ξ Q g R := by
      simpa only [gplus, Dplus, hcancel, hmacro Z0 hZ0S] using hocc0.2
    have hnear : Cs * (D g).1 (x, y) - q * macroS ξ Q g R ≤
        Dtplus.1 (x, y) := by
      have hC1 := hFav0.1
      have hJ0 : ∀ site ∈ Z0, site.2 < T.J :=
        fun site hs => hJgood site (hgood Z0 hZ0fam hs)
      have hDle : (D g).1 (x, y) ≤ Dplus.1 (x, y) :=
        s7b_discount_dist_le T hξ r Z0 hJ0 Dplus (D g)
          hmetric0.1 (by simpa only [gplus, Dplus, hcancel] using
            hmetric0.2.2.2.1) x y
      have hmul := mul_le_mul_of_nonneg_left hDle hCs.le
      dsimp only [sec8C1] at hC1
      rw [hmacro Z0 hZ0S] at hC1
      exact le_trans (sub_le_sub_right hmul _) hC1
    have hcenters := s7b_center_count_from_good T hd hq hR hr hCs
      g x y colour good Z0 k hk (hgood Z0 hZ0fam) hZ0k
      hgeom hJgood hveryGood hmetric P hP hPeq hP0 hP1
      total htotal htotal0 hocc hnear
    exact s7b_few_shifted_sets_of_centers T.J
      (1 + ⌈(2 * Cs * T.H + 1) /
        ((Cs - max T.c' 0) * T.c)⌉₊) k good family
      hJgood hcenters hgood
  · have hempty : family = ∅ := Finset.not_nonempty_iff_eq_empty.mp hzero
    simp only [family, hempty, Finset.card_empty, zero_le]

end HigherDimLQGMetric
