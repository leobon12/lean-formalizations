import HigherDimLQGMetric.Sec8b.Lemma85CenterCount

/-! Very-good labels supply every shortcut required by the centre count. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set Metric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

variable {d : ℕ}

theorem s7b_center_count_from_good {ξ Q cs Cs q R r : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hd : 3 ≤ d) (hq : 0 < q) (hR : 0 < R) (hr : 0 < r)
    (hCs : 0 < Cs)
    (g : DistRd d) (x y : Rd d) (colour : Fin d → ℤ)
    (good Z0 : Finset (Rd d × ℕ)) (k : ℕ)
    (hk : 1 ≤ k) (hZ0 : Z0 ⊆ good) (hZ0k : Z0.card ≤ k)
    (hgeom : ∀ site ∈ good, ∃ index : Fin d → ℤ,
      site.1 = latPt (r / (100 * d)) index ∧
        sec8Color d index = colour)
    (hJgood : ∀ site ∈ good, site.2 < T.J)
    (hvery : ∀ site ∈ good, S7bVeryGood T Q q R r x y g site)
    (hmetric : ∀ f : C(Rd d, ℝ),
      (D (addFun g f)).IsLength ∧ (Dt (addFun g f)).IsLength ∧
      (∀ u v : Rd d,
        cs * (D (addFun g f)).1 (u, v) ≤ (Dt (addFun g f)).1 (u, v) ∧
        (Dt (addFun g f)).1 (u, v) ≤ Cs * (D (addFun g f)).1 (u, v)) ∧
      IsWeylOf ξ (-f) (D (addFun g f)) (D g) ∧
      IsWeylOf ξ (-f) (Dt (addFun g f)) (Dt g))
    (P : ℝ → Rd d) (hP : IsGeod (D g) P)
    (hPeq : P = s7b_realPath (sec8Sel x y (D g).1))
    (hP0 : P 0 = x) (hP1 : P 1 = y)
    (total : ℝ)
    (htotal : (D (addFun g (F_Z T.f r Z0))).len P 0 1 =
      ENNReal.ofReal total)
    (htotal0 : 0 ≤ total)
    (hocc : total ≤ (D g).1 (x, y) +
      2 * T.H * k * q * macroS ξ Q g R)
    (hnear : Cs * (D g).1 (x, y) - q * macroS ξ Q g R ≤
      (Dt (addFun g (F_Z T.f r Z0))).1 (x, y)) :
    (good.image Prod.fst).card ≤
      (1 + ⌈(2 * Cs * T.H + 1) /
        ((Cs - max T.c' 0) * T.c)⌉₊) * k := by
  classical
  let Dplus := D (addFun g (F_Z T.f r Z0))
  let Dtplus := Dt (addFun g (F_Z T.f r Z0))
  let S := macroS ξ Q g R
  have hS : 0 < S := by dsimp [S, macroS]; positivity
  have hqS : 0 < q * S := mul_pos hq hS
  have hH : 0 ≤ T.H := by
    rw [T.constants.2.2.2.2.1]
    exact (mul_pos T.constants.1 (Real.exp_pos _)).le
  have hJ0 : ∀ site ∈ Z0, site.2 < T.J :=
    fun site hs => hJgood site (hZ0 hs)
  have hcomp : ∀ u v : Rd d,
      Dtplus.1 (u, v) ≤ Cs * Dplus.1 (u, v) :=
    fun u v => ((hmetric (F_Z T.f r Z0)).2.2.1 u v).2
  have hchoice : ∀ z ∈ good.image Prod.fst \ Z0.image Prod.fst,
      ∃ w : (ℝ × ℝ) × ℝ,
        S7bShortcutWindow Dplus P z r T.c (q * S) w ∧
        Dtplus.1 (P w.1.1, P w.1.2) ≤ max T.c' 0 * w.2 := by
    intro z hz
    obtain ⟨site, hsite, hsitez⟩ :=
      Finset.mem_image.mp (Finset.mem_sdiff.mp hz).1
    have hremote : ∀ p ∈ Z0, 10 * r ≤ ‖p.1 - site.1‖ := by
      intro p hp
      have hpGood := hZ0 hp
      have hpCenter : p.1 ∈ good.image Prod.fst :=
        Finset.mem_image.mpr ⟨p, hpGood, rfl⟩
      have hne : p.1 ≠ site.1 := by
        intro heq
        apply (Finset.mem_sdiff.mp hz).2
        exact Finset.mem_image.mpr ⟨p, hp, heq.trans hsitez⟩
      have hsiteCenter : site.1 ∈ good.image Prod.fst :=
        Finset.mem_image.mpr ⟨site, hsite, rfl⟩
      exact s7b_good_centers_sep (by omega : 1 ≤ d) hr colour good hgeom
        hpCenter hsiteCenter hne
    obtain ⟨a, b, L, ha, hab, hb, hL, hinside, hLlo, hlen, hshort⟩ :=
      s7b_one_remote_shortcut T hq hR hr g x y site
        (hJgood site hsite) (hvery site hsite) Z0 hJ0
        hremote hmetric P hP hPeq
    refine ⟨((a, b), L), ?_, hshort⟩
    exact ⟨ha, hab, hb, hL, by simpa only [← hsitez] using hinside,
      by simpa only [S, mul_assoc] using hLlo, hlen⟩
  have hcenter := s7b_center_count_of_windows
    (by omega : 1 ≤ d) hr hqS hCs T.constants.2.2.2.2.2.1
    T.constants.2.2.1 hH colour good Z0 k hk hZ0k hgeom
    Dplus Dtplus P hcomp
    (by simpa only [hP0, hP1, S] using hnear)
    htotal htotal0
    (by simpa only [S, mul_assoc] using hocc) hchoice
  simpa only [S] using hcenter

end HigherDimLQGMetric
