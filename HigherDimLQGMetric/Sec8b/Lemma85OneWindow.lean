import HigherDimLQGMetric.Sec8b.Lemma85CompareLen
import HigherDimLQGMetric.Sec8b.Lemma85Shifted

/-! One very-good centre gives a shortcut after any remote finite shift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_one_remote_shortcut {ξ Q cs Cs q R r : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hq : 0 < q) (hR : 0 < R) (hr : 0 < r)
    (g : DistRd d) (x y : Rd d)
    (site : Rd d × ℕ) (hJsite : site.2 < T.J)
    (hgood : S7bVeryGood T Q q R r x y g site)
    (Z : Finset (Rd d × ℕ))
    (hJ : ∀ p ∈ Z, p.2 < T.J)
    (hremote : ∀ p ∈ Z, 10 * r ≤ ‖p.1 - site.1‖)
    (hmetric : ∀ f : C(Rd d, ℝ),
      (D (addFun g f)).IsLength ∧ (Dt (addFun g f)).IsLength ∧
      (∀ u v : Rd d,
        cs * (D (addFun g f)).1 (u, v) ≤ (Dt (addFun g f)).1 (u, v) ∧
        (Dt (addFun g f)).1 (u, v) ≤ Cs * (D (addFun g f)).1 (u, v)) ∧
      IsWeylOf ξ (-f) (D (addFun g f)) (D g) ∧
      IsWeylOf ξ (-f) (Dt (addFun g f)) (Dt g))
    (P : ℝ → Rd d)
    (hP : IsGeod (D g) P)
    (hPeq : P = s7b_realPath (sec8Sel x y (D g).1)) :
    let Dplus := D (addFun g (F_Z T.f r Z))
    let Dtplus := Dt (addFun g (F_Z T.f r Z))
    let cplus := max T.c' 0
    let S := macroS ξ Q g R
    ∃ a b L : ℝ,
      0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ 0 < L ∧
      (∀ t ∈ Icc a b, P t ∈ ball site.1 (4 * r)) ∧
      T.c * q * S ≤ L ∧
      Dplus.len P a b = ENNReal.ofReal L ∧
      Dtplus.1 (P a, P b) ≤ cplus * L := by
  classical
  let bump := bumpAt (T.f site.2) r site.1
  let Dsingle := D (addFun g bump)
  let Dtsingle := Dt (addFun g bump)
  let Dplus := D (addFun g (F_Z T.f r Z))
  let Dtplus := Dt (addFun g (F_Z T.f r Z))
  let S := macroS ξ Q g R
  let s := sNorm ξ Q g r site.1
  let cplus := max T.c' 0
  have hS : 0 < S := by dsimp [S, macroS]; positivity
  have hqS : 0 < q * S := mul_pos hq hS
  have hs : 0 < s := lt_of_lt_of_le hqS hgood.2.1
  have hc : 0 < T.c := T.constants.2.2.1
  have hcs : 0 < T.c * s := mul_pos hc hs
  have hcplus : 0 ≤ cplus := le_max_right _ _
  have hsingle := hmetric bump
  have hplus := hmetric (F_Z T.f r Z)
  have hExc : Exc (sec8Sel x y (D g).1) Dsingle
      (sec8Collector T.V r site.1) site.1 r (T.b * s) := hgood.2.2.2
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hinside₀,
    Rpath, _, _, _, hRform, τ₁, τ₂, hτ₁, hτ₁₂, hτ₂, hcost, hshort⟩ :=
    s7b_T3_of_exc T hs hr site hJsite Dsingle Dtsingle (D g) (Dt g)
      hsingle.1 hsingle.2.1 hsingle.2.2.1
      hgood.1 hsingle.2.2.2.1 hsingle.2.2.2.2
      (sec8Sel x y (D g).1) (by simpa only [hPeq] using hP) hExc
  obtain ⟨a, b, ha, hab, hb, hinside, hcost', hshort'⟩ :=
    s7b_map_shortcut_window (D g) (Dt g)
      (s7b_realPath (sec8Sel x y (D g).1)) Rpath
      (ball site.1 (4 * r)) ha₀ hab₀ hb₀ hinside₀ hRform
      hτ₁ hτ₁₂ hτ₂ hcost hshort
  have hcostP : ENNReal.ofReal (T.c * s) ≤ (D g).len P a b := by
    simpa only [hPeq] using hcost'
  have hshortP : (Dt g).internal (ball site.1 (4 * r)) (P a) (P b) ≤
      ENNReal.ofReal T.c' * (D g).len P a b := by
    simpa only [hPeq] using hshort'
  have hcostPlus : ENNReal.ofReal (T.c * q * S) ≤ (D g).len P a b := by
    have hcs' : T.c * q * S ≤ T.c * s := by
      nlinarith only [hgood.2.1, hc.le]
    exact (ENNReal.ofReal_le_ofReal hcs').trans hcostP
  have hshortPlus : (Dt g).internal (ball site.1 (4 * r)) (P a) (P b) ≤
      ENNReal.ofReal cplus * (D g).len P a b := by
    calc
      _ ≤ ENNReal.ofReal T.c' * (D g).len P a b := hshortP
      _ ≤ ENNReal.ofReal cplus * (D g).len P a b := by
        gcongr
        exact le_max_left _ _
  obtain ⟨L, hL, hab', hinside', hLen, hLlo, _⟩ :=
    s7b_real_shortcut_window (D g) (Dt g) P (ball site.1 (4 * r))
      hP ha hab hb (by simpa only [hPeq] using hinside)
      (by positivity : 0 < T.c * q * S) hcplus
      hcostPlus hshortPlus
  have hremote' := s7b_remote_metric_window T hr Z hJ site.1 hremote
    Dplus (D g) Dtplus (Dt g) hplus.1
    hplus.2.2.2.1 hplus.2.2.2.2 P
    (hP.1.mono (Icc_subset_Icc ha hb)) hinside'
  have hDplusLen : Dplus.len P a b = ENNReal.ofReal L := by
    rw [hremote'.1, ← hLen]
  have hDtplusInt : Dtplus.internal (ball site.1 (4 * r)) (P a) (P b) ≤
      ENNReal.ofReal (cplus * L) := by
    rw [hremote'.2]
    calc
      (Dt g).internal (ball site.1 (4 * r)) (P a) (P b) ≤
          ENNReal.ofReal cplus * (D g).len P a b := hshortPlus
      _ = ENNReal.ofReal (cplus * L) := by rw [← hLen, ENNReal.ofReal_mul hcplus]
  have hshortReal : Dtplus.1 (P a, P b) ≤ cplus * L := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcplus hL.le)).mp
    exact ((Dtplus.ofReal_le_internal _ _ _).trans hDtplusInt)
  dsimp only
  exact ⟨a, b, L, ha, hab', hb, hL, hinside',
    by nlinarith only [hLlo], hDplusLen, hshortReal⟩

end HigherDimLQGMetric
