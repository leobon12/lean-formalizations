import QuantumZipper.Proofs.Zipper.WedgeXGoodBasic
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.Zipper.F2Step3DensCara

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D29 (wedge unzipping), X-G input: `E_t` vanishes only at the tips (`ExtNonvanishStmt`)

`WedgeUnzip.extNonvanishStmt_holds`: a.s., for all `t ≥ 0`, `E_t = F2.extInv (drive κ B ω) t`
is nonzero on `ℍ̄ \ {O⁻_t, O⁺_t}`.

Route. For `t > 0`, `E_t` is the Carathéodory extension `F` of the reverse map
`revMap (vrev W t) t` (`CaraR.revMapCaratheodory`: Ch. Pommerenke, *Boundary Behaviour of
Conformal Maps*, Springer 1992, Thm 2.1 and Prop 2.5/Thm 2.6, for the simple arc
`η(0,t]`, Rohde–Schramm, *Basic properties of SLE*, Ann. of Math. 161 (2005), Thm 6.1, proved as
`RS.rohdeSchrammSimple`; identification `F2.extInv_eq_of_cara`). On `ℍ`, `F = revMap ∈ ℍ`. On
`ℝ`, `F u = 0 = F 0₋` forces, by the two-sided boundary correspondence in
`Blueprint.IsCaratheodoryRevExt` (points with equal image are equal or welded), `u = 0₋`,
`u = 0₊ = φ(0₋)`, or `u ∈ [0₋, 0]` real with `F u` real, i.e. `u ≤ 0₋` or `u ≥ 0₊ ≥ 0`;
all of these give a tip (`O⁻_t = 0₋`, `O⁺_t = 0₊`, `O⁺_t ≥ 0` by
`F2.ae_forall_sideImages_fst_nonpos` for `−B`). At `t = 0`, `E_0 = id` and both tips are `0`.
Same identifications as `F2.exists_extInv_good`; the case analysis is our own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- **Deterministic core.** For `t > 0`, with both reverse hulls simple arcs, real points alive and
`O⁺_t ≥ 0`, `E_t` is nonzero on `ℍ̄` off the two tips. -/
theorem extInv_ne_zero_of_simple {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) (hK : IsSimpleCurveHull (revHull (B2.vrev W t) t))
    (hK' : IsSimpleCurveHull (revHull (B2.vrev (-W) t) t))
    (halive : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol W (x : ℂ) t v)
    (halive' : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol (-W) (x : ℂ) t v)
    (hsign : 0 ≤ (sideImages W t).2) :
    ∀ u ∈ Hbar, u ∉ tipPts W t → F2.extInv W t u ≠ 0 := by
  set V' := B2.vrev W t with hV'
  have hV'c : Continuous V' := B2.continuous_vrev hW t
  have hV'0 : V' 0 = 0 := B2.vrev_zero ht.le
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory V' hV'c hV'0 t ht hK
  have ha : (sideImages W t).1 = zeroMinus V' t :=
    B5.sideImages_fst_eq_zeroMinus_vrev hW hW0 ht hK halive
  have hb : (sideImages W t).2 = zeroPlus V' t := by
    obtain ⟨a, b, hL, hR⟩ := F1.exists_tendsto_sideImages_of_alive ht.le halive
    have h1 := F1.sideImages_reflect_swap ht.le hL hR
    have h2 := B5.sideImages_fst_eq_zeroMinus_vrev hW.neg (by simp [hW0]) ht hK' halive'
    have hvneg : B2.vrev (-W) t = -V' := by
      funext s; simp only [B2.vrev, Pi.neg_apply, hV']; ring
    rw [h1, hvneg, F2.zeroMinus_neg_eq hV'c ht.le hF] at h2
    exact neg_inj.1 h2
  intro u hu htip h0
  have hEq := F2.extInv_eq_of_cara hW hW0 ht.le hF u hu
  rw [h0] at hEq
  have hm : u ≠ ((zeroMinus V' t : ℝ) : ℂ) := fun h => htip (by
    rw [h, ofReal_mem_tipPts_iff, ← ha]; exact Set.mem_insert _ _)
  have hp : u ≠ ((zeroPlus V' t : ℝ) : ℂ) := fun h => htip (by
    rw [h, ofReal_mem_tipPts_iff, ← hb]; exact Set.mem_insert_of_mem _ rfl)
  by_cases hpos : 0 < u.im
  · have := Semigroup.mem_H_revMap hV'c ht.le (z := u) hpos
    rw [← hF.1 hpos, ← hEq] at this
    simp [H] at this
  have hz0 : u.im = 0 := le_antisymm (not_lt.1 hpos) hu
  have hzr : u = (u.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
  have hFu : F u = F ((zeroMinus V' t : ℝ) : ℂ) := by rw [← hEq, hF.2.2.2.1]
  rcases (hF.2.2.2.2.2.2 u hu _ (by simp [Hbar])).1 hFu with h | ⟨s, hs, h | h⟩
  · exact hm h
  · -- `u = s` real in `[0₋, 0]` with `F s = 0` real
    have him : (F (s : ℂ)).im = 0 := by rw [← h.1, ← hEq]; simp
    rcases (hF.2.2.2.2.2.1 s).1 him with h' | h'
    · exact hm (by rw [h.1, le_antisymm h' hs.1])
    · have hb0 : 0 ≤ zeroPlus V' t := hb ▸ hsign
      exact hp (by rw [h.1, le_antisymm (hs.2.trans hb0) h'])
  · apply hp
    rw [h.1, ofReal_inj, ← ofReal_inj.1 h.2, hF.2.2.2.2.1]

/-- **`ExtNonvanishStmt` holds.** -/
theorem extNonvanishStmt_holds : ExtNonvanishStmt := by
  intro κ hκ hκ4 Ω _ P _ B hB
  filter_upwards [RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ
      hκ4.le P B hB,
    RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le P (-B) hB.neg,
    hB.cont, hB.eval_zero_ae_eq_zero, RS.ae_real_alive hB hκ hκ4.le,
    RS.ae_real_alive hB.neg hκ hκ4.le, F2.ae_forall_sideImages_fst_nonpos hκ hκ4 hB.neg]
    with ω hK hK' hc h0 hal hal' hneg t ht
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  have hdr : drive κ (-B) ω = -drive κ B ω := by
    funext s; simp [drive]
  rcases ht.eq_or_lt with rfl | ht'
  · intro u hu htip
    rw [F2.extInv_zero_eq_self hWc hW0 hu]
    rintro rfl
    apply htip
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, ofReal_mem_tipPts_iff]
    unfold tipSet
    rw [B5.sideImages_fst_zero_time hW0]
    exact Set.mem_insert _ _
  have hK1 : IsSimpleCurveHull (revHull (B2.vrev (-drive κ B ω) t) t) := by
    rw [← hdr]; exact hK' t ht'
  have hsign : 0 ≤ (sideImages (drive κ B ω) t).2 := by
    obtain ⟨a, b, hL, hR⟩ := F1.exists_tendsto_sideImages_of_alive ht fun x hx => hal x hx t ht
    have h := hneg t ht
    rw [hdr, F1.sideImages_reflect_swap ht hL hR] at h
    simp only at h
    linarith
  refine extInv_ne_zero_of_simple hWc hW0 ht' (hK t ht') hK1 (fun x hx => hal x hx t ht)
    (fun x hx => ?_) hsign
  rw [← hdr]
  exact hal' x hx t ht

end WedgeUnzip
end QuantumZipper
