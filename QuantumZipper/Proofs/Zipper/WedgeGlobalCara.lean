import QuantumZipper.Proofs.Zipper.F2Step3DensCara
import QuantumZipper.Proofs.Zipper.WedgeUnzipCore

/-!
# D29 (wedge unzipping), core C: the global Carathéodory extension of `f_t⁻¹`

`WedgeUnzip.GlobalCaraStmt` holds (`globalCaraStmt_holds`): a.s., for **every** `t ≥ 0`, the map
`E_t = F2.extInv (drive κ B ω) t` is continuous on the closed upper half-plane `ℍ̄`. This is the
global form of `F2.step3BdryExt_holds` (`F2Step3DensCara.lean`), which only gives continuity on a
neighbourhood of the boundary segment `(O⁻_t, O⁺_t)`.

* For `t > 0`: a.s. the reverse hull `revHull (vrev W t) t` is a simple arc for all `t > 0` at
  once (`RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr`), so `revMap (vrev W t) t` has a
  Carathéodory extension `F` to `ℍ̄` (`CaraR.revMapCaratheodory`; Ch. Pommerenke, *Boundary
  Behaviour of Conformal Maps*, Springer 1992, Thms 2.1/2.6, via the Rohde–Schramm simple trace
  `RS.rohdeSchrammSimple`), and `extInv = F` on `ℍ̄` (`extInv_eq_of_cara`, the identification
  already used inside `F2.exists_extInv_good`: `fwdMapInv W t = revMap (vrev W t) t` on `ℍ` by
  `B2.fwdMapInv_eq_revMap_vrev`, and on `ℝ` both sides are the limit along `ℍ`).
* For `t = 0`: `fwdMapInv W 0 = id` on `ℍ` (`B2.fwdMapInv_eq_revMap_vrev` with
  `CharFun.revMap_zero_eq`), hence `extInv W 0 = id` on `ℍ̄` and it is continuous there.

The case `t = 0` and the bookkeeping are our own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace F2

section Det

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **`extInv` is the Carathéodory extension on `ℍ̄`.** If `F` is a Carathéodory extension of the
reverse map `revMap (vrev W t) t`, then `extInv W t = F` on the closed upper half-plane. (Same
identification as inside `exists_extInv_good`.) -/
theorem extInv_eq_of_cara (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hF : Blueprint.IsCaratheodoryRevExt (B2.vrev W t) t F) :
    ∀ z ∈ Hbar, extInv W t z = F z := by
  have hH : ∀ w ∈ H, fwdMapInv W t w = F w := by
    intro w hw
    rw [B2.fwdMapInv_eq_revMap_vrev hW hW0 ht hw]
    exact (hF.1 hw).symm
  intro z hz
  by_cases hpos : 0 < z.im
  · simp only [extInv, hpos, ↓reduceIte]
    exact hH z hpos
  · have hz0 : z.im = 0 := le_antisymm (not_lt.1 hpos) hz
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    simp only [extInv, hpos, ↓reduceIte, invBdry]
    have hmem : (z.re : ℂ) ∈ closure H := by
      rw [CA.Car.closure_H_eq_Hbar]; simp [Hbar]
    have := mem_closure_iff_nhdsWithin_neBot.1 hmem
    rw [hzr]
    simp only [ofReal_re]
    refine Tendsto.limUnder_eq ?_
    refine (((hF.2.1 _ (by simp [Hbar])).mono fun w (hw : 0 < w.im) =>
      (le_of_lt hw : 0 ≤ w.im)).tendsto).congr' ?_
    exact eventually_nhdsWithin_of_forall fun w hw => (hH w hw).symm

/-- **Global Carathéodory extension for `t > 0`.** If the reverse hull of `vrev W t` at time `t`
is a simple arc, then `extInv W t` is continuous on all of `ℍ̄`. -/
theorem continuousOn_extInv_of_simpleHull (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 < t)
    (hK : IsSimpleCurveHull (revHull (B2.vrev W t) t)) :
    ContinuousOn (extInv W t) Hbar := by
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory (B2.vrev W t) (B2.continuous_vrev hW t)
    (B2.vrev_zero ht.le) t ht hK
  exact hF.2.1.congr fun z hz => extInv_eq_of_cara hW hW0 ht.le hF z hz

/-- At time `0` the inverse forward map is the identity on the closed upper half-plane. -/
theorem extInv_zero_eq_self (hW : Continuous W) (hW0 : W 0 = 0) {z : ℂ} (hz : z ∈ Hbar) :
    extInv W 0 z = z := by
  have hH0 : ∀ w ∈ H, fwdMapInv W 0 w = w := by
    intro w hw
    rw [B2.fwdMapInv_eq_revMap_vrev hW hW0 le_rfl hw]
    exact CharFun.revMap_zero_eq (B2.continuous_vrev hW 0) (B2.vrev_zero le_rfl) hw
  by_cases hpos : 0 < z.im
  · simp only [extInv, hpos, ↓reduceIte]
    exact hH0 z hpos
  · have hz0 : z.im = 0 := le_antisymm (not_lt.1 hpos) hz
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    rw [hzr, extInv_ofReal, invBdry]
    have hmem : (z.re : ℂ) ∈ closure H := by
      rw [CA.Car.closure_H_eq_Hbar]; simp [Hbar]
    have := mem_closure_iff_nhdsWithin_neBot.1 hmem
    refine Tendsto.limUnder_eq ?_
    refine ((continuous_id.tendsto (z.re : ℂ)).mono_left nhdsWithin_le_nhds).congr' ?_
    exact eventually_nhdsWithin_of_forall fun w hw => (hH0 w hw).symm

/-- At time `0` the boundary extension `extInv W 0` is the identity, hence continuous on `ℍ̄`. -/
theorem continuousOn_extInv_zero (hW : Continuous W) (hW0 : W 0 = 0) :
    ContinuousOn (extInv W 0) Hbar :=
  continuousOn_id.congr fun _z hz => extInv_zero_eq_self hW hW0 hz

end Det

end F2

namespace WedgeUnzip

/-- **Core C holds: the global Carathéodory extension of `f_t⁻¹`.** -/
theorem globalCaraStmt_holds : GlobalCaraStmt := by
  intro κ hκ hκ4 Ω _ P _ B hB
  filter_upwards [RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le
      P B hB,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hK hc h0
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  intro t ht
  rcases ht.eq_or_lt with rfl | ht'
  · exact F2.continuousOn_extInv_zero hWc hW0
  · exact F2.continuousOn_extInv_of_simpleHull hWc hW0 ht' (by simpa [B2.Vr] using hK t ht')

end WedgeUnzip

end QuantumZipper
