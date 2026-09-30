import QuantumZipper.Proofs.Thm18.G3FidProxy
import QuantumZipper.Proofs.Thm18.G3G2LocDet
import QuantumZipper.Proofs.Zipper.D3PlusN1Local

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-FIX (1): the measurable canonical proxy from a local area limit

`locFieldFull_canonProxy_eq`: if `y` agrees near `0` (radius `r`) with a field `y'` whose area
approximations have a vague limit on the half-disc `halfDisc r`, and the local scale `s` of `y'`
satisfies `0 < s`, `s (R + 1) < r`, then the measurable scale proxy of `y` is `s` and the rich
local data of the measurable canonical description `canonProxy γ y` are those of the local
canonical description `canonicalOn γ y' (halfDisc r)`. No global area limit of `y` is needed.

Local copy of `scaleProxy_eq_scaleParam` (G3FidProxy) and of
`E5.locFieldFull_canonical_eq_canonicalOn`; own elementary argument (AGENT_GUIDE cost rule).
Used for the zoom of the Palm field through the local maps (Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 65: the zoomed figure only depends on the field near the point).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqF

open D3Plus LQGMeas

/-- The area proxy computes the local area limit on half-discs inside `halfDisc r`. -/
theorem areaProxy_eq_of_local {γ r : ℝ} {y : FieldSample} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn (halfDisc r) (areaApprox γ y) μ) {a : ℝ} (ha : a ≤ r) :
    areaProxy γ y a = μ (Metric.ball (0 : ℂ) a ∩ H) := by
  set U : Set ℂ := Metric.ball (0 : ℂ) a ∩ H with hU
  have hUo : IsOpen U := Metric.isOpen_ball.inter isOpen_H
  have hUb : Bornology.IsBounded U := Metric.isBounded_ball.subset inter_subset_left
  have hUc : Uᶜ.Nonempty :=
    ⟨0, fun h => by simpa [H] using (inter_subset_right h : (0 : ℂ) ∈ H)⟩
  have hUr : U ⊆ halfDisc r := fun z hz => ⟨Metric.ball_subset_ball ha hz.1, hz.2⟩
  unfold areaProxy
  rw [← hU, measure_open_eq_iSup _ hUo hUc]
  congr 1
  funext n
  have hsupp : tsupport (openBump U n) ⊆ halfDisc r := (tsupport_openBump_subset U n).trans hUr
  have hlim := hμ.2.2 _ (continuous_openBump U n) (hasCompactSupport_openBump hUb n) hsupp
  rw [areaFun, hlim.liminf_eq,
    ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ fun z => openBump_nonneg U n z)]
  exact GoodSample.integrable_of_tsupport hμ.2.1 (continuous_openBump U n)
    (hasCompactSupport_openBump hUb n) hsupp

/-- **The measurable canonical proxy from a local area limit.** -/
theorem locFieldFull_canonProxy_eq {γ r : ℝ} {R : ℕ} {y y' : FieldSample}
    (hag : AgreeNear y y' r) {μ : Measure ℂ}
    (hμ : IsVagueLimitOn (halfDisc r) (areaApprox γ y') μ)
    (hpos : 0 < scaleParamOn γ y' (halfDisc r))
    (hlt : scaleParamOn γ y' (halfDisc r) * ((R : ℝ) + 1) < r) :
    scaleProxy γ y = scaleParamOn γ y' (halfDisc r) ∧
    locFieldFull R (canonProxy γ y) = locFieldFull R (canonicalOn γ y' (halfDisc r)) := by
  set s := scaleParamOn γ y' (halfDisc r) with hs
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hsR : s * R < r := lt_of_le_of_lt (by nlinarith) hlt
  have hsr : s < r := lt_of_le_of_lt (by nlinarith) hlt
  have hμy : IsVagueLimitOn (halfDisc r) (areaApprox γ y) μ :=
    isVagueLimitOn_halfDisc_of_agree hag.symm' hμ
  set A : ℝ → ℝ≥0∞ := fun a => μ (Metric.ball (0 : ℂ) a ∩ H) with hA
  have hmono : Monotone A := fun a b hab =>
    measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball hab))
  set T : Set ℝ := {a : ℝ | 0 < a ∧ 1 ≤ A a} with hT
  have hsT : s = sInf T := by
    rw [hs, scaleParamOn, LocalRule.qAreaMeasureOn_eq (isOpen_halfDisc r) hμ]
  set SA : Set ℝ := {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧ 1 ≤ A q} with hSA
  have hSAT : sInf SA = sInf T := sInf_rat_le_eq_sInf (fun _ _ => rfl) hmono
  set SP : Set ℝ := {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧
    1 ≤ areaProxy γ y q} with hSP
  -- an element of `T` below `r`
  have hTne : T.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hsT, hne, Real.sInf_empty] at hpos
    exact lt_irrefl _ hpos
  have hTb : BddBelow T := ⟨0, fun a ha => ha.1.le⟩
  obtain ⟨b, hbT, hbr⟩ := exists_lt_of_csInf_lt hTne (hsT ▸ hsr)
  obtain ⟨q₀, hbq, hqr⟩ := exists_rat_btwn hbr
  have hq₀0 : 0 < (q₀ : ℝ) := hbT.1.trans hbq
  have hAq₀ : 1 ≤ A q₀ := hbT.2.trans (hmono hbq.le)
  have hPA : ∀ q : ℝ, q ≤ r → areaProxy γ y q = A q := fun q hq =>
    areaProxy_eq_of_local hμy hq
  have hSPe : scaleProxy γ y = sInf SP := rfl
  have heq : sInf SP = sInf SA := by
    refine sInf_eq_of_agree_below ⟨0, fun a ha => ha.1.le⟩ ⟨0, fun a ha => ha.1.le⟩
      (q := q₀) ⟨hq₀0, q₀, hq₀0, le_rfl, by rw [hPA _ hqr.le]; exact hAq₀⟩
      ⟨hq₀0, q₀, hq₀0, le_rfl, hAq₀⟩ fun a ha => ?_
    constructor
    · rintro ⟨ha0, q, hq0, hqa, h1⟩
      exact ⟨ha0, q, hq0, hqa, by rw [← hPA _ ((hqa.trans ha).trans hqr.le)]; exact h1⟩
    · rintro ⟨ha0, q, hq0, hqa, h1⟩
      exact ⟨ha0, q, hq0, hqa, by rw [hPA _ ((hqa.trans ha).trans hqr.le)]; exact h1⟩
  have hscale : scaleProxy γ y = s := by rw [hSPe, heq, hSAT, ← hsT]
  refine ⟨hscale, ?_⟩
  rw [canonProxy, canonicalOn, hscale]
  exact locFieldFull_rescale_congr hag hpos hsR

end G3ZqF
end Thm18Asm
end QuantumZipper
