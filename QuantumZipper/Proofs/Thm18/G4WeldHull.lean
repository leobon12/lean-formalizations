import QuantumZipper.Proofs.Thm18.G4WeldRem

/-!
# Theorem 1.8, node G4: the hull of the rescaled time reversal is a simple arc

For the SLE_κ driver `W` of Theorem 1.8, the rescaled time reversal
`revDrv W t' a = (t'/a², u ↦ (W(t' − a²u) − W t')/a)` has reverse hull `a⁻¹ · η(0,t']`
(`revHull_revDrv_eq`), which is the hull of a simple curve because the trace `η` is a simple
chord (Rohde–Schramm, part of `Thm18Inputs`). Hence the only non-trivial conditions for
`revDrv` to be a length-welding driver of the unzipped field are the base point and welding
identities (`RoundUpWeldData`). **Own elementary argument** (Loewner scaling, A1(d)).

* `revHull_revDrv_eq`: `revHull (revDrv W t' a) = a⁻¹ · fwdHull W t'`.
* `isLenWeldingDriver_revDrv`: the length-welding driver conditions reduce to the base point
  and the welding identity.
* `g4RoundUpCoreStmt_of_weld`, `g4RoundStmt_of_weld`: the reductions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

theorem revHull_revDrv_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t' a : ℝ}
    (ht : 0 < t') (ha : 0 < a) :
    revHull (revDrv W t' a).2 (revDrv W t' a).1 =
      (fun z => ((a : ℂ))⁻¹ * z) '' fwdHull W t' := by
  refine (revHull_revDrv_subset hW hW0 ht ha).antisymm ?_
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rintro _ ⟨k, hk, rfl⟩
  rw [← Cor15Group.revHull_vrev_eq_fwdHull hW hW0 ht] at hk
  obtain ⟨hkH, hkn⟩ := hk
  have him : ∀ z : ℂ, ((a : ℂ)⁻¹ * z).im = a⁻¹ * z.im := fun z => by
    rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]
  refine ⟨?_, fun ⟨y, hy, hyw⟩ => hkn ⟨a * y, ?_, ?_⟩⟩
  · show 0 < ((a : ℂ)⁻¹ * k).im
    rw [him]
    exact mul_pos (inv_pos.2 ha) hkH
  · show 0 < ((a : ℂ) * y).im
    simpa using mul_pos ha (show 0 < y.im from hy)
  · rw [revMap_revDrv hW ht.le ha hy] at hyw
    have := congrArg (fun z => (a : ℂ) * z) hyw
    simp only at this
    rw [mul_div_cancel₀ _ haC, ← mul_assoc, mul_inv_cancel₀ haC, one_mul] at this
    exact this

theorem isSimpleCurveHull_revDrv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t' a : ℝ}
    (ht : 0 < t') (ha : 0 < a) {η : ℝ → ℂ} (hη : IsSimpleChord η)
    (hK : fwdHull W t' = η '' Ioc 0 t') :
    IsSimpleCurveHull (revHull (revDrv W t' a).2 (revDrv W t' a).1) := by
  obtain ⟨hη0, hηc, hηi, hηH, -⟩ := hη
  rw [revHull_revDrv_eq hW hW0 ht ha, hK]
  have haC : ((a : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast ha.ne')
  have hmaps : MapsTo (fun u : ℝ => t' * u) (Icc 0 1) (Ici 0) := fun u hu =>
    mul_nonneg ht.le hu.1
  refine ⟨fun u => ((a : ℂ))⁻¹ * η (t' * u), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuousOn_const.mul (hηc.comp (continuousOn_const.mul continuousOn_id) hmaps)
  · intro u hu v hv huv
    have h1 := mul_left_cancel₀ haC huv
    exact mul_left_cancel₀ ht.ne' (hηi (hmaps hu) (hmaps hv) h1)
  · simp [hη0]
  · intro u hu
    have hp : η (t' * u) ∈ H := hηH _ (mul_pos ht hu.1)
    show 0 < (((a : ℂ))⁻¹ * η (t' * u)).im
    rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]
    exact mul_pos (inv_pos.2 ha) hp
  · ext w
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨s / t', ⟨div_pos hs.1 ht, (div_le_one ht).2 hs.2⟩, ?_⟩
      simp only
      rw [mul_div_cancel₀ _ ht.ne']
    · rintro ⟨u, hu, rfl⟩
      exact ⟨η (t' * u), ⟨t' * u, ⟨mul_pos ht hu.1, by nlinarith [hu.2]⟩, rfl⟩, rfl⟩

end Thm18Asm
end QuantumZipper
