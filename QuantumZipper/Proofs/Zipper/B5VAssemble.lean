import QuantumZipper.Proofs.Zipper.B5VReduce
import QuantumZipper.Proofs.Zipper.B5VFlow
import QuantumZipper.Proofs.Zipper.B5VSide
import QuantumZipper.Proofs.Zipper.B5LRID
import QuantumZipper.Proofs.RS.RealAlive

/-!
# B5-V at a fixed time from the window identities

Task B5V-FIX (`handoff/B5.md`, R1). For fixed `s ∈ (0,T]`, `t = T − s`, `V = Vr κ T B ω`,
`V' = Vr κ s B ω = vrev W s`, `F = realRevMap V t`:

* `vrev_shift`: `V (t + r) − V t = V' r` for `r ≥ 0`;
* `unzipLengths_fst_eq`: `L⁻_s = ν_{h⁰_s}[O⁻_s, 0]`, where `h⁰_s = h0f κ s` is the field unzipped
  by capacity time `s` (it is `Y_t = Yf κ T t`);
* **`ae_b5v_fixed_of_windows`**: B5-V at the fixed time `s`,
  `L⁻_s = ν_{h⁰}[0₋(T), 0₋(T − s)] = lenRHS κ T B X ω s` a.s., **given** the rational window
  identities `ν_{h⁰}(u,v) = ν_{h⁰_s}(F u, F v)` for `0₋(T) < u < v < 0₋(t)` a.s. (hypothesis
  `hwin`: the coordinate-change rule for the boundary measure, Sheffield arXiv:1012.4797,
  proof of Thm 1.3 / Lemma 5.6, pp. 66–68, at the pair `(h⁰_s, revMap V t)`; see the report of
  B5V-FIX for its status).

The endpoints are handled by `B5.realRevMap_endpoints` (`F → 0₋^{V'}(s)` at `0₋(T)⁺`, `F → 0` at
`0₋(t)⁻`) and `B5.sideImages_fst_eq_zeroMinus_vrev` (`O⁻_s = 0₋^{V'}(s)`); the atoms by B3(a)
(`ae_nu0_regular`, at horizons `T` and `s`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open B2

/-- `vrev W T (t + r) − vrev W T t = vrev W s r` for `t = T − s`, `0 ≤ s ≤ T`, `r ≥ 0`. -/
theorem vrev_shift {W : ℝ → ℝ} {T s r : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hr : 0 ≤ r) :
    vrev W T (T - s + r) - vrev W T (T - s) = vrev W s r := by
  have h : min (T - s + r) T = T - s + min r s := by
    rw [← min_add_add_left, sub_add_cancel]
  simp only [vrev]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ T - s + r), max_eq_left (by linarith : (0 : ℝ) ≤ T - s),
    max_eq_left hr, min_eq_left (by linarith : T - s ≤ T), h,
    show T - (T - s + min r s) = s - min r s by ring, show T - (T - s) = s by ring]
  ring

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- `L⁻_s = ν_{h⁰_s}[O⁻_s, 0]` (definitional). -/
theorem unzipLengths_fst_eq (s : ℝ) (ω : Ω) :
    (unzipLengths (Real.sqrt κ) (cfg κ B X ω) s).1 =
      qBoundaryMeasure (Real.sqrt κ) (h0f κ s B X ω) (Icc (sideImages (drive κ B ω) s).1 0) := by
  rw [unzipLengths_eq_unzippedField, h0f_eq_unzippedField]
  rfl

/-- **B5-V at a fixed time `s ∈ (0,T]`, from the window identities.** -/
theorem ae_b5v_fixed_of_windows (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hRSS : Blueprint.RohdeSchrammSimple) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    (hwin : ∀ᵐ ω ∂P, ∀ u v : ℚ, zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v →
      (v : ℝ) < zeroMinus (Vr κ T B ω) (T - s) →
      qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω) (Ioo u v) =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ s B X ω)
          (Ioo (realRevMap (Vr κ T B ω) (T - s) u) (realRevMap (Vr κ T B ω) (T - s) v))) :
    ∀ᵐ ω ∂P, (unzipLengths (Real.sqrt κ) (cfg κ B X ω) s).1 = lenRHS κ T B X ω s := by
  have hT : 0 < T := hs.trans_le hsT
  filter_upwards [hwin, hB.cont, hB.eval_zero_ae_eq_zero,
    ae_isSimpleCurveHull_revHull_Vr hRSS hκ hκ4.le hT P B hB,
    ae_isSimpleCurveHull_revHull_Vr hRSS hκ hκ4.le hs P B hB,
    RS.ae_real_alive hB hκ hκ4.le,
    ae_nu0_regular hReg hκ hκ4 hT hB hX hind,
    ae_nu0_regular hReg hκ hκ4 hs hB hX hind] with ω hw hc h0 hK hK' halive hνT hνs
  set W := drive κ B ω with hWdef
  have hWc : Continuous W := Thm14FromThm13.continuous_drive hc
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  have hVc : Continuous (Vr κ T B ω) := continuous_vrev hWc T
  have hV0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
  have hV'c : Continuous (Vr κ s B ω) := continuous_vrev hWc s
  have hV'0 : Vr κ s B ω 0 = 0 := vrev_zero hs.le
  have hshift : ∀ r, 0 ≤ r → Vr κ s B ω r = Vr κ T B ω (T - s + r) - Vr κ T B ω (T - s) :=
    fun r hr => (vrev_shift hs.le hsT hr).symm
  obtain ⟨hac, hmono, hA, hC⟩ := realRevMap_endpoints hVc hV0 hT hK hV'c hV'0 hs hK'
    (sub_nonneg.2 hsT) (by ring) hshift
  have hside : (sideImages W s).1 = zeroMinus (Vr κ s B ω) s :=
    sideImages_fst_eq_zeroMinus_vrev hWc hW0 hs hK' fun x hx => halive x hx s hs.le
  rw [unzipLengths_fst_eq, ← hWdef, hside]
  exact (measure_Icc_eq_of_windows hac hmono hA hC hw (hνT.1 _) (hνT.1 _) (hνs.1 _)
    (hνs.1 _)).symm

end B5
end QuantumZipper
