import QuantumZipper.Proofs.Zipper.F1PStarZipLenCore
import QuantumZipper.Proofs.Zipper.RegUnifDet

/-!
# Theorem 1.3, node F1 (D29): the constant shift is `RegEq`-stable on regular samples

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 (rule (5.1): adding a
constant `C` to a field multiplies boundary lengths by `e^{γC/2}`) and §5.4 (pp. 70–72). The
bookkeeping below is our own.

`F1.PStarZipLenInputsStmt` contains a field identity for the *shifted* configuration
`canonConfig γ (Y + k, drive κ B')`. To use it one must compare the shifted field with the
unshifted one, i.e. pass a `RegEq` statement through `addConst`. `avgReg` is a `limUnder`, so
this is *not* automatic at the (junk) centres outside `Hbar`; but for **regular** samples it is
true at every centre, because the raw values at the folded dyadic centres of a regular sample
are the honest ones: `y (foldedCircle d (radius k)) = F (d, radius k)` for `d ∈ Dy`. This file
proves that fact (from clause (ii) of `IsRegularWith` and the eventual stability of the dyadic
rounding at a dyadic lattice point, `dyadicRoundC_foldH_stable`), and derives

* `avgReg_eq_witness_foldH`: `avgReg y k z = F (foldH z, radius k)` for *every* `z : ℂ`;
* `avgReg_addConst_eq_witness`: `avgReg (y + c) k z = F (foldH z, radius k) + c`;
* `RegEq.addConst_of_isRegularSample`: `RegEq` is preserved by additive constants on regular
  samples (and hence `scaleParam`, `canonical` are too), which is the step that identifies the
  shifted `P_*` field `Y + k` with `canonical γ (zU γ X' A) + k` in the realization of core P.

The transport is what D29's node table calls "W-X/W-C transported through `addConst`"; the
remaining input of `PStarShiftRegStmt` is the convergence of the smoothed pairings along the
pushed circles (`RegShift`), which regularity alone does not give (clause (iii) of
`IsRegularWith` smooths at the same radius; the limit `ρ → 0⁺` is the good-sample input).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1

/-! ## Dyadic lattice points are stable under rounding -/

/-- `floor` at a finer dyadic mesh does nothing to a dyadic rational. -/
theorem dyadicRound_div_pow (m n : ℕ) (hn : n ≤ m) (a : ℤ) :
    dyadicRound m ((a : ℝ) / 2 ^ n) = (a : ℝ) / 2 ^ n := by
  have hpow : (2 : ℝ) ^ m = 2 ^ (m - n) * 2 ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  have hkey : (2 : ℝ) ^ m * ((a : ℝ) / 2 ^ n) = (((2 : ℤ) ^ (m - n) * a : ℤ) : ℝ) := by
    rw [hpow]
    push_cast
    field_simp
  unfold dyadicRound
  rw [hkey, Int.floor_intCast, hpow]
  push_cast
  field_simp

theorem dyadicRoundC_mk_div_pow (m n : ℕ) (hn : n ≤ m) (a b : ℤ) :
    dyadicRoundC m (⟨(a : ℝ) / 2 ^ n, (b : ℝ) / 2 ^ n⟩ : ℂ) =
      (⟨(a : ℝ) / 2 ^ n, (b : ℝ) / 2 ^ n⟩ : ℂ) :=
  Complex.ext (dyadicRound_div_pow m n hn a) (dyadicRound_div_pow m n hn b)

/-- **A folded dyadic point is a fixed point of all finer roundings.** The point
`foldH (dyadicRoundC n z)` has dyadic coordinates `(a/2^n, |b|/2^n)`, hence
`dyadicRoundC m (foldH (dyadicRoundC n z)) = foldH (dyadicRoundC n z)` for every `m ≥ n`. -/
theorem dyadicRoundC_foldH_stable (n : ℕ) (z : ℂ) :
    ∀ m ≥ n, dyadicRoundC m (foldH (dyadicRoundC n z)) = foldH (dyadicRoundC n z) := by
  intro m hm
  set a : ℤ := ⌊(2 : ℝ) ^ n * z.re⌋ with ha
  set b : ℤ := ⌊(2 : ℝ) ^ n * z.im⌋ with hb
  have hq : dyadicRoundC n z = (⟨(a : ℝ) / 2 ^ n, (b : ℝ) / 2 ^ n⟩ : ℂ) := rfl
  have hfold : foldH (⟨(a : ℝ) / 2 ^ n, (b : ℝ) / 2 ^ n⟩ : ℂ) =
      (⟨(a : ℝ) / 2 ^ n, ((|b| : ℤ) : ℝ) / 2 ^ n⟩ : ℂ) := by
    refine Complex.ext ?_ ?_
    · rw [TwoPoint.re_foldH]
    · rw [TwoPoint.im_foldH]
      show |(b : ℝ) / 2 ^ n| = ((|b| : ℤ) : ℝ) / 2 ^ n
      rw [Int.cast_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n)]
  rw [hq, hfold]
  exact dyadicRoundC_mk_div_pow m n hm a |b|

/-! ## Raw values at the folded dyadic circles -/

/-- **Raw values at `Dy` are the honest ones.** For a sample regular with witness `F`, the raw
value at every folded dyadic circle is `F` at that circle: the raw values along the rounding
sequence are eventually constant there (`dyadicRoundC_foldH_stable`) and converge to `F` by
clause (ii) of `IsRegularWith`. -/
theorem rawValue_Dy_of_isRegularWith {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) :
    ∀ k : ℕ, ∀ d ∈ RegUnif.Dy, y (foldedCircle d (radius k)) = F (d, radius k) := by
  intro k d hd
  obtain ⟨n, z, rfl⟩ := by
    simpa only [RegUnif.Dy, Set.mem_iUnion, Set.mem_range] using hd
  have hmem : foldH (dyadicRoundC n z) ∈ Hbar := CircleFubini.foldH_mem_Hbar' _
  have hT := hF.2.1 k _ hmem
  have hev : (fun m : ℕ => y (foldedCircle (dyadicRoundC m (foldH (dyadicRoundC n z)))
        (radius k))) =ᶠ[atTop]
      fun _ : ℕ => y (foldedCircle (foldH (dyadicRoundC n z)) (radius k)) :=
    Filter.eventually_atTop.2 ⟨n, fun m hm => by
      show y (foldedCircle (dyadicRoundC m (foldH (dyadicRoundC n z))) (radius k)) =
        y (foldedCircle (foldH (dyadicRoundC n z)) (radius k))
      rw [dyadicRoundC_foldH_stable n z m hm]⟩
  exact tendsto_const_nhds_iff.1 (hT.congr' hev)

/-- Raw convergence of a regular sample at **every** centre of `ℂ`, to the witness at the folded
centre (`RegUnif.tendsto_raw_of_witness` with its raw-value hypothesis discharged). -/
theorem tendsto_raw_of_isRegularWith {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) (k : ℕ) (z : ℂ) :
    Tendsto (fun n => y (foldedCircle (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (F (foldH z, radius k))) :=
  RegUnif.tendsto_raw_of_witness hF.1 (rawValue_Dy_of_isRegularWith hF) k z

/-- **`avgReg` of a regular sample at an arbitrary centre** is the witness at the folded
centre (the junk centres outside `Hbar` read the folded circle, which is a dyadic point). -/
theorem avgReg_eq_witness_foldH {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) (k : ℕ) (z : ℂ) :
    avgReg y k z = F (foldH z, radius k) := by
  unfold avgReg
  exact (tendsto_raw_of_isRegularWith hF k z).limUnder_eq

/-- **`avgReg` of a shifted regular sample**: the constant shift passes through `avgReg` at
*every* centre, not only at the admissible ones. -/
theorem avgReg_addConst_eq_witness {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) (c : ℝ) (k : ℕ) (z : ℂ) :
    avgReg (addConst y c) k z = F (foldH z, radius k) + c := by
  unfold avgReg
  rw [show (fun n => addConst y c (foldedCircle (dyadicRoundC n z) (radius k))) =
      (fun n => y (foldedCircle (dyadicRoundC n z) (radius k)) + c) from
    funext fun n => by simp only [addConst, measure_univ, ENNReal.toReal_one, mul_one]]
  exact ((tendsto_raw_of_isRegularWith hF k z).add_const c).limUnder_eq

/-! ## `RegEq` passes through additive constants -/

/-- **`RegEq` is preserved by additive constants on regular samples.** -/
theorem RegEq.addConst_of_isRegularSample {x y : FieldSample} (hx : IsRegularSample x)
    (hy : IsRegularSample y) (h : RegEq x y) (c : ℝ) :
    RegEq (addConst x c) (addConst y c) := by
  obtain ⟨F, hF⟩ := hx
  obtain ⟨G, hG⟩ := hy
  intro k z
  rw [avgReg_addConst_eq_witness hF c k z, avgReg_addConst_eq_witness hG c k z,
    ← avgReg_eq_witness_foldH hF k z, h k z, avgReg_eq_witness_foldH hG k z]

/-- Function form of `RegEq.addConst_of_isRegularSample`. -/
theorem avgReg_addConst_congr_of_isRegularSample {x y : FieldSample} (hx : IsRegularSample x)
    (hy : IsRegularSample y) (h : avgReg x = avgReg y) (c : ℝ) :
    avgReg (addConst x c) = avgReg (addConst y c) :=
  funext fun k => funext fun z => RegEq.addConst_of_isRegularSample hx hy (fun k z => congrFun (congrFun h k) z) c k z

/-- **The canonical scale passes through additive constants** (for regular samples agreeing in
`avgReg`). -/
theorem scaleParam_addConst_congr_of_isRegularSample {x y : FieldSample} (hx : IsRegularSample x)
    (hy : IsRegularSample y) (h : avgReg x = avgReg y) (c : ℝ) (γ : ℝ) :
    scaleParam γ (addConst x c) = scaleParam γ (addConst y c) :=
  Factorization.scaleParam_congr (avgReg_addConst_congr_of_isRegularSample hx hy h c) γ

end F1
end QuantumZipper
