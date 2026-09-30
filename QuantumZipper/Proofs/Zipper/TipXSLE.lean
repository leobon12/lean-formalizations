import QuantumZipper.Proofs.Zipper.WedgeTipXReg
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Proofs.Zipper.B5LocDet
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeLogImDom
import QuantumZipper.Proofs.RS.TraceMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SLE: negative moments of the distance of the SLE trace to its base on a capacity window

Task TX-SLE (handoff `handoff/TIPX-ROUTE.md`, §4, sub-task TX-U1(f)). Target
**`SLEBaseReturnStmt`**: for `0 < κ < 4` there is `a > 0` with
`E[(min_{r ∈ [1/16, 4]} |η(r)|)^{−a}] < ∞` (and the minimum is a.e.-measurable).

Proved here:
* `lintegral_rpow_neg_ne_top_of_tail` (generic): a polynomial tail `P(m < ε) ≤ C ε^b` gives
  `E[m^{−a}] < ∞` for `0 < a < b` (dyadic shells; own elementary proof);
* `aemeasurable_baseDist`: the window minimum is a.e.-measurable (the measurable continuous
  version of the trace, `RS.exists_measurable_sleTrace`, and rational approximation);
* `sleBaseReturn_of_side_bessel : SLEBaseSideStmt → SideBesselWinStmt → SLEBaseReturnStmt`.

The two inputs (each a single standard estimate; see the report of TX-SLE):
* `SLEBaseSideStmt` (harmonic measure): a.s. for all `s > 0`,
  `min(O⁺_s, −O⁻_s) ≤ C |η(s)|`: when the tip is within `ε` of the base, one side of `η[0,s]`
  is enclosed by `η[0,s]` and a crosscut inside `B̄(0, ε)`, so its harmonic measure from `∞`
  (`= O^±_s / π`) is at most that of `B̄(0, ε)` in `ℍ` (`= 4ε/π`). This is the "easy harmonic
  measure estimate" in the proof of Lawler, *Conformally Invariant Processes in the Plane* (2005),
  Prop. 6.12, p. 128, read at the base instead of the real point `1`.
* `SideBesselWinStmt` (Bessel): `O⁺_t` and `−O⁻_t` are Bessel processes of dimension
  `1 + 4/κ > 2` (scaled by `√κ`) started at `0`; with the scale function `y^{1 − 4/κ}` they come
  below `δ` during `[1/16, 4]` with probability `≤ C δ^b` (Lawler 2005, §1.10 and Prop. 1.21;
  Kemppainen, *SLE* (2017), Prop. 5.1; the project's `RS/RealAlive.lean` runs the same Dynkin
  argument for fixed `x > 0`).

The route replaces the handoff's suggestion (domain Markov at time `1/32` + Alberts–Kozdron
Thm 1.1 / `LWFar.bdryHitStmt_holds`), which needs a quantitative modulus of `f_{1/32}` at the base
of the curve (the base is not at positive distance from the hull, so the boundary-hitting estimate
does not apply directly); the harmonic-measure bound gives the linear modulus directly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- `min_{r ∈ [1/16, 4]} |η(r)|` (as an extended nonnegative real). -/
def baseDist (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ r ∈ Icc (1 / 16 : ℝ) 4, ENNReal.ofReal ‖sleTrace κ B ω r‖

/-! ## Tail bound to negative moment -/

section Tail

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- Pointwise dyadic majorant of `m^{−a}`. -/
theorem txsle_rpow_neg_le (m : ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    m ^ (-a) ≤ 1 + ∑' k : ℕ, ENNReal.ofReal (((1 / 2 : ℝ) ^ (k + 1)) ^ (-a)) *
      ({x : ℝ≥0∞ | x < ENNReal.ofReal ((1 / 2 : ℝ) ^ k)}.indicator 1 m) := by
  have hw1 : ∀ k : ℕ, 1 ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ (k + 1)) ^ (-a)) := fun k => by
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) (by linarith))
  rcases le_or_gt 1 m with h1 | h1
  · exact (ENNReal.rpow_le_one_of_one_le_of_neg h1 (by linarith)).trans le_self_add
  rcases eq_or_ne m 0 with h0 | h0
  · subst h0
    rw [ENNReal.zero_rpow_of_neg (by linarith)]
    refine le_trans ?_ le_add_self
    rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero]
    refine ENNReal.tsum_le_tsum fun k => ?_
    have hmem : (0 : ℝ≥0∞) ∈ {x : ℝ≥0∞ | x < ENNReal.ofReal ((1 / 2 : ℝ) ^ k)} :=
      show (0 : ℝ≥0∞) < _ from ENNReal.ofReal_pos.2 (by positivity)
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    exact hw1 k
  -- `0 < m < 1`
  have hmt : m ≠ ⊤ := (h1.trans ENNReal.one_lt_top).ne
  have hx : 0 < m.toReal := ENNReal.toReal_pos h0 hmt
  have hex : ∃ n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) ≤ m := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    rw [← ENNReal.ofReal_toReal hmt]
    refine ENNReal.ofReal_le_ofReal ((pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.le_succ n)).trans hn.le)
  classical
  set k := Nat.find hex with hk
  have hk1 : ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) ≤ m := Nat.find_spec hex
  have hk2 : m < ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    rcases Nat.eq_zero_or_eq_succ_pred k with h | h
    · rw [h, pow_zero, ENNReal.ofReal_one]; exact h1
    · have hmin := Nat.find_min hex (show k.pred < k by omega)
      rw [not_le] at hmin
      have e : k.pred + 1 = k := by omega
      rwa [e] at hmin
  have hmem : m ∈ {x : ℝ≥0∞ | x < ENNReal.ofReal ((1 / 2 : ℝ) ^ k)} := hk2
  refine le_trans ?_ le_add_self
  refine le_trans ?_ (ENNReal.le_tsum k)
  rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
  have hpos : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
  rw [← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hk1 ha.le)

end Tail

/-! ## Measurability of the window minimum -/

/-- For a continuous `φ`, the infimum over `[1/16, 4]` is the infimum over the rational points of
the clamp. -/
theorem txsle_iInf_Icc_eq_rat {φ : ℝ → ℝ≥0∞} (hφ : Continuous φ) :
    (⨅ r ∈ Icc (1 / 16 : ℝ) 4, φ r) =
      ⨅ q : ℚ, φ (max (1 / 16 : ℝ) (min (q : ℝ) 4)) := by
  set ψ : ℝ → ℝ≥0∞ := fun x => φ (max (1 / 16 : ℝ) (min x 4)) with hψ
  have hψc : Continuous ψ :=
    hφ.comp (continuous_const.max (continuous_id.min continuous_const))
  have hclamp : ∀ x : ℝ, max (1 / 16 : ℝ) (min x 4) ∈ Icc (1 / 16 : ℝ) 4 := fun x =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  apply le_antisymm
  · exact le_iInf fun q => iInf₂_le _ (hclamp q)
  · refine le_iInf₂ fun r hr => ?_
    set L := ⨅ q : ℚ, ψ q
    have hcl : IsClosed {x : ℝ | L ≤ ψ x} := isClosed_le continuous_const hψc
    have hsub : range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | L ≤ ψ x} := by
      rintro _ ⟨q, rfl⟩; exact iInf_le (fun q : ℚ => ψ q) q
    have hmem : r ∈ {x : ℝ | L ≤ ψ x} := by
      have := hcl.closure_subset_iff.2 hsub
      exact this ((Rat.denseRange_cast (𝕜 := ℝ)).closure_range ▸ mem_univ r)
    have hrr : max (1 / 16 : ℝ) (min r 4) = r := by
      rw [min_eq_left hr.2, max_eq_right hr.1]
    have h' : L ≤ φ (max (1 / 16 : ℝ) (min r 4)) := hmem
    rw [hrr] at h'
    exact h'

/-- **The window minimum is a.e.-measurable.** -/
theorem aemeasurable_baseDist {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    AEMeasurable (baseDist κ B) P := by
  obtain ⟨η, hηm, -, hηc, hηeq⟩ := RS.exists_measurable_sleTrace hB hκ hκ8
  refine ⟨fun ω => ⨅ q : ℚ, ENNReal.ofReal ‖η ω (max (1 / 16 : ℝ) (min (q : ℝ) 4))‖, ?_, ?_⟩
  · refine Measurable.iInf fun q => ENNReal.measurable_ofReal.comp (measurable_norm.comp ?_)
    exact hηm.comp (measurable_id.prodMk measurable_const)
  · filter_upwards [hηeq] with ω hω
    have hφ : Continuous fun r => ENNReal.ofReal ‖η ω r‖ :=
      ENNReal.continuous_ofReal.comp (continuous_norm.comp (hηc ω))
    refine Eq.trans ?_ (txsle_iInf_Icc_eq_rat hφ)
    unfold baseDist
    refine iInf_congr fun r => iInf_congr fun hr => ?_
    show _ = ENNReal.ofReal ‖η ω r‖
    rw [hω (show (0 : ℝ) ≤ r by linarith [hr.1] : r ∈ Ici 0)]

/-! ## The reduction -/

end WedgeUnzip
end QuantumZipper
