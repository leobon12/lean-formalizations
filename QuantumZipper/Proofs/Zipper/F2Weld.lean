import QuantumZipper.Proofs.Zipper.F2Reduce
import QuantumZipper.Proofs.Zipper.B2Driver
import QuantumZipper.Proofs.Zipper.ESMLMeas
import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.LQG.RevCouplingReg

/-!
# F2 step (1): B5 for the Theorem 1.3 configuration (`F2WeldLenStmt`), reduced to B5 and the
welding structure

Source: Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797, §5.1 (lengths by unzipping) and §5.4 (proof of Theorem 1.3, pp. 70–72, step
"the Theorem 1.3 field is the unzipped `Γ⁰` field"); blueprint node B5 (`SECTION5_BLUEPRINT.md`)
and F2 step (1).

Let `W = √κ B` (the Theorem 1.3 reverse driver), `V = vrev W T` (the forward driver of `η_T`),
`h = couplingFieldRev κ W T X` and `L^±_r` the lengths `unzipLengths` of `cfgT = (𝔥₀ + X, V)`.
The argument:
1. **Time reversal (B2(a), `B2.b2_V_brownian`).** `V = √κ B''` on `[0,T]` for a Brownian motion
   `B''` independent of `X`. So `cfgT` and the `Γ⁰` sample `B2.cfg κ B'' X` have the same lengths
   on `[0,T]` (`ESM.unzipLengths_eq_of_drive_eqOn`), and the reverse driver of `B''` is
   `vrev V T = W` on `[0,T]`.
2. **B5 for `Γ⁰` (input `B5UniformStmt`).** A.s., for all `s ∈ [0,T]`,
   `L⁻_s = ν_{h⁰}[0₋(T), 0₋(T−s)]` and `L⁺_s = ν_{h⁰}[0₊(T−s), 0₊(T)]`, with `h⁰ = B2.h0f` and
   `0_± = zeroMinus/zeroPlus` of the reverse driver.
3. **A13 (`B2.b2_ident_qBoundaryMeasure`).** `ν_{h⁰} = ν_h` a.s.
4. **Welded pairs (input `WeldTimesStmt`).** A welded pair with image on `η_T ∪ {0}` is
   `(0₋(u), 0₊(u))` for some reverse time `u ∈ [0,T]` (the image is `η(T − u)`).
5. **Additivity** (own elementary argument): `ν[0₋(u),0] + ν[0₋(T),0₋(u)] = ν[0₋(T),0]` since
   `ν_h` has no atoms (RCBMR); `r := T − u`; `L⁻_T = ν_h[0₋(T), 0] < ∞` (RCBMR, `0₋(0) = 0`).

## Inputs (open; exact statements below)
* `B5UniformStmt`: blueprint B5 (§5.1) in the B2 notation, both sides, **uniformly** in
  `s ∈ [0,T]` (the minus side is the hypothesis `hB5V` of `B5.ae_lr_id`; the fixed-time minus
  side is proved as `B5.ae_b5v_fixed_pos`). This is item R2 of `handoff/B5.md`.
* `WeldTimesStmt`: the welding structure of the reverse `SLE_κ` hull (deterministic given the
  simple-curve hull, `RohdeSchrammSimple`); the minus-side facts are `B5.hitTime_spec`,
  `B5.strictAntiOn_zeroMinus`; the plus side and the equality of the two hitting times are not
  in the repository.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-! ## The open inputs -/

/-- **Welding structure of the reverse `SLE_κ` hull** (Sheffield §1.3–§1.4; Rohde–Schramm).
A.s., every pair `x₋ < 0 < x₊` identified by the boundary extension of `f_T = revMap W T`
(`W = √κ B`) at a point of `η_T` or at the base point `0` is the pair `(0₋(u), 0₊(u))` of the
points swallowed at some reverse time `u ∈ [0,T]` (the pair is glued at time `u` and sent to
`η(T − u)`), and it lies in `[0₋(T), 0₊(T)]`. -/
def WeldTimesStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ ω ∂P, ∀ xm xp : ℝ, xm < 0 → 0 < xp →
      revMapBdry (drive κ B ω) T xm = revMapBdry (drive κ B ω) T xp →
      revMapBdry (drive κ B ω) T xm ∈ insert 0 (revHull (drive κ B ω) T) →
      ∃ u ∈ Icc (0 : ℝ) T, xm = zeroMinus (drive κ B ω) u ∧ xp = zeroPlus (drive κ B ω) u ∧
        zeroMinus (drive κ B ω) T ≤ xm ∧ xp ≤ zeroPlus (drive κ B ω) T

/-! ## Deterministic lemmas -/

theorem revMapBdry_congr_drive {V W : ℝ → ℝ} {u : ℝ} (h : EqOn V W (Icc 0 u)) :
    revMapBdry V u = revMapBdry W u := funext fun x => by
  unfold revMapBdry
  simp_rw [ReverseFlow.revMap_congr_drive _ h]

theorem zeroMinus_congr_drive {V W : ℝ → ℝ} {u : ℝ} (h : EqOn V W (Icc 0 u)) :
    zeroMinus V u = zeroMinus W u := by
  unfold zeroMinus; rw [revMapBdry_congr_drive h]

theorem zeroPlus_congr_drive {V W : ℝ → ℝ} {u : ℝ} (h : EqOn V W (Icc 0 u)) :
    zeroPlus V u = zeroPlus W u := by
  unfold zeroPlus; rw [revMapBdry_congr_drive h]

/-- `0₊(0) = 0` (mirror of `B5.zeroMinus_zero_time`): no positive point is sent to `0` at time
`0`, and `sInf ∅ = 0`. -/
theorem zeroPlus_zero_time {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) :
    zeroPlus W 0 = 0 := by
  have hb : ∀ x : ℝ, revMapBdry W 0 x = (x : ℂ) := fun x =>
    CaraR.revMapBdry_eq_of_extension_R8 (F := id)
      (fun z hz => (CharFun.revMap_zero_eq hW hW0 hz).symm) continuousOn_id x
  have hE : {x : ℝ | 0 < x ∧ revMapBdry W 0 x = 0} = ∅ := by
    ext x
    simp only [hb, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, Complex.ofReal_eq_zero]
    exact fun hx h => hx.ne' h
  unfold zeroPlus
  rw [hE, Real.sInf_empty]

/-- Own elementary argument: additivity of an atomless measure over adjacent closed intervals. -/
theorem measure_Icc_add_Icc {ν : Measure ℝ} (hat : ∀ x, ν {x} = 0) {a b c : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) : ν (Icc a b) + ν (Icc b c) = ν (Icc a c) := by
  have : NullSingletonClass ν := ⟨hat⟩
  have hd : Disjoint (Icc a b) (Ioc b c) :=
    Set.disjoint_left.2 fun x h1 h2 => absurd h1.2 (not_le.2 h2.1)
  rw [← Icc_union_Ioc_eq_Icc hab hbc, measure_union hd measurableSet_Ioc,
    measure_congr (Ioc_ae_eq_Icc (μ := ν))]

/-! ## The reduction -/

end F2
end QuantumZipper
