import QuantumZipper.Blueprint.ComplexAnalysis
import QuantumZipper.SLE.Defs
import QuantumZipper.Loewner.Forward
import QuantumZipper.Analysis.Holder
import Mathlib.Probability.BrownianMotion.Basic

/-!
# External blueprint items, part 3 (DECISIONS D2, D4, D6)

`Prop`-valued statements of published results that are not proved in this project yet.
Nothing is proved here.

* `RevMapHolder`: Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 5.2
  (p. 21), for κ < 4 (DECISIONS D6; DEVIATIONS L-RMH).
* `SLEOnePointBound`: Beffara, *The dimension of the SLE curves*, Ann. Probab. 36 (2008),
  Prop. 4 (p. 6), upper half, κ < 4 (DECISIONS D2; DEVIATIONS L-S1).
* `RohdeSchrammTraceGen`: Rohde–Schramm Thm 5.1 (p. 20) / Kemppainen, *Schramm–Loewner
  Evolution* (2017), Thm 5.2 and Def. 5.3 (p. 76) (DECISIONS D4; DEVIATIONS L-AD1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper.Blueprint

/-- **Hölder continuity of the reverse SLE map** (DECISIONS D6; DEVIATIONS L-RMH). For
κ ∈ (0,4) and `T > 0`, a.s. every Carathéodory extension of the reverse Loewner map at time `T`
is Hölder on every box `[-R,R] × [0,R]`, with an exponent that may depend on `ω` and `R`.
RS Thm 5.2 (p. 21) states the Hölder bound for `f̂_t = fwdMapInv W t`, the **inverse of the
centered forward map** `g_t − W_t` (not "the forward map"; AUDIT6 P3), on bounded subsets of `ℍ`.
The bound here is the reverse-time counterpart obtained from RS's martingale estimate (5.2) and
its proof (p. 22) — grid, Koebe distortion and Hardy–Littlewood (`RS.ae_revMap_holder`) — and it is
extended from `ℍ` to the closed box (including the real boundary) by continuity of the
Carathéodory extension (own elementary argument, `RS.holder_box_of_holder_H`); it does **not** use
the time-reversal identity. It is **proved**: `RS.revMapHolder`, `Proofs/RS/HolderClosure.lean`. -/
def RevMapHolder : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ᵐ ω ∂P,
      ∀ F : ℂ → ℂ, IsCaratheodoryRevExt (drive κ B ω) T F → ∀ R : ℝ, 0 < R →
        IsHolderOn F (Set.Icc (-R) R ×ℂ Set.Icc 0 R)

/-- **One-point estimate for SLE**, upper half (Beffara 2008, Prop. 4, p. 6; DECISIONS D2;
DEVIATIONS L-S1). Beffara states no range for `ε`; the range `ε ≤ Im z` is that of
Lawler–Zhou, *SLE curves and natural parametrization* (arXiv:1006.4936), Prop. 2.3, and of
Lawler, *Conformally Invariant Processes in the Plane* (2005), Thm 7.9; it is project node S1-5
(`EXT_RS_BLUEPRINT.md` §5). `∃ C` is equivalent to `∃ C > 0`
(`sleOnePointBound_pos_const`). -/
def SLEOnePointBound : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ C : ℝ,
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ z ∈ H, ∀ ε : ℝ, 0 < ε → ε ≤ z.im →
      P {ω | Metric.infDist z (sleTrace κ B ω '' Set.Ici 0) < ε} ≤
        ENNReal.ofReal (C * (ε / z.im) ^ (1 - κ / 8) * (z.im / ‖z‖) ^ (8 / κ - 1))

/-- **Existence of the SLE trace and generation of the hulls** (Rohde–Schramm 2005, Thm 5.1,
p. 20; Kemppainen 2017, Thm 5.2, Def. 5.3, p. 76; DECISIONS D4, EXT_RS §5 AD1-0). -/
def RohdeSchrammTraceGen (κ : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ),
    IsBrownianReal B P → ∀ᵐ ω ∂P,
      sleTrace κ B ω 0 = 0 ∧ ContinuousOn (sleTrace κ B ω) (Set.Ici 0) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ M : ℝ, (∀ s ∈ Set.Icc 0 t, ‖sleTrace κ B ω s‖ < M) →
        H \ fwdHull (drive κ B ω) t =
          connectedComponentIn (H \ sleTrace κ B ω '' Set.Icc 0 t) (M * Complex.I)

/-- Sanity: the constant in `SLEOnePointBound` may be taken positive. -/
theorem sleOnePointBound_pos_const (h : SLEOnePointBound) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ z ∈ H, ∀ ε : ℝ, 0 < ε → ε ≤ z.im →
        P {ω | Metric.infDist z (sleTrace κ B ω '' Set.Ici 0) < ε} ≤
          ENNReal.ofReal (C * (ε / z.im) ^ (1 - κ / 8) * (z.im / ‖z‖) ^ (8 / κ - 1)) := by
  intro κ hκ hκ4
  obtain ⟨C, hC⟩ := h κ hκ hκ4
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro Ω _ P _ B hB z hz ε hε hεz
  refine (hC P B hB z hz ε hε hεz).trans (ENNReal.ofReal_le_ofReal ?_)
  have ha : 0 ≤ (ε / z.im) ^ (1 - κ / 8) := Real.rpow_nonneg (div_nonneg hε.le (hε.le.trans hεz)) _
  have hb : 0 ≤ (z.im / ‖z‖) ^ (8 / κ - 1) :=
    Real.rpow_nonneg (div_nonneg (le_of_lt (lt_of_lt_of_le hε hεz)) (norm_nonneg _)) _
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg ha hb)

/-- Sanity: `RohdeSchrammTraceGen` gives a.s. that the trace starts at `0`. -/
theorem RohdeSchrammTraceGen.ae_trace_zero {κ : ℝ} (h : RohdeSchrammTraceGen κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) : ∀ᵐ ω ∂P, sleTrace κ B ω 0 = 0 :=
  (h P B hB).mono fun _ hω => hω.1

/-- Sanity: `RevMapHolder` specializes to a fixed `κ`, `T`, Brownian motion. -/
theorem RevMapHolder.ae {κ T : ℝ} (h : RevMapHolder) (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) : ∀ᵐ ω ∂P,
      ∀ F : ℂ → ℂ, IsCaratheodoryRevExt (drive κ B ω) T F → ∀ R : ℝ, 0 < R →
        IsHolderOn F (Set.Icc (-R) R ×ℂ Set.Icc 0 R) :=
  h κ hκ hκ4 T hT P B hB

end QuantumZipper.Blueprint
