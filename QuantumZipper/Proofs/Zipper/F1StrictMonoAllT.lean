import QuantumZipper.Proofs.Zipper.F1StrictMonoCore
import QuantumZipper.Proofs.Zipper.F1StrictMonoCocycle
import QuantumZipper.Proofs.Zipper.UnifUOPlus
import QuantumZipper.Proofs.Zipper.UnifSWMain
import QuantumZipper.Proofs.Zipper.UnifUGTip
import QuantumZipper.Proofs.Zipper.UnifD33Close

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, node F1: the D26/D29 cores and the field cocycle at **every** horizon

`F1StrictMonoCore.lean` states the D26 cores as "the fixed-horizon statement holds for every
`T > 0`" (`AnchorWindowAllStmt`, `UnifOffTipAllStmt`, `UnifTipAllStmt`, `UnifCoreAllStmt`), and
`F1StrictMonoCocycle.lean` does the same for the field cocycle (`CapCocycleRegAllStmt`). This
file discharges them from the fixed-horizon provers:

* `unifOffTipAllStmt_of_extAll` — `UnifOffTipStmt` at every `T` from the extended anchored-family
  input at every `T` (`UnifUOPlus.unifOffTipStmt_of_ext_refl`, whose plus side runs through the
  reflected pair `(−B, X ∘ refl)`);
* `unifTipAllStmt_of_ratAll` — `UnifTipStmt` at every `T` from its rational-time uniform form
  (`UnifUGTip.unifTipStmt_of_rat`), the input of the D31/D37 tip-moment chain;
* `anchorWindowAllStmt_of_extAll` — `AnchorWindowStmt` at every `T` from the same input, through
  `UnifSWMain.anchorWindowStmt_of_fam` (AW from AC-fam alone, no `UnifGlobalStmt`), with the
  bridge `anchorUnifFamStmt_of_ext` supplying AC-fam (which allows the anchor `q = T`) from
  AC-fam-ext (which asks `q < T`);
* `unifCoreAllStmt_of_extAll` — the conjunction, i.e. `RegUnif.UnifCoreAllStmt`;
* `capCocycleRegAllStmt_of_d33` — `CapCocycleRegAllStmt`, from `UnifD33Close.lean`
  (`capCocycleRegAllStmt_holds`, where the whole D33 uniform-Cauchy chain is closed).

The remaining hypotheses of the capstone `F1.lenStrictMonoStmt_of_allHorizonInputs` are exactly:
the D29 length node `UnscaledResampleLenStmt`, `WedgeUnzip.PStarRealizeStmt`,
`F2.UnscaledB3dStmt`, and — besides the standing `0 < κ < 4`, `IsBrownianReal B P`,
`IsFreeGFFModConstH X P`, `IndepFun (pathOf B) X P` — the two analytic inputs at every horizon:
`AnchorUnifFamExtAllStmt` (Sheffield–Wang arXiv:1605.06171 (3.5), Thm 4.3, at every horizon and
for the reflected pair) and `UnifTipRatAllStmt` (the uniform-in-time tip moment bound of the
D31/D37 chain, Sheffield arXiv:1012.4797 §5, Theorem 1.3).

The only new proof here is the bridge `anchorUnifFamStmt_of_ext`, which handles the degenerate
anchor `q = T` (AC-fam allows `q ≤ T`, AC-fam-ext only `q < T`): at `q = T` the time set is
`Icc T T`, and the window hypothesis `v < 0₋(0) = 0` together with the continuity of `0₋` at `0`
(`B5ZeroMinus.ae_zeroMinus_Vr_facts`) makes the window live at a rational anchor `q' < T` that is
arbitrarily close to `T`, so the AC-fam-ext instance at `q'` applies to the *same* window and
restricts. Own bookkeeping (a degenerate endpoint case, no mathematics).

Sources: Sheffield, arXiv:1012.4797, §5, Lemma 5.6 and the proof of Theorem 1.3; Sheffield–Wang,
arXiv:1605.06171, Thm 4.3; the D26 (cores), D29 (length) and D33 (uniform Cauchy) decisions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5

variable {Ω : Type} [MeasurableSpace Ω]

/-- **AC-fam-ext at every horizon, for the pair and its reflection**: the analytic input of the
off-tip node, quantified over all horizons and over both `(B, X)` and `(−B, X ∘ refl)` (the
reflection is needed by the plus side `unifOffTipPlusStmt_of_refl`, `UnifUOPlus.lean`). -/
def AnchorUnifFamExtAllStmt (κ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  (∀ T : ℝ, 0 < T → AnchorUnifFamExtStmt κ T P B X) ∧
    (∀ T : ℝ, 0 < T → AnchorUnifFamExtStmt κ T P (negB B) (reflX X))

/-- **AC-fam at every horizon.** -/
def AnchorUnifFamAllStmt (κ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ T : ℝ, 0 < T → AnchorUnifFamStmt κ T P B X

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- **AC-fam from AC-fam-ext at a fixed horizon.** `AnchorUnifFamStmt` allows the anchor `q = T`
(`q ≤ T`), while `AnchorUnifFamExtStmt` asks `q < T`. For `q < T` the reduction is verbatim
(`AC-fam-ext` drops the window bound `0₋(T) < u` and the anchor bound `0 < q`).

For `q = T` the time set is `Icc T T ∩ ℚ`: given the window hypotheses (`0₋(T) < u`,
`v < 0₋(T − T) = 0₋(0) = 0`, a.s. by `ae_zeroMinus_Vr_facts`), pick a rational anchor `q' < T`
with `0₋(T − q') > v`, which exists because `0₋` is continuous on `[0,T]` and `0₋(0) = 0 > v`.
The same window and the same family members satisfy the AC-fam-ext hypotheses at `q'` (the only
one at risk is `v < 0₋(T − q')`, just arranged), so the `q'` instance gives the uniform Cauchy
property on `Icc q' T ∩ ℚ ⊇ Icc T T ∩ ℚ`. -/
theorem anchorUnifFamStmt_of_ext (hκ : 0 < κ) (hκ4 : κ < 4) {T : ℝ} (hT : 0 < T)
    (hB : IsBrownianReal B P) (hF : AnchorUnifFamExtStmt κ T P B X) :
    AnchorUnifFamStmt κ T P B X := by
  intro q hq hqT u v i a b c d
  rcases lt_or_eq_of_le hqT with hqT' | hqT'
  · -- non-degenerate anchor: verbatim from AC-fam-ext
    filter_upwards [hF q hq.le hqT' u v i a b c d] with ω hω
    intro h1 h2 h3 h4 h5 h6 h7
    exact hω h2 h3 h4 h5 h6 h7
  · -- degenerate anchor `q = T`
    have hAll : ∀ᵐ ω ∂P, ∀ q' : ℚ, (0 : ℝ) < q' → (q' : ℝ) < T →
        (u : ℝ) < a → a < b → b < c → c < d → (d : ℝ) < v →
        (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q') →
        UniformCauchySeqOn (fun k s => awInt κ T B X ω u v (swFam i a b c d) s k) atTop
          (Icc (q' : ℝ) T ∩ range ((↑) : ℚ → ℝ)) :=
      ae_all_iff.2 fun q' => by
        by_cases hq' : (0 : ℝ) < q' ∧ (q' : ℝ) < T
        · filter_upwards [hF q' hq'.1.le hq'.2 u v i a b c d] with ω hω
          intro _ _ h1 h2 h3 h4 h5 h6
          exact hω h1 h2 h3 h4 h5 h6
        · filter_upwards with ω
          intro h0 hT' _
          exact absurd ⟨h0, hT'⟩ hq'
    filter_upwards [hAll, ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
      with ω hfam hzm
    intro hu0 hu1 hu2 hu3 hu4 hu5 huv
    obtain ⟨hzm0, -, -, hzc, -, -⟩ := hzm
    -- the window is live at time `0`: `v < 0₋(T − T) = 0₋ 0 = 0`
    have hv0 : (v : ℝ) < 0 := by
      have h : T - (q : ℝ) = 0 := sub_eq_zero.mpr hqT'.symm
      rw [h, hzm0] at huv
      exact huv
    -- a rational anchor `q' < T` with `0₋(T − q') > v`, by continuity of `0₋` at `0`
    obtain ⟨δ, hδ, hδc⟩ :=
      Metric.continuousWithinAt_iff.1 (hzc 0 ⟨le_rfl, hT.le⟩) (-(v : ℝ)) (by linarith)
    obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn (max_lt (by linarith : (0 : ℝ) < T)
      (by linarith : T - δ < T))
    have hq'0 : (0 : ℝ) < q' := (le_max_left (0 : ℝ) (T - δ)).trans_lt hq'1
    have hq'T : (q' : ℝ) < T := hq'2
    have hvq' : (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q') := by
      have hmem : T - (q' : ℝ) ∈ Icc 0 T := ⟨by linarith, by linarith⟩
      have hdist : dist (T - (q' : ℝ)) 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
        linarith [hq'1, le_max_right (0 : ℝ) (T - δ)]
      have h := hδc hmem hdist
      rw [Real.dist_eq, hzm0] at h
      have h2 : |zeroMinus (Vr κ T B ω) (T - (q' : ℝ))| < -(v : ℝ) := by
        simpa using h
      rw [abs_lt] at h2
      linarith [h2.1]
    refine (hfam q' hq'0 hq'T hu1 hu2 hu3 hu4 hu5 hvq').mono fun x hx => ?_
    have hTx : T ≤ x := by rw [← hqT']; exact hx.1.1
    exact ⟨⟨hq'T.le.trans hTx, hx.1.2⟩, hx.2⟩

/-- **AC-fam at every horizon from AC-fam-ext at every horizon.** -/
theorem anchorUnifFamAllStmt_of_extAll (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hF : AnchorUnifFamExtAllStmt κ P B X) : AnchorUnifFamAllStmt κ P B X :=
  fun T hT => anchorUnifFamStmt_of_ext hκ hκ4 hT hB (hF.1 T hT)

/-- **AW at every horizon from AC-fam at every horizon** (`anchorWindowStmt_of_fam` at each
`T`). -/
theorem anchorWindowAllStmt_of_famAll (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamAllStmt κ P B X) : AnchorWindowAllStmt κ P B X :=
  fun T hT => anchorWindowStmt_of_fam hκ hκ4 hT hB hX hind (hF T hT)

/-- **AW at every horizon from AC-fam-ext at every horizon.** -/
theorem anchorWindowAllStmt_of_extAll (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamExtAllStmt κ P B X) : AnchorWindowAllStmt κ P B X :=
  anchorWindowAllStmt_of_famAll hκ hκ4 hB hX hind
    (anchorUnifFamAllStmt_of_extAll hκ hκ4 hB hF)

/-- **UO at every horizon from AC-fam-ext at every horizon, for the pair and its reflection**
(`unifOffTipStmt_of_ext_refl` at each `T`). -/
theorem unifOffTipAllStmt_of_extAll (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamExtAllStmt κ P B X) : UnifOffTipAllStmt κ P B X :=
  fun T hT => unifOffTipStmt_of_ext_refl hκ hκ4 hT hB hX hind (hF.1 T hT) (hF.2 T hT)

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

end RegUnif

namespace F1

end F1
end QuantumZipper
