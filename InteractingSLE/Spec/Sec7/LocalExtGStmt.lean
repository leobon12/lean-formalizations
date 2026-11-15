/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtGKernel
import InteractingSLE.Spec.Sec7.LocalExtFStmt

/-!
# Theorem 1.2's restart input from Aux. lemma 54 and the restarted stopped seed coupling

Packet PROVE-LOCEXT-G. PROVE-LOCEXT-E reduced the restart side of Theorem 1.2 to one per-cell input,
`RestartTwoSeedExtensionStatement κ` (`LocalExtEMain.lean`). PROVE-LOCEXT-F states Aux. lemma 54 once for a **stopped seed
coupling** (`IsStoppedSeedCoupling`, `StoppedSeedExtensionStatement`, `LocalExtFStmt.lean`) and derives the time-`0` input
from it. This file does the same for the restart:

* `recode` for a **random word**: `recodeShift` is continuous on `ℍ` for every word (`continuousOn_recodeShift'`), so
  `recode_apply'` holds without hypotheses, and `(x, h) ↦ recode κ x ρ r h` is jointly measurable in the word and the field
  (`measurable_recode_word`);
* `restartRecode κ ρL ρR r (h, y)`: the recoded restarted field `h₀ = recode_{c}(h ∘ f⁻¹ − χ arg (f⁻¹)′)` with chart and
  current positions `c` read from the recorded history `y` — a measurable function of `(h, y)` (`measurable_restartRecode`);
* `RestartSeedCouplingStatement κ` (**named input: Aux. lemma 53 with steps 3–5 of Aux. lemma 55 at a restart**):
  conditionally on a cell event `D ∈ 𝓓_T`, a measure `Q` equivalent to `P|_D` carries a stopped seed coupling (LOCEXT-F's
  `IsStoppedSeedCoupling`) of a deterministic ordered word with the pattern's seed sums, whose field is a measurable
  function of `(h, 𝒳_T)` and whose two-seed history determines (measurably, with `(h, 𝒳_T)`) the two-seed history of the
  path restarted at `T` through its local stop;
* **`restartTwoSeedExtensionStatement_of_restartSeedCoupling`**: `StoppedSeedExtensionStatement κ` (Aux. lemma 54,
  LOCEXT-F) and `RestartSeedCouplingStatement κ` give LOCEXT-E's `RestartTwoSeedExtensionStatement κ`;
* **`exists_measurable_lifetime_trace_eq_comp_field_of_restartSeedCoupling`**: the conclusion of the frozen Theorem 1.2
  for every `κ > 0` from the two-seed graph input, Aux. lemma 54 and the named restart input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec5.Markov Determination

/-! ### The recoding for a random word -/

section RecodeWord

variable {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)

/-- `qExt` with the distant marks selected by an `if` (a jointly measurable form in the word). -/
theorem qExt_eq_sum_ite (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (z : ℂ) :
    qExt κ xL xR ρL ρR z = -(1 / Real.sqrt κ) *
      (∑ i, (if xL i ≠ 0 then ρL i * Complex.arg (z - xL i) else 0) +
        ∑ i, (if xR i ≠ 0 then ρR i * Complex.arg ((xR i : ℂ) - z) else 0)) := by
  simp only [qExt, distSetL, distSetR, Finset.sum_filter]

/-- **The recoding shift is continuous on `ℍ` for every word** (no ordering or radius hypothesis). -/
theorem continuousOn_recodeShift' (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    ContinuousOn (recodeShift κ xL xR ρL ρR r) H := by
  have hq : ContinuousOn (qExt κ xL xR ρL ρR) H := continuousOn_qExt
  have hc : Continuous (cutoffFn (6 * r) (7 * r)) := contDiff_cutoffFn.continuous (n := 0)
  exact (hc.continuousOn.mul hq).sub hq

/-- The recoded field tested against `φ`, for every word. -/
theorem recode_apply' (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (T : LQGMetric.DistOn upperHalfPlaneOpens)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    recode κ xL xR ρL ρR r T φ = T φ + ∫ z, φ z * recodeShift κ xL xR ρL ρR r z := by
  rw [recode, show (T + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens
      (recodeShift κ xL xR ρL ρR r)) φ = T φ + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens
      (recodeShift κ xL xR ρL ρR r) φ from rfl,
    SupercriticalConformalCovariance.GM24.smoothDist_apply (continuousOn_recodeShift' κ ρL ρR r xL xR)]

/-- The recoding shift is jointly measurable in the word and the point. -/
theorem measurable_recodeShift_word :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => recodeShift κ p.1.1 p.1.2 ρL ρR r p.2 := by
  have hq : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => qExt κ p.1.1 p.1.2 ρL ρR p.2 := by
    simp_rw [qExt_eq_sum_ite]
    refine measurable_const.mul (Measurable.add (Finset.measurable_sum _ fun i _ => ?_)
      (Finset.measurable_sum _ fun j _ => ?_))
    · have hxi : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => p.1.1 i :=
        (measurable_pi_apply i).comp measurable_fst.fst
      refine Measurable.ite ?_ (measurable_const.mul (Complex.measurable_arg.comp
        (measurable_snd.sub (Complex.measurable_ofReal.comp hxi)))) measurable_const
      exact (measurableSet_eq_fun hxi measurable_const).compl
    · have hxj : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => p.1.2 j :=
        (measurable_pi_apply j).comp measurable_fst.snd
      refine Measurable.ite ?_ (measurable_const.mul (Complex.measurable_arg.comp
        ((Complex.measurable_ofReal.comp hxj).sub measurable_snd))) measurable_const
      exact (measurableSet_eq_fun hxj measurable_const).compl
  have hc : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => cutoffFn (6 * r) (7 * r) p.2 :=
    (contDiff_cutoffFn.continuous (n := 0)).measurable.comp measurable_snd
  exact (hc.mul hq).sub hq

/-- **The recoded field is a jointly measurable function of the word and the field.** -/
theorem measurable_recode_word :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × LQGMetric.DistOn upperHalfPlaneOpens =>
      recode κ p.1.1 p.1.2 ρL ρR r p.2 := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  simp_rw [recode_apply']
  have hu : Measurable (Function.uncurry fun (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (z : ℂ) =>
      φ z * recodeShift κ x.1 x.2 ρL ρR r z) :=
    ((φ.continuous.measurable).comp measurable_snd).mul (measurable_recodeShift_word κ ρL ρR r)
  have hi : Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => ∫ z, φ z * recodeShift κ x.1 x.2 ρL ρR r z :=
    (hu.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  exact ((LQGMetric.measurable_distOn_apply φ).comp measurable_snd).add (hi.comp measurable_fst)

/-- **The recoded restarted field read from a recorded history**: `h₀ = recode_c(h ∘ f⁻¹ − χ arg (f⁻¹)′)`, with the
chart `f` (`histChart`) and the current positions `c` (`posL`, `posR` of `histState`) read from the history `y`. -/
def restartRecode (p : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR) :
    LQGMetric.DistOn upperHalfPlaneOpens :=
  recode κ (posL (histState p.2)) (posR (histState p.2)) ρL ρR r (restartField κ p)

theorem measurable_restartRecode : Measurable (restartRecode (nL := nL) (nR := nR) κ ρL ρR r) := by
  have hpos : Measurable fun p : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR =>
      (posL (histState p.2), posR (histState p.2)) :=
    (measurable_posL.comp (measurable_histState.comp measurable_snd)).prodMk
      (measurable_posR.comp (measurable_histState.comp measurable_snd))
  have h := (measurable_recode_word κ ρL ρR r).comp (hpos.prodMk (measurable_restartField κ))
  exact h

end RecodeWord

/-! ### The restarted stopped seed coupling and the restart input -/

section Main

variable {κ : ℝ}

/-- **Named input: Aux. lemma 53 with steps 3–5 of Aux. lemma 55 at a restart** (specification pp. 245–251: "Aux. lemma
53 justifies applying the preceding local comparison conditionally after every own-filtration stopping time strictly before
the threshold"). Same data as `RestartTwoSeedExtensionStatement`: a coupling of an ordered word, a finite stopping time `T`
of its driving filtration `𝓓`, a good event `G`, an admissible seed pattern `(S_L, S_R)` and a radius `r`, an event
`D ∈ 𝓓_T` of positive probability on which `T < ζ`, the pattern at `T` is `(S_L, S_R)` and `r` is a seed radius of the
current positions, and a measurable `K` equal to `𝒳_T` almost surely on `D`. Conclusion: a probability measure `Q`
equivalent to `P|_D` ((HL3) with the current positions as `𝓓_T`-measurable data) carrying a **stopped seed coupling**
(PROVE-LOCEXT-F's `IsStoppedSeedCoupling`) of some deterministic ordered word with the seed sums `∑_{S_L} ρL`, `∑_{S_R} ρR`
and radius `r`, whose field is a measurable function `F₀` of `(h, K)` ((HL8) at the restart: e.g. `restartRecode`), and
whose stopped two-seed history recovers, through a measurable `g` and `(h, K)`, the two-seed history of the path
restarted at `T` stopped at its capped local stop of radius `r`.

Under `Q`, the restarted driver through its local stop is the driver of the seed-weight word (Girsanov with the current
positions as data), the recoded restarted field has the two-seed GFF law, kernel and locality at every stop before the
local stop (the conditional Gaussian clause after the restart is `isCouplingCharFun_restart`). -/
def RestartSeedCouplingStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
      ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (T : Ω → ℝ≥0)
        (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) (G : Set Ω),
        MeasurableSet G → P Gᶜ = 0 → (∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) →
      ∀ (SL : Finset (Fin nL)) (SR : Finset (Fin nR)) (r : ℝ),
        -2 < ∑ i ∈ SL, ρL i → -2 < ∑ j ∈ SR, ρR j →
      ∀ D : Set Ω, MeasurableSet[hT.measurableSpace] D → P D ≠ 0 →
        (∀ ω ∈ D, ω ∈ G ∧ (T ω : ℝ≥0∞) < ζ ω ∧ (∀ i, VL i (T ω) ω = W (T ω) ω ↔ i ∈ SL) ∧
          (∀ j, VR j (T ω) ω = W (T ω) ω ↔ j ∈ SR) ∧ IsSeedRadius (curL VL W T ω) (curR VR W T ω) r) →
      ∀ K : Ω → DrivingHist nL nR, Measurable K →
        (∀ᵐ ω ∂P, ω ∈ D →
          K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) →
        ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P.restrict D ∧ P.restrict D ≪ Q ∧
          ∃ (mL mR : ℕ) (yL : Fin mL → ℝ) (yR : Fin mR → ℝ) (σL : Fin mL → ℝ) (σR : Fin mR → ℝ),
            IsOrderedForceWord yL yR ∧ seedSumL yL σL = ∑ i ∈ SL, ρL i ∧ seedSumR yR σR = ∑ j ∈ SR, ρR j ∧
          ∃ (W₀ : ℝ≥0 → Ω → ℝ) (VL₀ : Fin mL → ℝ≥0 → Ω → ℝ) (VR₀ : Fin mR → ℝ≥0 → Ω → ℝ)
            (S₀ : Ω → WithTop ℝ≥0)
            (F₀ : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR → LQGMetric.DistOn upperHalfPlaneOpens)
            (g : (LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR) × TwoSeedHist → TwoSeedHist),
            Measurable F₀ ∧ Measurable g ∧
            IsStoppedSeedCoupling κ yL yR σL σR r Q W₀ VL₀ VR₀ S₀ (fun ω => F₀ (h ω, K ω)) ∧
            ∀ᵐ ω ∂Q, twoSeedProj (curL VL W T ω) (curR VR W T ω)
                (stoppedHistory (completedState (restartDrv W T) (fun i => restartMark (VL i) W T)
                  (fun j => restartMark (VR j) W T) (restartLife ζ T))
                  (capStop r G (restartLife ζ T) (restartDrv W T)) ω) =
              g ((h ω, K ω), twoSeedProj yL yR (stoppedHistory (drivingState W₀ VL₀ VR₀) S₀ ω))

/-- **The restart input from Aux. lemma 54 and the restarted stopped seed coupling**: PROVE-LOCEXT-F's
`StoppedSeedExtensionStatement κ` applied to the stopped seed coupling of `RestartSeedCouplingStatement κ` gives an
extended reference pair over `F₀(h, K)`, hence over `(h, K)` (`HasReferenceExtension.comp`), recovering the restarted
two-seed history (`HasReferenceExtension.of_ae_eq` with `g`). -/
theorem restartTwoSeedExtensionStatement_of_restartSeedCoupling (hext : StoppedSeedExtensionStatement.{u} κ)
    (hrs : RestartSeedCouplingStatement.{u} κ) : RestartTwoSeedExtensionStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hC hX T hT G hGm hG0 hG SL SR r hSL hSR D hD hPD hDp K hKm hK
  obtain ⟨Q, hQ, hQD, hDQ, mL, mR, yL, yR, σL, σR, hFy, hsL, hsR, W₀, VL₀, VR₀, S₀, F₀, g, hF₀, hg, hstop, hrec⟩ :=
    hrs xL xR ρL ρR hF P 𝓕 W VL VR B ζ h hC hX T hT G hGm hG0 hG SL SR r hSL hSR D hD hPD hDp K hKm hK
  have hr : 0 < r := by
    obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hPD
    exact (hDp ω hω).2.2.2.2.1
  have hL : -2 < seedSumL yL σL := hsL ▸ hSL
  have hR : -2 < seedSumR yR σR := hsR ▸ hSR
  have hmain := hext yL yR σL σR r hFy hr hL hR Q W₀ VL₀ VR₀ S₀ _ hstop
  rw [hsL, hsR] at hmain
  exact ⟨Q, hQ, hQD, hDQ, (HasReferenceExtension.comp hF₀ hmain).of_ae_eq g hg hrec⟩

/-- **Theorem 1.2's conclusion from Aux. lemma 54 and the restarted stopped seed coupling**: for every `κ > 0`, the
two-seed graph input, `StoppedSeedExtensionStatement κ` (LOCEXT-F) and `RestartSeedCouplingStatement κ` give exactly the
conclusion of the frozen Theorem 1.2 for every coupling of an ordered force word. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_restartSeedCoupling {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hκ : 0 < κ)
    (h2 : LP.TwoSeedGraphInput.{u} κ) (hext : StoppedSeedExtensionStatement.{u} κ)
    (hrs : RestartSeedCouplingStatement.{u} κ) (hF : IsOrderedForceWord xL xR) [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  exists_measurable_lifetime_trace_eq_comp_field_of_restartTwoSeed hκ h2
    (restartTwoSeedExtensionStatement_of_restartSeedCoupling hext hrs) hF hC

/-- LP11's Lemma 7.5 determination statement from the Proposition 7.3 inputs, Aux. lemma 54 and the restart input. -/
theorem lemma75DeterminationStatement_of_restartSeedCoupling
    (h73d : Prop73DeterminationStatement.{u}) (h73t : Sec7.Prop73TraceStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedSeedExtensionStatement.{u} κ)
    (hrs : ∀ κ : ℝ, 0 < κ → κ < 4 → RestartSeedCouplingStatement.{u} κ) :
    LP.Lemma75DeterminationStatement.{u} :=
  lemma75DeterminationStatement_of_restartTwoSeed h73d h73t fun κ hκ hκ4 =>
    restartTwoSeedExtensionStatement_of_restartSeedCoupling (hext κ hκ hκ4) (hrs κ hκ hκ4)

end Main

end LocalExt

end InteractingSLE
