import HigherDimLQGMetric.DGZ.TightInternal
import HigherDimLQGMetric.DGZ.TightDistInf

/-!
# DGZ §6 (packet L5a): the export shapes reached up to Lemma 6.7

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemmas 6.2, 6.7 and (6.5); planning audit
`planning/audits/MA7-ref2-sections-4-6.md`, §4.2 (export table: `HolderTightShape` comes from
"Lemma 6.2, Prop 6.3, (6.5)", `DistInfShape` from "Lemma 6.7, (6.5)") and §5 row L5a; blueprint
Part C, Theorem `r2:thm:12` (a), (c). The shapes are the orchestrator's verbatim copies in
`HigherDimLQGMetric/DGZ/Interfaces.lean`.

* `distInf_aq` ([2] Lemma 6.7, normalized by `a^{(q)}_n`): the case `b = 1`, `G = 0` of
  `distInf_aq_pert`.
* **`distInfShape_of_cor52 : Cor52Shape d κ ξ Q → DistInfShape d κ ξ Q`** — complete: since
  `λ_n = a^{(1/2)}_n ≤ a^{(q)}_n` for `q ≥ 1/2`, the `λ_n`-normalized statement follows from
  `distInf_aq` with `T' := max T 0` and `N := 0`.
* `LambdaComparableShape` (DGZ (6.5), lower half; blueprint Prop `r2:prop:64`(b)) and
  **`holderTightShape_of_comparable : Cor52Shape → LambdaComparableShape → HolderTightShape`**.

**Why `HolderTightShape` needs (6.5) (reported correction of the packet target).**
`HolderTightShape` is normalized by the median `λ_n = a^{(1/2)}_n`, while Lemmas 6.1/6.2 bound `D_n`
by `M a^{(q)}_n ‖x - y‖^β` only for `q` close to `1` (`q ≥ q₁(β) > c₄(η)`, the percolation threshold
of Lemma 4.2). Passing from `a^{(q)}_n` to `λ_n` requires `a^{(q)}_n ≤ C λ_n`, i.e. a lower bound
`P[D_n(0, e₁; B₂(0)) ≤ δ a^{(q)}_n] ≤ 1/2` — the non-degeneracy (6.5), which [2] proves from Prop
6.4 via the zero-one law (packet L5b). It does not follow from `Cor52Shape` and the upper Hölder
bounds: these constrain only upper tails of `D_n`, and `Cor52Shape` with `k = 0` compares `a^{(q)}_n
≤ C a^{(q')}_n` only for `q < q'`. So `Cor52Shape → HolderTightShape` is proved here in the
corrected form with the extra hypothesis `LambdaComparableShape` (an L5b target), and
`holderTightAQ` (TightInternal) is the hypothesis-free `a^{(q)}`-normalized version.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ### DGZ Lemma 6.7, unperturbed -/

/-- **DGZ Lemma 6.7** (distance to infinity, normalized by `a^{(q)}_n`; blueprint `r2:lem:67` with
`b = 1`): under `Cor52Shape` and `DGZHyp` there is `q₂ ∈ (0, 1)` such that for `q ∈ [q₂, 1)`,
`r > 0`, `T` and `θ > 0` there is `R > r` with
`P[D_n(across B_R(0) \ B_r(0)) ≤ T a^{(q)}_n] ≤ θ` for every dyadic realization and every `n`. -/
theorem distInf_aq {κ : Rd d → ℝ} {ξ Q : ℝ} (hC52 : Cor52Shape d κ ξ Q) (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ r T θ : ℝ, 0 < r → 0 < θ → ∃ R : ℝ, r < R ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
            P {ω | acrossDist ξ (fun z => H n z ω) 0 R r ≤ T * aQ P H ξ n q} ≤
              ENNReal.ofReal θ := by
  obtain ⟨q₂, hq₂0, hq₂1, hpert⟩ := distInf_aq_pert hC52 h
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 r T θ hr hθ => ?_⟩
  obtain ⟨R, hrR, hR⟩ := hpert q hq₂q hq1 r T θ hr hθ
  refine ⟨R, hrR, fun Ω _ P W H hH n => ?_⟩
  have hb := hR Ω P W H hH 1 le_rfl one_le_two (fun _ _ => 0)
    (isBandVersion_zero_self h.kernel hH.whiteNoise one_pos) n
  simpa only [add_zero] using hb

/-! ### `DistInfShape` -/

/-- **`DistInfShape` from DGZ Cor 5.2** (blueprint Theorem `r2:thm:12`(c)): the `λ_n`-normalized
distance-to-infinity export follows from `distInf_aq` at any level `q ≥ 1/2`, because
`λ_n = a^{(1/2)}_n ≤ a^{(q)}_n`. -/
theorem distInfShape_of_cor52 {κ : Rd d → ℝ} {ξ Q : ℝ} (hC52 : Cor52Shape d κ ξ Q) :
    DistInfShape d κ ξ Q := by
  intro h r T θ hr hθ
  have hd0 : 0 < d := by have := h.dim; omega
  obtain ⟨q₂, hq₂0, hq₂1, hdist⟩ := distInf_aq hC52 h
  have hhalf0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hhalf1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  set q : ℝ≥0∞ := max q₂ 2⁻¹ with hq
  have hq1 : q < 1 := max_lt hq₂1 hhalf1
  obtain ⟨R, hrR, hR⟩ := hdist q (le_max_left _ _) hq1 r (max T 0) θ hr hθ
  refine ⟨R, hrR, 0, fun Ω _ P W H hH n _ => le_trans (measure_mono ?_) (hR Ω P W H hH n)⟩
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  have hlam : 0 < aQ P H ξ n 2⁻¹ := tight_aQ_pos hd0 hH ξ n hhalf0 hhalf1
  have hlamq : aQ P H ξ n 2⁻¹ ≤ aQ P H ξ n q :=
    tight_aQ_mono hH ξ n hhalf0 (le_max_right _ _) hq1
  have h1 : T * aQ P H ξ n 2⁻¹ ≤ max T 0 * aQ P H ξ n 2⁻¹ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le
  have h2 : max T 0 * aQ P H ξ n 2⁻¹ ≤ max T 0 * aQ P H ξ n q :=
    mul_le_mul_of_nonneg_left hlamq (le_max_right _ _)
  linarith

/-! ### `HolderTightShape` under the comparability (6.5) -/

/-- **DGZ (6.5), lower half** (blueprint Prop `r2:prop:64`(b), a target of packet L5b): for every
`q < 1`, `c a^{(q)}_n ≤ λ_n` for all `n` and all dyadic realizations, with `c > 0`. -/
def LambdaComparableShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ q : ℝ≥0∞, q < 1 → ∃ c : ℝ, 0 < c ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H → ∀ n : ℕ, c * aQ P H ξ n q ≤ aQ P H ξ n 2⁻¹

/-- **`HolderTightShape` from DGZ Cor 5.2 and (6.5)** (blueprint Theorem `r2:thm:12`(a)):
Lemma 6.2 normalized by `a^{(q₁)}_n` (`holderTightAQ`) and `a^{(q₁)}_n ≤ λ_n/c`. -/
theorem holderTightShape_of_comparable {κ : Rd d → ℝ} {ξ Q : ℝ} (hC52 : Cor52Shape d κ ξ Q)
    (hcomp : LambdaComparableShape d κ ξ Q) : HolderTightShape d κ ξ Q := by
  intro h β hβ0 hβ U V hU hV hVc hVb hVU θ hθ
  obtain ⟨q₁, -, hq₁, hAQ⟩ := holderTightAQ hC52 h hβ0 hβ
  obtain ⟨M, hM, hMb⟩ := hAQ q₁ le_rfl hq₁ U V hU hV hVc hVb hVU θ hθ
  obtain ⟨c, hc, hcb⟩ := hcomp h q₁ hq₁
  refine ⟨M / c, fun Ω _ P W H hH n => le_trans (measure_mono ?_) (hMb Ω P W H hH n)⟩
  rintro ω ⟨x, hx, y, hy, hlt⟩
  refine ⟨x, hx, y, hy, lt_of_le_of_lt ?_ hlt⟩
  have h1 := hcb Ω P W H hH n
  have h2 : M * aQ P H ξ n q₁ ≤ M / c * aQ P H ξ n 2⁻¹ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) _)

end DGZ

end HigherDimLQGMetric
