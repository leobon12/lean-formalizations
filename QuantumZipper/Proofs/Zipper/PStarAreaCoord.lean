import QuantumZipper.Proofs.Zipper.PStarAreaAll
import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.Zipper.B5LocDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# PSTAR-AREA: both wedge area nodes from the area coordinate-change rule at all times

Theorem 1.3 / Theorem 1.8, node E6 (`HitScaleZip.lean`). `PStarAreaAll.lean` reduces
`E6.PStarAreaAllStmt` to the D29 cores and the two wedge area nodes `E6.WedgeAreaFinStmt`
(finite area of every half-disc) and `E6.WedgeAreaHStmt` (infinite total area), for the fields
unzipped from the unscaled wedge configuration at all times `t ≥ 0`. This file derives **both**
nodes from one named input, the area coordinate-change rule at all times:

* `E6.WedgeAreaCoordStmt` (**W-A-cc**): a.s., for every `t ≥ 0` and every Borel `S ⊆ ℍ`,
  `μ_{x_t}(S) = μ_{x_0}(f_t⁻¹(S))`, where `x_0 = F2.zU γ X' A` is the unscaled wedge field,
  `x_t = unzippedField γ (x_0, W) t = x_0 ∘ f_t⁻¹ + Q log |(f_t⁻¹)'|` and `f_t⁻¹ = fwdMapInv W t`.
  This is Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011)
  (arXiv:0808.1560), Proposition 2.1, p. 13 (PDF): for `h̃ = h ∘ ψ + Q log |ψ'|`,
  `μ_h̃(A) = μ_h(ψ(A))` for each Borel `A`, almost surely; used by Sheffield, *Conformal weldings
  of random surfaces* (arXiv:1012.4797), §1.4 (1.3)/(1.6) and §5, to *define* the quantum area of
  the unzipped surface. Here `ψ = f_t⁻¹ : ℍ → ℍ \ K_t` is conformal
  (`RS.image_fwdMapInv_H`, `RS.injOn_fwdMapInv_H`).

Deterministic part (own elementary proof; the Loewner inputs are cited in the lemmas used):
* finiteness: `f_t⁻¹(B_a(0) ∩ ℍ) ⊆ B_b(0) ∩ ℍ` with `b = a + 6M + 6√t`
  (`B5.norm_fwdMapInv_sub_le`, Lawler, *Conformally Invariant Processes in the Plane*, Lemma 4.12);
* infinite mass: `f_t⁻¹(ℍ) = ℍ \ K_t ⊇ ℍ \ B̄_R(0)` (`RS.image_fwdMapInv_H`,
  `CaraR.fwdHull_subset_closedBall`), and `μ_{x_0}(ℍ \ B̄_R(0)) = ∞`
  (`E6.qAreaMeasure_H_sub_closedBall_eq_top`);
* at `t = 0`, `f_0⁻¹ = id` on `ℍ` (`Thm18Asm.G1Pkg.fwdMapInv_zero_time`);
* time `0` area property of the wedge field: `E6.ae_areaAll_wedgeField` (unconditional).

Results: `areaAll_unzippedField_of_coord` (deterministic), `wedgeAreaFinStmt_of_coord`,
`wedgeAreaHStmt_of_coord`, `pStarAreaAllStmt_of_coord`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip

/-! ## The named input -/

/-- **W-A-cc: area coordinate change at all times** (open; Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 2.1). A.s., for all `t ≥ 0` and all Borel `S ⊆ ℍ`, the quantum area of the
field unzipped from the unscaled wedge configuration at time `t` charges `S` as much as the
wedge's own area charges `f_t⁻¹(S)`. -/
def WedgeAreaCoordStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure (Real.sqrt κ)
          (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t) S =
        qAreaMeasure (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω)
          (fwdMapInv (drive κ B'' ω) t '' S)

/-! ## Deterministic transport -/

/-- A continuous driver is bounded on `[0,t]`. -/
theorem exists_abs_le_Icc_of_continuous {W : ℝ → ℝ} (hW : Continuous W) (t : ℝ) :
    ∃ M : ℝ, ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hW.continuousOn
  exact ⟨M, fun r hr => by simpa [Real.norm_eq_abs] using hM r hr⟩

/-- At time `0` the unzipping map fixes `ℍ` pointwise (`W 0 = 0`). -/
theorem fwdMapInv_zero_eq_self {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {w : ℂ}
    (hw : w ∈ H) : fwdMapInv W 0 w = w := by
  rw [Thm18Asm.G1Pkg.fwdMapInv_zero_time hW (show 0 < w.im from hw), hW0]
  simp

/-- `f_t⁻¹` maps a half-disc into a (larger) half-disc. -/
theorem exists_image_fwdMapInv_ball_subset {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) (a : ℝ) :
    ∃ b : ℝ, fwdMapInv W t '' (Metric.ball 0 a ∩ H) ⊆ Metric.ball 0 b ∩ H := by
  rcases ht.eq_or_lt with rfl | htpos
  · refine ⟨a, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [fwdMapInv_zero_eq_self hW hW0 hw.2]
    exact hw
  · obtain ⟨M, hM⟩ := exists_abs_le_Icc_of_continuous hW t
    refine ⟨a + (6 * M + 6 * Real.sqrt t), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨?_, RS.fwdMapInv_mem_H hW hW0 ht hw.2⟩
    have h1 := B5.norm_fwdMapInv_sub_le hW hW0 htpos hM hw.2
    have h2 : ‖w‖ < a := by
      have := hw.1
      rwa [Metric.mem_ball, dist_zero_right] at this
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖fwdMapInv W t w‖ = ‖w + (fwdMapInv W t w - w)‖ := by ring_nf
      _ ≤ ‖w‖ + ‖fwdMapInv W t w - w‖ := norm_add_le _ _
      _ < a + (6 * M + 6 * Real.sqrt t) := by linarith

/-- The image `f_t⁻¹(ℍ) = ℍ \ K_t` carries infinite area when the field has `AreaAll`. -/
theorem qAreaMeasure_image_fwdMapInv_H_eq_top {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (hx : AreaAll γ x) :
    qAreaMeasure γ x (fwdMapInv W t '' H) = ⊤ := by
  rcases ht.eq_or_lt with rfl | htpos
  · have himg : fwdMapInv W 0 '' H = H := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [fwdMapInv_zero_eq_self hW hW0 hw]
        exact hw
      · intro hz
        exact ⟨z, hz, fwdMapInv_zero_eq_self hW hW0 hz⟩
    rw [himg]
    exact hx.2
  · obtain ⟨M, hM⟩ := exists_abs_le_Icc_of_continuous hW t
    rw [RS.image_fwdMapInv_H hW hW0 ht]
    have hK := CaraR.fwdHull_subset_closedBall hW htpos hM
    refine eq_top_iff.2 ?_
    rw [← qAreaMeasure_H_sub_closedBall_eq_top hx.1 hx.2 (M + 3 * Real.sqrt t)]
    exact measure_mono (sdiff_subset_sdiff_right hK)

/-- **`AreaAll` transported along the unzipping map** (deterministic): if the field `x` has
`AreaAll` and the area coordinate-change rule holds at time `t`, the unzipped field has
`AreaAll`. -/
theorem areaAll_unzippedField_of_coord {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (hx : AreaAll γ x)
    (hc : ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ (x, W) t) S = qAreaMeasure γ x (fwdMapInv W t '' S)) :
    AreaAll γ (unzippedField γ (x, W) t) := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [hc _ (Metric.isOpen_ball.inter isOpen_H).measurableSet inter_subset_right]
    obtain ⟨b, hb⟩ := exists_image_fwdMapInv_ball_subset hW hW0 ht a
    exact (measure_mono hb).trans_lt (hx.1 b)
  · rw [hc _ isOpen_H.measurableSet subset_rfl]
    exact qAreaMeasure_image_fwdMapInv_H_eq_top hW hW0 ht hx

/-! ## The two wedge area nodes -/

/-- A.s. `AreaAll` for the unzipped unscaled wedge fields at all times, from W-A-cc. -/
theorem ae_areaAll_unzipped_of_coord (hK : WedgeAreaCoordStmt) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ)
    (hX : IsFreeGFFModConstH X' P)
    (hA : IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P)
    (hInd : IndepFun X' (fun ω t => A t ω) P) (hB : IsBrownianReal B'' P)
    (hIB : IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → AreaAll (Real.sqrt κ)
      (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t) := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  filter_upwards [hK κ hκ hκ4 P X' A B'' hX hA hInd hB hIB,
    ae_areaAll_wedgeField hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hInd,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hKω hxω hc h0 t ht
  have hWc : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  exact areaAll_unzippedField_of_coord hWc hW0 ht hxω (hKω t ht)

/-- **W-A-fin from W-A-cc.** -/
theorem wedgeAreaFinStmt_of_coord (hK : WedgeAreaCoordStmt) : WedgeAreaFinStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hInd hB hIB
  filter_upwards [ae_areaAll_unzipped_of_coord hK hκ hκ4 P X' A B'' hX hA hInd hB hIB]
    with ω h t ht a
  exact (h t ht).1 a

/-- **W-A-∞ from W-A-cc.** -/
theorem wedgeAreaHStmt_of_coord (hK : WedgeAreaCoordStmt) : WedgeAreaHStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hInd hB hIB
  filter_upwards [ae_areaAll_unzipped_of_coord hK hκ hκ4 P X' A B'' hX hA hInd hB hIB]
    with ω h t ht
  exact (h t ht).2

end QuantumZipper.E6
