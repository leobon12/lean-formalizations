import QuantumZipper.Proofs.Thm18.G3CvG0
import QuantumZipper.Proofs.LQG.CoordChangeSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, item 1: regularized evaluation of the free field at pulled-back circles

For a local conformal map `Φ` at a real point `b` (`PullData`, G3CvIso.lean) and a folded circle
`fc(c, r)` with `c ∈ Hbar`, `‖c − b‖ + r ≤ ρ` (interior or boundary centre), almost surely the
regularized evaluation of a free field `W` at `Φ_* fc(c, r)` equals its raw coordinate
(`ae_evalReg_pullCircle`); hence `coordChange (W ω) Φ Q` at `fc(c, r)` is the raw pairing
`W ω (Φ_* fc(c,r))` plus the deterministic `Q ∫ log |Φ'| d fc(c,r)` (`ae_coordChange_pullCircle`).
This is exactness at fixed maps: the maps do not depend on the field.

Route: the proof of `CoordChange.Data.ae_evalReg_pc` (CoordChangeSmooth.lean; pushed boundary
semicircles), with the smoothness data `Data` replaced by the bi-Lipschitz bound of `PullData`
and arbitrary centres `c ∈ Hbar`: `∫ avgReg_k d(Φ_*fc) = W(Φ_*fc ∗ circle_k)` a.s., the variance of
`W(Φ_*fc ∗ circle_k) − W(Φ_*fc)` is `O(2^{-k})` (`abs_kernelCov2_bind_le` with the `Lr` bound
`integral_Lr_pullCircle_bounds`), Borel–Cantelli. Own adaptation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Cv

open SmoothConv CircleFubini CoordChange

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

theorem ae_foldH_mem_disc {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcr : ‖c - b‖ + r ≤ ρ) :
    ∀ᵐ v ∂circleUnif c r, foldH v ∈ closedBall (b : ℂ) ρ ∩ Hbar := by
  filter_upwards [K3.ae_mem_sphere_circleUnif_k3 c hr] with v hv
  refine ⟨mem_closedBall_iff_norm.2 ?_, CircleFubini.foldH_mem_Hbar' v⟩
  have h1 := K3.norm_foldH_sub_foldH_le v c
  rw [mem_sphere_iff_norm.1 hv] at h1
  have h2 : ‖foldH c - b‖ = ‖c - b‖ := K3.norm_foldH_sub_ofReal b c
  calc ‖foldH v - b‖ = ‖(foldH v - foldH c) + (foldH c - b)‖ := by congr 1; ring
    _ ≤ ‖foldH v - foldH c‖ + ‖foldH c - b‖ := norm_add_le _ _
    _ ≤ ρ := by linarith

theorem foldedCircle_compl_null {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcr : ‖c - b‖ + r ≤ ρ) : foldedCircle c r (closedBall (b : ℂ) ρ ∩ Hbar)ᶜ = 0 := by
  have hm : MeasurableSet (closedBall (b : ℂ) ρ ∩ Hbar) :=
    isClosed_closedBall.measurableSet.inter isClosed_Hbar.measurableSet
  rw [foldedCircle, Measure.map_apply measurable_foldH hm.compl]
  exact ae_iff.1 (ae_foldH_mem_disc hr hcr)

instance isProbabilityMeasure_foldedCircle_g3cv2 (c : ℂ) (r : ℝ) :
    IsProbabilityMeasure (foldedCircle c r) := by
  rw [foldedCircle]
  exact (Measure.isProbabilityMeasure_map_iff measurable_foldH.aemeasurable).2 inferInstance

theorem isAdmissibleH_foldedCircle_g3cv2 (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsAdmissibleH (foldedCircle c r) := by
  refine admissible_of_bounds (R := ‖c‖ + r) ?_ (C := 2 * ENNReal.ofReal (potConst r))
    (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) (fun y => foldedCircle_pot_le hr c y)
  rw [foldedCircle, Measure.map_apply measurable_foldH (measurableSet_ballH _).compl]
  have hae := ae_iff.1 (K3.ae_mem_sphere_circleUnif_k3 c hr)
  refine measure_mono_null (fun v hv => ?_) hae
  intro hv'
  refine hv ⟨mem_closedBall_zero_iff.2 ?_, CircleFubini.foldH_mem_Hbar' v⟩
  have h1 : ‖v - c‖ = r := mem_sphere_iff_norm.1 hv'
  have h2 := K3.norm_foldH_sub_foldH_le v 0
  have h0 : foldH 0 = 0 := CircleFubini.foldH_of_mem' (by simp [Hbar])
  rw [h0, sub_zero, sub_zero] at h2
  calc ‖foldH v‖ ≤ ‖v‖ := h2
    _ = ‖(v - c) + c‖ := by congr 1; ring
    _ ≤ ‖v - c‖ + ‖c‖ := norm_add_le _ _
    _ = ‖c‖ + r := by rw [h1]; ring

/-- The pulled-back folded circle. -/
def pullCircle (Φ : ℂ → ℂ) (c : ℂ) (r : ℝ) : Measure ℂ := (foldedCircle c r).map Φ

theorem PullData.isAdmissibleH_pullCircle (hD : PullData Φ b r₀ ρ r₁ m M) {c : ℂ}
    {r : ℝ} (hr : 0 < r) (hcr : ‖c - b‖ + r ≤ ρ) : IsAdmissibleH (pullCircle Φ c r) :=
  hD.adm_map (isAdmissibleH_foldedCircle_g3cv2 c hr)
    (measure_mono_null (compl_subset_compl.2 inter_subset_left)
      (foldedCircle_compl_null hr hcr))

set_option maxHeartbeats 1000000 in
/-- **The `Lr` bound at pulled-back circles** (as `Data.integral_Lr_pc_bounds`). -/
theorem integral_Lr_pullCircle_bounds (hD : PullData Φ b r₀ ρ r₁ m M) {c : ℂ}
    {r : ℝ} (hr : 0 < r) (hcr : ‖c - b‖ + r ≤ ρ) {σ : ℝ} (hσ : 0 < σ) {x : ℂ} (hx : x ∈ Hbar) :
    0 ≤ ∫ w, Lr σ w x ∂(pullCircle Φ c r) ∧
      ∫ w, Lr σ w x ∂(pullCircle Φ c r) ≤ 16 * σ / (m * r) := by
  obtain ⟨hm, -, hbl⟩ := hD.bl
  have hgm : Measurable fun w => Lr σ w x :=
    (measurable_Lr hσ).comp (measurable_id.prodMk measurable_const)
  have hgm2 : Measurable fun y => Lr σ (Φ y) x := by
    have h := hgm.comp hD.conf.meas
    exact h
  have hcomp : ∫ w, Lr σ w x ∂(pullCircle Φ c r) =
      ∫ v, Lr σ (Φ (foldH v)) x ∂circleUnif c r := by
    rw [pullCircle, integral_map hD.conf.meas.aemeasurable hgm.aestronglyMeasurable, foldedCircle,
      integral_map measurable_foldH.aemeasurable hgm2.aestronglyMeasurable]
  rw [hcomp]
  set K' : Set ℂ := closedBall (b : ℂ) ρ ∩ Hbar with hK'
  have hK'c : IsCompact K' := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hbK : (b : ℂ) ∈ K' := ⟨mem_closedBall_self (by
    have := norm_nonneg (c - b); linarith), show (0 : ℝ) ≤ (b : ℂ).im by simp⟩
  have hcont : ContinuousOn (fun z => ‖Φ z - x‖) K' :=
    (((hD.conf.diff.mono (closedBall_subset_ball hD.hρr)).continuousOn).mono
      inter_subset_left).sub continuousOn_const |>.norm
  obtain ⟨z, hzK, hzmin⟩ := hK'c.exists_isMinOn ⟨_, hbK⟩ hcont
  set σ' := σ / (m / 4) with hσ'
  have hσ'0 : 0 < σ' := div_pos hσ (by linarith)
  have hbd : ∀ᵐ v ∂circleUnif c r, 0 ≤ Lr σ (Φ (foldH v)) x ∧
      Lr σ (Φ (foldH v)) x ≤ 2 * (ell σ' ‖v - z‖ + ell σ' ‖v - conj z‖) := by
    filter_upwards [ae_foldH_mem_disc hr hcr, ae_ne_circleUnif c hr.ne' z,
      ae_ne_circleUnif c hr.ne' (conj z)] with v hfv h1 h2
    have hwH : Φ (foldH v) ∈ Hbar := hD.up _ hfv
    have hfz : foldH v ≠ z := by
      intro e
      unfold foldH at e
      split_ifs at e
      · exact h1 e
      · exact h2 (by rw [← e, Complex.conj_conj])
    have hdz : 0 < ‖foldH v - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hfz)
    have hlip : m * ‖foldH v - z‖ ≤ ‖Φ (foldH v) - Φ z‖ := (hbl _ hfv.1 _ hzK.1).1
    have hmin : ‖Φ z - x‖ ≤ ‖Φ (foldH v) - x‖ := isMinOn_iff.1 hzmin _ hfv
    have htri : ‖Φ (foldH v) - Φ z‖ ≤ 2 * ‖Φ (foldH v) - x‖ := by
      calc ‖Φ (foldH v) - Φ z‖ = ‖(Φ (foldH v) - x) - (Φ z - x)‖ := by congr 1; ring
        _ ≤ ‖Φ (foldH v) - x‖ + ‖Φ z - x‖ := norm_sub_le _ _
        _ ≤ 2 * ‖Φ (foldH v) - x‖ := by linarith
    have hlow : m / 4 * ‖foldH v - z‖ ≤ ‖Φ (foldH v) - x‖ := by
      have := hlip.trans htri
      have hnn := mul_nonneg hm.le hdz.le
      linarith
    have hm4 : 0 < m / 4 * ‖foldH v - z‖ := mul_pos (by linarith) hdz
    have hd : 0 < ‖Φ (foldH v) - x‖ := lt_of_lt_of_le hm4 hlow
    obtain ⟨b0, b1⟩ := Lr_bounds (ρ := σ) hwH hx hd
    refine ⟨b0, b1.trans ?_⟩
    have e1 : ell σ ‖Φ (foldH v) - x‖ ≤ ell σ' ‖foldH v - z‖ := by
      rw [hσ', ← ell_mul (by linarith) hdz]
      exact ell_anti hm4 hlow
    have hv1 : 0 < ‖v - z‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
    have hv2 : 0 < ‖v - conj z‖ := norm_pos_iff.2 (sub_ne_zero.2 h2)
    have e2 : ell σ' ‖foldH v - z‖ ≤ ell σ' ‖v - z‖ + ell σ' ‖v - conj z‖ := by
      unfold foldH
      split_ifs
      · linarith [ell_nonneg (ρ := σ') hv2]
      · have : ‖conj v - z‖ = ‖v - conj z‖ := by
          rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
        rw [this]; linarith [ell_nonneg (ρ := σ') hv1]
    linarith
  obtain ⟨i1, j1⟩ := integral_ell_circle_le c z hr hσ'0
  obtain ⟨i2, j2⟩ := integral_ell_circle_le c (conj z) hr hσ'0
  refine ⟨integral_nonneg_of_ae (hbd.mono fun v hv => hv.1), ?_⟩
  calc ∫ v, Lr σ (Φ (foldH v)) x ∂circleUnif c r
      ≤ ∫ v, 2 * (ell σ' ‖v - z‖ + ell σ' ‖v - conj z‖) ∂circleUnif c r :=
        integral_mono_of_nonneg (hbd.mono fun v hv => hv.1) ((i1.add i2).const_mul 2)
          (hbd.mono fun v hv => hv.2)
    _ = 2 * (∫ v, ell σ' ‖v - z‖ ∂circleUnif c r +
          ∫ v, ell σ' ‖v - conj z‖ ∂circleUnif c r) := by
        rw [integral_const_mul, integral_add i1 i2]
    _ ≤ 2 * (σ' / r + σ' / r) := by linarith
    _ = 16 * σ / (m * r) := by rw [hσ']; field_simp; ring

theorem PullData.isAdmissibleH_pullCircle_bind (hD : PullData Φ b r₀ ρ r₁ m M) {c : ℂ}
    {r : ℝ} (hr : 0 < r) (hcr : ‖c - b‖ + r ≤ ρ) {σ : ℝ} (hσ : 0 < σ) :
    IsAdmissibleH ((pullCircle Φ c r).bind fun w => foldedCircle w σ) := by
  have hadm := hD.isAdmissibleH_pullCircle hr hcr
  have := hadm.1
  obtain ⟨K, hK, -, hKc⟩ := hadm.2.1
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  have := isFiniteMeasure_bind_circle (r := σ) (pullCircle Φ c r)
  refine admissible_of_bounds (R := R₀ + σ)
    (bind_circle_support (pullCircle Φ c r) hσ.le hKc hR₀ le_rfl)
    (C := (pullCircle Φ c r) univ * (2 * ENNReal.ofReal (potConst σ))) ?_
    (bind_circle_pot (pullCircle Φ c r) (fun z y => foldedCircle_pot_le hσ z y))
  exact ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)

/-- **Regularization at pulled-back circles** (item 1). -/
theorem ae_evalReg_pullCircle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : Ω → FieldSample} (hW : IsFreeGFFModConstH W P)
    (hD : PullData Φ b r₀ ρ r₁ m M) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcr : ‖c - b‖ + r ≤ ρ) :
    ∀ᵐ ω ∂P, evalReg (W ω) (pullCircle Φ c r) = W ω (pullCircle Φ c r) := by
  set μ := pullCircle Φ c r with hμ
  have hadm : IsAdmissibleH μ := hD.isAdmissibleH_pullCircle hr hcr
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hD.conf.meas.aemeasurable).2 inferInstance
  obtain ⟨K, hK, hKH, hKc⟩ := hadm.2.1
  have h1 : ∀ᵐ ω ∂P, ∀ k, ∫ z, avgReg (W ω) k z ∂μ =
      W ω (μ.bind fun w => foldedCircle w (radius k)) :=
    ae_all_iff.2 fun k => Regularization.ae_integral_avgReg_eq hW k μ hK hKH hKc
  set D : ℕ → Ω → ℝ := fun k ω => W ω (μ.bind fun w => foldedCircle w (radius k)) - W ω μ
  have hadmk : ∀ k, IsAdmissibleH (μ.bind fun w => foldedCircle w (radius k)) := fun k =>
    hD.isAdmissibleH_pullCircle_bind hr hcr (radius_pos k)
  have hmass : ∀ k, (μ.bind fun w => foldedCircle w (radius k)) univ = μ univ := fun k =>
    bind_circle_univ μ
  have hmom := fun k => integral_sq_pair_eq hW (hadmk k) hadm (hmass k)
  have hm := hD.bl.1
  have hvar : ∀ k, ∫ ω, D k ω ^ 2 ∂P ≤ 16 / (m * r) * (1 / 2 : ℝ) ^ k := by
    intro k
    rw [(hmom k).2]
    refine (le_abs_self _).trans ((abs_kernelCov2_bind_le hadm (radius_pos k) (hadmk k)
      (fun x hx => integral_Lr_pullCircle_bounds hD hr hcr (radius_pos k) hx)).trans
      (le_of_eq ?_))
    unfold radius; field_simp
  have hsum : Summable fun k => ∫ ω, D k ω ^ 2 ∂P := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => sq_nonneg _) hvar ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h2 := ae_tendsto_zero_of_summable_sq
    (fun k => ((hW.measurable_coord _).sub (hW.measurable_coord _)).aemeasurable)
    (fun k => (hmom k).1) hsum
  filter_upwards [h1, h2] with ω h1 h2
  unfold evalReg
  simp only [h1]
  have h3 : Tendsto (fun k => W ω (μ.bind fun w => foldedCircle w (radius k))) atTop
      (𝓝 (W ω μ)) := by
    have := h2.add_const (W ω μ)
    rw [zero_add] at this
    refine this.congr fun k => ?_
    show D k ω + W ω μ = _
    simp only [D]; ring
  exact h3.limUnder_eq

/-- **`coordChange` at circles is the raw pulled-back pairing** (a.s.). -/
theorem ae_coordChange_pullCircle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : Ω → FieldSample} (hW : IsFreeGFFModConstH W P)
    (hD : PullData Φ b r₀ ρ r₁ m M) (Q : ℝ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcr : ‖c - b‖ + r ≤ ρ) :
    ∀ᵐ ω ∂P, coordChange (W ω) Φ Q (foldedCircle c r) =
      W ω (pullCircle Φ c r) + Q * ∫ z, Real.log ‖deriv Φ z‖ ∂(foldedCircle c r) := by
  filter_upwards [ae_evalReg_pullCircle hW hD hr hcr] with ω h
  rw [coordChange, ← h]
  rfl

end G3Cv
end QuantumZipper
