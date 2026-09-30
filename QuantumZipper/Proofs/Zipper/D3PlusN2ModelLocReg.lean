import QuantumZipper.Proofs.Zipper.D3PlusN2ModelLocMain
import QuantumZipper.Proofs.Zipper.D3PlusN2HarmP1
import QuantumZipper.Proofs.GFF.K3.MixedM7B2

/-!
# N2Z-MODELREG, deterministic part: the model is locally good and locally regular

Task N2-MODELLOC. For a sample `X ω` and a function `H_ω` continuous on `ball 0 r ∩ Hbar` with
`X ω (bal μ) = ∫ H_ω dμ` on the dyadic circles `μ ∈ circSet r` (the harmonic part,
`d3PlusN2HarmPart_holds`):

* `n2Model_apply_circ`: on `circSet r`, `h_L μ = X μ − ∫ H_ω dμ + ∫ α(−log‖·‖) dμ + L/γ`;
* `isLocallyGoodOn_n2Model`: if `X ω` is good, `h_L` is locally good on `halfDisc r`
  (`h_L = X + (−H_ω + α(−log‖·‖) + L/γ)` on the dyadic circles inside `halfDisc r`);
* `agreeNear_n2Model_reg`: `h_L` agrees near `0` (radius `r/2`) with the regular sample
  `n2Reg = (X + (−H_ω ∘ retr + L/γ)) + α(−log‖·‖)` (`retr` the retraction onto
  `closedBall 0 (3r/4) ∩ Hbar`), whose regularity witness is explicit when `X ω` is regular
  (`isRegularWith_n2Reg`, `RegClosure.add_ofFun'`, `RegClosure.add_ofFun_log'`).

Own elementary arguments (locality bookkeeping; Sheffield, *Gaussian free fields for
mathematicians*, PTRF 139 (2007), §2.6 (domain Markov property) for the decomposition used).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

open Prop16Area.G

/-- A dyadic circle whose closed half-ball lies in `halfDisc r` is in `circSet r`. -/
theorem norm_add_lt_of_closedBall_inter_subset {d : ℂ} (hd : d ∈ Hbar) {ρ r : ℝ} (hρ : 0 ≤ ρ)
    (h : Metric.closedBall d ρ ∩ Hbar ⊆ halfDisc r) : ‖d‖ + ρ < r := by
  by_cases hd0 : d = 0
  · subst hd0
    have hw : (Complex.I * ρ : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ ∩ Hbar := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_of_nonneg hρ]
      · show 0 ≤ (Complex.I * ρ).im
        simp [hρ]
    have := (h hw).1
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg hρ] at this
    simpa using this
  · have hn : 0 < ‖d‖ := norm_pos_iff.2 hd0
    set w : ℂ := ((1 + ρ / ‖d‖ : ℝ) : ℂ) * d with hw
    have hc : 0 < 1 + ρ / ‖d‖ := by positivity
    have hwn : ‖w‖ = ‖d‖ + ρ := by
      rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
      field_simp
    have hwd : ‖w - d‖ = ρ := by
      have e : w - d = ((ρ / ‖d‖ : ℝ) : ℂ) * d := by rw [hw]; push_cast; ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hmem : w ∈ Metric.closedBall d ρ ∩ Hbar := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, hwd]
      · show 0 ≤ w.im
        rw [hw, Complex.im_ofReal_mul]
        exact mul_nonneg hc.le hd
    have := (h hmem).1
    rwa [Metric.mem_ball, dist_zero_right, hwn] at this

variable {Ω : Type*} {X : Ω → FieldSample} {γ α L r : ℝ} {ω : Ω} {Hω : ℂ → ℝ}

theorem n2Model_apply_circ {μ : Measure ℂ} (hμ : μ ∈ circSet r) :
    n2Model γ α L r X ω μ = X ω μ - X ω (K3.bal 0 r μ) + ∫ z, α * -Real.log ‖z‖ ∂μ + L / γ := by
  classical
  simp [n2Model, locModel, hμ, localZ, K3.markovZ, circData]

theorem integrable_H_circ (hH : ContinuousOn Hω (Metric.ball (0 : ℂ) r ∩ Hbar)) {μ : Measure ℂ}
    (hμ : μ ∈ circSet r) : Integrable Hω μ := by
  simpa using integrable_circ (α := 0) hH hμ

theorem integrable_log_circ (μ : Measure ℂ) (c : ℂ) (ρ : ℝ) (hμ : μ = foldedCircle c ρ) :
    Integrable (fun z => α * -Real.log ‖z‖) μ := by
  subst hμ
  exact (CoordReg.integrable_log_norm_foldedCircle c ρ).neg.const_mul α

/-- The local correction `−H_ω + α(−log‖·‖) + L/γ`. -/
def n2Psi (γ α L : ℝ) (Hω : ℂ → ℝ) : ℂ → ℝ := fun z => -Hω z + α * -Real.log ‖z‖ + L / γ

theorem n2Model_eq_add_psi (hH : ContinuousOn Hω (Metric.ball (0 : ℂ) r ∩ Hbar))
    (hdec : ∀ μ ∈ circSet r, X ω (K3.bal 0 r μ) = ∫ z, Hω z ∂μ) {c : ℂ} {ρ : ℝ}
    (hμ : foldedCircle c ρ ∈ circSet r) :
    n2Model γ α L r X ω (foldedCircle c ρ) =
      (X ω + ofFun (n2Psi γ α L Hω)) (foldedCircle c ρ) := by
  rw [n2Model_apply_circ hμ, hdec _ hμ, Pi.add_apply]
  show _ = X ω _ + ∫ z, (-Hω z + α * -Real.log ‖z‖ + L / γ) ∂foldedCircle c ρ
  have h1 := integrable_H_circ hH hμ
  have h1n : Integrable (fun z => -Hω z) (foldedCircle c ρ) := h1.neg
  have h2 := integrable_log_circ (α := α) _ c ρ rfl
  have h12 : Integrable (fun z => -Hω z + α * -Real.log ‖z‖) (foldedCircle c ρ) := h1n.add h2
  rw [integral_add h12 (integrable_const _), integral_add h1n h2, integral_neg,
    integral_const, probReal_univ, one_smul]
  ring

/-- **The model is locally good on the half-disc.** -/
theorem isLocallyGoodOn_n2Model (hH : ContinuousOn Hω (Metric.ball (0 : ℂ) r ∩ Hbar))
    (hdec : ∀ μ ∈ circSet r, X ω (K3.bal 0 r μ) = ∫ z, Hω z ∂μ) (hg : IsLQGGood γ (X ω)) :
    IsLocallyGoodOn γ (halfDisc r) (n2Model γ α L r X ω) := by
  have hHH : halfDisc r ⊆ Hbar := (halfDisc_subset_H r).trans F1.B4d.H_subset_Hbar
  refine ⟨halfDisc r, isOpen_halfDisc r, inter_eq_left.2 hHH, X ω, n2Psi γ α L Hω, hg, ?_, ?_⟩
  · have hlog : ContinuousOn (fun z : ℂ => α * -Real.log ‖z‖) (halfDisc r) := by
      refine continuousOn_const.mul (ContinuousOn.neg ?_)
      refine Real.continuousOn_log.comp continuous_norm.continuousOn fun z hz => ?_
      have : z ≠ 0 := fun h0 => by
        have h := hz.2; rw [h0] at h; simp [H] at h
      exact norm_ne_zero_iff.2 this
    exact ((hH.mono fun z hz => ⟨hz.1, hHH hz⟩).neg.add hlog).add continuousOn_const
  · intro n k z hz hW
    have hd := CircleCont.dyadicRoundC_mem_Hbar hz n
    have hlt := norm_add_lt_of_closedBall_inter_subset hd (radius_pos k).le hW
    exact n2Model_eq_add_psi hH hdec ⟨n, k, z, hlt, rfl⟩

/-- The continuous extension `H_ω ∘ retr` (retraction onto `closedBall 0 (3r/4) ∩ Hbar`). -/
def n2Hext (r : ℝ) (Hω : ℂ → ℝ) : ℂ → ℝ := fun z => Hω (K3.retr 0 (3 * r / 4) z)

theorem continuous_n2Hext (hr : 0 < r) (hH : ContinuousOn Hω (Metric.ball (0 : ℂ) r ∩ Hbar)) :
    Continuous (n2Hext r Hω) := by
  have h34 : 0 < 3 * r / 4 := by positivity
  refine hH.comp_continuous (K3.continuous_retr_m7b 0 h34) fun z => ⟨?_, K3.retr_mem_Hbar h34 z⟩
  have h := K3.norm_retr_sub_le (t := 0) h34 z
  rw [Complex.ofReal_zero, sub_zero] at h
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-- The regular comparison sample. -/
def n2Reg (γ α L r : ℝ) (Hω : ℂ → ℝ) (x : FieldSample) : FieldSample :=
  (x + ofFun fun z => -n2Hext r Hω z + L / γ) +
    ofFun fun v => α * -Real.log ‖v - ((0 : ℝ) : ℂ)‖

/-- Its regularity witness. -/
def n2RegW (γ α L r : ℝ) (Hω : ℂ → ℝ) (G : ℂ × ℝ → ℝ) : ℂ × ℝ → ℝ :=
  fun q => (G q + ∫ v, (-n2Hext r Hω v + L / γ) ∂foldedCircle q.1 q.2) +
    α * (CircleCont.circPot q.2 q.1 0 / 2)

theorem isRegularWith_n2Reg (hr : 0 < r) (hH : ContinuousOn Hω (Metric.ball (0 : ℂ) r ∩ Hbar))
    {x : FieldSample} {G : ℂ × ℝ → ℝ} (hx : IsRegularWith x G) :
    IsRegularWith (n2Reg γ α L r Hω x) (n2RegW γ α L r Hω G) :=
  (hx.add_ofFun' ((continuous_n2Hext hr hH).neg.add continuous_const).continuousOn).add_ofFun_log'
    α 0

/-- **The model agrees near `0` with the regular comparison sample.** -/
theorem agreeNear_n2Model_reg (hr : 0 < r)
    (hH : ContinuousOn Hω (Metric.ball (0 : ℂ) r ∩ Hbar))
    (hdec : ∀ μ ∈ circSet r, X ω (K3.bal 0 r μ) = ∫ z, Hω z ∂μ) :
    AgreeNear (n2Model γ α L r X ω) (n2Reg γ α L r Hω (X ω)) (r / 2) := by
  intro n k z hz
  set d := dyadicRoundC n z
  set ρ := radius k
  have hρ : 0 < ρ := radius_pos k
  have hμ : foldedCircle d ρ ∈ circSet r := ⟨n, k, z, by linarith, rfl⟩
  rw [n2Model_eq_add_psi hH hdec hμ]
  have hae : ∀ᵐ v ∂foldedCircle d ρ, v ∈ CircleFubini.ballH (‖d‖ + ρ) :=
    measure_eq_zero_iff_ae_notMem.1 (CircleFubini.foldedCircle_support hρ.le le_rfl) |>.mono
      fun w hw => by simpa using hw
  have hext : n2Hext r Hω =ᵐ[foldedCircle d ρ] Hω := by
    filter_upwards [hae] with v hv
    simp only [n2Hext]
    congr 1
    refine K3.retr_eq_self hv.2 ?_
    have := hv.1
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [Complex.ofReal_zero, sub_zero]
    linarith
  have h1 := integrable_H_circ hH hμ
  have h1n : Integrable (fun z => -Hω z) (foldedCircle d ρ) := h1.neg
  have h1' : Integrable (fun z => -n2Hext r Hω z) (foldedCircle d ρ) := (h1.congr hext.symm).neg
  have h2 := integrable_log_circ (α := α) _ d ρ rfl
  have h12 : Integrable (fun z => -Hω z + α * -Real.log ‖z‖) (foldedCircle d ρ) := h1n.add h2
  simp only [n2Reg, n2Psi, Pi.add_apply, ofFun, Complex.ofReal_zero, sub_zero]
  rw [integral_add h12 (integrable_const _), integral_add h1n h2,
    integral_add h1' (integrable_const _), integral_neg, integral_neg,
    integral_congr_ae hext]
  ring

end D3Plus
end QuantumZipper
