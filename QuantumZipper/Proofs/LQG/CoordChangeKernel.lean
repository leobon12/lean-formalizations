import QuantumZipper.Proofs.LQG.CoordChangeDet
import QuantumZipper.Proofs.LQG.KernelIdentities
import QuantumZipper.Proofs.GFF.Admissible
import QuantumZipper.Proofs.GFF.SmoothingConvergence

/-!
# M4-T4, step 2: kernel computations for pushed-forward semicircles

For the local data `h : CoordChange.Data ψ a b δ m C` (see `CoordChangeDet`) and real centres,
let `pc ψ s r = ψ_* fc(s, r)` be the pushed-forward boundary semicircle. Main results:

* `isAdmissibleH_pc`: `pc ψ s r` is admissible (bi-Lipschitz pushforward into `Hbar`).
* `abs_kernelCov2_pc_fc_le` (**energy lemma**, M4-T4 step 2):
  `|Var[X(ψ_* fc(t,r)) − X(fc(ψ t, ψ'(t) r))]| ≤ (24 C/m) r`.
* `abs_kernelCov2_pc_pc_le` (increments): for `|s − t|, |s' − t| ≤ r`,
  `|Var[X(ψ_* fc(s,r)) − X(ψ_* fc(s',r))]| ≤ (8C/m + 4/r) |s − s'|`.

The proofs expand `neumannH (ψ v) (ψ v')` with the difference quotient:
`ψ v − ψ v' = (v − v') dq ψ v v'` and, by Schwarz reflection, `conj (ψ v') = ψ (conj v')`.
The singular parts are then exact circle averages of `log|· − y|`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace CoordChange

/-- The pushed-forward boundary semicircle `ψ_* fc(s, r)`. -/
def pc (ψ : ℂ → ℂ) (s r : ℝ) : Measure ℂ := (foldedCircle (s : ℂ) r).map ψ

/-- The potential `x ↦ ∫ neumannH x y dν(y)`. -/
def potF (ν : Measure ℂ) (x : ℂ) : ℝ := ∫ y, neumannH x y ∂ν

/-- The regular remainder of `neumannH (ψ v) (ψ v')` once the two logarithmic singularities
are removed. -/
def rem (ψ : ℂ → ℂ) (v v' : ℂ) : ℝ :=
  neumannH (ψ v) (ψ v') + Real.log ‖v' - v‖ + Real.log ‖v' - conj v‖

theorem measurable_potF (ν : Measure ℂ) [SFinite ν] : Measurable (potF ν) :=
  (measurable_neumannH.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

instance (ψ : ℂ → ℂ) (s r : ℝ) : IsProbabilityMeasure (pc ψ s r) := by
  unfold pc; infer_instance

/-! ### Elementary facts -/

theorem circleUnif_ofReal_eq_map (s r : ℝ) :
    circleUnif (s : ℂ) r = (circleUnif 0 r).map (fun u => (s : ℂ) + u) := by
  have := KernelId.circleUnif_affine s 1 0 r
  simpa using this

theorem abs_log_max_sub_log_max_le {r x y : ℝ} (hr : 0 < r) :
    |Real.log (max r x) - Real.log (max r y)| ≤ |x - y| / r :=
  (abs_log_sub_log_le hr (le_max_left _ _) (le_max_left _ _)).trans
    (div_le_div_of_nonneg_right (by rw [max_comm r x, max_comm r y]; exact abs_max_sub_max_le_abs _ _ _) hr.le)

theorem norm_foldH_sub_ofReal (v : ℂ) (s : ℝ) : ‖foldH v - s‖ = ‖v - s‖ := by
  unfold foldH; split_ifs
  · rfl
  · have : conj v - (s : ℂ) = conj (v - s) := by simp [map_sub]
    rw [this, Complex.norm_conj]

theorem norm_ofReal_sub_conj (p : ℝ) (z : ℂ) : ‖(p : ℂ) - conj z‖ = ‖(p : ℂ) - z‖ := by
  have : (p : ℂ) - conj z = conj ((p : ℂ) - z) := by simp [map_sub]
  rw [this, Complex.norm_conj]

theorem neumannH_conj_left (x y : ℂ) : neumannH (conj x) y = neumannH x y := by
  unfold neumannH
  have h1 : ‖conj x - y‖ = ‖x - conj y‖ := by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
  have h2 : ‖conj x - conj y‖ = ‖x - y‖ := by rw [← map_sub, Complex.norm_conj]
  rw [h1, h2]; ring

theorem neumannH_conj_right (x y : ℂ) : neumannH x (conj y) = neumannH x y := by
  unfold neumannH; rw [Complex.conj_conj]; ring

theorem circleUnif_singleton' (z : ℂ) {r : ℝ} (hr : r ≠ 0) (c : ℂ) : circleUnif z r {c} = 0 := by
  rw [CircleMV.circleUnif_eq_circMeas]; exact LQGDimension.Coupling.circMeas_singleton hr c

theorem ae_ne_circleUnif (z : ℂ) {r : ℝ} (hr : r ≠ 0) (c : ℂ) : ∀ᵐ w ∂circleUnif z r, w ≠ c := by
  rw [ae_iff]; simpa using circleUnif_singleton' z hr c

theorem ae_norm_circleUnif (s : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ w ∂circleUnif (s : ℂ) r, ‖w - (s : ℂ)‖ = r := by
  filter_upwards [SmoothConv.ae_circleUnif_sc (s : ℂ) r] with w hw
  rwa [abs_of_pos hr] at hw

theorem mem_closedBall_of_circle {t s r R : ℝ} {w : ℂ} (hw : ‖w - s‖ = r)
    (h : |s - t| + r ≤ R) : w ∈ closedBall (t : ℂ) R := by
  rw [mem_closedBall, dist_eq_norm]
  calc ‖w - t‖ = ‖(w - s) + ((s : ℂ) - t)‖ := by congr 1; ring
    _ ≤ ‖w - s‖ + ‖(s : ℂ) - t‖ := norm_add_le _ _
    _ = r + |s - t| := by rw [hw, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ R := by linarith

theorem conj_mem_closedBall_real {t R : ℝ} {z : ℂ} (hz : z ∈ closedBall (t : ℂ) R) :
    conj z ∈ closedBall (t : ℂ) R := by
  rw [mem_closedBall] at hz ⊢
  rwa [← Complex.conj_ofReal t, Complex.dist_conj_conj]

theorem foldH_mem_closedBall_real {t R : ℝ} {z : ℂ} (hz : z ∈ closedBall (t : ℂ) R) :
    foldH z ∈ closedBall (t : ℂ) R := by
  unfold foldH; split_ifs
  · exact hz
  · exact conj_mem_closedBall_real hz

theorem ae_mem_circleUnif {t s r R : ℝ} (hr : 0 < r) (h : |s - t| + r ≤ R) :
    ∀ᵐ w ∂circleUnif (s : ℂ) r, w ∈ closedBall (t : ℂ) R := by
  filter_upwards [ae_norm_circleUnif s hr] with w hw
  exact mem_closedBall_of_circle hw h

theorem ae_mem_foldedCircle {t s r R : ℝ} (hr : 0 < r) (h : |s - t| + r ≤ R) :
    ∀ᵐ w ∂foldedCircle (s : ℂ) r, w ∈ closedBall (t : ℂ) R ∩ Hbar := by
  rw [foldedCircle]
  refine (ae_map_iff measurable_foldH.aemeasurable
    (measurableSet_closedBall.inter isClosed_Hbar.measurableSet)).2 ?_
  filter_upwards [ae_mem_circleUnif hr h] with w hw
  exact ⟨foldH_mem_closedBall_real hw, SmoothConv.foldH_mem_Hbar_sc w⟩

theorem aemeasurable_of_ae_mem {μ : Measure ℂ} {S : Set ℂ} (hS : MeasurableSet S)
    (hμ : ∀ᵐ w ∂μ, w ∈ S) {f : ℂ → ℂ} (hf : ContinuousOn f S) : AEMeasurable f μ := by
  have := hf.aemeasurable (μ := μ) hS
  rwa [Measure.restrict_eq_self_of_ae_mem hμ] at this

/-- The probability-measure bound used throughout: an a.e. bound around a constant. -/
theorem integrable_and_abs_integral_add_le {μ : Measure ℂ} [IsProbabilityMeasure μ] {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f μ) {c B : ℝ} (hb : ∀ᵐ w ∂μ, |f w + c| ≤ B) :
    Integrable f μ ∧ |∫ w, f w ∂μ + c| ≤ B := by
  have hi : Integrable f μ := by
    refine Integrable.of_bound hf (B + |c|) ?_
    filter_upwards [hb] with w hw
    rw [Real.norm_eq_abs]
    calc |f w| = |(f w + c) - c| := by ring_nf
      _ ≤ |f w + c| + |c| := abs_sub _ _
      _ ≤ B + |c| := by linarith
  refine ⟨hi, ?_⟩
  have e : ∫ w, f w ∂μ + c = ∫ w, (f w + c) ∂μ := by
    rw [integral_add hi (integrable_const c), integral_const]; simp
  rw [e]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun w => f w + c) (C := B)
    (by filter_upwards [hb] with w hw; rwa [Real.norm_eq_abs])
  simpa using this

theorem abs_log_max_sub_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log (max y x) - Real.log y| ≤ |Real.log x - Real.log y| := by
  rcases le_total x y with h | h
  · rw [max_eq_left h, sub_self, abs_zero]; exact abs_nonneg _
  · rw [max_eq_right h]

theorem kernelCov_comm_of_admissible {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) : kernelCov neumannH μ ν = kernelCov neumannH ν μ := by
  have := hμ.1; have := hν.1
  unfold kernelCov
  rw [integral_integral_swap (integrable_neumannH_prod hμ hν)]
  simp_rw [neumannH_symm]

/-! ### Consequences of the local data on circles -/

namespace Data

variable {ψ : ℂ → ℂ} {a b δ m C : ℝ}

theorem psi_foldH (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ} (hR : R ≤ δ)
    {w : ℂ} (hw : w ∈ closedBall (t : ℂ) R) : ψ (foldH w) = ψ w ∨ ψ (foldH w) = conj (ψ w) := by
  unfold foldH; split_ifs
  · exact Or.inl rfl
  · exact Or.inr (h.refl t ht w (h.closedBall_sub t hR hw))

theorem neumannH_psi_foldH_left (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR : R ≤ δ) {w : ℂ} (hw : w ∈ closedBall (t : ℂ) R) (y : ℂ) :
    neumannH (ψ (foldH w)) y = neumannH (ψ w) y := by
  rcases h.psi_foldH ht hR hw with e | e <;> rw [e]
  exact neumannH_conj_left _ _

theorem neumannH_psi_foldH_right (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR : R ≤ δ) {w : ℂ} (hw : w ∈ closedBall (t : ℂ) R) (x : ℂ) :
    neumannH x (ψ (foldH w)) = neumannH x (ψ w) := by
  rcases h.psi_foldH ht hR hw with e | e <;> rw [e]
  exact neumannH_conj_right _ _

theorem continuousOn_closedBall (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR : R ≤ δ) : ContinuousOn ψ (closedBall (t : ℂ) R) :=
  (h.diff t ht).continuousOn.mono (h.closedBall_sub t hR)

theorem aemeasurable_circleUnif (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR : R ≤ δ) {s r : ℝ} (hr : 0 < r) (hsr : |s - t| + r ≤ R) :
    AEMeasurable ψ (circleUnif (s : ℂ) r) :=
  aemeasurable_of_ae_mem measurableSet_closedBall (ae_mem_circleUnif hr hsr)
    (h.continuousOn_closedBall ht hR)

theorem aemeasurable_foldedCircle (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR : R ≤ δ) {s r : ℝ} (hr : 0 < r) (hsr : |s - t| + r ≤ R) :
    AEMeasurable ψ (foldedCircle (s : ℂ) r) :=
  aemeasurable_of_ae_mem measurableSet_closedBall
    ((ae_mem_foldedCircle hr hsr).mono fun _ hw => hw.1) (h.continuousOn_closedBall ht hR)

theorem integral_pc (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ} (hR : R ≤ δ)
    {s r : ℝ} (hr : 0 < r) (hsr : |s - t| + r ≤ R) {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ x, g x ∂(pc ψ s r) = ∫ w, g (ψ (foldH w)) ∂(circleUnif (s : ℂ) r) := by
  have hψ := h.aemeasurable_foldedCircle ht hR hr hsr
  unfold pc
  rw [integral_map hψ hg.aestronglyMeasurable]
  unfold foldedCircle at hψ ⊢
  exact integral_map measurable_foldH.aemeasurable (hg.comp_aemeasurable hψ).aestronglyMeasurable

/-- Admissibility of `ψ_* fc(s, r)`. -/
theorem isAdmissibleH_pc (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ r0 δ m C) {s r : ℝ} (hr : 0 < r) (hsr : |s - t| + r ≤ R) :
    IsAdmissibleH (pc ψ s r) := by
  classical
  have hRδ : R ≤ δ := hR.trans r0_le_δ
  set S := closedBall (t : ℂ) R
  set f : ℂ → ℂ := S.piecewise ψ (fun _ => 0) with hf
  have hfm : Measurable f :=
    ContinuousOn.measurable_piecewise (h.continuousOn_closedBall ht hRδ) continuousOn_const
      measurableSet_closedBall
  have hK : IsCompact (S ∩ Hbar) := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hae := ae_mem_foldedCircle hr hsr
  have hKc : foldedCircle (s : ℂ) r (S ∩ Hbar)ᶜ = 0 := ae_iff.1 hae
  have hfeq : ψ =ᵐ[foldedCircle (s : ℂ) r] f := by
    filter_upwards [hae] with w hw
    rw [hf, piecewise_eq_of_mem _ _ _ hw.1]
  have hmap : pc ψ s r = (foldedCircle (s : ℂ) r).map f := Measure.map_congr hfeq
  rw [hmap]
  have hs : ((s : ℂ)) ∈ Hbar := show (0 : ℝ) ≤ (s : ℂ).im by simp
  refine isAdmissibleH_map (isAdmissibleH_foldedCircle hs hr) hK hKc hfm ?_ ?_
    (c := m / 2) (by linarith [h.mpos]) ?_
  · refine (h.continuousOn_closedBall ht hRδ).mono inter_subset_left |>.congr ?_
    intro x hx; rw [hf, piecewise_eq_of_mem _ _ _ hx.1]
  · rintro _ ⟨x, hx, rfl⟩
    rw [hf, piecewise_eq_of_mem _ _ _ hx.1]
    exact h.im_nonneg ht hR0 hR hx.1 hx.2
  · intro x hx y hy
    have e : f x - f y = (x - y) * dq ψ x y := by
      rw [hf, piecewise_eq_of_mem _ _ _ hx.1, piecewise_eq_of_mem _ _ _ hy.1]
      exact h.sub_eq ht (h.closedBall_sub t hRδ hx.1) (h.closedBall_sub t hRδ hy.1)
    rw [e, norm_mul]
    have := h.norm_dq_ge ht hR0 hR hx.1 hy.1
    nlinarith [norm_nonneg (x - y)]

/-- The remainder in terms of the difference quotient. -/
theorem rem_eq (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R ≤ r0 δ m C) {v v' : ℂ} (hv : v ∈ closedBall (t : ℂ) R)
    (hv' : v' ∈ closedBall (t : ℂ) R) (h1 : v' ≠ v) (h2 : v' ≠ conj v) :
    rem ψ v v' = -Real.log ‖dq ψ v v'‖ - Real.log ‖dq ψ v (conj v')‖ := by
  have hRδ : R ≤ δ := hR.trans r0_le_δ
  have hvB := h.closedBall_sub t hRδ hv
  have hv'B := h.closedBall_sub t hRδ hv'
  have hcv' := conj_mem_closedBall_real hv'
  have hcv'B := h.closedBall_sub t hRδ hcv'
  have hq1 : 0 < ‖dq ψ v v'‖ := lt_of_lt_of_le (by linarith [h.mpos]) (h.norm_dq_ge ht hR0 hR hv hv')
  have hq2 : 0 < ‖dq ψ v (conj v')‖ :=
    lt_of_lt_of_le (by linarith [h.mpos]) (h.norm_dq_ge ht hR0 hR hv hcv')
  have hd1 : 0 < ‖v - v'‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h1))
  have hd2 : 0 < ‖v - conj v'‖ := by
    refine norm_pos_iff.2 (sub_ne_zero.2 fun e => h2 ?_)
    rw [e, Complex.conj_conj]
  have e1 : ‖ψ v - ψ v'‖ = ‖v - v'‖ * ‖dq ψ v v'‖ := by rw [h.sub_eq ht hvB hv'B, norm_mul]
  have e2 : ‖ψ v - conj (ψ v')‖ = ‖v - conj v'‖ * ‖dq ψ v (conj v')‖ := by
    rw [← h.refl t ht v' hv'B, h.sub_eq ht hvB hcv'B, norm_mul]
  have e3 : ‖v' - v‖ = ‖v - v'‖ := norm_sub_rev _ _
  have e4 : ‖v' - conj v‖ = ‖v - conj v'‖ := norm_sub_conj_comm v' v
  unfold rem neumannH
  rw [e1, e2, e3, e4, Real.log_mul hd1.ne' hq1.ne', Real.log_mul hd2.ne' hq2.ne']
  ring

/-- Inner integrals: `∫ neumannH (ψ v) (ψ v') dσ_{s'}(v') = ∫ rem − 2 log max(r', |s' − v|)`. -/
theorem integral_neumannH_psi (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ r0 δ m C) {s' r' : ℝ} (hr' : 0 < r') (hsr' : |s' - t| + r' ≤ R)
    {v : ℂ} (hv : v ∈ closedBall (t : ℂ) R) :
    Integrable (fun v' => rem ψ v v') (circleUnif (s' : ℂ) r') ∧
    (∀ᵐ v' ∂circleUnif (s' : ℂ) r',
      |rem ψ v v' + 2 * Real.log (deriv ψ t).re| ≤ 8 * C / m * R) ∧
    Integrable (fun v' => neumannH (ψ v) (ψ v')) (circleUnif (s' : ℂ) r') ∧
    ∫ v', neumannH (ψ v) (ψ v') ∂circleUnif (s' : ℂ) r' =
      ∫ v', rem ψ v v' ∂circleUnif (s' : ℂ) r' - 2 * Real.log (max r' ‖(s' : ℂ) - v‖) := by
  have hRδ : R ≤ δ := hR.trans r0_le_δ
  have hψ := h.aemeasurable_circleUnif ht hRδ hr' hsr'
  have hGm : AEStronglyMeasurable (fun v' => neumannH (ψ v) (ψ v')) (circleUnif (s' : ℂ) r') :=
    (measurable_neumannH.comp_aemeasurable (aemeasurable_const.prodMk hψ)).aestronglyMeasurable
  have hl1 := SmoothConv.integrable_log_norm_sub_circleUnif_sc (s' : ℂ) v r'
  have hl2 := SmoothConv.integrable_log_norm_sub_circleUnif_sc (s' : ℂ) (conj v) r'
  have hremm : AEStronglyMeasurable (fun v' => rem ψ v v') (circleUnif (s' : ℂ) r') :=
    (hGm.add hl1.1).add hl2.1
  have hbd : ∀ᵐ v' ∂circleUnif (s' : ℂ) r',
      |rem ψ v v' + 2 * Real.log (deriv ψ t).re| ≤ 8 * C / m * R := by
    filter_upwards [ae_mem_circleUnif hr' hsr', ae_ne_circleUnif (s' : ℂ) hr'.ne' v,
      ae_ne_circleUnif (s' : ℂ) hr'.ne' (conj v)] with v' hv' h1 h2
    rw [h.rem_eq ht hR0 hR hv hv' h1 h2]
    have b1 := h.abs_log_norm_dq_sub_le ht hR0 hR hv hv'
    have b2 := h.abs_log_norm_dq_sub_le ht hR0 hR hv (conj_mem_closedBall_real hv')
    have e : -Real.log ‖dq ψ v v'‖ - Real.log ‖dq ψ v (conj v')‖ + 2 * Real.log (deriv ψ t).re
        = -((Real.log ‖dq ψ v v'‖ - Real.log (deriv ψ t).re) +
          (Real.log ‖dq ψ v (conj v')‖ - Real.log (deriv ψ t).re)) := by ring
    rw [e, abs_neg]
    calc _ ≤ |Real.log ‖dq ψ v v'‖ - Real.log (deriv ψ t).re| +
          |Real.log ‖dq ψ v (conj v')‖ - Real.log (deriv ψ t).re| := abs_add_le _ _
      _ ≤ 4 * C / m * R + 4 * C / m * R := add_le_add b1 b2
      _ = 8 * C / m * R := by ring
  have hremi : Integrable (fun v' => rem ψ v v') (circleUnif (s' : ℂ) r') :=
    (integrable_and_abs_integral_add_le hremm hbd).1
  have hGeq : (fun v' => neumannH (ψ v) (ψ v')) =
      fun v' => rem ψ v v' - Real.log ‖v' - v‖ - Real.log ‖v' - conj v‖ := by
    funext v'; unfold rem; ring
  have hGi : Integrable (fun v' => neumannH (ψ v) (ψ v')) (circleUnif (s' : ℂ) r') := by
    rw [hGeq]; exact (hremi.sub hl1).sub hl2
  refine ⟨hremi, hbd, hGi, ?_⟩
  have hi2 : Integrable (fun v' => rem ψ v v' - Real.log ‖v' - v‖) (circleUnif (s' : ℂ) r') :=
    hremi.sub hl1
  rw [hGeq, integral_sub hi2 hl2, integral_sub hremi hl1,
    SmoothConv.integral_log_norm_sub_circleUnif_sc _ _ hr',
    SmoothConv.integral_log_norm_sub_circleUnif_sc _ _ hr', norm_ofReal_sub_conj]
  ring

/-- `potF (pc s' r')` at `ψ w`, for `w` in the ball, as a circle integral. -/
theorem potF_pc (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ} (hR : R ≤ δ)
    {s' r' : ℝ} (hr' : 0 < r') (hsr' : |s' - t| + r' ≤ R) (x : ℂ) :
    potF (pc ψ s' r') x = ∫ v', neumannH x (ψ v') ∂circleUnif (s' : ℂ) r' := by
  unfold potF
  have hm : Measurable (fun y => neumannH x y) :=
    measurable_neumannH.comp (measurable_const.prodMk measurable_id)
  rw [h.integral_pc ht hR hr' hsr' hm]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_circleUnif hr' hsr'] with w hw
  exact h.neumannH_psi_foldH_right ht hR hw x

theorem kernelCov_pc_left (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR : R ≤ δ) {s r : ℝ} (hr : 0 < r) (hsr : |s - t| + r ≤ R) (ν : Measure ℂ) [SFinite ν] :
    kernelCov neumannH (pc ψ s r) ν = ∫ w, potF ν (ψ (foldH w)) ∂circleUnif (s : ℂ) r :=
  h.integral_pc ht hR hr hsr (measurable_potF ν)

theorem potF_psi_foldH (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR : R ≤ δ) {w : ℂ} (hw : w ∈ closedBall (t : ℂ) R) (ν : Measure ℂ) :
    potF ν (ψ (foldH w)) = potF ν (ψ w) := by
  unfold potF
  simp_rw [h.neumannH_psi_foldH_left ht hR hw]

theorem aestronglyMeasurable_potF_comp (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b)
    {R : ℝ} (hR : R ≤ δ) {s r : ℝ} (hr : 0 < r) (hsr : |s - t| + r ≤ R) (ν : Measure ℂ)
    [SFinite ν] :
    AEStronglyMeasurable (fun w => potF ν (ψ (foldH w))) (circleUnif (s : ℂ) r) := by
  have hψ := h.aemeasurable_foldedCircle ht hR hr hsr
  unfold foldedCircle at hψ
  exact ((measurable_potF ν).comp_aemeasurable (hψ.comp_measurable measurable_foldH)).aestronglyMeasurable

theorem potF_fc_real (p : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (x : ℂ) :
    potF (foldedCircle (p : ℂ) ρ) x = -2 * Real.log (max ρ ‖(p : ℂ) - x‖) := by
  unfold potF
  simp_rw [neumannH_symm x]
  rw [SmoothConv.integral_neumannH_foldedCircle_sc _ _ hρ, norm_ofReal_sub_conj]
  ring

/-! ### The energy lemma -/

/-- **Energy lemma** (M4-T4 step 2): the pushed-forward semicircle and the semicircle of radius
`ψ'(t) r` around `ψ(t)` differ by `O(r)` in the Neumann energy. -/
theorem abs_kernelCov2_pc_fc_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ}
    (hr : 0 < r) (hr0 : r ≤ r0 δ m C) :
    |kernelCov2 neumannH (pc ψ t r, foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * r))
        (pc ψ t r, foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * r))| ≤
      24 * C / m * r := by
  have hrδ : r ≤ δ := hr0.trans r0_le_δ
  have htt : |t - t| + r ≤ r := by simp
  set L := Real.log (deriv ψ t).re with hL
  have hd := h.deriv_re_pos ht
  set ρ := (deriv ψ t).re * r with hρ
  have hρ0 : 0 < ρ := mul_pos hd hr
  set p : ℝ := (ψ t).re with hp
  have hpt : (p : ℂ) = ψ t := by
    apply Complex.ext
    · simp [hp]
    · simp [h.im_eq_zero ht (mem_ball_self (by linarith [h.δpos]) : (t : ℂ) ∈ ball (t : ℂ) (2 * δ))]
  set μ := pc ψ t r
  set ν := foldedCircle (p : ℂ) ρ
  have hμadm : IsAdmissibleH μ := h.isAdmissibleH_pc ht hr.le hr0 hr htt
  have hνadm : IsAdmissibleH ν :=
    isAdmissibleH_foldedCircle (show (0 : ℝ) ≤ (p : ℂ).im by simp) hρ0
  have : IsFiniteMeasure μ := hμadm.1
  have hσ : IsProbabilityMeasure (circleUnif (t : ℂ) r) := inferInstance
  -- K1
  have hK1 : |kernelCov neumannH μ μ + 2 * Real.log r + 2 * L| ≤ 8 * C / m * r := by
    rw [h.kernelCov_pc_left ht hrδ hr htt μ, add_assoc]
    refine (integrable_and_abs_integral_add_le
      (h.aestronglyMeasurable_potF_comp ht hrδ hr htt μ) ?_).2
    filter_upwards [ae_mem_circleUnif hr htt, ae_norm_circleUnif t hr] with w hw hw'
    rw [h.potF_psi_foldH ht hrδ hw, h.potF_pc ht hrδ hr htt]
    obtain ⟨hi, hb, -, heq⟩ := h.integral_neumannH_psi ht hr.le hr0 hr htt hw
    rw [heq, norm_sub_rev, hw', max_self]
    have := (integrable_and_abs_integral_add_le hi.1 hb).2
    calc |∫ v', rem ψ w v' ∂circleUnif (t : ℂ) r - 2 * Real.log r + (2 * Real.log r + 2 * L)|
        = |∫ v', rem ψ w v' ∂circleUnif (t : ℂ) r + 2 * L| := by ring_nf
      _ ≤ _ := this
  -- K2
  have hK2 : |kernelCov neumannH μ ν + 2 * Real.log r + 2 * L| ≤ 8 * C / m * r := by
    rw [h.kernelCov_pc_left ht hrδ hr htt ν, add_assoc]
    refine (integrable_and_abs_integral_add_le
      (h.aestronglyMeasurable_potF_comp ht hrδ hr htt ν) ?_).2
    filter_upwards [ae_mem_circleUnif hr htt, ae_norm_circleUnif t hr] with w hw hw'
    rw [h.potF_psi_foldH ht hrδ hw, potF_fc_real p hρ0, hpt]
    have htB : (t : ℂ) ∈ closedBall (t : ℂ) r := mem_closedBall_self hr.le
    have e1 : ‖ψ t - ψ w‖ = r * ‖dq ψ t w‖ := by
      rw [h.sub_eq ht (h.closedBall_sub t hrδ htB) (h.closedBall_sub t hrδ hw), norm_mul,
        norm_sub_rev, hw']
    have hq : 0 < ‖dq ψ t w‖ :=
      lt_of_lt_of_le (by linarith [h.mpos]) (h.norm_dq_ge ht hr.le hr0 htB hw)
    have e2 : max ρ (r * ‖dq ψ t w‖) = r * max (deriv ψ t).re ‖dq ψ t w‖ := by
      rw [hρ, mul_comm (deriv ψ t).re r, mul_max_of_nonneg _ _ hr.le]
    rw [e1, e2, Real.log_mul hr.ne' (lt_of_lt_of_le hd (le_max_left _ _)).ne']
    have b := (abs_log_max_sub_le hq hd).trans (h.abs_log_norm_dq_sub_le ht hr.le hr0 htB hw)
    have e3 : -2 * (Real.log r + Real.log (max (deriv ψ t).re ‖dq ψ t w‖)) + (2 * Real.log r
        + 2 * L) = -2 * (Real.log (max (deriv ψ t).re ‖dq ψ t w‖) - L) := by rw [hL]; ring
    rw [← hL] at b
    rw [e3, abs_mul]
    calc _ = 2 * |Real.log (max (deriv ψ t).re ‖dq ψ t w‖) - L| := by norm_num
      _ ≤ 2 * (4 * C / m * r) := by linarith
      _ = 8 * C / m * r := by ring
  have hK3 : kernelCov neumannH ν μ = kernelCov neumannH μ ν :=
    kernelCov_comm_of_admissible hνadm hμadm
  have hK4 : kernelCov neumannH ν ν = -2 * Real.log r - 2 * L := by
    rw [kernelCov_fc_real_sameCenter hρ0 hρ0, max_self, hρ, Real.log_mul hd.ne' hr.ne', hL]
    ring
  unfold kernelCov2
  simp only
  rw [hK3, hK4]
  have e : kernelCov neumannH μ μ - kernelCov neumannH μ ν - kernelCov neumannH μ ν +
      (-2 * Real.log r - 2 * L) = (kernelCov neumannH μ μ + 2 * Real.log r + 2 * L) -
      2 * (kernelCov neumannH μ ν + 2 * Real.log r + 2 * L) := by ring
  rw [e]
  calc _ ≤ |kernelCov neumannH μ μ + 2 * Real.log r + 2 * L| +
        |2 * (kernelCov neumannH μ ν + 2 * Real.log r + 2 * L)| := abs_sub _ _
    _ ≤ 8 * C / m * r + 2 * (8 * C / m * r) := by
        rw [abs_mul, abs_two]; linarith
    _ = 24 * C / m * r := by ring

/-! ### Increments -/

theorem potF_pc_eq (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R ≤ r0 δ m C) {s' r' : ℝ} (hr' : 0 < r') (hsr' : |s' - t| + r' ≤ R) {w : ℂ}
    (hw : w ∈ closedBall (t : ℂ) R) :
    potF (pc ψ s' r') (ψ (foldH w)) =
      ∫ v', rem ψ w v' ∂circleUnif (s' : ℂ) r' - 2 * Real.log (max r' ‖(s' : ℂ) - w‖) := by
  rw [h.potF_psi_foldH ht (hR.trans r0_le_δ) hw, h.potF_pc ht (hR.trans r0_le_δ) hr' hsr']
  exact (h.integral_neumannH_psi ht hR0 hR hr' hsr' hw).2.2.2

theorem abs_integral_rem_add_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ r0 δ m C) {s' r' : ℝ} (hr' : 0 < r') (hsr' : |s' - t| + r' ≤ R)
    {w : ℂ} (hw : w ∈ closedBall (t : ℂ) R) :
    |∫ v', rem ψ w v' ∂circleUnif (s' : ℂ) r' + 2 * Real.log (deriv ψ t).re| ≤ 8 * C / m * R :=
  have H := h.integral_neumannH_psi ht hR0 hR hr' hsr' hw
  (integrable_and_abs_integral_add_le H.1.1 H.2.1).2

theorem abs_integral_rem_sub_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ}
    (hr : 0 < r) (hr0 : 2 * r ≤ r0 δ m C) {s s' : ℝ} (hs : |s - t| ≤ r) (hs' : |s' - t| ≤ r)
    {w : ℂ} (hw : w ∈ closedBall (t : ℂ) (2 * r)) :
    |∫ v', rem ψ w v' ∂circleUnif (s : ℂ) r - ∫ v', rem ψ w v' ∂circleUnif (s' : ℂ) r| ≤
      4 * C / m * |s - s'| := by
  have hR0 : (0 : ℝ) ≤ 2 * r := by positivity
  have hsr : |s - t| + r ≤ 2 * r := by linarith
  have hs'r : |s' - t| + r ≤ 2 * r := by linarith
  have H := h.integral_neumannH_psi ht hR0 hr0 hr hsr hw
  have H' := h.integral_neumannH_psi ht hR0 hr0 hr hs'r hw
  have hmeas : ∀ s'' : ℝ, AEMeasurable (fun u : ℂ => (s'' : ℂ) + u) (circleUnif 0 r) :=
    fun _ => (measurable_const_add _).aemeasurable
  have e1 : ∫ v', rem ψ w v' ∂circleUnif (s : ℂ) r =
      ∫ u, rem ψ w ((s : ℂ) + u) ∂circleUnif 0 r := by
    have hm := H.1.aestronglyMeasurable
    rw [circleUnif_ofReal_eq_map s r] at hm ⊢
    exact integral_map (hmeas s) hm
  have e2 : ∫ v', rem ψ w v' ∂circleUnif (s' : ℂ) r =
      ∫ u, rem ψ w ((s' : ℂ) + u) ∂circleUnif 0 r := by
    have hm := H'.1.aestronglyMeasurable
    rw [circleUnif_ofReal_eq_map s' r] at hm ⊢
    exact integral_map (hmeas s') hm
  have i1 : Integrable (fun u => rem ψ w ((s : ℂ) + u)) (circleUnif 0 r) := by
    have hi := H.1
    rw [circleUnif_ofReal_eq_map s r] at hi
    exact (integrable_map_measure hi.aestronglyMeasurable (hmeas s)).1 hi
  have i2 : Integrable (fun u => rem ψ w ((s' : ℂ) + u)) (circleUnif 0 r) := by
    have hi := H'.1
    rw [circleUnif_ofReal_eq_map s' r] at hi
    exact (integrable_map_measure hi.aestronglyMeasurable (hmeas s')).1 hi
  rw [e1, e2, ← integral_sub i1 i2]
  have hb : ∀ᵐ u ∂circleUnif (0 : ℂ) r,
      ‖rem ψ w ((s : ℂ) + u) - rem ψ w ((s' : ℂ) + u)‖ ≤ 4 * C / m * |s - s'| := by
    filter_upwards [SmoothConv.ae_circleUnif_sc 0 r, ae_ne_circleUnif 0 hr.ne' (w - s),
      ae_ne_circleUnif 0 hr.ne' (conj w - s), ae_ne_circleUnif 0 hr.ne' (w - s'),
      ae_ne_circleUnif 0 hr.ne' (conj w - s')] with u hu h1 h2 h3 h4
    have hu' : ‖u‖ = r := by simpa [abs_of_pos hr] using hu
    have hv1 : (s : ℂ) + u ∈ closedBall (t : ℂ) (2 * r) :=
      mem_closedBall_of_circle (by rw [add_sub_cancel_left]; exact hu') hsr
    have hv2 : (s' : ℂ) + u ∈ closedBall (t : ℂ) (2 * r) :=
      mem_closedBall_of_circle (by rw [add_sub_cancel_left]; exact hu') hs'r
    rw [h.rem_eq ht hR0 hr0 hw hv1 (fun e => h1 (by rw [← e]; ring))
        (fun e => h2 (by rw [← e]; ring)),
      h.rem_eq ht hR0 hr0 hw hv2 (fun e => h3 (by rw [← e]; ring))
        (fun e => h4 (by rw [← e]; ring))]
    have b1 := h.abs_log_norm_dq_sub_log_norm_dq_le ht hR0 hr0 hw hv1 hw hv2
    have b2 := h.abs_log_norm_dq_sub_log_norm_dq_le ht hR0 hr0 hw (conj_mem_closedBall_real hv1)
      hw (conj_mem_closedBall_real hv2)
    have n1 : ‖((s : ℂ) + u) - ((s' : ℂ) + u)‖ = |s - s'| := by
      rw [show ((s : ℂ) + u) - ((s' : ℂ) + u) = ((s - s' : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    have n2 : ‖conj ((s : ℂ) + u) - conj ((s' : ℂ) + u)‖ = |s - s'| := by
      rw [← map_sub, Complex.norm_conj, n1]
    rw [sub_self, norm_zero, zero_add, n1] at b1
    rw [sub_self, norm_zero, zero_add, n2] at b2
    rw [Real.norm_eq_abs]
    set A1 := Real.log ‖dq ψ w ((s : ℂ) + u)‖
    set A2 := Real.log ‖dq ψ w ((s' : ℂ) + u)‖
    set B1 := Real.log ‖dq ψ w (conj ((s : ℂ) + u))‖
    set B2 := Real.log ‖dq ψ w (conj ((s' : ℂ) + u))‖
    have e : (-A1 - B1) - (-A2 - B2) = -((A1 - A2) + (B1 - B2)) := by ring
    rw [e, abs_neg]
    calc |(A1 - A2) + (B1 - B2)| ≤ |A1 - A2| + |B1 - B2| := abs_add_le _ _
      _ ≤ 2 * C / m * |s - s'| + 2 * C / m * |s - s'| := add_le_add b1 b2
      _ = 4 * C / m * |s - s'| := by ring
  have := norm_integral_le_of_norm_le_const hb
  simpa [Real.norm_eq_abs] using this

theorem integrable_potF_pc_comp (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ}
    (hr : 0 < r) (hr0 : 2 * r ≤ r0 δ m C) {s₀ s'' : ℝ} (hs₀ : |s₀ - t| ≤ r)
    (hs'' : |s'' - t| ≤ r) :
    Integrable (fun w => potF (pc ψ s'' r) (ψ (foldH w))) (circleUnif (s₀ : ℂ) r) := by
  have hR0 : (0 : ℝ) ≤ 2 * r := by positivity
  have hRδ : 2 * r ≤ δ := hr0.trans r0_le_δ
  have hs₀r : |s₀ - t| + r ≤ 2 * r := by linarith
  have hs''r : |s'' - t| + r ≤ 2 * r := by linarith
  refine (integrable_and_abs_integral_add_le (h.aestronglyMeasurable_potF_comp ht hRδ hr hs₀r _)
    (c := 2 * Real.log (deriv ψ t).re) (B := 8 * C / m * (2 * r) + 2 * (|Real.log r| + 2)) ?_).1
  filter_upwards [ae_mem_circleUnif hr hs₀r, ae_norm_circleUnif s₀ hr] with w hw hw'
  rw [h.potF_pc_eq ht hR0 hr0 hr hs''r hw]
  have b := h.abs_integral_rem_add_le ht hR0 hr0 hr hs''r hw
  have hx : ‖(s'' : ℂ) - w‖ ≤ 3 * r := by
    calc ‖(s'' : ℂ) - w‖ = ‖((s'' : ℂ) - s₀) - (w - s₀)‖ := by congr 1; ring
      _ ≤ ‖(s'' : ℂ) - s₀‖ + ‖w - s₀‖ := norm_sub_le _ _
      _ ≤ 2 * r + r := by
          rw [hw', ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have := abs_sub_le s'' t s₀
          rw [abs_sub_comm t s₀] at this
          linarith
      _ = 3 * r := by ring
  have l1 : Real.log r ≤ Real.log (max r ‖(s'' : ℂ) - w‖) := Real.log_le_log hr (le_max_left _ _)
  have l2 : Real.log (max r ‖(s'' : ℂ) - w‖) ≤ Real.log 3 + Real.log r := by
    rw [← Real.log_mul (by norm_num) hr.ne']
    exact Real.log_le_log (hr.trans_le (le_max_left _ _)) (max_le (by linarith) hx)
  have l3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have l4 : |Real.log (max r ‖(s'' : ℂ) - w‖)| ≤ |Real.log r| + 2 := by
    rw [abs_le]; constructor <;> cases abs_cases (Real.log r) <;>
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)]
  calc |∫ v', rem ψ w v' ∂circleUnif (s'' : ℂ) r - 2 * Real.log (max r ‖(s'' : ℂ) - w‖) +
        2 * Real.log (deriv ψ t).re|
      ≤ |∫ v', rem ψ w v' ∂circleUnif (s'' : ℂ) r + 2 * Real.log (deriv ψ t).re| +
        |2 * Real.log (max r ‖(s'' : ℂ) - w‖)| := by
        have e : ∫ v', rem ψ w v' ∂circleUnif (s'' : ℂ) r - 2 * Real.log (max r ‖(s'' : ℂ) - w‖) +
          2 * Real.log (deriv ψ t).re = (∫ v', rem ψ w v' ∂circleUnif (s'' : ℂ) r +
          2 * Real.log (deriv ψ t).re) - 2 * Real.log (max r ‖(s'' : ℂ) - w‖) := by ring
        rw [e]; exact abs_sub _ _
    _ ≤ 8 * C / m * (2 * r) + 2 * (|Real.log r| + 2) := by
        rw [abs_mul, abs_two]; linarith

theorem abs_kernelCov_pc_sub_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ}
    (hr : 0 < r) (hr0 : 2 * r ≤ r0 δ m C) {s₀ s s' : ℝ} (hs₀ : |s₀ - t| ≤ r) (hs : |s - t| ≤ r)
    (hs' : |s' - t| ≤ r) :
    |kernelCov neumannH (pc ψ s₀ r) (pc ψ s r) - kernelCov neumannH (pc ψ s₀ r) (pc ψ s' r)| ≤
      (4 * C / m + 2 / r) * |s - s'| := by
  have hR0 : (0 : ℝ) ≤ 2 * r := by positivity
  have hRδ : 2 * r ≤ δ := hr0.trans r0_le_δ
  have hs₀r : |s₀ - t| + r ≤ 2 * r := by linarith
  have hsr : |s - t| + r ≤ 2 * r := by linarith
  have hs'r : |s' - t| + r ≤ 2 * r := by linarith
  rw [h.kernelCov_pc_left ht hRδ hr hs₀r, h.kernelCov_pc_left ht hRδ hr hs₀r,
    ← integral_sub (h.integrable_potF_pc_comp ht hr hr0 hs₀ hs)
      (h.integrable_potF_pc_comp ht hr hr0 hs₀ hs')]
  have hb : ∀ᵐ w ∂circleUnif (s₀ : ℂ) r, ‖potF (pc ψ s r) (ψ (foldH w)) -
      potF (pc ψ s' r) (ψ (foldH w))‖ ≤ (4 * C / m + 2 / r) * |s - s'| := by
    filter_upwards [ae_mem_circleUnif hr hs₀r] with w hw
    rw [h.potF_pc_eq ht hR0 hr0 hr hsr hw, h.potF_pc_eq ht hR0 hr0 hr hs'r hw, Real.norm_eq_abs]
    have b1 := h.abs_integral_rem_sub_le ht hr hr0 hs hs' hw
    have b2 : |Real.log (max r ‖(s : ℂ) - w‖) - Real.log (max r ‖(s' : ℂ) - w‖)| ≤
        |s - s'| / r := by
      refine (abs_log_max_sub_log_max_le hr).trans (div_le_div_of_nonneg_right ?_ hr.le)
      refine (abs_norm_sub_norm_le _ _).trans (le_of_eq ?_)
      rw [show (s : ℂ) - w - ((s' : ℂ) - w) = ((s - s' : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    set I1 := ∫ v', rem ψ w v' ∂circleUnif (s : ℂ) r
    set I2 := ∫ v', rem ψ w v' ∂circleUnif (s' : ℂ) r
    set l1 := Real.log (max r ‖(s : ℂ) - w‖)
    set l2 := Real.log (max r ‖(s' : ℂ) - w‖)
    have e : I1 - 2 * l1 - (I2 - 2 * l2) = (I1 - I2) - 2 * (l1 - l2) := by ring
    rw [e]
    calc |(I1 - I2) - 2 * (l1 - l2)| ≤ |I1 - I2| + |2 * (l1 - l2)| := abs_sub _ _
      _ ≤ 4 * C / m * |s - s'| + 2 * (|s - s'| / r) := by
          rw [abs_mul, abs_two]; linarith
      _ = (4 * C / m + 2 / r) * |s - s'| := by ring
  have := norm_integral_le_of_norm_le_const hb
  simpa [Real.norm_eq_abs] using this

/-- **Increments**: the pushed-forward semicircles depend Lipschitz-continuously on the centre,
in the Neumann energy. -/
theorem abs_kernelCov2_pc_pc_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ}
    (hr : 0 < r) (hr0 : 2 * r ≤ r0 δ m C) {s s' : ℝ} (hs : |s - t| ≤ r) (hs' : |s' - t| ≤ r) :
    |kernelCov2 neumannH (pc ψ s r, pc ψ s' r) (pc ψ s r, pc ψ s' r)| ≤
      (8 * C / m + 4 / r) * |s - s'| := by
  have b1 := h.abs_kernelCov_pc_sub_le ht hr hr0 hs hs hs'
  have b2 := h.abs_kernelCov_pc_sub_le ht hr hr0 hs' hs hs'
  unfold kernelCov2
  simp only
  have e : kernelCov neumannH (pc ψ s r) (pc ψ s r) - kernelCov neumannH (pc ψ s r) (pc ψ s' r) -
      kernelCov neumannH (pc ψ s' r) (pc ψ s r) + kernelCov neumannH (pc ψ s' r) (pc ψ s' r) =
      (kernelCov neumannH (pc ψ s r) (pc ψ s r) - kernelCov neumannH (pc ψ s r) (pc ψ s' r)) -
      (kernelCov neumannH (pc ψ s' r) (pc ψ s r) -
        kernelCov neumannH (pc ψ s' r) (pc ψ s' r)) := by ring
  rw [e]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ (4 * C / m + 2 / r) * |s - s'| + (4 * C / m + 2 / r) * |s - s'| := add_le_add b1 b2
    _ = (8 * C / m + 4 / r) * |s - s'| := by ring

end Data

end CoordChange
end QuantumZipper
