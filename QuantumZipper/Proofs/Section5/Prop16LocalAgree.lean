import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Statements.Prop16

/-!
# Proposition 1.6, M4-P7-LOC (part 1): locality of the LQG approximations

Deterministic locality statements for field samples.

* `CircAgree W x x'`: `x` and `x'` agree on every **dyadic** folded circle
  `fc(d_n z, 2^{-k})` whose closed disc (within `Hbar`) lies in the open set `W` (countably many
  measures, so this is an a.s. statement about a coupling);
* `FcAgree W x x'`: the same for **every** folded circle (used for derived fields such as
  `translate`, `rescale`, whose values are built from `evalReg`).
* `avgReg_eq_of_circAgree`, `evalReg_eq_of_circAgree`: the regularized averages, and `evalReg`
  of a measure carried by a compact subset of `W`, only see the field inside `W`;
* `fcAgree_translate`, `fcAgree_rescale`, `fcAgree_addConst`: agreement is transported by the
  coordinate changes of Proposition 1.6;
* `fcAgree_translate_add_ofFun`, `fcAgree_rescale_add_ofFun`: for a regular `y` and `ψ`
  continuous on `W ∩ Hbar` only, `translate (y + ψ) t` agrees on `W − t` with
  `translate y t + ψ(· + t)` (and the same for `rescale`), via a cutoff of `ψ`;
* `isVagueLimitOn_of_circAgree`, `isVagueLimitOnR_of_circAgree`: local vague limits of
  `areaApprox` / `bdryApprox` transfer between fields agreeing on `W`.

This is the locality of the Gaussian multiplicative chaos approximations (Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 2.1 and §6: the measure on a
subdomain depends only on the circle averages there). The formal argument is our own elementary
one (AGENT_GUIDE cost rule): all approximations at scale `2^{-k}` near a compact `K` only use
circles within distance `2·2^{-k}` of `K`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace QuantumZipper

namespace Prop16Area

namespace G

open GoodSample RegClosure LocalRule CircleFubini

/-- Agreement on the dyadic folded circles inside `W`. -/
def CircAgree (W : Set ℂ) (x x' : FieldSample) : Prop :=
  ∀ (n k : ℕ) (z : ℂ), z ∈ Hbar → closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ W →
    x (foldedCircle (dyadicRoundC n z) (radius k)) = x' (foldedCircle (dyadicRoundC n z) (radius k))

/-- Agreement on every folded circle inside `W`. -/
def FcAgree (W : Set ℂ) (x x' : FieldSample) : Prop :=
  ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → closedBall d r ∩ Hbar ⊆ W →
    x (foldedCircle d r) = x' (foldedCircle d r)

variable {W : Set ℂ} {x x' x'' : FieldSample}

theorem FcAgree.circAgree (h : FcAgree W x x') : CircAgree W x x' := fun n k _ hz hW =>
  h _ (CircleCont.dyadicRoundC_mem_Hbar hz n) _ (radius_pos k) hW

theorem CircAgree.trans (h : CircAgree W x x') (h' : CircAgree W x' x'') : CircAgree W x x'' :=
  fun n k z hz hW => (h n k z hz hW).trans (h' n k z hz hW)

theorem FcAgree.trans (h : FcAgree W x x') (h' : FcAgree W x' x'') : FcAgree W x x'' :=
  fun d hd r hr hW => (h d hd r hr hW).trans (h' d hd r hr hW)

theorem FcAgree.mono {W' : Set ℂ} (h : FcAgree W x x') (hW : W' ⊆ W) : FcAgree W' x x' :=
  fun d hd r hr hW' => h d hd r hr (hW'.trans hW)

theorem eventually_two_radius_lt {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ k in atTop, 2 * radius k < δ := by
  have hr : Tendsto (fun k => 2 * radius k) atTop (𝓝 0) := by
    simpa using (tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul (2 : ℝ)
  exact hr.eventually (gt_mem_nhds hδ)

/-- The regularized average at scale `2^{-k}` only sees the dyadic circles near `z`. -/
theorem avgReg_eq_of_circAgree (h : CircAgree W x x') {k : ℕ} {z : ℂ} (hz : z ∈ Hbar)
    (hW : closedBall z (2 * radius k) ∩ Hbar ⊆ W) : avgReg x k z = avgReg x' k z := by
  unfold avgReg
  have hev : (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) =ᶠ[atTop]
      (fun n => x' (foldedCircle (dyadicRoundC n z) (radius k))) := by
    filter_upwards [(tendsto_dyadicRoundC z).eventually (ball_mem_nhds z (radius_pos k))]
      with n hn
    refine h n k z hz fun u hu => hW ⟨?_, hu.2⟩
    have h1 := hu.1
    rw [mem_closedBall] at h1 ⊢
    linarith [dist_triangle u (dyadicRoundC n z) z]
  unfold limUnder
  rw [Filter.map_congr hev]

/-- `evalReg` of a measure carried by a compact subset of `W` only sees the field inside `W`. -/
theorem evalReg_eq_of_circAgree (hWo : IsOpen W) (h : CircAgree W x x') {K : Set ℂ}
    (hK : IsCompact K) (hKW : K ⊆ W) {ν : Measure ℂ} (hν : ∀ᵐ u ∂ν, u ∈ K ∩ Hbar) :
    evalReg x ν = evalReg x' ν := by
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hWo hKW
  have hev : (fun k => ∫ w, avgReg x k w ∂ν) =ᶠ[atTop] (fun k => ∫ w, avgReg x' k w ∂ν) := by
    filter_upwards [eventually_two_radius_lt hδ] with k hk
    refine integral_congr_ae (hν.mono fun u hu => avgReg_eq_of_circAgree h hu.2 ?_)
    intro v hv
    refine hδW (mem_cthickening_of_dist_le v u δ K hu.1 ?_)
    have := hv.1
    rw [mem_closedBall] at this
    linarith
  unfold evalReg limUnder
  rw [Filter.map_congr hev]

theorem ae_fc_mem_ball_inter {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ u ∂foldedCircle d r, u ∈ closedBall d r ∩ Hbar := by
  filter_upwards [ae_fc_mem_closedBall hd hr, fc_ae_mem_Hbar d r] with u h1 h2
  exact ⟨h1, h2⟩

theorem isCompact_closedBall_inter_Hbar (c : ℂ) (r : ℝ) : IsCompact (closedBall c r ∩ Hbar) :=
  (isCompact_closedBall c r).inter_right isClosed_Hbar

/-- Agreement is transported by real translations. -/
theorem fcAgree_translate (hWo : IsOpen W) (h : CircAgree W x x') (t : ℝ) :
    FcAgree ((fun z => z + (t : ℂ)) ⁻¹' W) (translate x (t : ℂ)) (translate x' (t : ℂ)) := by
  intro d hd r hr hdW
  unfold translate
  refine evalReg_eq_of_circAgree hWo h (isCompact_closedBall_inter_Hbar (d + t) r) ?_ ?_
  · rintro u ⟨hu1, hu2⟩
    have hm : u - t ∈ closedBall d r ∩ Hbar := by
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm] at hu1 ⊢
        convert hu1 using 2; ring
      · have : (0 : ℝ) ≤ u.im := hu2
        show (0 : ℝ) ≤ (u - (t : ℂ)).im
        simpa using this
    simpa using hdW hm
  · refine (ae_map_iff (by fun_prop : Measurable fun z : ℂ => z + (t : ℂ)).aemeasurable
      ((measurableSet_closedBall.inter isClosed_Hbar.measurableSet).inter
        isClosed_Hbar.measurableSet)).2 ?_
    filter_upwards [ae_fc_mem_ball_inter hd hr] with u hu
    refine ⟨⟨?_, mapsTo_add_real t hu.2⟩, mapsTo_add_real t hu.2⟩
    have := hu.1
    rw [mem_closedBall, dist_eq_norm] at this ⊢
    convert this using 2; ring

theorem norm_div_sub_le {s : ℝ} (hs : 0 < s) {u d : ℂ} {r : ℝ}
    (hu : ‖u - (s : ℂ) * d‖ ≤ s * r) : ‖u / (s : ℂ) - d‖ ≤ r := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have e : u / (s : ℂ) - d = (u - (s : ℂ) * d) / (s : ℂ) := by field_simp
  rw [e, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, div_le_iff₀ hs]
  linarith

/-- Agreement is transported by dilations `z ↦ s z`, `s > 0`. -/
theorem fcAgree_rescale (hWo : IsOpen W) (h : CircAgree W x x') (Q : ℝ) {s : ℝ} (hs : 0 < s) :
    FcAgree ((fun z => (s : ℂ) * z) ⁻¹' W) (rescale x Q s) (rescale x' Q s) := by
  intro d hd r hr hdW
  unfold rescale coordChange
  congr 1
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  refine evalReg_eq_of_circAgree hWo h (isCompact_closedBall_inter_Hbar ((s : ℂ) * d) (s * r))
    ?_ ?_
  · rintro u ⟨hu1, hu2⟩
    have hm : u / (s : ℂ) ∈ closedBall d r ∩ Hbar := by
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm] at hu1 ⊢
        exact norm_div_sub_le hs hu1
      · have : (0 : ℝ) ≤ u.im := hu2
        show (0 : ℝ) ≤ (u / (s : ℂ)).im
        rw [Complex.div_ofReal_im]
        exact div_nonneg this hs.le
    have := hdW hm
    simpa [mul_div_cancel₀ _ hs'] using this
  · refine (ae_map_iff (by fun_prop : Measurable fun z : ℂ => (s : ℂ) * z).aemeasurable
      ((measurableSet_closedBall.inter isClosed_Hbar.measurableSet).inter
        isClosed_Hbar.measurableSet)).2 ?_
    filter_upwards [ae_fc_mem_ball_inter hd hr] with u hu
    refine ⟨⟨?_, mapsTo_mul_pos hs hu.2⟩, mapsTo_mul_pos hs hu.2⟩
    have := hu.1
    rw [mem_closedBall, dist_eq_norm] at this ⊢
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    exact mul_le_mul_of_nonneg_left this hs.le

theorem fcAgree_addConst (h : FcAgree W x x') (c : ℝ) :
    FcAgree W (addConst x c) (addConst x' c) := fun d hd r hr hW => by
  simp only [addConst, h d hd r hr hW]

theorem addConst_add_ofFun (x : FieldSample) (φ : ℂ → ℝ) (c : ℝ) :
    addConst (x + ofFun φ) c = addConst x c + ofFun φ := by
  funext μ
  simp only [addConst, Pi.add_apply]
  ring

/-- `ψ` and a cutoff `φ` of it: `y + ψ` and `y + φ` agree on circles in the open `thickening`. -/
theorem circAgree_add_ofFun_cutoff {y : FieldSample} {ψ φ : ℂ → ℝ} {δ : ℝ} {K : Set ℂ}
    (hφψ : EqOn φ ψ (cthickening δ K)) :
    CircAgree (thickening δ K) (y + ofFun ψ) (y + ofFun φ) := by
  refine FcAgree.circAgree fun d hd r hr hW => ?_
  simp only [Pi.add_apply, ofFun]
  congr 1
  refine integral_congr_ae ((ae_fc_mem_ball_inter hd hr).mono fun u hu => ?_)
  exact (hφψ (thickening_subset_cthickening δ K (hW hu))).symm

end G

end Prop16Area

end QuantumZipper
