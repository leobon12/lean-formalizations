import QuantumZipper.Proofs.Zipper.RegContDet

/-!
# JOINTMOD, deterministic input: joint continuity of the unzip maps in `(t, u)`

For a continuous driver `W` with `W 0 = 0`, the maps `(t, u) ↦ ψ_t(u) = fwdMapInv W t u` and
`(t, u) ↦ log ‖ψ_t'(u)‖` are jointly continuous on `[0,T] × ℍ`
(`continuousOn_fwdMapInv_joint`, `continuousOn_log_deriv_fwdMapInv_joint`). These are the
continuity inputs of `DetContStmt` (the deterministic part of the raw values, `JointModAssembly`).

Proof: the time-displacement bounds `RegCont.norm_fwdMapInv_add_sub_le` and
`RegCont.abs_log_deriv_fwdMapInv_add_sub_le` are uniform on `{Im u ≥ δ}`, so the time modulus is
uniform there (`flow_modulus`, the argument of `RegCont.continuousOn_of_flow_bound` made uniform);
combined with the continuity in `u` at fixed time (holomorphy of the reverse map) this gives
joint continuity (`continuousOn_joint_of_flow`). **Own elementary argument.**
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint UnzipInvariance

variable {W : ℝ → ℝ}

/-- **Uniform time modulus** from a uniform displacement bound. -/
theorem flow_modulus {ι E : Type*} [PseudoMetricSpace E] (hW : Continuous W) {T C : ℝ}
    {f : ι → ℝ → E}
    (hf : ∀ i, ∀ s h ε : ℝ, 0 ≤ s → 0 ≤ h → s + h ≤ T → 0 ≤ ε →
      (∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε) →
        dist (f i (s + h)) (f i s) ≤ C * (ε + h)) :
    ∀ η > 0, ∃ θ > 0, ∀ i, ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T, dist x y < θ →
      dist (f i x) (f i y) < η := by
  intro η hη
  set C' := |C| + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  set ε₀ := η / (2 * C') with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  have hU := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hW.continuousOn
  obtain ⟨δ₁, hδ₁, hU'⟩ := Metric.uniformContinuousOn_iff.1 hU ε₀ hε₀0
  have step : ∀ i, ∀ x y, x ∈ Icc (0 : ℝ) T → y ∈ Icc (0 : ℝ) T → x ≤ y → y - x < δ₁ →
      y - x < ε₀ → dist (f i y) (f i x) < η := by
    intro i x y hx hy hxy h1 h2
    have hosc : ∀ q ∈ Icc (0 : ℝ) (y - x), |W (x + (y - x) - q) - W (x + (y - x))| ≤ ε₀ := by
      intro q hq
      have e : x + (y - x) = y := by ring
      rw [e]
      have hmem : y - q ∈ Icc (0 : ℝ) T := ⟨by linarith [hq.2, hx.1], by linarith [hq.1, hy.2]⟩
      have hd : dist (y - q) y < δ₁ := by
        rw [Real.dist_eq, show y - q - y = -q by ring, abs_neg, abs_of_nonneg hq.1]
        linarith [hq.2]
      have := hU' (y - q) hmem y hy hd
      rw [Real.dist_eq] at this
      exact this.le
    have hb := hf i x (y - x) ε₀ hx.1 (by linarith) (by linarith [hy.2]) hε₀0.le hosc
    rw [show x + (y - x) = y by ring] at hb
    refine hb.trans_lt ?_
    have hpos : 0 < ε₀ + (y - x) := by linarith
    calc C * (ε₀ + (y - x)) ≤ |C| * (ε₀ + (y - x)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hpos.le
      _ ≤ C' * (ε₀ + (y - x)) := mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ < C' * (2 * ε₀) := mul_lt_mul_of_pos_left (by linarith) hC'0
      _ = η := by rw [hε₀]; field_simp
  refine ⟨min δ₁ ε₀, lt_min hδ₁ hε₀0, fun i a ha b hb hab => ?_⟩
  have hab1 : dist a b < δ₁ := hab.trans_le (min_le_left _ _)
  have hab2 : dist a b < ε₀ := hab.trans_le (min_le_right _ _)
  rcases le_total a b with h | h
  · have hd : b - a = dist a b := by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; ring
    rw [dist_comm]
    exact step i a b ha hb h (hd ▸ hab1) (hd ▸ hab2)
  · have hd : a - b = dist a b := by rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    exact step i b a hb ha h (hd ▸ hab1) (hd ▸ hab2)

/-- **Joint continuity** from continuity in space at fixed time and a displacement bound in time
that is uniform on `{Im u ≥ δ}` for every `δ > 0`. -/
theorem continuousOn_joint_of_flow {E : Type*} [PseudoMetricSpace E] (hW : Continuous W) {T : ℝ}
    {F : ℝ → ℂ → E} (hsp : ∀ t ∈ Icc (0 : ℝ) T, ContinuousOn (F t) H)
    (hfl : ∀ δ > 0, ∃ C : ℝ, ∀ s h ε : ℝ, 0 ≤ s → 0 ≤ h → s + h ≤ T → 0 ≤ ε →
      (∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε) →
        ∀ u ∈ H, δ ≤ u.im → dist (F (s + h) u) (F s u) ≤ C * (ε + h)) :
    ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2) (Icc 0 T ×ˢ H) := by
  rintro ⟨t₀, u₀⟩ ⟨ht₀, hu₀⟩
  have hu₀' : 0 < u₀.im := hu₀
  rw [Metric.continuousWithinAt_iff]
  intro η hη
  set δ := u₀.im / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨C, hC⟩ := hfl δ hδ0
  obtain ⟨θ, hθ, hθ'⟩ := flow_modulus (ι := {u : ℂ // u ∈ H ∧ δ ≤ u.im}) hW (C := C)
    (f := fun i s => F s i.1) (fun i s h ε hs hh hsh hε hosc =>
      hC s h ε hs hh hsh hε hosc i.1 i.2.1 i.2.2) (η / 2) (by positivity)
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousWithinAt_iff.1 (hsp t₀ ht₀ u₀ hu₀) (η / 2)
    (by positivity)
  refine ⟨min θ (min ρ δ), by positivity, ?_⟩
  rintro ⟨t, u⟩ ⟨ht, hu⟩ hd
  have hd' : dist (t, u) (t₀, u₀) < θ := hd.trans_le (min_le_left _ _)
  have hdρ : dist (t, u) (t₀, u₀) < min ρ δ := hd.trans_le (min_le_right _ _)
  rw [Prod.dist_eq, max_lt_iff] at hd' hdρ
  have htt : dist t t₀ < θ := hd'.1
  have huu : dist u u₀ < ρ := hdρ.2.trans_le (min_le_left _ _)
  have huuδ : dist u u₀ < δ := hdρ.2.trans_le (min_le_right _ _)
  have hIm : δ ≤ u.im := by
    have h1 : |u.im - u₀.im| ≤ dist u u₀ := by
      rw [dist_eq_norm, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have := (abs_le.1 h1).1
    linarith
  have e1 : dist (F t u) (F t₀ u) < η / 2 := hθ' ⟨u, hu, hIm⟩ t ht t₀ ht₀ htt
  have e2 : dist (F t₀ u) (F t₀ u₀) < η / 2 := hρ' hu huu
  calc dist (F t u) (F t₀ u₀) ≤ dist (F t u) (F t₀ u) + dist (F t₀ u) (F t₀ u₀) :=
        dist_triangle _ _ _
    _ < η / 2 + η / 2 := add_lt_add e1 e2
    _ = η := by ring

/-- `(t, u) ↦ ψ_t(u)` is jointly continuous on `[0,T] × ℍ`. -/
theorem continuousOn_fwdMapInv_joint (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℂ => fwdMapInv W p.1 p.2) (Icc 0 T ×ˢ H) := by
  refine continuousOn_joint_of_flow hW (fun t ht => ?_) fun δ hδ => ?_
  · refine ((differentiableOn_revMap (vRev W t) (continuous_vRev hW t) ht.1).continuousOn).congr
      fun u hu => fwdMapInv_eq_revMap_timeRev W hW hW0 ht.1 hu
  · refine ⟨(1 + 2 / δ) * Real.exp (2 / δ ^ 2 * |T|), fun s h ε hs hh hsh hε0 hε u hu hδu => ?_⟩
    have hu0 : 0 < u.im := hu
    rw [dist_eq_norm]
    refine (norm_fwdMapInv_add_sub_le hW hW0 hs hh hε hu).trans ?_
    have hsT : s ≤ |T| := (by linarith : s ≤ T).trans (le_abs_self T)
    have hE : Real.exp (2 / u.im ^ 2 * s) ≤ Real.exp (2 / δ ^ 2 * |T|) := by
      refine Real.exp_le_exp.2 (mul_le_mul ?_ hsT hs (by positivity))
      gcongr
    have h1 : ε + 2 * h / u.im ≤ (1 + 2 / δ) * (ε + h) := by
      have e : 2 * h / u.im ≤ 2 / δ * h := by
        rw [show 2 * h / u.im = 2 / u.im * h by ring]
        exact mul_le_mul_of_nonneg_right (by gcongr) hh
      nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ.le]
    calc (ε + 2 * h / u.im) * Real.exp (2 / u.im ^ 2 * s)
        ≤ ((1 + 2 / δ) * (ε + h)) * Real.exp (2 / δ ^ 2 * |T|) :=
          mul_le_mul h1 hE (Real.exp_pos _).le (by positivity)
      _ = (1 + 2 / δ) * Real.exp (2 / δ ^ 2 * |T|) * (ε + h) := by ring

/-- `(t, u) ↦ log ‖ψ_t'(u)‖` is jointly continuous on `[0,T] × ℍ`. -/
theorem continuousOn_log_deriv_fwdMapInv_joint (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℂ => Real.log ‖deriv (fwdMapInv W p.1) p.2‖) (Icc 0 T ×ˢ H) := by
  refine continuousOn_joint_of_flow (F := fun t u => Real.log ‖deriv (fwdMapInv W t) u‖) hW
    (fun t ht => ?_) fun δ hδ => ?_
  · have hV := continuous_vRev hW t
    refine (ContinuousOn.log (((differentiableOn_revMap _ hV ht.1).deriv isOpen_H).continuousOn.norm)
      fun z hz => norm_ne_zero_iff.2 (deriv_revMap_ne_zero _ hV ht.1 hz)).congr fun u hu => ?_
    simp only [deriv_fwdMapInv_eq hW hW0 ht.1 hu]
  · set K := 4 * Real.exp (2 / δ ^ 2 * |T|) / δ ^ 3 * |T| with hK
    have hK0 : 0 ≤ K := by positivity
    refine ⟨K * (1 + 2 / δ) + 2 / δ ^ 2, fun s h ε hs hh hsh hε0 hε u hu hδu => ?_⟩
    have hu0 : 0 < u.im := hu
    rw [Real.dist_eq]
    refine (abs_log_deriv_fwdMapInv_add_sub_le hW hW0 hs hh hε hu).trans ?_
    have hsT : s ≤ |T| := (by linarith : s ≤ T).trans (le_abs_self T)
    have hE : Real.exp (2 / u.im ^ 2 * s) ≤ Real.exp (2 / δ ^ 2 * |T|) := by
      refine Real.exp_le_exp.2 (mul_le_mul ?_ hsT hs (by positivity))
      gcongr
    have h1 : ε + 2 * h / u.im ≤ (1 + 2 / δ) * (ε + h) := by
      have e : 2 * h / u.im ≤ 2 / δ * h := by
        rw [show 2 * h / u.im = 2 / u.im * h by ring]
        exact mul_le_mul_of_nonneg_right (by gcongr) hh
      nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ.le]
    have hA : 4 * Real.exp (2 / u.im ^ 2 * s) / u.im ^ 3 * (ε + 2 * h / u.im) * s ≤
        K * ((1 + 2 / δ) * (ε + h)) := by
      rw [hK]
      have e1 : 4 * Real.exp (2 / u.im ^ 2 * s) / u.im ^ 3 ≤
          4 * Real.exp (2 / δ ^ 2 * |T|) / δ ^ 3 := by
        gcongr
      have hpos : 0 ≤ ε + 2 * h / u.im := by positivity
      calc 4 * Real.exp (2 / u.im ^ 2 * s) / u.im ^ 3 * (ε + 2 * h / u.im) * s
          ≤ 4 * Real.exp (2 / δ ^ 2 * |T|) / δ ^ 3 * ((1 + 2 / δ) * (ε + h)) * |T| := by
            gcongr
        _ = _ := by ring
    have hB : 2 * h / u.im ^ 2 ≤ 2 / δ ^ 2 * (ε + h) := by
      rw [show 2 * h / u.im ^ 2 = 2 / u.im ^ 2 * h by ring]
      calc 2 / u.im ^ 2 * h ≤ 2 / δ ^ 2 * h := mul_le_mul_of_nonneg_right (by gcongr) hh
        _ ≤ 2 / δ ^ 2 * (ε + h) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc _ ≤ K * ((1 + 2 / δ) * (ε + h)) + 2 / δ ^ 2 * (ε + h) := add_le_add hA hB
      _ = (K * (1 + 2 / δ) + 2 / δ ^ 2) * (ε + h) := by ring

/-! ## Continuity of folded-circle means of a time-dependent integrand -/

/-- **Parametric version of `TwoPoint.continuousOn_integral_foldedCircle`**: for `G(t,·)` with
`G` jointly continuous on `[0,T] × ℍ` and a `A + |log Im|` bound uniform in `t ∈ [0,T]`, the
folded-circle means `(t, c, r) ↦ ∫ G(t,·) dfc(c,r)` are jointly continuous. (The proof of
`TwoPoint.continuousOn_integral_foldedCircle`, with the clamped integrand continuous in `(t,u)`.) -/
theorem continuousOn_integral_foldedCircle_param {T : ℝ} (hT : 0 ≤ T) {G : ℝ → ℂ → ℝ}
    (hGm : ∀ t ∈ Icc (0 : ℝ) T, Measurable (G t))
    (hGc : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) (Icc 0 T ×ˢ H))
    (hGb : ∀ R, ∃ A, 0 ≤ A ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ u ∈ H, ‖u‖ ≤ R →
      |G t u| ≤ A + |Real.log u.im|) :
    ContinuousOn (fun p : ℝ × (ℂ × ℝ) => ∫ u, G p.1 u ∂foldedCircle p.2.1 p.2.2)
      (Icc 0 T ×ˢ {p : ℂ × ℝ | 0 < p.2}) := by
  rintro ⟨t₀, c₀, r₀⟩ ⟨ht₀, hr₀⟩
  have hr₀' : 0 < r₀ := hr₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set R := ‖c₀‖ + r₀ + 2 with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨A, hA0, hA⟩ := hGb (2 * R + 1)
  obtain ⟨τ, hτ0, hτ1, hτε⟩ := exists_tail_small (K := 18 * Real.sqrt (2 / r₀))
    (c := 2 * A + 4) (by positivity) (by positivity : 0 < ε / 3)
  set Gτ : ℝ → ℂ → ℝ := fun t u => G (projIcc 0 T hT t) (clampIm τ u) with hGτ
  have hGτc : Continuous fun p : ℝ × ℂ => Gτ p.1 p.2 := by
    have hmap : Continuous (fun p : ℝ × ℂ => (((projIcc 0 T hT p.1 : Icc (0 : ℝ) T) : ℝ),
        clampIm τ p.2)) :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
        ((continuous_clampIm τ).comp continuous_snd)
    exact hGc.comp_continuous hmap fun p => ⟨(projIcc 0 T hT p.1).2,
      show 0 < (clampIm τ p.2).im by rw [clampIm_im]; exact lt_max_of_lt_right hτ0⟩
  have hGτm : ∀ t, Measurable (Gτ t) := fun t =>
    (hGτc.comp (continuous_const.prodMk continuous_id)).measurable
  have hIc : Continuous fun p : ℝ × (ℂ × ℝ) => ∫ u, Gτ p.1 u ∂foldedCircle p.2.1 p.2.2 := by
    have e : (fun p : ℝ × (ℂ × ℝ) => ∫ u, Gτ p.1 u ∂foldedCircle p.2.1 p.2.2) = fun p =>
        (2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), Gτ p.1 (foldH (circleMap p.2.1 p.2.2 θ)) := by
      funext p; rw [integral_foldedCircle_eq (hGτm p.1), integral_Icc_eq_integral_Ico]
    rw [e]
    have hc : Continuous (fun q : (ℝ × (ℂ × ℝ)) × ℝ => circleMap q.1.2.1 q.1.2.2 q.2) := by
      simp only [circleMap]; fun_prop
    exact continuous_const.mul (continuous_parametric_integral_of_continuous
      (f := fun (p : ℝ × (ℂ × ℝ)) (θ : ℝ) => Gτ p.1 (foldH (circleMap p.2.1 p.2.2 θ)))
      (hGτc.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_foldH.comp hc)))
      isCompact_Icc)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1 (hIc.continuousAt (x := (t₀, c₀, r₀)))
    (ε / 3) (by positivity)
  have tail : ∀ q : ℝ × (ℂ × ℝ), q.1 ∈ Icc (0 : ℝ) T → r₀ / 2 ≤ q.2.2 → ‖q.2.1‖ + q.2.2 ≤ R →
      |(∫ u, G q.1 u ∂foldedCircle q.2.1 q.2.2) - ∫ u, Gτ q.1 u ∂foldedCircle q.2.1 q.2.2| <
        ε / 3 := by
    intro q hq0 hq1 hq2
    have hq0' : 0 < q.2.2 := by linarith
    have hGτq : ∀ u, Gτ q.1 u = G q.1 (clampIm τ u) := fun u => by
      simp only [hGτ, projIcc_of_mem hT hq0]
    have hAq := hA q.1 hq0
    have hint1 := integrable_of_log_bound (hGm q.1 hq0) hAq q.2.1 hq0' (by linarith)
    have hint2 : Integrable (Gτ q.1) (foldedCircle q.2.1 q.2.2) := by
      refine (integrable_const (A + |Real.log τ| + |Real.log (2 * R + 1)|)).mono'
        (hGτm q.1).aestronglyMeasurable ?_
      filter_upwards [foldedCircle_ae_norm_le q.2.1 hq0'.le] with u hu
      have hcl : clampIm τ u ∈ H :=
        show 0 < (clampIm τ u).im by rw [clampIm_im]; exact lt_max_of_lt_right hτ0
      have hG2 := hAq _ hcl ((norm_clampIm_le hτ0.le u).trans (by linarith))
      rw [clampIm_im] at hG2
      have hmax : max u.im τ ≤ 2 * R + 1 :=
        max_le (by linarith [Complex.im_le_norm u]) (by linarith)
      have hl := abs_log_le_of_mem hτ0 (le_max_right u.im τ) hmax
      rw [Real.norm_eq_abs, hGτq]
      linarith
    rw [← integral_sub hint1 hint2]
    refine abs_integral_le_integral_abs.trans_lt ?_
    simp_rw [hGτq]
    refine (integral_abs_sub_clamp_le (hGm q.1 hq0) hA0 (R := R) hAq q.2.1 hq0' hτ0 hτ1
      hq2).trans_lt ?_
    refine lt_of_le_of_lt ?_ hτε
    have hs : Real.sqrt (τ / q.2.2) ≤ Real.sqrt (2 / r₀) * Real.sqrt τ := by
      rw [← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      calc τ / q.2.2 ≤ τ / (r₀ / 2) := div_le_div_of_nonneg_left hτ0.le (by positivity) hq1
        _ = 2 / r₀ * τ := by field_simp
    have hf : 0 ≤ 2 * A + 2 * |Real.log τ| + 4 := by positivity
    calc 18 * Real.sqrt (τ / q.2.2) * (2 * A + 2 * |Real.log τ| + 4)
        ≤ 18 * (Real.sqrt (2 / r₀) * Real.sqrt τ) * (2 * A + 2 * |Real.log τ| + 4) := by
          gcongr
      _ = 18 * Real.sqrt (2 / r₀) * Real.sqrt τ * (2 * A + 4 + 2 * |Real.log τ|) := by ring
  refine ⟨min δ₁ (min 1 (r₀ / 2)), by positivity, ?_⟩
  rintro ⟨t, c, r⟩ ⟨ht, -⟩ hp
  have hp1 : dist (t, c, r) (t₀, c₀, r₀) < δ₁ := hp.trans_le (min_le_left _ _)
  have hp2 : dist (t, c, r) (t₀, c₀, r₀) < 1 :=
    hp.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hp3 : dist (t, c, r) (t₀, c₀, r₀) < r₀ / 2 :=
    hp.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have e : dist (t, c, r) (t₀, c₀, r₀) = max (dist t t₀) (max (dist c c₀) (dist r r₀)) := by
    simp only [Prod.dist_eq]
  rw [e] at hp2 hp3
  have hc1 : ‖c - c₀‖ < 1 := by
    rw [← dist_eq_norm]; exact (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hp2)
  have hr1 : |r - r₀| < 1 := by
    rw [← Real.dist_eq]; exact (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hp2)
  have hr2 : |r - r₀| < r₀ / 2 := by
    rw [← Real.dist_eq]; exact (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hp3)
  have hn : ‖c‖ ≤ ‖c₀‖ + ‖c - c₀‖ := by
    have := norm_sub_norm_le c c₀; linarith
  have t1 := abs_lt.1 (tail (t, c, r) ht (by simp only; linarith [(abs_lt.1 hr2).1])
    (by simp only; linarith [(abs_lt.1 hr1).2]))
  have t3 := abs_lt.1 (tail (t₀, c₀, r₀) ht₀ (by simp only; linarith) (by simp only; linarith))
  have t2 : |(∫ u, Gτ t u ∂foldedCircle c r) - ∫ u, Gτ t₀ u ∂foldedCircle c₀ r₀| < ε / 3 := by
    have := hδ₁' hp1; rwa [Real.dist_eq] at this
  have t2' := abs_lt.1 t2
  rw [Real.dist_eq, abs_lt]
  simp only at t1 t3 ⊢
  constructor <;> linarith [t1.1, t1.2, t2'.1, t2'.2, t3.1, t3.2]

end RegUnif
end QuantumZipper
