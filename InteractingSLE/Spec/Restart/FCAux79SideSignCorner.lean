/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCAux79SideSignFlow

/-!
# The orientation of the new piece, III: real touch points of the chart path off the corners

Packet PROVE-FCSIDE (the real-point side condition of `FCAux79.IsFCSideSign`, spec p. 290). For a simple chart path
`γ` with Loewner chart `f_Q` and extended inverse `Φ = Φ_Q`, a real point `γ(σ)`, `σ > 0`, reached at a chart point
`y` strictly between `0` and the image `R̃ = rightImg W 0 Q − W_Q` of `0⁺` is **left** of the seed `0`
(`IsFCLine.re_neg_of_real`); mirror: strictly between `L̃` and `0` it is **right** of the seed
(`IsFCLine.re_pos_of_real`). (At the corners `R̃`, `L̃` the rightmost, leftmost touch points are reached; those are
excluded in `IsFCSideSign`.)

## Proof (positive side)

Suppose `γ(σ) = x' > 0`. The chart points `c ∈ (0, R̃)` go to the path (`mem_γ_of_pos`: a real alive preimage would
have flow value `≥ R̃` or `≤ L̃ ≤ 0`), the points `c > R̃` to alive real points `a > 0` off the path
(`exists_alive_of_gt`), so `x_* = Φ(R̃) = γ(σ_*)` is a real point of the path (`rightImg_point`), and `x' ≤ x_*`
(otherwise an alive `a ∈ (0, x')` close to `x_*` would be trapped by `γ([0, σ])`, which joins `0` and `x'`; trapped
points are not adherent to the unbounded domain, `notMem_closure_of_trap`).
* `x' = x_*`: two chart points `y < R̃` over one positive real point — impossible by the relative fibre lemma
  (`false_of_two_pos`, `false_of_apply_eq_of_lt_rel`: off the point, `γ([0, s])` with the left real ray, `γ([s, Q])`
  with the tip value `Φ(0)`, and real rays are linked).
* `σ > σ_*`: `x' ∈ (0, x_*)` is trapped by `γ([0, σ_*])`, but `x' = Φ(y)` is adherent to the unbounded domain.
* `σ < σ_*`: at the capacity `σ_*` (a later line by `IsFCLine.exists_restrict`) the image of `0⁺` is `0`: otherwise
  `Φ_{σ_*}(R̃_{σ_*}) = x_*` (squeezed by the two trapping arguments) and `Φ_{σ_*}(0) = γ(σ_*) = x_*` contradict the
  relative fibre lemma. The transition `exists_transition` from `Q` to `σ_*` sends `y > 0` to `ξ > 0 = R̃_{σ_*}` with
  `Φ_{σ_*}(ξ) = γ(σ)`; but chart points right of `R̃_{σ_*}` go to alive points off the path.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE

namespace Restart.FCAux79

open Sec7 Sec7.SideHeightBox Supp7 MartChar.RealFlow

/-! ### Real flows and trapped points -/

section Flow

/-- **A real point right of the driver that the flow keeps alive has chart value above the image of `0⁺`**:
`R_t − W_t ≤ Re v_t` (mirror of `SideHeightBox.le_neg_rightImg_of_isForwardSol`). -/
theorem rightImg_sub_le_of_isForwardSol {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {x t : ℝ} (ht : 0 ≤ t)
    (hx : 0 < x) {v : ℝ → ℂ} (hv : QuantumZipper.IsForwardSol W (x : ℂ) t v) :
    rightImg W 0 t - W t ≤ (v t).re := by
  have him : ∀ r ∈ Icc (0 : ℝ) t, (v r).im = 0 := QuantumZipper.im_isForwardSol_real hW ht hv
  have hre : ∀ r ∈ Icc (0 : ℝ) t, 0 < (v r).re :=
    QuantumZipper.re_pos_isForwardSol_real hW ht hv (by rw [hW0]; exact hx)
  set X : ℝ → ℝ := fun r => (v r).re with hXdef
  have hvc : ContinuousOn v (Icc 0 t) := hv.1
  have hX : IsPosSol W x t X := by
    refine ⟨Complex.continuous_re.comp_continuousOn hvc, fun r hr => ⟨hre r hr, ?_⟩⟩
    have hsub : Icc (0 : ℝ) r ⊆ Icc 0 t := Icc_subset_Icc_right hr.2
    have hint : IntervalIntegrable (fun s => 2 / v s) MeasureTheory.volume 0 r := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hr.1]
      exact continuousOn_const.div (hvc.mono hsub) fun s hs => (hv.2 s (hsub hs)).1
    have heq := congrArg Complex.re (hv.2 r hr).2
    have hre_int : (∫ s in (0 : ℝ)..r, 2 / v s).re = ∫ s in (0 : ℝ)..r, (2 / v s).re :=
      (intervalIntegral.intervalIntegral_re hint).symm
    have hcongr : ∫ s in (0 : ℝ)..r, (2 / v s).re = ∫ s in (0 : ℝ)..r, 2 / X s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hr.1] at hs
      have hs' := hsub hs
      have hvs : v s = ((v s).re : ℂ) := Complex.ext (by simp) (by simp [him s hs'])
      show (2 / v s).re = 2 / (v s).re
      conv_lhs => rw [hvs]
      rw [show (2 : ℂ) / ((v s).re : ℂ) = (((2 : ℝ) / (v s).re : ℝ) : ℂ) by push_cast; ring, ofReal_re]
    rw [add_re, sub_re, ofReal_re, ofReal_re, hre_int, hcongr] at heq
    show X r = x - W r + ∫ s in (0 : ℝ)..r, 2 / X s
    exact heq
  have halive : Alive W x t := ⟨X, hX⟩
  have hcf : cflow W x t = X t := cflow_eq_of_isPosSol hW hX ⟨ht, le_rfl⟩
  have hle : rightImg W 0 t ≤ gImg W x t := rightImg_le_gImg hW ht hx halive
  have hg : gImg W x t = W t + X t := by rw [gImg, hcf]
  have hXt : X t = (v t).re := rfl
  linarith

/-- **A trapped real point is not adherent to the unbounded domain.** -/
theorem notMem_closure_of_trap {C : Set ℂ} (hC : IsCompact C) (hCc : IsPreconnected C)
    (hCim : ∀ w ∈ C, 0 ≤ w.im) {u v z : ℝ} (hu : (u : ℂ) ∈ C) (hv : (v : ℂ) ∈ C) (huz : u < z) (hzv : z < v)
    (hz : (z : ℂ) ∉ C) : (z : ℂ) ∉ closure (H \ fillH C) := by
  obtain ⟨ε, hε, hdis⟩ := isTrappedAt_of_isPreconnected hC hCc hCim hu hv huz hzv hz
  intro hcl
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.1 hcl ε hε
  exact Set.disjoint_left.1 hdis (by rw [mem_ball, dist_comm]; exact hwd) hw

end Flow

/-! ### The real points of one chart -/

section Chart

variable {Ω : Type*} {d : PairData Ω} {ω : Ω} {x₁ x₂ : ℝ} {t : ℝ≥0}
  {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}

/-- Every boundary value of `Φ` is adherent to the unbounded domain of the chart path. -/
theorem IsFCLine.extendFrom_mem_closure (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (c : ℝ) :
    extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) c ∈ closure (H \ fillH (γ '' Icc 0 Q)) := by
  have hch := hl.isChart
  have := neBot_nhdsWithin_H_ofReal c
  exact mem_closure_of_tendsto ((hch.inv_cont c (ofReal_mem_Hbar c)).tendsto.mono_left
    (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)) (eventually_nhdsWithin_of_forall fun w hw => hch.inv_mem hw)

/-- **A real point between `0` and a real point of the path, off an initial piece of the path through both, is not
adherent to the unbounded domain.** -/
theorem IsFCLine.notMem_closure_of_lt (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {s : ℝ≥0} (hs : s ≤ Q)
    (hsim : (γ s).im = 0) {z : ℝ} (hz0 : 0 < z) (hzs : z < (γ s).re) (hz : (z : ℂ) ∉ γ '' Icc 0 s) :
    (z : ℂ) ∉ closure (H \ fillH (γ '' Icc 0 Q)) := by
  have hsub : Icc 0 s ⊆ Icc 0 Q := Icc_subset_Icc_right hs
  have hC : IsCompact (γ '' Icc 0 s) := isCompact_Icc.image_of_continuousOn (hl.continuousOn_γ.mono hsub)
  have hCc : IsPreconnected (γ '' Icc 0 s) := isPreconnected_Icc.image _ (hl.continuousOn_γ.mono hsub)
  have hCim : ∀ w ∈ γ '' Icc 0 s, 0 ≤ w.im := by
    rintro _ ⟨s', hs', rfl⟩; exact hl.γ_mem_Hbar (hs'.2.trans hs)
  have h0 : ((0 : ℝ) : ℂ) ∈ γ '' Icc 0 s := ⟨0, ⟨le_rfl, zero_le⟩, by rw [hl.gen.1, ofReal_zero]⟩
  have hv : (((γ s).re : ℝ) : ℂ) ∈ γ '' Icc 0 s := ⟨s, ⟨zero_le, le_rfl⟩, (ofReal_re_of_im hsim).symm⟩
  intro hcl
  refine notMem_closure_of_trap hC hCc hCim h0 hv hz0 hzs hz ?_
  exact closure_mono (sdiff_subset_sdiff_right (fillH_mono (image_mono hsub))) hcl

/-- **Chart points strictly between `0` and the image of `0⁺` go onto the path.** -/
theorem IsFCLine.mem_γ_of_pos (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {c : ℝ} (hc0 : 0 < c)
    (hcR : c < rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q) :
    extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) c ∈ γ '' Icc 0 Q := by
  rcases hl.real_cases c with h | ⟨x, -, u, hu, huQ⟩
  · exact h
  exfalso
  have hQ := Q.coe_nonneg
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h1 := le_neg_rightImg_of_isForwardSol hl.continuous_rdrv hl.rdrv_zero hQ hx hu
    have h2 := le_rightImg (w := fun s : ℝ => -W s.toNNReal) hl.continuous_rdrv.neg 0 hQ
    rw [huQ, ofReal_re] at h1
    simp only [Real.toNNReal_coe] at h1 h2
    linarith
  · exact hl.notMem_γ_of_isForwardSol hu ⟨0, ⟨le_rfl, zero_le⟩, by rw [hl.gen.1, hx, ofReal_zero]⟩
  · have h1 := rightImg_sub_le_of_isForwardSol hl.continuous_rdrv hl.rdrv_zero hQ hx hu
    rw [huQ, ofReal_re] at h1
    simp only [Real.toNNReal_coe] at h1
    linarith

/-- **Chart points right of the image of `0⁺` go to alive real points `a > 0` off the path.** -/
theorem IsFCLine.exists_alive_of_gt (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {c : ℝ}
    (hcR : rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q < c) :
    ∃ a : ℝ, 0 < a ∧ extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) c = a ∧ (a : ℂ) ∉ γ '' Icc 0 Q := by
  obtain ⟨x, hx0, hxa, hxg⟩ := exists_alive_gImg_eq hl.continuous_rdrv Q.coe_nonneg
    (show rightImg (fun s : ℝ => W s.toNNReal) 0 Q < c + W Q by linarith)
  obtain ⟨u, hu, huQ⟩ := exists_isForwardSol_of_alive hl.continuous_rdrv hl.rdrv_zero Q.coe_nonneg hxa
  have h1 := hl.extendFrom_eq_of_isForwardSol hu
  have hval : u Q = (c : ℂ) := by
    rw [huQ, hxg]; simp only [Real.toNNReal_coe]; push_cast; ring
  rw [hval] at h1
  exact ⟨x, hx0, h1, hl.notMem_γ_of_isForwardSol hu⟩

/-- **The image of `0⁺` goes to a real point of the path** (when it is positive). -/
theorem IsFCLine.rightImg_point (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q)
    (hR : 0 < rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q) :
    extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q)
        ((rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q : ℝ) : ℂ) ∈ γ '' Icc 0 Q ∧
      (extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q)
        ((rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q : ℝ) : ℂ)).im = 0 := by
  set R := rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q with hRdef
  set Φ := extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) with hΦdef
  have hch := hl.isChart
  have hΦr : Continuous fun c : ℝ => Φ c := hch.inv_cont.comp_continuous continuous_ofReal ofReal_mem_Hbar
  have hγc : IsCompact (γ '' Icc 0 Q) := isCompact_Icc.image_of_continuousOn hl.continuousOn_γ
  constructor
  · have hlim : Tendsto (fun n : ℕ => R - R / ((n : ℝ) + 2)) atTop (𝓝 R) := by
      have h1 : Tendsto (fun n : ℕ => R / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      simpa using (tendsto_const_nhds (x := R)).sub h1
    refine hγc.isClosed.mem_of_tendsto ((hΦr.tendsto R).comp hlim) (Eventually.of_forall fun n => ?_)
    have hpos : 0 < R / ((n : ℝ) + 2) := div_pos hR (by positivity)
    have hlt : R / ((n : ℝ) + 2) < R := div_lt_self hR (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    exact hl.mem_γ_of_pos (by linarith) (by linarith)
  · have hlim : Tendsto (fun n : ℕ => R + 1 / ((n : ℝ) + 1)) atTop (𝓝 R) := by
      simpa using (tendsto_const_nhds (x := R)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine tendsto_nhds_unique ((continuous_im.tendsto _).comp ((hΦr.tendsto R).comp hlim))
      (tendsto_const_nhds.congr fun n => ?_)
    obtain ⟨a, -, ha, -⟩ := hl.exists_alive_of_gt (c := R + 1 / ((n : ℝ) + 1))
      (by linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)])
    have ha' : Φ ((R + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) = a := ha
    simp only [Function.comp_apply]
    rw [ha', ofReal_im]

/-- **A real point of the path lies left of the image of the corner `R̃`** (every chart point right of `R̃` goes to
an alive real point, and the alive points near `Φ(R̃)` left of a real point `γ(σ)` would be trapped by `γ([0, σ])`). -/
theorem IsFCLine.le_rightImg_point (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {σ : ℝ≥0} (hσ : σ ≤ Q)
    (him : (γ σ).im = 0) :
    (γ σ).re ≤ (extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q)
      ((rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q : ℝ) : ℂ)).re := by
  set R := rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q with hRdef
  set Φ := extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) with hΦdef
  have hch := hl.isChart
  have hΦr : Continuous fun c : ℝ => Φ c := hch.inv_cont.comp_continuous continuous_ofReal ofReal_mem_Hbar
  by_contra hlt
  push Not at hlt
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.continuous_iff.1 hΦr R ((γ σ).re - (Φ R).re) (by linarith)
  have hcR : dist (R + δ / 2) R < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]; exact half_lt_self hδ
  have hd := hδΦ _ hcR
  obtain ⟨a, ha0, ha, hanot⟩ := hl.exists_alive_of_gt (c := R + δ / 2) (by linarith)
  have ha' : Φ ((R + δ / 2 : ℝ) : ℂ) = a := ha
  have hre : |a - (Φ R).re| < (γ σ).re - (Φ R).re := by
    have h1 := Complex.abs_re_le_norm (Φ ↑(R + δ / 2) - Φ R)
    rw [sub_re, ha', ofReal_re] at h1
    rw [dist_eq_norm, ha'] at hd
    linarith
  have haσ : a < (γ σ).re := by linarith [(abs_lt.1 hre).2]
  refine hl.notMem_closure_of_lt hσ him ha0 haσ (fun h => hanot (image_mono (Icc_subset_Icc_right hσ) h)) ?_
  rw [← ha]
  exact hl.extendFrom_mem_closure _

/-- **Two chart points on one side of `0` over one point `γ(σ₀) ≠ 0` of the path** (or over the tip): impossible
(the relative fibre lemma). -/
theorem IsFCLine.false_of_two (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {σ₀ : ℝ≥0} (hσ₀ : σ₀ ≤ Q)
    (hne : γ σ₀ ≠ 0) {y₁ y₂ : ℝ} (hy12 : y₁ < y₂)
    (h1 : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) y₁ = γ σ₀)
    (h2 : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) y₂ = γ σ₀)
    (hside : (0 < y₁ ∨ y₂ < 0) ∨ σ₀ = Q) : False := by
  obtain ⟨hDo, hFd, hFi, hFs, hFbd, hFinf, hDE, hfr⟩ := hl.fibre_hyps
  have hch := hl.isChart
  have hinj : ∀ s ∈ Icc 0 Q, γ s = γ σ₀ → s = σ₀ := fun s hs h =>
    hl.inj ((ENNReal.coe_le_coe.2 hs.2).trans hl.lt.le) ((ENNReal.coe_le_coe.2 hσ₀).trans hl.lt.le) h
  refine false_of_apply_eq_of_lt_rel hDo hFd hch.inv_cont hFi (fun w hw => hch.inv_mem hw) hFs hFbd hFinf hDE hfr
    ?_ hy12 h1 h2
  intro z hz
  rcases hz.1 with hzr | ⟨s, hs, rfl⟩
  · obtain ⟨S, hSs, hSc, hzS, hSb⟩ := exists_ray hzr hz.2
    exact ⟨S, fun w hw => ⟨Or.inl (hSs hw).1, (hSs hw).2⟩, hSc, hzS, Or.inl hSb⟩
  have hsσ : s ≠ σ₀ := fun h => hz.2 (by rw [h]; rfl)
  rcases lt_or_gt_of_ne hsσ with hlt | hgt
  · have h0ne : (0 : ℂ) ≠ γ σ₀ := fun h => hne h.symm
    obtain ⟨S', hS's, hS'c, h0S', hS'b⟩ := exists_ray (c := 0) (q := γ σ₀) (by simp) h0ne
    have hsQ : s ≤ Q := hlt.le.trans hσ₀
    refine ⟨γ '' Icc 0 s ∪ S', ?_, ?_, Or.inl ⟨s, ⟨zero_le, le_rfl⟩, rfl⟩,
      Or.inl fun hb => hS'b (hb.subset subset_union_right)⟩
    · rintro w (⟨s', hs', rfl⟩ | hw)
      · refine ⟨Or.inr ⟨s', ⟨zero_le, hs'.2.trans hsQ⟩, rfl⟩, fun h => ?_⟩
        have := hinj s' ⟨zero_le, hs'.2.trans hsQ⟩ (mem_singleton_iff.1 h)
        exact absurd (this ▸ hs'.2) (not_le.2 hlt)
      · exact ⟨Or.inl (hS's hw).1, (hS's hw).2⟩
    · exact (isPreconnected_Icc.image _ (hl.continuousOn_γ.mono (Icc_subset_Icc_right hsQ))).union 0
        ⟨0, ⟨le_rfl, zero_le⟩, hl.gen.1⟩ h0S' hS'c
  · have hy₁ : 0 < y₁ ∨ y₂ < 0 := hside.resolve_right fun h => absurd hs.2 (not_le.2 (h ▸ hgt))
    refine ⟨γ '' Icc s Q, ?_, isPreconnected_Icc.image _ (hl.continuousOn_γ.mono (Icc_subset_Icc_left zero_le)),
      ⟨s, ⟨le_rfl, hs.2⟩, rfl⟩, Or.inr ⟨0, hy₁, Q, ⟨hs.2, le_rfl⟩, by rw [ofReal_zero, hch.tip]⟩⟩
    rintro w ⟨s', hs', rfl⟩
    refine ⟨Or.inr ⟨s', ⟨zero_le, hs'.2⟩, rfl⟩, fun h => ?_⟩
    have := hinj s' ⟨zero_le, hs'.2⟩ (mem_singleton_iff.1 h)
    exact absurd (this ▸ hs'.1) (not_le.2 hgt)

/-! #### The mirror image: the left side -/

/-- Mirror of `notMem_closure_of_lt`: a real point between a negative real point of the path and `0`. -/
theorem IsFCLine.notMem_closure_of_gt (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {s : ℝ≥0} (hs : s ≤ Q)
    (hsim : (γ s).im = 0) {z : ℝ} (hz0 : z < 0) (hzs : (γ s).re < z) (hz : (z : ℂ) ∉ γ '' Icc 0 s) :
    (z : ℂ) ∉ closure (H \ fillH (γ '' Icc 0 Q)) := by
  have hsub : Icc 0 s ⊆ Icc 0 Q := Icc_subset_Icc_right hs
  have hC : IsCompact (γ '' Icc 0 s) := isCompact_Icc.image_of_continuousOn (hl.continuousOn_γ.mono hsub)
  have hCc : IsPreconnected (γ '' Icc 0 s) := isPreconnected_Icc.image _ (hl.continuousOn_γ.mono hsub)
  have hCim : ∀ w ∈ γ '' Icc 0 s, 0 ≤ w.im := by
    rintro _ ⟨s', hs', rfl⟩; exact hl.γ_mem_Hbar (hs'.2.trans hs)
  have h0 : ((0 : ℝ) : ℂ) ∈ γ '' Icc 0 s := ⟨0, ⟨le_rfl, zero_le⟩, by rw [hl.gen.1, ofReal_zero]⟩
  have hu : (((γ s).re : ℝ) : ℂ) ∈ γ '' Icc 0 s := ⟨s, ⟨zero_le, le_rfl⟩, (ofReal_re_of_im hsim).symm⟩
  intro hcl
  refine notMem_closure_of_trap hC hCc hCim hu h0 hzs hz0 hz ?_
  exact closure_mono (sdiff_subset_sdiff_right (fillH_mono (image_mono hsub))) hcl

/-- Mirror of `mem_γ_of_pos`: chart points strictly between the image of `0⁻` and `0` go onto the path. -/
theorem IsFCLine.mem_γ_of_neg (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {c : ℝ}
    (hcL : -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q < c) (hc0 : c < 0) :
    extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) c ∈ γ '' Icc 0 Q := by
  rcases hl.real_cases c with h | ⟨x, -, u, hu, huQ⟩
  · exact h
  exfalso
  have hQ := Q.coe_nonneg
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h1 := le_neg_rightImg_of_isForwardSol hl.continuous_rdrv hl.rdrv_zero hQ hx hu
    rw [huQ, ofReal_re] at h1
    simp only [Real.toNNReal_coe] at h1
    linarith
  · exact hl.notMem_γ_of_isForwardSol hu ⟨0, ⟨le_rfl, zero_le⟩, by rw [hl.gen.1, hx, ofReal_zero]⟩
  · have h1 := rightImg_sub_le_of_isForwardSol hl.continuous_rdrv hl.rdrv_zero hQ hx hu
    have h2 := le_rightImg (w := fun s : ℝ => W s.toNNReal) hl.continuous_rdrv 0 hQ
    rw [huQ, ofReal_re] at h1
    simp only [Real.toNNReal_coe] at h1 h2
    linarith

/-- Mirror of `exists_alive_of_gt`: chart points left of the image of `0⁻` go to alive real points `a < 0`. -/
theorem IsFCLine.exists_alive_of_lt (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {c : ℝ}
    (hcL : c < -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q) :
    ∃ a : ℝ, a < 0 ∧ extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) c = a ∧ (a : ℂ) ∉ γ '' Icc 0 Q := by
  have hwn : Continuous fun s : ℝ => -W s.toNNReal := hl.continuous_rdrv.neg
  obtain ⟨x, hx0, hxa, hxg⟩ := exists_alive_gImg_eq hwn Q.coe_nonneg
    (show rightImg (fun s : ℝ => -W s.toNNReal) 0 Q < -c - W Q by linarith)
  obtain ⟨u, hu, huQ⟩ := exists_isForwardSol_of_alive hwn (by simp [hl.zero]) Q.coe_nonneg hxa
  have hu' := QuantumZipper.RS.isForwardSol_neg hu
  have hdrv : (fun t => -(fun s : ℝ => -W s.toNNReal) t) = fun s : ℝ => W s.toNNReal := by
    funext s; simp
  rw [hdrv, show -((x : ℝ) : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring] at hu'
  have h1 := hl.extendFrom_eq_of_isForwardSol hu'
  have hval : -u Q = (c : ℂ) := by
    rw [huQ, hxg]; simp only [Real.toNNReal_coe]; push_cast; ring
  simp only [hval] at h1
  exact ⟨-x, by linarith, h1, hl.notMem_γ_of_isForwardSol hu'⟩

/-- Mirror of `rightImg_point`: the image of `0⁻` goes to a real point of the path (when it is negative). -/
theorem IsFCLine.leftImg_point (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q)
    (hL : -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q < 0) :
    extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q)
        ((-rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q : ℝ) : ℂ) ∈ γ '' Icc 0 Q ∧
      (extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q)
        ((-rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q : ℝ) : ℂ)).im = 0 := by
  set L := -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q with hLdef
  set Φ := extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) with hΦdef
  have hch := hl.isChart
  have hΦr : Continuous fun c : ℝ => Φ c := hch.inv_cont.comp_continuous continuous_ofReal ofReal_mem_Hbar
  have hγc : IsCompact (γ '' Icc 0 Q) := isCompact_Icc.image_of_continuousOn hl.continuousOn_γ
  constructor
  · have hlim : Tendsto (fun n : ℕ => L - L / ((n : ℝ) + 2)) atTop (𝓝 L) := by
      have h1 : Tendsto (fun n : ℕ => L / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      simpa using (tendsto_const_nhds (x := L)).sub h1
    refine hγc.isClosed.mem_of_tendsto ((hΦr.tendsto L).comp hlim) (Eventually.of_forall fun n => ?_)
    have hneg : L / ((n : ℝ) + 2) < 0 := div_neg_of_neg_of_pos hL (by positivity)
    have hgt : L < L / ((n : ℝ) + 2) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact hl.mem_γ_of_neg (by linarith) (by linarith)
  · have hlim : Tendsto (fun n : ℕ => L - 1 / ((n : ℝ) + 1)) atTop (𝓝 L) := by
      simpa using (tendsto_const_nhds (x := L)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine tendsto_nhds_unique ((continuous_im.tendsto _).comp ((hΦr.tendsto L).comp hlim))
      (tendsto_const_nhds.congr fun n => ?_)
    obtain ⟨a, -, ha, -⟩ := hl.exists_alive_of_lt (c := L - 1 / ((n : ℝ) + 1))
      (by linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)])
    have ha' : Φ ((L - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) = a := ha
    simp only [Function.comp_apply]
    rw [ha', ofReal_im]

/-- Mirror of `le_rightImg_point`: a real point of the path lies right of the image of the corner `L̃`. -/
theorem IsFCLine.leftImg_point_le (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {σ : ℝ≥0} (hσ : σ ≤ Q)
    (him : (γ σ).im = 0) :
    (extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q)
      ((-rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q : ℝ) : ℂ)).re ≤ (γ σ).re := by
  set L := -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q with hLdef
  set Φ := extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) with hΦdef
  have hch := hl.isChart
  have hΦr : Continuous fun c : ℝ => Φ c := hch.inv_cont.comp_continuous continuous_ofReal ofReal_mem_Hbar
  by_contra hlt
  push Not at hlt
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.continuous_iff.1 hΦr L ((Φ L).re - (γ σ).re) (by linarith)
  have hcL : dist (L - δ / 2) L < δ := by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hδ)]; exact half_lt_self hδ
  have hd := hδΦ _ hcL
  obtain ⟨a, ha0, ha, hanot⟩ := hl.exists_alive_of_lt (c := L - δ / 2) (by linarith)
  have ha' : Φ ((L - δ / 2 : ℝ) : ℂ) = a := ha
  have hre : |a - (Φ L).re| < (Φ L).re - (γ σ).re := by
    have h1 := Complex.abs_re_le_norm (Φ ↑(L - δ / 2) - Φ L)
    rw [sub_re, ha', ofReal_re] at h1
    rw [dist_eq_norm, ha'] at hd
    linarith
  have haσ : (γ σ).re < a := by linarith [(abs_lt.1 hre).1]
  refine hl.notMem_closure_of_gt hσ him ha0 haσ (fun h => hanot (image_mono (Icc_subset_Icc_right hσ) h)) ?_
  rw [← ha]
  exact hl.extendFrom_mem_closure _

end Chart

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} {ω : Ω} {x₁ x₂ : ℝ} {t : ℝ≥0}
  {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}

omit [MeasurableSpace Ω] in
/-- **At a touch capacity right of the seed the image of `0⁺` is `0`.** If `γ(τ)` is a positive real point which is
also `Φ_Q(R̃_Q)` for a later capacity `Q ≥ τ`, then `R̃_τ ≤ 0`. -/
theorem IsFCLine.rightImg_le_zero_of_touch (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {τ : ℝ≥0} (hτQ : τ ≤ Q)
    {t' : ℝ≥0} (hlτ : IsFCLine d ω x₁ x₂ t' W γ ζc τ) (hτim : (γ τ).im = 0) (hτpos : 0 < (γ τ).re)
    (hτR : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q)
      ((rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q : ℝ) : ℂ) = γ τ) :
    rightImg (fun s : ℝ => W s.toNNReal) 0 τ - W τ ≤ 0 := by
  by_contra hBpos
  push Not at hBpos
  set Rτ := rightImg (fun s : ℝ => W s.toNNReal) 0 τ - W τ with hRτ
  set Φτ := extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) τ) with hΦτ
  obtain ⟨⟨s'', hs'', hs''e⟩, hRτim⟩ := hlτ.rightImg_point hBpos
  have h1 := hlτ.le_rightImg_point (le_refl τ) hτim
  rcases eq_or_lt_of_le h1 with h2 | h2
  · have hΦτR : Φτ ((Rτ : ℝ) : ℂ) = γ τ := Complex.ext h2.symm (hRτim.trans hτim.symm)
    exact hlτ.false_of_two (le_refl τ) (fun h => by rw [h, zero_re] at hτpos; exact lt_irrefl _ hτpos) hBpos
      (by rw [ofReal_zero]; exact hlτ.isChart.tip) hΦτR (Or.inr rfl)
  · have hs''τ : s'' < τ := by
      refine lt_of_le_of_ne hs''.2 fun h => ?_
      rw [h] at hs''e
      rw [← hs''e] at h2
      exact lt_irrefl _ h2
    have hs''im : (γ s'').im = 0 := by rw [hs''e]; exact hRτim
    have hnot : (((γ τ).re : ℝ) : ℂ) ∉ γ '' Icc 0 s'' := by
      rintro ⟨s', hs', he⟩
      rw [ofReal_re_of_im hτim] at he
      have := hl.inj ((ENNReal.coe_le_coe.2 ((hs'.2.trans hs''τ.le).trans hτQ)).trans hl.lt.le)
        ((ENNReal.coe_le_coe.2 hτQ).trans hl.lt.le) he
      exact absurd (this ▸ hs'.2) (not_le.2 hs''τ)
    have hcl : (((γ τ).re : ℝ) : ℂ) ∈ closure (H \ fillH (γ '' Icc 0 Q)) := by
      rw [ofReal_re_of_im hτim, ← hτR]
      exact hl.extendFrom_mem_closure _
    exact hl.notMem_closure_of_lt (hs''.2.trans hτQ) hs''im hτpos (by rw [hs''e]; exact h2) hnot hcl

/-- **A real point of the path reached strictly between `0` and the image of `0⁺` lies left of the seed.** -/
theorem IsFCLine.re_neg_of_real (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) {y : ℝ} {σ : ℝ≥0}
    (hσ0 : 0 < σ) (hσQ : σ ≤ Q) (hy0 : 0 < y) (hyR : y < rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q)
    (hy : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) y = γ σ) (him : (γ σ).im = 0) :
    (γ σ).re < 0 := by
  set R := rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q with hRdef
  set Φ := extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) with hΦdef
  have hR : 0 < R := hy0.trans hyR
  have hinj : ∀ a b : ℝ≥0, a ≤ Q → b ≤ Q → γ a = γ b → a = b := fun a b ha hb h =>
    hl.inj ((ENNReal.coe_le_coe.2 ha).trans hl.lt.le) ((ENNReal.coe_le_coe.2 hb).trans hl.lt.le) h
  have hne : (γ σ).re ≠ 0 := by
    intro h0
    have : γ σ = γ 0 := by rw [hl.gen.1, ← ofReal_re_of_im him, h0, ofReal_zero]
    exact (ne_of_gt hσ0) (hinj σ 0 hσQ zero_le this)
  refine lt_of_le_of_ne (not_lt.1 fun hpos => ?_) hne
  obtain ⟨⟨σs, hσs, hσse⟩, hRim⟩ := hl.rightImg_point hR
  have hxs := hl.le_rightImg_point hσQ him
  have hγσs_im : (γ σs).im = 0 := by rw [hσse]; exact hRim
  rcases eq_or_lt_of_le hxs with heq | hlt
  · -- `Φ(R̃) = γ(σ)`: two chart points over one positive real point
    have hΦR : Φ ((R : ℝ) : ℂ) = γ σ := Complex.ext heq.symm (hRim.trans him.symm)
    exact hl.false_of_two hσQ (fun h => by rw [h, zero_re] at hpos; exact lt_irrefl _ hpos) hyR hy hΦR
      (Or.inl (Or.inl hy0))
  rcases lt_trichotomy σ σs with hss | hss | hss
  · -- a later touch at `σs`: the image of `0⁺` vanishes there
    have hτ0 : 0 < σs := hσ0.trans hss
    obtain ⟨t', -, -, hlτ⟩ := hl.exists_restrict hd hτ0 hσs.2
    obtain ⟨ξ, -, hΦξ, hξpos, -⟩ := exists_transition hl.gen hl.cont hl.zero hl.inj hτ0 hσs.2 hl.lt hss hy
    have hxspos : 0 < (γ σs).re := by rw [hσse]; linarith
    have hB := hl.rightImg_le_zero_of_touch hσs.2 hlτ hγσs_im hxspos hσse.symm
    obtain ⟨a, -, ha, hanot⟩ := hlτ.exists_alive_of_gt (lt_of_le_of_lt hB (hξpos hy0))
    rw [hΦξ] at ha
    exact hanot (ha ▸ ⟨σ, ⟨zero_le, hss.le⟩, rfl⟩)
  · subst hss
    rw [hσse] at hlt
    exact lt_irrefl _ hlt
  · -- an earlier touch at `σs` traps `γ(σ)`
    have hnot : (((γ σ).re : ℝ) : ℂ) ∉ γ '' Icc 0 σs := by
      rintro ⟨s', hs', he⟩
      rw [ofReal_re_of_im him] at he
      have := hinj s' σ (hs'.2.trans hσs.2) hσQ he
      exact absurd (this ▸ hs'.2) (not_le.2 hss)
    have hcl : (((γ σ).re : ℝ) : ℂ) ∈ closure (H \ fillH (γ '' Icc 0 Q)) := by
      rw [ofReal_re_of_im him, ← hy]
      exact hl.extendFrom_mem_closure y
    exact hl.notMem_closure_of_lt hσs.2 hγσs_im hpos (by rw [hσse]; exact hlt) hnot hcl

omit [MeasurableSpace Ω] in
/-- Mirror of `rightImg_le_zero_of_touch`: at a touch capacity left of the seed the image of `0⁻` is `0`. -/
theorem IsFCLine.leftImg_ge_zero_of_touch (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {τ : ℝ≥0} (hτQ : τ ≤ Q)
    {t' : ℝ≥0} (hlτ : IsFCLine d ω x₁ x₂ t' W γ ζc τ) (hτim : (γ τ).im = 0) (hτneg : (γ τ).re < 0)
    (hτL : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q)
      ((-rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q : ℝ) : ℂ) = γ τ) :
    0 ≤ -rightImg (fun s : ℝ => -W s.toNNReal) 0 τ - W τ := by
  by_contra hBneg
  push Not at hBneg
  set Lτ := -rightImg (fun s : ℝ => -W s.toNNReal) 0 τ - W τ with hLτ
  set Φτ := extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) τ) with hΦτ
  obtain ⟨⟨s'', hs'', hs''e⟩, hLτim⟩ := hlτ.leftImg_point hBneg
  have h1 := hlτ.leftImg_point_le (le_refl τ) hτim
  rcases eq_or_lt_of_le h1 with h2 | h2
  · have hΦτL : Φτ ((Lτ : ℝ) : ℂ) = γ τ := Complex.ext h2 (hLτim.trans hτim.symm)
    exact hlτ.false_of_two (le_refl τ) (fun h => by rw [h, zero_re] at hτneg; exact lt_irrefl _ hτneg) hBneg
      hΦτL (by rw [ofReal_zero]; exact hlτ.isChart.tip) (Or.inr rfl)
  · have hs''τ : s'' < τ := by
      refine lt_of_le_of_ne hs''.2 fun h => ?_
      rw [h] at hs''e
      rw [← hs''e] at h2
      exact lt_irrefl _ h2
    have hs''im : (γ s'').im = 0 := by rw [hs''e]; exact hLτim
    have hnot : (((γ τ).re : ℝ) : ℂ) ∉ γ '' Icc 0 s'' := by
      rintro ⟨s', hs', he⟩
      rw [ofReal_re_of_im hτim] at he
      have := hl.inj ((ENNReal.coe_le_coe.2 ((hs'.2.trans hs''τ.le).trans hτQ)).trans hl.lt.le)
        ((ENNReal.coe_le_coe.2 hτQ).trans hl.lt.le) he
      exact absurd (this ▸ hs'.2) (not_le.2 hs''τ)
    have hcl : (((γ τ).re : ℝ) : ℂ) ∈ closure (H \ fillH (γ '' Icc 0 Q)) := by
      rw [ofReal_re_of_im hτim, ← hτL]
      exact hl.extendFrom_mem_closure _
    exact hl.notMem_closure_of_gt (hs''.2.trans hτQ) hs''im hτneg (by rw [hs''e]; exact h2) hnot hcl

/-- **A real point of the path reached strictly between the image of `0⁻` and `0` lies right of the seed** (the
mirror image of `re_neg_of_real`). -/
theorem IsFCLine.re_pos_of_real (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) {y : ℝ} {σ : ℝ≥0}
    (hσ0 : 0 < σ) (hσQ : σ ≤ Q) (hyL : -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q < y) (hy0 : y < 0)
    (hy : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) y = γ σ) (him : (γ σ).im = 0) :
    0 < (γ σ).re := by
  set L := -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q with hLdef
  set Φ := extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) with hΦdef
  have hL : L < 0 := hyL.trans hy0
  have hinj : ∀ a b : ℝ≥0, a ≤ Q → b ≤ Q → γ a = γ b → a = b := fun a b ha hb h =>
    hl.inj ((ENNReal.coe_le_coe.2 ha).trans hl.lt.le) ((ENNReal.coe_le_coe.2 hb).trans hl.lt.le) h
  have hne : (γ σ).re ≠ 0 := by
    intro h0
    have : γ σ = γ 0 := by rw [hl.gen.1, ← ofReal_re_of_im him, h0, ofReal_zero]
    exact (ne_of_gt hσ0) (hinj σ 0 hσQ zero_le this)
  refine lt_of_le_of_ne (not_lt.1 fun hneg => ?_) (Ne.symm hne)
  have hneg' : (γ σ).re < 0 := hneg
  obtain ⟨⟨σs, hσs, hσse⟩, hLim⟩ := hl.leftImg_point hL
  have hxs := hl.leftImg_point_le hσQ him
  have hγσs_im : (γ σs).im = 0 := by rw [hσse]; exact hLim
  rcases eq_or_lt_of_le hxs with heq | hlt
  · have hΦL : Φ ((L : ℝ) : ℂ) = γ σ := Complex.ext heq (hLim.trans him.symm)
    exact hl.false_of_two hσQ (fun h => by rw [h, zero_re] at hneg'; exact lt_irrefl _ hneg') hyL hΦL hy
      (Or.inl (Or.inr hy0))
  rcases lt_trichotomy σ σs with hss | hss | hss
  · have hτ0 : 0 < σs := hσ0.trans hss
    obtain ⟨t', -, -, hlτ⟩ := hl.exists_restrict hd hτ0 hσs.2
    obtain ⟨ξ, -, hΦξ, -, hξneg⟩ := exists_transition hl.gen hl.cont hl.zero hl.inj hτ0 hσs.2 hl.lt hss hy
    have hxsneg : (γ σs).re < 0 := by rw [hσse]; linarith
    have hB := hl.leftImg_ge_zero_of_touch hσs.2 hlτ hγσs_im hxsneg hσse.symm
    obtain ⟨a, -, ha, hanot⟩ := hlτ.exists_alive_of_lt (lt_of_lt_of_le (hξneg hy0) hB)
    rw [hΦξ] at ha
    exact hanot (ha ▸ ⟨σ, ⟨zero_le, hss.le⟩, rfl⟩)
  · subst hss
    rw [hσse] at hlt
    exact lt_irrefl _ hlt
  · have hnot : (((γ σ).re : ℝ) : ℂ) ∉ γ '' Icc 0 σs := by
      rintro ⟨s', hs', he⟩
      rw [ofReal_re_of_im him] at he
      have := hinj s' σ (hs'.2.trans hσs.2) hσQ he
      exact absurd (this ▸ hs'.2) (not_le.2 hss)
    have hcl : (((γ σ).re : ℝ) : ℂ) ∈ closure (H \ fillH (γ '' Icc 0 Q)) := by
      rw [ofReal_re_of_im him, ← hy]
      exact hl.extendFrom_mem_closure y
    exact hl.notMem_closure_of_gt hσs.2 hγσs_im hneg' (by rw [hσse]; exact hlt) hnot hcl

end Main

end Restart.FCAux79

end InteractingSLE
