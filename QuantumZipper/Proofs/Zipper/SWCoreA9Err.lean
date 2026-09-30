import QuantumZipper.Proofs.Zipper.SWCoreA9Path

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A9 (4): the offset distortion bound for `𝔥₀ + X₀` along the flow (pathwise)

`a9_pushErrR_path`: see the docstring of `SWCoreA9Path.lean` (proof plan there). Sheffield–Wang,
arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7); own bookkeeping, mirrors `a8_pushErr_wedge`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace SWCore

/-- The offset distortion error as a function of `(t, z, α)`, through the regular witnesses. -/
def a9Err (γ : ℝ) (Zh : ℝ × (ℂ × ℝ) → ℝ) (Fx : ℂ × ℝ → ℝ) (W : ℝ → ℝ) (r : ℝ)
    (p : ℝ × ℂ × ℝ) : ℝ :=
  Zh (p.1, (p.2.1, p.2.2 * r)) - Qc γ * Real.log ‖deriv (fwdMapInv W p.1) p.2.1‖ -
    Fx (fwdMapInv W p.1 p.2.1, p.2.2 * r * ‖deriv (fwdMapInv W p.1) p.2.1‖)

/-- Continuity of the error in `(t, z, α)`. -/
theorem a9_err_cont (γ : ℝ) {Fx : ℂ × ℝ → ℝ} (hFx : ContinuousOn Fx (Hbar ×ˢ Ioi 0))
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    {K : Set ℂ} (hKH : K ⊆ H) {Zh : ℝ × (ℂ × ℝ) → ℝ} (hZc : ContinuousOn Zh (RegUnif.parSet T))
    {r : ℝ} (hr : 0 < r)
    (hdpos : ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ K, 0 < ‖deriv (fwdMapInv W t) z‖) :
    ContinuousOn (a9Err γ Zh Fx W r) (Icc (0 : ℝ) T ×ˢ (K ×ˢ Icc (1 : ℝ) 2)) := by
  unfold a9Err
  have hHHbar : H ⊆ Hbar := fun w hw => le_of_lt (show 0 < w.im from hw)
  have hf1 : Continuous fun p : ℝ × ℂ × ℝ => (p.1, (p.2.1, p.2.2 * r)) := by fun_prop
  have hm1 : MapsTo (fun p : ℝ × ℂ × ℝ => (p.1, (p.2.1, p.2.2 * r)))
      (Icc (0 : ℝ) T ×ˢ (K ×ˢ Icc (1 : ℝ) 2)) (RegUnif.parSet T) := by
    intro p hp
    have hp1 : p.2.2 * r ∈ Ioi (0 : ℝ) := mul_pos (by linarith [hp.2.2.1]) hr
    exact ⟨hp.1, hHHbar (hKH hp.2.1), hp1⟩
  have h1 := ContinuousOn.comp hZc hf1.continuousOn hm1
  have hf2 : Continuous fun p : ℝ × ℂ × ℝ => (p.1, p.2.1) := by fun_prop
  have hm2 : MapsTo (fun p : ℝ × ℂ × ℝ => (p.1, p.2.1))
      (Icc (0 : ℝ) T ×ˢ (K ×ˢ Icc (1 : ℝ) 2)) (Icc 0 T ×ˢ H) :=
    fun p hp => ⟨hp.1, hKH hp.2.1⟩
  have h2 := ContinuousOn.comp (RegUnif.continuousOn_log_deriv_fwdMapInv_joint hW hW0 T)
    hf2.continuousOn hm2
  have hψc := ContinuousOn.comp (RegUnif.continuousOn_fwdMapInv_joint hW hW0 T)
    hf2.continuousOn hm2
  have hd : ContinuousOn (fun p : ℝ × ℂ × ℝ => ‖deriv (fwdMapInv W p.1) p.2.1‖)
      (Icc (0 : ℝ) T ×ˢ (K ×ˢ Icc (1 : ℝ) 2)) :=
    (Real.continuous_exp.comp_continuousOn h2).congr fun p hp => by
      simp only [Function.comp_def]
      rw [Real.exp_log (hdpos p.1 hp.1 p.2.1 hp.2.1)]
  have hf3 : Continuous fun p : ℝ × ℂ × ℝ => p.2.2 * r := by fun_prop
  have h3 := hψc.prodMk (hf3.continuousOn.mul hd)
  have hm3 : MapsTo (fun p : ℝ × ℂ × ℝ => (fwdMapInv W p.1 p.2.1,
      p.2.2 * r * ‖deriv (fwdMapInv W p.1) p.2.1‖))
      (Icc (0 : ℝ) T ×ˢ (K ×ˢ Icc (1 : ℝ) 2)) (Hbar ×ˢ Ioi 0) := by
    intro p hp
    exact ⟨hHHbar (RS.fwdMapInv_mem_H hW hW0 hp.1.1 (hKH hp.2.1)),
      mul_pos (mul_pos (by linarith [hp.2.2.1]) hr) (hdpos p.1 hp.1 p.2.1 hp.2.1)⟩
  have h4 := ContinuousOn.comp hFx h3 hm3
  exact (h1.sub (continuousOn_const.mul h2)).sub h4

set_option maxHeartbeats 800000 in
-- one long bookkeeping proof (continuity of the error, add-ons at rational points)
/-- **Offset distortion bound for `𝔥₀ + X₀` along the Loewner flow** (pathwise). -/
theorem a9_pushErrR_path (κ γ : ℝ) {X0 : FieldSample} {FX Fx : ℂ × ℝ → ℝ}
    (hFX : IsRegularWith X0 FX) (hFx : IsRegularWith (ofFun (h0rev κ) + X0) Fx)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {Tq : ℚ} (hT : (0 : ℝ) ≤ Tq)
    {A B C D : ℚ} (hAB : (A : ℝ) ≤ B) (hC : (0 : ℝ) < C) (hCD : (C : ℝ) ≤ D)
    {Zh : ℝ × (ℂ × ℝ) → ℝ} (hZc : ContinuousOn Zh (RegUnif.parSet Tq))
    (hreg : ∀ t ∈ Icc (0 : ℝ) Tq,
      IsRegularWith (unzippedField γ (ofFun (h0rev κ) + X0, W) t) (fun p => Zh (t, p)))
    (hrat : ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) Tq → ∀ z : ℚ × ℚ, zQ z ∈ rectC (A : ℝ) B C D →
      ∀ α : ℚ, (α : ℝ) ∈ Icc (1 : ℝ) 2 → ∀ k : ℕ,
        Zh ((q : ℝ), (zQ z, (α : ℝ) * radius k)) =
          unzippedField γ (ofFun (h0rev κ) + X0, W) q
            (foldedCircle (zQ z) ((α : ℝ) * radius k)))
    (hD : A9Data X0 W Tq A B C D) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) Tq, ∀ α ∈ Icc (1 : ℝ) 2,
      ∀ z ∈ rectC (A : ℝ) B C D,
        |pushErrR γ (ofFun (h0rev κ) + X0) (fwdMapInv W t) (α * radius k) z| ≤ η := by
  intro η hη
  set x := ofFun (h0rev κ) + X0 with hxdef
  set K := rectC (A : ℝ) B C D with hKdef
  obtain ⟨a', ha'⟩ : ∃ q : ℚ, (q : ℝ) = A - 1 := ⟨A - 1, by push_cast; ring⟩
  obtain ⟨b', hb'⟩ : ∃ q : ℚ, (q : ℝ) = B + 1 := ⟨B + 1, by push_cast; ring⟩
  obtain ⟨c', hc'⟩ : ∃ q : ℚ, (q : ℝ) = C / 2 := ⟨C / 2, by push_cast; ring⟩
  obtain ⟨d', hd'⟩ : ∃ q : ℚ, (q : ℝ) = D + 1 := ⟨D + 1, by push_cast; ring⟩
  have hc'0 : (0 : ℝ) < c' := by rw [hc']; linarith
  obtain ⟨ρ, M, m, hρ, hm, hcls⟩ := flow_mem_areaClass hW hW0 hT (a := a') (b := b')
    (d := d') hc'0
  set Kp := rectC (a' : ℝ) b' c' d' with hKp
  obtain ⟨Cd, L, r₀, hCd, -, hr₀, -, hbd⟩ := areaClass_deriv_bounds (a := (a' : ℝ)) (b := b')
    (c := c') (d := d') (M := M) (m := m) hρ
  set δ : ℝ := ρ / 6 with hδdef
  have hδ : 0 < δ := by positivity
  have hg := continuous_h0cut κ hδ
  obtain ⟨r₁, hr₁, hadd⟩ := addon_circle_unif (a := a') (b := b') (d := d') (M := M) (m := m)
    hc'0 hρ hg (η / 4) (by positivity)
  set δ₀ : ℝ := min (1 / 2) (C / 4) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (by norm_num) (by linarith)
  have hδ₀1 : δ₀ ≤ 1 / 2 := min_le_left _ _
  have hδ₀2 : δ₀ ≤ C / 4 := min_le_right _ _
  have hball : ∀ z ∈ K, closedBall z δ₀ ⊆ a7Open (a' : ℝ) b' c' d' := by
    intro z hz w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := (Complex.abs_re_le_norm (w - z)).trans hw
    have h2 := (Complex.abs_im_le_norm (w - z)).trans hw
    rw [Complex.sub_re, abs_le] at h1
    rw [Complex.sub_im, abs_le] at h2
    obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hKK : ∀ z ∈ K, z ∈ Kp := fun z hz =>
    a7Open_subset _ _ _ _ (hball z hz (mem_closedBall_self hδ₀.le))
  have hKH : K ⊆ H := a8_rect_H hC
  have hHHbar : H ⊆ Hbar := fun w hw => le_of_lt (show 0 < w.im from hw)
  have hrad : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, radius k ≤ ε := fun ε hε =>
    hrad.eventually (ge_mem_nhds hε)
  filter_upwards [hsm (r₁ / 2) (by positivity), hsm (δ₀ / 2) (by positivity),
    hsm (ρ / (4 * Cd)) (by positivity), hD (η / 4) (by positivity)] with k hk1 hk2 hk3 hk4
  have hr : 0 < radius k := radius_pos k
  have hdpos : ∀ t ∈ Icc (0 : ℝ) Tq, ∀ z ∈ K, 0 < ‖deriv (fwdMapInv W t) z‖ :=
    fun t ht z hz => lt_of_lt_of_le hm ((hcls t ht).2.2.2 z (hKK z hz))
  have hψH : ∀ t ∈ Icc (0 : ℝ) Tq, ∀ z ∈ K, fwdMapInv W t z ∈ H := fun t ht z hz =>
    RS.fwdMapInv_mem_H hW hW0 ht.1 (hKH hz)
  have hΦc := a9_err_cont γ hFx.1 hW hW0 hKH hZc hr hdpos
  set Φ := a9Err γ Zh Fx W (radius k) with hΦdef
  -- the error is `pushErrR`
  have hΦeq : ∀ t ∈ Icc (0 : ℝ) Tq, ∀ z ∈ K, ∀ α ∈ Icc (1 : ℝ) 2,
      pushErrR γ x (fwdMapInv W t) (α * radius k) z = Φ (t, z, α) := by
    intro t ht z hz α hα
    have hr' : 0 < α * radius k := mul_pos (by linarith [hα.1]) hr
    have e1 : evalReg (coordChange x (fwdMapInv W t) (Qc γ)) (foldedCircle z (α * radius k)) =
        Zh (t, (z, α * radius k)) :=
      (hreg t ht).evalReg_fc_of_mem (hHHbar (hKH hz)) hr'
    have e2 := hFx.evalReg_fc_of_mem (hHHbar (hψH t ht z hz)) (mul_pos hr' (hdpos t ht z hz))
    simp only [pushErrR, hΦdef, a9Err]
    rw [e1, e2]
  -- the bound at rational parameters
  have hΦrat : ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) Tq → ∀ z : ℚ × ℚ, zQ z ∈ K →
      ∀ α : ℚ, (α : ℝ) ∈ Icc (1 : ℝ) 2 → |Φ ((q : ℝ), zQ z, (α : ℝ))| ≤ η := by
    intro q hq z hz α hα
    obtain ⟨hTend, hbound⟩ := hk4 q hq α hα z hz
    have hrq := hrat q hq z hz α hα k
    have hdzz := hdpos q hq (zQ z) hz
    have hψzH := hψH q hq (zQ z) hz
    have hψcls := hcls q hq
    have hzKp := hKK (zQ z) hz
    have hzim := hz.2.1
    set zz := zQ z with hzz
    set s : ℝ := (α : ℝ) * radius k with hsdef
    set ψ := fwdMapInv W (q : ℝ) with hψdef
    have hs0 : 0 < s := mul_pos (by linarith [hα.1]) hr
    have hs2 : s ≤ 2 * radius k := mul_le_mul_of_nonneg_right hα.2 hr.le
    have hsδ₀ : s ≤ δ₀ := by linarith
    have hsr₁ : s ≤ r₁ := by linarith
    have hsim : s ≤ zz.im := by linarith
    have hB : closedBall zz s ⊆ a7Open (a' : ℝ) b' c' d' :=
      (closedBall_subset_closedBall hsδ₀).trans (hball zz hz)
    have hdiff : DifferentiableOn ℂ ψ (a7Open (a' : ℝ) b' c' d') :=
      hψcls.1.mono ((a7Open_subset _ _ _ _).trans (self_subset_thickening hρ _))
    have hne : ∀ u ∈ a7Open (a' : ℝ) b' c' d', deriv ψ u ≠ 0 := fun u hu =>
      norm_pos_iff.1 (lt_of_lt_of_le hm (hψcls.2.2.2 u (a7Open_subset _ _ _ _ hu)))
    have hlog := swcNA2_integral_log_deriv_fc (isOpen_a7Open _ _ _ _) hdiff hne hs0 hsim hB
    have hraw : Φ ((q : ℝ), zz, (α : ℝ)) =
        evalReg x ((foldedCircle zz s).map ψ) - Fx (ψ zz, s * ‖deriv ψ zz‖) := by
      simp only [hΦdef, a9Err]
      rw [hrq]
      simp only [unzippedField, coordChange]
      rw [hlog]
      ring
    -- the pushed circle: `𝔥₀` add-on
    have hae : AEMeasurable ψ (foldedCircle zz s) :=
      RegCont.aemeasurable_fwdMapInv hW hW0 hq.1 zz hs0
    have : IsProbabilityMeasure ((foldedCircle zz s).map ψ) :=
      (Measure.isProbabilityMeasure_map_iff hae).2 inferInstance
    have hKψc : IsCompact (ψ '' closedBall zz s) :=
      (isCompact_closedBall zz s).image_of_continuousOn (hdiff.continuousOn.mono hB)
    have hKψim : ∀ u ∈ ψ '' closedBall zz s, 3 * δ ≤ u.im := by
      rintro _ ⟨u, hu, rfl⟩
      have := (hψcls.2.2.1 u (self_subset_thickening hρ _ (a7Open_subset _ _ _ _ (hB hu)))).2
      rw [hδdef]; linarith
    have hcar : ∀ᵐ u ∂((foldedCircle zz s).map ψ), u ∈ ψ '' closedBall zz s := by
      refine (ae_map_iff hae hKψc.isClosed.measurableSet).2 ?_
      filter_upwards [a8_ae_circ hs0 hsim isClosed_closedBall
        fun θ => circleMap_mem_closedBall zz hs0.le θ] with u hu
      exact ⟨u, hu, rfl⟩
    have hpush := a9_evalReg_h0_add κ hFX hδ hKψc hKψim hcar hTend
    -- the round circle
    have hdC : ‖deriv ψ zz‖ ≤ Cd := (hbd ψ hψcls zz hzKp zz (mem_closedBall_self hr₀.le)).2.1
    have hρR0 : 0 < s * ‖deriv ψ zz‖ := mul_pos hs0 hdzz
    have hρRle : s * ‖deriv ψ zz‖ ≤ ρ / 2 := by
      have h4 : radius k * (4 * Cd) ≤ ρ := (le_div_iff₀ (by positivity)).1 hk3
      calc s * ‖deriv ψ zz‖ ≤ s * Cd := mul_le_mul_of_nonneg_left hdC hs0.le
        _ ≤ ρ / 2 := by nlinarith
    have hψzim : (ρ : ℝ) ≤ (ψ zz).im := (hψcls.2.2.1 zz (self_subset_thickening hρ _ hzKp)).2
    have hround : evalReg x (foldedCircle (ψ zz) (s * ‖deriv ψ zz‖)) =
        evalReg X0 (foldedCircle (ψ zz) (s * ‖deriv ψ zz‖)) +
          ∫ u, h0cut κ δ u ∂foldedCircle (ψ zz) (s * ‖deriv ψ zz‖) := by
      refine a9_evalReg_h0_add κ hFX hδ (isCompact_closedBall (ψ zz) (s * ‖deriv ψ zz‖)) ?_
        (a8_ae_circ hρR0 (by linarith) isClosed_closedBall
          fun θ => circleMap_mem_closedBall _ hρR0.le θ) (a8_reg_tendsto hFX (ψ zz) hρR0)
      intro u hu
      rw [mem_closedBall, dist_eq_norm] at hu
      have h := (Complex.abs_im_le_norm (u - ψ zz)).trans hu
      rw [Complex.sub_im, abs_le] at h
      rw [hδdef]; linarith [h.1]
    have hFxe : Fx (ψ zz, s * ‖deriv ψ zz‖) = evalReg x (foldedCircle (ψ zz) (s * ‖deriv ψ zz‖)) :=
      (hFx.evalReg_fc_of_mem (hHHbar hψzH) hρR0).symm
    obtain ⟨hA1, hA2⟩ := hadd ψ hψcls zz hzKp s hs0 hsr₁
    have hint : ∫ u, h0cut κ δ u ∂((foldedCircle zz s).map ψ) =
        ∫ w, h0cut κ δ (ψ w) ∂foldedCircle zz s :=
      integral_map hae hg.aestronglyMeasurable
    rw [hraw, hFxe, hpush, hround, hint]
    have e : evalReg X0 ((foldedCircle zz s).map ψ) + ∫ w, h0cut κ δ (ψ w) ∂foldedCircle zz s -
        (evalReg X0 (foldedCircle (ψ zz) (s * ‖deriv ψ zz‖)) +
          ∫ u, h0cut κ δ u ∂foldedCircle (ψ zz) (s * ‖deriv ψ zz‖)) =
        (evalReg X0 ((foldedCircle zz s).map ψ) -
          evalReg X0 (foldedCircle (ψ zz) (s * ‖deriv ψ zz‖))) +
        ((∫ w, h0cut κ δ (ψ w) ∂foldedCircle zz s - h0cut κ δ (ψ zz)) -
          (∫ u, h0cut κ δ u ∂foldedCircle (ψ zz) (s * ‖deriv ψ zz‖) - h0cut κ δ (ψ zz))) := by
      ring
    rw [e]
    calc _ ≤ |evalReg X0 ((foldedCircle zz s).map ψ) -
          evalReg X0 (foldedCircle (ψ zz) (s * ‖deriv ψ zz‖))| +
        (|∫ w, h0cut κ δ (ψ w) ∂foldedCircle zz s - h0cut κ δ (ψ zz)| +
          |∫ u, h0cut κ δ u ∂foldedCircle (ψ zz) (s * ‖deriv ψ zz‖) - h0cut κ δ (ψ zz)|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ ≤ η / 4 + (η / 4 + η / 4) := add_le_add hbound (add_le_add hA1 hA2)
      _ ≤ η := by linarith
  -- from the rational parameters to all parameters
  have hup := a9_le_of_rat hT hAB hCD hΦc (ε := η) fun q hq z hz α hα =>
    (abs_le.1 (hΦrat q hq z hz α hα)).2
  have hlo := a9_le_of_rat hT hAB hCD hΦc.neg (ε := η) fun q hq z hz α hα => by
    have := (abs_le.1 (hΦrat q hq z hz α hα)).1
    show -Φ _ ≤ η
    linarith
  intro t ht α hα z hz
  have hp : ((t, z, α) : ℝ × ℂ × ℝ) ∈ Icc (0 : ℝ) Tq ×ˢ (K ×ˢ Icc (1 : ℝ) 2) := ⟨ht, hz, hα⟩
  rw [hΦeq t ht z hz α hα]
  have h1 := hup _ hp
  have h2 : -Φ (t, z, α) ≤ η := hlo _ hp
  exact abs_le.2 ⟨by linarith, h1⟩

end SWCore
end QuantumZipper
