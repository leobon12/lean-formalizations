import QuantumZipper.Proofs.Zipper.SWCoreA8Add

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A8 (7): the flow distortion bound for the wedge field (pathwise)

`a8_pushErr_wedge`: for a good free sample `x`, a continuous radial process `A`, a continuous
driver `W` with `W 0 = 0` and the flow distortion data `A8Data` of `x` on the enlarged rational
rectangle `Kp = [a−1, b+1] × [c/2, d+1]`: for every `η > 0`, eventually in `k`, for all
`t ∈ [0,T]` and `z ∈ [a,b] × [c,d]`, `|pushErr γ (wedgeField (lateralPart x) A Q) f_t⁻¹ k z| ≤ η`.

Proof: `pushErr` of the wedge field is the difference of its pushed and round values
(`a7_pushErr_eq`; continuity in the centre from `A8Data` and `a8_cont_phi`); both values are
those of `x` plus the integral of the continuous cutoff profile (`a8_evalReg_wedge_add`, the
carriers staying at height `≥ δ₁/2` above the flow image of `Kp`); the free part is the
`A8Data` bound, the profile part is small by `addon_circle_unif`. Sheffield–Wang,
arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7); own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {W : ℝ → ℝ}

theorem a8_ae_circ {s : ℂ} {r : ℝ} (hr : 0 < r) (hrs : r ≤ s.im) {K : Set ℂ}
    (hKc : IsClosed K) (hK : ∀ θ, circleMap s r θ ∈ K) : ∀ᵐ w ∂foldedCircle s r, w ∈ K := by
  rw [foldedCircle_eq_circleUnif hr.le hrs, swA6_circleUnif_eq_map]
  exact (ae_map_iff (continuous_circleMap s r).measurable.aemeasurable hKc.measurableSet).2
    (ae_of_all _ hK)

/-- **Pathwise flow distortion bound for the wedge field.** -/
theorem a8_pushErr_wedge (γ Q : ℝ) (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {a b c d : ℝ} (hc : 0 < c) {a' b' c' d' : ℚ} (ha' : (a' : ℝ) = a - 1) (hb' : (b' : ℝ) = b + 1)
    (hc' : (c' : ℝ) = c / 2) (hd' : (d' : ℝ) = d + 1)
    (hD : A8Data x W T a' b' c' d') :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ rectC a b c d,
      |pushErr γ (wedgeField (lateralPart x) A Q) (fwdMapInv W t) k z| ≤ η := by
  intro η hη
  set Kp := rectC (a' : ℝ) b' c' d' with hKp
  have hc'0 : (0 : ℝ) < c' := by rw [hc']; linarith
  obtain ⟨ρ', M', m', hρ', hm', hcls⟩ := flow_mem_areaClass hW hW0 hT (a := a') (b := b')
    (d := d') hc'0
  set Kw := rectC ((a' : ℝ) - c' / 2) (b' + c' / 2) (c' / 2) (d' + c' / 2) with hKw
  have hKwH : Kw ⊆ H := a8_rect_H (by linarith)
  have hImc := E6.isCompact_flowImage hW hW0 T (swA6_isCompact_rectC _ _ _ _) hKwH
  have hImH := E6.flowImage_subset_H hW hW0 T hKwH
  obtain ⟨δ₁, hδ₁, hδ₁F⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ w ∈ E6.flowImage W T Kw, δ₁ ≤ w.im := by
    rcases (E6.flowImage W T Kw).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hImc.exists_isMinOn hne Complex.continuous_im.continuousOn
      exact ⟨w₀.im, hImH hw₀, fun w hw => hmin hw⟩
  have hKpH : Kp ⊆ H := a8_rect_H hc'0
  have hlogc := (RegUnif.continuousOn_log_deriv_fwdMapInv_joint hW hW0 T).mono
    (prod_mono (subset_refl (Icc (0 : ℝ) T)) hKpH)
  obtain ⟨Bd, hBd⟩ := (isCompact_Icc.prod (swA6_isCompact_rectC _ _ _ _)).exists_bound_of_continuousOn
    hlogc
  have hMd : ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ Kp, ‖deriv (fwdMapInv W t) z‖ ≤ Real.exp Bd := by
    intro t ht z hz
    have hpos : 0 < ‖deriv (fwdMapInv W t) z‖ := lt_of_lt_of_le hm' ((hcls t ht).2.2.2 z hz)
    have h1 := (le_abs_self _).trans ((hBd (t, z) ⟨ht, hz⟩).trans_eq' (Real.norm_eq_abs _).symm)
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 h1
  set δ := δ₁ / 6 with hδdef
  have hδ : 0 < δ := by positivity
  have hp := continuous_a8Cut hG hA Q hδ
  obtain ⟨r₀, hr₀, hadd⟩ := addon_circle_unif (a := a') (b := b') (d := d') (M := M') (m := m')
    hc'0 hρ' hp (η / 4) (by positivity)
  obtain ⟨hD1, hD2⟩ := hD
  set δ₀ : ℝ := min (1 / 2) (c / 4) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (by norm_num) (by linarith)
  have hδ₀1 : δ₀ ≤ 1 / 2 := min_le_left _ _
  have hδ₀2 : δ₀ ≤ c / 4 := min_le_right _ _
  have hball : ∀ z ∈ rectC a b c d, closedBall z δ₀ ⊆ a7Open (a' : ℝ) b' c' d' := by
    intro z hz w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := (Complex.abs_re_le_norm (w - z)).trans hw
    have h2 := (Complex.abs_im_le_norm (w - z)).trans hw
    rw [Complex.sub_re, abs_le] at h1
    rw [Complex.sub_im, abs_le] at h2
    obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hKK : ∀ z ∈ rectC a b c d, z ∈ Kp := fun z hz =>
    a7Open_subset _ _ _ _ (hball z hz (mem_closedBall_self hδ₀.le))
  have hrad : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, radius k ≤ ε := fun ε hε =>
    hrad.eventually (ge_mem_nhds hε)
  filter_upwards [hsm ((c' : ℝ) / 2) (by linarith), hsm (δ₁ / 2 / (Real.exp Bd))
    (by positivity), hsm r₀ hr₀, hsm (δ₀ / 2) (by linarith), hD1, hD2 (η / 2) (by linarith)]
    with k hk1 hk2 hk3 hk4 hk5 hk6
  intro t ht z hz
  set ψ := fwdMapInv W t with hψdef
  set r := radius k with hrdef
  have hr : 0 < r := radius_pos k
  have hψcls := hcls t ht
  have hzKp := hKK z hz
  -- pushed carriers
  have hImm := hImc.isClosed.measurableSet
  have hae : ∀ s : ℂ, AEMeasurable ψ (foldedCircle s r) := fun s =>
    RegCont.aemeasurable_fwdMapInv hW hW0 ht.1 s hr
  have hcar : ∀ s ∈ Kp, ∀ᵐ u ∂((foldedCircle s r).map ψ), u ∈ E6.flowImage W T Kw := by
    intro s hs
    refine (ae_map_iff (hae s) hImm).2 ?_
    have hrs : r ≤ s.im := by linarith [hs.2.1]
    filter_upwards [a8_ae_circ hr hrs (swA6_isCompact_rectC _ _ _ _).isClosed
      fun θ => a8_circ_mem hs hr.le hk1 θ] with w hw
    exact ⟨(t, w), ⟨ht, hw⟩, rfl⟩
  have hIm3 : ∀ u ∈ E6.flowImage W T Kw, 3 * δ ≤ u.im := fun u hu => by
    have := hδ₁F u hu; rw [hδdef]; linarith
  have hpush : ∀ s ∈ Kp, evalReg (wedgeField (lateralPart x) A Q) ((foldedCircle s r).map ψ) =
      evalReg x ((foldedCircle s r).map ψ) + ∫ u, a8Cut x A Q δ u ∂((foldedCircle s r).map ψ) := by
    intro s hs
    exact a8_evalReg_wedge_add hG hraw hA Q hδ hImc hIm3 (hcar s hs) ((hk5 t ht).1 s hs)
  -- the round circle
  set ρR := r * ‖deriv ψ z‖ with hρR
  have hd0 : 0 < ‖deriv ψ z‖ := lt_of_lt_of_le hm' (hψcls.2.2.2 z hzKp)
  have hρR0 : 0 < ρR := mul_pos hr hd0
  have hψzI : ψ z ∈ E6.flowImage W T Kw :=
    ⟨(t, z), ⟨ht, by
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hzKp
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩, rfl⟩
  have hρRle : ρR ≤ δ₁ / 2 := by
    have h1 := hMd t ht z hzKp
    have h2 : r * Real.exp Bd ≤ δ₁ / 2 := by
      rw [le_div_iff₀ (Real.exp_pos Bd)] at hk2; linarith
    calc ρR = r * ‖deriv ψ z‖ := rfl
      _ ≤ r * Real.exp Bd := mul_le_mul_of_nonneg_left h1 hr.le
      _ ≤ δ₁ / 2 := h2
  have hψzim := hδ₁F _ hψzI
  have hround : evalReg (wedgeField (lateralPart x) A Q) (foldedCircle (ψ z) ρR) =
      evalReg x (foldedCircle (ψ z) ρR) + ∫ u, a8Cut x A Q δ u ∂foldedCircle (ψ z) ρR := by
    refine a8_evalReg_wedge_add hG hraw hA Q hδ (isCompact_closedBall (ψ z) ρR) ?_
      (a8_ae_circ hρR0 (by linarith) isClosed_closedBall
        fun θ => circleMap_mem_closedBall _ hρR0.le θ) (a8_reg_tendsto hG.1 (ψ z) hρR0)
    intro u hu
    rw [mem_closedBall, dist_eq_norm] at hu
    have h := (Complex.abs_im_le_norm (u - ψ z)).trans hu
    rw [Complex.sub_im, abs_le] at h
    rw [hδdef]; linarith [h.1]
  -- pushErr as a difference
  have hdiff : DifferentiableOn ℂ ψ (a7Open (a' : ℝ) b' c' d') :=
    hψcls.1.mono ((a7Open_subset _ _ _ _).trans (self_subset_thickening hρ' _))
  have hne : ∀ u ∈ a7Open (a' : ℝ) b' c' d', deriv ψ u ≠ 0 := fun u hu =>
    norm_pos_iff.1 (lt_of_lt_of_le hm' (hψcls.2.2.2 u (a7Open_subset _ _ _ _ hu)))
  have hB : closedBall z (2 * r) ⊆ a7Open (a' : ℝ) b' c' d' :=
    (closedBall_subset_closedBall (by linarith)).trans (hball z hz)
  have him : 2 * r ≤ z.im := by linarith [hz.2.1]
  have hzO : z ∈ a7Open (a' : ℝ) b' c' d' := hball z hz (mem_closedBall_self hδ₀.le)
  have hnhds : Kp ∈ 𝓝 z :=
    Filter.mem_of_superset ((isOpen_a7Open _ _ _ _).mem_nhds hzO) (a7Open_subset _ _ _ _)
  have hc1 : ContinuousAt (fun s => evalReg x ((foldedCircle s r).map ψ)) z :=
    ((hk5 t ht).2).continuousAt hnhds
  have hc2 : ContinuousAt (fun s => ∫ u, a8Cut x A Q δ u ∂((foldedCircle s r).map ψ)) z := by
    have hj := a8_cont_phi hW hW0 (T := T) (A := a') (B := b') (D := d') hc'0 hr hk1
      hp.continuousOn hp.measurable
    exact (hj.comp (continuousOn_const.prodMk continuousOn_id) fun s hs => ⟨ht, hs⟩).continuousAt
      hnhds
  have hc3 : ContinuousAt (fun s =>
      evalReg (wedgeField (lateralPart x) A Q) ((foldedCircle s r).map ψ)) z := by
    refine (hc1.add hc2).congr ?_
    filter_upwards [hnhds] with s hs
    exact (hpush s hs).symm
  have h1 := hc3.tendsto.comp (RegClosure.tendsto_dyadicRoundC z)
  rw [a7_pushErr_eq (isOpen_a7Open _ _ _ _) hdiff hne hB him h1, hpush z hzKp, hround]
  -- the two error terms
  have hf := hk6 t ht z hzKp
  obtain ⟨hA1, hA2⟩ := hadd ψ hψcls z hzKp r hr hk3
  have hint : ∫ u, a8Cut x A Q δ u ∂((foldedCircle z r).map ψ) =
      ∫ w, a8Cut x A Q δ (ψ w) ∂foldedCircle z r :=
    integral_map (hae z) hp.aestronglyMeasurable
  rw [hint]
  have e : evalReg x ((foldedCircle z r).map ψ) + ∫ w, a8Cut x A Q δ (ψ w) ∂foldedCircle z r -
      (evalReg x (foldedCircle (ψ z) ρR) + ∫ u, a8Cut x A Q δ u ∂foldedCircle (ψ z) ρR) =
      (evalReg x ((foldedCircle z r).map ψ) - evalReg x (foldedCircle (ψ z) ρR)) +
      ((∫ w, a8Cut x A Q δ (ψ w) ∂foldedCircle z r - a8Cut x A Q δ (ψ z)) -
        (∫ u, a8Cut x A Q δ u ∂foldedCircle (ψ z) ρR - a8Cut x A Q δ (ψ z))) := by ring
  rw [e]
  calc _ ≤ |evalReg x ((foldedCircle z r).map ψ) - evalReg x (foldedCircle (ψ z) ρR)| +
        (|∫ w, a8Cut x A Q δ (ψ w) ∂foldedCircle z r - a8Cut x A Q δ (ψ z)| +
          |∫ u, a8Cut x A Q δ u ∂foldedCircle (ψ z) ρR - a8Cut x A Q δ (ψ z)|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ η / 2 + (η / 4 + η / 4) := add_le_add hf (add_le_add hA1 hA2)
    _ = η := by ring

end SWCore
end QuantumZipper
