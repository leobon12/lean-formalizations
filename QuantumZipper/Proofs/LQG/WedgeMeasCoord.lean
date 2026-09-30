import QuantumZipper.Proofs.LQG.WedgeCanonical2

/-!
# WEDGE-MEAS, step 1: the radial coordinates of the canonical wedge field

For a good free sample `x` (`WedgeTK.GoodRad x F`, raw dyadic agreement `hraw`) and a continuous
radial path `A`, the wedge field `W = wedgeField (lateralPart x) A Q` has regularized semicircle
averages about `0`

  `evalReg W (fc 0 ρ) = Q (−log ρ) + A (−log ρ)`    (`evalReg_wedgeField_fc0`),

i.e. the lateral part does not contribute on semicircles centred at `0` (Sheffield,
arXiv:1012.4797, §1.6: the semicircle average of `h` at radius `e^{-t}` is `A_t + Q t`). For the
rescaled field `rescale W Q s` (`s > 0`) this gives

  `radAvgReg (rescale W Q s) r = Q (−log r) + A (−log r − log s)`   (`radAvgReg_rescale_wedgeField`).

Own elementary bookkeeping on top of the density-rule lemmas of `WedgeCanonical2` (the profile is
truncated near `0` to a continuous function `gT`, which does not change any circle average used).
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace QuantumZipper

namespace WedgeMeasCoord

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {Q ρ : ℝ}

theorem zero_mem_Hbar_wm : (0 : ℂ) ∈ Hbar := by simp [Hbar]

/-- The wedge profile truncated at modulus `ρ / 4` (continuous on all of `ℂ`). -/
def gT (F : ℂ × ℝ → ℝ) (A : ℝ → ℝ) (Q ρ : ℝ) : ℂ → ℝ := fun z =>
  -F (0, max ‖z‖ (ρ / 4)) + Q * -Real.log (max ‖z‖ (ρ / 4)) + A (-Real.log (max ‖z‖ (ρ / 4)))

theorem continuous_gT (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) (hA : Continuous A) (hρ : 0 < ρ) :
    Continuous (gT F A Q ρ) := by
  have hm : Continuous fun z : ℂ => max ‖z‖ (ρ / 4) := continuous_norm.max continuous_const
  have hpos : ∀ z : ℂ, 0 < max ‖z‖ (ρ / 4) := fun z =>
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hlog : Continuous fun z : ℂ => Real.log (max ‖z‖ (ρ / 4)) :=
    hm.log fun z => (hpos z).ne'
  have hF' : Continuous fun z : ℂ => F (0, max ‖z‖ (ρ / 4)) :=
    hF.comp_continuous (continuous_const.prodMk hm) fun z => ⟨zero_mem_Hbar_wm, hpos z⟩
  unfold gT
  exact (hF'.neg.add (continuous_const.mul hlog.neg)).add (hA.comp hlog.neg)

theorem gT_eq (hG : WedgeTK.GoodRad x F) (hρ : 0 < ρ) {z : ℂ} (hz : ρ / 4 ≤ ‖z‖) :
    gT F A Q ρ z = WedgeCan.wedgeProfile x A Q z := by
  unfold gT WedgeCan.wedgeProfile
  rw [max_eq_left hz, hG.radAvgReg_eq (lt_of_lt_of_le (by positivity) hz)]

theorem integral_fc_profile_eq (hG : WedgeTK.GoodRad x F) (hρ : 0 < ρ) {w : ℂ} {r : ℝ}
    (hr : 0 < r) (hwr : ρ / 4 ≤ ‖w‖ - r) :
    ∫ u, WedgeCan.wedgeProfile x A Q u ∂foldedCircle w r = ∫ u, gT F A Q ρ u ∂foldedCircle w r :=
  integral_congr_ae ((WedgeCan.ae_fc_abs_le_norm hr).mono fun u hu =>
    (gT_eq hG hρ (hwr.trans ((le_abs_self _).trans hu))).symm)

/-- The dyadic averages of the wedge field agree, near the semicircle `‖u‖ = ρ`, with those of
`x + ofFun (gT …)`. -/
theorem avgReg_wedgeField_eq_gT (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (hρ : 0 < ρ) {k : ℕ} (hk : radius k < ρ / 2) {u : ℂ} (hu : u ∈ Hbar)
    (hun : ‖u‖ = ρ) :
    avgReg (wedgeField (lateralPart x) A Q) k u = avgReg (x + ofFun (gT F A Q ρ)) k u := by
  rw [WedgeCan.avgReg_wedgeField_eq hG hraw hA Q hu (by rw [hun]; linarith)]
  have hev : ∀ᶠ n : ℕ in atTop, 3 * ρ / 4 < ‖dyadicRoundC n u‖ :=
    (RegClosure.tendsto_dyadicRoundC u).norm.eventually
      (lt_mem_nhds (by rw [hun]; linarith))
  have heq : (fun n : ℕ => (x + ofFun (WedgeCan.wedgeProfile x A Q))
        (foldedCircle (dyadicRoundC n u) (radius k))) =ᶠ[atTop]
      fun n => (x + ofFun (gT F A Q ρ)) (foldedCircle (dyadicRoundC n u) (radius k)) := by
    filter_upwards [hev] with n hn
    show x _ + ∫ v, WedgeCan.wedgeProfile x A Q v ∂_ = x _ + ∫ v, gT F A Q ρ v ∂_
    rw [integral_fc_profile_eq hG hρ (radius_pos k) (by linarith)]
  unfold avgReg limUnder
  rw [Filter.map_congr heq]

/-- **Semicircle averages of the wedge field about `0`.** -/
theorem evalReg_wedgeField_fc0 (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (hρ : 0 < ρ) :
    evalReg (wedgeField (lateralPart x) A Q) (foldedCircle 0 ρ) =
      Q * -Real.log ρ + A (-Real.log ρ) := by
  have hkev : ∀ᶠ k : ℕ in atTop, radius k < ρ / 2 :=
    (tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT).eventually_lt_const
      (by linarith)
  have hW : evalReg (wedgeField (lateralPart x) A Q) (foldedCircle 0 ρ) =
      evalReg (x + ofFun (gT F A Q ρ)) (foldedCircle 0 ρ) := by
    have heq : (fun k : ℕ => ∫ u, avgReg (wedgeField (lateralPart x) A Q) k u
          ∂foldedCircle 0 ρ) =ᶠ[atTop]
        fun k => ∫ u, avgReg (x + ofFun (gT F A Q ρ)) k u ∂foldedCircle 0 ρ := by
      filter_upwards [hkev] with k hk
      refine integral_congr_ae ?_
      filter_upwards [WedgeTK.fc_ae_norm hρ, RegClosure.fc_ae_mem_Hbar 0 ρ] with u hu1 hu2
      exact avgReg_wedgeField_eq_gT hG hraw hA hρ hk hu2 hu1
    unfold evalReg limUnder
    rw [Filter.map_congr heq]
  have hc := continuous_gT (Q := Q) hG.1.1 hA hρ
  rw [hW, GoodSample.evalReg_add_ofFun_fc hG.1 hc.continuousOn zero_mem_Hbar_wm hρ,
    hG.1.evalReg_fc_of_mem zero_mem_Hbar_wm hρ]
  have hs : GoodSample.smoothFun (gT F A Q ρ) 0 ρ =
      -F (0, ρ) + Q * -Real.log ρ + A (-Real.log ρ) := by
    unfold GoodSample.smoothFun
    rw [integral_congr_ae (g := fun _ => -F (0, ρ) + Q * -Real.log ρ + A (-Real.log ρ))]
    · simp
    filter_upwards [WedgeTK.fc_ae_norm hρ] with u hu
    have hm : max ‖u‖ (ρ / 4) = ρ := by rw [hu]; exact max_eq_left (by linarith)
    simp only [gT, hm]
  rw [hs]; ring

/-- Raw semicircle values of a rescaled field about `0`. -/
theorem rescale_fc0 (y : FieldSample) (Q : ℝ) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    rescale y Q s (foldedCircle 0 r) = evalReg y (foldedCircle 0 (s * r)) + Q * Real.log s := by
  show evalReg y ((foldedCircle 0 r).map fun z => (s : ℂ) * z) +
    Q * ∫ z, Real.log ‖deriv (fun w : ℂ => (s : ℂ) * w) z‖ ∂foldedCircle 0 r = _
  rw [WedgeTK.fc_map_mul 0 r hs, mul_zero]
  simp only [WedgeMeas.deriv_mul_left', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    integral_const, smul_eq_mul]
  simp

/-- **Radial averages of the rescaled wedge field.** -/
theorem radAvgReg_rescale_wedgeField (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) {s : ℝ} (hs : 0 < s) {r : ℝ} (hr : 0 < r) :
    radAvgReg (rescale (wedgeField (lateralPart x) A Q) Q s) r =
      Q * -Real.log r + A (-Real.log r - Real.log s) := by
  set f : ℝ → ℝ := fun r' => Q * -Real.log (s * r') + A (-Real.log (s * r')) + Q * Real.log s
    with hf
  have hlim : Tendsto (fun n : ℕ => dyadicRound n r + radius n) atTop (𝓝 r) := by
    have h1 : Tendsto (fun n : ℕ => dyadicRound n r) atTop (𝓝 r) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _)
        (fun n => by rw [Real.norm_eq_abs]; exact CircleCont.abs_dyadicRound_sub_le n r)
        WedgeTK.tendsto_one_div_two_pow
    have h2 : Tendsto (fun n : ℕ => radius n) atTop (𝓝 0) :=
      tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT
    simpa using h1.add h2
  have hsr : s * r ≠ 0 := (mul_pos hs hr).ne'
  have hfc : ContinuousAt f r := by
    have hl : ContinuousAt (fun r' => Real.log (s * r')) r :=
      (continuousAt_const.mul continuousAt_id).log hsr
    exact ((continuousAt_const.mul hl.neg).add (hA.continuousAt.comp hl.neg)).add
      continuousAt_const
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < dyadicRound n r + radius n :=
    hlim.eventually (lt_mem_nhds hr)
  have heq : (fun n : ℕ => f (dyadicRound n r + radius n)) =ᶠ[atTop]
      fun n => rescale (wedgeField (lateralPart x) A Q) Q s
        (foldedCircle 0 (dyadicRound n r + radius n)) := by
    filter_upwards [hpos] with n hn
    rw [rescale_fc0 _ Q hs, evalReg_wedgeField_fc0 hG hraw hA (mul_pos hs hn)]
  have ht := ((hfc.tendsto.comp hlim).congr' heq)
  unfold radAvgReg
  rw [ht.limUnder_eq, hf]
  simp only
  rw [Real.log_mul hs.ne' hr.ne']
  ring_nf

end WedgeMeasCoord

end QuantumZipper
