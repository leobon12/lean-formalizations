import InteractingSLE.Spec.Ito.Bracket

/-!
# The two-point generator: `d(𝔥(y)𝔥(z) + G(y, z)) ` has no drift

Packet PROVE-T11-ITO (Specification L515–L527, (3.16)–(3.17)). On the two-point coordinate space
`(Coord × Coord) × ℝ` (`Λ(y), Λ(z), x = B_t`):

* `itoGen_onFst`, `itoGen_onSnd`: the generator of a function of one point's coordinates is the one-point generator;
* `itoGen_add`, `itoGen_mul` (`Bracket.lean`): linearity and the product rule;
* `itoGen_greenObs`: the generator of `G(Γ_y, Γ_z)` (`greenH`, independent of `x` because `G` is invariant under real
  translations) is the derivative of `G` in the direction of the coordinate densities; along the flow it equals
  `−Im(2/f_y) Im(2/f_z)` (QuantumZipper `FwdClock.kernel_alg`), the generator form of (3.16);
* `itoGen_twoObs_eq_zero`: `itoGen (𝔥(y) 𝔥(z) + G) = 0`, i.e. `d⟨𝔥(y), 𝔥(z)⟩ = −dG` ((3.17)).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex

namespace InteractingSLE

namespace Ito

section Gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_fst_line {F : E × ℝ → ℝ} {q : E × ℝ} (hF : DifferentiableAt ℝ F q) (w : E) :
    HasDerivAt (fun t : ℝ => F (q.1 + t • w, q.2)) (partialFst F q w) 0 := by
  have hline : HasDerivAt (fun t : ℝ => ((q.1 + t • w, q.2) : E × ℝ)) ((w, 0) : E × ℝ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => q.1 + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add q.1
    exact h1.prodMk (hasDerivAt_const 0 q.2)
  have h := (show HasFDerivAt F (fderiv ℝ F q) (q.1 + (0 : ℝ) • w, q.2) by
    simpa using hF.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hline
  rw [partialFst_apply]
  simpa [Function.comp_def] using h

/-- `F` read on the first point. -/
def onFst (F : E × ℝ → ℝ) (p : (E × E) × ℝ) : ℝ := F (p.1.1, p.2)

/-- `F` read on the second point. -/
def onSnd (F : E × ℝ → ℝ) (p : (E × E) × ℝ) : ℝ := F (p.1.2, p.2)

theorem contDiffAt_onFst {F : E × ℝ → ℝ} {p : (E × E) × ℝ} {n : WithTop ℕ∞}
    (hF : ContDiffAt ℝ n F (p.1.1, p.2)) : ContDiffAt ℝ n (onFst F) p :=
  hF.comp p (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt

theorem contDiffAt_onSnd {F : E × ℝ → ℝ} {p : (E × E) × ℝ} {n : WithTop ℕ∞}
    (hF : ContDiffAt ℝ n F (p.1.2, p.2)) : ContDiffAt ℝ n (onSnd F) p :=
  hF.comp p (contDiff_fst.snd.prodMk contDiff_snd).contDiffAt

theorem partialSnd_onFst {F : E × ℝ → ℝ} {p : (E × E) × ℝ} (hF : ContDiffAt ℝ 1 F (p.1.1, p.2)) :
    partialSnd (onFst F) p = partialSnd F (p.1.1, p.2) :=
  partialSnd_eq_of_hasDerivAt ((contDiffAt_onFst hF).differentiableAt one_ne_zero)
    (hasDerivAt_snd_line (hF.differentiableAt one_ne_zero))

theorem partialSnd_onSnd {F : E × ℝ → ℝ} {p : (E × E) × ℝ} (hF : ContDiffAt ℝ 1 F (p.1.2, p.2)) :
    partialSnd (onSnd F) p = partialSnd F (p.1.2, p.2) :=
  partialSnd_eq_of_hasDerivAt ((contDiffAt_onSnd hF).differentiableAt one_ne_zero)
    (hasDerivAt_snd_line (p := (p.1.2, p.2)) (hF.differentiableAt one_ne_zero))

theorem itoGen_onFst {F : E × ℝ → ℝ} {p : (E × E) × ℝ} (hF : ContDiffAt ℝ 2 F (p.1.1, p.2))
    (v : E × E) : itoGen (onFst F) p v = itoGen F (p.1.1, p.2) v.1 := by
  have hd : DifferentiableAt ℝ (onFst F) p := (contDiffAt_onFst hF).differentiableAt (by norm_num)
  have h1 : partialFst (onFst F) p v = partialFst F (p.1.1, p.2) v.1 := by
    refine partialFst_eq_of_hasDerivAt hd ?_
    have := hasDerivAt_fst_line (q := (p.1.1, p.2)) (hF.differentiableAt (by norm_num)) v.1
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [onFst, Prod.fst_add, Prod.smul_fst]
  have hline : ContinuousAt (fun y : ℝ => (((p.1, y) : (E × E) × ℝ).1.1, y)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : ∀ᶠ y in 𝓝 p.2, ContDiffAt ℝ 1 F (p.1.1, y) :=
    hline.eventually ((hF.eventually (by simp)).mono fun q hq => hq.of_le (by norm_num))
  have h2 : partialSndSnd (onFst F) p = partialSndSnd F (p.1.1, p.2) :=
    partialSndSnd_eq_of_hasDerivAt (contDiffAt_onFst hF) (g := fun y => partialSnd F (p.1.1, y))
      (hev.mono fun y hy => partialSnd_onFst (p := (p.1, y)) hy)
      (hasDerivAt_partialSnd (p := (p.1.1, p.2)) hF)
  simp only [itoGen, h1, h2]

theorem itoGen_onSnd {F : E × ℝ → ℝ} {p : (E × E) × ℝ} (hF : ContDiffAt ℝ 2 F (p.1.2, p.2))
    (v : E × E) : itoGen (onSnd F) p v = itoGen F (p.1.2, p.2) v.2 := by
  have hd : DifferentiableAt ℝ (onSnd F) p := (contDiffAt_onSnd hF).differentiableAt (by norm_num)
  have h1 : partialFst (onSnd F) p v = partialFst F (p.1.2, p.2) v.2 := by
    refine partialFst_eq_of_hasDerivAt hd ?_
    have := hasDerivAt_fst_line (q := (p.1.2, p.2)) (hF.differentiableAt (by norm_num)) v.2
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [onSnd, Prod.snd_add, Prod.smul_snd]
  have hline : ContinuousAt (fun y : ℝ => (((p.1, y) : (E × E) × ℝ).1.2, y)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : ∀ᶠ y in 𝓝 p.2, ContDiffAt ℝ 1 F (p.1.2, y) :=
    hline.eventually ((hF.eventually (by simp)).mono fun q hq => hq.of_le (by norm_num))
  have h2 : partialSndSnd (onSnd F) p = partialSndSnd F (p.1.2, p.2) :=
    partialSndSnd_eq_of_hasDerivAt (contDiffAt_onSnd hF) (g := fun y => partialSnd F (p.1.2, y))
      (hev.mono fun y hy => partialSnd_onSnd (p := (p.1, y)) hy)
      (hasDerivAt_partialSnd (p := (p.1.2, p.2)) hF)
  simp only [itoGen, h1, h2]

/-- Linearity of the generator. -/
theorem itoGen_add {F G : E × ℝ → ℝ} {p : E × ℝ} (hF : ContDiffAt ℝ 2 F p) (hG : ContDiffAt ℝ 2 G p)
    (v : E) : itoGen (fun q => F q + G q) p v = itoGen F p v + itoGen G p v := by
  have hdF := hF.differentiableAt (by norm_num)
  have hdG := hG.differentiableAt (by norm_num)
  have h1 : partialFst (fun q => F q + G q) p v = partialFst F p v + partialFst G p v := by
    simp only [partialFst_apply, fderiv_fun_add hdF hdG, add_apply]
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : E × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hevF : ∀ᶠ y in 𝓝 p.2, DifferentiableAt ℝ F (p.1, y) :=
    hline.eventually ((hF.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num))
  have hevG : ∀ᶠ y in 𝓝 p.2, DifferentiableAt ℝ G (p.1, y) :=
    hline.eventually ((hG.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num))
  have h2 : partialSndSnd (fun q => F q + G q) p = partialSndSnd F p + partialSndSnd G p :=
    partialSndSnd_eq_of_hasDerivAt (hF.add hG)
      (g := fun y => partialSnd F (p.1, y) + partialSnd G (p.1, y))
      ((hevF.and hevG).mono fun y hy => by
        simp only [partialSnd, fderiv_fun_add hy.1 hy.2, add_apply])
      ((hasDerivAt_partialSnd hF).add (hasDerivAt_partialSnd hG))
  simp only [itoGen, h1, h2]
  ring

end Gen

/-! ### The Green function term -/

section Green

open ComplexConjugate

variable {nL nR : ℕ}

/-- `G(Γ_y, Γ_z)` on the two-point coordinates (`= G(f_t y, f_t z)` by real-translation invariance). -/
def greenObs (p : (Coord nL nR × Coord nL nR) × ℝ) : ℝ := QuantumZipper.greenH p.1.1.1 p.1.2.1

theorem contDiff_sub_conj {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : (Coord nL nR × Coord nL nR) × ℝ => p.1.1.1 - conj p.1.2.1 :=
  contDiff_fst.fst.fst.sub (conjCLE.contDiff.comp contDiff_fst.snd.fst)

theorem contDiff_sub_sub {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : (Coord nL nR × Coord nL nR) × ℝ => p.1.1.1 - p.1.2.1 :=
  contDiff_fst.fst.fst.sub contDiff_fst.snd.fst

theorem contDiffAt_greenObs {p : (Coord nL nR × Coord nL nR) × ℝ}
    (h1 : p.1.1.1 - conj p.1.2.1 ≠ 0) (h2 : p.1.1.1 - p.1.2.1 ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n greenObs p := by
  have hA : ContDiffAt ℝ n (fun p : (Coord nL nR × Coord nL nR) × ℝ =>
      Real.log ‖p.1.1.1 - conj p.1.2.1‖) p :=
    (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 h1)).comp p
      ((contDiffAt_norm ℂ h1).comp p contDiff_sub_conj.contDiffAt)
  have hB : ContDiffAt ℝ n (fun p : (Coord nL nR × Coord nL nR) × ℝ =>
      Real.log ‖p.1.1.1 - p.1.2.1‖) p :=
    (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 h2)).comp p
      ((contDiffAt_norm ℂ h2).comp p contDiff_sub_sub.contDiffAt)
  exact hA.sub hB

/-- **The generator of the Green term**: `G` does not depend on `x`, and its derivative in the direction
`v = (v_y, v_z)` is `Re((a − b̄)/(Γ_y − Γ̄_z)) − Re((a − b)/(Γ_y − Γ_z))`, `a = v_y.Γ`, `b = v_z.Γ`. -/
theorem itoGen_greenObs {p : (Coord nL nR × Coord nL nR) × ℝ}
    (h1 : p.1.1.1 - conj p.1.2.1 ≠ 0) (h2 : p.1.1.1 - p.1.2.1 ≠ 0) (v : Coord nL nR × Coord nL nR) :
    itoGen greenObs p v = ((v.1.1 - conj v.2.1) / (p.1.1.1 - conj p.1.2.1)).re -
      ((v.1.1 - v.2.1) / (p.1.1.1 - p.1.2.1)).re := by
  have hd : ∀ y : ℝ, DifferentiableAt ℝ greenObs ((p.1, y) : (Coord nL nR × Coord nL nR) × ℝ) :=
    fun y => (contDiffAt_greenObs (n := 1) (p := (p.1, y)) h1 h2).differentiableAt one_ne_zero
  have hsnd : ∀ y : ℝ, partialSnd greenObs ((p.1, y) : (Coord nL nR × Coord nL nR) × ℝ) = 0 :=
    fun y => partialSnd_eq_of_hasDerivAt (hd y) (hasDerivAt_const y (greenObs (p.1, y)))
  have hss : partialSndSnd greenObs p = 0 :=
    partialSndSnd_eq_of_hasDerivAt (contDiffAt_greenObs h1 h2) (g := fun _ => 0)
      (Eventually.of_forall fun y => hsnd y) (hasDerivAt_const _ _)
  have hfst : partialFst greenObs p v = ((v.1.1 - conj v.2.1) / (p.1.1.1 - conj p.1.2.1)).re -
      ((v.1.1 - v.2.1) / (p.1.1.1 - p.1.2.1)).re := by
    refine partialFst_eq_of_hasDerivAt (hd p.2) ?_
    have hP : HasDerivAt (fun t : ℝ => (p.1.1.1 - conj p.1.2.1) + (t : ℂ) * (v.1.1 - conj v.2.1))
        (v.1.1 - conj v.2.1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (v.1.1 - conj v.2.1)).const_add
        (p.1.1.1 - conj p.1.2.1)
    have hQ : HasDerivAt (fun t : ℝ => (p.1.1.1 - p.1.2.1) + (t : ℂ) * (v.1.1 - v.2.1))
        (v.1.1 - v.2.1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (v.1.1 - v.2.1)).const_add
        (p.1.1.1 - p.1.2.1)
    have hlP := QuantumZipper.FwdClock.hasDerivWithinAt_log_norm hP.hasDerivWithinAt
      (s := univ) (by simpa using h1)
    have hlQ := QuantumZipper.FwdClock.hasDerivWithinAt_log_norm hQ.hasDerivWithinAt
      (s := univ) (by simpa using h2)
    rw [hasDerivWithinAt_univ] at hlP hlQ
    refine ((hlP.sub hlQ).congr_deriv (by simp)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [greenObs, QuantumZipper.greenH, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
      Prod.smul_snd, Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Pi.sub_apply]
    congr 3 <;> ring
  simp only [itoGen, hfst, hss, mul_zero, add_zero]

/-- The two-point observable `𝔥(y) 𝔥(z) + G(y, z)`. -/
def twoObs (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (p : (Coord nL nR × Coord nL nR) × ℝ) : ℝ :=
  onFst (meanObs κ ρL ρR) p * onSnd (meanObs κ ρL ρR) p + greenObs p

/-- **(3.17), generator form: `itoGen (𝔥(y)𝔥(z) + G) = 0`.** At a two-point state whose points have centred
force-point positions `aL, aR` (none `0`) and distinct `f_y ≠ f_z`, the generator of `twoObs` applied to the two
coordinate densities vanishes: the bracket `∂_x𝔥(y) ∂_x𝔥(z) = Im(2/f_y) Im(2/f_z)` cancels the drift
`−Im(2/f_y) Im(2/f_z)` of the Green function ((3.16)). -/
theorem itoGen_twoObs_eq_zero {κ : ℝ} (hκ : 0 < κ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {p : (Coord nL nR × Coord nL nR) × ℝ} (hy : (p.1.1, p.2) ∈ obsRegion κ)
    (hz : (p.1.2, p.2) ∈ obsRegion κ) (hyz : coordF κ (p.1.1, p.2) ≠ coordF κ (p.1.2, p.2))
    {aL : Fin nL → ℝ} {aR : Fin nR → ℝ}
    (hQLy : ∀ i, p.1.1.2.1 i = coordF κ (p.1.1, p.2) - aL i)
    (hQRy : ∀ i, p.1.1.2.2.1 i = coordF κ (p.1.1, p.2) - aR i)
    (hQLz : ∀ i, p.1.2.2.1 i = coordF κ (p.1.2, p.2) - aL i)
    (hQRz : ∀ i, p.1.2.2.2.1 i = coordF κ (p.1.2, p.2) - aR i)
    (haL : ∀ i, aL i ≠ 0) (haR : ∀ i, aR i ≠ 0) :
    itoGen (twoObs κ ρL ρR) p (coordDensity ρL ρR aL aR (coordF κ (p.1.1, p.2)),
      coordDensity ρL ρR aL aR (coordF κ (p.1.2, p.2))) = 0 := by
  set fy := coordF κ (p.1.1, p.2) with hfy
  set fz := coordF κ (p.1.2, p.2) with hfz
  have hΓy : p.1.1.1 = fy + (Real.sqrt κ : ℂ) * (p.2 : ℂ) := by rw [hfy, coordF]; ring
  have hΓz : p.1.2.1 = fz + (Real.sqrt κ : ℂ) * (p.2 : ℂ) := by rw [hfz, coordF]; ring
  have hfy0 : 0 < fy.im := hy.1
  have hfz0 : 0 < fz.im := hz.1
  have h2 : p.1.1.1 - p.1.2.1 ≠ 0 := by
    rw [hΓy, hΓz]; intro h; exact hyz (by linear_combination h)
  have hconj : p.1.1.1 - conj p.1.2.1 = fy - conj fz := by
    rw [hΓy, hΓz, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]; ring
  have h1 : p.1.1.1 - conj p.1.2.1 ≠ 0 := by
    rw [hconj]; intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hmy := contDiffAt_meanObs κ ρL ρR (n := 2) hy
  have hmz := contDiffAt_meanObs κ ρL ρR (n := 2) hz
  have hFy := contDiffAt_onFst (p := p) hmy
  have hFz := contDiffAt_onSnd (p := p) hmz
  unfold twoObs
  rw [itoGen_add (hFy.mul hFz) (contDiffAt_greenObs h1 h2), itoGen_mul hFy hFz,
    itoGen_onFst hmy, itoGen_onSnd hmz,
    itoGen_meanObs_eq_zero hκ ρL ρR hy hQLy hQRy haL haR,
    itoGen_meanObs_eq_zero hκ ρL ρR hz hQLz hQRz haL haR,
    partialSnd_onFst (hmy.of_le (by norm_num)), partialSnd_onSnd (hmz.of_le (by norm_num)),
    partialSnd_meanObs_eq hκ ρL ρR hy, partialSnd_meanObs_eq hκ ρL ρR hz,
    itoGen_greenObs h1 h2, hconj]
  have hsub : p.1.1.1 - p.1.2.1 = fy - fz := by rw [hΓy, hΓz]; ring
  rw [hsub]
  simp only [coordDensity, map_sub, Complex.conj_ofReal]
  have hk := QuantumZipper.FwdClock.kernel_alg hfy0 hfz0 hyz
  have e1 : 2 / fy - ((∑ i, ρL i / -aL i + ∑ i, ρR i / -aR i : ℝ) : ℂ) -
      ((starRingEnd ℂ) (2 / fz) - ((∑ i, ρL i / -aL i + ∑ i, ρR i / -aR i : ℝ) : ℂ)) =
      2 / fy - (starRingEnd ℂ) (2 / fz) := by ring
  have e2 : 2 / fy - ((∑ i, ρL i / -aL i + ∑ i, ρR i / -aR i : ℝ) : ℂ) -
      (2 / fz - ((∑ i, ρL i / -aL i + ∑ i, ρR i / -aR i : ℝ) : ℂ)) = 2 / fy - 2 / fz := by ring
  rw [e1, e2]
  linarith

end Green

end Ito

end InteractingSLE
