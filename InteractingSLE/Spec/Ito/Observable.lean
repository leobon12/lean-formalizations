import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import InteractingSLE.Spec.Ito.Mean
import InteractingSLE.Spec.Ito.Dynkin

/-!
# The mean as a smooth function of the Loewner coordinates; its Itô drift vanishes

Packet PROVE-T11-ITO (Specification §3.3, L500–L505: `d𝔥*_t = (2/f_t) dB_t`, (3.15)). Write the state of the evolution
at time `t` and the point `z` in the coordinates

`Λ = (Γ, Q^L, Q^R, L) = (f_t(z) + √κ B_t, f_t(z) − V̂^{L}_t, f_t(z) − V̂^{R}_t, log f_t'(z)) ∈ ℂ × ℂ^{nL} × ℂ^{nR} × ℂ`

(`V̂ = V − W`, so `Q = g_t(z) − V_t`). All four are absolutely continuous in `t`; the only martingale part of the
mean `𝔥_t(z)` enters through `f_t(z) = Γ − √κ B_t`. `meanObs κ ρL ρR (Λ, x)` is the mean as a function of
`(Λ, B_t = x)`: it is smooth on `obsRegion` (all arguments in `ℍ`), and

* `partialSnd_meanObs`: `∂_x meanObs = 2 Im(1/f)` with `f = Γ − √κ x` — the coefficient `Im(2/f_t)` of `dB_t`
  in (3.15);
* `itoGen_meanObs_eq_zero`: the Itô drift `∂_Λ meanObs · λ + ½ ∂²_x meanObs` vanishes for the density `λ` of the
  coordinates (`coordDensity`), whenever no force point sits on the driver — the computation
  `d𝔥*_t = (2/f_t) dB_t` of L500, using `2√κ χ = 4 − κ`.

Generic lemmas computing `partialFst`, `partialSnd`, `partialSndSnd` from one-variable derivatives are proved
first.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex

namespace InteractingSLE

namespace Ito

/-! ### Partial derivatives from one-variable derivatives -/

section Partials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E × ℝ → ℝ} {p : E × ℝ}

/-- `∂_Λ F(p) v` is the derivative of `t ↦ F(Λ + t v, x)` at `0`. -/
theorem partialFst_eq_of_hasDerivAt (hF : DifferentiableAt ℝ F p) {v : E} {d : ℝ}
    (hd : HasDerivAt (fun t : ℝ => F (p.1 + t • v, p.2)) d 0) : partialFst F p v = d := by
  have hline : HasDerivAt (fun t : ℝ => ((p.1 + t • v, p.2) : E × ℝ)) ((v, 0) : E × ℝ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p.1 + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p.1
    exact h1.prodMk (hasDerivAt_const 0 p.2)
  have hc : HasDerivAt (fun t : ℝ => F (p.1 + t • v, p.2)) (fderiv ℝ F p (v, 0)) 0 := by
    have h := (show HasFDerivAt F (fderiv ℝ F p) (p.1 + (0 : ℝ) • v, p.2) by
      simpa using hF.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hline
    simpa [Function.comp_def] using h
  rw [partialFst_apply]
  exact hc.unique hd

/-- `∂_x F(p)` is the derivative of `y ↦ F(Λ, y)`. -/
theorem partialSnd_eq_of_hasDerivAt (hF : DifferentiableAt ℝ F p) {d : ℝ}
    (hd : HasDerivAt (fun y : ℝ => F (p.1, y)) d p.2) : partialSnd F p = d := by
  have hline : HasDerivAt (fun y : ℝ => ((p.1, y) : E × ℝ)) ((0, 1) : E × ℝ) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hc := (show HasFDerivAt F (fderiv ℝ F p) (p.1, p.2) from hF.hasFDerivAt).comp_hasDerivAt
    p.2 hline
  exact hc.unique hd

/-- `∂²_x F(p)` is the derivative at `x` of `y ↦ ∂_x F(Λ, y)`, given near `x` by `g`. -/
theorem partialSndSnd_eq_of_hasDerivAt (hF : ContDiffAt ℝ 2 F p) {g : ℝ → ℝ} {d : ℝ}
    (hg : ∀ᶠ y in 𝓝 p.2, partialSnd F (p.1, y) = g y) (hd : HasDerivAt g d p.2) :
    partialSndSnd F p = d := by
  have hF1 : ContDiffAt ℝ 1 (fderiv ℝ F) p := hF.fderiv_right (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) p) (p.1, p.2) :=
    (hF1.differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun y : ℝ => ((p.1, y) : E × ℝ)) ((0, 1) : E × ℝ) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hc := (hD.comp_hasDerivAt p.2 hline).clm_apply (hasDerivAt_const p.2 ((0, 1) : E × ℝ))
  simp only [Function.comp_def, map_zero, add_zero] at hc
  have hc' : HasDerivAt g (fderiv ℝ (fderiv ℝ F) p (0, 1) (0, 1)) p.2 :=
    hc.congr_of_eventuallyEq (hg.mono fun y hy => by rw [← hy]; rfl)
  exact hc'.unique hd

end Partials

/-! ### Calculus of `arg` on the slit plane -/

theorem hasDerivAt_arg_comp {g : ℝ → ℂ} {g' : ℂ} {t : ℝ} (hg : HasDerivAt g g' t)
    (h : g t ∈ slitPlane) : HasDerivAt (fun s => arg (g s)) (g' / g t).im t := by
  have h2 := imCLM.hasFDerivAt.comp_hasDerivAt t (hg.clog_real h)
  simpa [Function.comp_def, log_im] using h2

theorem contDiffAt_arg {n : WithTop ℕ∞} {z : ℂ} (h : z ∈ slitPlane) :
    ContDiffAt ℝ n arg z := by
  have h1 : ContDiffAt ℝ n (fun z => (log z).im) z :=
    imCLM.contDiff.contDiffAt.comp z ((contDiffAt_log h).restrict_scalars ℝ)
  simpa [log_im] using h1

theorem mem_slitPlane_of_im_pos {z : ℂ} (h : 0 < z.im) : z ∈ slitPlane := Or.inr h.ne'

/-! ### The coordinates and the observable -/

section Observable

variable {nL nR : ℕ}

/-- Coordinates `(Γ, Q^L, Q^R, L)` of the state of the evolution at one point. -/
abbrev Coord (nL nR : ℕ) := ℂ × (Fin nL → ℂ) × (Fin nR → ℂ) × ℂ

/-- `f = Γ − √κ x`: the centred Loewner map recovered from the coordinates and `x = B_t`. -/
def coordF (κ : ℝ) (p : Coord nL nR × ℝ) : ℂ := p.1.1 - (Real.sqrt κ : ℂ) * (p.2 : ℂ)

/-- The mean `𝔥_t(z)` as a function of the coordinates and of `x = B_t`. -/
def meanObs (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (p : Coord nL nR × ℝ) : ℝ :=
  1 / Real.sqrt κ * (Real.pi * (1 + ∑ i, ρR i) - 2 * arg (coordF κ p)
    - (∑ i, ρL i * arg (p.1.2.1 i)) - ∑ i, ρR i * arg (p.1.2.2.1 i))
    - QuantumZipper.chiC κ * (p.1.2.2.2).im

/-- The open set where every argument of `meanObs` lies in `ℍ`. -/
def obsRegion (κ : ℝ) : Set (Coord nL nR × ℝ) :=
  {p | 0 < (coordF κ p).im ∧ (∀ i, 0 < (p.1.2.1 i).im) ∧ ∀ i, 0 < (p.1.2.2.1 i).im}

theorem contDiff_coordF (κ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (coordF κ : Coord nL nR × ℝ → ℂ) :=
  contDiff_fst.fst.sub (contDiff_const.mul (ofRealCLM.contDiff.comp contDiff_snd))

theorem contDiff_QL {n : WithTop ℕ∞} (i : Fin nL) :
    ContDiff ℝ n fun p : Coord nL nR × ℝ => p.1.2.1 i :=
  (contDiff_apply ℝ ℂ i).comp contDiff_fst.snd.fst

theorem contDiff_QR {n : WithTop ℕ∞} (i : Fin nR) :
    ContDiff ℝ n fun p : Coord nL nR × ℝ => p.1.2.2.1 i :=
  (contDiff_apply ℝ ℂ i).comp contDiff_fst.snd.snd.fst

theorem isOpen_obsRegion (κ : ℝ) : IsOpen (obsRegion κ : Set (Coord nL nR × ℝ)) := by
  have h : (obsRegion κ : Set (Coord nL nR × ℝ)) = {p | 0 < (coordF κ p).im} ∩
      (⋂ i, {p : Coord nL nR × ℝ | 0 < (p.1.2.1 i).im}) ∩
      ⋂ i, {p : Coord nL nR × ℝ | 0 < (p.1.2.2.1 i).im} := by
    ext p; simp [obsRegion, and_assoc]
  rw [h]
  refine ((isOpen_lt continuous_const (continuous_im.comp (contDiff_coordF κ (n := 0)).continuous)).inter
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (continuous_im.comp (contDiff_QL (n := 0) i).continuous))).inter
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (continuous_im.comp (contDiff_QR (n := 0) i).continuous))

theorem contDiffAt_meanObs (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : WithTop ℕ∞}
    {p : Coord nL nR × ℝ} (hp : p ∈ obsRegion κ) : ContDiffAt ℝ n (meanObs κ ρL ρR) p := by
  have h0 : ContDiffAt ℝ n (fun q : Coord nL nR × ℝ => arg (coordF κ q)) p :=
    (contDiffAt_arg (mem_slitPlane_of_im_pos hp.1)).comp p (contDiff_coordF κ).contDiffAt
  have hL : ∀ i ∈ (Finset.univ : Finset (Fin nL)), ContDiffAt ℝ n
      (fun q : Coord nL nR × ℝ => ρL i * arg (q.1.2.1 i)) p := fun i _ =>
    contDiffAt_const.mul ((contDiffAt_arg (mem_slitPlane_of_im_pos (hp.2.1 i))).comp p
      (contDiff_QL i).contDiffAt)
  have hR : ∀ i ∈ (Finset.univ : Finset (Fin nR)), ContDiffAt ℝ n
      (fun q : Coord nL nR × ℝ => ρR i * arg (q.1.2.2.1 i)) p := fun i _ =>
    contDiffAt_const.mul ((contDiffAt_arg (mem_slitPlane_of_im_pos (hp.2.2 i))).comp p
      (contDiff_QR i).contDiffAt)
  have him : ContDiffAt ℝ n (fun q : Coord nL nR × ℝ => (q.1.2.2.2).im) p :=
    (imCLM.contDiff.comp contDiff_fst.snd.snd.snd).contDiffAt
  exact (contDiffAt_const.mul (((contDiffAt_const.sub (contDiffAt_const.mul h0)).sub
    (ContDiffAt.sum hL)).sub (ContDiffAt.sum hR))).sub (contDiffAt_const.mul him)

theorem contDiffOn_meanObs (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (meanObs κ ρL ρR) (obsRegion κ) := fun _ hp =>
  (contDiffAt_meanObs κ ρL ρR hp).contDiffWithinAt

/-- The value of `meanObs` at a state: the explicit mean at `f = Γ − √κ x` minus `χ Im L`. -/
theorem meanObs_eq_meanHarmonic (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {p : Coord nL nR × ℝ} {aL : Fin nL → ℝ} {aR : Fin nR → ℝ}
    (hQL : ∀ i, p.1.2.1 i = coordF κ p - aL i) (hQR : ∀ i, p.1.2.2.1 i = coordF κ p - aR i) :
    meanObs κ ρL ρR p = meanHarmonic κ ρL ρR aL aR (coordF κ p) -
      QuantumZipper.chiC κ * (p.1.2.2.2).im := by
  simp only [meanObs, meanHarmonic, hQL, hQR]

/-! ### Derivatives of the observable -/

theorem hasDerivAt_coordF_snd (κ : ℝ) (e : Coord nL nR) (y : ℝ) :
    HasDerivAt (fun y : ℝ => coordF κ ((e, y) : Coord nL nR × ℝ)) (-(Real.sqrt κ : ℂ)) y := by
  have h := ((hasDerivAt_id y).ofReal_comp.const_mul (Real.sqrt κ : ℂ)).const_sub e.1
  simpa [coordF] using h

/-- `∂_x meanObs = (1/√κ)(−2 Im(−√κ/f))`, `f = Γ − √κ x`. -/
theorem partialSnd_meanObs (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {p : Coord nL nR × ℝ}
    (hp : p ∈ obsRegion κ) :
    partialSnd (meanObs κ ρL ρR) p =
      1 / Real.sqrt κ * -(2 * ((-(Real.sqrt κ : ℂ)) / coordF κ p).im) := by
  refine partialSnd_eq_of_hasDerivAt
    ((contDiffAt_meanObs κ ρL ρR (n := 1) hp).differentiableAt one_ne_zero) ?_
  have harg := hasDerivAt_arg_comp (hasDerivAt_coordF_snd κ p.1 p.2)
    (mem_slitPlane_of_im_pos hp.1)
  have h := ((((harg.const_mul 2).const_sub (Real.pi * (1 + ∑ i, ρR i))).sub_const
    (∑ i, ρL i * arg (p.1.2.1 i))).sub_const (∑ i, ρR i * arg (p.1.2.2.1 i))).const_mul
      (1 / Real.sqrt κ) |>.sub_const (QuantumZipper.chiC κ * (p.1.2.2.2).im)
  simpa [meanObs] using h

/-- `∂²_x meanObs = (1/√κ)(−2 Im(−(√κ)²/f²))`. -/
theorem partialSndSnd_meanObs (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {p : Coord nL nR × ℝ}
    (hp : p ∈ obsRegion κ) :
    partialSndSnd (meanObs κ ρL ρR) p =
      1 / Real.sqrt κ * -(2 * ((-(Real.sqrt κ : ℂ) ^ 2) / coordF κ p ^ 2).im) := by
  refine partialSndSnd_eq_of_hasDerivAt (contDiffAt_meanObs κ ρL ρR hp)
    (g := fun y => 1 / Real.sqrt κ * -(2 * ((-(Real.sqrt κ : ℂ)) /
      coordF κ ((p.1, y) : Coord nL nR × ℝ)).im)) ?_ ?_
  · have hopen : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : Coord nL nR × ℝ) ∈ obsRegion κ := by
      have hc : Continuous fun y : ℝ => ((p.1, y) : Coord nL nR × ℝ) :=
        continuous_const.prodMk continuous_id
      exact hc.continuousAt.preimage_mem_nhds ((isOpen_obsRegion κ).mem_nhds hp)
    exact hopen.mono fun y hy => partialSnd_meanObs κ ρL ρR hy
  · have hne : coordF κ ((p.1, p.2) : Coord nL nR × ℝ) ≠ 0 := fun h => by
      have := hp.1; rw [show p = (p.1, p.2) from rfl, h] at this; simp at this
    have hdiv := (hasDerivAt_const p.2 (-(Real.sqrt κ : ℂ))).div
      (hasDerivAt_coordF_snd κ p.1 p.2) hne
    have him := imCLM.hasFDerivAt.comp_hasDerivAt p.2 hdiv
    have h := ((him.const_mul 2).neg).const_mul (1 / Real.sqrt κ)
    refine h.congr_deriv ?_
    have e : (0 * coordF κ p - -(Real.sqrt κ : ℂ) * -(Real.sqrt κ : ℂ)) / coordF κ p ^ 2 =
        -(Real.sqrt κ : ℂ) ^ 2 / coordF κ p ^ 2 := by ring
    simp only [imCLM_apply, Prod.mk.eta, e]

/-- `∂_Λ meanObs (p) v`: the derivative of `meanObs` in the coordinates, in the direction `v`. -/
theorem partialFst_meanObs (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {p : Coord nL nR × ℝ}
    (hp : p ∈ obsRegion κ) (v : Coord nL nR) :
    partialFst (meanObs κ ρL ρR) p v =
      1 / Real.sqrt κ * (-(2 * (v.1 / coordF κ p).im) - (∑ i, ρL i * (v.2.1 i / p.1.2.1 i).im)
        - ∑ i, ρR i * (v.2.2.1 i / p.1.2.2.1 i).im) - QuantumZipper.chiC κ * v.2.2.2.im := by
  refine partialFst_eq_of_hasDerivAt
    ((contDiffAt_meanObs κ ρL ρR (n := 1) hp).differentiableAt one_ne_zero) ?_
  have hf : HasDerivAt (fun t : ℝ => coordF κ ((p.1 + t • v, p.2) : Coord nL nR × ℝ)) v.1 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v.1).const_add (coordF κ p)
    refine (h1.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [coordF, Complex.real_smul]; ring
  have hf0 : coordF κ ((p.1 + (0 : ℝ) • v, p.2) : Coord nL nR × ℝ) = coordF κ p := by simp
  have hQL : ∀ i, HasDerivAt (fun t : ℝ => (p.1 + t • v).2.1 i) (v.2.1 i) 0 := fun i => by
    have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (v.2.1 i)).const_add (p.1.2.1 i)
    refine (h1.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [Complex.real_smul]
  have hQR : ∀ i, HasDerivAt (fun t : ℝ => (p.1 + t • v).2.2.1 i) (v.2.2.1 i) 0 := fun i => by
    have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (v.2.2.1 i)).const_add
      (p.1.2.2.1 i)
    refine (h1.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [Complex.real_smul]
  have hL : HasDerivAt (fun t : ℝ => ((p.1 + t • v).2.2.2).im) v.2.2.2.im 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const v.2.2.2.im).const_add (p.1.2.2.2).im
    refine (h1.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [Complex.real_smul]
  have hA := hasDerivAt_arg_comp hf (by rw [hf0]; exact mem_slitPlane_of_im_pos hp.1)
  have hAL : ∀ i ∈ (Finset.univ : Finset (Fin nL)), HasDerivAt
      (fun t : ℝ => ρL i * arg ((p.1 + t • v).2.1 i)) (ρL i * (v.2.1 i / p.1.2.1 i).im) 0 :=
    fun i _ => by
      have := (hasDerivAt_arg_comp (hQL i) (by simpa using mem_slitPlane_of_im_pos (hp.2.1 i)))
      simpa using this.const_mul (ρL i)
  have hAR : ∀ i ∈ (Finset.univ : Finset (Fin nR)), HasDerivAt
      (fun t : ℝ => ρR i * arg ((p.1 + t • v).2.2.1 i)) (ρR i * (v.2.2.1 i / p.1.2.2.1 i).im) 0 :=
    fun i _ => by
      have := (hasDerivAt_arg_comp (hQR i) (by simpa using mem_slitPlane_of_im_pos (hp.2.2 i)))
      simpa using this.const_mul (ρR i)
  have h := ((((hA.const_mul 2).const_sub (Real.pi * (1 + ∑ i, ρR i))).sub
    (HasDerivAt.sum hAL)).sub (HasDerivAt.sum hAR)).const_mul (1 / Real.sqrt κ) |>.sub
      (hL.const_mul (QuantumZipper.chiC κ))
  rw [hf0] at h
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [meanObs, Finset.sum_apply, Pi.sub_apply]

/-! ### The drift of the mean vanishes -/

/-- The time-density of the coordinates when the centred force-point positions are `aL, aR`
(`a = V − W`) and `f = f_t(z)`: `dΓ = (2/f − μ) dt` with `μ = ∑ ρ/(W − V)`, `dQ_i = (2/f − 2/aᵢ) dt`,
`dL = −2/f² dt`. -/
def coordDensity (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (aL : Fin nL → ℝ) (aR : Fin nR → ℝ) (f : ℂ) :
    Coord nL nR :=
  (2 / f - ((∑ i, ρL i / (-aL i) + ∑ i, ρR i / (-aR i) : ℝ) : ℂ),
    fun i => 2 / f - ((2 / aL i : ℝ) : ℂ), fun i => 2 / f - ((2 / aR i : ℝ) : ℂ), -(2 / f ^ 2))

theorem im_two_div_sub_div (f : ℂ) (hf : f ≠ 0) {a : ℝ} (ha : a ≠ 0) (hfa : f - a ≠ 0) :
    ((2 / f - ((2 / a : ℝ) : ℂ)) / (f - a)).im = -(2 / a) * (f⁻¹).im := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have e : (2 / f - ((2 / a : ℝ) : ℂ)) / (f - a) = ((-(2 / a) : ℝ) : ℂ) * f⁻¹ := by
    push_cast
    field_simp
    ring
  rw [e, im_ofReal_mul]

/-- **The Itô drift of the mean vanishes** (Specification L500, `d𝔥*_t = (2/f_t) dB_t`): at a state with
centred force-point positions `aL, aR` none of which is `0` (no force point on the driver), the generator of
`meanObs` applied to the coordinate density is `0`. The `ρ`-terms cancel between `Γ` and the `Q`'s, and the
`1/f²`-terms cancel because `2χ = 4/√κ − √κ`. -/
theorem itoGen_meanObs_eq_zero {κ : ℝ} (hκ : 0 < κ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {p : Coord nL nR × ℝ} (hp : p ∈ obsRegion κ) {aL : Fin nL → ℝ} {aR : Fin nR → ℝ}
    (hQL : ∀ i, p.1.2.1 i = coordF κ p - aL i) (hQR : ∀ i, p.1.2.2.1 i = coordF κ p - aR i)
    (haL : ∀ i, aL i ≠ 0) (haR : ∀ i, aR i ≠ 0) :
    itoGen (meanObs κ ρL ρR) p (coordDensity ρL ρR aL aR (coordF κ p)) = 0 := by
  unfold itoGen
  rw [partialFst_meanObs κ ρL ρR hp, partialSndSnd_meanObs κ ρL ρR hp]
  set f := coordF κ p with hfdef
  have hf : f ≠ 0 := fun h => by have := hp.1; rw [← hfdef, h] at this; simp at this
  have hQL0 : ∀ i, f - aL i ≠ 0 := fun i h => by
    have := hp.2.1 i; rw [hQL i, h] at this; simp at this
  have hQR0 : ∀ i, f - aR i ≠ 0 := fun i h => by
    have := hp.2.2 i; rw [hQR i, h] at this; simp at this
  set μ : ℝ := ∑ i, ρL i / (-aL i) + ∑ i, ρR i / (-aR i) with hμ
  have e1 : ((2 / f - (μ : ℂ)) / f).im = 2 * (f⁻¹ ^ 2).im - μ * (f⁻¹).im := by
    have e : (2 / f - (μ : ℂ)) / f = ((2 : ℝ) : ℂ) * f⁻¹ ^ 2 - (μ : ℂ) * f⁻¹ := by
      field_simp; push_cast; ring
    rw [e, sub_im, im_ofReal_mul, im_ofReal_mul]
  have e3 : (-(2 / f ^ 2)).im = -2 * (f⁻¹ ^ 2).im := by
    have e : -(2 / f ^ 2) = ((-2 : ℝ) : ℂ) * f⁻¹ ^ 2 := by field_simp; push_cast; ring
    rw [e, im_ofReal_mul]
  have e4 : (-(Real.sqrt κ : ℂ) ^ 2 / f ^ 2).im = -(Real.sqrt κ ^ 2) * (f⁻¹ ^ 2).im := by
    have e : -(Real.sqrt κ : ℂ) ^ 2 / f ^ 2 = ((-(Real.sqrt κ ^ 2) : ℝ) : ℂ) * f⁻¹ ^ 2 := by
      field_simp; push_cast; ring
    rw [e, im_ofReal_mul]
  have eL : ∑ i, ρL i * ((2 / f - ((2 / aL i : ℝ) : ℂ)) / p.1.2.1 i).im =
      -(2 * (f⁻¹).im) * ∑ i, ρL i / aL i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQL i, im_two_div_sub_div f hf (haL i) (hQL0 i)]
    ring
  have eR : ∑ i, ρR i * ((2 / f - ((2 / aR i : ℝ) : ℂ)) / p.1.2.2.1 i).im =
      -(2 * (f⁻¹).im) * ∑ i, ρR i / aR i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQR i, im_two_div_sub_div f hf (haR i) (hQR0 i)]
    ring
  have hμ' : μ = -(∑ i, ρL i / aL i) - ∑ i, ρR i / aR i := by
    rw [hμ]
    simp only [div_neg, Finset.sum_neg_distrib]
    ring
  simp only [coordDensity]
  rw [e1, eL, eR, e3, e4, hμ']
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  rw [QuantumZipper.chiC]
  field_simp
  ring

/-- `∂_x meanObs = 2 Im(1/f) = Im(2/f)`: the coefficient of `dB_t` in (3.15). -/
theorem partialSnd_meanObs_eq {κ : ℝ} (hκ : 0 < κ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {p : Coord nL nR × ℝ} (hp : p ∈ obsRegion κ) :
    partialSnd (meanObs κ ρL ρR) p = (2 / coordF κ p).im := by
  rw [partialSnd_meanObs κ ρL ρR hp]
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have e : (-(Real.sqrt κ : ℂ)) / coordF κ p = ((-(Real.sqrt κ / 2) : ℝ) : ℂ) * (2 / coordF κ p) := by
    push_cast; ring
  rw [e, im_ofReal_mul]
  field_simp

end Observable

end Ito

end InteractingSLE
