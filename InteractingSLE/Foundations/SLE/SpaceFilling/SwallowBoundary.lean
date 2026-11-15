import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Foundations.Loewner.YuanTrace
import InteractingSLE.Foundations.SLE.SpaceFilling

/-!
# Boundary behaviour of the Loewner maps at swallowing times

Packet `planning/packets/PROVE-RS05-74b.md`. Deterministic part of the proof of [RS05, Lemma 7.3]
for `4 < κ < 8` (Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), p. 33, pinned
`source/external/RS05/arxiv-latex/SLEcont.tex` lines 2310–2340).

* **A monotone angle.** For `z ∈ ℍ` and a real point `x`, the cotangent of the angle of
  `g_t(z) − g_t(x)` is monotone in `t` (decreasing if `x > 0`, increasing if `x < 0`): the
  difference solves `h' = −2h/(Z_t X_t)`, which involves no driving noise. At the swallowing time of
  `x` it bounds the direction of `f_σ(z)` (`cot_fwdMap_le_of_realSwallowAt`,
  `le_cot_fwdMap_of_realSwallowAt`). This replaces the cluster-set argument of [RS05] ("`S` is the
  set of limit points of `g_{τ(1)}(z)` as `z → 0` … then `S ⊂ (−∞, W(τ(1)))`").
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE

variable {W : ℝ → ℝ}

/-! ### The monotone angle -/

/-- Real and imaginary parts of `2/u − 2/r`. -/
theorem re_two_div_sub_two_div (u : ℂ) (r : ℝ) :
    (2 / u - 2 / (r : ℂ)).re = 2 * u.re / (u.re ^ 2 + u.im ^ 2) - 2 / r := by
  rw [Complex.sub_re, Complex.div_re, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
    Complex.ofReal_re, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  ring

theorem im_two_div_sub_two_div (u : ℂ) (r : ℝ) :
    (2 / u - 2 / (r : ℂ)).im = -2 * u.im / (u.re ^ 2 + u.im ^ 2) := by
  rw [Complex.sub_im, Complex.div_im, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
    Complex.ofReal_im, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The numerator of the derivative of the cotangent `Re h / Im h`, `h = u − r`, along the flow:
it equals `−2 Im u |u − r|² / (r |u|²)`. -/
theorem cot_numerator_eq (u : ℂ) (r : ℝ) (hu : u.im ≠ 0) (hr : r ≠ 0) :
    (2 / u - 2 / (r : ℂ)).re * (u - r).im - (u - r).re * (2 / u - 2 / (r : ℂ)).im =
      -2 * u.im * ((u.re - r) ^ 2 + u.im ^ 2) / (r * (u.re ^ 2 + u.im ^ 2)) := by
  rw [re_two_div_sub_two_div, im_two_div_sub_two_div]
  have hN : u.re ^ 2 + u.im ^ 2 ≠ 0 := by positivity
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.sub_re, Complex.ofReal_re]
  field_simp
  ring

/-- **The angle is monotone.** Let `u` solve the flow from `z ∈ ℍ` and `v` the flow from a real
point on `[0, s]`. Then `t ↦ Re(u t − v t)/Im(u t − v t)` has derivative of sign `−sign(v)`. -/
theorem hasDerivWithinAt_cot (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) {x s : ℝ}
    {u v : ℝ → ℂ} (hu : IsForwardSol W z s u) (hv : IsForwardSol W (x : ℂ) s v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) s) :
    HasDerivWithinAt (fun t => (u t - v t).re / (u t - v t).im)
      (-2 * (u t).im * (((u t).re - (v t).re) ^ 2 + (u t).im ^ 2) /
        ((v t).re * ((u t).re ^ 2 + (u t).im ^ 2)) / (u t - v t).im ^ 2) (Icc 0 s) t := by
  have hs : 0 ≤ s := ht.1.trans ht.2
  have hvim : (v t).im = 0 := im_isForwardSol_real hW hs hv t ht
  have hvr : v t = ((v t).re : ℂ) := Complex.ext (by simp) (by simp [hvim])
  have huim : 0 < (u t).im := FwdClock.sol_im_pos hW hz hu ht
  have hvre : (v t).re ≠ 0 := fun h => (hv.2 t ht).1 (by rw [hvr, h]; simp)
  have hd : HasDerivWithinAt (fun t => u t - v t) (2 / u t - 2 / v t) (Icc 0 s) t := by
    have h := (FwdHolo.hasDerivWithinAt_shift hu ht).sub (FwdHolo.hasDerivWithinAt_shift hv ht)
    have e : (fun t => u t - v t) = (fun s => u s + (W s : ℂ)) - (fun s => v s + (W s : ℂ)) := by
      funext r; simp only [Pi.sub_apply]; ring
    rw [e]; exact h
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have himne : (u t - v t).im ≠ 0 := by
    rw [Complex.sub_im, hvim, sub_zero]; exact huim.ne'
  have hq := hre.div him himne
  have hq' : HasDerivWithinAt (fun t => (u t - v t).re / (u t - v t).im)
      (((2 / u t - 2 / v t).re * (u t - v t).im - (u t - v t).re * (2 / u t - 2 / v t).im) /
        (u t - v t).im ^ 2) (Icc 0 s) t := hq
  have hnum := cot_numerator_eq (u t) (v t).re huim.ne' hvre
  rw [← hvr] at hnum
  rw [← hnum]
  exact hq'

/-- For a real point `x > 0` the cotangent `Re(g_t z − g_t x)/Im(g_t z − g_t x)` decreases. -/
theorem antitoneOn_cot (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) {x s : ℝ}
    {u v : ℝ → ℂ} (hu : IsForwardSol W z s u) (hv : IsForwardSol W (x : ℂ) s v)
    (hpos : ∀ t ∈ Icc (0 : ℝ) s, 0 < (v t).re) :
    AntitoneOn (fun t => (u t - v t).re / (u t - v t).im) (Icc 0 s) := by
  have hd := fun t (ht : t ∈ Icc (0 : ℝ) s) => hasDerivWithinAt_cot hW hz hu hv ht
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 s)
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset) (fun t ht => ?_)
  have ht' := interior_subset ht
  have huim := FwdClock.sol_im_pos hW hz hu ht'
  have hvpos := hpos t ht'
  refine div_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg ?_ (by positivity))
    (sq_nonneg _)
  have : 0 ≤ ((u t).re - (v t).re) ^ 2 + (u t).im ^ 2 := by positivity
  nlinarith

/-- For a real point `x < 0` the cotangent increases. -/
theorem monotoneOn_cot (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) {x s : ℝ}
    {u v : ℝ → ℂ} (hu : IsForwardSol W z s u) (hv : IsForwardSol W (x : ℂ) s v)
    (hneg : ∀ t ∈ Icc (0 : ℝ) s, (v t).re < 0) :
    MonotoneOn (fun t => (u t - v t).re / (u t - v t).im) (Icc 0 s) := by
  have hd := fun t (ht : t ∈ Icc (0 : ℝ) s) => hasDerivWithinAt_cot hW hz hu hv ht
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s)
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset) (fun t ht => ?_)
  have ht' := interior_subset ht
  have huim := FwdClock.sol_im_pos hW hz hu ht'
  have hvneg := hneg t ht'
  refine div_nonneg (div_nonneg_of_nonpos ?_ ?_) (sq_nonneg _)
  · have : 0 ≤ ((u t).re - (v t).re) ^ 2 + (u t).im ^ 2 := by positivity
    nlinarith
  · have : 0 ≤ (u t).re ^ 2 + (u t).im ^ 2 := by positivity
    nlinarith

/-- A real solution from `x < 0` stays negative. -/
theorem re_neg_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x s : ℝ} (hx : x < 0)
    {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) s v) : ∀ t ∈ Icc (0 : ℝ) s, (v t).re < 0 := by
  intro t ht
  have h := isForwardSol_neg hv
  rw [← Complex.ofReal_neg] at h
  have := re_pos_isForwardSol_real (W := fun t => -W t) (by fun_prop) (ht.1.trans ht.2) h
    (by simp only [hW0, neg_zero]; linarith) t ht
  simp only [Complex.neg_re] at this
  linarith

/-- At its swallowing time the flow from a real point `x < 0` tends to `0` (reflection of
`tendsto_fwdMap_of_realSwallowAt`). -/
theorem tendsto_fwdMap_of_realSwallowAt_neg (hW : Continuous W) (hW0 : W 0 = 0) {x σ : ℝ}
    (hx : x < 0) (h : RealSwallowAt W x σ) :
    Tendsto (fun s => fwdMap W s x) (𝓝[<] σ) (𝓝 0) := by
  have h' : RealSwallowAt (fun t => -W t) (-x) σ := realSwallowAt_neg_iff.2 h
  have hlim := tendsto_fwdMap_of_realSwallowAt (W := fun t => -W t) (by fun_prop)
    (by simp [hW0]) (by linarith) h'
  have hlim' := hlim.neg
  rw [neg_zero] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT h.1] with s hs
  obtain ⟨v, hv⟩ := h.2.1 s ⟨hs.1.le, hs.2⟩
  rw [fwdMap_neg_real hW hv ⟨hs.1.le, le_rfl⟩, neg_neg]

/-- The cotangent of `g_t(z) − g_t(x)` tends to that of `f_σ(z)` at the swallowing time of `x`. -/
theorem tendsto_cot_of_tendsto (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) {σ : ℝ} (hσ : 0 < σ)
    {u : ℝ → ℂ} (hu : IsForwardSol W z σ u) {X : ℝ → ℂ} (hX : Tendsto X (𝓝[<] σ) (𝓝 0)) :
    Tendsto (fun t => (u t - X t).re / (u t - X t).im) (𝓝[<] σ)
      (𝓝 ((u σ).re / (u σ).im)) := by
  have hu' : Tendsto u (𝓝[<] σ) (𝓝 (u σ)) := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hσ]
    exact (hu.1 σ ⟨hσ.le, le_rfl⟩).tendsto.mono_left (nhdsWithin_mono _ Ico_subset_Icc_self)
  have h := hu'.sub hX
  rw [sub_zero] at h
  have himne : (u σ).im ≠ 0 := (FwdClock.sol_im_pos hW hz hu ⟨hσ.le, le_rfl⟩).ne'
  have hc : ContinuousAt (fun w : ℂ => w.re / w.im) (u σ) :=
    Complex.continuous_re.continuousAt.div Complex.continuous_im.continuousAt himne
  exact hc.tendsto.comp h

/-- **The angle at the swallowing time of a positive real point.** If `x > 0` is swallowed at
`σ` and `z ∈ ℍ \ K_σ`, then `Re f_σ(z)/Im f_σ(z) ≤ (Re z − x)/Im z`. -/
theorem cot_fwdMap_le_of_realSwallowAt (hW : Continuous W) (hW0 : W 0 = 0) {x σ : ℝ}
    (hx : 0 < x) (hsw : RealSwallowAt W x σ) {z : ℂ} (hz : z ∈ H \ fwdHull W σ) :
    (fwdMap W σ z).re / (fwdMap W σ z).im ≤ (z.re - x) / z.im := by
  have hσ := hsw.1
  have hzim : 0 < z.im := hz.1
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hσ.le hz.1 hz.2
  rw [fwdMap_eq hW hzim hu ⟨hσ.le, le_rfl⟩]
  refine le_of_tendsto (tendsto_cot_of_tendsto hW hzim hσ hu
    (tendsto_fwdMap_of_realSwallowAt hW hW0 hx hsw)) ?_
  filter_upwards [Ioo_mem_nhdsLT hσ] with s hs
  obtain ⟨v, hv⟩ := hsw.2.1 s ⟨hs.1.le, hs.2⟩
  have hus : IsForwardSol W z s u := isForwardSol_restrict hu hs.1.le hs.2.le
  have hanti := antitoneOn_cot hW hzim hus hv
    (fun t ht => re_pos_isForwardSol_real hW hs.1.le hv (by rw [hW0]; exact hx) t ht)
  have h0 := hanti ⟨le_rfl, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ hs.1.le
  have hu0 : u 0 = z := by rw [FwdHolo.sol_zero hu hσ.le, hW0]; simp
  have hv0 : v 0 = x := by rw [FwdHolo.sol_zero hv hs.1.le, hW0]; simp
  simp only at h0
  rw [fwdMap_eq_of_isForwardSol hW hv ⟨hs.1.le, le_rfl⟩]
  refine h0.trans (le_of_eq ?_)
  rw [hu0, hv0]
  simp

/-- **The angle at the swallowing time of a negative real point.** If `x < 0` is swallowed at
`σ` and `z ∈ ℍ \ K_σ`, then `(Re z − x)/Im z ≤ Re f_σ(z)/Im f_σ(z)`. -/
theorem le_cot_fwdMap_of_realSwallowAt (hW : Continuous W) (hW0 : W 0 = 0) {x σ : ℝ}
    (hx : x < 0) (hsw : RealSwallowAt W x σ) {z : ℂ} (hz : z ∈ H \ fwdHull W σ) :
    (z.re - x) / z.im ≤ (fwdMap W σ z).re / (fwdMap W σ z).im := by
  have hσ := hsw.1
  have hzim : 0 < z.im := hz.1
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hσ.le hz.1 hz.2
  rw [fwdMap_eq hW hzim hu ⟨hσ.le, le_rfl⟩]
  refine ge_of_tendsto (tendsto_cot_of_tendsto hW hzim hσ hu
    (tendsto_fwdMap_of_realSwallowAt_neg hW hW0 hx hsw)) ?_
  filter_upwards [Ioo_mem_nhdsLT hσ] with s hs
  obtain ⟨v, hv⟩ := hsw.2.1 s ⟨hs.1.le, hs.2⟩
  have hus : IsForwardSol W z s u := isForwardSol_restrict hu hs.1.le hs.2.le
  have hmono := monotoneOn_cot hW hzim hus hv (re_neg_of_isForwardSol hW hW0 hx hv)
  have h0 := hmono ⟨le_rfl, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ hs.1.le
  have hu0 : u 0 = z := by rw [FwdHolo.sol_zero hu hσ.le, hW0]; simp
  have hv0 : v 0 = x := by rw [FwdHolo.sol_zero hv hs.1.le, hW0]; simp
  simp only at h0
  rw [fwdMap_eq_of_isForwardSol hW hv ⟨hs.1.le, le_rfl⟩]
  refine (le_of_eq ?_).trans h0
  rw [hu0, hv0]
  simp

/-! ### Traces, extensions and the flow identity -/

/-- **The Rohde–Schramm form of the generation property gives a continuous Loewner trace**
(`H \ K_t` is the unbounded component of `ℍ \ γ[0,t]`, so `K_t = fill(γ[0,t])`). -/
theorem isLoewnerTrace_of_forall_bound {γ : ℝ → ℂ} (h0 : γ 0 = 0) (hc : ContinuousOn γ (Ici 0))
    (hgen : ∀ t : ℝ, 0 ≤ t → ∀ M : ℝ, (∀ s ∈ Icc 0 t, ‖γ s‖ < M) →
      H \ fwdHull W t = connectedComponentIn (H \ γ '' Icc 0 t) (M * Complex.I)) :
    IsLoewnerTrace W γ := by
  refine ⟨h0, hc, fun t ht => ?_⟩
  have hK : IsCompact (γ '' Icc 0 t) :=
    isCompact_Icc.image_of_continuousOn (hc.mono Icc_subset_Ici_self)
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall 0
  set R := max C 0 + 1 with hRdef
  have hR : 0 < R := by positivity
  have hKR : γ '' Icc 0 t ⊆ Metric.ball 0 R := fun w hw => by
    have := hC hw
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_ball, dist_zero_right]
    linarith [le_max_left C 0]
  have hcl : closure (γ '' Icc 0 t) = γ '' Icc 0 t := hK.isClosed.closure_eq
  have e1 := H_diff_fillH hR (by rw [hcl]; exact hKR)
  rw [hcl] at e1
  have e2 := hgen t ht (R + 1) fun s hs => by
    have := hKR ⟨s, hs, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at this
    linarith
  have e : H \ fwdHull W t = H \ fillH (γ '' Icc 0 t) := by rw [e1, e2]
  ext z
  constructor
  · intro hz
    by_contra hz'
    have hmem : z ∈ H \ fillH (γ '' Icc 0 t) := ⟨(fwdHull_mono (W := W)).2 t hz, hz'⟩
    rw [← e] at hmem
    exact hmem.2 hz
  · intro hz
    by_contra hz'
    have hmem : z ∈ H \ fwdHull W t := ⟨fillH_subset_H _ hz, hz'⟩
    rw [e] at hmem
    exact hmem.2 hz

/-- A vertical approach to a real point from inside `ℍ`. -/
theorem tendsto_vertical (a : ℝ) :
    Tendsto (fun n : ℕ => (a : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop
      (𝓝[H] (a : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have h : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (h.mul_const Complex.I).const_add (a : ℂ)
    simpa using h2
  · show 0 < ((a : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
    positivity

theorem vertical_mem_H (a : ℝ) (n : ℕ) :
    (a : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I ∈ H := by
  show 0 < ((a : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
  positivity

theorem ofReal_mem_Hbar (a : ℝ) : (a : ℂ) ∈ Hbar := by
  show 0 ≤ (a : ℂ).im
  simp

/-- **Composition of forward maps** (`f_{s+r} = f^{(s)}_r ∘ f_s`, from the flow identity
`RS.fwdMapInv_add_shift` of the inverse maps). -/
theorem fwdMap_add_shift (hW : Continuous W) (hW0 : W 0 = 0) {s r : ℝ} (hs : 0 ≤ s)
    (hr : 0 ≤ r) {z : ℂ} (hz : z ∈ H \ fwdHull W (s + r)) :
    fwdMap W s z ∈ H \ fwdHull (shiftDrive W s) r ∧
      fwdMap (shiftDrive W s) r (fwdMap W s z) = fwdMap W (s + r) z := by
  have hWs := continuous_shiftDrive hW s
  have hWs0 := shiftDrive_zero W s
  set w := fwdMap W (s + r) z with hwdef
  have hw : w ∈ H := FwdHolo.mapsTo_fwdMap hW (add_nonneg hs hr) hz
  set ζ := fwdMapInv (shiftDrive W s) r w with hζdef
  have hζ : ζ ∈ H \ fwdHull (shiftDrive W s) r := fwdMapInv_mem_compl_fwdHull hWs hWs0 hr hw
  have hz' : z = fwdMapInv W s ζ := by
    rw [← fwdMapInv_add_shift hW hW0 hs hr hw, hwdef, fwdMapInv_fwdMap hW hW0 (add_nonneg hs hr) hz]
  have h1 : fwdMap W s z = ζ := by rw [hz', fwdMap_fwdMapInv hW hW0 hs hζ.1]
  refine ⟨h1 ▸ hζ, ?_⟩
  rw [h1, hζdef, fwdMap_fwdMapInv hWs hWs0 hr hw]

/-! ### A swallowed real point on the boundary sits at the tip -/

/-- **A real point that is still on the boundary at its swallowing time is the tip.** Let `η` be a
continuous Loewner trace of `W`, and let `v ≠ 0` be swallowed at `σ`. If the boundary extension
`F̄_σ` of `F_σ = fwdMapInv W σ` takes the value `v` at a real point `u₀`, then `u₀ = 0` (so `v`
is the tip `F̄_σ(0) = η(σ)`). Proof: for `s < σ`, `F_σ = F_s ∘ F^{(s)}_{σ−s}`; points `w → u₀`
are moved by `F^{(s)}_{σ−s}` by at most `24 osc W|[s,σ] + 8√(σ−s)`, and `F_s(ζ) → v` forces
`ζ = f_s(F_s ζ) → X_s(v)` (`tendsto_fwdMap_of_isForwardSol`). Hence
`|X_s(v) − u₀| ≤ 24 osc W|[s,σ] + 8√(σ − s)`, and `X_s(v) → 0` as `s ↑ σ`. -/
theorem eq_zero_of_extendFrom_eq_of_realSwallowAt {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {v σ : ℝ} (hv : v ≠ 0) (hsw : RealSwallowAt W v σ)
    {u₀ : ℝ} (hu₀ : extendFrom H (fwdMapInv W σ) u₀ = v) : u₀ = 0 := by
  have hσ := hsw.1
  have hX : Tendsto (fun s => fwdMap W s v) (𝓝[<] σ) (𝓝 0) := by
    rcases lt_or_gt_of_ne hv with h | h
    · exact tendsto_fwdMap_of_realSwallowAt_neg hW hW0 h hsw
    · exact tendsto_fwdMap_of_realSwallowAt hW hW0 h hsw
  set w : ℕ → ℂ := fun n => (u₀ : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hwdef
  have hwH : ∀ n, w n ∈ H := vertical_mem_H u₀
  have hlimF : Tendsto (fun n => fwdMapInv W σ (w n)) atTop (𝓝 (v : ℂ)) := by
    have h := ((hη.hasBdryLimits hW hW0 hσ.le).tendsto (ofReal_mem_Hbar u₀)).comp
      (tendsto_vertical u₀)
    rw [hu₀] at h
    exact h
  have key : ∀ s ∈ Ico (0 : ℝ) σ, ∀ M : ℝ, (∀ r ∈ Icc (0 : ℝ) (σ - s), |shiftDrive W s r| ≤ M) →
      ‖fwdMap W s v - u₀‖ ≤ 24 * M + 8 * Real.sqrt (σ - s) := by
    intro s hs M hM
    obtain ⟨sol, hsol⟩ := hsw.2.1 s hs
    have hWs := continuous_shiftDrive hW s
    have hWs0 := shiftDrive_zero W s
    have hσs : 0 ≤ σ - s := sub_nonneg.2 hs.2.le
    set ζ : ℕ → ℂ := fun n => fwdMapInv (shiftDrive W s) (σ - s) (w n) with hζdef
    have hζH : ∀ n, ζ n ∈ H := fun n => fwdMapInv_mem_H hWs hWs0 hσs (hwH n)
    have hFs : ∀ n, fwdMapInv W s (ζ n) = fwdMapInv W σ (w n) := fun n => by
      have := fwdMapInv_add_shift hW hW0 hs.1 hσs (hwH n)
      rw [show s + (σ - s) = σ by ring] at this
      exact this.symm
    have hin : Tendsto (fun n => fwdMapInv W s (ζ n)) atTop (𝓝[H] (v : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => fwdMapInv_mem_H hW hW0 hs.1 (hζH n)⟩
      simp only [hFs]
      exact hlimF
    have hlimζ : Tendsto ζ atTop (𝓝 (fwdMap W s v)) := by
      have h := (tendsto_fwdMap_of_isForwardSol hW hs.1 hsol).comp hin
      rw [fwdMap_eq_of_isForwardSol hW hsol ⟨hs.1, le_rfl⟩]
      refine h.congr fun n => ?_
      simp only [Function.comp_apply]
      exact fwdMap_fwdMapInv hW hW0 hs.1 (hζH n)
    have hlimw : Tendsto w atTop (𝓝 (u₀ : ℂ)) := tendsto_nhdsWithin_iff.1 (tendsto_vertical u₀) |>.1
    have hbound : ∀ n, ‖ζ n - w n‖ ≤ 24 * M + 8 * Real.sqrt (σ - s) := fun n =>
      norm_fwdMapInv_sub_le hWs hWs0 hσs hM (hwH n)
    exact le_of_tendsto' ((hlimζ.sub hlimw).norm) hbound
  -- conclude
  by_contra hne
  have hpos : 0 < ‖(u₀ : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_pos.2 hne
  set e := ‖(u₀ : ℂ)‖ / 96 with hedef
  have he : 0 < e := by positivity
  obtain ⟨δ, hδ, hWδ⟩ := Metric.continuousAt_iff.1 hW.continuousAt e he
  have hev : ∀ᶠ s in 𝓝[<] σ,
      ‖(u₀ : ℂ)‖ ≤ ‖fwdMap W s v‖ + (24 * (2 * e) + 8 * Real.sqrt (σ - s)) := by
    filter_upwards [Ioo_mem_nhdsLT (show max 0 (σ - δ) < σ from max_lt hσ (by linarith))]
      with s hs
    have hs0 : 0 ≤ s := (le_max_left _ _).trans hs.1.le
    have hsδ : σ - δ < s := (le_max_right _ _).trans_lt hs.1
    have hM : ∀ r ∈ Icc (0 : ℝ) (σ - s), |shiftDrive W s r| ≤ 2 * e := by
      intro r hr
      have h1 := hWδ (show dist (s + r) σ < δ by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2])
      have h2 := hWδ (show dist s σ < δ by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.2])
      rw [Real.dist_eq] at h1 h2
      simp only [shiftDrive]
      rw [abs_le]
      constructor <;> linarith [abs_lt.1 h1, abs_lt.1 h2]
    have hk := key s ⟨hs0, hs.2⟩ (2 * e) hM
    have htri : ‖(u₀ : ℂ)‖ ≤ ‖fwdMap W s v‖ + ‖fwdMap W s v - u₀‖ := by
      have := norm_sub_le (fwdMap W s v) (fwdMap W s v - u₀)
      rw [sub_sub_cancel] at this
      exact this
    linarith
  have hlim : Tendsto (fun s => ‖fwdMap W s v‖ + (24 * (2 * e) + 8 * Real.sqrt (σ - s)))
      (𝓝[<] σ) (𝓝 (0 + (24 * (2 * e) + 8 * Real.sqrt (σ - σ)))) := by
    refine Tendsto.add (by simpa using hX.norm) (Tendsto.const_add _ (Tendsto.const_mul _ ?_))
    exact ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).tendsto σ).mono_left
      nhdsWithin_le_nhds
  have := ge_of_tendsto hlim hev
  rw [sub_self, Real.sqrt_zero, mul_zero, add_zero, zero_add] at this
  linarith

/-! ### The tip at the swallowing time of a real point -/

/-- **[RS05]'s "`S ⊂ (−∞, W(τ(1)))`", one half.** If `x > 0` is swallowed at `τ`, then the
boundary extension `F̄_τ` never takes the value `0` (the starting point of the trace) at a real
point `u₀ ≥ 0`: points `w → u₀` would give `z = F_τ(w) → 0` with
`Re w/Im w ≤ (Re z − x)/Im z → −∞` (`cot_fwdMap_le_of_realSwallowAt`), but `Re w ≥ 0`. -/
theorem extendFrom_ne_zero_of_nonneg {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {x τ : ℝ} (hx : 0 < x) (hsw : RealSwallowAt W x τ) {u₀ : ℝ} (hu₀ : 0 ≤ u₀) :
    extendFrom H (fwdMapInv W τ) u₀ ≠ 0 := by
  intro h
  have hτ := hsw.1
  set w : ℕ → ℂ := fun n => (u₀ : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hwdef
  have hlim : Tendsto (fun n => fwdMapInv W τ (w n)) atTop (𝓝 0) := by
    have h' := ((hη.hasBdryLimits hW hW0 hτ.le).tendsto (ofReal_mem_Hbar u₀)).comp
      (tendsto_vertical u₀)
    rw [h] at h'
    exact h'
  have hre : ∀ᶠ n in atTop, (fwdMapInv W τ (w n)).re < x :=
    (Complex.continuous_re.tendsto 0).comp hlim |>.eventually (gt_mem_nhds (by simpa using hx))
  obtain ⟨n, hn⟩ := hre.exists
  have hz := fwdMapInv_mem_compl_fwdHull hW hW0 hτ.le (vertical_mem_H u₀ n)
  have hcot := cot_fwdMap_le_of_realSwallowAt hW hW0 hx hsw hz
  rw [fwdMap_fwdMapInv hW hW0 hτ.le (vertical_mem_H u₀ n)] at hcot
  have hl : 0 ≤ (w n).re / (w n).im := by
    apply div_nonneg
    · simp [hwdef, hu₀]
    · exact (vertical_mem_H u₀ n).le
  have hr : ((fwdMapInv W τ (w n)).re - x) / (fwdMapInv W τ (w n)).im < 0 :=
    div_neg_of_neg_of_pos (by linarith) hz.1
  linarith

/-- **[RS05]'s "`S ⊂ (−∞, W(τ))`", other half, at a left swallowing time.** If `a < 0` is swallowed
at `σ`, then the tip `F̄_σ(0)` is not a real point to the right of `a`. -/
theorem extendFrom_zero_ne_of_lt {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a σ : ℝ} (ha : a < 0) (hsw : RealSwallowAt W a σ) {v : ℝ} (hv : a < v) :
    extendFrom H (fwdMapInv W σ) 0 ≠ v := by
  intro h
  have hσ := hsw.1
  set w : ℕ → ℂ := fun n => ((0 : ℝ) : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hwdef
  have hlim : Tendsto (fun n => fwdMapInv W σ (w n)) atTop (𝓝 (v : ℂ)) := by
    have h' := ((hη.hasBdryLimits hW hW0 hσ.le).tendsto (ofReal_mem_Hbar 0)).comp
      (tendsto_vertical 0)
    rw [Complex.ofReal_zero, h] at h'
    exact h'
  have hre : ∀ᶠ n in atTop, a < (fwdMapInv W σ (w n)).re :=
    (Complex.continuous_re.tendsto _).comp hlim |>.eventually (lt_mem_nhds (by simpa using hv))
  obtain ⟨n, hn⟩ := hre.exists
  have hz := fwdMapInv_mem_compl_fwdHull hW hW0 hσ.le (vertical_mem_H 0 n)
  have hcot := le_cot_fwdMap_of_realSwallowAt hW hW0 ha hsw hz
  rw [fwdMap_fwdMapInv hW hW0 hσ.le (vertical_mem_H 0 n)] at hcot
  have hr : (w n).re / (w n).im = 0 := by simp [hwdef]
  have hl : 0 < ((fwdMapInv W σ (w n)).re - a) / (fwdMapInv W σ (w n)).im :=
    div_pos (by linarith) hz.1
  linarith

/-! ### Points near the origin after a right swallowing time -/

/-- Points of `ℍ \ K_τ` near the starting point `0` are not mapped near the tip: if `x > 0` is
swallowed at `τ`, then `‖f_τ(z)‖ ≥ δ` for `z ∈ ℍ \ K_τ` close to `0` (because `F̄_τ(0) ≠ 0`,
`extendFrom_ne_zero_of_nonneg`, and `F̄_τ` is continuous at `0`). -/
theorem exists_le_norm_fwdMap_of_realSwallowAt {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {x τ : ℝ} (hx : 0 < x) (hsw : RealSwallowAt W x τ) :
    ∃ ε > 0, ∃ δ > 0, ∀ z ∈ H \ fwdHull W τ, ‖z‖ < ε → δ ≤ ‖fwdMap W τ z‖ := by
  have hτ := hsw.1
  set p := extendFrom H (fwdMapInv W τ) 0 with hpdef
  have hp : p ≠ 0 := by
    have := extendFrom_ne_zero_of_nonneg hη hW hW0 hx hsw (le_refl 0)
    rwa [Complex.ofReal_zero] at this
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hlim : Tendsto (fwdMapInv W τ) (𝓝[H] 0) (𝓝 p) :=
    (hη.hasBdryLimits hW hW0 hτ.le).tendsto (by simpa using ofReal_mem_Hbar 0)
  obtain ⟨ρ, hρ, hρF⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlim (‖p‖ / 2) (half_pos hpn)
  refine ⟨‖p‖ / 2, half_pos hpn, ρ, hρ, fun z hz hzn => ?_⟩
  by_contra hlt
  push Not at hlt
  have hwH : fwdMap W τ z ∈ H := FwdHolo.mapsTo_fwdMap hW hτ.le hz
  have h1 := hρF hwH (by rwa [dist_zero_right])
  rw [fwdMapInv_fwdMap hW hW0 hτ.le hz, dist_eq_norm] at h1
  have := norm_sub_norm_le p z
  rw [norm_sub_rev] at h1
  linarith

/-- **Where the points near `0` go at a right swallowing time.** If `x > 0` is swallowed at `τ`,
then for `z ∈ ℍ \ K_τ` close to `0`, `f_τ(z)` has real part in `[−R, −δ]`: it is at distance
`≥ δ₀` from `0` (`exists_le_norm_fwdMap_of_realSwallowAt`), at bounded distance from `z`
(`norm_fwdMapInv_sub_le`), and its direction is almost `π` (`cot_fwdMap_le_of_realSwallowAt`). -/
theorem exists_re_fwdMap_mem_of_realSwallowAt {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {x τ : ℝ} (hx : 0 < x) (hsw : RealSwallowAt W x τ) :
    ∃ ε > 0, ∃ δ > 0, ∃ R > 0, ∀ z ∈ H \ fwdHull W τ, ‖z‖ < ε →
      -R ≤ (fwdMap W τ z).re ∧ (fwdMap W τ z).re ≤ -δ := by
  have hτ := hsw.1
  obtain ⟨ε₀, hε₀, δ₀, hδ₀, hlow⟩ := exists_le_norm_fwdMap_of_realSwallowAt hη hW hW0 hx hsw
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hτ.le
  set R := max C 0 + 1 with hRdef
  have hR : 0 < R := by positivity
  set ε := min (min ε₀ 1) (min (x / 2) (x * δ₀ / (4 * R))) with hεdef
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, δ₀ / 2, half_pos hδ₀, R, hR, fun z hz hzn => ?_⟩
  have hn1 : ‖z‖ < ε₀ := hzn.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hn2 : ‖z‖ < 1 := hzn.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hn3 : ‖z‖ < x / 2 := hzn.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hn4 : ‖z‖ < x * δ₀ / (4 * R) := hzn.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set w := fwdMap W τ z with hwdef
  have hwH : w ∈ H := FwdHolo.mapsTo_fwdMap hW hτ.le hz
  have hwlow : δ₀ ≤ ‖w‖ := hlow z hz hn1
  have hwup : ‖w‖ ≤ R := by
    have h1 := hC w hwH
    rw [fwdMapInv_fwdMap hW hW0 hτ.le hz] at h1
    have h2 := norm_sub_norm_le w z
    rw [norm_sub_rev] at h1
    linarith [le_max_left C 0]
  have hcot := cot_fwdMap_le_of_realSwallowAt hW hW0 hx hsw hz
  rw [← hwdef] at hcot
  have hb : 0 < w.im := hwH
  have hd : 0 < z.im := hz.1
  have hcz : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hdz : z.im ≤ ‖z‖ := Complex.im_le_norm z
  have hzpos : 0 < ‖z‖ := hd.trans_le hdz
  rw [div_le_div_iff₀ hb hd] at hcot
  -- w.re * z.im ≤ (z.re - x) * w.im
  have hneg : (z.re - x) * w.im ≤ -(x / 2) * w.im := by
    apply mul_le_mul_of_nonneg_right _ hb.le; linarith
  have hare : w.re < 0 := by
    by_contra h
    push Not at h
    have : 0 ≤ w.re * z.im := mul_nonneg h hd.le
    nlinarith
  have h1 : w.re * ‖z‖ ≤ -(x / 2) * w.im := by
    have : w.re * ‖z‖ ≤ w.re * z.im := mul_le_mul_of_nonpos_left hdz hare.le
    linarith
  have hreR : -R ≤ w.re := by
    have := Complex.abs_re_le_norm w
    rw [abs_of_neg hare] at this
    linarith
  have him : w.im ≤ δ₀ / 2 := by
    -- (x/2) * w.im ≤ -w.re * ‖z‖ ≤ R * ‖z‖ < x * δ₀ / 4
    have h2 : (x / 2) * w.im ≤ R * ‖z‖ := by nlinarith
    have h3 : R * ‖z‖ < x * δ₀ / 4 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * R)] at hn4
      nlinarith
    nlinarith
  refine ⟨hreR, ?_⟩
  have hsum : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
  rw [abs_of_neg hare, abs_of_pos hb] at hsum
  linarith

/-- **The cluster condition shortly after a right swallowing time.** If `x > 0` is swallowed at
`τ`, there are `r₀, ε, δ, R > 0` such that for every `t₁ ∈ [τ, τ + r₀]` and every `z ∈ ℍ \ K_{t₁}`
with `‖z‖ < ε`, `Re f_{t₁}(z) ∈ (−R, −δ)` (the forward maps move points by at most
`24 osc + 8√(t₁ − τ)` between `τ` and `t₁`, `norm_fwdMap_sub_self_le`). -/
theorem exists_clusterCond_of_realSwallowAt {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {x τ : ℝ} (hx : 0 < x) (hsw : RealSwallowAt W x τ) :
    ∃ r₀ > 0, ∃ ε > 0, ∃ δ > 0, ∃ R > 0, ∀ t₁ ∈ Icc τ (τ + r₀),
      ∀ z ∈ H \ fwdHull W t₁, ‖z‖ < ε →
        -R < (fwdMap W t₁ z).re ∧ (fwdMap W t₁ z).re < -δ := by
  have hτ := hsw.1
  obtain ⟨ε, hε, δ₀, hδ₀, R₀, hR₀, hbd⟩ := exists_re_fwdMap_mem_of_realSwallowAt hη hW hW0 hx hsw
  have hWs := continuous_shiftDrive hW τ
  have hWs0 := shiftDrive_zero W τ
  obtain ⟨r₁, hr₁, hr₁W⟩ := Metric.continuousAt_iff.1 hWs.continuousAt (δ₀ / 100) (by positivity)
  set r₀ := min (r₁ / 2) ((δ₀ / 32) ^ 2) with hr₀def
  have hr₀ : 0 < r₀ := by positivity
  refine ⟨r₀, hr₀, ε, hε, δ₀ / 2, half_pos hδ₀, R₀ + δ₀ / 2, by positivity,
    fun t₁ ht₁ z hz hzn => ?_⟩
  set r := t₁ - τ with hrdef
  have hr : 0 ≤ r := sub_nonneg.2 ht₁.1
  have hrr₀ : r ≤ r₀ := by linarith [ht₁.2]
  have ht₁eq : τ + r = t₁ := by ring
  rw [← ht₁eq] at hz ⊢
  have hzτ : z ∈ H \ fwdHull W τ :=
    ⟨hz.1, fun h => hz.2 ((fwdHull_mono (W := W)).1 (le_add_of_nonneg_right hr) h)⟩
  obtain ⟨hmem, hcomp⟩ := fwdMap_add_shift hW hW0 hτ.le hr hz
  have hM : ∀ q ∈ Icc (0 : ℝ) r, |shiftDrive W τ q| ≤ δ₀ / 100 := by
    intro q hq
    have h := hr₁W (show dist q 0 < r₁ by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hq.1]
      linarith [hq.2, min_le_left (r₁ / 2) ((δ₀ / 32) ^ 2)])
    rw [Real.dist_eq, hWs0, sub_zero] at h
    exact h.le
  have hdisp := norm_fwdMap_sub_self_le hWs hWs0 hr hM hmem ⟨hr, le_rfl⟩
  rw [hcomp] at hdisp
  have hsq : Real.sqrt r ≤ δ₀ / 32 := by
    rw [Real.sqrt_le_left (by positivity)]
    linarith [min_le_right (r₁ / 2) ((δ₀ / 32) ^ 2)]
  have hre := Complex.abs_re_le_norm (fwdMap W (τ + r) z - fwdMap W τ z)
  rw [Complex.sub_re] at hre
  obtain ⟨h1, h2⟩ := hbd z hzτ hzn
  constructor <;> linarith [abs_le.1 (hre.trans hdisp)]

/-! ### The half-ball criterion -/

/-- Negative form of `realSwallowAt_of_le_of_le`. -/
theorem realSwallowAt_of_le_of_le_neg (hW : Continuous W) (hW0 : W 0 = 0) {a v b σ : ℝ}
    (hb : b < 0) (hav : a ≤ v) (hvb : v ≤ b) (has : RealSwallowAt W a σ)
    (hbs : RealSwallowAt W b σ) : RealSwallowAt W v σ := by
  rw [← realSwallowAt_neg_iff] at has hbs ⊢
  exact realSwallowAt_of_le_of_le (W := fun t => -W t) (by fun_prop) (by simp [hW0])
    (by linarith) (by linarith) (by linarith) hbs has

/-- **The half-ball criterion** (the composition step of [RS05, Lemma 7.3]). Let `η` be a
continuous Loewner trace of `W` and `η'` one of the shifted driver `V = W(t₁ + ·) − W(t₁)`.
Suppose that every `z ∈ ℍ \ K_{t₁}` with `‖z‖ < ε` has `Re f_{t₁}(z) ∈ (−R, −δ)`, and that
`V` swallows `[a, b] ⊇ [−R, −δ]` (`b < 0`) at once at time `σ`. Then `K_{t₁ + σ}` contains a
half-neighbourhood of `0`.

Proof: otherwise there are `z_n → 0` in `ℍ \ K_{t₁+σ}`; with `w_n = f_{t₁+σ}(z_n)` (bounded) and
`ζ_n = F^V_σ(w_n)`, `F_{t₁}(ζ_n) = z_n`. Along a subsequence `w_n → w ∈ ℍ̄`,
`ζ_n → v = F̄^V_σ(w)` and `F̄_{t₁}(v) = 0`, so `v` is real, and the cluster condition gives
`v ∈ [−R, −δ] ⊆ [a, b]`. Then `w` is real and `v` is swallowed by `V` at `σ`, so `w = 0`
(`eq_zero_of_extendFrom_eq_of_realSwallowAt`) and the tip `F̄^V_σ(0) = v > a`, which
`extendFrom_zero_ne_of_lt` excludes. -/
theorem hullContainsHalfBall_of_clusterCond {η η' : ℝ → ℂ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : IsLoewnerTrace W η) {t₁ : ℝ} (ht₁ : 0 ≤ t₁) (hη' : IsLoewnerTrace (shiftDrive W t₁) η')
    {ε R δ : ℝ} (hε : 0 < ε)
    (hcl : ∀ z ∈ H \ fwdHull W t₁, ‖z‖ < ε →
      -R < (fwdMap W t₁ z).re ∧ (fwdMap W t₁ z).re < -δ)
    {a b σ : ℝ} (ha : a < -R) (hb : -δ ≤ b) (hb0 : b < 0)
    (hsa : RealSwallowAt (shiftDrive W t₁) a σ) (hsb : RealSwallowAt (shiftDrive W t₁) b σ) :
    HullContainsHalfBall W (t₁ + σ) := by
  set V := shiftDrive W t₁ with hVdef
  have hV : Continuous V := continuous_shiftDrive hW t₁
  have hV0 : V 0 = 0 := shiftDrive_zero W t₁
  have hσ := hsa.1
  have hT : 0 ≤ t₁ + σ := add_nonneg ht₁ hσ.le
  by_contra hnot
  have hseq : ∀ n : ℕ, ∃ z ∈ H, ‖z‖ < 1 / ((n : ℝ) + 1) ∧ z ∉ fwdHull W (t₁ + σ) := by
    intro n
    by_contra hcon
    push Not at hcon
    exact hnot ⟨1 / ((n : ℝ) + 1), by positivity, fun z hz hzn => hcon z hz hzn⟩
  choose z hzH hzn hzK using hseq
  have hz0 : Tendsto z atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hzn n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  set w : ℕ → ℂ := fun n => fwdMap W (t₁ + σ) (z n) with hwdef
  have hwH : ∀ n, w n ∈ H := fun n => FwdHolo.mapsTo_fwdMap hW hT ⟨hzH n, hzK n⟩
  have hFw : ∀ n, fwdMapInv W (t₁ + σ) (w n) = z n := fun n =>
    fwdMapInv_fwdMap hW hW0 hT ⟨hzH n, hzK n⟩
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hT
  have hwb : ∀ n, w n ∈ Metric.closedBall (0 : ℂ) (1 + max C 0) ∩ Hbar := by
    intro n
    refine ⟨?_, H_subset_Hbar (hwH n)⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hC (w n) (hwH n)
    rw [hFw n] at h1
    have h2 := norm_sub_norm_le (w n) (z n)
    rw [norm_sub_rev] at h1
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith [hzn n, le_max_left C 0]
  obtain ⟨w', hw'mem, φ, hφ, hlimw⟩ :=
    ((isCompact_closedBall (0 : ℂ) (1 + max C 0)).inter_right isClosed_Hbar).tendsto_subseq hwb
  set ζ : ℕ → ℂ := fun n => fwdMapInv V σ (w n) with hζdef
  have hζH : ∀ n, ζ n ∈ H := fun n => fwdMapInv_mem_H hV hV0 hσ.le (hwH n)
  have hFζ : ∀ n, fwdMapInv W t₁ (ζ n) = z n := fun n => by
    rw [← fwdMapInv_add_shift hW hW0 ht₁ hσ.le (hwH n), hFw n]
  set F' := extendFrom H (fwdMapInv V σ) with hF'def
  have hF'c : ContinuousOn F' Hbar := (hη'.hasBdryLimits hV hV0 hσ.le).continuousOn
  have hζeq : ∀ n, F' (w n) = ζ n := fun n =>
    extendFrom_H_eq (continuousOn_fwdMapInv hV hV0 hσ.le) (hwH n)
  have hlimζ : Tendsto (ζ ∘ φ) atTop (𝓝 (F' w')) := by
    have h := (hF'c w' hw'mem.2).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hlimw, Eventually.of_forall fun n => H_subset_Hbar (hwH (φ n))⟩)
    exact h.congr fun n => hζeq (φ n)
  set v := F' w' with hvdef
  have hvHbar : v ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hlimζ (Eventually.of_forall fun n => hζH (φ n))
  set F := extendFrom H (fwdMapInv W t₁) with hFdef
  have hFc : ContinuousOn F Hbar := (hη.hasBdryLimits hW hW0 ht₁).continuousOn
  have hFv : F v = 0 := by
    have h1 : Tendsto (fun n => F (ζ (φ n))) atTop (𝓝 (F v)) :=
      (hFc v hvHbar).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hlimζ, Eventually.of_forall fun n => H_subset_Hbar (hζH (φ n))⟩)
    have h2 : ∀ n, F (ζ (φ n)) = z (φ n) := fun n => by
      rw [hFdef, extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 ht₁) (hζH (φ n)), hFζ]
    exact tendsto_nhds_unique (h1.congr h2) (hz0.comp hφ.tendsto_atTop)
  have hvR : v.im = 0 := by
    by_contra hne
    have hvH : v ∈ H := lt_of_le_of_ne hvHbar (Ne.symm hne)
    have h := fwdMapInv_mem_H hW hW0 ht₁ hvH
    rw [← extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 ht₁) hvH, ← hFdef, hFv] at h
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h)
  have hvre : -R ≤ v.re ∧ v.re ≤ -δ := by
    have hsmall : ∀ᶠ n in atTop, ‖z (φ n)‖ < ε :=
      ((hz0.comp hφ.tendsto_atTop).norm).eventually (gt_mem_nhds (by simpa using hε))
    have hev : ∀ᶠ n in atTop, -R < (ζ (φ n)).re ∧ (ζ (φ n)).re < -δ := by
      filter_upwards [hsmall] with n hn
      have hmem : z (φ n) ∈ H \ fwdHull W t₁ := by
        rw [← hFζ]; exact fwdMapInv_mem_compl_fwdHull hW hW0 ht₁ (hζH (φ n))
      have h := hcl _ hmem hn
      rwa [← hFζ, fwdMap_fwdMapInv hW hW0 ht₁ (hζH (φ n))] at h
    have hre := (Complex.continuous_re.tendsto v).comp hlimζ
    exact ⟨ge_of_tendsto hre (hev.mono fun n h => h.1.le),
      le_of_tendsto hre (hev.mono fun n h => h.2.le)⟩
  have hw'R : w'.im = 0 := by
    by_contra hne
    have hw'H : w' ∈ H := lt_of_le_of_ne hw'mem.2 (Ne.symm hne)
    have hvH : v ∈ H := by
      rw [hvdef, hF'def, extendFrom_H_eq (continuousOn_fwdMapInv hV hV0 hσ.le) hw'H]
      exact fwdMapInv_mem_H hV hV0 hσ.le hw'H
    have : (0 : ℝ) < v.im := hvH
    linarith
  have hw'eq : w' = (w'.re : ℂ) := Complex.ext (by simp) (by simp [hw'R])
  have hveq : v = (v.re : ℂ) := Complex.ext (by simp) (by simp [hvR])
  have hvs : RealSwallowAt V v.re σ :=
    realSwallowAt_of_le_of_le_neg hV hV0 hb0 (by linarith) (by linarith) hsa hsb
  have hF'w : extendFrom H (fwdMapInv V σ) (w'.re : ℂ) = (v.re : ℂ) := by
    rw [← hw'eq, ← hF'def, ← hvdef, ← hveq]
  have hu := eq_zero_of_extendFrom_eq_of_realSwallowAt hη' hV hV0 (by linarith) hvs hF'w
  rw [hu, Complex.ofReal_zero] at hF'w
  exact extendFrom_zero_ne_of_lt hη' hV hV0 (by linarith) hsa (by linarith) hF'w

end InteractingSLE
