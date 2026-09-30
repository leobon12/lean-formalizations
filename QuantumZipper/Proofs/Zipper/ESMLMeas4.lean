import QuantumZipper.Proofs.Zipper.ESMLMeas3
import QuantumZipper.Proofs.Zipper.F1Side3
import QuantumZipper.Proofs.RS.HullBasics
import QuantumZipper.Proofs.RS.RealAlive
import QuantumZipper.Proofs.Loewner.ForwardFlow
import QuantumZipper.Proofs.Zipper.E1TransferM4Ae
import QuantumZipper.Proofs.Zipper.B5VHccMeas

/-!
# ESM-LMEAS-4: a measurable reader for the side images of a continuous driver path

Fourth part of the ESM-LMEAS task (node **E-SM**, obligation `hLad` of
`ESM.lintegral_levelTime_strongMarkov_lenA`, decision D21). `ESMLMeas3.lenMinusSur` needs the two
side images `O^±_s` of the stopped driver as a *measurable* function of the driver path: the
input `hside` of `ESM.ae_lenMinus_eq_surrogate`.

* `sidePtL`, `sidePtR`: the complex approximants `∓1/(n+1) + i/(m+1)` of the origin from inside
  `ℍ`. `fwdMap W s` is measurable in the *path* at points of `ℍ` (`measurable_fwdMap_Wof`, by
  `isOpen_goodPaths_continuousOn_fwdMap`, as in `ForwardFlow.measurable_fwdMap_drive`), while
  measurability at *real* points is false in general (existence of the forward solution is not
  open there) — this is why the reader is built from the complex approximants.
* `sideReader`: the reader, `(liminf_n liminf_m (fwdMap W_s (sidePtL n m)).re,
  limsup_n limsup_m (fwdMap W_s (sidePtR n m)).re)` for the path driver `W_s = Wof κ s hs f`;
  measurable by `Measurable.liminf`/`Measurable.limsup`.
* `sideImages_Wof_eq_sideReader`: deterministic form. If every real `x ≠ 0` is alive at time `s`
  under `W_s`, the side images of `W_s` are the reader's values: the inner limits are
  `RS.fwdFlow_near_alive_real` (D5: the complex approximants converge to the real forward map),
  the outer ones the monotone limits of `x ↦ (fwdMap W_s s x).re` on `(-∞,0)` and `(0,∞)`
  (`F1.tendsto_nhdsLT_of_monotoneOn`, `F1.tendsto_nhdsGT_of_monotoneOn`).
* `ae_sideImages_eq_sideReader`: the unconditional almost-sure form for `W = drive κ (clampB s B)`
  with `κ ≤ 4`, from `RS.ae_real_alive` and `ESM.sideImages_congr_drive` (the stopped driver
  agrees with the path driver on `[0,s]`).

Sources: Sheffield, arXiv:1012.4797, §5.2 (unzipping at a stopping time); Rohde–Schramm,
*Basic properties of SLE*, Lemma 6.2 (`RS.ae_real_alive`); Kemppainen, *Schramm–Loewner
Evolution*, Prop. 5.1–5.2. The reader construction and its measurability are own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace ESM

open F1 CoordsFull CharFun

/-! ## The complex approximants of the origin -/

/-- The approximant `-1/(n+1) + i/(m+1)` of the origin from below-left, in `ℍ`. -/
def sidePtL (n m : ℕ) : ℂ :=
  ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ) + ((1 / ((m : ℝ) + 1)) : ℝ) * Complex.I

/-- The approximant `1/(n+1) + i/(m+1)` of the origin from below-right, in `ℍ`. -/
def sidePtR (n m : ℕ) : ℂ :=
  ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) + ((1 / ((m : ℝ) + 1)) : ℝ) * Complex.I

theorem sidePtL_im (n m : ℕ) : (sidePtL n m).im = 1 / ((m : ℝ) + 1) := by
  rw [sidePtL, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem sidePtR_im (n m : ℕ) : (sidePtR n m).im = 1 / ((m : ℝ) + 1) := by
  rw [sidePtR, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem sidePtL_im_pos (n m : ℕ) : 0 < (sidePtL n m).im := by
  rw [sidePtL_im]; positivity

theorem sidePtR_im_pos (n m : ℕ) : 0 < (sidePtR n m).im := by
  rw [sidePtR_im]; positivity

theorem sidePtL_mem_H (n m : ℕ) : sidePtL n m ∈ H := sidePtL_im_pos n m

theorem sidePtR_mem_H (n m : ℕ) : sidePtR n m ∈ H := sidePtR_im_pos n m

/-! ## Measurability of `fwdMap` of a path driver at points of `ℍ` -/

/-- **`fwdMap` of the path driver is measurable in the path at points of `ℍ`.** Same proof as
`ForwardFlow.measurable_fwdMap_drive` with the Borel space `C(Icc 0 s, ℝ)` in place of `Ω`: on
the open set of paths for which `z` is not swallowed, `g ↦ fwdMap (extIccPath hs g) s z` is
continuous, and it agrees with `fwdMap (Wof κ s hs g) s z` (`fwdMap_congr_drive`). -/
theorem measurable_fwdMap_Wof (κ s : ℝ) (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) :
    Measurable fun f : C(Icc (0 : ℝ) s, ℝ) => fwdMap (Wof κ s hs f) s z := by
  let Φ : C(Icc (0 : ℝ) s, ℝ) → C(Icc (0 : ℝ) s, ℝ) := fun f =>
    ⟨fun u => Real.sqrt κ * f u, by fun_prop⟩
  have hΦ : Measurable Φ :=
    ContinuousMap.measurable_iff_eval.2 fun u =>
      measurable_const.mul (continuous_eval_const u).measurable
  have hfun : (fun f : C(Icc (0 : ℝ) s, ℝ) => fwdMap (Wof κ s hs f) s z) =
      (fun g => fwdMap (extIccPath hs g) s z) ∘ Φ := by
    funext f
    refine fwdMap_congr_drive (continuous_Wof κ s hs f) (continuous_extIccPath hs (Φ f)) hz hs
      (fun r hr => ?_)
    rw [extIccPath_of_mem hs (Φ f) hr]
    change Real.sqrt κ * f (projIcc 0 s hs r) = Φ f ⟨r, hr⟩
    rw [projIcc_of_mem hs hr]
    rfl
  rw [hfun]
  obtain ⟨hGo, hFc⟩ := isOpen_goodPaths_continuousOn_fwdMap hz hs
  classical
  have hpw : (fun g => fwdMap (extIccPath hs g) s z) =
      {g | ∃ u, IsForwardSol (extIccPath hs g) z s u}.piecewise
        (fun g => fwdMap (extIccPath hs g) s z) (fun _ => 0) := by
    funext g
    by_cases hg : g ∈ {g | ∃ u, IsForwardSol (extIccPath hs g) z s u}
    · simp only [Set.piecewise, hg, ite_true]
    · simp only [Set.piecewise, hg, ite_false]
      exact dif_neg hg
  rw [hpw]
  exact (hFc.measurable_piecewise continuousOn_const hGo.measurableSet).comp hΦ

/-! ## The reader -/

/-- **The measurable side-image reader of a continuous driver path.** The left (first) component
is the iterated `liminf` of the real parts of `fwdMap` at the approximants `sidePtL n m`, the
right (second) component the iterated `limsup` at the `sidePtR n m`. On the a.s. event where
every real `x ≠ 0` is alive it computes `sideImages (Wof κ s hs f) s`. -/
def sideReader (κ s : ℝ) (hs : 0 ≤ s) (f : C(Icc (0 : ℝ) s, ℝ)) : ℝ × ℝ :=
  (liminf (fun n : ℕ => liminf (fun m : ℕ =>
      (fwdMap (Wof κ s hs f) s (sidePtL n m)).re) atTop) atTop,
   limsup (fun n : ℕ => limsup (fun m : ℕ =>
      (fwdMap (Wof κ s hs f) s (sidePtR n m)).re) atTop) atTop)

/-- **Measurability of the reader.** -/
theorem measurable_sideReader (κ s : ℝ) (hs : 0 ≤ s) : Measurable (sideReader κ s hs) := by
  refine Measurable.prodMk ?_ ?_
  · refine Measurable.liminf (f := fun n : ℕ => fun f =>
        liminf (fun m : ℕ => (fwdMap (Wof κ s hs f) s (sidePtL n m)).re) atTop) fun n => ?_
    refine Measurable.liminf (f := fun m : ℕ => fun f =>
      (fwdMap (Wof κ s hs f) s (sidePtL n m)).re) fun m => ?_
    exact Complex.measurable_re.comp (measurable_fwdMap_Wof κ s hs (sidePtL_im_pos n m))
  · refine Measurable.limsup (f := fun n : ℕ => fun f =>
        limsup (fun m : ℕ => (fwdMap (Wof κ s hs f) s (sidePtR n m)).re) atTop) fun n => ?_
    refine Measurable.limsup (f := fun m : ℕ => fun f =>
      (fwdMap (Wof κ s hs f) s (sidePtR n m)).re) fun m => ?_
    exact Complex.measurable_re.comp (measurable_fwdMap_Wof κ s hs (sidePtR_im_pos n m))

/-! ## The deterministic identity -/

/-- Convergence of the left approximants `m ↦ sidePtL n m` to the real point `-1/(n+1)` inside
`ℍ`. -/
theorem tendsto_sidePtL (n : ℕ) :
    Tendsto (fun m : ℕ => sidePtL n m) atTop (𝓝[H] ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun m => sidePtL_mem_H n m⟩
  have h1 : Tendsto (fun m : ℕ => ((1 / ((m : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h3 : Tendsto (fun m : ℕ => ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ) +
      ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝 ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) := by
    simpa using tendsto_const_nhds.add (h1.mul_const Complex.I)
  exact h3

/-- Convergence of the right approximants `m ↦ sidePtR n m` to the real point `1/(n+1)` inside
`ℍ`. -/
theorem tendsto_sidePtR (n : ℕ) :
    Tendsto (fun m : ℕ => sidePtR n m) atTop (𝓝[H] (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun m => sidePtR_mem_H n m⟩
  have h1 : Tendsto (fun m : ℕ => ((1 / ((m : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h3 : Tendsto (fun m : ℕ => (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ) +
      (((1 / ((m : ℝ) + 1)) : ℝ) : ℂ) * Complex.I) atTop
      (𝓝 (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) := by
    simpa using tendsto_const_nhds.add (h1.mul_const Complex.I)
  exact h3

theorem neg_one_div_ne_zero (n : ℕ) : -(1 / ((n : ℝ) + 1)) ≠ 0 :=
  neg_ne_zero.2 (ne_of_gt (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))

/-- **The deterministic identity.** If every real `x ≠ 0` is alive at time `s` under the path
driver, the side images of the driver are the reader's values. -/
theorem sideImages_Wof_eq_sideReader (κ s : ℝ) (hs : 0 ≤ s) (f : C(Icc (0 : ℝ) s, ℝ))
    (halive : ∀ x : ℝ, x ≠ 0 → ∃ u, IsForwardSol (Wof κ s hs f) (x : ℂ) s u) :
    sideImages (Wof κ s hs f) s = sideReader κ s hs f := by
  set W := Wof κ s hs f with hW
  have hWc : Continuous W := continuous_Wof κ s hs f
  set g : ℝ → ℝ := fun x => (fwdMap W s x).re with hg
  -- the value of `g` at alive real points is the value of a solution
  have hval : ∀ x : ℝ, x ≠ 0 → ∃ v : ℝ → ℂ, IsForwardSol W (x : ℂ) s v ∧ g x = (v s).re := by
    intro x hx
    obtain ⟨v, hv⟩ := halive x hx
    refine ⟨v, hv, ?_⟩
    rw [hg]
    exact congrArg Complex.re (fwdMap_eq_of_isForwardSol hv ⟨hs, le_rfl⟩)
  have hmono : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → x < y → g x < g y := by
    intro x y hx hy hxy
    obtain ⟨v₁, hv₁, hg₁⟩ := hval x hx
    obtain ⟨v₂, hv₂, hg₂⟩ := hval y hy
    rw [hg₁, hg₂]
    exact isForwardSol_lt_of_lt hs hxy hv₁ hv₂ s ⟨hs, le_rfl⟩
  have hbdAbove : BddAbove (g '' Iio (0 : ℝ)) := by
    refine ⟨g 1, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact (hmono y 1 (ne_of_lt (mem_Iio.1 hy)) one_ne_zero
      ((mem_Iio.1 hy).trans zero_lt_one)).le
  have hbdBelow : BddBelow (g '' Ioi (0 : ℝ)) := by
    refine ⟨g (-1), ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact (hmono (-1) y (by norm_num) (ne_of_gt (mem_Ioi.1 hy))
      ((by norm_num : (-1 : ℝ) < 0).trans (mem_Ioi.1 hy))).le
  have hzero : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- the reader's left component
  have hleft : liminf (fun n : ℕ => liminf (fun m : ℕ =>
      (fwdMap W s (sidePtL n m)).re) atTop) atTop = sSup (g '' Iio (0 : ℝ)) := by
    have hinner : ∀ n : ℕ, liminf (fun m : ℕ => (fwdMap W s (sidePtL n m)).re) atTop =
        g (-(1 / ((n : ℝ) + 1))) := by
      intro n
      have hx : -(1 / ((n : ℝ) + 1)) ≠ 0 := neg_one_div_ne_zero n
      obtain ⟨v, hv, hgv⟩ := hval _ hx
      have hnear := RS.fwdFlow_near_alive_real hWc hs hv
      have hcomp := (Complex.continuous_re.tendsto (v s)).comp
        (hnear.2.1.comp (tendsto_sidePtL n))
      exact hcomp.liminf_eq.trans hgv.symm
    rw [liminf_congr (Eventually.of_forall hinner)]
    have htend : Tendsto (fun n : ℕ => g (-(1 / ((n : ℝ) + 1)))) atTop
        (𝓝 (sSup (g '' Iio (0 : ℝ)))) := by
      refine tendsto_order.2 ⟨?_, ?_⟩
      · intro b hb
        have hne : (g '' Iio (0 : ℝ)).Nonempty := ⟨g (-1 / 2), -1 / 2, by norm_num, rfl⟩
        obtain ⟨z, ⟨y, hy, hzy⟩, hbz⟩ := exists_lt_of_lt_csSup hne hb
        have hy0 : y < 0 := mem_Iio.1 hy
        filter_upwards [(tendsto_order.1 hzero).2 (-y) (neg_pos.2 hy0)] with n hn
        have hyn : y < -(1 / ((n : ℝ) + 1)) := by linarith
        exact hbz.trans (hzy ▸ (hmono y _ (ne_of_lt hy0) (neg_one_div_ne_zero _) hyn))
      · intro b hb
        filter_upwards with n
        exact (le_csSup hbdAbove ⟨-(1 / ((n : ℝ) + 1)),
          by rw [mem_Iio]; exact neg_lt_zero.2 (by positivity), rfl⟩).trans_lt hb
    exact htend.liminf_eq
  -- the reader's right component
  have hright : limsup (fun n : ℕ => limsup (fun m : ℕ =>
      (fwdMap W s (sidePtR n m)).re) atTop) atTop = sInf (g '' Ioi (0 : ℝ)) := by
    have hinner : ∀ n : ℕ, limsup (fun m : ℕ => (fwdMap W s (sidePtR n m)).re) atTop =
        g (1 / ((n : ℝ) + 1)) := by
      intro n
      have hx : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
      obtain ⟨v, hv, hgv⟩ := hval _ hx
      have hnear := RS.fwdFlow_near_alive_real hWc hs hv
      have hcomp := (Complex.continuous_re.tendsto (v s)).comp
        (hnear.2.1.comp (tendsto_sidePtR n))
      exact hcomp.limsup_eq.trans hgv.symm
    rw [limsup_congr (Eventually.of_forall hinner)]
    have htend : Tendsto (fun n : ℕ => g (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (sInf (g '' Ioi (0 : ℝ)))) := by
      refine tendsto_order.2 ⟨?_, ?_⟩
      · intro b hb
        filter_upwards with n
        exact hb.trans_le (csInf_le hbdBelow ⟨1 / ((n : ℝ) + 1),
          by rw [mem_Ioi]; positivity, rfl⟩)
      · intro b hb
        have hne : (g '' Ioi (0 : ℝ)).Nonempty := ⟨g 1, 1, by norm_num, rfl⟩
        obtain ⟨z, ⟨y, hy, hzy⟩, hzb⟩ := exists_lt_of_csInf_lt hne hb
        have hy0 : 0 < y := mem_Ioi.1 hy
        filter_upwards [(tendsto_order.1 hzero).2 y hy0] with n hn
        exact (hzy ▸ (hmono _ y (by positivity) (ne_of_gt hy0) hn)).trans hzb
    exact htend.limsup_eq
  -- assemble
  have hlimL : limUnder (𝓝[<] (0 : ℝ)) g = sSup (g '' Iio (0 : ℝ)) :=
    (tendsto_nhdsLT_of_monotoneOn (f := g)
      (fun x hx y hy hxy => by
        rcases lt_or_eq_of_le hxy with hlt | heq
        · exact (hmono x y (ne_of_lt (mem_Iio.1 hx)) (ne_of_lt (mem_Iio.1 hy)) hlt).le
        · rw [heq])
      (fun x hx => (hmono x 1 (ne_of_lt (mem_Iio.1 hx)) one_ne_zero
        ((mem_Iio.1 hx).trans zero_lt_one)).le)).limUnder_eq
  have hlimR : limUnder (𝓝[>] (0 : ℝ)) g = sInf (g '' Ioi (0 : ℝ)) :=
    (tendsto_nhdsGT_of_monotoneOn (f := g)
      (fun x hx y hy hxy => by
        rcases lt_or_eq_of_le hxy with hlt | heq
        · exact (hmono x y (ne_of_gt (mem_Ioi.1 hx)) (ne_of_gt (mem_Ioi.1 hy)) hlt).le
        · rw [heq])
      (fun x hx => (hmono (-1) x (by norm_num) (ne_of_gt (mem_Ioi.1 hx))
        ((by norm_num : (-1 : ℝ) < 0).trans (mem_Ioi.1 hx))).le)).limUnder_eq
  have hside : sideImages W s = (limUnder (𝓝[<] (0 : ℝ)) g, limUnder (𝓝[>] (0 : ℝ)) g) := by
    simp only [sideImages, hg]
  rw [hside, hlimL, hlimR]
  exact Prod.ext hleft.symm hright.symm

/-! ## The almost-sure form for the stopped Brownian driver -/

/-- The path `pathC s B ω` at the projection of `r ∈ [0,s]` is `B (min r s)`. -/
theorem pathC_projIcc_eq {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 => B u ω) (s : ℝ≥0) (hs0 : (0 : ℝ) ≤ (s : ℝ)) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) (s : ℝ)) (ω : Ω) :
    pathC (s : ℝ) B hBc ω (projIcc 0 (s : ℝ) hs0 r) = B (min r.toNNReal s) ω := by
  have hle : r.toNNReal ≤ s := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
    exact hr.2
  have h1 : (projIcc 0 (s : ℝ) hs0 r : ℝ) = r := by
    rw [projIcc_of_mem hs0 hr]
  have h2 : (projIcc 0 (s : ℝ) hs0 r).1.toNNReal = min r.toNNReal s := by
    rw [congrArg Real.toNNReal h1, min_eq_left hle]
  show B ((projIcc 0 (s : ℝ) hs0 r).1.toNNReal) ω = B (min r.toNNReal s) ω
  exact congrArg (fun u => B u ω) h2

/-- The path driver `Wof κ s hs (pathC s B ω)` agrees with the stopped Brownian driver on
`[0,s]`. -/
theorem wof_pathC_eq_clampB {Ω : Type*} (κ : ℝ) (s : ℝ≥0) (hs0 : (0 : ℝ) ≤ (s : ℝ))
    (B : ℝ≥0 → Ω → ℝ) (hBc : ∀ ω, Continuous fun u : ℝ≥0 => B u ω) (ω : Ω) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) (s : ℝ)) :
    Wof κ (s : ℝ) hs0 (pathC (s : ℝ) B hBc ω) r = drive κ (clampB s B) ω r := by
  change Real.sqrt κ * pathC (s : ℝ) B hBc ω (projIcc 0 (s : ℝ) hs0 r)
    = Real.sqrt κ * B (min r.toNNReal s) ω
  rw [pathC_projIcc_eq B hBc s hs0 hr ω]

/-- **The almost-sure identity for the stopped Brownian driver**: the side images of
`drive κ (clampB s B) ω` are the reader's values at the path `pathC s B ω`. From the a.s.
aliveness of all real points (`RS.ae_real_alive`), the agreement of the stopped driver with the
path driver on `[0,s]` (`ESM.sideImages_congr_drive`, `isForwardSol_congr_drive`) and the
deterministic identity `sideImages_Wof_eq_sideReader`. -/
theorem ae_sideImages_eq_sideReader {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 => B u ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (s : ℝ≥0) :
    ∀ᵐ ω ∂P, sideImages (drive κ (clampB s B) ω) (s : ℝ) =
      sideReader κ (s : ℝ) s.2 (pathC (s : ℝ) B hBc ω) := by
  filter_upwards [hB.eval_zero_ae_eq_zero, RS.ae_real_alive hB hκ hκ4] with ω h0 halive
  have hagree : ∀ r ∈ Set.Icc (0 : ℝ) (s : ℝ),
      Wof κ (s : ℝ) s.2 (pathC (s : ℝ) B hBc ω) r = drive κ (clampB s B) ω r :=
    fun r hr => wof_pathC_eq_clampB κ s s.2 B hBc ω hr
  have halive' : ∀ x : ℝ, x ≠ 0 →
      ∃ u, IsForwardSol (Wof κ (s : ℝ) s.2 (pathC (s : ℝ) B hBc ω)) (x : ℂ) (s : ℝ) u := by
    intro x hx
    obtain ⟨u, hu⟩ := halive x hx (s : ℝ) s.2
    have hu' : IsForwardSol (drive κ (clampB s B) ω) (x : ℂ) (s : ℝ) u :=
      isForwardSol_congr_drive (fun r hr => (drive_clampB_eqOn (κ := κ) s ω r hr).symm) hu
    exact ⟨u, isForwardSol_congr_drive (fun r hr => (hagree r hr).symm) hu'⟩
  exact (sideImages_congr_drive s.2 hagree).symm.trans
    (sideImages_Wof_eq_sideReader κ (s : ℝ) s.2 (pathC (s : ℝ) B hBc ω) halive')

/-! ## Input 2: the boundary certificate of the surrogate field

`hgood` of `ESM.ae_lenMinus_eq_surrogate`: a.s. the coordinate reconstruction `unzipFieldCoord`
of the path surrogate carries the certificate `E1.M4.BCert`. For `s > 0` this is
`E1.ae_bCert_h0f` at `T = s` (a.s. `BCert` of `addConst (h0f κ s B X) c`), stripped of the
additive constant (`B5.bCert_addConst` with the a.s. `RawConverges` of `E1.ae_rawConverges_h0f`),
transported to the stopped driver (`B5.bCert_congr_full` along `coordChange_congr_of_eqOn`) and
to the coordinate reconstruction (`coordsFull_unzipFieldCoord` and
`ae_coordsFull_unzipFieldPath`). -/

/-- **Input 2 (`hgood`), `s > 0`.** -/
theorem ae_bCert_unzipFieldCoord {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hReg : Blueprint.RevCouplingBoundaryMeasureRegular) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 => B u ω) {s : ℝ≥0} (hs : 0 < (s : ℝ)) :
    ∀ᵐ ω ∂P, E1.M4.BCert (Real.sqrt κ) (unzipFieldCoord κ (s : ℝ) s.2
      (X ω, pathC (s : ℝ) B hBc ω)) := by
  have hbc_ev : ∀ᵐ ω ∂P, E1.M4.BCert (Real.sqrt κ)
      (addConst (B2.h0f κ (s : ℝ) B X ω) (-(E1.mReg κ (s : ℝ) B X 0 ω))) :=
    E1.ae_bCert_h0f (Ω := Ω) (P := P) (κ := κ) (T := (s : ℝ)) hReg hκ hκ4 hs hB hX hind
      (0 : Measure ℂ)
  have hraw_ev : ∀ᵐ ω ∂P, LocalRule.RawConverges (B2.h0f κ (s : ℝ) B X ω) Hbar :=
    E1.ae_rawConverges_h0f (Ω := Ω) (P := P) (κ := κ) (T := (s : ℝ)) hB hX hind hs.le
  have hcoord_ev : ∀ᵐ ω ∂P, coordsFull (coordChange (ofFun (h0rev κ) + X ω)
      (fwdMapInv (drive κ (clampB ((s : ℝ).toNNReal) B) ω) (s : ℝ)) (Qc (Real.sqrt κ))) =
      coordsFull (unzipFieldPath κ (s : ℝ) s.2 (X ω, pathC (s : ℝ) B hBc ω)) :=
    ae_coordsFull_unzipFieldPath (Ω := Ω) (P := P) (B := B) (X := X) (κ := κ) (s := (s : ℝ))
      hB hBc s.2
  filter_upwards [hbc_ev, hraw_ev, hcoord_ev, hB.eval_zero_ae_eq_zero] with ω hbc hraw hcoord h0
  -- the normalizing constant at `ϖ = 0` vanishes, so `hbc` is a certificate for `h0f` itself
  have h1 : E1.M4.BCert (Real.sqrt κ) (B2.h0f κ (s : ℝ) B X ω) := by
    have hm : E1.mReg κ (s : ℝ) B X 0 ω = 0 := by
      show evalReg (B2.h0f κ (s : ℝ) B X ω) 0 = 0
      rw [evalReg]
      simp only [integral_zero_measure]
      exact tendsto_const_nhds.limUnder_eq
    have hzero : addConst (B2.h0f κ (s : ℝ) B X ω) (0 : ℝ) = B2.h0f κ (s : ℝ) B X ω := by
      funext μ
      simp [addConst]
    have h := hbc
    rw [hm, neg_zero] at h
    rwa [hzero] at h
  -- the stopped driver agrees with the unstopped one on `[0,s]`
  have hsN : ((s : ℝ).toNNReal) = s := Subtype.coe_injective (Real.coe_toNNReal _ s.2)
  have hcoord' : coordsFull (coordChange (ofFun (h0rev κ) + X ω)
      (fwdMapInv (drive κ (clampB s B) ω) (s : ℝ)) (Qc (Real.sqrt κ))) =
      coordsFull (unzipFieldPath κ (s : ℝ) s.2 (X ω, pathC (s : ℝ) B hBc ω)) := by
    simpa only [hsN] using hcoord
  have hc : Continuous (drive κ B ω) := drive_continuous (hBc ω)
  have h0' : drive κ (clampB s B) ω 0 = 0 := by
    have hcl : (clampB s B) 0 = B 0 := by
      funext ω'
      rw [clampB_apply, min_eq_left (show (0 : ℝ≥0) ≤ s from s.2)]
    have hdr : drive κ (clampB s B) ω 0 = drive κ B ω 0 := by
      simp only [drive, Real.toNNReal_zero, hcl]
    rw [hdr]
    exact drive_zero h0
  have hEqOn : EqOn (fwdMapInv (drive κ B ω) (s : ℝ))
      (fwdMapInv (drive κ (clampB s B) ω) (s : ℝ)) H :=
    fwdMapInv_eqOn_of_drive_eqOn hc (drive_continuous (continuous_clampB hBc s ω))
      (drive_zero h0) h0' s.2 (fun r hr => (drive_clampB_eqOn (κ := κ) s ω r hr).symm)
  have hcf : coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) (s : ℝ))
      (Qc (Real.sqrt κ)) = B2.h0f κ (s : ℝ) B X ω := by
    rw [B2.h0f_eq_unzippedField]
    rfl
  have h2 : E1.M4.BCert (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + X ω)
      (fwdMapInv (drive κ (clampB s B) ω) (s : ℝ)) (Qc (Real.sqrt κ))) := by
    refine B5.bCert_congr_full (x := B2.h0f κ (s : ℝ) B X ω) ?_ h1
    rw [← hcf]
    funext i
    exact UnzipInvariance.coordChange_congr_of_eqOn hEqOn
      (foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i))
      (ofFun (h0rev κ) + X ω) (Qc (Real.sqrt κ))
  refine B5.bCert_congr_full (γ := Real.sqrt κ) ?_ h2
  rw [coordsFull_unzipFieldCoord (κ := κ) (s := (s : ℝ)) (hs := s.2)]
  exact hcoord'

end ESM
end QuantumZipper
