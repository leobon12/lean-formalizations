import InteractingSLE.Foundations.Harmonic.StepData

/-!
# Bounded harmonic extension of piecewise-constant boundary data in the strip

Packet GEO-STEP (`planning/INFRA-GEO.md` §4; design handoff `planning/handoffs/INFRA-GEO-ARCH.md` §D.5).

The strip `𝒮 = {0 < Im z < 1}` (Specification Aux. lemma 1, p. 13) with step data on its two
boundary lines (Specification p. 2, "in the strip"). The extension is transported from `ℍ` by the
conformal bijection `z ↦ exp(πz)`: the lower line goes to `(0, ∞)`, the upper line to `(−∞, 0)`
with reversed orientation, the strip ends `Re z → −∞`, `Re z → +∞` to `0` and `∞`.

Convention (design question Q7): `StepData.bdry` is right-continuous in the real-part variable
of each boundary line. On the upper line this is not the right-continuous convention in the
transported `ℍ` variable; the two differ only at the finitely many breakpoints, which every
statement here excludes.

## Main statements
* `InteractingSLE.StripStepData.harmonicOnNhd_harmonicExt`;
* `InteractingSLE.StripStepData.tendsto_harmonicExt_lower`, `…_upper`;
* `InteractingSLE.StripStepData.eqOn_harmonicExt` (uniqueness among bounded harmonic functions,
  by Lindelöf's maximum principle with the barrier `cosh(πx/2) cos(π(y − 1/2)/2)`).
-/

set_option autoImplicit false

noncomputable section

open Complex Metric Filter Topology Finset
open Set (EqOn)
open scoped Real
open QuantumZipper (H Hbar)

namespace InteractingSLE

/-- The horizontal strip `𝒮 = {0 < Im z < 1}` (Specification Aux. lemma 1, p. 13). -/
def strip : Set ℂ := {z | 0 < z.im ∧ z.im < 1}

theorem isOpen_strip : IsOpen strip :=
  (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)

/-- The frontier of the strip lies on its two boundary lines. -/
theorem im_eq_zero_or_eq_one_of_mem_frontier_strip {z : ℂ} (hz : z ∈ frontier strip) :
    z.im = 0 ∨ z.im = 1 := by
  rw [isOpen_strip.frontier_eq] at hz
  obtain ⟨hcl, hns⟩ := hz
  have hsub : closure strip ⊆ {w : ℂ | 0 ≤ w.im ∧ w.im ≤ 1} :=
    closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩)
      ((isClosed_le continuous_const continuous_im).inter
        (isClosed_le continuous_im continuous_const))
  obtain ⟨h0, h1⟩ := hsub hcl
  rcases h0.lt_or_eq with h0 | h0
  · rcases h1.lt_or_eq with h1 | h1
    · exact absurd ⟨h0, h1⟩ hns
    · exact Or.inr h1
  · exact Or.inl h0.symm

/-! ### Maximum principle on the strip -/

/-- The barrier on the strip: `Re (exp w + exp (−w))` with `w = (π/2)(z − i/2)`. -/
private def stripBarrier (z : ℂ) : ℝ :=
  (exp (((π / 2 : ℝ) : ℂ) * (z - I / 2))).re + (exp (-(((π / 2 : ℝ) : ℂ) * (z - I / 2)))).re

private theorem stripBarrier_eq (z : ℂ) :
    stripBarrier z = (Real.exp (π / 2 * z.re) + Real.exp (-(π / 2 * z.re))) *
      Real.cos (π / 2 * (z.im - 1 / 2)) := by
  simp only [stripBarrier, exp_re, mul_re, ofReal_re, ofReal_im, sub_re, sub_im, neg_re, neg_im,
    zero_mul, sub_zero, mul_im]
  simp only [div_ofNat_re, div_ofNat_im, I_re, I_im, Real.cos_neg]
  ring_nf

private theorem harmonicOnNhd_stripBarrier :
    InnerProductSpace.HarmonicOnNhd stripBarrier strip := by
  intro z _
  have h1 : AnalyticAt ℂ (fun w : ℂ => exp (((π / 2 : ℝ) : ℂ) * (w - I / 2))) z :=
    (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp
  have h2 : AnalyticAt ℂ (fun w : ℂ => exp (-(((π / 2 : ℝ) : ℂ) * (w - I / 2)))) z :=
    (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).neg.cexp
  exact h1.harmonicAt_re.add h2.harmonicAt_re

private theorem half_le_cos_of_mem_strip {z : ℂ} (hz : z ∈ strip) :
    1 / 2 ≤ Real.cos (π / 2 * (z.im - 1 / 2)) := by
  obtain ⟨h0, h1⟩ := hz
  have hpi := Real.pi_pos
  have habs : |π / 2 * (z.im - 1 / 2)| ≤ π / 3 := by
    rw [abs_le]; constructor <;> nlinarith
  calc (1 : ℝ) / 2 = Real.cos (π / 3) := Real.cos_pi_div_three.symm
    _ ≤ Real.cos |π / 2 * (z.im - 1 / 2)| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
    _ = Real.cos (π / 2 * (z.im - 1 / 2)) := Real.cos_abs _

private theorem stripBarrier_ge {z : ℂ} (hz : z ∈ strip) :
    (π / 2 * |z.re| + 1) / 2 ≤ stripBarrier z := by
  rw [stripBarrier_eq]
  have hc := half_le_cos_of_mem_strip hz
  have e1 := Real.add_one_le_exp (π / 2 * z.re)
  have e2 := Real.add_one_le_exp (-(π / 2 * z.re))
  have p1 := Real.exp_pos (π / 2 * z.re)
  have p2 := Real.exp_pos (-(π / 2 * z.re))
  have hpi := Real.pi_pos
  have hsum : π / 2 * |z.re| + 1 ≤ Real.exp (π / 2 * z.re) + Real.exp (-(π / 2 * z.re)) := by
    rcases abs_cases z.re with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
  have hpos : 0 ≤ π / 2 * |z.re| + 1 := by positivity
  nlinarith

/-- **Lindelöf's maximum principle on the strip** (bounded version, finitely many exceptional
boundary points on each line). -/
theorem le_zero_of_harmonicOnNhd_strip {f : ℂ → ℝ} (Elo Eup : Finset ℝ)
    (hf : InnerProductSpace.HarmonicOnNhd f strip) (hbd : BddAbove (f '' strip))
    (hlo : ∀ t : ℝ, t ∉ Elo → ∀ ε > 0, ∀ᶠ z in 𝓝[strip] (t : ℂ), f z ≤ ε)
    (hup : ∀ t : ℝ, t ∉ Eup → ∀ ε > 0, ∀ᶠ z in 𝓝[strip] ((t : ℂ) + I), f z ≤ ε) :
    ∀ z ∈ strip, f z ≤ 0 := by
  have hpi := Real.pi_pos
  refine harmonic_le_zero_of_barrier
    (Elo.image ((↑) : ℝ → ℂ) ∪ Eup.image fun t : ℝ => (t : ℂ) + I) isOpen_strip hf hbd ?_
    harmonicOnNhd_stripBarrier
    (fun y hy => le_trans (by positivity) (stripBarrier_ge hy)) ?_
  · intro x₀ hx₀ hx₀E
    rcases im_eq_zero_or_eq_one_of_mem_frontier_strip hx₀ with him | him
    · have hx : ((x₀.re : ℝ) : ℂ) = x₀ := Complex.ext (by simp) (by simp [him])
      have hre : x₀.re ∉ Elo := fun h =>
        hx₀E (Finset.mem_union_left _ (Finset.mem_image.2 ⟨x₀.re, h, hx⟩))
      rw [← hx]
      exact hlo x₀.re hre
    · have hx : ((x₀.re : ℝ) : ℂ) + I = x₀ := Complex.ext (by simp) (by simp [him])
      have hre : x₀.re ∉ Eup := fun h =>
        hx₀E (Finset.mem_union_right _ (Finset.mem_image.2 ⟨x₀.re, h, hx⟩))
      rw [← hx]
      exact hup x₀.re hre
  · intro M
    refine ⟨2 * |M| / (π / 2) + 1, fun y hy hRy => ?_⟩
    have hb := stripBarrier_ge hy
    have hn : ‖y‖ ≤ |y.re| + 1 := by
      have := Complex.norm_le_abs_re_add_abs_im y
      have : |y.im| ≤ 1 := abs_le.2 ⟨by linarith [hy.1], hy.2.le⟩
      linarith
    have h1 : 2 * |M| / (π / 2) ≤ |y.re| := by linarith
    have h2 : 2 * |M| ≤ π / 2 * |y.re| := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    linarith [le_abs_self M]

/-- Two bounded harmonic functions on the strip whose difference tends to `0` at every point of
the two boundary lines outside finite sets agree on the strip. -/
theorem eqOn_of_tendsto_sub_strip {u w : ℂ → ℝ} (Elo Eup : Finset ℝ)
    (hu : InnerProductSpace.HarmonicOnNhd u strip) (hw : InnerProductSpace.HarmonicOnNhd w strip)
    (hub : Bornology.IsBounded (u '' strip)) (hwb : Bornology.IsBounded (w '' strip))
    (hlo : ∀ t : ℝ, t ∉ Elo → Tendsto (fun z => u z - w z) (𝓝[strip] (t : ℂ)) (𝓝 0))
    (hup : ∀ t : ℝ, t ∉ Eup → Tendsto (fun z => u z - w z) (𝓝[strip] ((t : ℂ) + I)) (𝓝 0)) :
    EqOn u w strip := by
  obtain ⟨Cu, hCu⟩ := isBounded_iff_forall_norm_le.1 hub
  obtain ⟨Cw, hCw⟩ := isBounded_iff_forall_norm_le.1 hwb
  have bu : ∀ z ∈ strip, |u z| ≤ Cu := fun z hz => hCu _ ⟨z, hz, rfl⟩
  have bw : ∀ z ∈ strip, |w z| ≤ Cw := fun z hz => hCw _ ⟨z, hz, rfl⟩
  have hbd : ∀ (f g : ℂ → ℝ), (∀ z ∈ strip, |f z| ≤ Cu + Cw ∧ |g z| ≤ Cu + Cw) →
      BddAbove ((f - g) '' strip) := by
    intro f g hfg
    refine ⟨2 * (Cu + Cw), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Pi.sub_apply]
    linarith [abs_le.1 (hfg z hz).1, abs_le.1 (hfg z hz).2]
  have hCu0 : ∀ z ∈ strip, 0 ≤ Cu := fun z hz => (abs_nonneg _).trans (bu z hz)
  have hCw0 : ∀ z ∈ strip, 0 ≤ Cw := fun z hz => (abs_nonneg _).trans (bw z hz)
  have hbnd : ∀ z ∈ strip, |u z| ≤ Cu + Cw ∧ |w z| ≤ Cu + Cw := fun z hz =>
    ⟨by linarith [bu z hz, hCw0 z hz], by linarith [bw z hz, hCu0 z hz]⟩
  have ev : ∀ (F : Filter ℂ), Tendsto (fun z => u z - w z) F (𝓝 0) → ∀ ε > 0,
      (∀ᶠ z in F, (u - w) z ≤ ε) ∧ ∀ᶠ z in F, (w - u) z ≤ ε := by
    intro F hF ε hε
    refine ⟨?_, ?_⟩
    · filter_upwards [hF.eventually (gt_mem_nhds hε)] with z hz
      simp only [Pi.sub_apply]; linarith
    · have := hF.neg
      rw [neg_zero] at this
      filter_upwards [this.eventually (gt_mem_nhds hε)] with z hz
      simp only [Pi.sub_apply]; linarith
  have h1 := le_zero_of_harmonicOnNhd_strip Elo Eup (hu.sub hw) (hbd u w hbnd)
    (fun t ht ε hε => (ev _ (hlo t ht) ε hε).1) (fun t ht ε hε => (ev _ (hup t ht) ε hε).1)
  have h2 := le_zero_of_harmonicOnNhd_strip Elo Eup (hw.sub hu)
    (hbd w u fun z hz => ⟨(hbnd z hz).2, (hbnd z hz).1⟩)
    (fun t ht ε hε => (ev _ (hlo t ht) ε hε).2) (fun t ht ε hε => (ev _ (hup t ht) ε hε).2)
  intro z hz
  have a := h1 z hz
  have b := h2 z hz
  simp only [Pi.sub_apply] at a b
  linarith

/-! ### `exp (π z)` maps the strip into `ℍ` -/

theorem exp_pi_mul_mem_H {z : ℂ} (hz : z ∈ strip) : exp (π * z) ∈ H := by
  show 0 < (exp (π * z)).im
  rw [exp_im]
  have hre : (↑π * z).im = π * z.im := by simp
  rw [hre]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hz.1) (by nlinarith [Real.pi_pos, hz.2]))

private theorem analyticAt_exp_pi_mul (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => exp (π * w)) z :=
  (analyticAt_const.mul analyticAt_id).cexp

private theorem tendsto_exp_pi_mul_nhdsWithin (z : ℂ) :
    Tendsto (fun w : ℂ => exp (π * w)) (𝓝[strip] z) (𝓝[H] (exp (π * z))) :=
  tendsto_nhdsWithin_iff.2
    ⟨((analyticAt_exp_pi_mul z).continuousAt.tendsto).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun _ hw => exp_pi_mul_mem_H hw⟩

/-- Bounded piecewise-constant data on the two boundary lines of the strip: `lower` on `ℝ`,
`upper` on `ℝ + i`, each as a function of the real part. -/
structure StripStepData where
  /-- data on the lower line `ℝ` -/
  lower : StepData
  /-- data on the upper line `ℝ + i` -/
  upper : StepData

namespace StripStepData

variable (s : StripStepData)

/-- Breakpoints of the transported word on `∂ℍ` under `z ↦ exp(πz)` (lower line to `(0, ∞)`,
upper line to `(−∞, 0)` with reversed order, strip ends `∓∞` to `0` and `∞`). -/
def bptsH : Fin (s.upper.n + 1 + s.lower.n) → ℝ :=
  Fin.append
    (Fin.append (fun j : Fin s.upper.n => -Real.exp (π * s.upper.x j.rev)) fun _ : Fin 1 => 0)
    fun j : Fin s.lower.n => Real.exp (π * s.lower.x j)

/-- Values of the transported word on `∂ℍ`. -/
def valsH (k : Fin (s.upper.n + 1 + s.lower.n + 1)) : ℝ :=
  Fin.append (fun k : Fin (s.upper.n + 1) => s.upper.v k.rev)
    (fun k : Fin (s.lower.n + 1) => s.lower.v k) (Fin.cast (by omega) k)

/-- The bounded harmonic extension in the strip (Specification p. 2, "in the strip"). -/
def harmonicExt (z : ℂ) : ℝ :=
  stepHarmonicH (s.upper.n + 1 + s.lower.n) s.bptsH s.valsH (exp (π * z))

theorem bptsH_upper (i : Fin s.upper.n) :
    s.bptsH (Fin.castAdd s.lower.n (Fin.castAdd 1 i)) = -Real.exp (π * s.upper.x i.rev) := by
  simp [bptsH]

theorem bptsH_zero : s.bptsH (Fin.castAdd s.lower.n (Fin.natAdd s.upper.n 0)) = 0 := by
  simp [bptsH]

theorem bptsH_lower (i : Fin s.lower.n) :
    s.bptsH (Fin.natAdd (s.upper.n + 1) i) = Real.exp (π * s.lower.x i) := by
  simp [bptsH]

theorem bptsH_castAdd_nonpos (i : Fin (s.upper.n + 1)) : s.bptsH (Fin.castAdd s.lower.n i) ≤ 0 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [bptsH_upper]; exact neg_nonpos.2 (Real.exp_pos _).le
  · rw [Fin.fin_one_eq_zero i, bptsH_zero]

theorem monotone_bptsH : Monotone s.bptsH := by
  intro i j hij
  revert hij
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij
  · -- both in the nonpositive part
    have hij' : i ≤ j := by
      have := Fin.le_def.1 hij
      simp only [Fin.val_castAdd] at this
      exact Fin.le_def.2 this
    revert hij'
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij'
    · rw [bptsH_upper, bptsH_upper, neg_le_neg_iff, Real.exp_le_exp]
      have hij'' : i ≤ j := by
        have := Fin.le_def.1 hij'
        simp only [Fin.val_castAdd] at this
        exact Fin.le_def.2 this
      have : j.rev ≤ i.rev := Fin.rev_le_rev.2 hij''
      exact mul_le_mul_of_nonneg_left (s.upper.monotone_x this) Real.pi_pos.le
    · rw [bptsH_upper, Fin.fin_one_eq_zero j, bptsH_zero]
      exact neg_nonpos.2 (Real.exp_pos _).le
    · exfalso
      have := (Fin.le_def.1 hij')
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    · rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  · exact (s.bptsH_castAdd_nonpos i).trans (by rw [bptsH_lower]; exact (Real.exp_pos _).le)
  · exfalso
    have := (Fin.le_def.1 hij)
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  · rw [bptsH_lower, bptsH_lower, Real.exp_le_exp]
    have hij' : i ≤ j := by
      have := Fin.le_def.1 hij
      simp only [Fin.val_natAdd] at this
      exact Fin.le_def.2 (by omega)
    exact mul_le_mul_of_nonneg_left (s.lower.monotone_x hij') Real.pi_pos.le

/-- The transported word on `∂ℍ`. -/
def toH : StepData where
  n := s.upper.n + 1 + s.lower.n
  x := s.bptsH
  monotone_x := s.monotone_bptsH
  v := s.valsH

theorem harmonicExt_eq (z : ℂ) : s.harmonicExt z = s.toH.harmonicExtH (exp (π * z)) := rfl

theorem harmonicOnNhd_harmonicExt : InnerProductSpace.HarmonicOnNhd s.harmonicExt strip :=
  fun _ hz => harmonicAt_stepHarmonicH_comp _ s.bptsH s.valsH (analyticAt_exp_pi_mul _)
    (exp_pi_mul_mem_H hz)

theorem isBounded_image_harmonicExt : Bornology.IsBounded (s.harmonicExt '' strip) :=
  s.toH.isBounded_image_harmonicExtH.subset
    (Set.image_subset_iff.2 fun _ hz => ⟨_, exp_pi_mul_mem_H hz, (s.harmonicExt_eq _).symm⟩)

private theorem card_le_n (d : StepData) (t : ℝ) :
    (univ.filter fun i => d.x i ≤ t).card ≤ d.n :=
  (card_filter_le _ _).trans (by simp)

private theorem exp_pi_mul_ofReal (t : ℝ) : exp (π * (t : ℂ)) = ((Real.exp (π * t) : ℝ) : ℂ) := by
  rw [ofReal_exp, ofReal_mul]

private theorem exp_pi_mul_ofReal_add_I (t : ℝ) :
    exp (π * ((t : ℂ) + I)) = ((-Real.exp (π * t) : ℝ) : ℂ) := by
  rw [mul_add, exp_add, exp_pi_mul_I, exp_pi_mul_ofReal]
  push_cast
  ring

theorem toH_bdry_exp (t : ℝ) :
    s.toH.bdry (Real.exp (π * t)) = s.lower.bdry t := by
  set c := (univ.filter fun i => s.lower.x i ≤ t).card with hc
  have hcn : c ≤ s.lower.n := card_le_n _ _
  have hk : s.upper.n + 1 + c ≤ s.toH.n := by show _ ≤ s.upper.n + 1 + s.lower.n; omega
  rw [s.toH.bdry_eq_of_forall_le_iff hk]
  · show s.valsH (⟨s.upper.n + 1 + c, by omega⟩ : Fin (s.upper.n + 1 + s.lower.n + 1)) = s.lower.v _
    have hcast : (Fin.cast (by omega) (⟨s.upper.n + 1 + c, by omega⟩ :
        Fin (s.upper.n + 1 + s.lower.n + 1)) : Fin (s.upper.n + 1 + (s.lower.n + 1))) =
        Fin.natAdd (s.upper.n + 1) (⟨c, by omega⟩ : Fin (s.lower.n + 1)) := Fin.ext rfl
    unfold valsH
    rw [hcast, Fin.append_right]
  · intro j
    show s.bptsH j ≤ _ ↔ _
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have h1 := s.bptsH_castAdd_nonpos i
      have h2 := Real.exp_pos (π * t)
      simp only [Fin.val_castAdd]
      exact ⟨fun _ => by omega, fun _ => by linarith⟩
    · rw [bptsH_lower, Real.exp_le_exp, mul_le_mul_iff_right₀ Real.pi_pos,
        le_iff_lt_card_filter s.lower.monotone_x t i, Fin.val_natAdd, ← hc]
      omega

theorem toH_bdry_neg_exp (t : ℝ) (ht : ∀ j, s.upper.x j ≠ t) :
    s.toH.bdry (-Real.exp (π * t)) = s.upper.bdry t := by
  set c := (univ.filter fun i => s.upper.x i ≤ t).card with hc
  have hcn : c ≤ s.upper.n := card_le_n _ _
  have hk : s.upper.n - c ≤ s.toH.n := by show _ ≤ s.upper.n + 1 + s.lower.n; omega
  rw [s.toH.bdry_eq_of_forall_le_iff hk]
  · show s.valsH (⟨s.upper.n - c, by omega⟩ : Fin (s.upper.n + 1 + s.lower.n + 1)) = s.upper.v _
    have hcast : (Fin.cast (by omega) (⟨s.upper.n - c, by omega⟩ :
        Fin (s.upper.n + 1 + s.lower.n + 1)) : Fin (s.upper.n + 1 + (s.lower.n + 1))) =
        Fin.castAdd (s.lower.n + 1) (⟨s.upper.n - c, by omega⟩ : Fin (s.upper.n + 1)) :=
      Fin.ext rfl
    unfold valsH
    rw [hcast, Fin.append_left]
    show s.upper.v _ = s.upper.v _
    congr 1
    ext
    simp only [Fin.val_rev]
    omega
  · intro j
    show s.bptsH j ≤ _ ↔ _
    have h2 := Real.exp_pos (π * t)
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [bptsH_upper, neg_le_neg_iff, Real.exp_le_exp, mul_le_mul_iff_right₀ Real.pi_pos]
        have hiff := le_iff_lt_card_filter s.upper.monotone_x t i.rev
        rw [← hc, Fin.val_rev] at hiff
        simp only [Fin.val_castAdd]
        have hne := ht i.rev
        have hi := i.2
        constructor
        · intro h
          have : ¬ s.upper.x i.rev ≤ t := fun h' => hne (le_antisymm h' h)
          rw [hiff] at this
          omega
        · intro h
          have : ¬ s.upper.x i.rev ≤ t := by rw [hiff]; omega
          linarith [not_le.1 this]
      · rw [Fin.fin_one_eq_zero i, bptsH_zero]
        simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero]
        exact ⟨fun h => by linarith, fun h => by omega⟩
    · rw [bptsH_lower]
      simp only [Fin.val_natAdd]
      have := Real.exp_pos (π * s.lower.x i)
      exact ⟨fun h => by linarith, fun h => by omega⟩

theorem tendsto_harmonicExt_lower {t : ℝ} (ht : ∀ j, s.lower.x j ≠ t) :
    Tendsto s.harmonicExt (𝓝[strip] (t : ℂ)) (𝓝 (s.lower.bdry t)) := by
  have hne : ∀ j, s.toH.x j ≠ Real.exp (π * t) := by
    intro j
    show s.bptsH j ≠ _
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact ne_of_lt ((s.bptsH_castAdd_nonpos i).trans_lt (Real.exp_pos _))
    · rw [bptsH_lower]
      intro h
      exact ht i (mul_left_cancel₀ Real.pi_ne_zero (Real.exp_injective h))
  have h1 := tendsto_exp_pi_mul_nhdsWithin (t : ℂ)
  rw [exp_pi_mul_ofReal] at h1
  rw [← s.toH_bdry_exp t]
  exact (s.toH.tendsto_harmonicExtH hne).comp h1

theorem tendsto_harmonicExt_upper {t : ℝ} (ht : ∀ j, s.upper.x j ≠ t) :
    Tendsto s.harmonicExt (𝓝[strip] ((t : ℂ) + I)) (𝓝 (s.upper.bdry t)) := by
  have hne : ∀ j, s.toH.x j ≠ -Real.exp (π * t) := by
    intro j
    show s.bptsH j ≠ _
    have h2 := Real.exp_pos (π * t)
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [bptsH_upper]
        intro h
        exact ht i.rev (mul_left_cancel₀ Real.pi_ne_zero (Real.exp_injective (neg_inj.1 h)))
      · rw [Fin.fin_one_eq_zero i, bptsH_zero]
        intro h
        linarith
    · rw [bptsH_lower]
      intro h
      linarith [Real.exp_pos (π * s.lower.x i)]
  have h1 := tendsto_exp_pi_mul_nhdsWithin ((t : ℂ) + I)
  rw [exp_pi_mul_ofReal_add_I] at h1
  rw [← s.toH_bdry_neg_exp t ht]
  exact (s.toH.tendsto_harmonicExtH hne).comp h1

theorem eqOn_harmonicExt {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u strip)
    (hbdd : Bornology.IsBounded (u '' strip))
    (hlo : ∀ t : ℝ, (∀ j, s.lower.x j ≠ t) → Tendsto u (𝓝[strip] (t : ℂ)) (𝓝 (s.lower.bdry t)))
    (hup : ∀ t : ℝ, (∀ j, s.upper.x j ≠ t) →
      Tendsto u (𝓝[strip] ((t : ℂ) + I)) (𝓝 (s.upper.bdry t))) :
    EqOn u s.harmonicExt strip := by
  refine eqOn_of_tendsto_sub_strip (univ.image s.lower.x) (univ.image s.upper.x) hu
    s.harmonicOnNhd_harmonicExt hbdd s.isBounded_image_harmonicExt (fun t ht => ?_)
    (fun t ht => ?_)
  · have ht' : ∀ j, s.lower.x j ≠ t := fun j hj => ht (mem_image.2 ⟨j, mem_univ _, hj⟩)
    simpa using (hlo t ht').sub (s.tendsto_harmonicExt_lower ht')
  · have ht' : ∀ j, s.upper.x j ≠ t := fun j hj => ht (mem_image.2 ⟨j, mem_univ _, hj⟩)
    simpa using (hup t ht').sub (s.tendsto_harmonicExt_upper ht')

end StripStepData

end InteractingSLE
