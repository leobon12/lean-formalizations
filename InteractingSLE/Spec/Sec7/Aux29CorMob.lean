/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInActPoisson
import InteractingSLE.Spec.Sec7.Aux2728Pocket
import InteractingSLE.Spec.Sec6.DiskCaratheodory

/-!
# Aux. lemma 29 for a conformal chart through the bounded coordinate `1/(z + i)`

PROVE-AUX29-CORNER. Theorem 1.2's R.7 collar (`hSideCollar`) asks for R.5's old-chart comparison at
every real current coordinate off the jump set. R.5 gives no comparison at a prime end whose physical
landing is the current tip or the bounded pocket's outgoing corner (specification p. 474–475: "All
current real preimages of each such exceptional physical point are excluded here"). The source covers
those prime ends with Aux. lemma 29 (p. 164): the full stopped Gaussian kernel (p. 475) is identified
by "the retained subpower estimate and the logarithmic-derivative estimate", and "Aux. 29 removes
every singular harmonic term, including all prime ends over those finitely many physical points".

Aux. 29 (`Sec6.aux29_eqOn_of_tendsto`, landed through
`PocketStopSide.mean_eq_phaseWordExt_of_incident_germs`) is stated on a domain with a disc
uniformization continuous on the closed disc, hence a bounded one. A current pocket domain can be
unbounded (the seed-opening pocket), and its inverse chart lands at `∞`. Following the source's
"fixed conformal compactification of the ambient domain" (p. 199), this file transports the whole
argument by the Möbius map `mob z = 1/(z + i)`, which maps `ℍ̄` into the closed unit disc and `∞` to
`0`:

* the disc chart `discMap F p` (`ζ ↦ mob (F (cayleyInv ζ))`, value `p` at `1`) is a conformal
  bijection onto `mob '' dom`, continuous on the closed disc (`continuousOn_discMap`), given a
  continuous extension `F` of the chart inverse to `ℍ̄` and the limit `p` of `mob ∘ inverse` at `∞`;
* logarithmic growth on `dom ⊆ ℍ` (Wang–Wu Lemma 4.6's global form) becomes subpower growth on
  `mob '' dom` (`abs_le_comp_mobInv`);
* the derivative argument of `c.1 ∘ mobInv` is `A ∘ mobInv + (π − 2 arg)` (`deriv_comp_mobInv`);
  the correction `π − 2 arg` is harmonic and bounded on the lower half-plane;
* **`eqOn_phaseWordExt_of_landing_germs`**: if the corrected mean has the phase word's boundary value
  at every real chart point whose physical landing avoids a given finite set `X`, the landings of the
  jump points and the landing at `∞`, then it equals the full phase word on the whole domain.

The exceptional physical points may carry infinitely many prime ends; nothing about their fibres is
assumed. Deterministic; no hypothesis is a probabilistic or source-level input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar chiC)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped Real

namespace InteractingSLE.Sec7.Aux29Cor

open PocketStopSide PhaseSel

/-- The Möbius map `z ↦ 1/(z + i)`; it sends `ℍ̄` into the closed unit disc and `∞` to `0`. -/
def mob (z : ℂ) : ℂ := (z + I)⁻¹

/-- The inverse Möbius map `w ↦ 1/w − i`. -/
def mobInv (w : ℂ) : ℂ := w⁻¹ - I

@[simp] theorem mobInv_mob (z : ℂ) : mobInv (mob z) = z := by simp [mob, mobInv]

@[simp] theorem mob_mobInv (w : ℂ) : mob (mobInv w) = w := by simp [mob, mobInv]

theorem mob_injective : Function.Injective mob := fun z y h => by
  rw [← mobInv_mob z, h, mobInv_mob]

theorem image_mob_eq_preimage (O : Set ℂ) : mob '' O = mobInv ⁻¹' O := by
  ext w
  refine ⟨?_, fun hw => ⟨mobInv w, hw, mob_mobInv w⟩⟩
  rintro ⟨z, hz, rfl⟩
  simpa using hz

theorem one_le_norm_add_I {z : ℂ} (hz : z ∈ Hbar) : 1 ≤ ‖z + I‖ := by
  have hz' : (0 : ℝ) ≤ z.im := hz
  have h : (z + I).im = z.im + 1 := by simp
  calc (1 : ℝ) ≤ (z + I).im := by rw [h]; linarith
    _ ≤ |(z + I).im| := le_abs_self _
    _ ≤ ‖z + I‖ := Complex.abs_im_le_norm _

theorem add_I_ne_zero {z : ℂ} (hz : z ∈ Hbar) : z + I ≠ 0 := by
  intro h
  have := one_le_norm_add_I hz
  rw [h, norm_zero] at this
  linarith

theorem mob_ne_zero {z : ℂ} (hz : z ∈ Hbar) : mob z ≠ 0 := inv_ne_zero (add_I_ne_zero hz)

theorem norm_mob_le_one {z : ℂ} (hz : z ∈ Hbar) : ‖mob z‖ ≤ 1 := by
  rw [mob, norm_inv]
  exact inv_le_one_of_one_le₀ (one_le_norm_add_I hz)

theorem im_mob_neg {z : ℂ} (hz : z ∈ Hbar) : (mob z).im < 0 := by
  have hz' : (0 : ℝ) ≤ z.im := hz
  rw [mob, Complex.inv_im]
  have hn : 0 < Complex.normSq (z + I) := Complex.normSq_pos.2 (add_I_ne_zero hz)
  have h : (z + I).im = z.im + 1 := by simp
  rw [h, neg_div]
  exact neg_neg_of_pos (div_pos (by linarith) hn)

theorem mob_mem_slitPlane {z : ℂ} (hz : z ∈ Hbar) : mob z ∈ slitPlane :=
  Or.inr (im_mob_neg hz).ne

/-- `mob` is `1`-Lipschitz on `ℍ̄`. -/
theorem norm_mob_sub_le {z y : ℂ} (hz : z ∈ Hbar) (hy : y ∈ Hbar) :
    ‖mob z - mob y‖ ≤ ‖z - y‖ := by
  have hz0 := add_I_ne_zero hz
  have hy0 := add_I_ne_zero hy
  have e : mob z - mob y = (y - z) / ((z + I) * (y + I)) := by
    rw [mob, mob, inv_sub_inv hz0 hy0]
    ring_nf
  rw [e, norm_div, norm_mul, norm_sub_rev y z]
  have h1 := one_le_norm_add_I hz
  have h2 := one_le_norm_add_I hy
  have hp : 1 ≤ ‖z + I‖ * ‖y + I‖ := one_le_mul_of_one_le_of_one_le h1 h2
  exact div_le_self (norm_nonneg _) hp

theorem continuousAt_mob {z : ℂ} (hz : z ∈ Hbar) : ContinuousAt mob z :=
  (continuousAt_id.add continuousAt_const).inv₀ (add_I_ne_zero hz)

theorem differentiableAt_mob {z : ℂ} (hz : z ∈ Hbar) : DifferentiableAt ℂ mob z :=
  (differentiableAt_id.add_const I).inv (add_I_ne_zero hz)

theorem differentiableAt_mobInv {w : ℂ} (hw : w ≠ 0) : DifferentiableAt ℂ mobInv w :=
  (differentiableAt_inv hw).sub_const I

theorem deriv_mobInv (w : ℂ) : deriv mobInv w = -(w ^ 2)⁻¹ := by
  have h : deriv mobInv w = deriv (fun w : ℂ => w⁻¹) w := by
    show deriv (fun w : ℂ => w⁻¹ - I) w = _
    rw [deriv_sub_const]
  rw [h, deriv_inv]

theorem mobInv_ne_neg_I_of_ne_zero {w : ℂ} (hw : w ≠ 0) : mobInv w ≠ -I := by
  intro h
  apply hw
  have : w⁻¹ = 0 := by rw [mobInv] at h; linear_combination h
  exact inv_eq_zero.1 this

theorem continuousAt_mobInv {w : ℂ} (hw : w ≠ 0) : ContinuousAt mobInv w :=
  (differentiableAt_mobInv hw).continuousAt

/-- `mob` maps an open subset of `ℍ` onto an open set. -/
theorem isOpen_image_mob {O : Set ℂ} (hOo : IsOpen O) (hOH : O ⊆ H) : IsOpen (mob '' O) := by
  rw [image_mob_eq_preimage]
  have hsub : mobInv ⁻¹' O ⊆ {w | w ≠ 0} := by
    intro w hw h0
    have := hOH hw
    rw [h0, mobInv, inv_zero, zero_sub] at this
    have h' : (0 : ℝ) < (-I).im := this
    simp at h'
    linarith
  have hcont : ContinuousOn mobInv {w | w ≠ 0} := fun w hw => (continuousAt_mobInv hw).continuousWithinAt
  have := hcont.isOpen_inter_preimage isOpen_ne hOo
  rwa [inter_eq_right.2 hsub] at this

theorem image_mob_subset_ball {O : Set ℂ} (hOH : O ⊆ H) : mob '' O ⊆ closedBall 0 1 := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_closedBall_zero_iff]
  exact norm_mob_le_one (QuantumZipper.H_subset_Hbar (hOH hz))

theorem image_mob_subset_lower {O : Set ℂ} (hOH : O ⊆ H) : mob '' O ⊆ {w | w.im < 0} := by
  rintro _ ⟨z, hz, rfl⟩
  exact im_mob_neg (QuantumZipper.H_subset_Hbar (hOH hz))

/-- `mob` sends the frontier of an open subset of `ℍ` into the frontier of its image. -/
theorem mob_mem_frontier {O : Set ℂ} (hOo : IsOpen O) (hOH : O ⊆ H) {z : ℂ}
    (hz : z ∈ frontier O) : mob z ∈ frontier (mob '' O) := by
  have hzc : z ∈ closure O := frontier_subset_closure hz
  have hzH : z ∈ Hbar := by
    have : closure O ⊆ Hbar := (closure_mono hOH).trans
      (QuantumZipper.CA.Car.closure_H_eq_Hbar ▸ subset_rfl)
    exact this hzc
  rw [(isOpen_image_mob hOo hOH).frontier_eq]
  refine ⟨mem_closure_image (continuousAt_mob hzH) hzc, ?_⟩
  rintro ⟨y, hy, he⟩
  rw [hOo.frontier_eq] at hz
  exact hz.2 (mob_injective he ▸ hy)


/-! ### Boundary values of a conformal chart's inverse -/

theorem real_mem_Hbar (x : ℝ) : (x : ℂ) ∈ Hbar := by
  show (0 : ℝ) ≤ (x : ℂ).im
  simp

theorem neBot_nhdsWithin_H {w : ℂ} (hw : w ∈ Hbar) : (𝓝[H] w).NeBot := by
  apply mem_closure_iff_nhdsWithin_neBot.1
  rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
  exact hw

theorem neBot_cobounded_inf_H : (Bornology.cobounded ℂ ⊓ 𝓟 H).NeBot := by
  refine (Filter.hasBasis_cobounded_norm.inf_principal H).neBot_iff.2 fun {R} _ => ?_
  refine ⟨((|R| + 1 : ℝ) : ℂ) * I, ?_, ?_⟩
  · show R ≤ ‖((|R| + 1 : ℝ) : ℂ) * I‖
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith [le_abs_self R]
  · show (0 : ℝ) < (((|R| + 1 : ℝ) : ℂ) * I).im
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    positivity

variable {c : Chart}

/-- The extension of the inverse is the boundary limit of the inverse from `ℍ`. -/
theorem tendsto_inv_of_extension {F : ℂ → ℂ} (hF : EqOn F c.2.1 H) (hFc : ContinuousOn F Hbar)
    {w : ℂ} (hw : w ∈ Hbar) : Tendsto c.2.1 (𝓝[H] w) (𝓝 (F w)) :=
  ((hFc w hw).mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)).congr'
    (eventually_nhdsWithin_of_forall fun _ hy => hF hy)

/-- A real boundary value of the inverse lies on the frontier of the chart domain. -/
theorem extension_real_mem_frontier (hc : c.IsConformal) {F : ℂ → ℂ} (hF : EqOn F c.2.1 H)
    (hFc : ContinuousOn F Hbar) (x : ℝ) : F x ∈ frontier (c.dom : Set ℂ) := by
  have hlim := tendsto_inv_of_extension hF hFc (real_mem_Hbar x)
  have := neBot_nhdsWithin_H (real_mem_Hbar x)
  rw [c.dom.isOpen.frontier_eq]
  refine ⟨mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun _ hy => hc.inv_mem_dom hy),
    fun hFx => ?_⟩
  have hfwd : Tendsto (fun y => c.1 (c.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (c.1 (F x))) :=
    ((hc.differentiableOn_fwd.differentiableAt (c.dom.isOpen.mem_nhds hFx)).continuousAt.tendsto).comp hlim
  have hid : Tendsto (fun y => c.1 (c.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
      (eventually_nhdsWithin_of_forall fun y hy => (hc.2.2 y hy).symm)
  have he := tendsto_nhds_unique hfwd hid
  have hmem := hc.fwd_mem hFx
  rw [he] at hmem
  have : (0 : ℝ) < (x : ℂ).im := hmem
  simp at this

/-- The extension maps `ℍ̄` into `ℍ̄`. -/
theorem extension_mem_Hbar (hc : c.IsConformal) {F : ℂ → ℂ} (hF : EqOn F c.2.1 H)
    (hFc : ContinuousOn F Hbar) {w : ℂ} (hw : w ∈ Hbar) : F w ∈ Hbar := by
  have hcl : closure (c.dom : Set ℂ) ⊆ Hbar := (closure_mono hc.dom_subset).trans
    (QuantumZipper.CA.Car.closure_H_eq_Hbar ▸ subset_rfl)
  have := neBot_nhdsWithin_H hw
  exact hcl (mem_closure_of_tendsto (tendsto_inv_of_extension hF hFc hw)
    (eventually_nhdsWithin_of_forall fun _ hy => hc.inv_mem_dom hy))

/-- A limit at `∞` within `ℍ` of a function continuous on `ℍ̄` is also its limit within `ℍ̄`. -/
theorem tendsto_cobounded_Hbar {G : ℂ → ℂ} (hGc : ContinuousOn G Hbar) {p : ℂ}
    (hG : Tendsto G (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p)) :
    Tendsto G (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 p) := by
  rw [Metric.tendsto_nhds] at hG ⊢
  intro ε hε
  have h2 := hG (ε / 2) (by positivity)
  rw [(Filter.hasBasis_cobounded_norm.inf_principal H).eventually_iff] at h2
  obtain ⟨R, -, hR⟩ := h2
  rw [(Filter.hasBasis_cobounded_norm.inf_principal Hbar).eventually_iff]
  refine ⟨R + 1, trivial, fun w ⟨hwR, hwH⟩ => ?_⟩
  have hwR' : R + 1 ≤ ‖w‖ := hwR
  have hpath : Tendsto (fun t : ℝ => w + (t : ℂ) * I) (𝓝[>] 0) (𝓝[Hbar] w) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous (fun t : ℝ => w + (t : ℂ) * I) := by fun_prop
      have := hc.tendsto 0
      simp only [ofReal_zero, zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      show (0 : ℝ) ≤ (w + (t : ℂ) * I).im
      have ht' : (0 : ℝ) < t := ht
      have hw' : (0 : ℝ) ≤ w.im := hwH
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith
  have hlim : Tendsto (fun t : ℝ => dist (G (w + (t : ℂ) * I)) p) (𝓝[>] 0) (𝓝 (dist (G w) p)) :=
    (((hGc w hwH).tendsto.comp hpath).dist tendsto_const_nhds)
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, dist (G (w + (t : ℂ) * I)) p ≤ ε / 2 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    refine (hR ⟨?_, ?_⟩).le
    · show R ≤ ‖w + (t : ℂ) * I‖
      have h1 : ‖(t : ℂ) * I‖ = t := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      have h2 := norm_sub_norm_le w (-((t : ℂ) * I))
      rw [sub_neg_eq_add, norm_neg, h1] at h2
      linarith [ht.2]
    · show (0 : ℝ) < (w + (t : ℂ) * I).im
      have hw' : (0 : ℝ) ≤ w.im := hwH
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith [ht.1]
  exact (le_of_tendsto hlim hev).trans_lt (by linarith)

/-- The limit at `∞` of `mob ∘ inv` lies on the frontier of the image domain. -/
theorem limit_mem_frontier (hc : c.IsConformal) {p : ℂ}
    (hp : Tendsto (fun w => mob (c.2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p)) :
    p ∈ frontier (mob '' (c.dom : Set ℂ)) := by
  have := neBot_cobounded_inf_H
  rw [(isOpen_image_mob c.dom.isOpen hc.dom_subset).frontier_eq]
  refine ⟨mem_closure_of_tendsto hp (eventually_inf_principal.2 (Eventually.of_forall
    fun _ hw => mem_image_of_mem _ (hc.inv_mem_dom hw))), ?_⟩
  rintro ⟨z, hz, rfl⟩
  have hzH : z ∈ Hbar := QuantumZipper.H_subset_Hbar (hc.dom_subset hz)
  have h1 : Tendsto c.2.1 (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 z) := by
    have := ((continuousAt_mobInv (mob_ne_zero hzH)).tendsto.comp hp)
    simpa only [Function.comp_def, mobInv_mob] using this
  have h2 : Tendsto (fun w => c.1 (c.2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 (c.1 z)) :=
    ((hc.differentiableOn_fwd.differentiableAt (c.dom.isOpen.mem_nhds hz)).continuousAt.tendsto).comp h1
  have h3 : Tendsto (fun w => c.1 (c.2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ) :=
    (tendsto_id.mono_left inf_le_left).congr'
      (eventually_inf_principal.2 (Eventually.of_forall fun w hw => (hc.2.2 w hw).symm))
  exact h2.not_tendsto (Metric.disjoint_nhds_cobounded _) h3


/-! ### The disc chart of the bounded image -/

/-- The disc chart of `mob '' dom`: `ζ ↦ mob (F (cayleyInv ζ))`, with the value `p` (the image of the
prime end at `∞`) at `1`. -/
def discMap (F : ℂ → ℂ) (p : ℂ) (ζ : ℂ) : ℂ := if ζ = 1 then p else mob (F (cayleyInv ζ))

theorem discMap_of_ne_one {F : ℂ → ℂ} {p ζ : ℂ} (h : ζ ≠ 1) :
    discMap F p ζ = mob (F (cayleyInv ζ)) := by simp only [discMap, h, ↓reduceIte]

theorem discMap_one (F : ℂ → ℂ) (p : ℂ) : discMap F p 1 = p := by simp only [discMap, ↓reduceIte]

theorem ne_one_of_mem_ball {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) : ζ ≠ 1 := by
  rintro rfl
  simp at hζ

theorem discMap_eqOn_ball {F : ℂ → ℂ} (hF : EqOn F c.2.1 H) (p : ℂ) :
    EqOn (discMap F p) (fun ζ => mob (c.2.1 (cayleyInv ζ))) (ball 0 1) := fun ζ hζ => by
  rw [discMap_of_ne_one (ne_one_of_mem_ball hζ), hF (QuantumZipper.CA.cayleyInv_mem_H hζ)]

theorem isConformalBijection_mob {O : Set ℂ} (hOH : O ⊆ H) : IsConformalBijection mob O (mob '' O) :=
  ⟨fun _ hz => (differentiableAt_mob (QuantumZipper.H_subset_Hbar (hOH hz))).differentiableWithinAt,
    mob_injective.injOn.bijOn_image⟩

theorem isConformalBijection_discMap (hc : c.IsConformal) {F : ℂ → ℂ} (hF : EqOn F c.2.1 H) (p : ℂ) :
    IsConformalBijection (discMap F p) (ball 0 1) (mob '' (c.dom : Set ℂ)) := by
  have h := isConformalBijection_comp (isConformalBijection_mob hc.dom_subset)
    (Aux2728Pocket.isConformalBijection_disc hc)
  exact ⟨h.1.congr (discMap_eqOn_ball hF p), h.2.congr (discMap_eqOn_ball hF p).symm⟩

/-- The disc chart is continuous on the closed disc. -/
theorem continuousOn_discMap (hc : c.IsConformal) {F : ℂ → ℂ} (hF : EqOn F c.2.1 H)
    (hFc : ContinuousOn F Hbar) {p : ℂ}
    (hp : Tendsto (fun w => mob (c.2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p)) :
    ContinuousOn (discMap F p) (closedBall 0 1) := by
  have hm : MapsTo cayleyInv (closedBall 0 1 \ {1}) Hbar := fun w hw =>
    QuantumZipper.CA.cayleyInv_mem_Hbar hw.1
  intro ζ hζ
  by_cases h1 : ζ = 1
  · subst h1
    rw [← continuousWithinAt_sdiff_self]
    have hG : ContinuousOn (fun w => mob (F w)) Hbar := fun w hw =>
      (continuousAt_mob (extension_mem_Hbar hc hF hFc hw)).comp_continuousWithinAt (hFc w hw)
    have hGlim : Tendsto (fun w => mob (F w)) (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 p) :=
      tendsto_cobounded_Hbar hG (hp.congr' (eventually_inf_principal.2
        (Eventually.of_forall fun w hw => by simp only [hF hw])))
    have hcay : Tendsto cayleyInv (𝓝[closedBall 0 1 \ {1}] 1) (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) :=
      tendsto_inf.2 ⟨QuantumZipper.CA.tendsto_cayleyInv_nhdsNE_one.mono_left
        (nhdsWithin_mono _ fun w hw => hw.2), tendsto_principal.2 (eventually_nhdsWithin_of_forall hm)⟩
    show Tendsto (discMap F p) (𝓝[closedBall 0 1 \ {1}] 1) (𝓝 (discMap F p 1))
    rw [discMap_one]
    exact (hGlim.comp hcay).congr' (eventually_nhdsWithin_of_forall fun w hw =>
      (discMap_of_ne_one hw.2).symm)
  · have hci : ContinuousWithinAt cayleyInv (closedBall 0 1 \ {1}) ζ :=
      ((QuantumZipper.CA.continuousOn_cayleyInv ζ h1).continuousAt
        (isOpen_ne.mem_nhds h1)).continuousWithinAt
    have hcont : ContinuousWithinAt (fun ζ => mob (F (cayleyInv ζ))) (closedBall 0 1 \ {1}) ζ :=
      (continuousAt_mob (extension_mem_Hbar hc hF hFc (hm ⟨hζ, h1⟩))).comp_continuousWithinAt
        (f := F ∘ cayleyInv) (x := ζ) ((hFc _ (hm ⟨hζ, h1⟩)).comp hci hm)
    have h2 : ContinuousWithinAt (discMap F p) (closedBall 0 1 \ {1}) ζ :=
      hcont.congr (fun w hw => discMap_of_ne_one hw.2) (discMap_of_ne_one h1)
    rwa [sdiff_eq, continuousWithinAt_inter (isOpen_compl_singleton.mem_nhds h1)] at h2


/-! ### The derivative argument of the transported chart -/

/-- `−1/w² = |w|⁻² e^{i(π − 2 arg w)}`. -/
theorem neg_inv_sq_eq {w : ℂ} (hw : w ≠ 0) :
    -(w ^ 2)⁻¹ = (((‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * exp (((π - 2 * arg w : ℝ) : ℂ) * I) := by
  have hr : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  have he : exp ((arg w : ℂ) * I) ≠ 0 := exp_ne_zero _
  have hexp : exp (((π - 2 * arg w : ℝ) : ℂ) * I) = -(exp ((arg w : ℂ) * I) ^ 2)⁻¹ := by
    have e1 : ((π - 2 * arg w : ℝ) : ℂ) * I = (π : ℂ) * I - ((arg w : ℂ) * I + (arg w : ℂ) * I) := by
      push_cast
      ring
    rw [e1, exp_sub, exp_add, Complex.exp_pi_mul_I]
    field_simp
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [hexp]
  push_cast
  field_simp

/-- The derivative argument of `c.1 ∘ mobInv` on `mob '' dom`. -/
theorem deriv_comp_mobInv (hc : c.IsConformal) {A : ℂ → ℝ}
    (hA : ∀ z ∈ c.dom, deriv c.1 z = ‖deriv c.1 z‖ * exp (A z * I)) :
    ∀ w ∈ mob '' (c.dom : Set ℂ), deriv (fun w => c.1 (mobInv w)) w =
      ‖deriv (fun w => c.1 (mobInv w)) w‖ * exp (((A (mobInv w) + (π - 2 * arg w) : ℝ) : ℂ) * I) := by
  rintro _ ⟨z, hz, rfl⟩
  have hw0 : mob z ≠ 0 := mob_ne_zero (QuantumZipper.H_subset_Hbar (hc.dom_subset hz))
  have h1 : DifferentiableAt ℂ c.1 (mobInv (mob z)) := by
    rw [mobInv_mob]
    exact hc.differentiableOn_fwd.differentiableAt (c.dom.isOpen.mem_nhds hz)
  have hd : deriv (fun w => c.1 (mobInv w)) (mob z) = deriv c.1 z * -((mob z) ^ 2)⁻¹ := by
    have := deriv_comp (mob z) h1 (differentiableAt_mobInv hw0)
    rw [deriv_mobInv, mobInv_mob] at this
    exact this
  set r : ℝ := ‖deriv c.1 z‖ * (‖mob z‖ ^ 2)⁻¹ with hrdef
  have hr : 0 ≤ r := by positivity
  have hform : deriv (fun w => c.1 (mobInv w)) (mob z) =
      (r : ℂ) * exp (((A (mobInv (mob z)) + (π - 2 * arg (mob z)) : ℝ) : ℂ) * I) := by
    rw [hd, hA z hz, neg_inv_sq_eq hw0, mobInv_mob, hrdef]
    push_cast
    rw [add_mul, exp_add]
    ring
  rw [hform, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, Complex.norm_exp_ofReal_mul_I,
    mul_one]


/-! ### Growth in the bounded coordinate -/

/-- Distances to the complement do not shrink under `mob^{-1}`: for `z ∈ O ⊆ ℍ`,
`dist(mob z, (mob '' O)ᶜ) ≤ dist(z, Oᶜ)`. -/
theorem infDist_mob_le {O : Set ℂ} (hOH : O ⊆ H) {z : ℂ} (hz : z ∈ O) :
    infDist (mob z) (mob '' O)ᶜ ≤ infDist z Oᶜ := by
  have hzH : z ∈ H := hOH hz
  have h0 : (0 : ℂ) ∈ Oᶜ := fun h => by
    have : (0 : ℝ) < (0 : ℂ).im := hOH h
    simp at this
  refine (le_infDist ⟨0, h0⟩).2 fun y hy => ?_
  have hmem : ∀ y' : ℂ, y' ∈ Hbar → y' ∉ O → infDist (mob z) (mob '' O)ᶜ ≤ dist z y' := by
    intro y' hy'H hy'O
    have hmy : mob y' ∈ (mob '' O)ᶜ := by
      rintro ⟨o, ho, he⟩
      exact hy'O (mob_injective he ▸ ho)
    calc infDist (mob z) (mob '' O)ᶜ ≤ dist (mob z) (mob y') := infDist_le_dist_of_mem hmy
      _ = ‖mob z - mob y'‖ := dist_eq_norm _ _
      _ ≤ ‖z - y'‖ := norm_mob_sub_le (QuantumZipper.H_subset_Hbar hzH) hy'H
      _ = dist z y' := (dist_eq_norm _ _).symm
  by_cases hyH : 0 ≤ y.im
  · exact hmem y hyH hy
  · replace hyH := not_le.1 hyH
    have hre : ((z.re : ℝ) : ℂ) ∈ Hbar := real_mem_Hbar z.re
    have hreO : ((z.re : ℝ) : ℂ) ∉ O := fun h => by
      have : (0 : ℝ) < ((z.re : ℝ) : ℂ).im := hOH h
      simp at this
    refine (hmem _ hre hreO).trans ?_
    have hz' : (0 : ℝ) < z.im := hzH
    have e1 : dist z ((z.re : ℝ) : ℂ) = z.im := by
      rw [dist_eq_norm]
      have : z - ((z.re : ℝ) : ℂ) = ((z.im : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz']
    rw [e1, dist_eq_norm]
    calc z.im ≤ |(z - y).im| := by
          rw [sub_im]
          exact (by linarith : z.im ≤ z.im - y.im).trans (le_abs_self _)
      _ ≤ ‖z - y‖ := Complex.abs_im_le_norm _

/-- **Logarithmic growth on `O ⊆ ℍ` gives subpower growth on `mob '' O`.** -/
theorem abs_le_comp_mobInv {O : Set ℂ} (hOo : IsOpen O) (hOH : O ⊆ H) {V : ℂ → ℝ} {K : ℝ}
    (hlog : ∀ z ∈ O, |V z| ≤ K * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Oᶜ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ w ∈ mob '' O, |V (mobInv w)| ≤ (max K 0 * (1 + 2 * Real.log 3) + 2 * max K 0 / ε) *
      (1 + infDist w (frontier (mob '' O)) ^ (-ε)) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mobInv_mob]
  set O' := mob '' O with hO'
  have hzH : z ∈ H := hOH hz
  have hzHb : z ∈ Hbar := QuantumZipper.H_subset_Hbar hzH
  have hO'o : IsOpen O' := isOpen_image_mob hOo hOH
  have hw : mob z ∈ O' := mem_image_of_mem _ hz
  have h0 : (0 : ℂ) ∈ O'ᶜ := by
    rintro ⟨o, ho, he⟩
    exact mob_ne_zero (QuantumZipper.H_subset_Hbar (hOH ho)) he
  have hneu : O' ≠ univ := fun h => h0 (h ▸ mem_univ _)
  set d := infDist (mob z) O'ᶜ with hd
  have hdf : infDist (mob z) (frontier O') = d :=
    le_antisymm (Sec6.infDist_frontier_le_infDist_compl hO'o ⟨0, h0⟩ hw)
      (Sec6.infDist_compl_le_infDist_frontier hO'o ⟨_, hw⟩ hneu _)
  rw [hdf]
  have hdpos : 0 < d :=
    (IsClosed.notMem_iff_infDist_pos hO'o.isClosed_compl ⟨0, h0⟩).1 (fun h => h hw)
  have hdw : d ≤ ‖mob z‖ := by
    have := infDist_le_dist_of_mem (x := mob z) h0
    rwa [dist_zero_right] at this
  have hw1 : ‖mob z‖ ≤ 1 := norm_mob_le_one hzHb
  have hd1 : d ≤ 1 := hdw.trans hw1
  have hwpos : 0 < ‖mob z‖ := hdpos.trans_le hdw
  -- `‖z‖ ≤ 1/d + 1`
  have hz1 : ‖z‖ ≤ 1 / d + 1 := by
    have e : z = (mob z)⁻¹ - I := by simp [mob]
    calc ‖z‖ = ‖(mob z)⁻¹ - I‖ := by rw [← e]
      _ ≤ ‖(mob z)⁻¹‖ + ‖I‖ := norm_sub_le _ _
      _ = ‖mob z‖⁻¹ + 1 := by rw [norm_inv, Complex.norm_I]
      _ ≤ 1 / d + 1 := by
          rw [one_div]
          exact add_le_add_left (inv_anti₀ hdpos hdw) _
  -- `1 / dist(z, Oᶜ) ≤ 1 / d`
  have hdz : d ≤ infDist z Oᶜ := infDist_mob_le hOH hz
  have hiz : 1 / infDist z Oᶜ ≤ 1 / d := one_div_le_one_div_of_le hdpos hdz
  set L := Real.log (2 + 1 / d) with hL
  have hpos1 : 0 < 1 / d := one_div_pos.2 hdpos
  have hL1 : Real.log (1 + ‖z‖) ≤ L :=
    Real.log_le_log (by positivity) (by linarith)
  have hL2 : Real.log (1 + 1 / infDist z Oᶜ) ≤ L := by
    have hnn : 0 ≤ 1 / infDist z Oᶜ := one_div_nonneg.2 infDist_nonneg
    exact Real.log_le_log (by positivity) (by linarith)
  have hL0 : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  have hL0' : 0 ≤ Real.log (1 + 1 / infDist z Oᶜ) :=
    Real.log_nonneg (by linarith [one_div_nonneg.2 (infDist_nonneg (x := z) (s := Oᶜ))])
  -- `L ≤ log 3 + d^{-ε}/ε`
  have hpow : 0 ≤ d ^ (-ε) := Real.rpow_nonneg hdpos.le _
  have hLb : L ≤ Real.log 3 + d ^ (-ε) / ε := by
    have h3 : 2 + 1 / d ≤ 3 * d⁻¹ := by
      rw [one_div]
      have : 1 ≤ d⁻¹ := one_le_inv₀ hdpos |>.2 hd1
      linarith
    have hlog3 : Real.log (3 * d⁻¹) = Real.log 3 + Real.log d⁻¹ :=
      Real.log_mul (by norm_num) (inv_ne_zero hdpos.ne')
    have hinv : Real.log d⁻¹ ≤ d ^ (-ε) / ε := by
      have := Real.log_le_rpow_div (inv_nonneg.2 hdpos.le) hε
      rwa [Real.inv_rpow hdpos.le, ← Real.rpow_neg hdpos.le] at this
    calc L ≤ Real.log (3 * d⁻¹) := Real.log_le_log (by positivity) h3
      _ = Real.log 3 + Real.log d⁻¹ := hlog3
      _ ≤ Real.log 3 + d ^ (-ε) / ε := by linarith
  have hK : 0 ≤ max K 0 := le_max_right _ _
  have hbr : 0 ≤ 1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Oᶜ) := by linarith
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc |V z| ≤ K * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Oᶜ)) := hlog z hz
    _ ≤ max K 0 * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Oᶜ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hbr
    _ ≤ max K 0 * (1 + 2 * (Real.log 3 + d ^ (-ε) / ε)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
    _ = max K 0 * (1 + 2 * Real.log 3) + 2 * max K 0 / ε * d ^ (-ε) := by ring
    _ ≤ (max K 0 * (1 + 2 * Real.log 3) + 2 * max K 0 / ε) * (1 + d ^ (-ε)) := by
        have h1 : 0 ≤ max K 0 * (1 + 2 * Real.log 3) := by positivity
        have h2 : 0 ≤ 2 * max K 0 / ε := by positivity
        nlinarith


/-! ### Aux. lemma 29 through the bounded coordinate -/

/-- The argument correction of `mobInv`: `π − 2 arg w`, a branch of `arg (mobInv)′`. -/
def argCorr (w : ℂ) : ℝ := π - 2 * arg w

theorem harmonicOnNhd_argCorr {O' : Set ℂ} (hO' : O' ⊆ {w | w.im < 0}) :
    InnerProductSpace.HarmonicOnNhd argCorr O' := by
  intro w hw
  have hslit : w ∈ slitPlane := Or.inr (hO' hw).ne
  have harg : InnerProductSpace.HarmonicAt (fun w : ℂ => arg w) w := by
    have := (analyticAt_id.clog hslit).harmonicAt_im
    simpa only [Complex.log_im, id] using this
  have h := (InnerProductSpace.harmonicAt_const (π : ℝ)).sub (harg.const_smul (c := (2 : ℝ)))
  convert h using 1
  ext w'
  simp only [argCorr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem continuousOn_argCorr {O' : Set ℂ} (hO' : O' ⊆ {w | w.im < 0}) : ContinuousOn argCorr O' := by
  intro w hw
  exact (continuousAt_const.sub
    (continuousAt_const.mul (Complex.continuousAt_arg (Or.inr (hO' hw).ne)))).continuousWithinAt

theorem abs_argCorr_le (w : ℂ) : |argCorr w| ≤ 3 * π := by
  have h := Complex.abs_arg_le_pi w
  rw [argCorr, abs_le]
  have h1 := abs_le.1 h
  constructor <;> linarith [Real.pi_pos]

theorem isConformalBijection_mobInv {O : Set ℂ} (hOH : O ⊆ H) :
    IsConformalBijection mobInv (mob '' O) O := by
  refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hw
    exact (differentiableAt_mobInv (mob_ne_zero (QuantumZipper.H_subset_Hbar (hOH hz)))).differentiableWithinAt
  · rintro _ ⟨z, hz, rfl⟩
    rwa [mobInv_mob]
  · intro w₁ _ w₂ _ h
    rw [← mob_mobInv w₁, h, mob_mobInv]
  · intro z hz
    exact ⟨mob z, mem_image_of_mem _ hz, mobInv_mob z⟩

/-- **Aux. lemma 29 for a conformal chart, through the bounded coordinate** `mob` (specification
p. 164 and its use in the full stopped Gaussian kernel, p. 475; "use the fixed conformal
compactification of the ambient domain", p. 199). Let `c` be a conformal chart whose inverse extends
continuously to `ℍ̄` (`F`) and has a limit at `∞` after `mob` (`p`). Let `V` be harmonic on the chart
domain with logarithmic growth, and `A` a continuous argument of `c.1′`. Fix a finite set `X` of
physical points. If at every real chart point `x` off the jump set whose physical landing `F x` avoids
`X`, the landings of the jump points and the landing at `∞`, the corrected mean `V + χ A` has the phase
word's boundary value, then `V = phaseWordExt ∘ c.1 − χ A` on the whole domain. Every prime end over
the finitely many exceptional physical points is excluded; their number of prime ends is not
assumed finite. -/
theorem eqOn_phaseWordExt_of_landing_germs {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} (hL : vL 0 ≤ 0) (hR : 0 ≤ vR 0) (d : ℝ)
    (hc : c.IsConformal) {F : ℂ → ℂ} (hF : EqOn F c.2.1 H) (hFc : ContinuousOn F Hbar)
    {p : ℂ} (hp : Tendsto (fun w => mob (c.2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p))
    {V : ℂ → ℝ} (hV : InnerProductSpace.HarmonicOnNhd V c.dom) {K : ℝ}
    (hlog : ∀ z ∈ (c.dom : Set ℂ),
      |V z| ≤ K * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z (c.dom : Set ℂ)ᶜ)))
    {A : ℂ → ℝ} (hAc : ContinuousOn A (c.dom : Set ℂ))
    (hA : ∀ z ∈ c.dom, deriv c.1 z = ‖deriv c.1 z‖ * exp (A z * I))
    {X : Set ℂ} (hX : X.Finite)
    (hIncident : ∀ x : ℝ, x ∉ forceJumpSet vL vR → F x ∉ X →
      (∀ y ∈ forceJumpSet vL vR, F x ≠ F y) → mob (F x) ≠ p →
      Tendsto (fun y => V (c.2.1 y) + chiC κ * A (c.2.1 y)) (𝓝[H] (x : ℂ))
        (𝓝 (phaseData κ ρL ρR vL vR d x))) :
    ∀ z ∈ (c.dom : Set ℂ), V z = phaseWordExt κ ρL ρR vL vR d (c.1 z) - chiC κ * A z := by
  set O : Set ℂ := (c.dom : Set ℂ) with hOdef
  set O' : Set ℂ := mob '' O with hO'def
  have hOo : IsOpen O := c.dom.isOpen
  have hOH : O ⊆ H := hc.dom_subset
  have hO'o : IsOpen O' := isOpen_image_mob hOo hOH
  have hO'low : O' ⊆ {w | w.im < 0} := image_mob_subset_lower hOH
  set J : Set ℝ := forceJumpSet vL vR with hJ
  have hJf : J.Finite := by
    rw [hJ]
    unfold forceJumpSet
    exact (((finite_range vL).union (finite_range vR)).insert 0)
  set P' : Set ℂ := (mob '' (X ∪ (fun y : ℝ => F y) '' J) ∪ {p}) ∩ frontier O' with hP'
  have hP'f : P'.Finite :=
    (((hX.union (hJf.image _)).image mob).union (finite_singleton p)).inter_of_left _
  -- the transported objects
  set V' : ℂ → ℝ := fun w => V (mobInv w) - chiC κ * argCorr w with hV'
  set φ' : ℂ → ℂ := fun w => c.1 (mobInv w) with hφ'
  set A' : ℂ → ℝ := fun w => A (mobInv w) + argCorr w with hA'
  have hmapsInv : MapsTo mobInv O' O := (isConformalBijection_mobInv hOH).2.mapsTo
  have hdiffInv : DifferentiableOn ℂ mobInv O' := (isConformalBijection_mobInv hOH).1
  have hV'h : InnerProductSpace.HarmonicOnNhd V' O' := by
    have h1 : InnerProductSpace.HarmonicOnNhd (V ∘ mobInv) O' :=
      LQGMetric.harmonicOnNhd_comp_holo hOo hO'o hV hdiffInv hmapsInv
    have h := h1.sub ((harmonicOnNhd_argCorr hO'low).const_smul (c := chiC κ))
    convert h using 1
    ext w
    simp only [hV', Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hSub : ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ w ∈ O',
      |V' w| ≤ Cε * (1 + infDist w (frontier O') ^ (-ε)) := by
    intro ε hε
    set C₀ := max K 0 * (1 + 2 * Real.log 3) + 2 * max K 0 / ε
    refine ⟨C₀ + |chiC κ| * (3 * π), fun w hw => ?_⟩
    have h1 := abs_le_comp_mobInv hOo hOH hlog hε w hw
    have hβ := abs_argCorr_le w
    have ht : 0 ≤ infDist w (frontier O') ^ (-ε) := Real.rpow_nonneg infDist_nonneg _
    have hχ : 0 ≤ |chiC κ| := abs_nonneg _
    calc |V' w| ≤ |V (mobInv w)| + |chiC κ| * |argCorr w| := by
          simp only [hV']
          rw [← abs_mul]
          exact abs_sub _ _
      _ ≤ C₀ * (1 + infDist w (frontier O') ^ (-ε)) + |chiC κ| * (3 * π) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left hβ hχ)
      _ ≤ (C₀ + |chiC κ| * (3 * π)) * (1 + infDist w (frontier O') ^ (-ε)) := by
          have : 0 ≤ |chiC κ| * (3 * π) := by positivity
          nlinarith
  have hφ'c : IsConformalBijection φ' O' H :=
    isConformalBijection_comp (Aux2728Pocket.isConformalBijection_fwd hc) (isConformalBijection_mobInv hOH)
  have hA'c : ContinuousOn A' O' :=
    (hAc.comp (hdiffInv.continuousOn) hmapsInv).add (continuousOn_argCorr hO'low)
  have hA'd : ∀ w ∈ O', deriv φ' w = ‖deriv φ' w‖ * exp (A' w * I) := by
    intro w hw
    have := deriv_comp_mobInv hc hA w hw
    simpa only [hφ', hA', argCorr] using this
  have hInc : ∀ q ∈ sphere (0 : ℂ) 1, discMap F p q ∉ P' →
      ∃ x : ℝ, x ∉ J ∧ Tendsto (fun ζ => φ' (discMap F p ζ)) (𝓝[ball 0 1] q) (𝓝[H] (x : ℂ)) ∧
        Tendsto (fun ζ => V' (discMap F p ζ) + chiC κ * A' (discMap F p ζ))
          (𝓝[ball 0 1] q) (𝓝 (phaseData κ ρL ρR vL vR d x)) := by
    intro q hq hqP
    by_cases hq1 : q = 1
    · subst hq1
      exact absurd ⟨Or.inr (by rw [discMap_one]; rfl), by rw [discMap_one]; exact limit_mem_frontier hc hp⟩
        hqP
    obtain ⟨hre, hlim⟩ := Lemma71M.cayleyInv_boundary hq hq1
    set x : ℝ := (QuantumZipper.CA.cayleyInv q).re with hx
    have hdq : discMap F p q = mob (F x) := by rw [discMap_of_ne_one hq1, ← hre]
    have hfr : discMap F p q ∈ frontier O' := by
      rw [hdq]
      exact mob_mem_frontier hOo hOH (extension_real_mem_frontier hc hF hFc x)
    have hnot : discMap F p q ∉ mob '' (X ∪ (fun y : ℝ => F y) '' J) ∪ {p} := fun h => hqP ⟨h, hfr⟩
    rw [hdq] at hnot
    have hxX : F x ∉ X := fun h => hnot (Or.inl (mem_image_of_mem _ (Or.inl h)))
    have hxJ' : ∀ y ∈ J, F x ≠ F y := fun y hy h =>
      hnot (Or.inl (mem_image_of_mem _ (Or.inr ⟨y, hy, h.symm⟩)))
    have hxJ : x ∉ J := fun h => hxJ' x h rfl
    have hxp : mob (F x) ≠ p := fun h => hnot (Or.inr h)
    have hside := hIncident x hxJ hxX hxJ' hxp
    rw [← hre] at hlim
    have hball : ∀ ζ ∈ ball (0 : ℂ) 1, discMap F p ζ = mob (c.2.1 (cayleyInv ζ)) :=
      fun ζ hζ => discMap_eqOn_ball hF p hζ
    refine ⟨x, hxJ, ?_, ?_⟩
    · refine hlim.congr' (eventually_nhdsWithin_of_forall fun ζ hζ => ?_)
      show _ = φ' (discMap F p ζ)
      rw [hball ζ hζ]
      simp only [hφ', mobInv_mob]
      exact (hc.2.2 _ (QuantumZipper.CA.cayleyInv_mem_H hζ)).symm
    · refine ((hside.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hlim.mono_right nhdsWithin_le_nhds) (hlim.eventually self_mem_nhdsWithin)) :)).congr'
        (eventually_nhdsWithin_of_forall fun ζ hζ => ?_)
      show _ = V' (discMap F p ζ) + chiC κ * A' (discMap F p ζ)
      rw [hball ζ hζ]
      simp only [Function.comp_apply, hV', hA', mobInv_mob]
      ring
  have key := PocketStopSide.mean_eq_phaseWordExt_of_incident_germs hκ ρL ρR hL hR d hO'o
    (isConformalBijection_discMap hc hF p) (continuousOn_discMap hc hF hFc hp) hP'f
    inter_subset_right hV'h hSub hφ'c hA'c hA'd hInc
  intro z hz
  have h := key (mob z) (mem_image_of_mem _ hz)
  simp only [hV', hφ', hA', mobInv_mob] at h
  linarith

end InteractingSLE.Sec7.Aux29Cor
