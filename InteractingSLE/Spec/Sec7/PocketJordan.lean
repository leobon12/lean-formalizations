/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71FBdry
import InteractingSLE.Spec.Sec6.Aux41Full
import InteractingSLE.WangWu.UnboundedComponent

/-!
# A pocket in the counterflow chart and its Jordan coordinate

Packet PROVE-STRIPSYS17 (specification §7.4.1, proof of Lemma 7.25, p. 414: "The erased counterflow is therefore a
complete continuous traversal of this actual Jordan pocket"; Aux. lemma 125, p. 395: "let `ψ : C → ℍ` send the
counterflow entry to zero and its terminal pocket endpoint to infinity"; Aux. lemma 120, p. 387: `ψ = m ∘ φ`,
`m(z) = −1/z`).

The selected pocket `C` of Aux. lemma 130 lives in the flow chart (flow seed `0`, flow target `∞`); its compactified
picture is the Cayley image `D = cayley(C)` in the unit disc, whose frontier is the Jordan curve made of the two
selected arcs, with marked points `p = cayley(x₀)` (the opening contact, the counterflow's terminal pocket endpoint)
and `q = cayley(y₀)` (the closing contact, the counterflow entry; `q = 1` when `y₀` is the flow target `∞`). The
counterflow is a Loewner trace from `0` in the chart `m(z) = −1/z` (`StripSysPath`: "the curve `R(η')` of the
frozen docstring is `−1/η'`"), so the pocket it traverses is `C' = m(C)` and Aux. lemma 41 asks for a Jordan
coordinate of `C'` with `m(x₀) ↦ ∞` and `m(y₀) ↦ 0` (`Sec6.IsJordanCoord`).

In the compactified picture `m` is the half-turn: `cayley(m z) = −cayley z` (`cayley_negInv`). Hence a two-point
uniformizer `Ψ` of `D` (`p ↦ 0`, `q ↦ ∞`, with its Jordan boundary extension, `Lemma71F.exists_twoPoint_…_ext`)
gives the Jordan coordinate `ψ' = m ∘ (a Ψ) ∘ (−cayley)` of `C'` (`cfCoord`), for every scale `a > 0`, with the value
`0` at `m(y₀)` (`isJordanCoord_cfCoord`). The case `y₀ = ∞` (`q = 1`, `m(y₀) = 0`) needs no separate treatment.

## Main results

* `cfPt w = cayleyInv (−w)`: the counterflow-chart point of a disc point (`cfPt (cayley z) = m z`, `cfPt 1 = 0`);
* `cayley_negInv`, `cfPt_neg_cayley`, `neg_cayley_cfPt`: the half-turn identities;
* `image_negInv_eq`: `m(C) = cfPt(cayley(C))`;
* `IsConformalBijection.im_eq_zero_of_mem_frontier`: a two-point uniformizer with a Jordan boundary extension is real
  on the frontier;
* **`isJordanCoord_cfCoord`**: the Jordan coordinate of `m(C)`;
* `isOpen_image_negInv'`, `isConnected_image_negInv`, `isBounded_image_negInv`, **`frontier_image_negInv`**: the
  topology of `m(C)` (bounded when the opening contact is not the flow seed; frontier `cfPt(∂D)`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)

namespace InteractingSLE.Sec7.PocketJordan

/-! ### The half-turn in the compactified picture -/

/-- The counterflow-chart point `cayleyInv (−w)` of a point `w` of the closed disc (`m(cayleyInv w)`). -/
def cfPt (w : ℂ) : ℂ := cayleyInv (-w)

theorem mem_Hbar_iff {z : ℂ} : z ∈ Hbar ↔ 0 ≤ z.im := Iff.rfl

theorem mem_H_iff {z : ℂ} : z ∈ H ↔ 0 < z.im := Iff.rfl

theorem add_I_ne_zero_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : z + I ≠ 0 :=
  QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hz

theorem negInv_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : negInv z ∈ Hbar := by
  show 0 ≤ (negInv z).im
  rw [WangWu.negInv, neg_im, inv_im, neg_div, neg_neg]
  exact div_nonneg hz (normSq_nonneg z)

theorem negInv_eq_zero_iff {z : ℂ} : negInv z = 0 ↔ z = 0 := by
  simp [WangWu.negInv]

theorem im_negInv_eq_zero {z : ℂ} (hz : z.im = 0) : (negInv z).im = 0 := by
  rw [WangWu.negInv, neg_im, inv_im, hz, neg_zero, zero_div, neg_zero]

/-- **The half-turn**: `cayley (−1/z) = −cayley z` for `z ≠ 0` in the closed half-plane. -/
theorem cayley_negInv {z : ℂ} (hz : z ∈ Hbar) (hz0 : z ≠ 0) : cayley (negInv z) = -cayley z := by
  have hzI : z + I ≠ 0 := add_I_ne_zero_of_mem_Hbar hz
  have hmI : negInv z + I ≠ 0 := add_I_ne_zero_of_mem_Hbar (negInv_mem_Hbar hz)
  have key : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
  simp only [QuantumZipper.CA.cayley, WangWu.negInv] at hmI ⊢
  rw [neg_div', div_eq_div_iff hmI hzI]
  linear_combination (-2) * key + (-2) * Complex.I_sq

/-- The counterflow point of `−cayley z` is `z` (closed half-plane). -/
theorem cfPt_neg_cayley {z : ℂ} (hz : z ∈ Hbar) : cfPt (-cayley z) = z := by
  rw [cfPt, neg_neg]
  exact QuantumZipper.CA.cayleyInv_cayley (add_I_ne_zero_of_mem_Hbar hz)

/-- `−cayley` of the counterflow point of `w ≠ −1` is `w`. -/
theorem neg_cayley_cfPt {w : ℂ} (hw : w ≠ -1) : -cayley (cfPt w) = w := by
  have hw' : -w ≠ 1 := fun h => hw (by rw [← neg_neg w, h])
  rw [cfPt, QuantumZipper.CA.cayley_cayleyInv hw', neg_neg]

/-- The counterflow point of a Cayley image is the inversion: `cfPt (cayley z) = −1/z` (`z ≠ 0`, closed half-plane). -/
theorem cfPt_cayley {z : ℂ} (hz : z ∈ Hbar) (hz0 : z ≠ 0) : cfPt (cayley z) = negInv z := by
  have h := cfPt_neg_cayley (negInv_mem_Hbar hz)
  rwa [cayley_negInv hz hz0, neg_neg] at h

theorem cfPt_one : cfPt 1 = 0 := by
  simp [cfPt, QuantumZipper.CA.cayleyInv]

theorem cfPt_mem_H {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : cfPt w ∈ H :=
  QuantumZipper.CA.cayleyInv_mem_H (by rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff])

theorem cfPt_mem_Hbar {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) : cfPt w ∈ Hbar :=
  QuantumZipper.CA.cayleyInv_mem_Hbar (by rwa [mem_closedBall_zero_iff, norm_neg, ← mem_closedBall_zero_iff])

theorem continuousAt_cfPt {w : ℂ} (hw : w ≠ -1) : ContinuousAt cfPt w := by
  have hw' : -w ≠ 1 := fun h => hw (by rw [← neg_neg w, h])
  exact (QuantumZipper.CA.differentiableAt_cayleyInv hw').continuousAt.comp continuous_neg.continuousAt

theorem continuousOn_cfPt : ContinuousOn cfPt {w | w ≠ -1} := fun _ hw =>
  (continuousAt_cfPt hw).continuousWithinAt

theorem injOn_cfPt : InjOn cfPt {w | w ≠ -1} := fun w hw w' hw' h => by
  rw [← neg_cayley_cfPt hw, ← neg_cayley_cfPt hw', h]

theorem continuousAt_neg_cayley {z : ℂ} (hz : z ∈ Hbar) : ContinuousAt (fun z => -cayley z) z :=
  (QuantumZipper.CA.differentiableAt_cayley (add_I_ne_zero_of_mem_Hbar hz)).continuousAt.neg

theorem continuousOn_neg_cayley : ContinuousOn (fun z => -cayley z) Hbar := fun _ hz =>
  (continuousAt_neg_cayley hz).continuousWithinAt

theorem injOn_neg_cayley : InjOn (fun z => -cayley z) Hbar := fun z hz z' hz' h => by
  rw [← cfPt_neg_cayley hz, ← cfPt_neg_cayley hz']
  exact congrArg cfPt h

/-! ### The inverted pocket -/

section Image

variable {C : Set ℂ}

theorem ne_zero_of_mem_H {z : ℂ} (hz : z ∈ H) : z ≠ 0 := WangWu.ne_zero_of_mem_H hz

theorem H_subset_Hbar' {z : ℂ} (hz : z ∈ H) : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hz)

/-- The inverted pocket is the counterflow image of the Cayley image: `m(C) = cfPt(cayley(C))`. -/
theorem image_negInv_eq (hCH : C ⊆ H) : negInv '' C = cfPt '' (cayley '' C) := by
  rw [image_image]
  refine image_congr fun z hz => ?_
  exact (cfPt_cayley (H_subset_Hbar' (hCH hz)) (ne_zero_of_mem_H (hCH hz))).symm

theorem image_negInv_subset_H (hCH : C ⊆ H) : negInv '' C ⊆ H := WangWu.image_negInv_subset_H hCH

/-- `−cayley` maps the inverted pocket onto the Cayley image. -/
theorem image_neg_cayley_image_negInv (hCH : C ⊆ H) :
    (fun z => -cayley z) '' (negInv '' C) = cayley '' C := by
  rw [image_image]
  refine image_congr fun z hz => ?_
  rw [cayley_negInv (H_subset_Hbar' (hCH hz)) (ne_zero_of_mem_H (hCH hz)), neg_neg]

theorem closure_image_negInv_subset_Hbar (hCH : C ⊆ H) : closure (negInv '' C) ⊆ Hbar :=
  closure_minimal (fun _ hz => H_subset_Hbar' (image_negInv_subset_H hCH hz))
    (isClosed_le continuous_const Complex.continuous_im)

/-- `−cayley` maps the closure of the inverted pocket into the closure of the Cayley image. -/
theorem neg_cayley_mem_closure (hCH : C ⊆ H) {z : ℂ} (hz : z ∈ closure (negInv '' C)) :
    -cayley z ∈ closure (cayley '' C) := by
  have hzH := closure_image_negInv_subset_Hbar hCH hz
  have := (continuousAt_neg_cayley hzH).continuousWithinAt.mem_closure_image hz
  rwa [image_neg_cayley_image_negInv hCH] at this

theorem isOpen_image_negInv' (hCo : IsOpen C) (hCH : C ⊆ H) : IsOpen (negInv '' C) :=
  WangWu.isOpen_image_negInv hCo hCH

theorem isConnected_image_negInv (hCc : IsConnected C) (hCH : C ⊆ H) : IsConnected (negInv '' C) :=
  hCc.image _ (WangWu.continuousOn_negInv.mono hCH)

/-- `−cayley` maps a frontier point of the inverted pocket to a frontier point of the Cayley image. -/
theorem neg_cayley_mem_frontier (hCo : IsOpen C) (hCH : C ⊆ H) {z : ℂ} (hz : z ∈ frontier (negInv '' C)) :
    -cayley z ∈ frontier (cayley '' C) := by
  have hzc := frontier_subset_closure hz
  have hzH := closure_image_negInv_subset_Hbar hCH hzc
  rw [(Lemma71F.isOpen_cayley_image hCo hCH).frontier_eq]
  refine ⟨neg_cayley_mem_closure hCH hzc, fun hD => ?_⟩
  have : z ∈ negInv '' C := by
    rw [image_negInv_eq hCH, ← cfPt_neg_cayley hzH]
    exact mem_image_of_mem _ hD
  rw [(isOpen_image_negInv' hCo hCH).frontier_eq] at hz
  exact hz.2 this

/-- **The frontier of the inverted pocket** is the counterflow image of the frontier of the Cayley image, when the
latter avoids `−1` (the image of the flow seed). -/
theorem frontier_image_negInv (hCo : IsOpen C) (hCH : C ⊆ H) (h1 : (-1 : ℂ) ∉ frontier (cayley '' C)) :
    frontier (negInv '' C) = cfPt '' frontier (cayley '' C) := by
  ext z
  constructor
  · intro hz
    have hzH := closure_image_negInv_subset_Hbar hCH (frontier_subset_closure hz)
    exact ⟨_, neg_cayley_mem_frontier hCo hCH hz, cfPt_neg_cayley hzH⟩
  · rintro ⟨w, hw, rfl⟩
    have hw1 : w ≠ -1 := fun h => h1 (h ▸ hw)
    have hDo := Lemma71F.isOpen_cayley_image hCo hCH
    rw [hDo.frontier_eq] at hw
    rw [(isOpen_image_negInv' hCo hCH).frontier_eq]
    refine ⟨?_, fun hmem => ?_⟩
    · have := (continuousAt_cfPt hw1).continuousWithinAt.mem_closure_image hw.1
      rwa [← image_negInv_eq hCH] at this
    · rw [image_negInv_eq hCH] at hmem
      obtain ⟨w', hw', hww'⟩ := hmem
      have hw'1 : w' ≠ -1 := fun h => by
        rw [h] at hw'
        exact (Lemma71F.ne_one_of_mem_ball (by
          have := Lemma71F.cayley_image_subset_ball hCH hw'
          rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff] at this)) rfl
      have : w' = w := by rw [← neg_cayley_cfPt hw'1, ← neg_cayley_cfPt hw1, hww']
      exact hw.2 (this ▸ hw')

/-- **The inverted pocket is bounded** when the flow seed `0` is not adherent to the pocket. -/
theorem isBounded_image_negInv (h0 : (0 : ℂ) ∉ closure C) : IsBounded (negInv '' C) := by
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ball (0 : ℂ) δ ∩ C = ∅ := by
    rw [mem_closure_iff_nhds] at h0
    push Not at h0
    obtain ⟨U, hU, hUC⟩ := h0
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
    refine ⟨δ, hδ, eq_empty_of_forall_notMem fun z hz => ?_⟩
    have : (U ∩ C).Nonempty := ⟨z, hδU hz.1, hz.2⟩
    rw [hUC] at this
    exact this.ne_empty rfl
  refine isBounded_iff_forall_norm_le.2 ⟨δ⁻¹, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [WangWu.norm_negInv]
  have hzδ : δ ≤ ‖z‖ := by
    by_contra h
    push Not at h
    have : z ∈ ball (0 : ℂ) δ ∩ C := ⟨mem_ball_zero_iff.2 h, hz⟩
    rw [hball] at this
    exact this
  exact inv_anti₀ hδ hzδ

/-- The flow seed is not adherent to the pocket when `−1` is not on the frontier of its Cayley image. -/
theorem zero_notMem_closure (hCo : IsOpen C) (hCH : C ⊆ H) (h1 : (-1 : ℂ) ∉ frontier (cayley '' C)) :
    (0 : ℂ) ∉ closure C := by
  intro h0
  have h0f : (0 : ℂ) ∈ frontier C := by
    rw [hCo.frontier_eq]
    exact ⟨h0, fun h => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hCH h)⟩
  have := Lemma71F.cayley_mem_frontier hCo hCH h0f
  rw [show cayley 0 = -1 by simp [QuantumZipper.CA.cayley]] at this
  exact h1 this

end Image

/-! ### The Jordan coordinate in the counterflow chart -/

section Coord

/-- **A two-point uniformizer with its Jordan boundary extension** (the conclusion of
`Lemma71F.exists_twoPoint_uniformizer_ext_of_jordan`): a conformal bijection `Ψ : D → ℍ`, continuous, injective and
`ℍ̄`-valued on `closure D \ {q}`, with `Ψ p = 0` and `|Ψ| → ∞` at `q`. -/
structure IsBdryUniformizer (D : Set ℂ) (p q : ℂ) (Ψ : ℂ → ℂ) : Prop where
  conf : IsConformalBijection Ψ D H
  cont : ContinuousOn Ψ (closure D \ {q})
  inj : InjOn Ψ (closure D \ {q})
  mapsTo : MapsTo Ψ (closure D \ {q}) Hbar
  zero : Ψ p = 0
  tendsto : Tendsto (fun w => ‖Ψ w‖) (𝓝[closure D \ {q}] q) atTop

/-- A bounded Jordan domain has a two-point uniformizer with its boundary extension (`Lemma71F`). -/
theorem exists_isBdryUniformizer {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D) (hDb : IsBounded D)
    (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier D)) {p q : ℂ} (hp : p ∈ frontier D) (hq : q ∈ frontier D)
    (hpq : p ≠ q) : ∃ Ψ : ℂ → ℂ, IsBdryUniformizer D p q Ψ := by
  obtain ⟨Ψ, h1, h2, h3, h4, h5, h6⟩ :=
    Lemma71F.exists_twoPoint_uniformizer_ext_of_jordan hDo hDc hDb hJ hp hq hpq
  exact ⟨Ψ, ⟨h1, h2, h3, h4, h5, h6⟩⟩

variable {D : Set ℂ} {p q : ℂ} {Ψ : ℂ → ℂ}

namespace IsBdryUniformizer

/-- `Ψ` vanishes only at `p`. -/
theorem ne_zero (hU : IsBdryUniformizer D p q Ψ) (hp : p ∈ closure D) (hpq : p ≠ q) {w : ℂ}
    (hw : w ∈ closure D \ {q}) (hwp : w ≠ p) : Ψ w ≠ 0 := fun h =>
  hwp (hU.inj hw ⟨hp, hpq⟩ (h.trans hU.zero.symm))

/-- **The uniformizer is real on the frontier** (away from `q`). -/
theorem im_eq_zero (hU : IsBdryUniformizer D p q Ψ) (hDo : IsOpen D) (hqD : q ∉ D) {w : ℂ}
    (hw : w ∈ frontier D) (hwq : w ≠ q) : (Ψ w).im = 0 := by
  rw [hDo.frontier_eq] at hw
  refine le_antisymm (not_lt.1 fun hpos => hw.2 ?_) (hU.mapsTo ⟨hw.1, hwq⟩)
  obtain ⟨w', hw', he⟩ := hU.conf.2.surjOn (show Ψ w ∈ H from hpos)
  have hw'q : w' ≠ q := fun h => hqD (h ▸ hw')
  rw [← hU.inj ⟨subset_closure hw', hw'q⟩ ⟨hw.1, hwq⟩ he]
  exact hw'

end IsBdryUniformizer

/-- The coordinate on the closed Cayley image: `m(a Ψ w)`, with the value `0` at `q`. -/
def cfMap (a : ℝ) (Ψ : ℂ → ℂ) (q : ℂ) (w : ℂ) : ℂ :=
  open scoped Classical in if w = q then 0 else negInv ((a : ℂ) * Ψ w)

/-- **The Jordan coordinate in the counterflow chart**: `z ↦ m(a Ψ(−cayley z))`, `0` where `−cayley z = q`. -/
def cfCoord (a : ℝ) (Ψ : ℂ → ℂ) (q : ℂ) (z : ℂ) : ℂ := cfMap a Ψ q (-cayley z)

theorem cfMap_self (a : ℝ) (Ψ : ℂ → ℂ) (q : ℂ) : cfMap a Ψ q q = 0 := by simp [cfMap]

theorem cfMap_of_ne {a : ℝ} {w : ℂ} (hw : w ≠ q) : cfMap a Ψ q w = negInv ((a : ℂ) * Ψ w) := by
  simp [cfMap, hw]

theorem norm_cfMap_of_ne {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : w ≠ q) : ‖cfMap a Ψ q w‖ = (a * ‖Ψ w‖)⁻¹ := by
  rw [cfMap_of_ne hw, WangWu.norm_negInv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

theorem im_ofReal_mul (a : ℝ) (x : ℂ) : ((a : ℂ) * x).im = a * x.im := by
  simp [Complex.mul_im]

theorem continuousAt_negInv {x : ℂ} (hx : x ≠ 0) : ContinuousAt negInv x := by
  show ContinuousAt (fun z : ℂ => -z⁻¹) x
  exact (continuousAt_inv₀ hx).neg

theorem continuousOn_cfMap (hU : IsBdryUniformizer D p q Ψ) {a : ℝ} (ha : 0 < a) (hp : p ∈ closure D)
    (hpq : p ≠ q) : ContinuousOn (cfMap a Ψ q) (closure D \ {p}) := by
  intro w hw
  by_cases hwq : w = q
  · subst hwq
    rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt, cfMap_self]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun w => ‖Ψ w‖) (𝓝[(closure D \ {p}) \ {w}] w) atTop :=
      hU.tendsto.mono_left (nhdsWithin_mono _ fun x hx => ⟨hx.1.1, hx.2⟩)
    have h2 : Tendsto (fun x => (a * ‖Ψ x‖)⁻¹) (𝓝[(closure D \ {p}) \ {w}] w) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (h1.const_mul_atTop ha)
    refine h2.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    exact (norm_cfMap_of_ne ha hx.2).symm
  · have heq : cfMap a Ψ q =ᶠ[𝓝 w] fun x => negInv ((a : ℂ) * Ψ x) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hwq] with x hx
      exact cfMap_of_ne hx
    refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (eventually_nhdsWithin_of_eventually_nhds heq)
      (cfMap_of_ne hwq)
    have hmem : closure D \ {q} ∈ 𝓝[closure D \ {p}] w := by
      rw [sdiff_eq]
      exact inter_mem (mem_of_superset self_mem_nhdsWithin sdiff_subset)
        (mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hwq))
    have hΨw : ContinuousWithinAt Ψ (closure D \ {p}) w :=
      (hU.cont w ⟨hw.1, hwq⟩).mono_of_mem_nhdsWithin hmem
    have hne : (a : ℂ) * Ψ w ≠ 0 :=
      mul_ne_zero (by exact_mod_cast ha.ne') (hU.ne_zero hp hpq ⟨hw.1, hwq⟩ hw.2)
    have h1 : ContinuousWithinAt (fun x => (a : ℂ) * Ψ x) (closure D \ {p}) w :=
      Filter.Tendsto.const_mul (a : ℂ) hΨw
    exact ContinuousAt.comp_continuousWithinAt (f := fun x => (a : ℂ) * Ψ x) (x := w) (continuousAt_negInv hne)
      h1

theorem injOn_cfMap (hU : IsBdryUniformizer D p q Ψ) {a : ℝ} (ha : 0 < a) (hp : p ∈ closure D)
    (hpq : p ≠ q) : InjOn (cfMap a Ψ q) (closure D \ {p}) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have key : ∀ w ∈ closure D \ {p}, w ≠ q → cfMap a Ψ q w ≠ 0 := fun w hw hwq h => by
    rw [cfMap_of_ne hwq, negInv_eq_zero_iff] at h
    exact hU.ne_zero hp hpq ⟨hw.1, hwq⟩ hw.2 ((mul_eq_zero.1 h).resolve_left ha')
  intro w hw w' hw' h
  by_cases hwq : w = q
  · by_cases hw'q : w' = q
    · rw [hwq, hw'q]
    · rw [hwq, cfMap_self] at h
      exact absurd h.symm (key w' hw' hw'q)
  · by_cases hw'q : w' = q
    · rw [hw'q, cfMap_self] at h
      exact absurd h (key w hw hwq)
    · rw [cfMap_of_ne hwq, cfMap_of_ne hw'q] at h
      have h' := WangWu.negInv_involutive.injective h
      exact hU.inj ⟨hw.1, hwq⟩ ⟨hw'.1, hw'q⟩ (mul_left_cancel₀ ha' h')

theorem mapsTo_cfMap (hU : IsBdryUniformizer D p q Ψ) {a : ℝ} (ha : 0 < a) :
    MapsTo (cfMap a Ψ q) (closure D \ {p}) Hbar := by
  intro w hw
  by_cases hwq : w = q
  · rw [hwq, cfMap_self]
    show (0 : ℝ) ≤ (0 : ℂ).im
    simp
  · rw [cfMap_of_ne hwq]
    refine negInv_mem_Hbar ?_
    show 0 ≤ ((a : ℂ) * Ψ w).im
    rw [im_ofReal_mul]
    exact mul_nonneg ha.le (hU.mapsTo ⟨hw.1, hwq⟩)

/-- Scaling by a positive real is a conformal bijection of `ℍ`. -/
theorem isConformalBijection_ofReal_mul {a : ℝ} (ha : 0 < a) :
    IsConformalBijection (fun z => (a : ℂ) * z) H H := by
  refine ⟨(differentiable_id.const_mul (a : ℂ)).differentiableOn, ?_⟩
  have h := QuantumZipper.CA.bijOn_affine_H (b := 0) ha
  simp only [Complex.ofReal_zero, add_zero] at h
  exact h

theorem isConformalBijection_negInv_H : IsConformalBijection negInv H H :=
  ⟨WangWu.differentiableOn_negInv, fun _ hz => WangWu.negInv_mem_H hz,
    WangWu.negInv_involutive.injective.injOn, fun y hy => ⟨negInv y, WangWu.negInv_mem_H hy, WangWu.negInv_negInv y⟩⟩

/-- `−cayley` is a conformal bijection of the inverted pocket onto the Cayley image. -/
theorem isConformalBijection_neg_cayley {C : Set ℂ} (hCH : C ⊆ H) :
    IsConformalBijection (fun z => -cayley z) (negInv '' C) (cayley '' C) := by
  have hsub := image_negInv_subset_H hCH
  refine ⟨fun z hz => ((QuantumZipper.CA.differentiableAt_cayley
    (add_I_ne_zero_of_mem_Hbar (H_subset_Hbar' (hsub hz)))).neg).differentiableWithinAt, ?_⟩
  refine ⟨fun z hz => ?_, injOn_neg_cayley.mono fun z hz => H_subset_Hbar' (hsub hz), ?_⟩
  · rw [← image_neg_cayley_image_negInv hCH]
    exact mem_image_of_mem _ hz
  · rw [← image_neg_cayley_image_negInv hCH]
    exact surjOn_image _ _

/-- **The Jordan coordinate of the inverted pocket.** Let `C ⊆ ℍ` be open, and let `Ψ` be a two-point uniformizer of
its Cayley image `D` with its boundary extension (`p ↦ 0`, `q ↦ ∞`, `p ≠ q` on the frontier of `D`, neither equal to
`−1`, the image of the flow seed). For every `a > 0`, `cfCoord a Ψ q` is a Jordan coordinate of `m(C)` sending
`cfPt p = m(x₀)` to `∞` and `cfPt q = m(y₀)` to `0`. -/
theorem isJordanCoord_cfCoord {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H)
    (hU : IsBdryUniformizer (cayley '' C) p q Ψ) (hp : p ∈ frontier (cayley '' C))
    (hq : q ∈ frontier (cayley '' C)) (hpq : p ≠ q) (hp1 : p ≠ -1) (hq1 : q ≠ -1) {a : ℝ} (ha : 0 < a) :
    Sec6.IsJordanCoord (negInv '' C) (cfPt p) (cfPt q) (cfCoord a Ψ q) := by
  set D := cayley '' C with hD
  set C' := negInv '' C with hC'
  have hDo : IsOpen D := Lemma71F.isOpen_cayley_image hCo hCH
  have hpc : p ∈ closure D := frontier_subset_closure hp
  have hqD : q ∉ D := by
    rw [hDo.frontier_eq] at hq
    exact hq.2
  have hC'H : closure C' ⊆ Hbar := closure_image_negInv_subset_Hbar hCH
  -- `−cayley` maps `closure C' \ {cfPt p}` into `closure D \ {p}`
  have hmaps : MapsTo (fun z => -cayley z) (closure C' \ {cfPt p}) (closure D \ {p}) := by
    intro z hz
    refine ⟨neg_cayley_mem_closure hCH hz.1, fun h => hz.2 ?_⟩
    show z = cfPt p
    rw [← h, cfPt_neg_cayley (hC'H hz.1)]
  have hFc : ContinuousOn (fun z => -cayley z) (closure C' \ {cfPt p}) :=
    continuousOn_neg_cayley.mono fun z hz => hC'H hz.1
  have hpH : cfPt p ∈ Hbar :=
    cfPt_mem_Hbar (closure_minimal (fun w hw => ball_subset_closedBall (Lemma71F.cayley_image_subset_ball hCH hw))
      isClosed_closedBall hpc)
  refine ⟨(continuousOn_cfMap hU ha hpc hpq).comp hFc hmaps,
    (injOn_cfMap hU ha hpc hpq).comp (injOn_neg_cayley.mono fun z hz => hC'H hz.1) hmaps,
    (mapsTo_cfMap hU ha).comp hmaps, ?_, ?_, ?_, ?_⟩
  · -- conformal bijection
    have hcomp := isConformalBijection_comp isConformalBijection_negInv_H
      (isConformalBijection_comp (isConformalBijection_ofReal_mul ha)
        (isConformalBijection_comp hU.conf (isConformalBijection_neg_cayley hCH)))
    have heq : EqOn (cfCoord a Ψ q) (negInv ∘ (fun z => (a : ℂ) * z) ∘ Ψ ∘ fun z => -cayley z) C' := by
      intro z hz
      have hzD : -cayley z ∈ D := by
        rw [hD, ← image_neg_cayley_image_negInv hCH]
        exact mem_image_of_mem _ hz
      have hzq : -cayley z ≠ q := fun h => hqD (h ▸ hzD)
      simp only [cfCoord, cfMap_of_ne hzq, comp_apply]
    exact ⟨hcomp.1.congr fun z hz => heq hz, hcomp.2.congr heq.symm⟩
  · -- real on the frontier
    intro z hz
    have hzH := hC'H (frontier_subset_closure hz.1)
    have hF := neg_cayley_mem_frontier hCo hCH hz.1
    by_cases hzq : -cayley z = q
    · simp only [cfCoord, hzq, cfMap_self, zero_im]
    · simp only [cfCoord]
      rw [cfMap_of_ne hzq]
      refine im_negInv_eq_zero ?_
      rw [im_ofReal_mul, hU.im_eq_zero hDo hqD hF hzq, mul_zero]
  · -- `m(y₀) ↦ 0`
    simp only [cfCoord, neg_cayley_cfPt hq1, cfMap_self]
  · -- `m(x₀) ↦ ∞`
    rw [← tendsto_norm_atTop_iff_cobounded]
    have hFp : -cayley (cfPt p) = p := neg_cayley_cfPt hp1
    have hFt : Tendsto (fun z => -cayley z) (𝓝[closure C' \ {cfPt p}] (cfPt p)) (𝓝 p) := by
      have := (continuousAt_neg_cayley hpH).tendsto.mono_left (nhdsWithin_le_nhds (s := closure C' \ {cfPt p}))
      rwa [hFp] at this
    have hev : ∀ᶠ z in 𝓝[closure C' \ {cfPt p}] (cfPt p), -cayley z ∈ closure D \ {q} ∧ -cayley z ≠ p := by
      have h1 : ∀ᶠ z in 𝓝[closure C' \ {cfPt p}] (cfPt p), -cayley z ≠ q :=
        hFt (isOpen_compl_singleton.mem_nhds hpq)
      filter_upwards [h1, self_mem_nhdsWithin] with z hz1 hz2
      exact ⟨⟨(hmaps hz2).1, hz1⟩, (hmaps hz2).2⟩
    have hFt' : Tendsto (fun z => -cayley z) (𝓝[closure C' \ {cfPt p}] (cfPt p)) (𝓝[closure D \ {q}] p) :=
      tendsto_nhdsWithin_iff.2 ⟨hFt, hev.mono fun z hz => hz.1⟩
    have hΨ0 : Tendsto (fun z => Ψ (-cayley z)) (𝓝[closure C' \ {cfPt p}] (cfPt p)) (𝓝 0) := by
      have := (hU.cont p ⟨hpc, hpq⟩).tendsto.comp hFt'
      rwa [hU.zero] at this
    have hpos : Tendsto (fun z => a * ‖Ψ (-cayley z)‖) (𝓝[closure C' \ {cfPt p}] (cfPt p)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hev.mono fun z hz => ?_⟩
      · have := (hΨ0.norm).const_mul a
        rwa [norm_zero, mul_zero] at this
      · exact mul_pos ha (norm_pos_iff.2 (hU.ne_zero hpc hpq hz.1 hz.2))
    refine (tendsto_inv_nhdsGT_zero.comp hpos).congr' (hev.mono fun z hz => ?_)
    simp only [comp_apply, cfCoord]
    exact (norm_cfMap_of_ne ha hz.1.2).symm

end Coord

end InteractingSLE.Sec7.PocketJordan
