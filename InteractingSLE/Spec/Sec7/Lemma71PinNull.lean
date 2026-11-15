/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PinScale

/-!
# Ingredients of the pinned pocket statement: null sets, the empty hull, default data, boundary values and pins

Packet PROVE-LEMMA71S. `Lemma71F.Lemma71PocketPinStatement` asks for pocket data whose pathwise clauses hold for
**every** `ω`; the construction gives some of them only almost surely. The data are therefore redefined on a null set
`N`, which is put into the base σ-algebra `𝓐₀ = σ(β, α) ∨ 𝒩`. This file collects the ingredients:

* **`isChartCouplingCharFunConst_sup_nullSets`**: adding the null sets to the base σ-algebra of the prefix filtration
  (and changing the chart on a null set) keeps the fixed-time chart clause (`condExp_ae_eq_of_le_sup_nullSets`);
* `fillH_empty`, `canonDerivLog_empty_eqOn`: the empty hull and its canonical logarithm (`0`);
* `exists_index_near`, `exists_index_seq_zero`, `exists_index_seq_infty`: default points of a dense sequence in `ℍ`;
* `isDerivLog_dilation`: the dilation chart has the constant logarithm `log r`;
* **`tendsto_fwd_cayleyInv`**: the boundary value of a chart `c = Ψ ∘ cayley` at the Cayley preimage of a point of the
  closure (the segment points of the mapped segment);
* **`eventually_tendsto_pin`**: on a pocket frame with the inherited branch, for all large `j` the inherited lift minus
  `Im log g′` of the wall prefix `β([0, j])` tends to `0` along every chart approach to `−1/(j + 1)` (the argument of
  `Lemma71O.pocketBranchStatement`, with its pin exposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71S

open QuantumZipper (H Hbar fwdHull)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71D Lemma71E

/-! ### Null sets in the base σ-algebra -/

section Null

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Null sets do not change conditional expectations**: if `m₁ ≤ m₂ ≤ m₁ ∨ 𝒩`, then `E[X | m₂] = E[X | m₁]` almost
surely. -/
theorem condExp_ae_eq_of_le_sup_nullSets [IsProbabilityMeasure P] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂)
    (h₂ : m₂ ≤ m₁ ⊔ Ito.nullSets P) (h₂Ω : m₂ ≤ mΩ) {X : Ω → E} (hX : Integrable X P) :
    P[X | m₂] =ᵐ[P] P[X | m₁] := by
  have hm₁ : m₁ ≤ mΩ := h₁₂.trans h₂Ω
  refine (ae_eq_condExp_of_forall_setIntegral_eq h₂Ω hX (fun s _ _ => integrable_condExp.integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · have key : ∃ s', MeasurableSet[m₁] s' ∧ s =ᵐ[P] s' :=
      (sup_le le_eventuallyMeasurableSpace (MeasurableSpace.generateFrom_le fun _ hu =>
        ⟨∅, @MeasurableSet.empty _ m₁, ae_eq_empty.mpr hu.2⟩) :
        m₁ ⊔ Ito.nullSets P ≤ eventuallyMeasurableSpace m₁ (ae P)) s (h₂ s hs)
    obtain ⟨s', hs', hss'⟩ := key
    rw [setIntegral_congr_set hss', setIntegral_congr_set hss', setIntegral_condExp hm₁ hX hs']
  · exact (stronglyMeasurable_condExp.mono h₁₂).aestronglyMeasurable

theorem prefixFiltrationOf_mono_base {m₀ m₀' : MeasurableSpace Ω} (h : m₀ ≤ m₀') (γ : Ω → ℝ → ℂ) (t : ℝ≥0) :
    prefixFiltrationOf (mΩ := mΩ) m₀ γ t ≤ prefixFiltrationOf (mΩ := mΩ) m₀' γ t :=
  inf_le_inf_right _ (sup_le_sup_right h _)

/-- With the null sets in the base σ-algebra, the prefix filtration is within the null augmentation of the old one. -/
theorem prefixFiltrationOf_sup_nullSets_le {m₀ : MeasurableSpace Ω} (hm₀ : m₀ ≤ mΩ) {γ : Ω → ℝ → ℂ}
    (hpm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k)) (P : @Measure Ω mΩ) (t : ℝ≥0) :
    prefixFiltrationOf (mΩ := mΩ) (m₀ ⊔ Ito.nullSets P) γ t ≤
      prefixFiltrationOf (mΩ := mΩ) m₀ γ t ⊔ Ito.nullSets P := by
  have hpre := isPrefixAdapted_prefixFiltrationOf (mΩ := mΩ) m₀ γ hpm
  have h₀ : m₀ ≤ prefixFiltrationOf (mΩ := mΩ) m₀ γ t := le_prefixFiltrationOf (mΩ := mΩ) hm₀ γ t
  show (m₀ ⊔ Ito.nullSets P ⊔ MeasurableSpace.generateFrom
      {s | ∃ r' : ℝ≥0, r' ≤ t ∧ ∃ n k, s = prefixEvent γ r' n k}) ⊓ mΩ ≤ _
  refine inf_le_left.trans (sup_le (sup_le (h₀.trans le_sup_left) le_sup_right) ?_)
  refine MeasurableSpace.generateFrom_le fun s hs => ?_
  obtain ⟨r', hr', n, k, rfl⟩ := hs
  exact le_sup_left (b := Ito.nullSets P) _ ((prefixFiltrationOf (mΩ := mΩ) m₀ γ).mono hr' _ (hpre r' n k))

/-- **The fixed-time chart clause survives adding the null sets to the base σ-algebra and changing the chart on a
null set.** -/
theorem isChartCouplingCharFunConst_sup_nullSets [IsProbabilityMeasure P] {m₀ : MeasurableSpace Ω}
    (hm₀ : m₀ ≤ mΩ) {γ : Ω → ℝ → ℂ} (hpm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k)) {κ : ℝ}
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c c' : Ω → Chart} {a k : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable[mΩ] h) (hc : ∀ᵐ ω ∂P, c' ω = c ω)
    (hcf : IsChartCouplingCharFunConst κ ρL ρR P (prefixFiltrationOf (mΩ := mΩ) m₀ γ) W VL VR ζ c a k h) :
    IsChartCouplingCharFunConst κ ρL ρR P (prefixFiltrationOf (mΩ := mΩ) (m₀ ⊔ Ito.nullSets P) γ) W VL VR ζ c' a k
      h := by
  intro t u hu φ
  have hXm : Measurable[mΩ] fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) := by
    have hφm : Measurable[mΩ] fun ω => h ω φ := (LQGMetric.measurable_distOn_apply φ).comp hh
    exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hφm))
  have hXi : Integrable (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) P := by
    refine (MemLp.of_bound (μ := P) (p := 1) hXm.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)).integrable
      le_rfl
    show ‖Complex.exp (Complex.I * (h ω φ : ℂ))‖ ≤ 1
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hce := condExp_ae_eq_of_le_sup_nullSets (mΩ := mΩ) (P := P)
    (prefixFiltrationOf_mono_base (mΩ := mΩ) (le_sup_left : m₀ ≤ m₀ ⊔ Ito.nullSets P) γ t)
    (prefixFiltrationOf_sup_nullSets_le (mΩ := mΩ) hm₀ hpm P t)
    ((prefixFiltrationOf (mΩ := mΩ) (m₀ ⊔ Ito.nullSets P) γ).le t) hXi
  filter_upwards [hcf t u hu φ, hce, hc] with ω h1 h2 h3 hlt hsub
  rw [h3] at hsub ⊢
  rw [h2]
  exact h1 hlt hsub

end Null

/-! ### The empty hull -/

section Empty

theorem fillH_empty : fillH (∅ : Set ℂ) = ∅ := by
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨hzH, hz'⟩ := hz
  rw [closure_empty, sdiff_empty] at hz'
  rcases hz' with h | h
  · exact h
  · have hpre : IsPreconnected H :=
      (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
    rw [hpre.connectedComponentIn hzH] at h
    exact Sec4.not_isBounded_H h

/-- The canonical logarithm of the derivative of the mapping-out function of the empty hull is `0` on `ℍ`. -/
theorem canonDerivLog_empty_eqOn : EqOn (Restart.canonDerivLog (∅ : Set ℂ)) 0 H := by
  have hg := ConformalImage.isMapOut_mapOut isHPHull_empty
  have hid : EqOn (ConformalImage.mapOut (∅ : Set ℂ)) id (H \ ∅) := hg.eqOn isHPHull_empty isMapOut_empty_id
  have hderiv : ∀ z ∈ H, deriv (ConformalImage.mapOut (∅ : Set ℂ)) z = 1 := fun z hz => by
    have hev : ConformalImage.mapOut (∅ : Set ℂ) =ᶠ[𝓝 z] id := by
      filter_upwards [QuantumZipper.isOpen_H.mem_nhds hz] with w hw
      exact hid ⟨hw, notMem_empty w⟩
    rw [hev.deriv_eq, deriv_id]
  have h0 : Restart.IsCanonicalDerivLog ∅ (ConformalImage.mapOut ∅) 0 := by
    refine ⟨⟨differentiableOn_const 0, fun z hz => ?_⟩, 0, fun w hw => ?_⟩
    · rw [hderiv z (by simpa only [sdiff_empty] using hz)]
      simp
    · rw [hderiv w hw, Complex.log_one]
      rfl
  have h1 := Restart.isCanonicalDerivLog_canonDerivLog (A := ∅) isHPHull_empty
  have := Restart.IsCanonicalDerivLog.eqOn h1 h0 isHPHull_empty hg
  rwa [sdiff_empty] at this

end Empty

/-! ### Default data -/

section Default

/-- A point of a dense sequence in `ℍ` near a given point of `ℍ`. -/
theorem exists_index_near {e : ℕ → ℂ} (he : DenseRange e) {z : ℂ} (hz : z ∈ H) {r : ℝ} (hr : 0 < r) :
    ∃ j, e j ∈ H ∧ dist (e j) z < r := by
  have hzr : 0 < min z.im r := lt_min hz hr
  obtain ⟨j, hj⟩ := he.exists_mem_open isOpen_ball ⟨z, mem_ball_self hzr⟩
  have hd : dist (e j) z < min z.im r := hj
  refine ⟨j, ?_, hd.trans_le (min_le_right _ _)⟩
  have h1 : |(e j - z).im| ≤ ‖e j - z‖ := Complex.abs_im_le_norm _
  rw [← dist_eq_norm] at h1
  have h2 := h1.trans_lt (hd.trans_le (min_le_left _ _))
  rw [Complex.sub_im] at h2
  show 0 < (e j).im
  linarith [neg_abs_le ((e j).im - z.im)]

/-- Indices of a dense sequence: points of `ℍ` tending to `0`. -/
theorem exists_index_seq_zero {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ N : ℕ → ℕ, (∀ m, e (N m) ∈ H) ∧ Tendsto (fun m => e (N m)) atTop (𝓝 0) := by
  have hz : ∀ m : ℕ, ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I ∈ H := fun m => by
    show 0 < (((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
    positivity
  choose N hNH hNd using fun m : ℕ => exists_index_near he (hz m) (r := 1 / ((m : ℝ) + 1)) (by positivity)
  refine ⟨N, hNH, ?_⟩
  have h0 : Tendsto (fun m : ℕ => 2 * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun m => dist_nonneg) (fun m => ?_) h0)
  have h2 : dist (((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I) 0 = 1 / ((m : ℝ) + 1) := by
    rw [dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  calc dist (e (N m)) 0 ≤ dist (e (N m)) (((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I) +
        dist (((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I) 0 := dist_triangle _ _ _
    _ ≤ 2 * (1 / ((m : ℝ) + 1)) := by rw [h2]; linarith [hNd m]

/-- Indices of a dense sequence: points of `ℍ` tending to `∞`. -/
theorem exists_index_seq_infty {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ N : ℕ → ℕ, (∀ m, e (N m) ∈ H) ∧ Tendsto (fun m => ‖e (N m)‖) atTop atTop := by
  have hz : ∀ m : ℕ, (((m : ℝ) + 1 : ℝ) : ℂ) * Complex.I ∈ H := fun m => by
    show 0 < ((((m : ℝ) + 1 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
    positivity
  choose N hNH hNd using fun m : ℕ => exists_index_near he (hz m) one_pos
  refine ⟨N, hNH, tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop⟩
  have h2 : ‖(((m : ℝ) + 1 : ℝ) : ℂ) * Complex.I‖ = (m : ℝ) + 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h3 := norm_sub_norm_le ((((m : ℝ) + 1 : ℝ) : ℂ) * Complex.I) (e (N m))
  rw [← dist_eq_norm, dist_comm, h2] at h3
  linarith [hNd m]

/-- The dilation chart has the constant derivative logarithm `log r`. -/
theorem isDerivLog_dilation {r : ℝ} (hr : 0 < r) (D : Set ℂ) :
    IsDerivLog (Chart.dilation r).1 (fun _ => ((Real.log r : ℝ) : ℂ)) D := by
  refine ⟨differentiableOn_const _, fun z _ => ?_⟩
  show Complex.exp ((Real.log r : ℝ) : ℂ) = deriv (fun z => (r : ℂ) * z) z
  rw [deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one, ← Complex.ofReal_exp, Real.exp_log hr]

end Default

/-! ### Boundary values of a chart through the Cayley transform -/

/-- **The boundary value of a chart `c = Ψ ∘ cayley` at the Cayley preimage of a point of the closure.** If
`c.1 = Ψ ∘ cayley` on `C ⊆ ℍ`, `Ψ` is continuous within a set `S ⊇ cayley '' C` at a point `p ≠ 1` of the closure of
`cayley '' C`, then `cayleyInv p ∈ closure C` and `c.1 → Ψ p` at `cayleyInv p` within `C`. -/
theorem tendsto_fwd_cayleyInv {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} (hCH : C ⊆ H)
    (hΨe : ∀ x ∈ C, c.1 x = Ψ (cayley x)) {S : Set ℂ} (hCS : cayley '' C ⊆ S) {p : ℂ}
    (hΨc : ContinuousWithinAt Ψ S p) (hp1 : p ≠ 1) (hp : p ∈ closure (cayley '' C)) :
    cayleyInv p ∈ closure C ∧ Tendsto c.1 (𝓝[C] (cayleyInv p)) (𝓝 (Ψ p)) := by
  have hcc : cayley (cayleyInv p) = p := QuantumZipper.CA.cayley_cayleyInv hp1
  have hinvc : ContinuousAt cayleyInv p := (QuantumZipper.CA.differentiableAt_cayleyInv hp1).continuousAt
  have hcayc : ContinuousAt cayley (cayleyInv p) :=
    (QuantumZipper.CA.differentiableAt_cayley
      (QuantumZipper.CA.ne_neg_I_iff.1 (QuantumZipper.CA.cayleyInv_ne_neg_I hp1))).continuousAt
  have hback : cayleyInv '' (cayley '' C) = C := by
    rw [image_image]
    refine (image_congr fun z hz => ?_).trans (image_id C)
    exact QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (hCH hz).le)
  refine ⟨?_, ?_⟩
  · have := hinvc.continuousWithinAt.mem_closure_image hp
    rwa [hback] at this
  · have h1 : Tendsto cayley (𝓝[C] (cayleyInv p)) (𝓝[cayley '' C] p) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => mem_image_of_mem _ hx⟩
      have := hcayc.tendsto.mono_left (nhdsWithin_le_nhds (s := C))
      rwa [hcc] at this
    have h2 := (hΨc.tendsto.mono_left (nhdsWithin_mono _ hCS)).comp h1
    exact h2.congr' (eventually_nhdsWithin_of_forall fun x hx => (hΨe x hx).symm)

/-! ### The pin of the inherited branch -/

section Pin

open Lemma71O Lemma71O.PocketFrame
open Lemma71N (IsPocketFrame IsPocketBranch)

variable {β α : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ}

/-- **The pin of the inherited branch, pathwise** (the argument of `Lemma71O.pocketBranchStatement`): on a pocket frame
with the inherited branch `n` and generating traces of both walls, for every family of chart approaches `z j k` to
the chart points `ξ_j = −1/(j + 1)`, for all large `j` the inherited lift minus `Im log g′` of the canonical logarithm
of the wall prefix `fill β([0, j])` tends to `0` along `z j ·`. -/
theorem eventually_tendsto_pin (hF : IsPocketFrame β α C c Ψ a b) {n : ℤ} (hN : IsPocketBranch β α c n)
    {Wβ Wα : ℝ≥0 → ℝ} (htrβ : IsGeneratingTrace Wβ ⊤ β) (htrα : IsGeneratingTrace Wα ⊤ α) {z : ℕ → ℕ → ℂ}
    (hzC : ∀ j k, z j k ∈ C)
    (hzt : ∀ j : ℕ, Tendsto (fun k => c.1 (z j k)) atTop (𝓝[H] (((-(1 / ((j : ℝ) + 1)) : ℝ)) : ℂ))) :
    ∀ᶠ j : ℕ in atTop, (∀ k, z j k ∈ H \ fillH (β '' Icc 0 (j : ℝ≥0))) ∧
      Tendsto (fun k => c.2.2 (z j k) + 2 * π * n -
        (Restart.canonDerivLog (fillH (β '' Icc 0 (j : ℝ≥0))) (z j k)).im) atTop (𝓝 0) := by
  have hWβ := continuous_of_isGeneratingTrace_top htrβ
  have hWβ0 : Wβ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrβ (by simp)
  set ξ : ℕ → ℝ := fun j => -(1 / ((j : ℝ) + 1)) with hξdef
  obtain ⟨sa, hsa⟩ := exists_land_zero_eq hF
  set Q₀ : ℕ := ⌈(sa : ℝ)⌉₊ + 1 with hQ₀
  have hsaQ₀ : sa < (Q₀ : ℝ≥0) := by
    have h1 : (sa : ℝ) ≤ ⌈(sa : ℝ)⌉₊ := Nat.le_ceil _
    have h2 : (sa : ℝ) < (Q₀ : ℝ) := by rw [hQ₀]; push_cast; linarith
    exact_mod_cast h2
  obtain ⟨ρ, hρ, hball⟩ := Lemma71N.exists_ball_tail hF.hβ hsaQ₀
  have hξt : Tendsto ξ atTop (𝓝 0) := by
    have : Tendsto (fun j : ℕ => -(1 / ((j : ℝ) + 1))) atTop (𝓝 (-(0 : ℝ))) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    rw [neg_zero] at this
    exact this
  have hlt : Tendsto (fun j => land c (ξ j)) atTop (𝓝 (land c 0)) := by
    have := ((continuous_land_ofReal hF).tendsto 0).comp hξt
    rw [Complex.ofReal_zero] at this
    exact this
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hlt (ball_mem_nhds _ hρ))
  filter_upwards [eventually_ge_atTop (max J Q₀)] with j hj
  have hzK : ∀ k, z j k ∈ H \ fillH (β '' Icc 0 (j : ℝ≥0)) := fun k =>
    dom_subset_H_diff_fillH htrβ hF.hdom (subset_H_diff_fwdHull_left hF htrβ) j (by rw [hF.hdom]; exact hzC j k)
  refine ⟨hzK, ?_⟩
  have hξj : ξ j < 0 := by simp only [hξdef, Left.neg_neg_iff]; positivity
  obtain ⟨s, -, -, hs⟩ := land_ofReal_neg hF hξj
  have hsQ : s < (j : ℝ≥0) := by
    have hsQ₀ : s < (Q₀ : ℝ≥0) := by
      by_contra hle
      refine hball s (not_lt.1 hle) ?_
      rw [← hs, ← hsa]
      exact hJ j (le_of_max_le_left hj)
    exact hsQ₀.trans_le (by exact_mod_cast le_of_max_le_right hj)
  have hland : Tendsto c.2.1 (𝓝[H] (ξ j : ℂ)) (𝓝 (β s)) :=
    hs ▸ tendsto_land hF (mem_Hbar_of_im_eq_zero (by simp))
  have hbr := (hN Wβ Wα htrβ htrα (ξ j) s j hsQ).1 hξj hland
  have hcomp := hbr.comp (hzt j)
  refine hcomp.congr fun k => ?_
  have hinv : c.2.1 (c.1 (z j k)) = z j k := hF.hc.inv_fwd (by rw [← SetLike.mem_coe, hF.hdom]; exact hzC j k)
  simp only [Function.comp_apply, hinv]
  rw [canonDerivLog_eqOn_logDerivFwd htrβ hWβ hWβ0 j (hzK k)]

end Pin

end InteractingSLE.Sec7.Lemma71S
