/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3Orient
import InteractingSLE.Spec.Sec5.Prop55HalfSide

/-!
# Lemma GW3's geometry for walls that touch the real line

Packet PROVE-T14-GW8. Lemma GW3 and Theorem GW4 (`source/spec/p625-671.md` L203–L262, pp. 636–638) use the
components between the two boundary walks `R`, `L` as Jordan components with a chart `(C; x_C, y_C) → (ℍ; 0, ∞)`
whose positive boundary is on `R` and whose negative boundary is on `L` ("The ordered-contact Jordan argument and GB13a
consequently apply to these two proper simple curves, with their actual real connectors included"). PROVE-ORIENT
proved this for walls in `ℍ` at positive times (`GW3.hasOrientedUniformizer_of_mem_betweenComponents`); the GW1 walks
may run along `ℝ` (their real connectors), which that theorem does not cover.

This file proves the planar statement for walls that may touch `ℝ`, by a conformal change of coordinates:
the square-root map `Φ(z) = i √(−i z)` (`sectorMap`) sends `ℍ̄` homeomorphically onto the closed sector
`{|Re w| ≤ Im w}` (`closedSector`), `ℍ` onto the open sector, the positive reals onto the ray of argument `π/4` and the
negative reals onto the ray of argument `3π/4`; its inverse is the polynomial `q(w) = −i w²` (`sectorInv`). A proper
curve from `0` in `ℍ̄` becomes a simple proper curve in `ℍ` (`isSimpleProper_sectorMap_comp`). The two side
regions outside the sector (`rightWedge`, `leftWedge`) touch the positive and the negative real axis, so the frozen
sides `rightSideOf`, `leftSideOf` are transported (`sectorInv_mem_rightSideOf_or`, `sectorInv_mem_leftSideOf_or`), as
are the components between the walls (`image_mem_betweenComponents`) and the oriented uniformizers
(`HasOrientedUniformizer.of_sectorMap`).

## Main result

* **`hasOrientedUniformizer_of_touching`** (deterministic): let `γR`, `γL` be proper curves from `0` in `ℍ̄`
  (`Supp9B.IsProperCurve`), with `range γR` disjoint from the frozen left side of `range γL`, and with every negative
  real point of `γR` also on `γL`. Then every component between `range γR` and `range γL` has an oriented uniformizer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Function Metric
open QuantumZipper (H Hbar isOpen_H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Theorem14.GW3SidedProof

/-! ### The square-root sector map -/

/-- The square-root chart `Φ(z) = i √(−i z)` (principal branch), a homeomorphism of `ℍ̄` onto the closed sector
`{|Re w| ≤ Im w}`. -/
def sectorMap (z : ℂ) : ℂ := I * (-I * z) ^ ((2 : ℂ)⁻¹)

/-- The inverse of `sectorMap`, the polynomial `q(w) = −i w²`. -/
def sectorInv (w : ℂ) : ℂ := -I * w ^ 2

/-- The closed upper sector `{|Re w| ≤ Im w}` between the rays of argument `π/4` and `3π/4`. -/
def closedSector : Set ℂ := {w | |w.re| ≤ w.im}

/-- The open upper sector `{|Re w| < Im w}`. -/
def openSector : Set ℂ := {w | |w.re| < w.im}

/-- The open wedge between the positive real axis and the ray of argument `π/4`. -/
def rightWedge : Set ℂ := {w | 0 < w.im ∧ w.im < w.re}

/-- The open wedge between the ray of argument `3π/4` and the negative real axis. -/
def leftWedge : Set ℂ := {w | 0 < w.im ∧ w.im < -w.re}

theorem sectorInv_re (w : ℂ) : (sectorInv w).re = 2 * w.re * w.im := by
  simp [sectorInv, sq]; ring

theorem sectorInv_im (w : ℂ) : (sectorInv w).im = w.im ^ 2 - w.re ^ 2 := by
  simp [sectorInv, sq]

theorem continuous_sectorInv : Continuous sectorInv := by
  unfold sectorInv; fun_prop

theorem sectorInv_sectorMap (z : ℂ) : sectorInv (sectorMap z) = z := by
  have h := Complex.cpow_nat_inv_pow (-I * z) (n := 2) two_ne_zero
  have h2 : ((2 : ℕ) : ℂ) = 2 := by norm_num
  rw [h2] at h
  unfold sectorInv sectorMap
  rw [mul_pow, h, I_sq]
  ring_nf
  rw [I_sq]
  ring

theorem sectorMap_injective : Injective sectorMap :=
  LeftInverse.injective sectorInv_sectorMap

theorem sectorMap_zero : sectorMap 0 = 0 := by
  simp [sectorMap]

theorem sectorMap_im_nonneg (z : ℂ) : 0 ≤ (sectorMap z).im := by
  have hre : 0 ≤ ((-I * z) ^ ((2 : ℂ)⁻¹)).re := by
    by_cases hz : -I * z = 0
    · rw [hz, zero_cpow (by norm_num)]
      simp
    rw [cpow_def_of_ne_zero hz, exp_re]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ?_)
    have h1 : (log (-I * z) * (2 : ℂ)⁻¹).im = arg (-I * z) / 2 := by
      have : (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) := by push_cast; ring
      rw [this, mul_im, log_im, ofReal_re, ofReal_im, mul_zero, zero_add]
      ring
    rw [h1]
    have := neg_pi_lt_arg (-I * z)
    have := arg_le_pi (-I * z)
    constructor <;> linarith
  simpa [sectorMap] using hre

theorem sq_le_sq_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) :
    (sectorMap z).re ^ 2 ≤ (sectorMap z).im ^ 2 := by
  have h := sectorInv_im (sectorMap z)
  rw [sectorInv_sectorMap] at h
  have : (0 : ℝ) ≤ z.im := hz
  linarith

theorem sectorMap_mem_closedSector {z : ℂ} (hz : z ∈ Hbar) : sectorMap z ∈ closedSector :=
  abs_le_of_sq_le_sq' (sq_le_sq_of_mem_Hbar hz) (sectorMap_im_nonneg z) |> fun h => abs_le.2 h

theorem sectorMap_mem_openSector {z : ℂ} (hz : z ∈ H) : sectorMap z ∈ openSector := by
  have h := sectorInv_im (sectorMap z)
  rw [sectorInv_sectorMap] at h
  have hz' : (0 : ℝ) < z.im := hz
  have hlt : (sectorMap z).re ^ 2 < (sectorMap z).im ^ 2 := by linarith
  exact abs_lt_of_sq_lt_sq hlt (sectorMap_im_nonneg z)

theorem isClosed_closedSector : IsClosed closedSector :=
  isClosed_le (continuous_abs.comp continuous_re) continuous_im

theorem isOpen_openSector : IsOpen openSector :=
  isOpen_lt (continuous_abs.comp continuous_re) continuous_im

theorem openSector_subset_closedSector : openSector ⊆ closedSector := fun w hw =>
  (show |w.re| < w.im from hw).le

theorem openSector_subset_H : openSector ⊆ H := fun w hw =>
  show (0 : ℝ) < w.im from lt_of_le_of_lt (abs_nonneg _) hw

theorem closure_openSector_subset : closure openSector ⊆ closedSector :=
  closure_minimal openSector_subset_closedSector isClosed_closedSector

theorem ofReal_notMem_closedSector {x : ℝ} (hx : x ≠ 0) : (x : ℂ) ∉ closedSector := by
  intro h
  have h' : |x| ≤ 0 := by simpa [closedSector] using h
  exact hx (abs_nonpos_iff.1 h')

theorem mem_H_of_mem_closedSector {w : ℂ} (hw : w ∈ closedSector) (h0 : w ≠ 0) : w ∈ H := by
  show (0 : ℝ) < w.im
  have h1 : |w.re| ≤ w.im := hw
  rcases (abs_nonneg w.re).trans h1 |>.lt_or_eq with h | h
  · exact h
  · exfalso
    have hre : w.re = 0 := abs_eq_zero.1 (le_antisymm (h ▸ h1) (abs_nonneg _))
    exact h0 (Complex.ext hre h.symm)

theorem sectorMap_mem_H {z : ℂ} (hz : z ∈ Hbar) (h0 : z ≠ 0) : sectorMap z ∈ H := by
  refine mem_H_of_mem_closedSector (sectorMap_mem_closedSector hz) fun h => h0 ?_
  rw [← sectorInv_sectorMap z, h]
  simp [sectorInv]

theorem injOn_sectorInv : InjOn sectorInv closedSector := by
  intro w hw w' hw' h
  have h2 : (w - w') * (w + w') = 0 := by
    have : -I * w ^ 2 = -I * w' ^ 2 := h
    have h' : w ^ 2 = w' ^ 2 := by
      have hI : (-I : ℂ) ≠ 0 := neg_ne_zero.2 I_ne_zero
      exact mul_left_cancel₀ hI this
    linear_combination h'
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · have hw1 : |w.re| ≤ w.im := hw
    have hw2 : |w'.re| ≤ w'.im := hw'
    have hre : w'.re = -w.re := by
      have := congrArg Complex.re h3; simp at this; linarith
    have him : w'.im = -w.im := by
      have := congrArg Complex.im h3; simp at this; linarith
    rw [hre, him, abs_neg] at hw2
    have h0 : w.im = 0 := by linarith [abs_nonneg w.re]
    have h0' : w.re = 0 := abs_eq_zero.1 (le_antisymm (by linarith) (abs_nonneg _))
    apply Complex.ext <;> simp [hre, him, h0, h0']

theorem sectorInv_mem_Hbar {w : ℂ} (hw : w ∈ closedSector) : sectorInv w ∈ Hbar := by
  show (0 : ℝ) ≤ (sectorInv w).im
  rw [sectorInv_im]
  have h1 : |w.re| ≤ w.im := hw
  nlinarith [abs_nonneg w.re, sq_abs w.re]

theorem sectorInv_mem_H {w : ℂ} (hw : w ∈ openSector) : sectorInv w ∈ H := by
  show (0 : ℝ) < (sectorInv w).im
  rw [sectorInv_im]
  have h1 : |w.re| < w.im := hw
  nlinarith [abs_nonneg w.re, sq_abs w.re]

theorem sectorMap_sectorInv {w : ℂ} (hw : w ∈ closedSector) : sectorMap (sectorInv w) = w :=
  injOn_sectorInv (sectorMap_mem_closedSector (sectorInv_mem_Hbar hw)) hw (sectorInv_sectorMap _)

/-- On the boundary rays of the sector, `q` is real: `q(p) = 2 Re p Im p`. -/
theorem sectorInv_eq_ofReal {p : ℂ} (hp : |p.re| = p.im) : sectorInv p = ((2 * p.re * p.im : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [sectorInv_re]
  · rw [sectorInv_im, ofReal_im, ← hp, sq_abs]; ring

theorem continuousOn_sectorMap : ContinuousOn sectorMap Hbar := by
  intro z hz
  have hz' : (0 : ℝ) ≤ z.im := hz
  have h1 : ContinuousAt (fun u : ℂ => u ^ ((2 : ℂ)⁻¹)) (-I * z) :=
    continuousAt_cpow_const_of_re_pos (Or.inl (by simpa using hz')) (by norm_num)
  exact (continuousAt_const.mul (h1.comp (continuousAt_const.mul continuousAt_id))).continuousWithinAt

theorem differentiableAt_sectorMap {z : ℂ} (hz : z ∈ H) : DifferentiableAt ℂ sectorMap z := by
  have hz' : (0 : ℝ) < z.im := hz
  have hs : -I * z ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by simpa using hz'))
  exact (differentiableAt_const _).mul ((differentiableAt_const _).mul differentiableAt_id |>.cpow_const hs)

theorem norm_sectorMap_sq (z : ℂ) : ‖sectorMap z‖ ^ 2 = ‖z‖ := by
  conv_rhs => rw [← sectorInv_sectorMap z]
  simp [sectorInv]

/-! ### The two wedges outside the sector -/

theorem convexComb_pos {a b u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hu : 0 < u) (hv : 0 < v) :
    0 < a * u + b * v := by
  have h1 := mul_le_mul_of_nonneg_left (min_le_left u v) ha
  have h2 := mul_le_mul_of_nonneg_left (min_le_right u v) hb
  have h3 := lt_min hu hv
  nlinarith

theorem convex_rightWedge : Convex ℝ rightWedge := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only [rightWedge, Set.mem_ofPred_eq, add_im, add_re, smul_im, smul_re, smul_eq_mul]
  refine ⟨convexComb_pos ha hb hab hx1 hy1, ?_⟩
  have := convexComb_pos ha hb hab (sub_pos.2 hx2) (sub_pos.2 hy2)
  linarith

theorem convex_leftWedge : Convex ℝ leftWedge := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only [leftWedge, Set.mem_ofPred_eq, add_im, add_re, smul_im, smul_re, smul_eq_mul]
  refine ⟨convexComb_pos ha hb hab hx1 hy1, ?_⟩
  have := convexComb_pos ha hb hab (show 0 < -x.re - x.im by linarith) (show 0 < -y.re - y.im by linarith)
  linarith

theorem rightWedge_subset_H : rightWedge ⊆ H := fun _ hw => hw.1

theorem leftWedge_subset_H : leftWedge ⊆ H := fun _ hw => hw.1

theorem disjoint_rightWedge_closedSector : Disjoint rightWedge closedSector :=
  Set.disjoint_left.2 fun w hw hs => by
    have h1 : |w.re| ≤ w.im := hs
    linarith [le_abs_self w.re, hw.2]

theorem disjoint_leftWedge_closedSector : Disjoint leftWedge closedSector :=
  Set.disjoint_left.2 fun w hw hs => by
    have h1 : |w.re| ≤ w.im := hs
    linarith [neg_le_abs w.re, hw.2]

/-- A point of the ray of argument `π/4` is a limit of points of the right wedge (move right). -/
theorem mem_closure_rightWedge {p : ℂ} (hp : p.re = p.im) (hp0 : 0 < p.im) : p ∈ closure rightWedge := by
  have ht : Tendsto (fun s : ℝ => p + (s : ℂ)) (𝓝[>] 0) (𝓝 p) := by
    have : Continuous (fun s : ℝ => p + (s : ℂ)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : (0 : ℝ) < s)
  exact ⟨by simpa using hp0, by simp; linarith⟩

/-- A point of the ray of argument `3π/4` is a limit of points of the left wedge (move left). -/
theorem mem_closure_leftWedge {p : ℂ} (hp : p.re = -p.im) (hp0 : 0 < p.im) : p ∈ closure leftWedge := by
  have ht : Tendsto (fun s : ℝ => p - (s : ℂ)) (𝓝[>] 0) (𝓝 p) := by
    have : Continuous (fun s : ℝ => p - (s : ℂ)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : (0 : ℝ) < s)
  exact ⟨by simpa using hp0, by simp; linarith⟩

/-- A positive real is a limit of points of the right wedge (move up). -/
theorem ofReal_mem_closure_rightWedge {x : ℝ} (hx : 0 < x) : (x : ℂ) ∈ closure rightWedge := by
  have ht : Tendsto (fun s : ℝ => (x : ℂ) + (s : ℂ) * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have : Continuous (fun s : ℝ => (x : ℂ) + (s : ℂ) * I) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hx] with s hs
  exact ⟨by simpa using hs.1, by simpa using hs.2⟩

/-- A negative real is a limit of points of the left wedge (move up). -/
theorem ofReal_mem_closure_leftWedge {x : ℝ} (hx : x < 0) : (x : ℂ) ∈ closure leftWedge := by
  have ht : Tendsto (fun s : ℝ => (x : ℂ) + (s : ℂ) * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have : Continuous (fun s : ℝ => (x : ℂ) + (s : ℂ) * I) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (neg_pos.2 hx)] with s hs
  exact ⟨by simpa using hs.1, by simp; linarith [hs.2]⟩

/-! ### Leaving the sector, and the frozen sides -/

section Sides

variable {K Rγ : Set ℂ}

/-- **Leaving the sector.** For a closed `K` and `w ∈ openSector \ K`, if the component of `w` in `ℍ \ K` is not
contained in its component in `openSector \ K`, some point of the former, in the closure of the latter, lies off the
open sector. -/
theorem exists_exit (hKc : IsClosed K) {w : ℂ} (hw : w ∈ openSector) (hwK : w ∉ K)
    (hnot : ¬ connectedComponentIn (H \ K) w ⊆ connectedComponentIn (openSector \ K) w) :
    ∃ p ∈ connectedComponentIn (H \ K) w,
      p ∈ closure (connectedComponentIn (openSector \ K) w) ∧ p ∉ openSector := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply hnot
  have hAo : IsOpen (connectedComponentIn (openSector \ K) w) :=
    (isOpen_openSector.sdiff hKc).connectedComponentIn
  have hwA : w ∈ connectedComponentIn (openSector \ K) w := mem_connectedComponentIn ⟨hw, hwK⟩
  have hcl : ∀ p ∈ connectedComponentIn (H \ K) w, p ∈ closure (connectedComponentIn (openSector \ K) w) →
      p ∈ connectedComponentIn (openSector \ K) w := by
    intro p hpV hpA
    have hpS : p ∈ openSector := hcon p hpV hpA
    have hpK : p ∉ K := (connectedComponentIn_subset _ _ hpV).2
    have hBo : IsOpen (connectedComponentIn (openSector \ K) p) :=
      (isOpen_openSector.sdiff hKc).connectedComponentIn
    obtain ⟨y, hyB, hyA⟩ := mem_closure_iff.1 hpA _ hBo (mem_connectedComponentIn ⟨hpS, hpK⟩)
    rw [connectedComponentIn_eq hyA, ← connectedComponentIn_eq hyB]
    exact mem_connectedComponentIn ⟨hpS, hpK⟩
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hAo isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)) (fun p hp => ?_)
    ⟨w, mem_connectedComponentIn ⟨openSector_subset_H hw, hwK⟩, hwA⟩
  by_cases hpc : p ∈ closure (connectedComponentIn (openSector \ K) w)
  · exact Or.inl (hcl p hp hpc)
  · exact Or.inr hpc

/-- The closure of a component of `openSector \ K` lies in the closed sector. -/
theorem closure_component_subset (w : ℂ) : closure (connectedComponentIn (openSector \ K) w) ⊆ closedSector :=
  (closure_mono ((connectedComponentIn_subset _ _).trans sdiff_subset)).trans closure_openSector_subset

/-- Under `q`, a component of `openSector \ K` goes into the component of `ℍ \ Rγ`, when `q⁻¹ Rγ ∩ closedSector ⊆ K`. -/
theorem image_component_subset (hRγ : ∀ v ∈ closedSector, sectorInv v ∈ Rγ → v ∈ K) {w : ℂ} (hw : w ∈ openSector)
    (hwK : w ∉ K) :
    sectorInv '' connectedComponentIn (openSector \ K) w ⊆ connectedComponentIn (H \ Rγ) (sectorInv w) := by
  refine (isPreconnected_connectedComponentIn.image _ continuous_sectorInv.continuousOn).subset_connectedComponentIn
    (mem_image_of_mem _ (mem_connectedComponentIn ⟨hw, hwK⟩)) ?_
  rintro _ ⟨v, hv, rfl⟩
  have hv' := connectedComponentIn_subset _ _ hv
  exact ⟨sectorInv_mem_H hv'.1, fun h => hv'.2 (hRγ v (openSector_subset_closedSector hv'.1) h)⟩

/-- An exit point on the boundary rays maps to a real point, off `Rγ`, in the closure of the component of `q w`. -/
theorem exit_real (hRγ : ∀ v ∈ closedSector, sectorInv v ∈ Rγ → v ∈ K) {w : ℂ} (hw : w ∈ openSector)
    (hwK : w ∉ K) {p : ℂ} (hpA : p ∈ closure (connectedComponentIn (openSector \ K) w)) (hpK : p ∉ K)
    (hp : |p.re| = p.im) :
    ((2 * p.re * p.im : ℝ) : ℂ) ∉ Rγ ∧
      ((2 * p.re * p.im : ℝ) : ℂ) ∈ closure (connectedComponentIn (H \ Rγ) (sectorInv w)) := by
  rw [← sectorInv_eq_ofReal hp]
  refine ⟨fun h => hpK (hRγ p (closure_component_subset w hpA) h), ?_⟩
  exact closure_mono (image_component_subset hRγ hw hwK)
    (image_closure_subset_closure_image continuous_sectorInv (mem_image_of_mem _ hpA))

/-- A wedge meeting the closure of a component of `ℍ \ K` at a point of the component lies in it. -/
theorem wedge_subset_component (hKc : IsClosed K) (hKS : K ⊆ closedSector) {W : Set ℂ} (hWc : IsPreconnected W)
    (hWH : W ⊆ H) (hWK : Disjoint W closedSector) {w p : ℂ} (hpV : p ∈ connectedComponentIn (H \ K) w)
    (hpW : p ∈ closure W) : W ⊆ connectedComponentIn (H \ K) w := by
  have hVo : IsOpen (connectedComponentIn (H \ K) w) := (isOpen_H.sdiff hKc).connectedComponentIn
  obtain ⟨y, hyV, hyW⟩ := mem_closure_iff.1 hpW _ hVo hpV
  rw [connectedComponentIn_eq hyV]
  exact hWc.subset_connectedComponentIn hyW fun v hv =>
    ⟨hWH hv, fun hvK => Set.disjoint_left.1 hWK hv (hKS hvK)⟩

/-- An exit point of the component of `w`: it lies in `ℍ \ K` on one of the boundary rays. -/
theorem exit_props {w : ℂ} {p : ℂ}
    (hpV : p ∈ connectedComponentIn (H \ K) w) (hpA : p ∈ closure (connectedComponentIn (openSector \ K) w))
    (hpS : p ∉ openSector) : p ∉ K ∧ |p.re| = p.im ∧ 0 < p.im := by
  have hp' := connectedComponentIn_subset _ _ hpV
  have hpc : |p.re| ≤ p.im := closure_component_subset w hpA
  have hpeq : |p.re| = p.im := le_antisymm hpc (not_lt.1 hpS)
  exact ⟨hp'.2, hpeq, hp'.1⟩

/-- **The right side through `q`.** Let `K` be closed in the closed sector with `q⁻¹ Rγ ∩ closedSector ⊆ K`. A point
`w` of the open sector on the right of `K` is mapped by `q` to the right of `Rγ`, unless it is also on the left of
`K`. -/
theorem sectorInv_mem_rightSideOf_or (hKc : IsClosed K) (hKS : K ⊆ closedSector)
    (hRγ : ∀ v ∈ closedSector, sectorInv v ∈ Rγ → v ∈ K) {w : ℂ} (hw : w ∈ openSector) (hR : w ∈ rightSideOf K) :
    sectorInv w ∈ rightSideOf Rγ ∨ w ∈ leftSideOf K := by
  obtain ⟨⟨hwH, hwK⟩, x, hx0, hxK, hxcl⟩ := hR
  have hnot : ¬ connectedComponentIn (H \ K) w ⊆ connectedComponentIn (openSector \ K) w := fun h =>
    ofReal_notMem_closedSector hx0.ne' (closure_component_subset w (closure_mono h hxcl))
  obtain ⟨p, hpV, hpA, hpS⟩ := exists_exit hKc hw hwK hnot
  obtain ⟨hpK, hpeq, hpim⟩ := exit_props hpV hpA hpS
  rcases lt_trichotomy p.re 0 with hre | hre | hre
  · right
    have hpre : p.re = -p.im := by rw [← hpeq, abs_of_neg hre, neg_neg]
    have hsub := wedge_subset_component hKc hKS convex_leftWedge.isPreconnected leftWedge_subset_H
      disjoint_leftWedge_closedSector hpV (mem_closure_leftWedge hpre hpim)
    exact ⟨⟨hwH, hwK⟩, -1, by norm_num, fun h => ofReal_notMem_closedSector (by norm_num) (hKS h),
      closure_mono hsub (ofReal_mem_closure_leftWedge (by norm_num))⟩
  · rw [hre, abs_zero] at hpeq
    exact absurd hpeq hpim.ne
  · left
    obtain ⟨h1, h2⟩ := exit_real hRγ hw hwK hpA hpK hpeq
    exact ⟨⟨sectorInv_mem_H hw, fun h => hwK (hRγ w (openSector_subset_closedSector hw) h)⟩,
      2 * p.re * p.im, by positivity, h1, h2⟩

/-- **The left side through `q`** (mirror of `sectorInv_mem_rightSideOf_or`). -/
theorem sectorInv_mem_leftSideOf_or (hKc : IsClosed K) (hKS : K ⊆ closedSector)
    (hRγ : ∀ v ∈ closedSector, sectorInv v ∈ Rγ → v ∈ K) {w : ℂ} (hw : w ∈ openSector) (hL : w ∈ leftSideOf K) :
    sectorInv w ∈ leftSideOf Rγ ∨ w ∈ rightSideOf K := by
  obtain ⟨⟨hwH, hwK⟩, x, hx0, hxK, hxcl⟩ := hL
  have hnot : ¬ connectedComponentIn (H \ K) w ⊆ connectedComponentIn (openSector \ K) w := fun h =>
    ofReal_notMem_closedSector hx0.ne (closure_component_subset w (closure_mono h hxcl))
  obtain ⟨p, hpV, hpA, hpS⟩ := exists_exit hKc hw hwK hnot
  obtain ⟨hpK, hpeq, hpim⟩ := exit_props hpV hpA hpS
  rcases lt_trichotomy p.re 0 with hre | hre | hre
  · left
    obtain ⟨h1, h2⟩ := exit_real hRγ hw hwK hpA hpK hpeq
    have hneg : 2 * p.re * p.im < 0 := by nlinarith
    exact ⟨⟨sectorInv_mem_H hw, fun h => hwK (hRγ w (openSector_subset_closedSector hw) h)⟩,
      2 * p.re * p.im, hneg, h1, h2⟩
  · rw [hre, abs_zero] at hpeq
    exact absurd hpeq hpim.ne
  · right
    have hpre : p.re = p.im := by rw [← hpeq, abs_of_pos hre]
    have hsub := wedge_subset_component hKc hKS convex_rightWedge.isPreconnected rightWedge_subset_H
      disjoint_rightWedge_closedSector hpV (mem_closure_rightWedge hpre hpim)
    exact ⟨⟨hwH, hwK⟩, 1, by norm_num, fun h => ofReal_notMem_closedSector (by norm_num) (hKS h),
      closure_mono hsub (ofReal_mem_closure_rightWedge (by norm_num))⟩

end Sides

/-! ### Proper curves through the sector map -/

/-- **A proper curve from `0` in `ℍ̄` becomes a simple proper curve in `ℍ`** under the sector map. -/
theorem isSimpleProper_sectorMap_comp {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) (h0 : γ 0 = 0) :
    Sec7.Lemma71I.IsSimpleProper (sectorMap ∘ γ) := by
  obtain ⟨hc, hi, him, ht⟩ := hγ
  refine ⟨continuousOn_sectorMap.comp_continuous hc him, sectorMap_injective.comp hi, by simp [h0, sectorMap_zero],
    fun t ht0 => sectorMap_mem_H (him t) fun h => ht0.ne' (hi (h.trans h0.symm)), ?_⟩
  have hfun : (fun t => ‖(sectorMap ∘ γ) t‖) = fun t => Real.sqrt ‖γ t‖ := funext fun t => by
    rw [comp_apply, ← norm_sectorMap_sq (γ t), Real.sqrt_sq (norm_nonneg _)]
  rw [hfun]
  exact Real.tendsto_sqrt_atTop.comp ht

theorem isSeedProper_of_isSimpleProper {η : ℝ≥0 → ℂ} (h : Sec7.Lemma71I.IsSimpleProper η) :
    Sec5.Prop55Half.IsSeedProper η :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem isClosed_range_of_isSimpleProper {η : ℝ≥0 → ℂ} (h : Sec7.Lemma71I.IsSimpleProper η) :
    IsClosed (range η) :=
  Sec7.Lemma71I.arcRange_realPath η ▸ (Sec7.Lemma71I.IsSimpleProper.isProperArc h).isClosed_arcRange

theorem disjoint_leftSideOf_rightSideOf_of_isSimpleProper {η : ℝ≥0 → ℂ} (h : Sec7.Lemma71I.IsSimpleProper η) :
    Disjoint (leftSideOf (range η)) (rightSideOf (range η)) :=
  Sec7.Lemma71I.arcRange_realPath η ▸ (Sec7.Lemma71I.IsSimpleProper.isProperArc h).disjoint_leftSideOf_rightSideOf

/-- The range of a proper curve in `ℍ̄` is closed (through the sector map). -/
theorem isClosed_range_of_isProperCurve {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) (h0 : γ 0 = 0) :
    IsClosed (range γ) := by
  have hR := isClosed_range_of_isSimpleProper (isSimpleProper_sectorMap_comp hγ h0)
  have he : range γ = Hbar ∩ sectorMap ⁻¹' range (sectorMap ∘ γ) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨hγ.2.2.1 t, t, rfl⟩
    · rintro ⟨-, t, ht⟩
      exact ⟨t, sectorMap_injective ht⟩
  rw [he]
  exact continuousOn_sectorMap.preimage_isClosed_of_isClosed QuantumZipper.isClosed_Hbar hR

theorem range_sectorMap_comp (γ : ℝ≥0 → ℂ) : range (sectorMap ∘ γ) = sectorMap '' range γ :=
  range_comp sectorMap γ

theorem range_sectorMap_comp_subset {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) :
    range (sectorMap ∘ γ) ⊆ closedSector := by
  rintro _ ⟨t, rfl⟩
  exact sectorMap_mem_closedSector (hγ.2.2.1 t)

/-- The preimage condition of the side lemmas for the image of a set in `ℍ̄`. -/
theorem mem_image_of_sectorInv_mem {S : Set ℂ} {v : ℂ} (hv : v ∈ closedSector) (h : sectorInv v ∈ S) :
    v ∈ sectorMap '' S :=
  ⟨sectorInv v, h, sectorMap_sectorInv hv⟩

/-! ### Components between the walls -/

/-- **The components between two walls go to components between their images.** -/
theorem image_mem_betweenComponents {γR γL : ℝ≥0 → ℂ} (hR : Supp9B.IsProperCurve γR) (hR0 : γR 0 = 0)
    (hL : Supp9B.IsProperCurve γL) (hL0 : γL 0 = 0) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range γR) (range γL)) :
    sectorMap '' C ∈ betweenComponents (range (sectorMap ∘ γR)) (range (sectorMap ∘ γL)) := by
  obtain ⟨z, ⟨hzH, hzRL⟩, hzR, hzL, rfl⟩ := hC
  have hR' := isSimpleProper_sectorMap_comp hR hR0
  have hL' := isSimpleProper_sectorMap_comp hL hL0
  set K := range (sectorMap ∘ γR) ∪ range (sectorMap ∘ γL) with hKdef
  have hKc : IsClosed K := (isClosed_range_of_isSimpleProper hR').union (isClosed_range_of_isSimpleProper hL')
  have hKS : K ⊆ closedSector := union_subset (range_sectorMap_comp_subset hR) (range_sectorMap_comp_subset hL)
  have hKpre : ∀ v ∈ closedSector, sectorInv v ∈ range γR ∪ range γL → v ∈ K := by
    intro v hv h
    rw [hKdef, range_sectorMap_comp, range_sectorMap_comp, ← image_union]
    exact mem_image_of_sectorInv_mem hv h
  have hz'S : sectorMap z ∈ openSector := sectorMap_mem_openSector hzH
  have hz'K : sectorMap z ∉ K := by
    rw [hKdef, range_sectorMap_comp, range_sectorMap_comp, ← image_union]
    rintro ⟨r, hr, hrz⟩
    exact hzRL (sectorMap_injective hrz ▸ hr)
  refine ⟨sectorMap z, ⟨openSector_subset_H hz'S, hz'K⟩, ?_, ?_, ?_⟩
  · intro h
    rcases sectorInv_mem_rightSideOf_or (K := range (sectorMap ∘ γR)) (Rγ := range γR)
      (isClosed_range_of_isSimpleProper hR') (range_sectorMap_comp_subset hR)
      (fun v hv h' => (range_sectorMap_comp γR).symm ▸ mem_image_of_sectorInv_mem hv h') hz'S h with h1 | h1
    · rw [sectorInv_sectorMap] at h1
      exact hzR h1
    · exact Set.disjoint_left.1 (disjoint_leftSideOf_rightSideOf_of_isSimpleProper hR') h1 h
  · intro h
    rcases sectorInv_mem_leftSideOf_or (K := range (sectorMap ∘ γL)) (Rγ := range γL)
      (isClosed_range_of_isSimpleProper hL') (range_sectorMap_comp_subset hL)
      (fun v hv h' => (range_sectorMap_comp γL).symm ▸ mem_image_of_sectorInv_mem hv h') hz'S h with h1 | h1
    · rw [sectorInv_sectorMap] at h1
      exact hzL h1
    · exact Set.disjoint_left.1 (disjoint_leftSideOf_rightSideOf_of_isSimpleProper hL') h h1
  -- the component itself
  have hVA : connectedComponentIn (H \ K) (sectorMap z) ⊆ connectedComponentIn (openSector \ K) (sectorMap z) := by
    by_contra hnot
    obtain ⟨p, hpV, hpA, hpS⟩ := exists_exit hKc hz'S hz'K hnot
    obtain ⟨hpK, hpeq, hpim⟩ := exit_props hpV hpA hpS
    obtain ⟨h1, h2⟩ := exit_real hKpre hz'S hz'K hpA hpK hpeq
    rw [sectorInv_sectorMap] at h2
    have h1R : ((2 * p.re * p.im : ℝ) : ℂ) ∉ range γR := fun h => h1 (Or.inl h)
    have h1L : ((2 * p.re * p.im : ℝ) : ℂ) ∉ range γL := fun h => h1 (Or.inr h)
    rcases lt_trichotomy p.re 0 with hre | hre | hre
    · have hneg : 2 * p.re * p.im < 0 := by nlinarith
      exact hzL ⟨⟨hzH, fun h => hzRL (Or.inr h)⟩, _, hneg, h1L,
        closure_mono (connectedComponentIn_mono _ (sdiff_subset_sdiff_right subset_union_right)) h2⟩
    · rw [hre, abs_zero] at hpeq
      exact hpim.ne hpeq
    · exact hzR ⟨⟨hzH, fun h => hzRL (Or.inl h)⟩, _, by positivity, h1R,
        closure_mono (connectedComponentIn_mono _ (sdiff_subset_sdiff_right subset_union_left)) h2⟩
  apply Subset.antisymm
  · refine (isPreconnected_connectedComponentIn.image _ (continuousOn_sectorMap.mono fun v hv =>
      (le_of_lt ((connectedComponentIn_subset _ _ hv).1 : (0 : ℝ) < v.im)))).subset_connectedComponentIn
      (mem_image_of_mem _ (mem_connectedComponentIn ⟨hzH, hzRL⟩)) ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' := connectedComponentIn_subset _ _ hv
    refine ⟨openSector_subset_H (sectorMap_mem_openSector hv'.1), ?_⟩
    rw [range_sectorMap_comp, range_sectorMap_comp, ← image_union]
    rintro ⟨r, hr, hrv⟩
    exact hv'.2 (sectorMap_injective hrv ▸ hr)
  · intro v hv
    have hvA := hVA hv
    have hv1 : sectorInv v ∈ connectedComponentIn (H \ (range γR ∪ range γL)) z := by
      have := image_component_subset hKpre hz'S hz'K (mem_image_of_mem sectorInv hvA)
      rwa [sectorInv_sectorMap] at this
    exact ⟨sectorInv v, hv1, sectorMap_sectorInv
      (openSector_subset_closedSector (connectedComponentIn_subset _ _ hvA).1)⟩

/-! ### Oriented uniformizers back through the sector map -/

/-- **An oriented uniformizer of the image component gives one of the component.** The uniformizer is `ψ ∘ Φ`; its
inverse is `q ∘ ψ⁻¹`, whose boundary limits are the `q`-images of those of `ψ⁻¹`. -/
theorem hasOrientedUniformizer_of_sectorMap {R L C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H)
    (h : GW3.HasOrientedUniformizer (sectorMap '' R) (sectorMap '' L) (sectorMap '' C)) :
    GW3.HasOrientedUniformizer R L C := by
  obtain ⟨-, -, ψ, hψ, hlim⟩ := h
  have hΦ : IsConformalBijection sectorMap C (sectorMap '' C) :=
    ⟨fun z hz => (differentiableAt_sectorMap (hCH hz)).differentiableWithinAt, sectorMap_injective.injOn.bijOn_image⟩
  have hf := isConformalBijection_comp hψ hΦ
  have heq : EqOn (invFunOn (ψ ∘ sectorMap) C) (sectorInv ∘ invFunOn ψ (sectorMap '' C)) H := by
    intro w hw
    have hex : ∃ a ∈ sectorMap '' C, ψ a = w := hψ.2.surjOn hw
    obtain ⟨z₀, hz₀, hz₀w⟩ := invFunOn_mem hex
    have hψw : ψ (invFunOn ψ (sectorMap '' C) w) = w := invFunOn_eq hex
    rw [comp_apply, ← hz₀w, sectorInv_sectorMap]
    have h1 : (ψ ∘ sectorMap) z₀ = w := by rw [comp_apply, hz₀w, hψw]
    rw [← h1]
    exact hf.2.injOn.leftInvOn_invFunOn hz₀
  refine ⟨hCo, hCH, ψ ∘ sectorMap, hf, fun x => ?_⟩
  obtain ⟨p, hp, hpR, hpL⟩ := hlim x
  refine ⟨sectorInv p, ((continuous_sectorInv.tendsto p).comp hp).congr'
    (eventually_nhdsWithin_of_forall fun w hw => (heq hw).symm), fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := hpR hx
    rwa [sectorInv_sectorMap]
  · obtain ⟨r, hr, rfl⟩ := hpL hx
    rwa [sectorInv_sectorMap]

/-! ### The main theorem -/

/-- A real point `x > 0` goes to the ray of argument `π/4`. -/
theorem sectorMap_ofReal_pos {x : ℝ} (hx : 0 < x) :
    (sectorMap x).re = (sectorMap x).im ∧ 0 < (sectorMap x).im := by
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hH := sectorMap_mem_H hxH (by exact_mod_cast hx.ne')
  have him := sectorInv_im (sectorMap x)
  have hre := sectorInv_re (sectorMap x)
  rw [sectorInv_sectorMap, ofReal_im] at him
  rw [sectorInv_sectorMap, ofReal_re] at hre
  have hH' : (0 : ℝ) < (sectorMap x).im := hH
  have hpos : 0 < (sectorMap x).re := by nlinarith
  refine ⟨?_, hH'⟩
  nlinarith [sq_nonneg ((sectorMap x).re - (sectorMap x).im), sq_nonneg ((sectorMap x).re + (sectorMap x).im)]

/-- **Lemma GW3's geometry for walls that may touch `ℝ`** (deterministic). Let `γR`, `γL` be proper curves from `0` in
`ℍ̄` (continuous, injective, `‖γ t‖ → ∞`), such that `range γR` misses the frozen left side of `range γL`, and every
negative real point of `γR` lies on `γL`. Then every component between `range γR` and `range γL` has an oriented
uniformizer: a conformal map onto `ℍ` whose inverse tends to a point of `range γR` at every positive and to a point of
`range γL` at every negative real point. Proof: the sector map `Φ` turns the walls into simple proper curves in `ℍ`
with the same order and the same between-components (`image_mem_betweenComponents`), where PROVE-ORIENT's
`GW3.hasOrientedUniformizer_of_mem_betweenComponents` applies; `q = Φ⁻¹` carries the uniformizer back. -/
theorem hasOrientedUniformizer_of_touching {γR γL : ℝ≥0 → ℂ} (hR : Supp9B.IsProperCurve γR) (hR0 : γR 0 = 0)
    (hL : Supp9B.IsProperCurve γL) (hL0 : γL 0 = 0) (hd : Disjoint (range γR) (leftSideOf (range γL)))
    (hneg : ∀ x : ℝ, x < 0 → (x : ℂ) ∈ range γR → (x : ℂ) ∈ range γL) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range γR) (range γL)) : GW3.HasOrientedUniformizer (range γR) (range γL) C := by
  have hR' := isSimpleProper_sectorMap_comp hR hR0
  have hL' := isSimpleProper_sectorMap_comp hL hL0
  have hLc' := isClosed_range_of_isSimpleProper hL'
  have hLS' := range_sectorMap_comp_subset hL
  have hLpre : ∀ v ∈ closedSector, sectorInv v ∈ range γL → v ∈ range (sectorMap ∘ γL) := fun v hv h =>
    (range_sectorMap_comp γL).symm ▸ mem_image_of_sectorInv_mem hv h
  have hJ := disjoint_leftSideOf_rightSideOf_of_isSimpleProper hL'
  -- the order of the image walls
  have hd' : Disjoint (range (sectorMap ∘ γR)) (leftSideOf (range (sectorMap ∘ γL))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ hw
    have hHb : γR t ∈ Hbar := hR.2.2.1 t
    rcases (show (0 : ℝ) ≤ (γR t).im from hHb).lt_or_eq with him | him
    · rcases sectorInv_mem_leftSideOf_or hLc' hLS' hLpre (sectorMap_mem_openSector him) hw with h1 | h1
      · rw [sectorInv_sectorMap] at h1
        exact Set.disjoint_left.1 hd ⟨t, rfl⟩ h1
      · exact Set.disjoint_left.1 hJ hw h1
    · have hreal : γR t = ((γR t).re : ℂ) := Complex.ext (by simp) (by simp [him])
      rcases lt_trichotomy (γR t).re 0 with hx | hx | hx
      · have hmem := hneg _ hx (hreal ▸ ⟨t, rfl⟩)
        rw [← hreal] at hmem
        obtain ⟨s, hs⟩ := hmem
        exact hw.1.2 ⟨s, by rw [comp_apply, comp_apply, hs]⟩
      · have h0 : (sectorMap ∘ γR) t = 0 := by
          rw [comp_apply, hreal, hx, ofReal_zero, sectorMap_zero]
        have h1 : (0 : ℝ) < ((sectorMap ∘ γR) t).im := hw.1.1
        rw [h0, zero_im] at h1
        exact lt_irrefl _ h1
      · obtain ⟨hpre, hpim⟩ := sectorMap_ofReal_pos hx
        rw [← hreal] at hpre hpim
        have hsub := wedge_subset_component hLc' hLS' convex_rightWedge.isPreconnected rightWedge_subset_H
          disjoint_rightWedge_closedSector (mem_connectedComponentIn hw.1) (mem_closure_rightWedge hpre hpim)
        exact Set.disjoint_left.1 hJ hw ⟨hw.1, 1, by norm_num,
          fun h => ofReal_notMem_closedSector (by norm_num) (hLS' h),
          closure_mono hsub (ofReal_mem_closure_rightWedge (by norm_num))⟩
  have hLR' := Sec5.Prop55Half.range_subset_closedLeftSide_of_disjoint (isSeedProper_of_isSimpleProper hR')
    (isSeedProper_of_isSimpleProper hL') hd'
  have hU := GW3.hasOrientedUniformizer_of_mem_betweenComponents hR' hL' hLR'
    (image_mem_betweenComponents hR hR0 hL hL0 hC)
  rw [range_sectorMap_comp, range_sectorMap_comp] at hU
  obtain ⟨z, hz, -, -, rfl⟩ := hC
  exact hasOrientedUniformizer_of_sectorMap
    (isOpen_H.sdiff ((isClosed_range_of_isProperCurve hR hR0).union
      (isClosed_range_of_isProperCurve hL hL0))).connectedComponentIn
    (fun v hv => (connectedComponentIn_subset _ _ hv).1) hU

end InteractingSLE.Theorem14.GW3SidedProof
