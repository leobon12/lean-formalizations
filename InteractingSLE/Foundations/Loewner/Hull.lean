import InteractingSLE.Foundations.Loewner.HullExists
import InteractingSLE.Foundations.Harmonic.MaxPrinciple
import QuantumZipper.Proofs.Thm18.A1RPick

/-!
# Compact `ℍ`-hulls, mapping-out functions and half-plane capacity

Design `planning/INFRA-GEO.md` §3–§4, packet GEO-HCAP-A. This module collects the API: it imports
`HullBasic` (definitions, filling, uniqueness) and `HullExists` (existence), and defines the
half-plane capacity. References: G. F. Lawler, *Conformally invariant processes in the plane*, AMS
2005, §3.4 ([Law05]).

## Main definitions

* `HPHull.hcap`: the half-plane capacity, defined from the proved `IsHPHull.existsUnique_hcap`;
* `hcapFill A hA hc`: the capacity of the filling of a bounded `A` with `A ∪ {Im ≤ 0}`
  preconnected (corrected form of the design's `hcapOf`).

## Main results

* `IsHPHull.exists_isMapOut`, `IsMapOut.eqOn`, `IsHPHull.existsUnique_hcap`:
  `z (g_A(z) − z) → hcap(A)`, `hcap(A)` real;
* `IsMapOut.im_le`: `Im g_A(z) ≤ Im z`; `HPHull.hcap_nonneg`;
* `HPHull.hcap_eq_add`: `hcap(B) = hcap(g_A(B \ A)) + hcap(A)`; `HPHull.hcap_mono`;
* `HPHull.hcap_affHomeo`, `hcapFill_affine`: `hcap(rA + x) = r² hcap(A)`;
* `HPHull.hcap_halfDisc`, `HPHull.hcap_le_rad_sq`: `hcap(A) ≤ r²` if `A ⊆ B̄(x, r)`, `x ∈ ℝ`;
* `HPHull.hcap_eq_zero_iff`: `hcap(A) = 0 ↔ A = ∅`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

/-! ### Half-plane capacity -/

/-- The imaginary axis goes to `∞` inside `ℍ \ A`. -/
theorem IsHPHull.tendsto_ofReal_mul_I {A : Set ℂ} (hA : IsHPHull A) :
    Tendsto (fun y : ℝ => (y : ℂ) * I) atTop (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A)) := by
  obtain ⟨R₁, hR₁, hAR₁⟩ := hA.exists_subset_ball
  have hnorm : ∀ y : ℝ, ‖(y : ℂ) * I‖ = |y| := fun y => by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  refine tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 ?_, tendsto_principal.2 ?_⟩
  · simp only [hnorm]
    exact tendsto_abs_atTop_atTop
  · filter_upwards [eventually_gt_atTop R₁] with y hy
    refine ⟨show 0 < ((y : ℂ) * I).im by simp; linarith, fun h => ?_⟩
    have := mem_ball_zero_iff.1 (hAR₁ h)
    rw [hnorm, abs_of_pos (by linarith)] at this
    linarith

theorem IsHPHull.neBot {A : Set ℂ} (hA : IsHPHull A) :
    (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A)).NeBot :=
  hA.tendsto_ofReal_mul_I.neBot

/-- Mapping-out functions of the same hull have the same behaviour at `∞`. -/
theorem IsMapOut.tendsto_congr {A : Set ℂ} {g₁ g₂ : ℂ → ℂ} (hA : IsHPHull A)
    (h₁ : IsMapOut A g₁) (h₂ : IsMapOut A g₂) {L : ℂ}
    (h : Tendsto (fun z => z * (g₁ z - z)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A)) (𝓝 L)) :
    Tendsto (fun z => z * (g₂ z - z)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A)) (𝓝 L) := by
  refine h.congr' ?_
  filter_upwards [mem_inf_of_right (mem_principal_self (H \ A))] with z hz
  rw [IsMapOut.eqOn hA h₁ h₂ hz]

/-- Well-definedness of the half-plane capacity: `g_A(z) = z + hcap(A)/z + o(|z|⁻¹)`
([Law05] §3.4), i.e. `z (g_A(z) − z) → hcap(A)`. -/
theorem IsHPHull.existsUnique_hcap {A : Set ℂ} (hA : IsHPHull A) :
    ∃! a : ℝ, ∀ g, IsMapOut A g →
      Tendsto (fun z => z * (g z - z)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A)) (𝓝 (a : ℂ)) := by
  obtain ⟨g₀, a, hg₀, hT⟩ := hA.exists_isMapOut_tendsto
  refine ⟨a, fun g hg => IsMapOut.tendsto_congr hA hg₀ hg hT, fun a' ha' => ?_⟩
  have := hA.neBot
  exact_mod_cast tendsto_nhds_unique (ha' g₀ hg₀) hT

/-- The **half-plane capacity** of a compact `ℍ`-hull (defined from the proved `∃!`). -/
def HPHull.hcap (A : HPHull) : ℝ :=
  A.2.existsUnique_hcap.choose

theorem HPHull.tendsto_hcap (A : HPHull) {g : ℂ → ℂ} (hg : IsMapOut A.1 g) :
    Tendsto (fun z => z * (g z - z)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A.1)) (𝓝 (A.hcap : ℂ)) :=
  A.2.existsUnique_hcap.choose_spec.1 g hg

/-- The half-plane capacity is the limit of `z (g z − z)` for any mapping-out function `g`. -/
theorem HPHull.hcap_eq_of_tendsto (A : HPHull) {g : ℂ → ℂ} (hg : IsMapOut A.1 g) {a : ℝ}
    (h : Tendsto (fun z => z * (g z - z)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A.1))
      (𝓝 (a : ℂ))) : A.hcap = a :=
  A.2.existsUnique_hcap.unique A.2.existsUnique_hcap.choose_spec.1
    fun _ hg' => IsMapOut.tendsto_congr A.2 hg hg' h

/-- Mapping-out functions are within bounded distance of the identity. -/
theorem IsMapOut.exists_norm_sub_le {A : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A)
    (hg : IsMapOut A g) : ∃ M, ∀ z ∈ H \ A, ‖g z - z‖ ≤ M := by
  obtain ⟨R₀, hR₀⟩ := eventually_cobounded_inf_principal_iff.1
    (hg.2.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos))
  obtain ⟨C, hC⟩ := hg.exists_norm_le hA
  refine ⟨1 + 2 * |R₀| + |C|, fun z hz => ?_⟩
  by_cases hzR : R₀ ≤ ‖z‖
  · have := hR₀ z hz hzR
    rw [dist_zero_right] at this
    linarith [abs_nonneg R₀, abs_nonneg C]
  · rw [not_le] at hzR
    have h1 := hC z hz
    have h2 : ‖g z - z‖ ≤ ‖g z‖ + ‖z‖ := norm_sub_le _ _
    linarith [le_abs_self R₀, le_abs_self C]

/-- **Mapping-out functions lower the height**: `Im g(z) ≤ Im z` on `ℍ \ A` (maximum principle
for the bounded harmonic function `Im(w − g⁻¹(w))` on `ℍ`). -/
theorem IsMapOut.im_le {A : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A) (hg : IsMapOut A g)
    {z : ℂ} (hz : z ∈ H \ A) : (g z).im ≤ z.im := by
  set S := H \ A with hSdef
  have hS : IsOpen S := hA.isOpen
  set e := QuantumZipper.CA.univalentOPH hS hg.1.1 hg.1.2.injOn with he
  have himg : g '' S = H := hg.1.2.image_eq
  have hsd : DifferentiableOn ℂ e.symm H := by
    have := QuantumZipper.CA.differentiableOn_univalentOPH_symm hS hg.1.1 hg.1.2.injOn
    rwa [himg] at this
  have hleft : ∀ z ∈ S, e.symm (g z) = z := fun z hz =>
    QuantumZipper.CA.univalentOPH_symm_apply_apply hS hg.1.1 hg.1.2.injOn hz
  have hright : ∀ w ∈ H, g (e.symm w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hS hg.1.1 hg.1.2.injOn (himg.symm ▸ hw)
  have hsS : ∀ w ∈ H, e.symm w ∈ S := fun w hw => by
    have : w ∈ e.target := by rw [QuantumZipper.CA.univalentOPH_target, himg]; exact hw
    exact e.map_target this
  obtain ⟨M, hM⟩ := hg.exists_norm_sub_le hA
  set f : ℂ → ℝ := fun w => (w - e.symm w).im with hfdef
  have hf : InnerProductSpace.HarmonicOnNhd f H := fun w hw =>
    (analyticAt_id.sub (hsd.analyticAt (QuantumZipper.isOpen_H.mem_nhds hw))).harmonicAt_im
  have hbd : BddAbove (f '' H) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hM _ (hsS w hw)
    rw [hright w hw] at h1
    exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans h1)
  have hfr : ∀ t : ℝ, t ∉ (∅ : Finset ℝ) → ∀ ε > 0, ∀ᶠ w in 𝓝[H] (t : ℂ), f w ≤ ε := by
    intro t _ ε hε
    have hc : Tendsto (fun w : ℂ => w.im) (𝓝[H] (t : ℂ)) (𝓝 (0 : ℝ)) := by
      have := (continuous_im.tendsto (t : ℂ)).mono_left (nhdsWithin_le_nhds (s := H))
      simpa using this
    filter_upwards [hc.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with w hw hwH
    have : 0 < (e.symm w).im := (hsS w hwH).1
    simp only [hfdef, sub_im]
    linarith
  have hle := le_zero_of_harmonicOnNhd_H ∅ hf hbd hfr (g z) (hg.1.2.mapsTo hz)
  simp only [hfdef, sub_im, hleft z hz] at hle
  linarith

/-- **Half-plane capacity is nonnegative** ([Law05] §3.4). -/
theorem HPHull.hcap_nonneg (A : HPHull) : 0 ≤ A.hcap := by
  obtain ⟨g, hg⟩ := A.2.exists_isMapOut
  have hT := (Complex.continuous_re.tendsto _).comp
    ((A.tendsto_hcap hg).comp A.2.tendsto_ofReal_mul_I)
  rw [ofReal_re] at hT
  refine ge_of_tendsto hT ?_
  filter_upwards [A.2.tendsto_ofReal_mul_I.eventually (mem_inf_of_right (mem_principal_self _)),
    eventually_gt_atTop (0 : ℝ)] with y hy hy0
  have h1 := hg.im_le A.2 hy
  simp only [Function.comp_apply, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_im, zero_sub, mul_im, sub_re, add_zero] at h1 ⊢
  nlinarith

/-! ### Composition of mapping-out functions and monotonicity -/

section Comp

variable {A B : Set ℂ} {g : ℂ → ℂ}

/-- `ℍ \ g_A(B \ A) = g_A(ℍ \ B)` for hulls `A ⊆ B`. -/
theorem IsMapOut.H_diff_image (hg : IsMapOut A g) (hAB : A ⊆ B) (hBH : B ⊆ H) :
    H \ g '' (B \ A) = g '' (H \ B) := by
  ext w
  constructor
  · rintro ⟨hw, hwC⟩
    obtain ⟨z, hz, rfl⟩ := hg.1.2.surjOn hw
    refine ⟨z, ⟨hz.1, fun hzB => hwC ⟨z, ⟨hzB, hz.2⟩, rfl⟩⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hzS : z ∈ H \ A := ⟨hz.1, fun h => hz.2 (hAB h)⟩
    refine ⟨hg.1.2.mapsTo hzS, ?_⟩
    rintro ⟨z', hz', hzz'⟩
    have := hg.1.2.injOn ⟨hBH hz'.1, hz'.2⟩ hzS hzz'
    exact hz.2 (this ▸ hz'.1)

/-- The image `g_A(B \ A)` of a larger hull is a hull. -/
theorem IsMapOut.isHPHull_image (hA : IsHPHull A) (hB : IsHPHull B) (hAB : A ⊆ B)
    (hg : IsMapOut A g) : IsHPHull (g '' (B \ A)) := by
  have hBS : B \ A ⊆ H \ A := fun z hz => ⟨hB.1 hz.1, hz.2⟩
  have hHB : H \ B ⊆ H \ A := fun z hz => ⟨hz.1, fun h => hz.2 (hAB h)⟩
  refine ⟨fun w ⟨z, hz, hzw⟩ => hzw ▸ hg.1.2.mapsTo (hBS hz), ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hg.exists_norm_le hA
    obtain ⟨M, hM⟩ := hB.2.1.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨M + C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    linarith [hC z (hBS hz), hM z hz.1]
  · rw [hg.H_diff_image hAB hB.1]
    exact QuantumZipper.CA.isOpen_image_of_injOn hA.isOpen hg.1.1 hg.1.2.injOn hB.isOpen hHB
  · rw [hg.H_diff_image hAB hB.1]
    exact isSimplyConnected_of_isConformalBijection hB.isOpen
      ⟨hg.1.1.mono hHB, (hg.1.2.injOn.mono hHB).bijOn_image⟩ hB.2.2.2

/-- A mapping-out function sends `∞` to `∞` within the complements of larger hulls. -/
theorem IsMapOut.tendsto_cobounded (hA : IsHPHull A) (hg : IsMapOut A g) {S T : Set ℂ}
    (hS : S ⊆ H \ A) (hST : MapsTo g S T) :
    Tendsto g (Bornology.cobounded ℂ ⊓ 𝓟 S) (Bornology.cobounded ℂ ⊓ 𝓟 T) := by
  obtain ⟨M, hM⟩ := hg.exists_norm_sub_le hA
  refine tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 ?_, tendsto_principal.2 ?_⟩
  · refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-M)
      (tendsto_norm_cobounded_atTop.mono_left inf_le_left))
    filter_upwards [mem_inf_of_right (mem_principal_self S)] with z hz
    have h1 := hM z (hS hz)
    have h2 : ‖z‖ ≤ ‖g z - z‖ + ‖g z‖ := by
      calc ‖z‖ = ‖-(g z - z) + g z‖ := by ring_nf
        _ ≤ ‖-(g z - z)‖ + ‖g z‖ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    linarith
  · filter_upwards [mem_inf_of_right (mem_principal_self S)] with z hz
    exact hST hz

/-- `g_C ∘ g_A` maps out `B` when `C = g_A(B \ A)`. -/
theorem IsMapOut.comp (hA : IsHPHull A) (hB : IsHPHull B) (hAB : A ⊆ B) (hg : IsMapOut A g)
    {gC : ℂ → ℂ} (hgC : IsMapOut (g '' (B \ A)) gC) : IsMapOut B (gC ∘ g) := by
  have hHB : H \ B ⊆ H \ A := fun z hz => ⟨hz.1, fun h => hz.2 (hAB h)⟩
  have hbij : BijOn g (H \ B) (H \ g '' (B \ A)) := by
    rw [hg.H_diff_image hAB hB.1]; exact (hg.1.2.injOn.mono hHB).bijOn_image
  refine ⟨isConformalBijection_comp hgC.1 ⟨hg.1.1.mono hHB, hbij⟩, ?_⟩
  have hT := hg.tendsto_cobounded hA hHB hbij.mapsTo
  have h1 := hgC.2.comp hT
  have h2 := hg.2.mono_left (inf_le_inf_left _ (principal_mono.2 hHB))
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr fun z => ?_
  simp only [Function.comp_apply]
  ring

/-- **Composition rule for capacities**: `hcap(B) = hcap(g_A(B \ A)) + hcap(A)`
([Law05] §3.4). -/
theorem HPHull.hcap_eq_add {A B : HPHull} (hAB : A.1 ⊆ B.1) {g : ℂ → ℂ} (hg : IsMapOut A.1 g) :
    B.hcap = HPHull.hcap ⟨g '' (B.1 \ A.1), hg.isHPHull_image A.2 B.2 hAB⟩ + A.hcap := by
  set C : HPHull := ⟨g '' (B.1 \ A.1), hg.isHPHull_image A.2 B.2 hAB⟩ with hCdef
  obtain ⟨gC, hgC⟩ := C.2.exists_isMapOut
  have hcomp : IsMapOut B.1 (gC ∘ g) := hg.comp A.2 B.2 hAB hgC
  have hHB : H \ B.1 ⊆ H \ A.1 := fun z hz => ⟨hz.1, fun h => hz.2 (hAB h)⟩
  have hmaps : MapsTo g (H \ B.1) (H \ C.1) := by
    intro z hz
    rw [show C.1 = g '' (B.1 \ A.1) from rfl, hg.H_diff_image hAB B.2.1]
    exact ⟨z, hz, rfl⟩
  have hT := hg.tendsto_cobounded A.2 hHB hmaps
  have hC := (C.tendsto_hcap hgC).comp hT
  have hA' := (A.tendsto_hcap hg).mono_left (inf_le_inf_left _ (principal_mono.2 hHB))
  -- `z / g z → 1`
  have hzinv : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ B.1)) (𝓝 0) :=
    tendsto_inv₀_cobounded.mono_left inf_le_left
  have hgsub := hg.2.mono_left (inf_le_inf_left _ (principal_mono.2 hHB))
  have hratio : Tendsto (fun z => g z / z) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ B.1)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ))).add (hgsub.mul hzinv)
    rw [zero_mul, add_zero] at this
    refine this.congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    have hz0 : z ≠ 0 := by rintro rfl; exact absurd (show (0 : ℝ) < (0 : ℂ).im from hz.1) (by simp)
    field_simp
    ring
  have hratio' : Tendsto (fun z => z / g z) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ B.1)) (𝓝 1) := by
    have := hratio.inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr fun z => ?_
    simp [inv_div]
  have hsum := (hratio'.mul hC).add hA'
  rw [one_mul] at hsum
  have := B.hcap_eq_of_tendsto hcomp (a := C.hcap + A.hcap) (by
    push_cast
    refine hsum.congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    have hgz0 : g z ≠ 0 := by
      intro h
      have := hg.1.2.mapsTo (hHB hz)
      rw [h] at this
      exact absurd (show (0 : ℝ) < (0 : ℂ).im from this) (by simp)
    simp only [Function.comp_apply]
    field_simp
    ring)
  exact this

/-- **Monotonicity of half-plane capacity** ([Law05] §3.4). -/
theorem HPHull.hcap_mono {A B : HPHull} (hAB : A.1 ⊆ B.1) : A.hcap ≤ B.hcap := by
  obtain ⟨g, hg⟩ := A.2.exists_isMapOut
  rw [HPHull.hcap_eq_add hAB hg]
  linarith [HPHull.hcap_nonneg ⟨g '' (B.1 \ A.1), hg.isHPHull_image A.2 B.2 hAB⟩]

end Comp

/-! ### Affine covariance -/

section Affine

variable {r : ℝ} {x : ℝ}

/-- The real affine map `z ↦ r z + x` (`r > 0`) as a homeomorphism of `ℂ`. -/
def affHomeo (r : ℝ) (hr : 0 < r) (x : ℝ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (r : ℂ) (ofReal_ne_zero.2 hr.ne')).trans (Homeomorph.addRight (x : ℂ))

theorem coe_affHomeo (hr : 0 < r) : ⇑(affHomeo r hr x) = fun z => (r : ℂ) * z + x := rfl

theorem affHomeo_symm_apply (hr : 0 < r) (w : ℂ) :
    (affHomeo r hr x).symm w = (w - x) / r := by
  apply (affHomeo r hr x).injective
  rw [Homeomorph.apply_symm_apply, coe_affHomeo]
  have : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  field_simp
  ring

theorem im_affHomeo (hr : 0 < r) (z : ℂ) : (affHomeo r hr x z).im = r * z.im := by
  simp [coe_affHomeo]

theorem affHomeo_mem_H_iff (hr : 0 < r) {z : ℂ} : affHomeo r hr x z ∈ H ↔ z ∈ H := by
  show 0 < (affHomeo r hr x z).im ↔ 0 < z.im
  rw [im_affHomeo]
  exact ⟨fun h => pos_of_mul_pos_right h hr.le, fun h => mul_pos hr h⟩

theorem image_affHomeo_diff_H (hr : 0 < r) (A : Set ℂ) :
    affHomeo r hr x '' (H \ A) = H \ affHomeo r hr x '' A := by
  rw [image_sdiff (affHomeo r hr x).injective]
  congr 1
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩; exact (affHomeo_mem_H_iff hr).2 hz
  · intro hw
    refine ⟨(affHomeo r hr x).symm w, (affHomeo_mem_H_iff (x := x) hr).1 ?_, by simp⟩
    rwa [Homeomorph.apply_symm_apply]

theorem isBounded_image_affHomeo_iff (hr : 0 < r) {X : Set ℂ} :
    Bornology.IsBounded (affHomeo r hr x '' X) ↔ Bornology.IsBounded X := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 h
    refine isBounded_iff_forall_norm_le.2 ⟨(M + |x|) / r, fun z hz => ?_⟩
    have h1 := hM _ ⟨z, hz, rfl⟩
    rw [coe_affHomeo] at h1
    have h2 : r * ‖z‖ ≤ ‖(r : ℂ) * z + x‖ + |x| := by
      have := norm_sub_le ((r : ℂ) * z + x) (x : ℂ)
      rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    rw [le_div_iff₀ hr]; linarith
  · intro h
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 h
    refine isBounded_iff_forall_norm_le.2 ⟨r * M + |x|, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [coe_affHomeo]
    calc ‖(r : ℂ) * z + x‖ ≤ ‖(r : ℂ) * z‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ = r * ‖z‖ + |x| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_real,
          Real.norm_eq_abs]
      _ ≤ r * M + |x| := by nlinarith [hM z hz]

theorem differentiable_affHomeo (hr : 0 < r) : Differentiable ℂ (affHomeo r hr x) := by
  rw [coe_affHomeo]; fun_prop

/-- Compact `ℍ`-hulls are preserved by `z ↦ r z + x`. -/
theorem IsHPHull.image_affHomeo {A : Set ℂ} (hA : IsHPHull A) (hr : 0 < r) :
    IsHPHull (affHomeo r hr x '' A) := by
  refine ⟨?_, (isBounded_image_affHomeo_iff hr).2 hA.2.1, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩; exact (affHomeo_mem_H_iff hr).2 (hA.1 hz)
  · rw [← image_affHomeo_diff_H]; exact (affHomeo r hr x).isOpenMap _ hA.isOpen
  · rw [← image_affHomeo_diff_H]
    exact isSimplyConnected_of_isConformalBijection hA.isOpen
      ⟨(differentiable_affHomeo hr).differentiableOn,
        ((affHomeo r hr x).injective.injOn).bijOn_image⟩ hA.2.2.2

/-- The mapping-out function of `r A + x` is `w ↦ r g((w − x)/r) + x`. -/
theorem IsMapOut.comp_affHomeo {A : Set ℂ} {g : ℂ → ℂ} (hg : IsMapOut A g) (hr : 0 < r) :
    IsMapOut (affHomeo r hr x '' A)
      (fun w => affHomeo r hr x (g ((affHomeo r hr x).symm w))) := by
  set e := affHomeo r hr x with hedef
  have hS : e '' (H \ A) = H \ e '' A := image_affHomeo_diff_H hr A
  have hsymm : BijOn e.symm (H \ e '' A) (H \ A) := by
    rw [← hS]
    refine ⟨?_, e.symm.injective.injOn, fun z hz => ⟨e z, ⟨z, hz, rfl⟩, by simp⟩⟩
    rintro _ ⟨z, hz, rfl⟩; simpa using hz
  have heH : BijOn e H H := by
    refine ⟨fun z hz => (affHomeo_mem_H_iff hr).2 hz, e.injective.injOn, fun w hw =>
      ⟨e.symm w, (affHomeo_mem_H_iff (x := x) hr).1 (by rwa [Homeomorph.apply_symm_apply]),
        by simp⟩⟩
  have hsymmd : Differentiable ℂ e.symm := by
    have : ⇑e.symm = fun w : ℂ => (w - (x : ℂ)) / (r : ℂ) := funext (affHomeo_symm_apply hr)
    rw [this]; fun_prop
  refine ⟨⟨(differentiable_affHomeo hr).comp_differentiableOn
      (hg.1.1.comp hsymmd.differentiableOn hsymm.mapsTo), heH.comp (hg.1.2.comp hsymm)⟩, ?_⟩
  -- `e(g(ζ)) − e(ζ) = r (g ζ − ζ)`
  have hT : Tendsto e.symm (Bornology.cobounded ℂ ⊓ 𝓟 (H \ e '' A))
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A)) := by
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2
      (mem_inf_of_right (mem_principal.2 fun w hw => hsymm.mapsTo hw))⟩
    have h1 : Tendsto (fun w : ℂ => (w - x) / r) (Bornology.cobounded ℂ)
        (Bornology.cobounded ℂ) := by
      refine tendsto_norm_atTop_iff_cobounded.1 ?_
      have : ∀ w : ℂ, ‖(w - x) / r‖ = ‖w - x‖ / r := fun w => by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      simp only [this]
      refine Tendsto.atTop_div_const hr ?_
      refine tendsto_atTop_mono (fun w => ?_) (tendsto_atTop_add_const_right _ (-‖(x : ℂ)‖)
        tendsto_norm_cobounded_atTop)
      linarith [norm_sub_norm_le w (x : ℂ)]
    have : ⇑e.symm = fun w : ℂ => (w - (x : ℂ)) / (r : ℂ) := funext (affHomeo_symm_apply hr)
    rw [this]
    exact h1.mono_left inf_le_left
  have := (hg.2.comp hT).const_mul (r : ℂ)
  rw [mul_zero] at this
  refine this.congr fun w => ?_
  obtain ⟨ζ, rfl⟩ := e.surjective w
  simp only [Function.comp_apply, hedef, Homeomorph.symm_apply_apply]
  simp only [coe_affHomeo]
  ring

/-- **Affine covariance of half-plane capacity** ([Law05] §3.4): `hcap(r A + x) = r² hcap(A)`. -/
theorem HPHull.hcap_affHomeo (A : HPHull) (hr : 0 < r) :
    HPHull.hcap ⟨affHomeo r hr x '' A.1, A.2.image_affHomeo hr⟩ = r ^ 2 * A.hcap := by
  obtain ⟨g, hg⟩ := A.2.exists_isMapOut
  set e := affHomeo r hr x with hedef
  have hS : e '' (H \ A.1) = H \ e '' A.1 := image_affHomeo_diff_H hr A.1
  have hT : Tendsto e.symm (Bornology.cobounded ℂ ⊓ 𝓟 (H \ e '' A.1))
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A.1)) := by
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (mem_inf_of_right (mem_principal.2 ?_))⟩
    · have : ⇑e.symm = fun w : ℂ => (w - (x : ℂ)) / (r : ℂ) := funext (affHomeo_symm_apply hr)
      rw [this]
      refine (tendsto_norm_atTop_iff_cobounded.1 ?_).mono_left inf_le_left
      have hn : ∀ w : ℂ, ‖(w - x) / r‖ = ‖w - x‖ / r := fun w => by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      simp only [hn]
      refine Tendsto.atTop_div_const hr ?_
      refine tendsto_atTop_mono (fun w => ?_) (tendsto_atTop_add_const_right _ (-‖(x : ℂ)‖)
        tendsto_norm_cobounded_atTop)
      linarith [norm_sub_norm_le w (x : ℂ)]
    · rw [← hS]; rintro _ ⟨z, hz, rfl⟩; simpa using hz
  have h1 := (A.tendsto_hcap hg).comp hT
  have h2 := hg.2.comp hT
  have h3 := (h1.const_mul ((r : ℂ) ^ 2)).add (h2.const_mul ((r : ℂ) * x))
  rw [mul_zero, add_zero] at h3
  refine HPHull.hcap_eq_of_tendsto _ (hg.comp_affHomeo hr) ?_
  push_cast
  refine h3.congr fun w => ?_
  obtain ⟨ζ, rfl⟩ := e.surjective w
  simp only [Function.comp_apply, hedef, Homeomorph.symm_apply_apply]
  simp only [coe_affHomeo]
  ring

/-- The filling commutes with `z ↦ r z + x`. -/
theorem fillH_image_affHomeo (hr : 0 < r) (A : Set ℂ) :
    fillH (affHomeo r hr x '' A) = affHomeo r hr x '' fillH A := by
  set e := affHomeo r hr x with hedef
  have hcl : closure (e '' A) = e '' closure A := (e.image_closure A).symm
  have hF : H \ e '' closure A = e '' (H \ closure A) := (image_affHomeo_diff_H hr _).symm
  have key : ∀ z : ℂ, e z ∈ fillH (e '' A) ↔ z ∈ fillH A := by
    intro z
    simp only [fillH, mem_ofPred_eq]
    rw [affHomeo_mem_H_iff hr, hcl, e.injective.mem_set_image, hF]
    refine and_congr_right fun _ => or_congr_right ?_
    by_cases hz : z ∈ H \ closure A
    · rw [← e.image_connectedComponentIn hz, isBounded_image_affHomeo_iff hr]
    · rw [connectedComponentIn_eq_empty hz,
        connectedComponentIn_eq_empty (by rwa [e.injective.mem_set_image])]
  ext w
  constructor
  · intro hw
    refine ⟨e.symm w, (key _).1 (by simpa using hw), by simp⟩
  · rintro ⟨z, hz, rfl⟩
    exact (key z).2 hz

end Affine

/-! ### Capacity of the filling (corrected `hcapOf`) -/

/-- **Half-plane capacity of the filling** of a bounded set `A` with `A ∪ {Im ≤ 0}` preconnected
(the corrected form of the design's `hcapOf`, which needs this hypothesis: see
`not_isHPHull_fillH_closedBall`). -/
def hcapFill (A : Set ℂ) (hA : Bornology.IsBounded A)
    (hc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) : ℝ :=
  HPHull.hcap ⟨fillH A, isHPHull_fillH_of_isPreconnected hA hc⟩

theorem HPHull.hcap_congr {A B : HPHull} (h : A.1 = B.1) : A.hcap = B.hcap := by
  rw [Subtype.ext h]

/-- **Scaling and translation** ([Law05] §3.4): `hcap(rA + x) = r² hcap(A)` (corrected form of
the design's `hcapOf_affine`). -/
theorem hcapFill_affine {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) {r : ℝ} (hr : 0 < r) (x : ℝ)
    (hA' : Bornology.IsBounded ((fun z => (r : ℂ) * z + x) '' A))
    (hc' : IsPreconnected ((fun z => (r : ℂ) * z + x) '' A ∪ {z : ℂ | z.im ≤ 0})) :
    hcapFill ((fun z => (r : ℂ) * z + x) '' A) hA' hc' = r ^ 2 * hcapFill A hA hc := by
  have he : (fun z => (r : ℂ) * z + x) = ⇑(affHomeo r hr x) := (coe_affHomeo hr).symm
  set K : HPHull := ⟨fillH A, isHPHull_fillH_of_isPreconnected hA hc⟩
  rw [hcapFill, hcapFill, ← HPHull.hcap_affHomeo K hr]
  apply HPHull.hcap_congr
  show fillH ((fun z => (r : ℂ) * z + x) '' A) = affHomeo r hr x '' fillH A
  rw [he, fillH_image_affHomeo]

/-! ### The half-disc and the bound `hcap ≤ r²` -/

/-- The empty set is a compact `ℍ`-hull. -/
theorem isHPHull_empty : IsHPHull ∅ := by
  refine ⟨empty_subset _, Bornology.isBounded_empty, by simpa using QuantumZipper.isOpen_H, ?_⟩
  rw [sdiff_empty]
  have hc : Convex ℝ H := convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0
  have := hc.contractibleSpace ⟨I, show (0 : ℝ) < I.im by simp⟩
  exact SimplyConnectedSpace.ofContractible _

theorem isMapOut_empty_id : IsMapOut ∅ id := by
  refine ⟨⟨differentiableOn_id, by rw [sdiff_empty]; exact bijOn_id H⟩, ?_⟩
  simp only [id, sub_self]
  exact tendsto_const_nhds

/-- The closed half-disc `B̄(0, r) ∩ ℍ`. -/
def halfDisc (r : ℝ) : Set ℂ := closedBall 0 r ∩ H

theorem H_diff_halfDisc (r : ℝ) : H \ halfDisc r = {z | z ∈ H ∧ r < ‖z‖} := by
  ext z
  constructor
  · rintro ⟨hz, hzD⟩
    exact ⟨hz, not_le.1 fun h => hzD ⟨mem_closedBall_zero_iff.2 h, hz⟩⟩
  · rintro ⟨hz, hzr⟩
    exact ⟨hz, fun h => absurd (mem_closedBall_zero_iff.1 h.1) (not_le.2 hzr)⟩

theorem isHPHull_halfDisc {r : ℝ} (hr : 0 < r) : IsHPHull (halfDisc r) := by
  have hU : H \ halfDisc r = H \ closedBall 0 r := by
    rw [H_diff_halfDisc]; ext z; simp
  refine ⟨inter_subset_right, isBounded_closedBall.subset inter_subset_left, ?_, ?_⟩
  · rw [hU]; exact QuantumZipper.isOpen_H.sdiff isClosed_closedBall
  rw [hU]
  set z₀ : ℂ := ((r + 1 : ℝ) : ℂ) * I
  have hT : {w : ℂ | r < w.im} ⊆ connectedComponentIn (H \ closedBall 0 r) z₀ := by
    refine (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear r).isPreconnected
      |>.subset_connectedComponentIn (show r < z₀.im by simp [z₀]) fun w hw => ?_
    have hw' : r < w.im := hw
    refine ⟨show 0 < w.im by linarith, fun h => ?_⟩
    have := mem_closedBall_zero_iff.1 h
    linarith [Complex.abs_im_le_norm w, le_abs_self w.im]
  have hsub : H \ closedBall 0 r ⊆ connectedComponentIn (H \ closedBall 0 r) z₀ := by
    intro z hz
    have hzr : r < ‖z‖ := by
      have := hz.2; rw [mem_closedBall_zero_iff, not_le] at this; exact this
    set R : ℝ := (r + ‖z‖) / 2
    have hR : 0 < R := by positivity
    have hCR : closedBall (0 : ℂ) r ⊆ ball 0 R := closedBall_subset_ball (by simp [R]; linarith)
    have h1 := mem_connectedComponentIn_of_le_norm hR hCR hz.1 (by simp [R]; linarith)
    have h2 : ((R + 1 : ℝ) : ℂ) * I ∈ connectedComponentIn (H \ closedBall 0 r) z₀ :=
      hT (show r < (((R + 1 : ℝ) : ℂ) * I).im by simp [R]; linarith)
    rw [connectedComponentIn_eq h2]
    exact h1
  have hconn : IsConnected (H \ closedBall 0 r) := by
    have hz₀ : z₀ ∈ H \ closedBall 0 r := connectedComponentIn_subset _ _
      (hT (show r < z₀.im by simp [z₀]))
    rw [subset_antisymm hsub (connectedComponentIn_subset _ _)]
    exact isConnected_connectedComponentIn_iff.2 hz₀
  refine isSimplyConnected_of_forall_not_isBounded
    (QuantumZipper.isOpen_H.sdiff isClosed_closedBall) hconn fun a ha => ?_
  set P : Set ℂ := closedBall 0 r ∪ {z : ℂ | z.im ≤ 0}
  have hP : IsPreconnected P := (convex_closedBall (0 : ℂ) r).isPreconnected.union 0
    (mem_closedBall_self hr.le) (show (0 : ℂ).im ≤ 0 by simp) isPreconnected_lowerHalf
  have hPc : P ⊆ (H \ closedBall 0 r)ᶜ := by
    rintro z (hz | hz) ⟨hzH, hzB⟩
    · exact hzB hz
    · exact absurd (show 0 < z.im from hzH) (not_lt.2 hz)
  have haP : a ∈ P := by
    by_contra h
    apply ha
    refine ⟨show 0 < a.im from not_le.1 fun h' => h (Or.inr h'), fun h' => h (Or.inl h')⟩
  intro hb
  exact not_isBounded_lowerHalf
    (hb.subset (subset_union_right.trans (hP.subset_connectedComponentIn haP hPc)))

theorem im_neg_ofReal_div (r : ℝ) (z : ℂ) : (-(r : ℂ) / z).im = r * z.im / normSq z := by
  rw [div_im]; simp; ring

/-- The mapping-out function of the half-disc is `z ↦ z + r²/z`. -/
theorem isMapOut_halfDisc {r : ℝ} (hr : 0 < r) :
    IsMapOut (halfDisc r) (fun z => z + (r : ℂ) ^ 2 / z) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have hz0 : ∀ z ∈ H, z ≠ 0 := fun z hz h => by
    rw [h] at hz; exact absurd (show (0 : ℝ) < (0 : ℂ).im from hz) (by simp)
  set q : ℂ → ℂ := fun z => -(r : ℂ) / z with hqdef
  have hq : BijOn q (H \ halfDisc r) (ball 0 1 ∩ H) := by
    rw [H_diff_halfDisc]
    refine ⟨fun z hz => ⟨?_, ?_⟩, fun z hz z' hz' h => ?_, fun u hu => ?_⟩
    · rw [mem_ball_zero_iff, hqdef, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, div_lt_one (by linarith [hz.2])]
      exact hz.2
    · show 0 < (q z).im
      rw [hqdef, im_neg_ofReal_div]
      exact div_pos (mul_pos hr hz.1) (normSq_pos.2 (hz0 z hz.1))
    · simp only [hqdef] at h
      rw [div_eq_div_iff (hz0 z hz.1) (hz0 z' hz'.1)] at h
      have : (r : ℂ) * (z - z') = 0 := by linear_combination h
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hr0)
    · obtain ⟨hu1, hu2⟩ := hu
      have hu0 : u ≠ 0 := hz0 u hu2
      refine ⟨-(r : ℂ) / u, ⟨?_, ?_⟩, ?_⟩
      · show 0 < (-(r : ℂ) / u).im
        rw [im_neg_ofReal_div]
        exact div_pos (mul_pos hr hu2) (normSq_pos.2 hu0)
      · rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
          lt_div_iff₀ (norm_pos_iff.2 hu0)]
        have := mem_ball_zero_iff.1 hu1
        nlinarith
      · simp only [hqdef]; field_simp
  have hbij : BijOn (fun z => z + (r : ℂ) ^ 2 / z) (H \ halfDisc r) H := by
    have h := (QuantumZipper.CA.bijOn_affine_H (a := 2 * r) (b := 0) (by linarith)).comp
      (bijOn_joukowski.comp hq)
    refine h.congr fun z hz => ?_
    have := hz0 z hz.1
    simp only [Function.comp_apply, hqdef, joukowski]
    push_cast
    field_simp
    ring
  refine ⟨⟨fun z hz => ?_, hbij⟩, ?_⟩
  · exact (differentiableAt_id.add ((differentiableAt_const _).div differentiableAt_id
      (hz0 z hz.1))).differentiableWithinAt
  · have := (tendsto_inv₀_cobounded.mono_left (inf_le_left (b := 𝓟 (H \ halfDisc r)))).const_mul
      ((r : ℂ) ^ 2)
    rw [mul_zero] at this
    refine this.congr fun z => ?_
    simp [div_eq_mul_inv]

theorem HPHull.hcap_halfDisc {r : ℝ} (hr : 0 < r) :
    HPHull.hcap ⟨halfDisc r, isHPHull_halfDisc hr⟩ = r ^ 2 := by
  refine HPHull.hcap_eq_of_tendsto _ (isMapOut_halfDisc hr) ?_
  push_cast
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
  have : z ≠ 0 := fun h => by
    rw [h] at hz; exact absurd (show (0 : ℝ) < (0 : ℂ).im from hz.1) (by simp)
  field_simp
  ring

/-- The inverse of a mapping-out function, as a holomorphic map `ℍ → ℍ \ A`. -/
theorem IsMapOut.exists_symm {A : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A) (hg : IsMapOut A g) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h H ∧ (∀ w ∈ H, h w ∈ H \ A ∧ g (h w) = w) ∧
      ∀ z ∈ H \ A, h (g z) = z := by
  have hS : IsOpen (H \ A) := hA.isOpen
  set e := QuantumZipper.CA.univalentOPH hS hg.1.1 hg.1.2.injOn with he
  have himg : g '' (H \ A) = H := hg.1.2.image_eq
  refine ⟨e.symm, ?_, fun w hw => ⟨?_, ?_⟩, fun z hz => ?_⟩
  · have := QuantumZipper.CA.differentiableOn_univalentOPH_symm hS hg.1.1 hg.1.2.injOn
    rwa [himg] at this
  · have : w ∈ e.target := by rw [QuantumZipper.CA.univalentOPH_target, himg]; exact hw
    exact e.map_target this
  · exact QuantumZipper.CA.univalentOPH_apply_symm_apply hS hg.1.1 hg.1.2.injOn (himg.symm ▸ hw)
  · exact QuantumZipper.CA.univalentOPH_symm_apply_apply hS hg.1.1 hg.1.2.injOn hz

theorem HPHull.hcap_eq_zero_of_eq_empty (A : HPHull) (h : A.1 = ∅) : A.hcap = 0 := by
  have hg : IsMapOut A.1 id := h ▸ isMapOut_empty_id
  refine HPHull.hcap_eq_of_tendsto A hg ?_
  simp only [id, sub_self, mul_zero, ofReal_zero]
  exact tendsto_const_nhds

/-- **`hcap(A) = 0` iff `A = ∅`** ([Law05] §3.4). If `A ≠ ∅`, `φ = g⁻¹ − id` maps `ℍ` into `ℍ`
(it is non-constant with `Im φ ≥ 0`), and the Schwarz–Pick bound
`Im φ(iy) ≥ Im φ(i) · y/(y + 1)²` keeps `y Im φ(iy) → hcap(A)` away from `0`. -/
theorem HPHull.hcap_eq_zero_iff (A : HPHull) : A.hcap = 0 ↔ A.1 = ∅ := by
  refine ⟨fun h0 => ?_, A.hcap_eq_zero_of_eq_empty⟩
  obtain ⟨g, hg⟩ := A.2.exists_isMapOut
  obtain ⟨h, hd, hright, hleft⟩ := hg.exists_symm A.2
  obtain ⟨C, hC⟩ := hg.exists_norm_le A.2
  set φ : ℂ → ℂ := fun w => h w - w with hφdef
  have hφd : DifferentiableOn ℂ φ H := hd.sub differentiableOn_id
  have hφim : ∀ w ∈ H, 0 ≤ (φ w).im := by
    intro w hw
    have := hg.im_le A.2 (hright w hw).1
    rw [(hright w hw).2] at this
    simp only [hφdef, sub_im]; linarith
  -- `h` sends `∞` to `∞`
  have hhT : Tendsto h (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A.1)) := by
    refine tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 ?_, tendsto_principal.2 ?_⟩
    · refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C)
        (tendsto_norm_cobounded_atTop.mono_left inf_le_left))
      filter_upwards [mem_inf_of_right (mem_principal_self H)] with w hw
      have := hC _ (hright w hw).1
      rw [(hright w hw).2] at this
      linarith
    · filter_upwards [mem_inf_of_right (mem_principal_self H)] with w hw
      exact (hright w hw).1
  have hφ0 : Tendsto φ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 0) := by
    have := (hg.2.comp hhT).neg
    rw [neg_zero] at this
    refine this.congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self H)] with w hw
    simp only [Function.comp_apply, hφdef, (hright w hw).2]
    ring
  have hiy : Tendsto (fun y : ℝ => (y : ℂ) * I) atTop (Bornology.cobounded ℂ ⊓ 𝓟 H) := by
    have := isHPHull_empty.tendsto_ofReal_mul_I
    rwa [sdiff_empty] at this
  have hne : (Bornology.cobounded ℂ ⊓ 𝓟 H).NeBot := hiy.neBot
  have hHc : IsPreconnected H :=
    (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).isPreconnected
  have hIH : I ∈ H := show (0 : ℝ) < I.im by simp
  by_cases hzero : ∃ w₀ ∈ H, (φ w₀).im = 0
  · -- `φ` is constant, hence `0`, so `h = id` and `A = ∅`
    obtain ⟨w₀, hw₀, hw₀0⟩ := hzero
    rcases (hφd.analyticOnNhd QuantumZipper.isOpen_H).is_constant_or_isOpen hHc with
      ⟨c, hc⟩ | hopen
    · have hc0 : c = 0 := by
        refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hφ0
        filter_upwards [mem_inf_of_right (mem_principal_self H)] with w hw
        exact (hc w hw).symm
      ext a
      simp only [mem_empty_iff_false, iff_false]
      intro ha
      have haH : a ∈ H := A.2.1 ha
      have h1 := (hright a haH).1
      have h2 : h a = a := by
        have := hc a haH; rw [hc0] at this; simp only [hφdef] at this
        exact sub_eq_zero.1 this
      rw [h2] at h1
      exact h1.2 ha
    · have hO := hopen H subset_rfl QuantumZipper.isOpen_H
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO (φ w₀) ⟨w₀, hw₀, rfl⟩
      obtain ⟨w, hw, hwe⟩ := hball (show φ w₀ - ((ε / 2 : ℝ) : ℂ) * I ∈ ball (φ w₀) ε by
        rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith)
      have := hφim w hw
      rw [hwe] at this
      simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
        hw₀0] at this
      linarith
  · simp only [not_exists, not_and] at hzero
    have hφH : MapsTo φ H H := fun w hw =>
      lt_of_le_of_ne (hφim w hw) (fun h' => hzero w hw h'.symm)
    have hp : 0 < (φ I).im := hφH hIH
    -- `y Im φ(iy) → hcap(A) = 0`
    have hT1 := (A.tendsto_hcap hg).comp (hhT.comp hiy)
    have hφiy := hφ0.comp hiy
    have hratio : Tendsto (fun y : ℝ => (y : ℂ) * I / h ((y : ℂ) * I)) atTop (𝓝 1) := by
      have hinv : Tendsto (fun y : ℝ => ((y : ℂ) * I)⁻¹) atTop (𝓝 0) :=
        tendsto_inv₀_cobounded.comp (hiy.mono_right inf_le_left)
      have := ((tendsto_const_nhds (x := (1 : ℂ))).add (hφiy.mul hinv)).inv₀ (by simp)
      rw [zero_mul, add_zero, inv_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hy0 : (y : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hy.ne') I_ne_zero
      have hh0 : h ((y : ℂ) * I) ≠ 0 := by
        intro h'
        have := (hright _ (show 0 < ((y : ℂ) * I).im by simpa using hy)).1.1
        rw [h'] at this; exact absurd (show (0 : ℝ) < (0 : ℂ).im from this) (by simp)
      have hy0' : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
      simp only [Function.comp_apply, hφdef]
      rw [show (1 : ℂ) + (h ((y : ℂ) * I) - (y : ℂ) * I) * ((y : ℂ) * I)⁻¹ =
        h ((y : ℂ) * I) / ((y : ℂ) * I) by field_simp; ring, inv_div]
    have hT2 := (hT1.mul hratio)
    rw [mul_one, h0, ofReal_zero] at hT2
    have hT3 : Tendsto (fun y : ℝ => y * (φ ((y : ℂ) * I)).im) atTop (𝓝 0) := by
      have := (Complex.continuous_re.tendsto 0).comp hT2
      rw [zero_re] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hyH : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy
      have hh0 : h ((y : ℂ) * I) ≠ 0 := by
        intro h'
        have := (hright _ hyH).1.1
        rw [h'] at this; exact absurd (show (0 : ℝ) < (0 : ℂ).im from this) (by simp)
      simp only [Function.comp_apply, (hright _ hyH).2, hφdef]
      have : h ((y : ℂ) * I) * ((y : ℂ) * I - h ((y : ℂ) * I)) *
          ((y : ℂ) * I / h ((y : ℂ) * I)) = -((y : ℂ) * I) * (h ((y : ℂ) * I) - (y : ℂ) * I) := by
        field_simp; ring
      rw [this]
      simp only [neg_mul, neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_zero, mul_im, zero_mul, sub_im]
      ring
    -- Schwarz–Pick lower bound
    have hSP : ∀ y : ℝ, 0 < y → (φ I).im * (y ^ 2 / (y + 1) ^ 2) ≤ y * (φ ((y : ℂ) * I)).im := by
      intro y hy
      have hyH : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy
      have h1 := QuantumZipper.R18.A1R.im_ge_of_mapsTo_H hφd hφH hyH
      have h2 : ‖(y : ℂ) * I + I‖ ^ 2 = (y + 1) ^ 2 := by
        rw [show (y : ℂ) * I + I = ((y + 1 : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
          Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [h2] at h1
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at h1
      have h3 : (φ I).im * (y ^ 2 / (y + 1) ^ 2) = y * ((φ I).im * y / (y + 1) ^ 2) := by
        field_simp
      rw [h3]
      exact mul_le_mul_of_nonneg_left h1 hy.le
    have hlim : Tendsto (fun y : ℝ => (φ I).im * (y ^ 2 / (y + 1) ^ 2)) atTop
        (𝓝 ((φ I).im * 1)) := by
      refine tendsto_const_nhds.mul ?_
      have : Tendsto (fun y : ℝ => (1 + y⁻¹) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
        ((tendsto_const_nhds.add tendsto_inv_atTop_zero).pow 2)
      have h' := this.inv₀ (by norm_num)
      rw [add_zero, one_pow, inv_one] at h'
      refine h'.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      field_simp
    rw [mul_one] at hlim
    have := le_of_tendsto_of_tendsto hlim hT3
      (eventually_atTop.2 ⟨1, fun y hy => hSP y (by linarith)⟩)
    linarith

/-- **`hcap(A) ≤ r²`** for a hull in the closed disc of radius `r` centred at a real point
([Law05] §3.4: the half-disc has capacity `r²`, and capacity is monotone and translation
invariant). -/
theorem HPHull.hcap_le_rad_sq (A : HPHull) {x r : ℝ} (hA : A.1 ⊆ closedBall (x : ℂ) r) :
    A.hcap ≤ r ^ 2 := by
  rcases le_or_gt r 0 with hr | hr
  · have hAe : A.1 = ∅ := by
      ext a
      simp only [mem_empty_iff_false, iff_false]
      intro ha
      have h1 : dist a x ≤ r := mem_closedBall.1 (hA ha)
      have h2 : a = x := dist_le_zero.1 (h1.trans hr)
      have h3 : 0 < a.im := A.2.1 ha
      rw [h2] at h3; simp at h3
    rw [A.hcap_eq_zero_of_eq_empty hAe]; positivity
  · have h1 := HPHull.hcap_affHomeo A one_pos (x := -x)
    rw [one_pow, one_mul] at h1
    rw [← h1, ← HPHull.hcap_halfDisc hr]
    apply HPHull.hcap_mono
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, (affHomeo_mem_H_iff one_pos).2 (A.2.1 ha)⟩
    rw [mem_closedBall_zero_iff, coe_affHomeo]
    have := mem_closedBall.1 (hA ha)
    rw [dist_eq_norm] at this
    simpa [sub_eq_add_neg] using this

end InteractingSLE
