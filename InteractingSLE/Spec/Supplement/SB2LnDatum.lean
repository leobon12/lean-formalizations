/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LmMirror

/-!
# SB2(2)'s union word datum for the mirrored configuration (deterministic)

Packet PROVE-SB2-LCMEAN, round 2 (route α of the round-1 handoff: the source's physical-coordinates route, supplement
p. 632, "the finite-exception Poisson uniqueness argument identifies the entire mean"). The P-level union-mean engine
(`FinRel.ae_survivingWordBoundaryOn_unionC`, `Union.ae_eqOn_physicalMean_of_boundaryOn`) consumes the deterministic
union word datum `FinRel.HasUnionWordBoundaryOnC`. FIN produces it for SB2(1)'s configuration
(`FinRel.IsRelConfigJK.hasUnionWordBoundaryOnK`). Here it is produced for SB2(2)'s mirrored configuration
`Lm.IsRelConfigJKL`, by reflecting the datum:

* `image_reflectC_connectedComponentIn`, `H_diff_union_image_reflectC`, `ball_eq_image_reflectC`,
  **`mem_freeNear_reflect`**: components, balls and the one-sided `freeNear` sets under `R(z) = −z̄`;
* **`hasUnionWordBoundaryOnC_of_reflect`**: the datum of the reflected data (disc parametrization `ζ ↦ R(f(ζ̄))`,
  chart `R ∘ φ ∘ R`, extension `−G ∘ R`, lift `−L ∘ R`, exceptional set `conj '' E`) gives the datum of the data;
* `relComp_reflect`;
* **`IsRelConfigJKL.hasUnionWordBoundaryOnK`**: the mirrored configuration with the individual-mean formulas gives the
  union word datum on the relative component, in the original picture.

Deterministic; R48-neutral. Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped ComplexConjugate
open QuantumZipper (H fwdMap fwdHull logDerivFwd)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.SB.Ln

open LP (reflectC)
open Sec7.FlowReflect (reflData reflJumps)
open FinRel (freeNear HasUnionWordBoundaryOnC)
open _root_.InteractingSLE.Theorem14.SB.Union (relComp)

/-! ### Components, balls and `freeNear` under the reflection -/

theorem image_reflectC_connectedComponentIn {S : Set ℂ} {z : ℂ} (hz : z ∈ S) :
    reflectC '' connectedComponentIn S z = connectedComponentIn (reflectC '' S) (reflectC z) :=
  LP.reflectHomeo.image_connectedComponentIn hz

theorem H_diff_union_image_reflectC (A B : Set ℂ) :
    H \ (reflectC '' A ∪ reflectC '' B) = reflectC '' (H \ (A ∪ B)) := by
  rw [← image_union, LP.H_diff_reflectC_image]

theorem ball_eq_image_reflectC (p : ℂ) (r : ℝ) : ball p r = reflectC '' ball (reflectC p) r := by
  rw [LP.image_reflectC_ball, LP.reflectC_reflectC]

/-- **`freeNear` under the reflection.** -/
theorem mem_freeNear_reflect {A B : Set ℂ} {p z : ℂ} {r : ℝ}
    (hz : z ∈ freeNear (reflectC '' B) (reflectC '' A) p r) : reflectC z ∈ freeNear B A (reflectC p) r := by
  obtain ⟨hz1, hz2⟩ := hz
  have hT : (H \ reflectC '' A) ∩ ball p r = reflectC '' ((H \ A) ∩ ball (reflectC p) r) := by
    rw [LP.H_diff_reflectC_image, ball_eq_image_reflectC, image_inter LP.reflectC_injective]
  rw [hT] at hz1 hz2
  obtain ⟨y, hy, rfl⟩ := hz1
  rw [LP.reflectC_reflectC]
  refine ⟨hy, ?_⟩
  rw [← image_reflectC_connectedComponentIn hy] at hz2
  exact (disjoint_image_iff LP.reflectC_injective).1 hz2

theorem tendsto_conj_nhdsWithin_ball (q : ℂ) :
    Tendsto (fun ζ : ℂ => conj ζ) (𝓝[ball 0 1] q) (𝓝[ball 0 1] (conj q)) :=
  tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_conj.tendsto q).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun ζ hζ => by simpa using hζ⟩

theorem mem_image_reflectC_union_real {A : Set ℂ} {p : ℂ} (hp : p ∈ reflectC '' A ∪ {z : ℂ | z.im = 0}) :
    reflectC p ∈ A ∪ {z : ℂ | z.im = 0} := by
  rcases hp with ⟨a, ha, rfl⟩ | hp
  · rw [LP.reflectC_reflectC]; exact Or.inl ha
  · exact Or.inr (by simp only [mem_ofPred_eq, LP.im_reflectC]; exact hp)

/-! ### The datum under the reflection -/

/-- **The union word datum of the reflected data gives the datum of the data** (sets `R(·)`, functions `−(·) ∘ R`,
word `y ↦ −b(−y)` with jumps `−J`); the complement of the union is asked to be open (its components then are). -/
theorem hasUnionWordBoundaryOnC_of_reflect {C A₁ A₂ : Set ℂ} {u₀ v w₁ w₂ : ℂ → ℝ} {χ : ℝ} {b : ℝ → ℝ}
    {J : Finset ℝ} (hUo : IsOpen (H \ (A₁ ∪ A₂)))
    (h : HasUnionWordBoundaryOnC (reflectC '' C) (reflectC '' A₁) (reflectC '' A₂) (fun z => -u₀ (reflectC z))
      (fun z => -v (reflectC z)) (fun z => -w₁ (reflectC z)) (fun z => -w₂ (reflectC z)) χ (reflData b)
      (reflJumps J)) :
    HasUnionWordBoundaryOnC C A₁ A₂ u₀ v w₁ w₂ χ b J := by
  intro z₀ hz₀
  obtain ⟨f', φ', G', L', E', hf', hφ', hG', hL', hd', hE', hv', hlim'⟩ := h (reflectC z₀) (mem_image_of_mem _ hz₀)
  set K := connectedComponentIn (H \ (A₁ ∪ A₂)) z₀ with hK
  have hK' : connectedComponentIn (H \ (reflectC '' A₁ ∪ reflectC '' A₂)) (reflectC z₀) = reflectC '' K := by
    by_cases hz : z₀ ∈ H \ (A₁ ∪ A₂)
    · rw [H_diff_union_image_reflectC, hK, image_reflectC_connectedComponentIn hz]
    · rw [H_diff_union_image_reflectC, hK, connectedComponentIn_eq_empty hz, image_empty,
        connectedComponentIn_eq_empty]
      rintro ⟨y, hy, e⟩
      exact hz (LP.reflectC_injective e ▸ hy)
  rw [hK'] at hf' hφ' hL' hd' hv'
  have hKo : IsOpen K := hUo.connectedComponentIn
  have hRKo : IsOpen (reflectC '' K) := Sec7.FlowReflect.isOpen_image_reflectC hKo
  have hRK : ∀ {z}, z ∈ K → reflectC z ∈ reflectC '' K := fun hz => mem_image_of_mem _ hz
  have hRK' : ∀ {y}, y ∈ reflectC '' K → reflectC y ∈ K := by
    rintro _ ⟨z, hz, rfl⟩; rwa [LP.reflectC_reflectC]
  have hball : ∀ {ζ : ℂ}, ζ ∈ ball (0 : ℂ) 1 → conj ζ ∈ ball (0 : ℂ) 1 := fun hζ => by simpa using hζ
  -- the deriv of the reflected chart
  have hdiffφ : ∀ z ∈ K, DifferentiableAt ℂ φ' (reflectC z) := fun z hz =>
    (hφ'.1 _ (hRK hz)).differentiableAt (hRKo.mem_nhds (hRK hz))
  refine ⟨fun ζ => reflectC (f' (conj ζ)), fun z => reflectC (φ' (reflectC z)), fun z => -G' (reflectC z),
    fun z => -L' (reflectC z), (fun q => conj q) '' E', ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- differentiability of the disc parametrization
    intro ζ hζ
    have hd : DifferentiableAt ℂ f' (conj ζ) :=
      (hf'.1 _ (hball hζ)).differentiableAt (isOpen_ball.mem_nhds (hball hζ))
    have h2 := hd.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.neg.differentiableWithinAt
  · intro ζ hζ
    exact hRK' (hf'.2.mapsTo (hball hζ))
  · intro ζ₁ hζ₁ ζ₂ hζ₂ e
    have e1 := hf'.2.injOn (hball hζ₁) (hball hζ₂) (LP.reflectC_injective e)
    simpa using congrArg (fun z => conj z) e1
  · intro z hz
    obtain ⟨ζ', hζ', e⟩ := hf'.2.surjOn (hRK hz)
    refine ⟨conj ζ', hball hζ', ?_⟩
    simp only [Complex.conj_conj, e, LP.reflectC_reflectC]
  · intro z hz
    exact (Theorem14.SB.Lf.differentiableAt_refl_comp (F := φ') (hdiffφ z hz)).differentiableWithinAt
  · intro z hz
    exact Sec7.FlowReflect.reflectC_mem_H (hφ'.2.mapsTo (hRK hz))
  · intro z₁ hz₁ z₂ hz₂ e
    exact LP.reflectC_injective (hφ'.2.injOn (hRK hz₁) (hRK hz₂) (LP.reflectC_injective e))
  · intro w hw
    obtain ⟨y, hy, e⟩ := hφ'.2.surjOn (Sec7.FlowReflect.reflectC_mem_H hw)
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, by simp only [LP.reflectC_reflectC, e]⟩
  · refine Sec7.FlowReflect.IsBoundedHarmonicExtension.reflect hG' fun x hx => ⟨?_, ?_⟩
    · rw [Finset.mem_coe, Sec7.FlowReflect.mem_reflJumps, neg_neg]; exact hx
    · simp only [Sec7.FlowReflect.reflData, neg_neg]
  · exact (hL'.comp LP.continuous_reflectC.continuousOn fun z hz => hRK hz).neg
  · intro z hz
    have hder : deriv (fun w => reflectC (φ' (reflectC w))) z = conj (deriv φ' (reflectC z)) :=
      Theorem14.SB.Lf.deriv_refl_comp (F := φ') (hdiffφ z hz)
    rw [hder, Complex.norm_conj]
    nth_rewrite 1 [hd' _ (hRK hz)]
    rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  · exact hE'.image _
  · intro z hz
    have e := hv' (hRK hz)
    simp only [LP.reflectC_reflectC] at e ⊢
    linarith
  · intro q hq hqE
    have hq' : conj q ∈ sphere (0 : ℂ) 1 := by simpa using hq
    have hqE' : conj q ∉ E' := fun h => hqE ⟨conj q, h, Complex.conj_conj q⟩
    have hconj := tendsto_conj_nhdsWithin_ball q
    rcases hlim' (conj q) hq' hqE' with ⟨p', hp', hpA, ⟨r, hr, hev⟩, hl⟩ | ⟨p', hp', hpA, ⟨r, hr, hev⟩, hl⟩
    · refine Or.inl ⟨reflectC p', (LP.continuous_reflectC.tendsto p').comp (hp'.comp hconj),
        mem_image_reflectC_union_real hpA, ⟨r, hr, (hconj.eventually hev).mono fun ζ hζ => mem_freeNear_reflect hζ⟩,
        ?_⟩
      have h2 := (hl.comp hconj).neg
      rw [neg_zero] at h2
      refine h2.congr fun ζ => ?_
      simp only [Function.comp_apply, LP.reflectC_reflectC]
      ring
    · refine Or.inr ⟨reflectC p', (LP.continuous_reflectC.tendsto p').comp (hp'.comp hconj),
        mem_image_reflectC_union_real hpA, ⟨r, hr, (hconj.eventually hev).mono fun ζ hζ => mem_freeNear_reflect hζ⟩,
        ?_⟩
      have h2 := (hl.comp hconj).neg
      rw [neg_zero] at h2
      refine h2.congr fun ζ => ?_
      simp only [Function.comp_apply, LP.reflectC_reflectC]
      ring

/-! ### The mirrored configuration's datum -/

theorem relComp_reflect (A : Set ℂ) (Ψ : ℂ → ℂ) (Wr : ℝ → ℝ) (u : ℝ) :
    relComp (reflectC '' A) (fun z => reflectC (Ψ (reflectC z))) (-Wr) u = reflectC '' relComp A Ψ Wr u := by
  ext z
  simp only [relComp, mem_ofPred_eq, LP.fwdHull_neg, Lm.reflectC_mem_H_diff_iff, LP.reflectC_reflectC]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨reflectC z, ⟨h1, h2⟩, LP.reflectC_reflectC z⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    simp only [LP.reflectC_reflectC]
    exact ⟨h1, h2⟩

/-- The complement of the union of the retained set and the explored hull of the mirrored configuration is open. -/
theorem IsRelConfigJKL.isOpen_compl_union {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ}
    {η ηr : ℝ → ℂ} {t u χ lam : ℝ} {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G v : ℂ → ℝ}
    (hc : Lm.IsRelConfigJKL A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v) :
    IsOpen (H \ (A ∪ fwdHull w t)) := by
  have ht : 0 ≤ t := FinRel.IsRelConfigJK.ht hc
  have hwc : Continuous w := by simpa using (FinRel.IsRelConfigJK.hw hc).neg
  have hAo : IsOpen (H \ A) := by
    have h1 := Sec7.FlowReflect.isOpen_image_reflectC (FinRel.IsRelConfigJK.chart hc).isOpen
    rwa [LP.H_diff_reflectC_image, Sec7.FlowReflect.reflectC_image_image] at h1
  have e : H \ (A ∪ fwdHull w t) = (H \ A) ∩ (H \ fwdHull w t) := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_union]
    tauto
  rw [e]
  exact hAo.inter (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hwc ht)

/-- **The union word datum of the mirrored configuration** (`FinRel.IsRelConfigJK.hasUnionWordBoundaryOnK` for
`Lm.IsRelConfigJKL`, in the original picture): with the retained-chart formula for `w₁` and the explored-chain formula
for `w₂`, the union `A ∪ K_t` has the union word datum of `βu` on the relative component. -/
theorem IsRelConfigJKL.hasUnionWordBoundaryOnK {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ}
    {η ηr : ℝ → ℂ} {t u χ lam : ℝ} {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G u₀ w₁ w₂ v : ℂ → ℝ}
    (hc : Lm.IsRelConfigJKL A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t)) :
    HasUnionWordBoundaryOnC (relComp A Ψ Wr u) A (fwdHull w t) u₀ v w₁ w₂ χ βu Su := by
  have ht : 0 ≤ t := FinRel.IsRelConfigJK.ht hc
  have hUo : IsOpen (H \ (A ∪ fwdHull w t)) := IsRelConfigJKL.isOpen_compl_union hc
  have hw₁' : EqOn (fun z => -w₁ (reflectC z) + -u₀ (reflectC z))
      (fun z => -G₀ (reflectC (reflectC (Ψ (reflectC z)))) - χ * (conj (LΨ (reflectC z))).im)
      (H \ reflectC '' A) := by
    intro z hz
    have e := hw₁ (Lm.reflectC_mem_H_diff_iff.1 hz)
    simp only [LP.reflectC_reflectC, Complex.conj_im] at e ⊢
    linarith
  have hw₂' : EqOn (fun z => -w₂ (reflectC z) + -u₀ (reflectC z))
      (fun z => -GE (reflectC (fwdMap (-w) t z)) - χ * (logDerivFwd (-w) t z).im) (H \ fwdHull (-w) t) := by
    intro z hz
    rw [LP.fwdHull_neg] at hz
    have e := hw₂ (Lm.reflectC_mem_H_diff_iff.1 hz)
    have e1 : fwdMap (-w) t z = reflectC (fwdMap w t (reflectC z)) := by
      rw [← LP.fwdMap_neg w ht, LP.reflectC_reflectC]
    have e2 : (logDerivFwd (-w) t z).im = -(logDerivFwd w t (reflectC z)).im := by
      rw [← LP.im_logDerivFwd_neg w ht, LP.reflectC_reflectC]
    simp only at e ⊢
    rw [e1, e2, LP.reflectC_reflectC]
    linarith
  have h := FinRel.IsRelConfigJK.hasUnionWordBoundaryOnK hc hw₁' hw₂'
  rw [relComp_reflect, LP.fwdHull_neg] at h
  exact hasUnionWordBoundaryOnC_of_reflect hUo h

end InteractingSLE.Theorem14.SB.Ln
