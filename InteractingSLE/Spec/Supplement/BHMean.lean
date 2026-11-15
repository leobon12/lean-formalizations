/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BHMeanSide

/-!
# The boundary-hitting mean identification: assembly

Packet PROVE-BHMEAN. The union prime-end datum `HasUnionWordBoundary A K_t u₀ v w₁ w₂ χ βu Su` of
`RelUnionWordBoundaryStatement`, from the transition facts `RelTransition` on the relative hull image:

* the joint complement is one component, parametrized by `Ψi ∘ f̃_u⁻¹ ∘ cayleyInv` (`BHMeanChart`);
* the exceptional set is finite: `1` (the point `∞` of the joint chart, the retained tip) and the Cayley images of `0`
  (the relative tip), the jumps of `βu`, the real flow of the retained jumps, and the points of the relative hull image
  sent by the transition to a jump of `βE`;
* at every other boundary point `q`, `x = cayleyInv q` is real; off the relative hull image the retained side
  applies (`retained_side`), on it the explored side (`explored_side`).

Main results: **`hasUnionWordBoundary_of_relTransition`**; **`RelTransitionStatement`** (the transition facts in the
setting of `RelUnionWordBoundaryStatement`, the one remaining input) and
**`relUnionWordBoundaryStatement_of_transition`**.

Deterministic. Conditional helpers with distinct names; they replace no source theorem. R48: serves Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Supp8.BHMean

open Theorem14.SB.SewGerm (HasUnionWordBoundary)

/-- At time `0` the boundary extension of the inverse map is the identity. -/
theorem extendFrom_fwdMapInv_zero {Wr : ℝ → ℝ} (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) {z : ℂ} (hz : z ∈ Hbar) :
    extendFrom H (fwdMapInv Wr 0) z = z := by
  have h : Tendsto (fwdMapInv Wr 0) (𝓝[H] z) (𝓝 z) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun w hw =>
      (fwdMapInv_zero_time hWr hWr0 hw).symm)
  exact extendFrom_eq (by rw [closure_H]; exact hz) h

/-- The Cayley inverse at a boundary point `q ≠ 1` of the disc is a real point, approached from `ℍ`. -/
theorem tendsto_cayleyInv_sphere {q : ℂ} (hq : q ∈ sphere (0 : ℂ) 1) (hq1 : q ≠ 1) :
    cayleyInv q = ((cayleyInv q).re : ℂ) ∧
      Tendsto cayleyInv (𝓝[ball 0 1] q) (𝓝[H] ((cayleyInv q).re : ℂ)) := by
  have hnorm : ‖q‖ = 1 := by simpa using hq
  have him : (cayleyInv q).im = 0 := by rw [QuantumZipper.CA.im_cayleyInv, hnorm]; simp
  have hre : cayleyInv q = ((cayleyInv q).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  refine ⟨hre, tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ζ hζ =>
    QuantumZipper.CA.cayleyInv_mem_H hζ⟩⟩
  have hc : ContinuousAt cayleyInv q :=
    QuantumZipper.CA.continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hq1)
  rw [← hre]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

section Assembly

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ}
  {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G u₀ w₁ w₂ v : ℂ → ℝ}

/-- **The union word boundary datum of the relative configuration, from the transition facts.** -/
theorem hasUnionWordBoundary_of_relTransition (hΨ : IsRetainedChart A Ψ Ψi LΨ)
    (hw : Continuous w) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hG₀ : IsBoundedHarmonicExtension β₀ S₀ G₀) (hGE : IsBoundedHarmonicExtension βE SE GE)
    (hG : IsBoundedHarmonicExtension βu Su G)
    (hsE : IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam)
    (hsu : IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam)
    (hflow : IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u))
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t))
    (hv : ∀ z, v z = G (fwdMap Wr u (Ψ z)) - χ * ((logDerivFwd Wr u (Ψ z)).im + (LΨ z).im))
    (hT : RelTransition Ψ Ψi LΨ w Wr t u) :
    HasUnionWordBoundary A (fwdHull w t) u₀ v w₁ w₂ χ βu Su := by
  obtain ⟨T, hTinj, hTx⟩ := hT
  set R' : Set ℝ := {x : ℝ | x ≠ 0 ∧ extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u)} with hR'
  set φ : ℝ → ℝ := fun s => (fwdMap Wr u (s : ℂ)).re with hφ
  set X : Set ℝ := insert 0 ((↑Su : Set ℝ) ∪ φ '' (↑S₀ : Set ℝ) ∪ (R' ∩ T ⁻¹' (↑SE : Set ℝ))) with hX
  have hXf : X.Finite := by
    refine Set.Finite.insert _ (((Su.finite_toSet).union ((S₀.finite_toSet).image φ)).union ?_)
    refine Set.Finite.of_finite_image ((SE.finite_toSet).subset ?_) (hTinj.mono inter_subset_left)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  set E : Set ℂ := insert (1 : ℂ) ((fun x : ℝ => cayley (x : ℂ)) '' X) with hE
  have hEf : E.Finite := (hXf.image _).insert _
  intro z₀ hz₀
  rw [connectedComponentIn_C hΨ hw ht hWr hWr0 hu hK hd hz₀]
  refine ⟨fun ζ => jointInv Ψi Wr u (cayleyInv ζ), jointFwd Ψ Wr u, G, jointLift Ψ LΨ Wr u, E,
    isConformalBijection_diskInv hΨ hw ht hWr hWr0 hu hK hd, isConformalBijection_jointFwd hΨ hw ht hWr hWr0 hu hK hd,
    hG, continuousOn_jointLift hΨ hw ht hWr hWr0 hu hK hd,
    fun z hz => deriv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz, hEf, fun z _ => hv z, ?_⟩
  intro q hq hqE
  have hq1 : q ≠ 1 := fun h => hqE (h ▸ mem_insert _ _)
  obtain ⟨hre, hcay⟩ := tendsto_cayleyInv_sphere hq hq1
  set x : ℝ := (cayleyInv q).re with hxdef
  have hxX : x ∉ X := fun hx => hqE (mem_insert_of_mem _ ⟨x, hx, by
    simp only
    rw [← hre, QuantumZipper.CA.cayley_cayleyInv hq1]⟩)
  have hx0 : x ≠ 0 := fun h => hxX (h ▸ mem_insert _ _)
  have hxS : x ∉ Su := fun h => hxX (mem_insert_of_mem _ (Or.inl (Or.inl h)))
  by_cases hxK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u)
  · -- the explored side
    obtain ⟨hsign, hT0, hTK, hTl, hLl⟩ := hTx x hx0 hxK
    have hTS : T x ∉ SE := fun h => hxX (mem_insert_of_mem _ (Or.inr ⟨⟨hx0, hxK⟩, h⟩))
    obtain ⟨p, hp, hpK, hr, hlim⟩ := explored_side hΨ hw ht hWr hWr0 hηr hu hK hd hGE hG hsE hsu hw₂ hx0 hxK hxS
      hTS hsign hT0 hTK hTl hLl
    exact Or.inr ⟨p, hp.comp hcay, hpK, hr, hlim.comp hcay⟩
  · -- the retained side
    have hyS : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ S₀ := by
      intro hS
      have hyim := im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hxK
      have hre0 : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ≠ 0 := by
        intro h0
        have hy0 : extendFrom H (fwdMapInv Wr u) (x : ℂ) = 0 := Complex.ext h0 hyim
        rcases hu.eq_or_lt with rfl | hpos
        · rw [extendFrom_fwdMapInv_zero hWr hWr0 (show (0 : ℝ) ≤ (x : ℂ).im by simp)] at hy0
          exact hx0 (by exact_mod_cast hy0)
        · exact hxK (hy0 ▸ ConformalImageFull.zero_mem_closure_fwdHull hWr hWr0 hpos)
      have hxφ := eq_fwdMap_of_extendFrom_notMem_closure hηr hWr hWr0 hu hxK hre0
      exact hxX (mem_insert_of_mem _ (Or.inl (Or.inr ⟨_, hS, hxφ.symm⟩)))
    obtain ⟨p, hp, hpA, hr, hlim⟩ := retained_side hΨ hw ht hWr hWr0 hηr hu hK hd hG₀ hG hflow hw₁ hxS hxK hyS
    exact Or.inl ⟨p, hp.comp hcay, hpA, hr, hlim.comp hcay⟩

end Assembly

/-- **The transition facts of the relative configuration** (the geometric input of the explored side, in the setting
of `RelUnionWordBoundaryStatement`). -/
def RelTransitionStatement : Prop :=
  ∀ (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (w Wr : ℝ → ℝ) (η ηr : ℝ → ℂ) (t u : ℝ),
    IsRetainedChart A Ψ Ψi LΨ →
    Continuous w → w 0 = 0 → IsLoewnerTrace w η → 0 ≤ t →
    Continuous Wr → Wr 0 = 0 → IsLoewnerTrace Wr ηr → 0 ≤ u →
    Ψ '' fwdHull w t = fwdHull Wr u →
    Disjoint (closure (fwdHull w t)) (closure A) →
    Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0) →
    RelTransition Ψ Ψi LΨ w Wr t u

/-- **The boundary-hitting mean identification from the transition facts.** -/
theorem relUnionWordBoundaryStatement_of_transition (hT : RelTransitionStatement) :
    RelUnionWordBoundaryStatement := by
  intro A Ψ Ψi LΨ w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G u₀ w₁ w₂ v hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd
    htip hG₀ hGE hG hsE hsu hflow hw₁ hw₂ hv
  exact hasUnionWordBoundary_of_relTransition hΨ hw ht hWr hWr0 hηr hu hK hd hG₀ hGE hG hsE hsu hflow hw₁ hw₂ hv
    (hT A Ψ Ψi LΨ w Wr η ηr t u hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd htip)

end InteractingSLE.Supp8.BHMean
