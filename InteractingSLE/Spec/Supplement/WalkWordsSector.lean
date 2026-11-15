/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsMobius
import InteractingSLE.Spec.Supplement.GW3SidedProofWalk
import InteractingSLE.Spec.Supplement.WalkWordsOrient

/-!
# The walk order of component charts between the boundary walks

Packet PROVE-WALK-WORDS. The walls of the boundary walks may touch `ℝ` (original-real connectors), so PROVE-ORIENT's
pocket chart does not apply to them directly; PROVE-T14-GW8's sector map `Φ(z) = i (−i z)^{1/2}` turns proper curves
from `0` in `ℍ̄` into simple proper curves in `ℍ` with the same order and the same between-components
(`GW3SidedProof.image_mem_betweenComponents`). A chart `g` of a component `C` gives the chart `g ∘ Φ⁻¹` of `Φ(C)`, with
the `Φ`-images of the landings, so the walk order of every chart transfers back:

* **`walkOrder_of_touching`** (deterministic): for proper curves `γR`, `γL` from `0` with `range γR` off the left side
  of `range γL`, every negative real point of `γR` on `γL`, the contact order and no common continuum, every conformal
  bijection of a component between them onto `ℍ` with the component-chart landings has the walk order;
* **`walkComponentWalkOrderStatement_of_walks`**: `WalkComponentWalkOrderStatement` from the named inputs of
  `GW3SidedProof.gw3GeometryRegStatement_of_walks` (the walks proper, GW2a's containment, SB's frontier statement, the
  right walk's negative reals), with the contact order and no common continuum from `WalkBetweenFacts`;
* **`walkComponentOrientationStatement_of_walks`**: hence `WalkComponentOrientationStatement` from these inputs and the
  walk chronology `WalkPieceChronologyStatement` alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Function Metric
open QuantumZipper (H Hbar isOpen_H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkWords

open GW3SidedProof

/-- **The sector images of ordered walls are ordered** (the order step of
`GW3SidedProof.hasOrientedUniformizer_of_touching`): `range (Φ ∘ γL)` lies on the closed left side of `Φ ∘ γR`. -/
theorem range_subset_closedLeftSide_sector {γR γL : ℝ≥0 → ℂ} (hR : Supp9B.IsProperCurve γR) (hR0 : γR 0 = 0)
    (hL : Supp9B.IsProperCurve γL) (hL0 : γL 0 = 0) (hd : Disjoint (range γR) (leftSideOf (range γL)))
    (hneg : ∀ x : ℝ, x < 0 → (x : ℂ) ∈ range γR → (x : ℂ) ∈ range γL) :
    range (sectorMap ∘ γL) ⊆ closedLeftSide (sectorMap ∘ γR) := by
  have hR' := isSimpleProper_sectorMap_comp hR hR0
  have hL' := isSimpleProper_sectorMap_comp hL hL0
  have hLc' := isClosed_range_of_isSimpleProper hL'
  have hLS' := range_sectorMap_comp_subset hL
  have hLpre : ∀ v ∈ closedSector, sectorInv v ∈ range γL → v ∈ range (sectorMap ∘ γL) := fun v hv h =>
    (range_sectorMap_comp γL).symm ▸ mem_image_of_sectorInv_mem hv h
  have hJ := disjoint_leftSideOf_rightSideOf_of_isSimpleProper hL'
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
  exact Sec5.Prop55Half.range_subset_closedLeftSide_of_disjoint (isSeedProper_of_isSimpleProper hR')
    (isSeedProper_of_isSimpleProper hL') hd'

/-- The sector inverse is a conformal bijection of `Φ(C)` onto `C`. -/
theorem isConformalBijection_sectorInv {C : Set ℂ} :
    IsConformalBijection sectorInv (sectorMap '' C) C := by
  refine ⟨fun w _ => (show Differentiable ℂ sectorInv by unfold sectorInv; fun_prop).differentiableAt
    |>.differentiableWithinAt, ⟨?_, ?_, ?_⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    rwa [sectorInv_sectorMap]
  · rintro _ ⟨z, -, rfl⟩ _ ⟨z', -, rfl⟩ h
    rw [sectorInv_sectorMap, sectorInv_sectorMap] at h
    rw [h]
  · intro z hz
    exact ⟨sectorMap z, mem_image_of_mem _ hz, sectorInv_sectorMap z⟩

/-- **The landing map and the walk order of every component chart between walls that may touch `ℝ`**
(deterministic): the inverse chart lands along a continuous injective map `ℓ : ℝ → ℂ`, and the walk order holds. -/
theorem landing_and_walkOrder_of_touching {γR γL : ℝ≥0 → ℂ} (hR : Supp9B.IsProperCurve γR) (hR0 : γR 0 = 0)
    (hL : Supp9B.IsProperCurve γL) (hL0 : γL 0 = 0) (hd : Disjoint (range γR) (leftSideOf (range γL)))
    (hneg : ∀ x : ℝ, x < 0 → (x : ℂ) ∈ range γR → (x : ℂ) ∈ range γL)
    (hco : ∀ s s' t t' : ℝ≥0, γR s = γL t → γR s' = γL t' → (s < s' ↔ t < t'))
    (hnc : ∀ S ⊆ range γR ∩ range γL, IsPreconnected S → S.Subsingleton) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range γR) (range γL)) {g : ℂ → ℂ} (hg : IsConformalBijection g C H)
    (hland : ∀ x : ℝ, ∃ p : ℂ, Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 p) ∧
      (0 < x → p ∈ range γR) ∧ (x < 0 → p ∈ range γL)) :
    (∃ ℓ : ℝ → ℂ, Continuous ℓ ∧ Injective ℓ ∧ ∀ x : ℝ, Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (ℓ x))) ∧
    (∀ (x x' : ℝ) (v v' : ℝ≥0), 0 < x → x < x' → Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (γR v)) →
        Tendsto (invFunOn g C) (𝓝[H] (x' : ℂ)) (𝓝 (γR v')) → v < v') ∧
      (∀ (x x' : ℝ) (v v' : ℝ≥0), x < x' → x' < 0 → Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (γL v)) →
        Tendsto (invFunOn g C) (𝓝[H] (x' : ℂ)) (𝓝 (γL v')) → v' < v) := by
  have hR' := isSimpleProper_sectorMap_comp hR hR0
  have hL' := isSimpleProper_sectorMap_comp hL hL0
  have hLR' := range_subset_closedLeftSide_sector hR hR0 hL hL0 hd hneg
  have hco' : ∀ s s' t t' : ℝ≥0, (sectorMap ∘ γR) s = (sectorMap ∘ γL) t →
      (sectorMap ∘ γR) s' = (sectorMap ∘ γL) t' → (s < s' ↔ t < t') := fun s s' t t' h h' =>
    hco s s' t t' (sectorMap_injective h) (sectorMap_injective h')
  have hnc' : ∀ S ⊆ range (sectorMap ∘ γR) ∩ range (sectorMap ∘ γL), IsPreconnected S → S.Subsingleton := by
    intro S hS hSc
    have hback : ∀ w ∈ S, sectorMap (sectorInv w) = w := fun w hw => by
      obtain ⟨s, hs⟩ := (hS hw).1
      rw [← hs, comp_apply, sectorInv_sectorMap]
    have hsub : sectorInv '' S ⊆ range γR ∩ range γL := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := hS hw
      refine ⟨⟨s, ?_⟩, ⟨t, ?_⟩⟩
      · rw [← hs, comp_apply, sectorInv_sectorMap]
      · rw [← ht, comp_apply, sectorInv_sectorMap]
    have h := hnc _ hsub (hSc.image _ continuous_sectorInv.continuousOn)
    intro w hw w' hw'
    rw [← hback w hw, ← hback w' hw', h (mem_image_of_mem _ hw) (mem_image_of_mem _ hw')]
  have hC' := image_mem_betweenComponents hR hR0 hL hL0 hC
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  have hg' : IsConformalBijection (g ∘ sectorInv) (sectorMap '' C) H :=
    isConformalBijection_comp hg isConformalBijection_sectorInv
  have hinv : ∀ ζ ∈ H, invFunOn (g ∘ sectorInv) (sectorMap '' C) ζ = sectorMap (invFunOn g C ζ) := by
    intro ζ hζ
    have hz := invFunOn_mem (hg.2.surjOn hζ)
    have hz' := invFunOn_mem (hg'.2.surjOn hζ)
    refine hg'.2.injOn hz' (mem_image_of_mem _ hz) ?_
    rw [invFunOn_eq (hg'.2.surjOn hζ), comp_apply, sectorInv_sectorMap, invFunOn_eq (hg.2.surjOn hζ)]
  have htr : ∀ (x : ℝ) (p : ℂ), Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 p) →
      Tendsto (invFunOn (g ∘ sectorInv) (sectorMap '' C)) (𝓝[H] (x : ℂ)) (𝓝 (sectorMap p)) := by
    intro x p hp
    have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ (x : ℂ).im by simp)
    have hev : ∀ᶠ ζ in 𝓝[H] (x : ℂ), invFunOn g C ζ ∈ Hbar := eventually_nhdsWithin_of_forall fun ζ hζ =>
      Sec7.Prop74B.mem_Hbar_of_mem_H (hCH (invFunOn_mem (hg.2.surjOn hζ)))
    have hpH : p ∈ Hbar := QuantumZipper.isClosed_Hbar.mem_of_tendsto hp hev
    exact ((continuousOn_sectorMap p hpH).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hp, hev⟩)).congr'
      (eventually_nhdsWithin_of_forall fun ζ hζ => (hinv ζ hζ).symm)
  have hland' : ∀ x : ℝ, ∃ p : ℂ, Tendsto (invFunOn (g ∘ sectorInv) (sectorMap '' C)) (𝓝[H] (x : ℂ)) (𝓝 p) ∧
      (0 < x → p ∈ range (sectorMap ∘ γR)) ∧ (x < 0 → p ∈ range (sectorMap ∘ γL)) := by
    intro x
    obtain ⟨p, hp, hpR, hpL⟩ := hland x
    refine ⟨sectorMap p, htr x p hp, fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨s, hs⟩ := hpR hx
      exact ⟨s, by rw [comp_apply, hs]⟩
    · obtain ⟨s, hs⟩ := hpL hx
      exact ⟨s, by rw [comp_apply, hs]⟩
  obtain ⟨hoR, hoL⟩ := walkOrder_of_isConformalBijection hR' hL' hLR' hco' hnc' hC' hg' hland'
  obtain ⟨G, lam, hGc, hGi, hlam, hland0, -, -⟩ :=
    exists_ext_of_isConformalBijection hR' hL' hLR' hco' hnc' hC' hg' hland'
  have hxH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hsec : ∀ x : ℝ, G ((lam * x : ℝ) : ℂ) ∈ closedSector := fun x => by
    have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (hxH x)
    refine isClosed_closedSector.mem_of_tendsto (hland0 x) (eventually_nhdsWithin_of_forall fun ζ hζ => ?_)
    obtain ⟨z, hz, hzeq⟩ := invFunOn_mem (hg'.2.surjOn hζ)
    rw [← hzeq]
    exact openSector_subset_closedSector (sectorMap_mem_openSector (hCH hz))
  have hGr : Continuous (fun y : ℝ => G y) :=
    continuousOn_univ.1 (hGc.comp continuous_ofReal.continuousOn fun y _ => hxH y)
  refine ⟨⟨fun x => sectorInv (G ((lam * x : ℝ) : ℂ)), continuous_sectorInv.comp
    (hGr.comp (continuous_const.mul continuous_id)), fun x y h => ?_, fun x => ?_⟩,
    fun x x' v v' hx hxx' hv hv' => hoR x x' v v' hx hxx' (htr x _ hv) (htr x' _ hv'),
    fun x x' v v' hxx' hx' hv hv' => hoL x x' v v' hxx' hx' (htr x _ hv) (htr x' _ hv')⟩
  · have h1 := injOn_sectorInv (hsec x) (hsec y) h
    exact mul_left_cancel₀ hlam.ne' (ofReal_injective (hGi (hxH _) (hxH _) h1))
  · refine ((continuous_sectorInv.tendsto _).comp (hland0 x)).congr'
      (eventually_nhdsWithin_of_forall fun ζ hζ => ?_)
    rw [comp_apply, hinv ζ hζ, sectorInv_sectorMap]

/-- **The walk order of every component chart between walls that may touch `ℝ`** (deterministic). -/
theorem walkOrder_of_touching {γR γL : ℝ≥0 → ℂ} (hR : Supp9B.IsProperCurve γR) (hR0 : γR 0 = 0)
    (hL : Supp9B.IsProperCurve γL) (hL0 : γL 0 = 0) (hd : Disjoint (range γR) (leftSideOf (range γL)))
    (hneg : ∀ x : ℝ, x < 0 → (x : ℂ) ∈ range γR → (x : ℂ) ∈ range γL)
    (hco : ∀ s s' t t' : ℝ≥0, γR s = γL t → γR s' = γL t' → (s < s' ↔ t < t'))
    (hnc : ∀ S ⊆ range γR ∩ range γL, IsPreconnected S → S.Subsingleton) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range γR) (range γL)) {g : ℂ → ℂ} (hg : IsConformalBijection g C H)
    (hland : ∀ x : ℝ, ∃ p : ℂ, Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 p) ∧
      (0 < x → p ∈ range γR) ∧ (x < 0 → p ∈ range γL)) :
    (∀ (x x' : ℝ) (v v' : ℝ≥0), 0 < x → x < x' → Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (γR v)) →
        Tendsto (invFunOn g C) (𝓝[H] (x' : ℂ)) (𝓝 (γR v')) → v < v') ∧
      (∀ (x x' : ℝ) (v v' : ℝ≥0), x < x' → x' < 0 → Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (γL v)) →
        Tendsto (invFunOn g C) (𝓝[H] (x' : ℂ)) (𝓝 (γL v')) → v' < v) :=
  (landing_and_walkOrder_of_touching hR hR0 hL hL0 hd hneg hco hnc hC hg hland).2

/-! ### The boundary walks -/

/-- **Per sample: the landing map and the walk order of a component chart** between two sets `Rs`, `Ls` given as
ranges of complete simple flows, with `Rs` off the left side of `Ls`, every negative real point of `Rs` on `Ls`, the
contact order and no common continuum. -/
theorem chartFacts_of_walls {Rs Ls : Set ℂ} (hd : Disjoint Rs (leftSideOf Ls))
    (hneg : ∀ x : ℝ, x < 0 → (x : ℂ) ∈ Rs → (x : ℂ) ∈ Ls)
    (hnc : ∀ S ⊆ Rs ∩ Ls, IsPreconnected S → S.Subsingleton) {C : Set ℂ} (hC : C ∈ betweenComponents Rs Ls)
    {c : Chart} (hc : IsComponentChart Rs Ls C c) {γR γL : ℝ≥0 → ℂ} (hrR : range γR = Rs)
    (hfR : GB11.IsCompleteSimpleFlow γR) (hrL : range γL = Ls) (hfL : GB11.IsCompleteSimpleFlow γL)
    (hco : ∀ s s' t t' : ℝ≥0, γR s = γL t → γR s' = γL t' → (s < s' ↔ t < t')) :
    (∃ ℓ : ℝ → ℂ, Continuous ℓ ∧ Injective ℓ ∧ ∀ x : ℝ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (ℓ x))) ∧
    (∀ (x x' : ℝ) (v v' : ℝ≥0), 0 < x → x < x' → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (γR v)) →
        Tendsto c.2.1 (𝓝[H] (x' : ℂ)) (𝓝 (γR v')) → v < v') ∧
      (∀ (x x' : ℝ) (v v' : ℝ≥0), x < x' → x' < 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (γL v)) →
        Tendsto c.2.1 (𝓝[H] (x' : ℂ)) (𝓝 (γL v')) → v' < v) := by
  subst hrR hrL
  have hpR : Supp9B.IsProperCurve γR := ⟨hfR.1, hfR.2.1, hfR.2.2.2.1, hfR.2.2.2.2⟩
  have hpL : Supp9B.IsProperCurve γL := ⟨hfL.1, hfL.2.1, hfL.2.2.2.1, hfL.2.2.2.2⟩
  have hg : IsConformalBijection c.1 C H := ⟨hc.1, hc.2.2.2.1.bijOn hc.2.1 hc.2.2.1⟩
  have heq : ∀ ζ ∈ H, invFunOn c.1 C ζ = c.2.1 ζ := fun ζ hζ =>
    hg.2.injOn (invFunOn_mem (hg.2.surjOn hζ)) (hc.2.2.1 hζ)
      ((invFunOn_eq (hg.2.surjOn hζ)).trans (hc.2.2.2.1.2 hζ).symm)
  have hcongr : ∀ (x : ℝ) (p : ℂ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) →
      Tendsto (invFunOn c.1 C) (𝓝[H] (x : ℂ)) (𝓝 p) := fun x p hp =>
    hp.congr' (eventually_nhdsWithin_of_forall fun ζ hζ => (heq ζ hζ).symm)
  have hland : ∀ x : ℝ, ∃ p : ℂ, Tendsto (invFunOn c.1 C) (𝓝[H] (x : ℂ)) (𝓝 p) ∧
      (0 < x → p ∈ range γR) ∧ (x < 0 → p ∈ range γL) := fun x => by
    obtain ⟨p, hp, h1, h2⟩ := hc.2.2.2.2.1 x
    exact ⟨p, hcongr x p hp, h1, h2⟩
  obtain ⟨⟨ℓ, hℓc, hℓi, hℓ⟩, hoR, hoL⟩ :=
    landing_and_walkOrder_of_touching hpR hfR.2.2.1 hpL hfL.2.2.1 hd hneg hco hnc hC hg hland
  refine ⟨⟨ℓ, hℓc, hℓi, fun x => (hℓ x).congr' (eventually_nhdsWithin_of_forall fun ζ hζ => heq ζ hζ)⟩,
    fun x x' v v' hx hxx' hv hv' => hoR x x' v v' hx hxx' (hcongr x _ hv) (hcongr x' _ hv'),
    fun x x' v v' hxx' hx' hv hv' => hoL x x' v v' hxx' hx' (hcongr x _ hv) (hcongr x' _ hv')⟩

/-- **The landing maps of the component charts** (proved conclusion): almost surely, every component chart of a
component between the walks lands along a continuous injective map `ℓ : ℝ → ℂ`. Same hypotheses as
`WalkIntFiber.WalkPhysicalGeometryStatement`. -/
def WalkComponentLandingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkNorm.WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ C ∈ betweenComponents
        (WalkMean.physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (WalkMean.walkRuns κ b jumps E ω).1)
        (WalkMean.physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (WalkMean.walkRuns κ b jumps E ω).2),
        ∀ c : Chart, IsComponentChart
          (WalkMean.physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (WalkMean.walkRuns κ b jumps E ω).1)
          (WalkMean.physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (WalkMean.walkRuns κ b jumps E ω).2)
          C c →
        ∃ ℓ : ℝ → ℂ, Continuous ℓ ∧ Injective ℓ ∧ ∀ x : ℝ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (ℓ x))

/-- The per-sample wall facts `hd`, `hneg` of `GW3SidedProof.gw3GeometryRegStatement_of_walks`, almost surely, together
with `WalkBetweenFacts`. -/
theorem ae_wallFacts (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : RightWalkNegRealRegStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec)) :
    ∀ᵐ ω ∂P, Disjoint (WalkMean.physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (WalkMean.walkRuns κ b jumps E ω).1)
        (leftSideOf (WalkMean.physOf (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (WalkMean.walkRuns κ b jumps E ω).2)) ∧
      ∀ x : ℝ, x < 0 →
        (x : ℂ) ∈ WalkMean.physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (WalkMean.walkRuns κ b jumps E ω).1 →
        (x : ℂ) ∈ WalkMean.physOf (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (WalkMean.walkRuns κ b jumps E ω).2 := by
  have hpi := Real.pi_pos
  have hRA := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg, hRA,
    hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hPRω hPLω hRAω hFω hNRω
  obtain ⟨γR₀, hγR₀, -, hγR₀r⟩ := hPRω
  obtain ⟨γL₀, hγL₀, hγL₀0, hγL₀r⟩ := hPLω
  have hRK : range γR₀ ⊆ counterflowCompletedRange (fun t => W' t ω₀) := hγR₀r ▸ hRAω
  have hKL := hFω.2
  rw [← hγL₀r] at hKL
  have hd₀ : Disjoint (range γR₀) (leftSideOf (range γL₀)) := by
    rw [Set.disjoint_left]
    intro z hzR hzL
    exact (Set.eq_empty_iff_forall_notMem.1 hKL) z ⟨hRK hzR, hzL⟩
  have hneg₀ := neg_real_mem_of_frontier hγR₀ (isClosed_range_of_isProperCurve hγL₀ hγL₀0) hRK hKL
    (hγR₀r ▸ hNRω)
  rw [hγR₀r, hγL₀r] at hd₀
  rw [hγR₀r, hγL₀r] at hneg₀
  exact ⟨hd₀, hneg₀⟩

/-- **`WalkComponentWalkOrderStatement`** from the named inputs of `GW3SidedProof.gw3GeometryRegStatement_of_walks`
(both walks proper curves from `0`, GW2a's containment, SB's frontier statement, the right walk's negative reals); the
contact order and no common continuum come from `WalkBetweenFacts`. -/
theorem walkComponentWalkOrderStatement_of_walks (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : RightWalkNegRealRegStatement.{u}) :
    WalkComponentWalkOrderStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg hdrv hfacts
  filter_upwards [ae_wallFacts hPR hPL hA hF hNR hκ hκ4 hb hh hcf hζ' hE hreg, hfacts] with ω₀ hw hfω
  obtain ⟨hpf, -, hnc, -⟩ := hfω
  intro C hC c hc γR γL hrR hfR hrL hfL
  exact (chartFacts_of_walls hw.1 hw.2 hnc hC hc hrR hfR hrL hfL (hpf.2.2 γR γL hrR hrL hfR hfL)).2

/-- **`WalkComponentLandingStatement`** from the same named inputs. -/
theorem walkComponentLandingStatement_of_walks (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : RightWalkNegRealRegStatement.{u}) :
    WalkComponentLandingStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg hdrv hfacts
  filter_upwards [ae_wallFacts hPR hPL hA hF hNR hκ hκ4 hb hh hcf hζ' hE hreg, hfacts] with ω₀ hw hfω
  obtain ⟨hpf, -, hnc, -⟩ := hfω
  obtain ⟨⟨γR, hγR, hγR0, hrR⟩, ⟨γL, hγL, hγL0, hrL⟩, hco⟩ := hpf
  have hfR : GB11.IsCompleteSimpleFlow γR := ⟨hγR.1, hγR.2.1, hγR0, hγR.2.2.1, hγR.2.2.2⟩
  have hfL : GB11.IsCompleteSimpleFlow γL := ⟨hγL.1, hγL.2.1, hγL0, hγL.2.2.1, hγL.2.2.2⟩
  intro C hC c hc
  exact (chartFacts_of_walls hw.1 hw.2 hnc hC hc hrR hfR hrL hfL (hco γR γL hrR hrL hfR hfL)).1

/-- **`WalkComponentOrientationStatement`** from the walk chronology and the named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks`. -/
theorem walkComponentOrientationStatement_of_walks (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : RightWalkNegRealRegStatement.{u})
    (hch : WalkPieceChronologyStatement.{u}) : WalkComponentOrientationStatement.{u} :=
  walkComponentOrientationStatement_of_walkOrder (walkComponentWalkOrderStatement_of_walks hPR hPL hA hF hNR) hch

end InteractingSLE.Theorem14.WalkWords
