/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.MeanIdentChamber
import InteractingSLE.WangWu.UnboundedComponent
import InteractingSLE.Spec.Sec6.Prop61BMarked
import InteractingSLE.Foundations.Topology.Schoenflies.Disc

/-!
# Wang–Wu Proposition 4.20: the conditional mean in each chamber between ordered seed lines

Packet PROVE-WW-B6. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.4,
Proposition 4.20 (p. 29, text dump L1701–1745):

> In each component between them, the conditional mean of `h` is the bounded harmonic function with values
> `λ − u₂` on the right side of `γ_{u₂}`, `−λ − u₁` on the left side of `γ_{u₁}`. (D2)
>
> *Proof.* … A component between two ordered simple arcs is bounded by one subarc of each, with common endpoints and
> disjoint interiors. … It is a Jordan domain in the sphere. In particular, the two possible exceptions to the boundary
> identification are precisely its opening and closing prime ends. … The bounded harmonic extension of the values in
> (D2) is a candidate with the same boundary limits outside those two prime ends. Apply Corollary 4.8 to identify the
> mean with this candidate, including the exclusion of all singular endpoint contributions.

PROVE-WW-B5 proved the locality of the union and the wall values (`ae_tendsto_unionMean_between`). This file proves the
final identification:

* `exists_chamber_chart` (deterministic): every component `C` between two ordered simple proper arcs `R` (right wall)
  and `L` (left wall) has a **conformal chart** `f : 𝔻 → C` such that, outside a finite set `E` of circle points (the
  preimages of the opening and closing points), `f(ζ)` tends, as `ζ → q` in `𝔻`, to a wall point `R(s)` off `L` or to a
  wall point `L(s)` off `R` (`s > 0`). In the disc coordinates of the walls `C` is the pocket of a contact gap
  (`exists_contactGap_of_mem_betweenComponents`, PROVE-WW-B4), a bounded Jordan domain; the closed-disc Schoenflies
  theorem (`Foundations.Schoenflies.schoenflies_disc`: Carathéodory's homeomorphism, continuous and injective on the
  closed disc) gives its Riemann map, and `f` is that map followed by the inverse Cayley map.
* **`ae_eqOn_chamber`** (Proposition 4.20, identification of the chamber mean): almost surely the union mean has a
  harmonic representative `w` on `ℍ \ (R ∪ L)` such that on every component `C` between the walls, `w` equals every
  bounded harmonic function `v` on `C` with the (D2) limits `ℓ_R(R(s))` at the right-wall points and `ℓ_L(L(s))` at the
  left-wall points off the other wall — Corollary 4.8 for every component (`ae_eqOn_of_condMean_global`, bounded or
  not), with the two corners as the finite exceptional set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.LocalSets

universe u

namespace InteractingSLE.WangWu

/-! ### The conformal chart of a chamber -/

section Chart

variable {R L : ℝ → ℂ}

/-- A crosscut point at a time of `(0, 1)` is the Cayley image of the arc at a positive time. -/
theorem toDisc_eq_cayley_arcTime {γ : ℝ → ℂ} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    toDisc γ s = cayley (γ (arcTime s)) ∧ 0 < arcTime s :=
  ⟨toDisc_of_lt hs.2, arcTime_pos hs⟩

/-- The limit of `cayleyInv ∘ φ` at a circle point whose image is a crosscut point at a time of `(0, 1)`. -/
theorem tendsto_cayleyInv_comp {γ : ℝ → ℂ} (hγ : IsProperArc γ) {φ : ℂ → ℂ}
    (hφc : ContinuousOn φ (closedBall 0 1)) {q : ℂ} (hq : q ∈ sphere (0 : ℂ) 1) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hφq : φ q = toDisc γ s) :
    Tendsto (cayleyInv ∘ φ) (𝓝[ball 0 1] q) (𝓝 (γ (arcTime s))) := by
  obtain ⟨e, ht⟩ := toDisc_eq_cayley_arcTime (γ := γ) hs
  have hz : γ (arcTime s) ∈ Hbar := hγ.mem_Hbar ht.le
  have h1 : Tendsto φ (𝓝[ball 0 1] q) (𝓝 (φ q)) :=
    (hφc q (sphere_subset_closedBall hq)).tendsto.mono_left (nhdsWithin_mono _ ball_subset_closedBall)
  rw [hφq, e] at h1
  have h2 := (continuousAt_cayleyInv (cayley_ne_one_of_Hbar hz)).tendsto.comp h1
  rwa [cayleyInv_cayley_of_mem_Hbar hz] at h2

/-- **The conformal chart of a chamber.** Let `R` (right wall) and `L` (left wall) be simple proper arcs of `ℍ` with
`L` avoiding the right side of `R`, and `C` a component between them. There is a conformal bijection `f : 𝔻 → C` and
a finite set `E` of circle points such that at every other circle point `q`, `f(ζ)` tends (as `ζ → q` in `𝔻`) to a
point `R(s)` of the right wall off the left wall, or to a point `L(s)` of the left wall off the right wall, `s > 0`. -/
theorem exists_chamber_chart (hR : IsProperArc R) (hL : IsProperArc L)
    (hord : Disjoint (arcRange L) (rightSideOf (arcRange R))) {C : Set ℂ}
    (hC : C ∈ betweenComponents (arcRange R) (arcRange L)) :
    ∃ f : ℂ → ℂ, IsConformalBijection f (ball 0 1) C ∧ ∃ E : Set ℂ, E.Finite ∧
      ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        (∃ s > 0, R s ∉ arcRange L ∧ Tendsto f (𝓝[ball 0 1] q) (𝓝 (R s))) ∨
          (∃ s > 0, L s ∉ arcRange R ∧ Tendsto f (𝓝[ball 0 1] q) (𝓝 (L s))) := by
  obtain ⟨a, b, hg, hCe⟩ := exists_contactGap_of_mem_betweenComponents hR hL hord hC
  have hα := hR.isDiscCrosscut_toDisc
  have hβ := hL.isDiscCrosscut_toDisc
  have hord' := (disjoint_rightSideOf_iff hR hL).1 hord
  obtain ⟨hJ, hJball, -, -, w, hw, -⟩ := pocket_props hα hβ hord' hg
  obtain ⟨φ, hφc, hφi, hφd, -, hφball, hφsph⟩ :=
    Foundations.Schoenflies.schoenflies_disc hJ hw.1 hw.2
  rw [connectedComponentIn_eq_jordanIn hJ hw.1 hw.2, ← hCe] at hφball
  -- the chart `f = cayleyInv ∘ φ`
  have hCH : C ⊆ H := by
    obtain ⟨z, hz, -, -, rfl⟩ := hC
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hCHbar : ∀ z ∈ C, z ∈ Hbar := fun z hz => le_of_lt (show (0 : ℝ) < z.im from hCH hz)
  have hφC : ∀ ζ ∈ ball (0 : ℂ) 1, ∃ z ∈ C, φ ζ = cayley z := fun ζ hζ => by
    obtain ⟨z, hz, e⟩ : φ ζ ∈ cayley '' C := hφball ▸ mem_image_of_mem φ hζ
    exact ⟨z, hz, e.symm⟩
  have hφb : ∀ ζ ∈ ball (0 : ℂ) 1, φ ζ ∈ ball (0 : ℂ) 1 := fun ζ hζ =>
    hJball (hCe ▸ hφball ▸ mem_image_of_mem φ hζ)
  refine ⟨cayleyInv ∘ φ, ⟨fun ζ hζ => ?_, ⟨fun ζ hζ => ?_, fun ζ hζ ζ' hζ' e => ?_, fun z hz => ?_⟩⟩, ?_⟩
  · exact ((QuantumZipper.CA.differentiableAt_cayleyInv (ne_one_of_mem_ball (hφb ζ hζ))).comp ζ
      ((hφd ζ hζ).differentiableAt (isOpen_ball.mem_nhds hζ))).differentiableWithinAt
  · obtain ⟨z, hz, e⟩ := hφC ζ hζ
    simp only [Function.comp_apply, e, cayleyInv_cayley_of_mem_Hbar (hCHbar z hz)]
    exact hz
  · have e' := congrArg cayley e
    simp only [Function.comp_apply, cayley_cayleyInv_of_mem_ball (hφb ζ hζ),
      cayley_cayleyInv_of_mem_ball (hφb ζ' hζ')] at e'
    exact hφi (ball_subset_closedBall hζ) (ball_subset_closedBall hζ') e'
  · obtain ⟨ζ, hζ, e⟩ : cayley z ∈ φ '' ball 0 1 := hφball ▸ mem_image_of_mem cayley hz
    refine ⟨ζ, hζ, ?_⟩
    simp only [Function.comp_apply, e, cayleyInv_cayley_of_mem_Hbar (hCHbar z hz)]
  -- the exceptional set: the preimages of the two corners
  refine ⟨{q | q ∈ sphere (0 : ℂ) 1 ∧ (φ q = toDisc R a ∨ φ q = toDisc R b)}, ?_, ?_⟩
  · refine Set.Finite.of_finite_image ((Set.toFinite ({toDisc R a, toDisc R b} : Set ℂ)).subset ?_)
      (hφi.mono fun q hq => sphere_subset_closedBall hq.1)
    rintro _ ⟨q, ⟨-, h | h⟩, rfl⟩
    · exact Or.inl h
    · exact Or.inr (mem_singleton_iff.2 h)
  intro q hq hqE
  have hqa : φ q ≠ toDisc R a := fun h => hqE ⟨hq, Or.inl h⟩
  have hqb : φ q ≠ toDisc R b := fun h => hqE ⟨hq, Or.inr h⟩
  obtain ⟨ha, hb, hab, hgap⟩ := hg
  obtain ⟨hja, hβa⟩ := contactMap_mem hβ ha
  obtain ⟨hjb, hβb⟩ := contactMap_mem hβ hb
  have hmono := strictMonoOn_contactMap hα hβ hord'
  have hφqJ : φ q ∈ pocketCurve (toDisc R) (toDisc L) a b := hφsph ▸ mem_image_of_mem φ hq
  rcases hφqJ with ⟨s, hs, hφs⟩ | ⟨r, hr, hφr⟩
  · -- a point of the right wall
    have hsa : s ≠ a := fun h => hqa (by rw [← hφs, h])
    have hsb : s ≠ b := fun h => hqb (by rw [← hφs, h])
    have hs' : s ∈ Ioo a b := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), lt_of_le_of_ne hs.2 hsb⟩
    have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt ha.1.1 hs'.1, lt_of_lt_of_le hs'.2 hb.1.2⟩
    refine Or.inl ⟨arcTime s, arcTime_pos hs01, fun hRL => ?_,
      tendsto_cayleyInv_comp hR hφc hq hs01 hφs.symm⟩
    refine hgap s hs' ⟨Ioo_subset_Icc_self hs01, ?_⟩
    rw [toDisc_of_lt hs01.2]
    exact (hL.cayley_mem_crossRange_iff (hR.mem_Hbar (arcTime_pos hs01).le)).2 hRL
  · -- a point of the left wall
    have hβa' : toDisc L (contactMap (toDisc R) (toDisc L) a) = toDisc R a := hβa
    have hra : r ≠ contactMap (toDisc R) (toDisc L) a := fun h => hqa (by rw [← hφr, h, hβa'])
    have hrb : r ≠ contactMap (toDisc R) (toDisc L) b := fun h => hqb (by rw [← hφr, h, hβb])
    have hr' : r ∈ Ioo (contactMap (toDisc R) (toDisc L) a) (contactMap (toDisc R) (toDisc L) b) :=
      ⟨lt_of_le_of_ne hr.1 (Ne.symm hra), lt_of_le_of_ne hr.2 hrb⟩
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hja.1 hr'.1, lt_of_lt_of_le hr'.2 hjb.2⟩
    refine Or.inr ⟨arcTime r, arcTime_pos hr01, fun hLR => ?_,
      tendsto_cayleyInv_comp hL hφc hq hr01 hφr.symm⟩
    -- `L(t)` on the right wall would be a contact strictly inside the gap
    have hmem : toDisc L r ∈ crossRange (toDisc R) := by
      rw [toDisc_of_lt hr01.2]
      exact (hR.cayley_mem_crossRange_iff (hL.mem_Hbar (arcTime_pos hr01).le)).2 hLR
    obtain ⟨s', hs', hs'e⟩ := hmem
    have hc : s' ∈ Sec7.pocketContactSet (toDisc R) (toDisc L) :=
      ⟨hs', r, Ioo_subset_Icc_self hr01, hs'e.symm⟩
    have hj : contactMap (toDisc R) (toDisc L) s' = r :=
      contactMap_eq hβ (Ioo_subset_Icc_self hr01) hs'e
    refine hgap s' ⟨?_, ?_⟩ hc
    · by_contra hle
      have := hmono.monotoneOn hc ha (not_lt.1 hle)
      rw [hj] at this
      exact absurd hr'.1 (not_lt.2 this)
    · by_contra hle
      have := hmono.monotoneOn hb hc (not_lt.1 hle)
      rw [hj] at this
      exact absurd hr'.2 (not_lt.2 this)

end Chart

/-! ### The identification of the chamber mean -/

section Identification

/-- **The deterministic identification on one chamber.** Let `w` be harmonic on `ℍ \ (R ∪ L)` with the (D2) wall
limits from between the walls, and suppose Corollary 4.8 holds for `w` on every component of `ℍ \ (R ∪ L)` with a
conformal chart (`hcor`). Then `w` equals every bounded harmonic function `v` on a chamber `C` with the same limits from
`C`. -/
theorem eqOn_chamber_of_cor48 {R L : ℝ → ℂ} (hR : IsProperArc R) (hL : IsProperArc L)
    (hord : Disjoint (arcRange L) (rightSideOf (arcRange R))) {ℓR ℓL : ℂ → ℝ} {w : ℂ → ℝ}
    (hwR : ∀ s > 0, R s ∉ arcRange L →
      Tendsto w (𝓝[leftSideOf (arcRange R) ∩ rightSideOf (arcRange L)] (R s)) (𝓝 (ℓR (R s))))
    (hwL : ∀ s > 0, L s ∉ arcRange R →
      Tendsto w (𝓝[leftSideOf (arcRange R) ∩ rightSideOf (arcRange L)] (L s)) (𝓝 (ℓL (L s))))
    (hcor : ∀ C : Set ℂ, IsOpen C → C ⊆ H \ (arcRange R ∪ arcRange L) →
      ∀ f : ℂ → ℂ, IsConformalBijection f (ball 0 1) C →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v C → (∃ M, ∀ z ∈ C, |v z| ≤ M) →
      ∀ E : Set ℂ, E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → Tendsto (fun ζ => w (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) →
      EqOn w v C)
    {C : Set ℂ} (hC : C ∈ betweenComponents (arcRange R) (arcRange L)) {v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v C) (hvb : ∃ M, ∀ z ∈ C, |v z| ≤ M)
    (hvR : ∀ s > 0, R s ∉ arcRange L → Tendsto v (𝓝[C] (R s)) (𝓝 (ℓR (R s))))
    (hvL : ∀ s > 0, L s ∉ arcRange R → Tendsto v (𝓝[C] (L s)) (𝓝 (ℓL (L s)))) :
    EqOn w v C := by
  have hCsub : C ⊆ H \ (arcRange R ∪ arcRange L) := by
    obtain ⟨z, -, -, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hCo : IsOpen C := by
    obtain ⟨z, -, -, -, rfl⟩ := hC
    exact (QuantumZipper.isOpen_H.sdiff (hR.isClosed_arcRange.union hL.isClosed_arcRange)).connectedComponentIn
  have hCB := subset_between_of_mem_betweenComponents hR hL hC
  obtain ⟨f, hf, E, hE, hlim⟩ := exists_chamber_chart hR hL hord hC
  refine hcor C hCo hCsub f hf v hv hvb E hE fun q hq hqE => ?_
  have hfC : ∀ {z : ℂ}, Tendsto f (𝓝[ball 0 1] q) (𝓝 z) → Tendsto f (𝓝[ball 0 1] q) (𝓝[C] z) :=
    fun hfz => tendsto_nhdsWithin_iff.2 ⟨hfz, eventually_mem_nhdsWithin.mono fun ζ hζ => hf.2.mapsTo hζ⟩
  have key : ∀ {z : ℂ} {ℓ : ℝ}, Tendsto f (𝓝[ball 0 1] q) (𝓝 z) →
      Tendsto w (𝓝[leftSideOf (arcRange R) ∩ rightSideOf (arcRange L)] z) (𝓝 ℓ) →
      Tendsto v (𝓝[C] z) (𝓝 ℓ) → Tendsto (fun ζ => w (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0) := by
    intro z ℓ hfz hw hv'
    have h1 := (hw.mono_left (nhdsWithin_mono _ hCB)).comp (hfC hfz)
    have h2 := hv'.comp (hfC hfz)
    have := h1.sub h2
    rwa [sub_self] at this
  rcases hlim q hq hqE with ⟨s, hs, hsL, hfs⟩ | ⟨s, hs, hsR, hfs⟩
  · exact key hfs (hwR s hs hsL) (hvR s hs hsL)
  · exact key hfs (hwL s hs hsR) (hvL s hs hsR)

section Probabilistic

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Wang–Wu Proposition 4.20: the conditional mean in each chamber** (identification by Corollary 4.8). Under the
hypotheses of `ae_tendsto_unionMean_between` (random simple proper walls `R`, `L` whose ranges are field-determined
local sets of the zero-boundary GFF `h`, single-line means with left-side values `ℓ_R` on `R` and right-side values
`ℓ_L` on `L`), and with `L` to the left of `R` (`L` avoids the right side of `R`, Proposition 4.19): for every version
`g` of the mean of the union `R ∪ L` (a local set determined by `h`), almost surely `g` has a harmonic representative
`w` on `ℍ \ (R ∪ L)` such that on every component `C` between the walls, `w = v` for every bounded harmonic `v` on `C`
with the (D2) limits `ℓ_R(R(s))` at the points of `R` and `ℓ_L(L(s))` at the points of `L` off the other wall (taken
from inside `C`). For seed lines of `F = h + m₀` at heights `u₁ < u₂`: `ℓ_R = −λ − u₁ − m₀`, `ℓ_L = λ − u₂ − m₀`. -/
theorem ae_eqOn_chamber (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hRdet : LQGMetric.AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hLdet : LQGMetric.AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω)) h P)
    (hLloc : IsLocalSet (fun ω => arcRange (L ω)) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (arcRange (L ω)) (rightSideOf (arcRange (R ω))))
    {gR gL : Ω → DistOn upperHalfPlaneOpens}
    (hgR : IsLocalSetMean (fun ω => arcRange (R ω)) h P gR)
    (hgL : IsLocalSetMean (fun ω => arcRange (L ω)) h P gL) {ℓR ℓL : ℂ → ℝ}
    (hℓR : ∀ᵐ ω ∂P, HasLeftSideLimit (gR ω) (R ω) ℓR)
    (hℓL : ∀ᵐ ω ∂P, HasRightSideLimit (gL ω) (L ω) ℓL)
    (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean (fun ω => arcRange (R ω) ∪ arcRange (L ω)) h P g) :
    ∀ᵐ ω ∂P, ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (arcRange (R ω) ∪ arcRange (L ω))) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (arcRange (R ω) ∪ arcRange (L ω)) →
        g ω φ = ∫ z, w z * φ z) ∧
      ∀ C ∈ betweenComponents (arcRange (R ω)) (arcRange (L ω)),
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v C → (∃ M, ∀ z ∈ C, |v z| ≤ M) →
      (∀ s > 0, R ω s ∉ arcRange (L ω) → Tendsto v (𝓝[C] (R ω s)) (𝓝 (ℓR (R ω s)))) →
      (∀ s > 0, L ω s ∉ arcRange (R ω) → Tendsto v (𝓝[C] (L ω s)) (𝓝 (ℓL (L ω s)))) →
      EqOn w v C := by
  obtain ⟨⟨hloc, -⟩, hwall⟩ := ae_tendsto_unionMean_between hh hRm hLm hRdet hLdet hRloc hLloc harc hgR hgL hℓR hℓL
  have hA : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω) ∪ arcRange (L ω) :=
    measurable_union_hitting hRm hLm
  have hmean := Sec6.IsLocalSetMean.ae_eq_condExp_germSigma hh hA hloc hg
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ (arcRange (R ω) ∪ arcRange (L ω))) := hloc.2.1.mono fun _ h => h.2
  filter_upwards [hwall g hg, ae_eqOn_of_condMean_global hh hmean hopen, harc, hord] with
    ω ⟨w, hw, hrep, hwR, hwL⟩ hcor hω hordω
  exact ⟨w, hw, hrep, fun C hC v hv hvb hvR hvL =>
    eqOn_chamber_of_cor48 hω.1 hω.2 hordω hwR hwL (hcor w hw hrep) hC hv hvb hvR hvL⟩

end Probabilistic

end Identification

end InteractingSLE.WangWu
