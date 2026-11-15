/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinUnionC

/-!
# SB2's union mean with the upper hull handled per prime end (`finK` replaced)

Packet PROVE-T14-SB2FIN2 (Theorem 1.4's SB2; the orchestrator's item (1), `hpinch`). `IsRelConfigJC.finK` (finitely many
`x` off the closed relative hull landing on `closure (K_t ∖ A)`) is used by the union-word lemma only to get, at the
other such `x`, the one-sided condition `freeNear K_t A p r` near the landing `p` (through `retained_side_rel`'s
`hpK`). The landed route derives `finK` from finitely many pinch points of `∂D_A`, which fails whenever `A` has a
two-sided arc. Here the configuration asks for the one-sided condition itself:

* **`IsRelConfigJK`**: `IsRelConfigJC` with `finK` replaced by `oneK` — at **every** `x` whose relative landing is off
  the closed relative hull, the joint approach eventually lies in `freeNear (K_t) A p r` (proved for SB2(1) with no
  input, `eventually_freeNearK_of_notMem_closure`, `SB2GPinch`);
* `retained_side_relK` (`Union.retained_side_rel` without `hpK`); **`IsRelConfigJK.hasUnionWordBoundaryOnK`**,
  **`ae_eqOn_unionMean_of_relConfigJK`**, **`ae_chartTransport_eq_couplingMean_of_relConfigJK`**: the landed
  statements for the new configuration (the proofs are those of `SB2FinUnionC`, with the retained alternative taking
  its one-sided condition from `oneK`).

R48: serves Theorem 1.4. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn CondIndepEv)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open QuantumZipper.CA (cayley cayleyInv)

universe u

namespace InteractingSLE.Theorem14.SB.FinRel

open InteractingSLE.Theorem14.SB.Union
open Supp8.BHMean (jointInv jointFwd jointLift jointChart jointLog IsSideWord IsFlowedWord)
open Supp8.Q3Rel (IsRetainedChartOff IsGoodPt)
open Supp8.RelTrans (nhdsWithin_H_neBot_of_mem_Hbar ofReal_mem_Hbar transBdry liftDiff)
open WangWu (chartAL chartAR)
open LocalSets

section SidesK

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ}
  {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G u₀ w₁ w₂ v : ℂ → ℝ}

/-- **The retained-side alternative without the hull condition** (`Union.retained_side_rel` without `hpK`). -/
theorem retained_side_relK (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hG₀ : IsBoundedHarmonicExtension β₀ S₀ G₀) (hG : IsBoundedHarmonicExtension βu Su G)
    (hflow : IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u))
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    {x : ℝ} (hxS : x ∉ Su) (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u))
    (hyS : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ S₀) (hyb : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ Sb) :
    ∃ p : ℂ, Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) ∧ p ∈ A ∪ {z : ℂ | z.im = 0} ∧
      Tendsto (fun y => (w₁ (jointInv Ψi Wr u y) + u₀ (jointInv Ψi Wr u y)) -
        (G (jointFwd Ψ Wr u (jointInv Ψi Wr u y)) - χ * jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y)))
        (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  have hyim : yc.im = 0 := Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hy
  have hyr : yc = (yc.re : ℂ) := Complex.ext (by simp) (by simp [hyim])
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] (x : ℂ)) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hxbar,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  obtain ⟨p, hp⟩ := hΨ.inv_lands yc.re hyb
  rw [← hyr] at hp
  have hjoint : Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) := hp.comp hlimF
  have hpe : extendFrom H (jointInv Ψi Wr u) (x : ℂ) = p :=
    extendFrom_eq (by rw [closure_H]; exact hxbar) hjoint
  have hycb : yc ∈ Hbar := show (0 : ℝ) ≤ yc.im from hyim.ge
  have hNe : (𝓝[H] yc).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hycb)
  have hpbar : p ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hp (eventually_nhdsWithin_of_forall fun v hv => (hΨ.inv_mem v hv).1)
  have hpC : p ∉ H \ A := Supp8.Q3Rel.notMem_compl_of_tendsto_inv hΨ hyim hp
  have hpAR : p ∈ A ∪ {z : ℂ | z.im = 0} := by
    by_cases hpA : p ∈ A
    · exact Or.inl hpA
    · exact Or.inr (le_antisymm (not_lt.1 fun hpos => hpC ⟨hpos, hpA⟩) hpbar)
  refine ⟨p, hjoint, hpAR, ?_⟩
  -- the limit
  have hyK : ((yc.re : ℝ) : ℂ) ∉ closure (fwdHull Wr u) := by rw [← hyr]; exact hy
  have hL0 : Tendsto (fun v => (logDerivFwd Wr u (fwdMapInv Wr u v)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have := Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure hWr hWr0 hu hyK
    rw [← hyr] at this
    exact this.comp hlimF
  have hG₀l : Tendsto (fun v => G₀ (fwdMapInv Wr u v)) (𝓝[H] (x : ℂ)) (𝓝 (β₀ yc.re)) := by
    have := hG₀.2.2 yc.re hyS
    rw [← hyr] at this
    exact this.comp hlimF
  have hGl : Tendsto G (𝓝[H] (x : ℂ)) (𝓝 (βu x)) := hG.2.2 x hxS
  have hsum := (hG₀l.sub hGl).add (hL0.const_mul χ)
  rw [hflow x hxS hy hyS, sub_self, mul_zero, add_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun v hv => ?_)
  have hFv := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hv
  have hJ : jointInv Ψi Wr u v ∈ H \ A := hΨ.inv_mem _ hFv.1
  have hΨJ : Ψ (jointInv Ψi Wr u v) = fwdMapInv Wr u v := hΨ.fwd_inv _ hFv.1
  have e1 := hw₁ hJ
  simp only at e1
  simp only [jointLift, jointFwd_jointInv_rel hΨ hWr hWr0 hu hv, e1, hΨJ]
  ring


end SidesK

/-- **The junction configuration with one-sided cusp points and one-sided retained landings**: `IsRelConfigJC` with
`finK` replaced by `oneK` (at every real point off the relative hull image, the joint parametrization stays in the
`K_t`-free components of `(ℍ ∖ A) ∩ B(p, r)`). -/
structure IsRelConfigJK (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (Sb : Finset ℝ) (w Wr : ℝ → ℝ) (η ηr : ℝ → ℂ)
    (t u χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ) : Prop where
  chart : IsRetainedChartOff A Ψ Ψi LΨ Sb
  hw : Continuous w
  hw0 : w 0 = 0
  hη : IsLoewnerTrace w η
  ht : 0 ≤ t
  hWr : Continuous Wr
  hWr0 : Wr 0 = 0
  hηr : IsLoewnerTrace Wr ηr
  hu : 0 ≤ u
  hullIn : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u
  hullFr : ∀ z ∈ H \ A, Ψ z ∈ frontier (fwdHull Wr u) → z ∈ fwdHull w t
  bad : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u)
  tip : Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0)
  collar : ∃ x₁ < chartAL Wr u,
    (∀ x ∈ Ioo x₁ (chartAR Wr u), IsGoodPt Sb Wr u (x : ℂ)) ∧
    (∀ x ∈ Ioo x₁ (chartAL Wr u), (extendFrom H (jointInv Ψi Wr u) (x : ℂ)).im = 0) ∧
    (∃ x₀ ∈ Ioo x₁ (chartAL Wr u), extendFrom H (jointInv Ψi Wr u) (x₀ : ℂ) ∉ closure A ∧
      extendFrom H (jointInv Ψi Wr u) (x₀ : ℂ) ∉ closure (fwdHull w t) ∧
      extendFrom H (jointInv Ψi Wr u) (x₀ : ℂ) ≠ 0)
  landK : ∀ x ∈ Ico (chartAL Wr u) (chartAR Wr u),
    extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∈ closure (fwdHull w t)
  cusp : {x : ℝ | x ∈ Ico (chartAL Wr u) (chartAR Wr u) ∧
    extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∈ closure A ∧ ¬ ∃ r > 0, ∀ᶠ y in 𝓝[H] (x : ℂ),
      jointInv Ψi Wr u y ∈ freeNear A (fwdHull w t) (extendFrom H (jointInv Ψi Wr u) (x : ℂ)) r}.Finite
  oneK : ∀ x : ℝ, extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u) → ∃ r > 0,
    ∀ᶠ y in 𝓝[H] (x : ℂ), jointInv Ψi Wr u y ∈ freeNear (fwdHull w t) A (extendFrom H (jointInv Ψi Wr u) (x : ℂ)) r
  bhe₀ : IsBoundedHarmonicExtension β₀ S₀ G₀
  bheE : IsBoundedHarmonicExtension βE SE GE
  bheu : IsBoundedHarmonicExtension βu Su G
  sideE : IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam
  sideu : IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam
  flow : IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u)
  cand : ∀ z, v z = G (fwdMap Wr u (Ψ z)) - χ * ((logDerivFwd Wr u (Ψ z)).im + (LΨ z).im)


section Assembly

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ}
  {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G u₀ w₁ w₂ v : ℂ → ℝ}

/-- **The one-sided union word boundary datum of the configuration `IsRelConfigJK` on the relative component**
(`IsRelConfigJC.hasUnionWordBoundaryOnC` with the retained alternative's one-sided condition from `oneK`). -/
theorem IsRelConfigJK.hasUnionWordBoundaryOnK
    (hc : IsRelConfigJK A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t)) :
    HasUnionWordBoundaryOnC (relComp A Ψ Wr u) A (fwdHull w t) u₀ v w₁ w₂ χ βu Su := by
  have hΨ := hc.chart
  have hw := hc.hw
  have hw0 := hc.hw0
  have hη := hc.hη
  have ht := hc.ht
  have hWr := hc.hWr
  have hWr0 := hc.hWr0
  have hηr := hc.hηr
  have hu := hc.hu
  have hKin := hc.hullIn
  obtain ⟨x₁, hx₁, hgood, hleft, x₀, hx₀, hp₀A, hp₀K, hp₀0⟩ := hc.collar
  have hAL0 : chartAL Wr u ≤ 0 := WangWu.chartAL_nonpos hWr hu
  have hAR0 : 0 ≤ chartAR Wr u := WangWu.chartAR_nonneg hWr hu
  -- the open set `V = (x₁, a_R)` of points landing off `ℍ ∖ K_t`
  set V : Set ℝ := Ioo x₁ (chartAR Wr u) with hVdef
  have hV : IsOpen V := isOpen_Ioo
  have hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s := by
    intro s hs
    refine ⟨hgood s hs, ?_⟩
    rcases lt_or_ge s (chartAL Wr u) with h | h
    · intro hp
      have h1 : (0 : ℝ) < (extendFrom H (jointInv Ψi Wr u) (s : ℂ)).im := hp.1
      rw [hleft s ⟨hs.1, h⟩] at h1
      exact lt_irrefl _ h1
    · exact notMem_compl_of_mem_closure hw ht (hc.landK s ⟨h, hs.2⟩)
  have hIV : Ico (chartAL Wr u) (chartAR Wr u) ⊆ V := fun s hs => ⟨hx₁.trans_le hs.1, hs.2⟩
  have hIV₀ : Ico x₀ (chartAR Wr u) ⊆ V := fun s hs => ⟨hx₀.1.trans_le hs.1, hs.2⟩
  -- the exceptional real points
  set T := transBdry Ψi w Wr t u with hTdef
  set R' : Set ℝ := {x : ℝ | x ≠ 0 ∧ x ∈ Ico (chartAL Wr u) (chartAR Wr u) ∧
    extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u)} with hR'
  set φ : ℝ → ℝ := fun s => (fwdMap Wr u (s : ℂ)).re with hφ
  set Xb : Set ℝ := {x : ℝ | ∃ b ∈ Sb, extendFrom H (fwdMapInv Wr u) (x : ℂ) = (b : ℂ)} with hXb
  set XA : Set ℝ := {x : ℝ | x ∈ Ico (chartAL Wr u) (chartAR Wr u) ∧
    extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∈ closure A ∧ ¬ ∃ r > 0, ∀ᶠ y in 𝓝[H] (x : ℂ),
      jointInv Ψi Wr u y ∈ freeNear A (fwdHull w t) (extendFrom H (jointInv Ψi Wr u) (x : ℂ)) r} with hXA
  set XK : Set ℝ := ∅ with hXK
  set X : Set ℝ := insert 0 (insert (chartAR Wr u) ((↑Su : Set ℝ) ∪ φ '' (↑S₀ : Set ℝ) ∪
    (R' ∩ T ⁻¹' (↑SE : Set ℝ)) ∪ Xb ∪ XA ∪ XK)) with hX
  have hmono := strictMonoOn_transBdry_Ico (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl hIV
  have hXf : X.Finite := by
    refine Set.Finite.insert _ (Set.Finite.insert _ ((((((Su.finite_toSet).union
      ((S₀.finite_toSet).image φ)).union ?_).union
      (Supp8.Q3Rel.finite_badPts hWr hWr0 hηr hu hc.bad)).union hc.cusp).union Set.finite_empty))
    refine Set.Finite.of_finite_image ((SE.finite_toSet).subset ?_)
      (hmono.injOn.mono fun x hx => hx.1.2.1)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  set E : Set ℂ := insert (1 : ℂ) ((fun x : ℝ => cayley (x : ℂ)) '' X) with hE
  have hEf : E.Finite := (hXf.image _).insert _
  intro z₀ hz₀
  rw [connectedComponentIn_eq_relComp hΨ hWr hWr0 hu hKin hc.hullFr hz₀]
  refine ⟨fun ζ => jointInv Ψi Wr u (cayleyInv ζ), jointFwd Ψ Wr u, G, jointLift Ψ LΨ Wr u, E,
    isConformalBijection_diskInv_rel hΨ hWr hWr0 hu, isConformalBijection_jointFwd_rel hΨ hWr hWr0 hu,
    hc.bheu, continuousOn_jointLift_rel hΨ hWr hWr0 hu,
    fun z hz => deriv_jointFwd_rel hΨ hWr hWr0 hu hz, hEf, fun z _ => hc.cand z, ?_⟩
  intro q hq hqE
  have hq1 : q ≠ 1 := fun h => hqE (h ▸ mem_insert _ _)
  obtain ⟨hre, hcay⟩ := Supp8.BHMean.tendsto_cayleyInv_sphere hq hq1
  set x : ℝ := (cayleyInv q).re with hxdef
  have hxX : x ∉ X := fun hx => hqE (mem_insert_of_mem _ ⟨x, hx, by
    simp only
    rw [← hre, QuantumZipper.CA.cayley_cayleyInv hq1]⟩)
  have hX' : ∀ {P : Set ℝ}, P ⊆ X → x ∉ P := fun hP hx => hxX (hP hx)
  have hx0 : x ≠ 0 := fun h => hxX (h ▸ mem_insert _ _)
  have hxAR : x ≠ chartAR Wr u := fun h => hxX (mem_insert_of_mem _ (h ▸ mem_insert _ _))
  have hsub : ∀ {P : Set ℝ}, P ⊆ (↑Su : Set ℝ) ∪ φ '' (↑S₀ : Set ℝ) ∪ (R' ∩ T ⁻¹' (↑SE : Set ℝ)) ∪ Xb ∪ XA ∪ XK →
      x ∉ P := fun hP hx => hxX (mem_insert_of_mem _ (mem_insert_of_mem _ (hP hx)))
  have hxS : x ∉ Su := hsub fun y hy => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hy))))
  have hxb : x ∉ Xb := hsub fun y hy => Or.inl (Or.inl (Or.inr hy))
  have hxA : x ∉ XA := hsub fun y hy => Or.inl (Or.inr hy)
  clear hX'
  by_cases hxK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u)
  · -- the explored side
    have hxI := Supp8.RelTrans.hullImage_subset_Icc hηr hWr hWr0 hu hxK
    have hxI' : x ∈ Ico (chartAL Wr u) (chartAR Wr u) := ⟨hxI.1, lt_of_le_of_ne hxI.2 hxAR⟩
    have hxR' : x ∈ R' := ⟨hx0, hxI', hxK⟩
    have hg : IsGoodPt Sb Wr u (x : ℂ) := Supp8.Q3Rel.goodPt_of_mem_closure hc.bad hxK
    have hpK := hc.landK x hxI'
    obtain ⟨vT, hvT, hFv, hTl⟩ := exists_tendsto_transition_rel (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin
      (show ((x : ℂ)).im = 0 by simp) hg (notMem_compl_of_mem_closure hw ht hpK)
    have hφe : extendFrom H (fun y => fwdMap w t (jointInv Ψi Wr u y)) (x : ℂ) = vT :=
      extendFrom_eq (by rw [closure_H]; exact ofReal_mem_Hbar x) hTl
    have hvTe : vT = ((T x : ℝ) : ℂ) := by
      simp only [hTdef, transBdry, hφe]
      exact Complex.ext (by simp) (by simp [hvT])
    obtain ⟨hsign, hT0⟩ := transBdry_pos_iff_rel (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl hIV hc.tip
      hxI' hx0
    have hTS : T x ∉ SE := fun h => hsub (fun y hy => Or.inl (Or.inl (Or.inl (Or.inr hy)))) ⟨hxR', h⟩
    have hTK : extendFrom H (fwdMapInv w t) (T x : ℂ) ∈ closure (fwdHull w t) := by
      rw [← hvTe, hFv]; exact hpK
    have hLl := tendsto_liftDiff_zero_of_free_collar (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl hx₀.2
      hIV₀ hp₀A hp₀K hp₀0 (x := x) ⟨hx₀.2.le.trans hxI'.1, hxI'.2⟩
    obtain ⟨hp, hpKR, hlim⟩ := explored_side_relC hΨ hw ht hWr hWr0 hηr hu hKin hc.bheE hc.bheu hc.sideE
      hc.sideu hw₂ hx0 hxK hg hpK hxS hTS hsign hT0 hTK (hvTe ▸ hTl) hLl
    refine Or.inr ⟨_, hp.comp hcay, hpKR, ?_, hlim.comp hcay⟩
    by_cases hpA : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∈ closure A
    · -- a one-sided cusp point
      have hcusp : ∃ r > 0, ∀ᶠ y in 𝓝[H] (x : ℂ),
          jointInv Ψi Wr u y ∈ freeNear A (fwdHull w t) (extendFrom H (jointInv Ψi Wr u) (x : ℂ)) r := by
        by_contra hn
        exact hxA ⟨hxI', hpA, hn⟩
      obtain ⟨r, hr, hev⟩ := hcusp
      exact ⟨r, hr, hcay.eventually hev⟩
    · obtain ⟨r, hr, hball⟩ := Supp8.GB6.exists_ball_disjoint_of_notMem_closure hpA
      refine ⟨r, hr, eventually_freeNear_of_ball (f := fun ζ => jointInv Ψi Wr u (cayleyInv ζ))
        (hcay.eventually (eventually_nhdsWithin_of_forall
        fun y hy => relComp_subset hKin (jointInv_mem_relComp hΨ hWr hWr0 hu hy))) (hp.comp hcay) hr
        fun z hz => absurd hz.1 (Set.disjoint_left.1 hball hz.2)⟩
  · -- the retained side
    have hyim := Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hxK
    have hyr : extendFrom H (fwdMapInv Wr u) (x : ℂ) = ((extendFrom H (fwdMapInv Wr u) (x : ℂ)).re : ℂ) :=
      Complex.ext (by simp) (by simp [hyim])
    have hyS : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ S₀ := by
      intro hS
      have hre0 : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ≠ 0 := by
        intro h0
        have hy0 : extendFrom H (fwdMapInv Wr u) (x : ℂ) = 0 := Complex.ext h0 hyim
        rcases hu.eq_or_lt with rfl | hpos
        · rw [Supp8.BHMean.extendFrom_fwdMapInv_zero hWr hWr0 (show (0 : ℝ) ≤ (x : ℂ).im by simp)] at hy0
          exact hx0 (by exact_mod_cast hy0)
        · exact hxK (hy0 ▸ ConformalImageFull.zero_mem_closure_fwdHull hWr hWr0 hpos)
      have hxφ := Supp8.BHMean.eq_fwdMap_of_extendFrom_notMem_closure hηr hWr hWr0 hu hxK hre0
      exact hsub (fun y hy => Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hy))))) ⟨_, hS, hxφ.symm⟩
    have hyb : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ Sb := fun hb => hxb ⟨_, hb, hyr⟩
    obtain ⟨p, hp, hpA, hlim⟩ := retained_side_relK hΨ hWr hWr0 hηr hu hc.bhe₀ hc.bheu hc.flow hw₁
      hxS hxK hyS hyb
    have hpe : extendFrom H (jointInv Ψi Wr u) (x : ℂ) = p :=
      extendFrom_eq (by rw [closure_H]; exact ofReal_mem_Hbar x) hp
    obtain ⟨r, hr, hev⟩ := hc.oneK x hxK
    rw [hpe] at hev
    exact Or.inl ⟨p, hp.comp hcay, hpA, ⟨r, hr, hcay.eventually hev⟩, hlim.comp hcay⟩

end Assembly

/-! ### The union mean and its chart transport for the cusp configuration -/

section Mean

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

/-- **The conditional mean of the union of a retained set and an explored hull meeting it at junctions, on the
relative component, one-sided cusp form** (ruling R84; `Union.ae_eqOn_unionMean_of_relConfigJ` for the configuration
`IsRelConfigJK`): if a.s. on `D` the cusp configuration `IsRelConfigJK` holds and the two individual means are the
retained-chart and the explored-chain formulas, the union mean plus `u₀` equals the relative candidate `v` on
`relComp A Ψ Wr u`. -/
theorem ae_eqOn_unionMean_of_relConfigJK
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ} {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ}
    {t u : Ω → ℝ} {χ lam : ℝ}
    {β₀ βE βu : Ω → ℝ → ℝ} {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] fun ω => fwdHull (w ω) (t ω))
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h u₀) P)
    (hlK : IsLocalSet (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (fwdHull (w ω) (t ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fwdHull (w ω) (t ω))) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField h u₀) P g₁)
    (hg₂ : IsLocalSetMean (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g₂)
    {D : Set Ω}
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigJK (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω) (t ω)
      (u ω) χ lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω))
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ ω (Ψ ω z) - χ * (LΨ ω z).im) (H \ A ω))
    (hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (w ω) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (w ω) (t ω) → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (t ω) z) - χ * (logDerivFwd (w ω) (t ω) z).im)
        (H \ fwdHull (w ω) (t ω))) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ fwdHull (w ω) (t ω))) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ fwdHull (w ω) (t ω)) →
        g ω φ = ∫ z, wU z * φ z) →
      EqOn (fun z => wU z + u₀ z) (v ω) (relComp (A ω) (Ψ ω) (Wr ω) (u ω)) := by
  have hword : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ w₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (w ω) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (w ω) (t ω) → g₂ ω φ = ∫ z, w₂ z * φ z) →
      HasUnionWordBoundaryOnC (relComp (A ω) (Ψ ω) (Wr ω) (u ω)) (A ω) (fwdHull (w ω) (t ω)) u₀ (v ω) w₁ w₂ χ
        (βu ω) (Su ω) := by
    filter_upwards [hcfg, hind₁, hind₂] with ω hc h1 h2 hωD w₁ w₂ hw₁ hr₁ hw₂ hr₂
    exact (hc hωD).hasUnionWordBoundaryOnK (h1 hωD w₁ hw₁ hr₁) (h2 hωD w₂ hw₂ hr₂)
  have hsurv := ae_survivingWordBoundaryOn_unionC hh0 hAm hKm hdA hlA hlK hunbA hunbK hg hg₁ hg₂
    (fun ω => relComp (A ω) (Ψ ω) (Wr ω) (u ω)) u₀ v χ βu Su hword
  have hC : ∀ᵐ ω ∂P, ω ∈ D →
      relComp (A ω) (Ψ ω) (Wr ω) (u ω) ⊆ H \ (A ω ∪ fwdHull (w ω) (t ω)) := by
    filter_upwards [hcfg] with ω hc hωD
    exact relComp_subset (hc hωD).hullIn
  exact ae_eqOn_physicalMean_of_boundaryOn hh0 hu₀ hu₀b (measurable_union_hitting hAm hKm) hlU hg
    (fun ω => relComp (A ω) (Ψ ω) (Wr ω) (u ω)) χ hC hsurv


/-- **The union mean of the junction configuration, read in the retained chart, is the relative coupling mean** (K2's
`hmean` form; SB2, p. 632; the landed `Union.ae_chartTransport_eq_couplingMean_of_relConfigJ` for the cusp
configuration). Under the hypotheses of `ae_eqOn_unionMean_of_relConfigJK`, for a family of conformal
charts `c ω` with continuous lifts whose inverse is the retained inverse `Ψi ω` on `ℍ` and whose lift along it is
`Im LΨ + ℓ₀`: almost surely on `D`, for every test `ψ` off the relative hull,
`chartTransport (c ω) 1 a χ (g ω + u₀) ψ = ∫ couplingMean κ (Wr ω) (u ω) (G ω + a + χ ℓ₀) ψ`. -/
theorem ae_chartTransport_eq_couplingMean_of_relConfigJK {κ : ℝ}
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ} {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ}
    {t u : Ω → ℝ} {lam : ℝ}
    {β₀ βE βu : Ω → ℝ → ℝ} {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] fun ω => fwdHull (w ω) (t ω))
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h u₀) P)
    (hlK : IsLocalSet (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (fwdHull (w ω) (t ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fwdHull (w ω) (t ω))) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField h u₀) P g₁)
    (hg₂ : IsLocalSetMean (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g₂)
    {D : Set Ω}
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigJK (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω) (t ω)
      (u ω) (chiC κ) lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω))
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ ω (Ψ ω z) - chiC κ * (LΨ ω z).im) (H \ A ω))
    (hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (w ω) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (w ω) (t ω) → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (t ω) z) - chiC κ * (logDerivFwd (w ω) (t ω) z).im)
        (H \ fwdHull (w ω) (t ω)))
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hℓ : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcinv : ∀ ω, ∀ y ∈ H, (c ω).2.1 y = Ψi ω y) {ℓ₀ : ℝ}
    (hlift : ∀ ω, ∀ y ∈ H, (c ω).2.2 ((c ω).2.1 y) = (LΨ ω ((c ω).2.1 y)).im + ℓ₀) (a : ℝ) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wr ω) (u ω)) →
      Chart.chartTransport (hc ω) 1 a (chiC κ) (g ω + smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ y, couplingMean κ (Wr ω) (u ω) (fun z => G ω z + (a + chiC κ * ℓ₀)) y * ψ y := by
  have hmean := ae_eqOn_unionMean_of_relConfigJK hh0 hu₀ hu₀b hAm hKm hdA hlA hlK hlU hunbA hunbK hg hg₁ hg₂ hcfg
    hind₁ hind₂
  filter_upwards [hmean, hcfg, hg.2.1] with ω hmω hcω hgω hωD ψ hψ
  obtain ⟨wU, hwU, hrepU⟩ := hgω
  have hcfgω := hcω hωD
  have hEq := hmω hωD wU hwU hrepU
  have hΨ := hcfgω.chart
  -- the inverse chart image of the complement of the relative hull lies in the relative component
  have hsub : (c ω).2.1 '' (H \ fwdHull (Wr ω) (u ω)) ⊆ relComp (A ω) (Ψ ω) (Wr ω) (u ω) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hcinv ω y hy.1]
    exact ⟨hΨ.inv_mem y hy.1, by rw [hΨ.fwd_inv y hy.1]; exact hy⟩
  have hsubU : relComp (A ω) (Ψ ω) (Wr ω) (u ω) ⊆ H \ (A ω ∪ fwdHull (w ω) (t ω)) :=
    relComp_subset hcfgω.hullIn
  have hOH : (c ω).2.1 '' (H \ fwdHull (Wr ω) (u ω)) ⊆ H := fun z hz => (hsubU (hsub hz)).1
  refine chartTransport_eq_couplingMean_of_relComp (hc ω) (hℓ ω) (LΨ := LΨ ω) (ℓ₀ := ℓ₀) (wU := wU)
    (fun y hy => hlift ω y hy.1) ?_ ?_ (fun y hy => ?_) a hψ
  · exact ((Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hwU).add
      ((Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hu₀).mono sdiff_subset)).mono
      (hsub.trans hsubU)
  · exact rep_add_smoothDist hOH (fun z hz => hwU z (hsubU (hsub hz))) hu₀
      (fun φ hφ => hrepU φ (hφ.trans (hsub.trans hsubU)))
  · have hz : (c ω).2.1 y ∈ relComp (A ω) (Ψ ω) (Wr ω) (u ω) := hsub ⟨y, hy, rfl⟩
    have hΨy : Ψ ω ((c ω).2.1 y) = y := by rw [hcinv ω y hy.1]; exact hΨ.fwd_inv y hy.1
    have e := hEq hz
    simp only at e
    rw [e, hcfgω.cand, hΨy]

end Mean

end InteractingSLE.Theorem14.SB.FinRel
