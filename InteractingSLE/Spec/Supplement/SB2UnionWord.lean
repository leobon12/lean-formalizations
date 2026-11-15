/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2UnionLift

/-!
# Lemma SB2 at a junction: the union word boundary datum on the relative component

Packet PROVE-T14-SB2UNION. The deterministic core of SB2's union mean ("The active word and the one branch", p. 632):
for a retained set `A` with chart `Ψ` landing off a finite set, a physical explored hull `K_t` that may touch `A`, and a
relative chain `(Wr, ηr)` at time `u`, the relative component `relComp A Ψ Wr u` (the unbounded component of
`ℍ ∖ (A ∪ K_t)`, `SB2UnionChart`) carries the union word boundary datum of the two individual means
(`HasUnionWordBoundaryOn`, the restriction of `SB.SewGerm.HasUnionWordBoundary` to the components through a set).

The landed disjoint configuration (`Supp8.Q3Rel.relUnionWordBoundaryOffStatement`) is replaced by the **junction
configuration** (`IsRelConfigJ`):

* the hull hypotheses `hKin`, `hKfr` of `SB2UnionChart`;
* a **free left collar**: a point `x₁ < a_L` such that every real point of `(x₁, a_R)` is good, the points of
  `(x₁, a_L)` land at real points, the points of the relative hull image other than its right base land on the closed
  explored hull, and some point `x₀ ∈ (x₁, a_L)` lands at an untouched real point `≠ 0` (off `cl A` and `cl K_t`);
* **finitely many junction landings**: finitely many points of `[a_L, a_R)` land on `cl A`, and finitely many real
  points off the relative hull image land on `cl (K_t ∖ A)` ("there are only finitely many surviving angle, connector
  and original marks and finitely many incident fibers over each of their physical images", p. 632);

and the remaining data exactly as in `Q3Rel.IsRelConfigOff` (chart, chains, the exceptional points off the closed
relative hull, the tip identity, the three bounded harmonic extensions, the side and flowed words, the candidate).

* `retained_side_rel`, `explored_side_rel`: the two alternatives at the good real points;
* **`hasUnionWordBoundaryOn_relComp`** / `IsRelConfigJ.hasUnionWordBoundaryOn`: the datum on `relComp`.

Deterministic. Conditional helpers with distinct names; they replace no source theorem. R48: serves Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Theorem14.SB.Union

open Supp8.BHMean (jointInv jointFwd jointLift jointChart jointLog IsSideWord IsFlowedWord)
open Supp8.Q3Rel (IsRetainedChartOff IsGoodPt)
open Supp8.RelTrans (nhdsWithin_H_neBot_of_mem_Hbar ofReal_mem_Hbar transBdry liftDiff)
open WangWu (chartAL chartAR)

/-- **The union word boundary datum on the components through `C`** (`SB.SewGerm.HasUnionWordBoundary` restricted to
`z₀ ∈ C`). -/
def HasUnionWordBoundaryOn (C A₁ A₂ : Set ℂ) (u₀ v w₁ w₂ : ℂ → ℝ) (χ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) : Prop :=
  ∀ z₀ ∈ C, ∃ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
    IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (A₁ ∪ A₂)) z₀) ∧
    IsConformalBijection φc (connectedComponentIn (H \ (A₁ ∪ A₂)) z₀) H ∧
    IsBoundedHarmonicExtension b jumps G ∧
    ContinuousOn L (connectedComponentIn (H \ (A₁ ∪ A₂)) z₀) ∧
    (∀ z ∈ connectedComponentIn (H \ (A₁ ∪ A₂)) z₀,
      deriv φc z = ‖deriv φc z‖ * Complex.exp (L z * Complex.I)) ∧
    E.Finite ∧
    EqOn v (fun z => G (φc z) - χ * L z) (connectedComponentIn (H \ (A₁ ∪ A₂)) z₀) ∧
    ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      (∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        p ∈ A₁ ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₂ ∩ ball p r ⊆ A₁) ∧
        Tendsto (fun ζ => (w₁ (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
          (𝓝[ball 0 1] q) (𝓝 0)) ∨
      (∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        p ∈ A₂ ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₁ ∩ ball p r ⊆ A₂) ∧
        Tendsto (fun ζ => (w₂ (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
          (𝓝[ball 0 1] q) (𝓝 0))

/-- The landed datum is the case `C = ℍ ∖ (A₁ ∪ A₂)`. -/
theorem HasUnionWordBoundaryOn.of_hasUnionWordBoundary {A₁ A₂ : Set ℂ} {u₀ v w₁ w₂ : ℂ → ℝ} {χ : ℝ}
    {b : ℝ → ℝ} {jumps : Finset ℝ} (h : SewGerm.HasUnionWordBoundary A₁ A₂ u₀ v w₁ w₂ χ b jumps) {C : Set ℂ}
    (hC : C ⊆ H \ (A₁ ∪ A₂)) : HasUnionWordBoundaryOn C A₁ A₂ u₀ v w₁ w₂ χ b jumps :=
  fun z₀ hz₀ => h z₀ (hC hz₀)

section Sides

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ}
  {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G u₀ w₁ w₂ v : ℂ → ℝ}

/-- **The retained-side alternative at a junction** (`Q3Rel.retained_side` with the junction hypothesis `hKin`): at a
real point `x` off the relative hull image whose joint landing point is off `cl (K_t ∖ A)`, the joint parametrization
lands at a point `p` of `A ∪ ℝ` near which `K_t` lies in `A`, and the retained mean minus the candidate tends to `0`. -/
theorem retained_side_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hG₀ : IsBoundedHarmonicExtension β₀ S₀ G₀) (hG : IsBoundedHarmonicExtension βu Su G)
    (hflow : IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u))
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    {x : ℝ} (hxS : x ∉ Su) (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u))
    (hyS : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ S₀) (hyb : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ Sb)
    (hpK : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure (fwdHull w t \ A)) :
    ∃ p : ℂ, Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) ∧ p ∈ A ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, fwdHull w t ∩ ball p r ⊆ A) ∧
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
  rw [hpe] at hpK
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
  obtain ⟨r, hr, hball⟩ := Supp8.GB6.exists_ball_disjoint_of_notMem_closure hpK
  refine ⟨p, hjoint, hpAR, ⟨r, hr, fun z hz => ?_⟩, ?_⟩
  · by_contra hzA
    exact Set.disjoint_left.1 hball hz.2 ⟨hz.1, hzA⟩
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

/-- **The explored-side alternative at a junction** (`Q3Rel.explored_side` with `hKin`): at a real point `x ≠ 0` of
the relative hull image whose joint landing point lies on the closed explored hull and off `cl A`, with the transition
facts, the joint parametrization lands at a point `p` of `K_t ∪ ℝ` near which `A` lies in `K_t`, and the explored mean
minus the candidate tends to `0`. -/
theorem explored_side_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u)
    (hGE : IsBoundedHarmonicExtension βE SE GE) (hG : IsBoundedHarmonicExtension βu Su G)
    (hsE : IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam)
    (hsu : IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam)
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t))
    {T : ℝ → ℝ} {x : ℝ} (hx0 : x ≠ 0) (hxK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u))
    (hg : IsGoodPt Sb Wr u (x : ℂ))
    (hpK : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∈ closure (fwdHull w t))
    (hpA : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure A)
    (hxS : x ∉ Su) (hTS : T x ∉ SE) (hsign : 0 < T x ↔ 0 < x) (hT0 : T x ≠ 0)
    (hTK : extendFrom H (fwdMapInv w t) (T x : ℂ) ∈ closure (fwdHull w t))
    (hTl : Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] (x : ℂ)) (𝓝 (T x : ℂ)))
    (hLl : Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
      (𝓝[H] (x : ℂ)) (𝓝 0)) :
    ∃ p : ℂ, Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) ∧ p ∈ fwdHull w t ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, A ∩ ball p r ⊆ fwdHull w t) ∧
      Tendsto (fun y => (w₂ (jointInv Ψi Wr u y) + u₀ (jointInv Ψi Wr u y)) -
        (G (jointFwd Ψ Wr u (jointInv Ψi Wr u y)) - χ * jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y)))
        (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hjoint := (Supp8.Q3Rel.tendsto_jointInv hΨ hWr hWr0 hηr hu hxbar hg).1
  set p : ℂ := extendFrom H (jointInv Ψi Wr u) (x : ℂ) with hpdef
  have hpbar : p ∈ Hbar := by
    rw [← closure_H]; exact closure_mono (isHPHull_fwdHull hw ht).1 hpK
  have hpKR : p ∈ fwdHull w t ∪ {z : ℂ | z.im = 0} := by
    by_cases hpH : p ∈ H
    · left
      by_contra hpn
      exact notMem_compl_of_mem_closure hw ht hpK ⟨hpH, hpn⟩
    · exact Or.inr (le_antisymm (not_lt.1 hpH) hpbar)
  obtain ⟨r, hr, hball⟩ := Supp8.GB6.exists_ball_disjoint_of_notMem_closure hpA
  refine ⟨p, hjoint, hpKR, ⟨r, hr, fun z hz => absurd hz.1 (Set.disjoint_left.1 hball hz.2)⟩, ?_⟩
  -- the limit
  have hJC : ∀ y ∈ H, jointInv Ψi Wr u y ∈ H \ fwdHull w t := fun y hy => by
    have h := relComp_subset hKin (jointInv_mem_relComp hΨ hWr hWr0 hu hy)
    exact ⟨h.1, fun hk => h.2 (Or.inr hk)⟩
  have hTH : Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] (x : ℂ)) (𝓝[H] (T x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hTl, eventually_nhdsWithin_of_forall fun y hy =>
      QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht (hJC y hy)⟩
  have hGEl := (hGE.2.2 (T x) hTS).comp hTH
  have hGl : Tendsto G (𝓝[H] (x : ℂ)) (𝓝 (βu x)) := hG.2.2 x hxS
  have hsum := (hGEl.sub hGl).sub (hLl.const_mul χ)
  have hβ : βE (T x) = βu x := by
    rw [hsE (T x) hTS hT0 hTK, hsu x hxS hx0 hxK]
    simp only [hsign]
  rw [hβ, sub_self, mul_zero, sub_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have e2 := hw₂ (hJC y hy)
  simp only at e2
  simp only [Function.comp, jointLift, jointFwd_jointInv_rel hΨ hWr hWr0 hu hy, e2]
  ring

end Sides

/-! ### The junction configuration and its union word boundary datum -/

/-- **The deterministic junction configuration** (module docstring): the data of `Q3Rel.IsRelConfigOff` with the hull
identity and the disjointness of the closed hulls replaced by the junction hull hypotheses, the free left collar and
finitely many junction landings. -/
structure IsRelConfigJ (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (Sb : Finset ℝ) (w Wr : ℝ → ℝ) (η ηr : ℝ → ℂ)
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
  finA : {x : ℝ | x ∈ Ico (chartAL Wr u) (chartAR Wr u) ∧
    extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∈ closure A}.Finite
  finK : {x : ℝ | extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u) ∧
    extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∈ closure (fwdHull w t \ A)}.Finite
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

/-- **The union word boundary datum of the junction configuration on the relative component** (SB2, p. 632: "The
finite-exception Poisson uniqueness argument identifies the entire mean"; the boundary datum it needs). -/
theorem IsRelConfigJ.hasUnionWordBoundaryOn
    (hc : IsRelConfigJ A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t)) :
    HasUnionWordBoundaryOn (relComp A Ψ Wr u) A (fwdHull w t) u₀ v w₁ w₂ χ βu Su := by
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
    extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∈ closure A} with hXA
  set XK : Set ℝ := {x : ℝ | extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u) ∧
    extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∈ closure (fwdHull w t \ A)} with hXK
  set X : Set ℝ := insert 0 (insert (chartAR Wr u) ((↑Su : Set ℝ) ∪ φ '' (↑S₀ : Set ℝ) ∪
    (R' ∩ T ⁻¹' (↑SE : Set ℝ)) ∪ Xb ∪ XA ∪ XK)) with hX
  have hmono := strictMonoOn_transBdry_Ico (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl hIV
  have hXf : X.Finite := by
    refine Set.Finite.insert _ (Set.Finite.insert _ ((((((Su.finite_toSet).union
      ((S₀.finite_toSet).image φ)).union ?_).union
      (Supp8.Q3Rel.finite_badPts hWr hWr0 hηr hu hc.bad)).union hc.finA).union hc.finK))
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
  have hxK' : x ∉ XK := hsub fun y hy => Or.inr hy
  clear hX'
  by_cases hxK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u)
  · -- the explored side
    have hxI := Supp8.RelTrans.hullImage_subset_Icc hηr hWr hWr0 hu hxK
    have hxI' : x ∈ Ico (chartAL Wr u) (chartAR Wr u) := ⟨hxI.1, lt_of_le_of_ne hxI.2 hxAR⟩
    have hxR' : x ∈ R' := ⟨hx0, hxI', hxK⟩
    have hg : IsGoodPt Sb Wr u (x : ℂ) := Supp8.Q3Rel.goodPt_of_mem_closure hc.bad hxK
    have hpK := hc.landK x hxI'
    have hpA : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure A := fun h => hxA ⟨hxI', h⟩
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
    obtain ⟨p, hp, hpKR, hr, hlim⟩ := explored_side_rel hΨ hw ht hWr hWr0 hηr hu hKin hc.bheE hc.bheu hc.sideE
      hc.sideu hw₂ hx0 hxK hg hpK hpA hxS hTS hsign hT0 hTK (hvTe ▸ hTl) hLl
    exact Or.inr ⟨p, hp.comp hcay, hpKR, hr, hlim.comp hcay⟩
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
    have hpK : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure (fwdHull w t \ A) := fun h => hxK' ⟨hxK, h⟩
    obtain ⟨p, hp, hpA, hr, hlim⟩ := retained_side_rel hΨ hWr hWr0 hηr hu hc.bhe₀ hc.bheu hc.flow hw₁ hxS hxK hyS
      hyb hpK
    exact Or.inl ⟨p, hp.comp hcay, hpA, hr, hlim.comp hcay⟩

end Assembly

end InteractingSLE.Theorem14.SB.Union
