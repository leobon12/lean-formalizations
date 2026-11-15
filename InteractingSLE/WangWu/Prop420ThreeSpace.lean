/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop420ThreeLines
import InteractingSLE.Spec.Sec7.Lemma71LMain

/-!
# Wang–Wu Proposition 4.20 for three ordered lines, the middle one stopped: the three-line space and its law

Packet PROVE-WW-B22. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.20
(text dump L1701–1745): "If either line is stopped in the filtration enlarged by the other line, the same rule holds on
all exposed sides. The statement also holds for three ordered seed lines, one of which may be stopped in the
filtration enlarged by the other two." Its proof: "The single-line determinism proved in Proposition 4.18 and Lemma
4.5 give locality. The local-set union boundary lemma identifies the mean on the relative interior of every exposed
arc. […] For a stopped line, compare first with the full union. […] At points on the other line not belonging to the
stopped line, compactness gives positive distance from the stopped set and the same boundary lemma applies directly.
Only the tip prime ends remain; Corollary 4.8 applies again. For three ordered lines, each complementary component is
bounded by two adjacent exposed arcs." With Corollary 4.23 ("the full conditional field law given its local-set
information is a kernel depending only on `A`") this is the Gaussian law, given the walls and the middle prefix, with
the identified mean in every complementary component.

The specification's form of this statement is Remark 6.7's three-curve law, landed curve-generically as
`Sec7.Lemma71L.ae_condExp_exp_eq_three_of_le_aeSigma` (Lemma 6.2's hypotheses on each curve, a zero-boundary GFF, a
middle stopping time in path form, and the prime-end premise `Sec7.Lemma71G.IsThreeChartPremise`: every prime end of
the component outside a finite set either lies on the stopped union where the full three-line union is contained in it
nearby, with the full-union mean converging to the candidate, or lies on the outer union of the two complete walls
where the stopped union is contained in it nearby, with the wall-union mean converging to the candidate — exactly the
two comparisons of Wang–Wu's proof — the conclusion being Corollary 4.8's identification and the Gaussian kernel).

This file
* defines the **three-line space** `SeedThree.IsThreeLineSpace P h u₀ β α γ`: the curve-generic part of the
  specification's `Sec7.Lemma72B.IsThreeCurveSpace` (a measurable field `h` whose centred field `h − u₀` is a
  zero-boundary GFF, `u₀` bounded harmonic, Lemma 6.2's hypotheses for each of the three curves, and almost surely: the
  curves avoid `ℝ ∖ {0}`, are simple proper arcs, ordered `β` (left wall) / `γ` (middle) / `α` (right wall), and the
  middle one shares no arc with either wall), with no flow-line or `κ < 4` clause;
* defines the **`κ = 4` seed three-line space** `SeedThree.IsSeedThreeSpace`: a three-line space whose curves are the
  seed lines of nonnegative two-seed couplings of `h + u₂`, `h + u₁`, `h` (`u₁ < 0 < u₂`);
* proves **`SeedThree.IsThreeLineSpace.ae_condExp_exp_eq_three`**: the stopped three-line law for the original field
  `h` on every such space (Proposition 4.20 stopped / three lines with Corollary 4.23, given its prime-end premise);
* proves **`SeedThree.isSeedThreeSpace_of_seed`**: the seed lines of three nonnegative couplings at heights
  `u₁ < 0 < u₂` form a three-line space as soon as they are almost surely ordered (Proposition 4.19) and share no arc
  (Lemma 4.21) — Lemma 6.2's hypotheses are `SeedField.exists_lemma62Version_seed`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedThree

open Sec7.Lemma71G (IsLemma62Curve IsThreeChartPremise)
open Sec7.Lemma71I (IsSimpleProper realPath NoCommonArc)
open Sec6 LocalSets

section Space

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The three-line space** (curve-generic part of the specification's `Sec7.Lemma72B.IsThreeCurveSpace`): a
measurable field `h` and a bounded harmonic `u₀` on `ℍ` whose difference `h − u₀` is a zero-boundary GFF; three curves
`β` (left wall), `α` (right wall), `γ` (middle) with Lemma 6.2's hypotheses for `h − u₀`; almost surely they avoid
`ℝ ∖ {0}`, are simple proper arcs, the triple `(α, γ, β)` is ordered (`WangWu.IsOrderedArcs`, right to left) and the
middle curve shares no nontrivial arc with either wall. -/
def IsThreeLineSpace (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) :
    Prop :=
  Measurable h ∧ (InnerProductSpace.HarmonicOnNhd u₀ H ∧ ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M) ∧
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
    IsLemma62Curve β (WholeField.centredField h u₀) P ∧ IsLemma62Curve α (WholeField.centredField h u₀) P ∧
    IsLemma62Curve γ (WholeField.centredField h u₀) P ∧
    ∀ᵐ ω ∂P, (∀ i (t : ℝ≥0) (x : ℝ), x ≠ 0 → Three.threeCurves β α γ i ω t ≠ x) ∧
      IsSimpleProper (β ω) ∧ IsSimpleProper (α ω) ∧ IsSimpleProper (γ ω) ∧
      IsOrderedArcs (realPath (α ω)) (realPath (γ ω)) (realPath (β ω)) ∧
      NoCommonArc (γ ω) (α ω) ∧ NoCommonArc (γ ω) (β ω)

/-- **The `κ = 4` seed three-line space** (Proposition 4.24's configuration: "Choose `a, b` sufficiently large that the
seed lines at heights `u₁, 0, u₂` are all non-boundary-intersecting"): a three-line space for a GFF `h` with the
two-seed data of `(ρL; ρR)` and its bounded harmonic extension `u₀`, whose left wall, right wall and middle curve are,
almost surely on `[0, ∞)`, the seed lines of optional hull couplings of the nonnegative words of heights
`u₂ > 0 > u₁` and `0` with the fields `h + u₂`, `h + u₁`, `h`. -/
def IsSeedThreeSpace (rL rR u₁ u₂ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ)
    (β α γ : Ω → ℝ≥0 → ℂ) : Prop :=
  u₁ < 0 ∧ 0 < u₂ ∧ 0 ≤ rL - u₂ / wwLambda ∧ 0 ≤ rR + u₁ / wwLambda ∧
    IsGFFWithBoundaryData P h (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
      LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) ∧
    IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
      LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀ ∧
    IsThreeLineSpace P h u₀ β α γ ∧
    ∀ (c : ℝ) (η : Ω → ℝ≥0 → ℂ), (c, η) ∈ ({(u₂, β), (u₁, α), (0, γ)} : Set (ℝ × (Ω → ℝ≥0 → ℂ))) →
      ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
        (ζ : Ω → ℝ≥0∞),
        IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - c / wwLambda)
          (fun _ => rR + c / wwLambda) P 𝓕 W VL VR B ζ (fun ω => Exist.flowField 0 c (h ω)) ∧
        ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ realPath (η ω) = seedLine ζ W ω

end Space

/-! ### The stopped three-line law -/

section Law

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {τ : Ω → ℝ≥0∞}
  {S : Hist → Hist → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- **Proposition 4.20 for three ordered lines, the middle one stopped, with Corollary 4.23** (the stopped three-line
law). On a three-line space, let the middle line be stopped at `τ = S(β, α, γ)`, a stopping time of the filtration of
the middle path enlarged by the two complete walls (path form, Galmarino), and let `𝒢` be any σ-algebra inside the
completion of the germs of `A(τ) = β ∪ α ∪ γ[0, τ]` and the labelled histories (e.g. the walls and the middle prefix).
On an event `E ∈ 𝒢` where the prime-end premise holds in the component of `ℍ ∖ A(τ)` containing the support of the
test function `φ`, with mean value `M` and variance `V` (both `𝒢`-measurable), the conditional characteristic function
of `(h, φ)` given `𝒢` is `exp(i M) exp(−V/2)`: the field in that component is the identified bounded harmonic mean
(`G ∘ φ_C − χ L`, the mean pairing being `M`) plus a zero-boundary GFF of the component (`V = G_C(φ, φ)`). -/
theorem IsThreeLineSpace.ae_condExp_exp_eq_three (hS : IsThreeLineSpace P h u₀ β α γ)
    (hSm : Measurable fun z : (Hist × Hist) × (ℚ≥0 → ℂ) => S z.1.1 z.1.2 z.2)
    (hSg : ∀ x y c c', (∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ S x y c) → c q = c' q) → S x y c' = S x y c)
    (hτ : ∀ ω, τ ω = S (histOf (pathCoord (β ω)) ⊤) (histOf (pathCoord (α ω)) ⊤) (pathCoord (γ ω)))
    {gS gL gT : Ω → DistOn upperHalfPlaneOpens}
    (hgS : IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops τ))
      (WholeField.centredField h u₀) P gS)
    (hgL : IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL)
    (hgT : IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
      (WholeField.centredField h u₀) P gT) (χ : ℝ)
    (φ : TestOn upperHalfPlaneOpens) (h𝒢m : 𝒢 ≤ mΩ)
    (h𝒢 : 𝒢 ≤ aeSigma (germSigma (explored (Three.threeCurves β α γ) (Three.threeStops τ))
        (WholeField.centredField h u₀) ⊔ stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ)) P)
    {E : Set Ω} (hE : MeasurableSet[𝒢] E) {M V : Ω → ℝ} (hM : Measurable[𝒢] M) (hV : Measurable[𝒢] V)
    (hprem : ∀ᵐ ω ∂P, ω ∈ E → IsThreeChartPremise
      (explored (Three.threeCurves β α γ) (Three.threeStops τ) ω)
      (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
      (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀ χ φ
      (M ω) (V ω)) :
    ∀ᵐ ω ∂P, ω ∈ E → P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝒢] ω =
      Complex.exp (Complex.I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * V ω) : ℝ) : ℂ) := by
  obtain ⟨-, hu₀, hh0, hβ, hα, hγ, -⟩ := hS
  have hlaw := Sec7.Lemma71L.ae_condExp_exp_eq_three_of_le_aeSigma hh0 hβ hα hγ hSm hSg hτ hgS hgL hgT hu₀.1
    hu₀.2 χ φ h𝒢m h𝒢 hE hM hV hprem
  have hfield : (fun ω' => Complex.exp (Complex.I *
      ((WholeField.centredField h u₀ ω' φ + ∫ x, u₀ x * φ x : ℝ) : ℂ))) =
      fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) := by
    funext ω'
    rw [WholeField.centredField_apply h hu₀.1 ω' φ, sub_add_cancel]
  rwa [hfield] at hlaw

end Law

/-! ### The seed lines form a three-line space -/

section Seed

/-- `seedLine` only reads the positive part of its time. -/
theorem seedLine_toNNReal {Ω : Type*} (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) :
    seedLine ζ W ω (t.toNNReal : ℝ) = seedLine ζ W ω t := by
  simp only [seedLine, Real.toNNReal_coe]

/-- A path agreeing with a seed line on `[0, ∞)` has that seed line as its real-time path. -/
theorem realPath_eq_seedLine {Ω : Type*} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {ω : Ω} {η : ℝ≥0 → ℂ}
    (hη : ∀ t : ℝ≥0, η t = seedLine ζ W ω t) : realPath η = seedLine ζ W ω := by
  funext t
  simp only [realPath, hη, seedLine_toNNReal]

/-- A continuous path whose real-time path is a proper arc is a simple proper curve. -/
theorem isSimpleProper_of_isProperArc {η : ℝ≥0 → ℂ} (hc : Continuous η) (harc : IsProperArc (realPath η)) :
    IsSimpleProper η := by
  have hr : ∀ t : ℝ≥0, realPath η t = η t := Sec7.Lemma71I.realPath_coe η
  refine ⟨hc, fun s t hst => ?_, ?_, fun t ht => ?_, ?_⟩
  · have := harc.inj (show (s : ℝ) ∈ Ici (0 : ℝ) from s.2) (show (t : ℝ) ∈ Ici (0 : ℝ) from t.2)
      (by rw [hr, hr, hst])
    exact NNReal.coe_injective this
  · rw [← hr 0, NNReal.coe_zero]; exact harc.zero
  · rw [← hr t]; exact harc.mem_H _ ht
  · have := harc.tendsto.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
    refine this.congr fun t => ?_
    simp only [Function.comp_apply, id, hr]

/-- A simple proper curve avoids `ℝ ∖ {0}`. -/
theorem IsSimpleProper.ne_real {η : ℝ≥0 → ℂ} (hη : IsSimpleProper η) (t : ℝ≥0) {x : ℝ} (hx : x ≠ 0) :
    η t ≠ x := by
  intro hxt
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, hη.2.2.1] at hxt
    exact hx (by exact_mod_cast hxt.symm)
  · have hH := hη.2.2.2.1 t (pos_iff_ne_zero.2 ht)
    rw [hxt] at hH
    have : (0 : ℝ) < ((x : ℂ)).im := hH
    simp at this

/-- **No common arc from the empty interior of the contact times** (the converse of
`Sec7.Lemma71I.interior_contact_eq_empty`). -/
theorem noCommonArc_of_interior_eq_empty {γ α : ℝ≥0 → ℂ}
    (h : interior {t ∈ Ici (0 : ℝ) | realPath γ t ∈ arcRange (realPath α)} = ∅) : NoCommonArc γ α := by
  intro a b ha hab
  by_contra hne
  push Not at hne
  have hsub : Ioo (a : ℝ) b ⊆ {t ∈ Ici (0 : ℝ) | realPath γ t ∈ arcRange (realPath α)} := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := (show (0 : ℝ) < a by exact_mod_cast ha).le.trans ht.1.le
    refine ⟨ht0, ?_⟩
    rw [Sec7.Lemma71I.arcRange_realPath]
    have := hne t.toNNReal (by rw [Real.coe_toNNReal _ ht0]; exact ht.1.le)
      (by rw [Real.coe_toNNReal _ ht0]; exact ht.2.le)
    exact this
  have hne' : (Ioo (a : ℝ) b).Nonempty := nonempty_Ioo.2 (by exact_mod_cast hab)
  obtain ⟨t, ht⟩ := hne'
  have := interior_maximal hsub isOpen_Ioo ht
  rw [h] at this
  exact this

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **A version of a nonnegative seed line**: Lemma 6.2's hypotheses, and almost surely an infinite lifetime, the seed
line as its real-time path, and a simple proper curve. -/
theorem exists_seedVersion (hhm : Measurable h) {rL rR c : ℝ} (hL : 0 ≤ rL - c / wwLambda)
    (hR : 0 ≤ rR + c / wwLambda) {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - c / wwLambda)
      (fun _ => rR + c / wwLambda) P 𝓕 W VL VR B ζ (fun ω => Exist.flowField 0 c (h ω)))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) :
    ∃ η : Ω → ℝ≥0 → ℂ, IsLemma62Curve η (WholeField.centredField h u₀) P ∧
      ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ realPath (η ω) = seedLine ζ W ω ∧ IsSimpleProper (η ω) := by
  obtain ⟨η, hη, hae⟩ := SeedField.exists_lemma62Version_seed hhm hL hR hC hu₀
  refine ⟨η, hη, ?_⟩
  filter_upwards [hae] with ω hω
  have he := realPath_eq_seedLine hω.2.1
  exact ⟨hω.1, he, isSimpleProper_of_isProperArc (hη.1 ω) (he ▸ hω.2.2)⟩

/-- **The seed lines of three nonnegative couplings form a `κ = 4` seed three-line space** (Proposition 4.24's
configuration). Given a GFF `h` with two-seed data, heights `u₁ < 0 < u₂` with nonnegative words, optional hull
couplings of the words of heights `u₂`, `u₁`, `0` with `h + u₂`, `h + u₁`, `h`, whose seed lines are almost surely
ordered (Proposition 4.19: `IsOrderedArcs`, right wall `u₁`, middle `0`, left wall `u₂`) and such that the middle line
spends no time interval on either wall (Lemma 4.21), versions of the three seed lines form an `IsSeedThreeSpace`. -/
theorem isSeedThreeSpace_of_seed {rL rR u₁ u₂ : ℝ} (hu₁ : u₁ < 0) (hu₂ : 0 < u₂) (hL : 0 ≤ rL - u₂ / wwLambda)
    (hR : 0 ≤ rR + u₁ / wwLambda)
    (hh : IsGFFWithBoundaryData P h (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
      LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {𝓕β 𝓕α 𝓕γ : Filtration ℝ≥0 mΩ} {Wβ Wα Wγ : ℝ≥0 → Ω → ℝ} {VLβ VRβ VLα VRα VLγ VRγ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {Bβ Bα Bγ : ℝ≥0 → Ω → ℝ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
    (hCβ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₂ / wwLambda)
      (fun _ => rR + u₂ / wwLambda) P 𝓕β Wβ VLβ VRβ Bβ ζβ (fun ω => Exist.flowField 0 u₂ (h ω)))
    (hCα : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₁ / wwLambda)
      (fun _ => rR + u₁ / wwLambda) P 𝓕α Wα VLα VRα Bα ζα (fun ω => Exist.flowField 0 u₁ (h ω)))
    (hCγ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - 0 / wwLambda)
      (fun _ => rR + 0 / wwLambda) P 𝓕γ Wγ VLγ VRγ Bγ ζγ (fun ω => Exist.flowField 0 0 (h ω)))
    (hord : ∀ᵐ ω ∂P, IsOrderedArcs (seedLine ζα Wα ω) (seedLine ζγ Wγ ω) (seedLine ζβ Wβ ω))
    (hnc : ∀ᵐ ω ∂P,
      interior {t ∈ Ici (0 : ℝ) | seedLine ζγ Wγ ω t ∈ arcRange (seedLine ζα Wα ω)} = ∅ ∧
        interior {t ∈ Ici (0 : ℝ) | seedLine ζγ Wγ ω t ∈ arcRange (seedLine ζβ Wβ ω)} = ∅) :
    ∃ β α γ : Ω → ℝ≥0 → ℂ, IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ := by
  have hl : 0 < wwLambda := wwLambda_pos
  have hdiv₁ : u₁ / wwLambda < 0 := div_neg_of_neg_of_pos hu₁ hl
  have hdiv₂ : 0 < u₂ / wwLambda := div_pos hu₂ hl
  have hLα : 0 ≤ rL - u₁ / wwLambda := by linarith
  have hRβ : 0 ≤ rR + u₂ / wwLambda := by linarith
  have hLγ : 0 ≤ rL - 0 / wwLambda := by rw [zero_div, sub_zero]; linarith
  have hRγ : 0 ≤ rR + 0 / wwLambda := by rw [zero_div, add_zero]; linarith
  have hhm : Measurable h := hh.1
  obtain ⟨β, hβ, hβae⟩ := exists_seedVersion hhm hL hRβ hCβ hu₀.1
  obtain ⟨α, hα, hαae⟩ := exists_seedVersion hhm hLα hR hCα hu₀.1
  obtain ⟨γ, hγ, hγae⟩ := exists_seedVersion hhm hLγ hRγ hCγ hu₀.1
  refine ⟨β, α, γ, hu₁, hu₂, hL, hR, hh, hu₀, ⟨hhm, ⟨hu₀.1, hu₀.2.1⟩,
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀, hβ, hα, hγ, ?_⟩, ?_⟩
  · filter_upwards [hβae, hαae, hγae, hord, hnc] with ω hβω hαω hγω hoω hnω
    obtain ⟨-, hβr, hβs⟩ := hβω
    obtain ⟨-, hαr, hαs⟩ := hαω
    obtain ⟨-, hγr, hγs⟩ := hγω
    refine ⟨fun i t x hx => ?_, hβs, hαs, hγs, ?_, ?_, ?_⟩
    · fin_cases i
      · exact IsSimpleProper.ne_real hβs t hx
      · exact IsSimpleProper.ne_real hαs t hx
      · exact IsSimpleProper.ne_real hγs t hx
    · rw [hαr, hγr, hβr]; exact hoω
    · refine noCommonArc_of_interior_eq_empty ?_
      rw [hγr, hαr]; exact hnω.1
    · refine noCommonArc_of_interior_eq_empty ?_
      rw [hγr, hβr]; exact hnω.2
  · intro c η hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨𝓕β, Wβ, VLβ, VRβ, Bβ, ζβ, hCβ, hβae.mono fun ω hω => ⟨hω.1, hω.2.1⟩⟩
    · exact ⟨𝓕α, Wα, VLα, VRα, Bα, ζα, hCα, hαae.mono fun ω hω => ⟨hω.1, hω.2.1⟩⟩
    · exact ⟨𝓕γ, Wγ, VLγ, VRγ, Bγ, ζγ, hCγ, hγae.mono fun ω hω => ⟨hω.1, hω.2.1⟩⟩

end Seed

end InteractingSLE.WangWu.SeedThree
