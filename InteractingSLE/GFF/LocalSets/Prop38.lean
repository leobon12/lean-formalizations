import InteractingSLE.GFF.LocalSets.Prop38Patch

/-!
# Proposition 3.8: boundary behaviour of `𝒞_{A₁ ∪̃ A₂} − 𝒞_{A₂}`

Specification §3.2, Proposition 3.8 (p. 59; transcription `source/spec/p049-096.md#prop-3.8`):

> Assume that `D` is a bounded, simply connected domain. Let `A₁, A₂` be connected local sets. Then
> `𝒞_{A₁ ∪̃ A₂} − 𝒞_{A₂}` is almost surely a harmonic function in `D ∖ (A₁ ∪̃ A₂)` that tends to
> zero on all sequences of points in `D ∖ (A₁ ∪̃ A₂)` that tend to a limit in either:
> (i) a connected component of `A₂ ∖ A₁` (consisting of more than a single point) or
> (ii) a connected component of `A₁ ∩ A₂` (consisting of more than a single point) at a point that
> has positive distance from `(A₁ ∖ A₂) ∪ (A₂ ∖ A₁)`.

Here `D = ℍ` (local sets are defined on `ℍ`, ruling R19 (5)); a relatively closed `A ⊆ ℍ` stands for
`A ∪ ∂ℍ`, so `A₁ ∩ A₂` of the source is `(A₁ ∩ A₂) ∪ ℝ` and `A₂ ∖ A₁` is `A₂ ∖ A₁`. The
conditionally independent union is the union of conditionally independent local sets
(Proposition 3.7). "`A₂` connected" is used only through the simple connectivity of the components
of `ℍ ∖ A₂` ("These components are simply connected: `A₂` is connected and includes the ambient
boundary", p. 60), i.e. through the hypothesis that every component of `A₂ ∪ {Im ≤ 0}` is unbounded;
it holds when `A₂ ∪ ℝ` is connected (`not_isBounded_of_isPreconnected_union_real`). The
connectedness of `A₁` and the "more than a single point" conditions are not needed.

## Main results

* `IsLocalSetMean.ae_tendsto_sub_of_union` : the general form — almost surely
  `𝒞_A − 𝒞_{A₂}` is a harmonic function `u` on `ℍ ∖ A` with `u(z) → 0` at every point
  `z₀ ∈ A₂ ∪ ℝ` near which `A₁ ⊆ A₂`;
* `IsLocalSetMean.ae_tendsto_sub_of_union_of_isPreconnected` : **Proposition 3.8**, cases (i)
  and (ii), for `A₂ ∪ ℝ` connected.

## Proof (own route on `ℍ`, ruling R34)

For a rational patch `U = B(c, 4R)` and `E = {A₁ ∩ U ⊆ A₂}`, the exponential moments of
`(𝒞_A − 𝒞_{A₂})(bump)` on `E` and on the `n`-th dyadic layer of `ℍ ∖ A₂` are bounded through the two
conditional Gaussian laws (`lintegral_layer_indicator_le`), and Borel–Cantelli over the random layers
(`ae_eventually_abs_lt_of_layer`) gives uniform smallness near `∂(ℍ ∖ A₂) ∩ B(c, R)`; countably many
patches cover every point of `A₂ ∪ ℝ` near which `A₁ ⊆ A₂`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper LQGMetric
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)
open GFF (layerSet bumpMass bumpMass_pos)

/-- `v φ` is integrable for `v` continuous on an open `U ⊇ supp φ`. -/
lemma integrable_mul_test {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} (hv : ContinuousOn v U)
    (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ U) :
    Integrable fun z => v z * φ z := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (φ.hasCompactSupport.mul_left)
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ U
  · exact ((hv z hz).continuousAt (hU.mem_nhds hz)).mul φ.continuous.continuousAt
  · have h0 := (notMem_tsupport_iff_eventuallyEq).1 (fun h => hz (hφ h))
    have : (fun z => v z * φ z) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with w hw
      simp only [Pi.zero_apply] at hw; rw [hw, mul_zero]
    exact (continuousAt_congr this).2 continuousAt_const

/-- The difference of two distributions harmonic on `U` is harmonic on `U`. -/
theorem IsHarmonicDistOn.sub' {T₁ T₂ : DistOn upperHalfPlaneOpens} {U : Set ℂ} (hU : IsOpen U)
    (h₁ : IsHarmonicDistOn T₁ U) (h₂ : IsHarmonicDistOn T₂ U) :
    IsHarmonicDistOn (T₁ - T₂) U := by
  obtain ⟨v₁, hv₁, hT₁⟩ := h₁
  obtain ⟨v₂, hv₂, hT₂⟩ := h₂
  refine ⟨v₁ - v₂, hv₁.sub hv₂, fun φ hφ => ?_⟩
  have hc : ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v U → ContinuousOn v U :=
    fun v hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  rw [sub_apply, hT₁ φ hφ, hT₂ φ hφ,
    ← integral_sub (integrable_mul_test hU (hc v₁ hv₁) φ hφ)
      (integrable_mul_test hU (hc v₂ hv₂) φ hφ)]
  congr 1; funext z; simp only [Pi.sub_apply]; ring

section Prop38

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A₁ A₂ : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 3.8, general form.** Let `A₁, A₂` be local sets of a zero-boundary GFF `h` on
`ℍ`, conditionally independent given `h`, such that every component of `A₂ ∪ {Im ≤ 0}` is
unbounded (so the components of `ℍ ∖ A₂` are simply connected). For any versions `g` of
`𝒞_{A₁ ∪ A₂}` and `g₂` of `𝒞_{A₂}`, almost surely `g − g₂` is, on `ℍ ∖ (A₁ ∪ A₂)`, a harmonic
function `u`, and `u(z) → 0` as `z → z₀` in `ℍ ∖ (A₁ ∪ A₂)` for every `z₀ ∈ A₂ ∪ ℝ` that has a
neighbourhood in which `A₁ ⊆ A₂`. -/
theorem IsLocalSetMean.ae_tendsto_sub_of_union (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₂ : IsLocalSetMean A₂ h P g₂) :
    ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ (A₁ ω ∪ A₂ ω)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ - g₂ ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ A₂ ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A₁ ω ∩ ball z₀ r ⊆ A₂ ω) →
        Tendsto u (𝓝[H \ (A₁ ω ∪ A₂ ω)] z₀) (𝓝 0) := by
  classical
  have hhm := hh.measurable
  set A : Ω → Set ℂ := fun ω => A₁ ω ∪ A₂ ω with hAdef
  have hA : Measurable[mΩ, hittingSigma] A := measurable_union_hitting hA₁ hA₂
  obtain ⟨g₀, hg₀m, hg₀h, hg₀c⟩ := IsLocalSet.exists_condLaw_union_germs hh hA₁ hA₂ hci h₁ h₂
  have h𝒥le : germSigma A h ⊔
      (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) ⊔
        (germSigma A₁ h ⊔ germSigma A₂ h) ≤ mΩ :=
    sup_le (sup_le (germSigma_le hA hhm) (sup_le hA₁.comap_le hA₂.comap_le))
      (sup_le (germSigma_le hA₁ hhm) (germSigma_le hA₂ hhm))
  have hA𝒥 : germSigma A h ≤ germSigma A h ⊔
      (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) ⊔
        (germSigma A₁ h ⊔ germSigma A₂ h) := le_sup_left.trans le_sup_left
  have hA₂𝒥 : germSigma A₂ h ≤ germSigma A h ⊔
      (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) ⊔
        (germSigma A₁ h ⊔ germSigma A₂ h) := le_sup_right.trans le_sup_right
  have h₁₂𝒥 : MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma ≤
      germSigma A h ⊔
      (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) ⊔
        (germSigma A₁ h ⊔ germSigma A₂ h) := le_sup_right.trans le_sup_left
  have hg₀m' := hg₀m.mono hA𝒥 le_rfl
  have hA₁c := h₁.2.1
  have hA₂c := h₂.2.1
  have hAc := IsLocalSet.ae_relClosed_union h₁ h₂
  -- `g = g₀` on `ℍ ∖ A`, simultaneously for all test functions
  have hgg₀ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, g ω φ = g₀ ω φ := fun φ => by
    have := ae_apply_eq_of_isCondZeroBoundaryGFF (P := P) hA𝒥 h𝒥le hhm hg.1 hg₀m' hg.2.2 hg₀c φ
      MeasurableSet.univ (fun c => Eventually.of_forall fun _ _ => rfl)
    filter_upwards [this] with ω hω using hω (mem_univ ω)
  have hgeq : ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
      g ω φ = g₀ ω φ := by
    refine ae_forall_apply_eq_of_bump ?_ hg.2.1 hg₀h fun x δ hδ hB => ?_
    · filter_upwards [hAc] with ω ⟨_, ho⟩ using ⟨ho, sdiff_subset⟩
    · filter_upwards [hgg₀ (GFF.bumpTest x hδ hB)] with ω hω _ using hω
  -- the difference `D = g₀ − g₂` and its harmonic representative `u`
  set D : Ω → DistOn upperHalfPlaneOpens := fun ω => g₀ ω - g₂ ω with hDdef
  have hDm : Measurable D := LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp (hg₀m.mono (germSigma_le hA hhm) le_rfl)).sub
      ((measurable_distOn_apply φ).comp (hg₂.1.mono (germSigma_le hA₂ hhm) le_rfl))
  have hDh : ∀ᵐ ω ∂P, IsHarmonicDistOn (D ω) (H \ A ω) := by
    filter_upwards [hg₀h, hg₂.2.1, hAc] with ω h0 h2 ⟨_, ho⟩
    exact IsHarmonicDistOn.sub' ho h0 (IsHarmonicDistOn.mono h2 (fun z hz =>
      ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩))
  set u : Ω → ℂ → ℝ := fun ω => if hω : IsHarmonicDistOn (D ω) (H \ A ω) then hω.choose else 0
    with hudef
  have hu : ∀ ω, IsHarmonicDistOn (D ω) (H \ A ω) →
      InnerProductSpace.HarmonicOnNhd (u ω) (H \ A ω) ∧
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → D ω φ = ∫ z, u ω z * φ z := by
    intro ω hω
    simp only [hudef, hω, dite_true]
    exact hω.choose_spec
  -- the patches `B(c_k, 4 R_j)`
  set cen : ℕ → ℂ := TopologicalSpace.denseSeq ℂ with hcen
  set rad : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hrad
  have hrad0 : ∀ j, 0 < rad j := fun j => by positivity
  set O : Ω → Set ℂ := fun ω => H \ relClosureH (A₂ ω) with hOdef
  have hBC : ∀ p : ℕ × ℕ, ∀ m : ℕ, ∀ᵐ ω ∂P,
      ω ∈ inclEvent A₁ A₂ (ball (cen p.1) (4 * rad p.2)) → ∃ N : ℕ, ∀ n ≥ N, ∀ w ∈ O ω,
        dist w (cen p.1) < 2 * rad p.2 → (1 / 2 : ℝ) ^ (n + 1) ≤ infDist w (O ω)ᶜ →
          infDist w (O ω)ᶜ ≤ (1 / 2 : ℝ) ^ n → |u ω w| < 1 / ((m : ℝ) + 1) := by
    intro p m
    have hR := hrad0 p.2
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (GFF.eventually_params hR 1)
    have hE : MeasurableSet (inclEvent A₁ A₂ (ball (cen p.1) (4 * rad p.2))) :=
      sup_le hA₁.comap_le hA₂.comap_le _ (measurableSet_inclEvent A₁ A₂ _)
    refine ae_eventually_abs_lt_of_layer (O := O) (u := u)
      (G := fun n q => bumpPair D (bumpRad (rad p.2) n) (bumpRad_pos hR n) q /
        (bumpRad (rad p.2) n ^ 2 * bumpMass)) (n₁ := n₁) hE
      (fun n => (measurable_bumpPair hDm _).div_const _) hR
      (fun n => measurableSet_layerSet_compl hA₂ _ _ n) ?_ ?_ (by positivity)
    · filter_upwards [hA₁c, hA₂c, hDh, hAc] with ω h1 h2 hD hAω hωE
      obtain ⟨huh, hur⟩ := hu ω hD
      have hincl := (mem_inclEvent_iff isOpen_ball h1 h2).1 hωE
      have hO : O ω = H \ A₂ ω := by simp only [hOdef, relClosureH_eq h2.1 h2.2]
      have hsub : O ω ∩ ball (cen p.1) (4 * rad p.2) ⊆ H \ A ω := by
        rw [hO]
        rintro z ⟨⟨hzH, hz₂⟩, hzU⟩
        exact ⟨hzH, fun h' => h'.elim (fun hz₁ => hz₂ (hincl ⟨hz₁, hzU⟩)) hz₂⟩
      refine ⟨isOpen_H_diff_relClosureH _, fun z hz => huh z (hsub hz), fun n hn y hy => ?_⟩
      obtain ⟨hnR, hnτ, -⟩ := hn₁ n hn
      have hB : closedBall y (bumpRad (rad p.2) n) ⊆ H \ A ω := by
        refine fun z hz => hsub ⟨closedBall_bumpRad_subset hR hnτ hy hz, ?_⟩
        have hyc : dist y (cen p.1) < 3 * rad p.2 := hy.1.1.2
        have hδR : bumpRad (rad p.2) n < rad p.2 := (bumpRad_lt hR hnτ).trans_le hnR
        rw [mem_ball]
        have := dist_triangle z y (cen p.1)
        have := mem_closedBall.1 hz
        linarith
      exact bumpPair_eq_of_harmonic (T := D) (bumpRad_pos hR n) hAω.2 huh hur hB sdiff_subset
    · intro n hn y l hl
      exact lintegral_layer_indicator_le hh hA₁ hA₂ hA₁c hA₂c hunb h𝒥le hA₂𝒥 h₁₂𝒥 hg₀m' hg₀c hg₂
        hR (hn₁ n hn).2.1 y l hl
  -- assembly
  have hBC' := ae_all_iff.2 fun p => ae_all_iff.2 (hBC p)
  filter_upwards [hBC', hA₁c, hA₂c, hDh, hgeq] with ω hω h1 h2 hD hge
  obtain ⟨huh, hur⟩ := hu ω hD
  refine ⟨u ω, huh, fun φ hφ => ?_, fun z₀ hz₀ ⟨r, hr, hrA⟩ => ?_⟩
  · rw [hge φ hφ, ← hur φ hφ]
    rfl
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < r / 5 by positivity)
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z₀
      (rad j) (hrad0 j)
    have hkj : dist z₀ (cen k) < rad j := hk
    obtain ⟨mm, hmm⟩ := exists_nat_one_div_lt hε
    have hrj : rad j < r / 5 := hj
    have hU : ball (cen k) (4 * rad j) ⊆ ball z₀ r := fun w hw => by
      rw [mem_ball] at hw ⊢
      have := dist_triangle w (cen k) z₀
      rw [dist_comm (cen k) z₀] at this
      linarith
    have hE : ω ∈ inclEvent A₁ A₂ (ball (cen (k, j).1) (4 * rad (k, j).2)) :=
      (mem_inclEvent_iff isOpen_ball h1 h2).2 fun z hz => hrA ⟨hz.1, hU hz.2⟩
    obtain ⟨N, hN⟩ := hω (k, j) mm hE
    refine ⟨min (rad j) ((1 / 2 : ℝ) ^ N), lt_min (hrad0 j) (by positivity), fun {x} hxA hxz => ?_⟩
    have hrc := relClosureH_eq h2.1 h2.2
    have hxO : x ∈ O ω := by
      refine ⟨hxA.1, ?_⟩
      simp only [hrc]
      exact fun h' => hxA.2 (Or.inr h')
    have hz₀O : z₀ ∈ (O ω)ᶜ := by
      intro hzO
      rcases hz₀ with hz | hz
      · exact hzO.2 (by simp only [hrc]; exact hz)
      · have h0 : (0 : ℝ) < z₀.im := hzO.1
        have h0' : z₀.im = 0 := hz
        linarith
    have hOc : IsClosed (O ω)ᶜ := (isOpen_H_diff_relClosureH _).isClosed_compl
    have hd0 : 0 < infDist x (O ω)ᶜ :=
      (IsClosed.notMem_iff_infDist_pos hOc ⟨z₀, hz₀O⟩).1 (fun h => h hxO)
    have hdx : infDist x (O ω)ᶜ ≤ dist x z₀ := infDist_le_dist_of_mem hz₀O
    have hdN : infDist x (O ω)ᶜ < (1 / 2 : ℝ) ^ N :=
      lt_of_le_of_lt hdx (lt_of_lt_of_le hxz (min_le_right _ _))
    obtain ⟨n, hnN, hn1, hn2⟩ := GFF.exists_layer_index hd0 hdN
    have hxc : dist x (cen k) < 2 * rad j := by
      have := dist_triangle x z₀ (cen k)
      have := lt_of_lt_of_le hxz (min_le_left _ _)
      linarith
    have := hN n hnN x hxO hxc hn1 hn2
    rw [Real.dist_eq, sub_zero]
    linarith

/-- **Proposition 3.8.** Let `A₁, A₂` be local sets of a zero-boundary GFF `h` on `ℍ`,
conditionally independent given `h` (so that `A₁ ∪ A₂` is their conditionally independent union),
with `A₂ ∪ ∂ℍ` connected. For any versions `g` of `𝒞_{A₁ ∪̃ A₂}` and `g₂` of `𝒞_{A₂}`, almost surely
`g − g₂` is, on `ℍ ∖ (A₁ ∪ A₂)`, a harmonic function `u` that tends to zero along every sequence in
`ℍ ∖ (A₁ ∪ A₂)` converging to
(i) a point of `A₂ ∖ A₁`, or
(ii) a point of `A₁ ∩ A₂` (with `∂ℍ` adjoined) at positive distance from `(A₁ ∖ A₂) ∪ (A₂ ∖ A₁)`.
The source's restrictions to components with more than one point, and the connectedness of `A₁`,
are not needed. -/
theorem IsLocalSetMean.ae_tendsto_sub_of_union_of_isPreconnected
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hconn : ∀ᵐ ω ∂P, IsPreconnected (A₂ ω ∪ {z : ℂ | z.im = 0}))
    {g g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₂ : IsLocalSetMean A₂ h P g₂) :
    ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ (A₁ ω ∪ A₂ ω)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ - g₂ ω φ = ∫ z, u z * φ z) ∧
      (∀ z₀ ∈ A₂ ω \ A₁ ω, Tendsto u (𝓝[H \ (A₁ ω ∪ A₂ ω)] z₀) (𝓝 0)) ∧
      (∀ z₀ ∈ (A₁ ω ∩ A₂ ω) ∪ {z : ℂ | z.im = 0},
        (∃ r > 0, Disjoint (ball z₀ r) ((A₁ ω \ A₂ ω) ∪ (A₂ ω \ A₁ ω))) →
          Tendsto u (𝓝[H \ (A₁ ω ∪ A₂ ω)] z₀) (𝓝 0)) := by
  have hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z) := by
    filter_upwards [hconn] with ω hω using not_isBounded_of_isPreconnected_union_real hω
  filter_upwards [IsLocalSetMean.ae_tendsto_sub_of_union hh hA₁ hA₂ hci h₁ h₂ hunb hg hg₂,
    h₁.2.1, h₂.2.1] with ω ⟨u, hu, hrep, hlim⟩ ⟨_, ho₁⟩ ⟨hs₂, _⟩
  refine ⟨u, hu, hrep, fun z₀ hz₀ => ?_, fun z₀ hz₀ ⟨r, hr, hdis⟩ => ?_⟩
  · obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 ho₁ z₀ ⟨hs₂ hz₀.1, hz₀.2⟩
    exact hlim z₀ (Or.inl hz₀.1) ⟨ε, hε, fun z hz => absurd hz.1 (hεA hz.2).2⟩
  · refine hlim z₀ ?_ ⟨r, hr, fun z hz => ?_⟩
    · rcases hz₀ with hz | hz
      · exact Or.inl hz.2
      · exact Or.inr hz
    · by_contra hz₂
      exact Set.disjoint_left.1 hdis hz.2 (Or.inl ⟨hz.1, hz₂⟩)

end Prop38

end LocalSets
end InteractingSLE
