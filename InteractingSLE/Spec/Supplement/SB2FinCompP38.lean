/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinCompMom
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# Proposition 3.8 per prime end (ruling R84)

Packet PROVE-T14-SB2FIN. The component form of Proposition 3.8: almost surely `𝒞_{A₁ ∪ A₂} − 𝒞_{A₂}` is a harmonic
function `u` on `ℍ ∖ (A₁ ∪ A₂)` that tends to `0` at every point `z₀ ∈ A₂ ∪ ℝ` **along the `A₁`-free components of
`(ℍ ∖ A₂) ∩ B(z₀, r)`** (`freeNear A₁ A₂ z₀ r`: the points whose component there misses `A₁`), for every `r > 0`.

The landed general form (`LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union`) needs `A₁ ⊆ A₂` near `z₀`; that fails at
a point where `A₁` and `A₂` touch from opposite sides (the bounce points of SB2, ruling R84), while along the side
that `A₁` does not reach the means still agree. Same proof, with the random domain `O' = compFree A₁ A₂ c R` of the
`A₁`-free components of each rational patch instead of `ℍ ∖ A₂` and the event `{A₁ ∩ U ⊆ A₂}`:
`SB2FinCompEv` (chains of rational balls, measurability), `SB2FinCompMom` (the distance identity, the layers, the
moment bound via the component's Green covariance), and the landed Borel–Cantelli step
`LocalSets.ae_eventually_abs_lt_of_layer` with `O := O'`.

* **`ae_tendsto_sub_of_union_comp`** (the source's Proposition 3.8 at prime ends);
* **`ae_tendsto_comp_sub_of_union_comp`** / `_symm`: the prime-end form of `Sec6.ae_tendsto_comp_sub_of_union`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.FinRel

open LocalSets
open QuantumZipper LQGMetric
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)
open GFF (layerSet bumpMass bumpMass_pos)

/-- **The `A₁`-free points near `z₀`**: the points of `(ℍ ∖ A₂) ∩ B(z₀, r)` whose component there misses `A₁`. -/
def freeNear (A₁ A₂ : Set ℂ) (z₀ : ℂ) (r : ℝ) : Set ℂ :=
  {z | z ∈ (H \ A₂) ∩ ball z₀ r ∧ Disjoint (connectedComponentIn ((H \ A₂) ∩ ball z₀ r) z) A₁}

theorem freeNear_subset {A₁ A₂ : Set ℂ} {z₀ : ℂ} {r : ℝ} : freeNear A₁ A₂ z₀ r ⊆ H \ (A₁ ∪ A₂) := by
  intro z hz
  refine ⟨hz.1.1.1, fun h => h.elim (fun h1 => Set.disjoint_left.1 hz.2 ?_ h1) hz.1.1.2⟩
  exact mem_connectedComponentIn hz.1

section Main

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A₁ A₂ : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 3.8 per prime end.** Let `A₁, A₂` be local sets of a zero-boundary GFF `h` on `ℍ`, conditionally
independent given `h`, with every component of `A₂ ∪ {Im ≤ 0}` unbounded. For any versions `g` of `𝒞_{A₁ ∪ A₂}` and
`g₂` of `𝒞_{A₂}`, almost surely `g − g₂` is, on `ℍ ∖ (A₁ ∪ A₂)`, a harmonic function `u`, and `u(z) → 0` as `z → z₀`
within the `A₁`-free components of `(ℍ ∖ A₂) ∩ B(z₀, r)`, for every `z₀ ∈ A₂ ∪ ℝ` and every `r > 0`. -/
theorem ae_tendsto_sub_of_union_comp (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
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
      ∀ z₀ ∈ A₂ ω ∪ {z : ℂ | z.im = 0}, ∀ r > 0,
        Tendsto u (𝓝[freeNear (A₁ ω) (A₂ ω) z₀ r] z₀) (𝓝 0) := by
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
  -- the patches `B(c_k, 4 R_j)` and their `A₁`-free parts
  set cen : ℕ → ℂ := TopologicalSpace.denseSeq ℂ with hcen
  set rad : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hrad
  have hrad0 : ∀ j, 0 < rad j := fun j => by positivity
  set O : ℕ × ℕ → Ω → Set ℂ := fun p ω => compFree (A₁ ω) (A₂ ω) (cen p.1) (rad p.2) with hOdef
  have hBC : ∀ p : ℕ × ℕ, ∀ m : ℕ, ∀ᵐ ω ∂P,
      ω ∈ (univ : Set Ω) → ∃ N : ℕ, ∀ n ≥ N, ∀ w ∈ O p ω,
        dist w (cen p.1) < 2 * rad p.2 → (1 / 2 : ℝ) ^ (n + 1) ≤ infDist w (O p ω)ᶜ →
          infDist w (O p ω)ᶜ ≤ (1 / 2 : ℝ) ^ n → |u ω w| < 1 / ((m : ℝ) + 1) := by
    intro p m
    have hR := hrad0 p.2
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (GFF.eventually_params hR 1)
    have hsmall : ∀ᶠ n : ℕ in atTop, 2 * (1 / 2 : ℝ) ^ n < rad p.2 := by
      have ht : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 (2 * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 2
      rw [mul_zero] at ht
      exact ht.eventually (gt_mem_nhds hR)
    obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hsmall
    refine ae_eventually_abs_lt_of_layer (O := O p) (u := u)
      (G := fun n q => bumpPair D (bumpRad (rad p.2) n) (bumpRad_pos hR n) q /
        (bumpRad (rad p.2) n ^ 2 * bumpMass)) (n₁ := max n₁ n₂) MeasurableSet.univ
      (fun n => (measurable_bumpPair hDm _).div_const _) hR
      (fun n => measurableSet_layerSet_compFree hA₁ hA₂ _ _ n) ?_ ?_ (by positivity)
    · filter_upwards [hA₁c, hA₂c, hDh, hAc] with ω h1 h2 hD hAω _
      obtain ⟨huh, hur⟩ := hu ω hD
      have hsub : O p ω ⊆ H \ A ω := by
        intro z hz
        have hz' : z ∈ freeNear (A₁ ω) (A₂ ω) (cen p.1) (4 * rad p.2) := by
          have hrc := relClosureH_eq h2.1 h2.2
          have hrc1 := relClosureH_eq h1.1 h1.2
          have hz2 := hz.2
          simp only [patchDom, hrc, hrc1] at hz2
          refine ⟨?_, hz2⟩
          have hz1 := hz.1
          simp only [patchDom, hrc] at hz1
          exact hz1
        exact freeNear_subset hz'
      refine ⟨isOpen_compFree, fun z hz => huh z (hsub hz.1), fun n hn y hy => ?_⟩
      obtain ⟨-, hnτ, -⟩ := hn₁ n (le_of_max_le_left hn)
      have hB : closedBall y (bumpRad (rad p.2) n) ⊆ H \ A ω :=
        (closedBall_bumpRad_subset_of_layer hR hnτ hy).trans hsub
      exact bumpPair_eq_of_harmonic (T := D) (bumpRad_pos hR n) hAω.2 huh hur hB sdiff_subset
    · intro n hn y l hl
      have hn1 := hn₁ n (le_of_max_le_left hn)
      have hlay : ∀ ω, y ∈ layerSet (O p ω) (cen p.1) (rad p.2) n →
          ω ∈ {ω | y ∈ compFree (A₁ ω) (A₂ ω) (cen p.1) (rad p.2)} ∩
            {ω | y ∈ layerSet (H \ relClosureH (A₂ ω)) (cen p.1) (rad p.2) n} := fun ω hy =>
        (mem_layerSet_compFree (hn₂ n (le_of_max_le_right hn))).1 hy
      refine le_trans (lintegral_mono fun ω => ?_) (lintegral_layer_indicator_le_comp (c := cen p.1) hh hA₁ hA₂
        hA₁c hA₂c hunb h𝒥le hA₂𝒥 h₁₂𝒥 hg₀m' hg₀c hg₂ hR hn1.2.1 y l hl)
      by_cases hω : y ∈ layerSet (O p ω) (cen p.1) (rad p.2) n
      · rw [indicator_of_mem (show ω ∈ univ ∩ {ω | y ∈ layerSet (O p ω) (cen p.1) (rad p.2) n} from
          ⟨mem_univ _, hω⟩), indicator_of_mem (hlay ω hω)]
      · rw [indicator_of_notMem (fun h => hω h.2)]
        exact zero_le
  -- assembly
  have hBC' := ae_all_iff.2 fun p => ae_all_iff.2 (hBC p)
  filter_upwards [hBC', hA₁c, hA₂c, hDh, hgeq] with ω hω h1 h2 hD hge
  obtain ⟨huh, hur⟩ := hu ω hD
  refine ⟨u ω, huh, fun φ hφ => ?_, fun z₀ hz₀ r hr => ?_⟩
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
    obtain ⟨N, hN⟩ := hω (k, j) mm (mem_univ ω)
    refine ⟨min (rad j) ((1 / 2 : ℝ) ^ N), lt_min (hrad0 j) (by positivity), fun {x} hxA hxz => ?_⟩
    have hrc := relClosureH_eq h2.1 h2.2
    have hrc1 := relClosureH_eq h1.1 h1.2
    have hxc : dist x (cen k) < 2 * rad j := by
      have := dist_triangle x z₀ (cen k)
      have := lt_of_lt_of_le hxz (min_le_left _ _)
      linarith
    have hxO : x ∈ O (k, j) ω := by
      have hxP : x ∈ patchDom (A₂ ω) (cen k) (rad j) := by
        refine ⟨?_, ?_⟩
        · rw [hrc]; exact hxA.1.1
        · rw [mem_ball]; linarith [hrad0 j]
      refine ⟨hxP, ?_⟩
      rw [hrc1]
      refine hxA.2.mono_left (connectedComponentIn_mono _ fun w hw => ?_)
      have hw' := hw
      simp only [patchDom, hrc] at hw'
      exact ⟨hw'.1, hU hw'.2⟩
    have hz₀O : z₀ ∈ (O (k, j) ω)ᶜ := by
      intro hzO
      have hzP := hzO.1.1
      rcases hz₀ with hz | hz
      · exact hzP.2 (by rw [hrc]; exact hz)
      · have h0 : (0 : ℝ) < z₀.im := hzP.1
        have h0' : z₀.im = 0 := hz
        linarith
    have hOc : IsClosed (O (k, j) ω)ᶜ := isOpen_compFree.isClosed_compl
    have hd0 : 0 < infDist x (O (k, j) ω)ᶜ :=
      (IsClosed.notMem_iff_infDist_pos hOc ⟨z₀, hz₀O⟩).1 (fun h => h hxO)
    have hdx : infDist x (O (k, j) ω)ᶜ ≤ dist x z₀ := infDist_le_dist_of_mem hz₀O
    have hdN : infDist x (O (k, j) ω)ᶜ < (1 / 2 : ℝ) ^ N :=
      lt_of_le_of_lt hdx (lt_of_lt_of_le hxz (min_le_right _ _))
    obtain ⟨n, hnN, hn1, hn2⟩ := GFF.exists_layer_index hd0 hdN
    have := hN n hnN x hxO hxc hn1 hn2
    rw [Real.dist_eq, sub_zero]
    linarith

/-- **Proposition 3.8 per prime end, read in a chart** (the component form of `Sec6.ae_tendsto_comp_sub_of_union`):
almost surely, for all harmonic representatives `v` of `𝒞_{A₁ ∪ A₂}` and `v₂` of `𝒞_{A₂}`, every map `f` of the disc
and every boundary point `q` with `f(ζ) → p ∈ A₂ ∪ ℝ` along which `f` eventually stays in the `A₁`-free components of
`(ℍ ∖ A₂) ∩ B(p, r)` (some `r > 0`), `v ∘ f − v₂ ∘ f → 0` at `q`. -/
theorem ae_tendsto_comp_sub_of_union_comp (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₂ : IsLocalSetMean A₂ h P g₂) :
    ∀ᵐ ω ∂P, ∀ v v₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd v₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ x, v₂ x * φ x) →
      ∀ (f : ℂ → ℂ) (q p : ℂ), Tendsto f (𝓝[ball 0 1] q) (𝓝 p) → p ∈ A₂ ω ∪ {z : ℂ | z.im = 0} →
        (∃ r > 0, ∀ᶠ ζ in 𝓝[ball 0 1] q, f ζ ∈ freeNear (A₁ ω) (A₂ ω) p r) →
        Tendsto (fun ζ => v (f ζ) - v₂ (f ζ)) (𝓝[ball 0 1] q) (𝓝 0) := by
  filter_upwards [ae_tendsto_sub_of_union_comp hh hA₁ hA₂ hci h₁ h₂ hunb hg hg₂,
    h₁.2.1, h₂.2.1] with ω ⟨u, hu, hrep, hlim⟩ ⟨_, ho₁⟩ ⟨_, ho₂⟩ v v₂ hv hvrep hv₂ hv₂rep f q p hfq hp hr
  have hUeq : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
    ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]; tauto
  have hoU : IsOpen (H \ (A₁ ω ∪ A₂ ω)) := hUeq ▸ ho₁.inter ho₂
  have hUA₂ : H \ (A₁ ω ∪ A₂ ω) ⊆ H \ A₂ ω := sdiff_subset_sdiff_right subset_union_right
  have hcont : ∀ {U : Set ℂ} {w : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd w U →
      ContinuousOn w U := fun hw z hz => (hw z hz).1.continuousAt.continuousWithinAt
  have huv : EqOn u (fun z => v z - v₂ z) (H \ (A₁ ω ∪ A₂ ω)) := by
    refine Sec6.eqOn_of_integral_mul_eq hoU sdiff_subset hu
      (hv.sub fun z hz => hv₂ z (hUA₂ hz)) fun φ hφ => ?_
    rw [← hrep φ hφ, hvrep φ hφ, hv₂rep φ (hφ.trans hUA₂),
      ← integral_sub (integrable_mul_test hoU (hcont hv) φ hφ)
        (integrable_mul_test hoU ((hcont hv₂).mono hUA₂) φ hφ)]
    congr 1; funext z; ring
  obtain ⟨r, hr0, hev⟩ := hr
  have hT : Tendsto f (𝓝[ball 0 1] q) (𝓝[freeNear (A₁ ω) (A₂ ω) p r] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hfq, hev⟩
  refine ((hlim p hp r hr0).comp hT).congr' ?_
  filter_upwards [hev] with ζ hζ
  exact huv (freeNear_subset hζ)

/-- The same with the roles of `A₁` and `A₂` exchanged: `𝒞_{A₁ ∪ A₂}` against `𝒞_{A₁}` along the `A₂`-free
components of `(ℍ ∖ A₁) ∩ B(p, r)`, `p ∈ A₁ ∪ ℝ`. -/
theorem ae_tendsto_comp_sub_of_union_comp_symm (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    {g g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₁ : IsLocalSetMean A₁ h P g₁) :
    ∀ᵐ ω ∂P, ∀ v v₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd v₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ x, v₁ x * φ x) →
      ∀ (f : ℂ → ℂ) (q p : ℂ), Tendsto f (𝓝[ball 0 1] q) (𝓝 p) → p ∈ A₁ ω ∪ {z : ℂ | z.im = 0} →
        (∃ r > 0, ∀ᶠ ζ in 𝓝[ball 0 1] q, f ζ ∈ freeNear (A₂ ω) (A₁ ω) p r) →
        Tendsto (fun ζ => v (f ζ) - v₁ (f ζ)) (𝓝[ball 0 1] q) (𝓝 0) := by
  have hcomm : (fun ω => A₂ ω ∪ A₁ ω) = fun ω => A₁ ω ∪ A₂ ω := funext fun ω => union_comm _ _
  have hg' : IsLocalSetMean (fun ω => A₂ ω ∪ A₁ ω) h P g := hcomm ▸ hg
  filter_upwards [ae_tendsto_comp_sub_of_union_comp hh hA₂ hA₁ hci.symm h₂ h₁ hunb hg' hg₁] with ω hω
    v v₁ hv hvrep hv₁ hv₁rep f q p hfq hp hr
  rw [union_comm (A₁ ω)] at hv hvrep
  exact hω v v₁ hv hvrep hv₁ hv₁rep f q p hfq hp hr

end Main

end InteractingSLE.Theorem14.SB.FinRel
