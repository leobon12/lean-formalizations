/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinCompP38

/-! # Marked Proposition 3.8 along free components

Packet PROVE-AUX61-GLUEINST. The component moment estimate already holds
for a supplied marked conditional decomposition. Its Borel–Cantelli argument
therefore gives the relative mean limit on each free access, without assuming
conditional independence of the sets or separation throughout a physical ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE.Sec5.Aux61GPrime

open QuantumZipper LQGMetric
open LocalSets
open InteractingSLE.Theorem14.SB.FinRel
open GFF (layerSet bumpMass bumpMass_pos)

variable {Ω : Type u} {𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A₁ A₂ : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The marked conditional relative mean tends to zero through each component
near the smaller set that is disjoint from the additional set. -/
theorem ae_tendsto_sub_of_condLaw_comp (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hA₁c : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) (hA₂c : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    (h𝒥 : 𝒥 ≤ mΩ) (h₂𝒥 : germSigma A₂ h ≤ 𝒥)
    (h₁₂𝒥 : MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma ≤ 𝒥)
    {g₀ g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₀m : Measurable[𝒥] g₀)
    (hg₀h : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ (A₁ ω ∪ A₂ ω)))
    (hg₀c : IsCondZeroBoundaryGFF P 𝒥 (fun ω => H \ (A₁ ω ∪ A₂ ω)) fun ω => h ω - g₀ ω)
    (hg₂ : IsLocalSetMean A₂ h P g₂) :
    ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ (A₁ ω ∪ A₂ ω)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g₀ ω φ - g₂ ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ A₂ ω ∪ {z : ℂ | z.im = 0}, ∀ r > 0,
        Tendsto u (𝓝[freeNear (A₁ ω) (A₂ ω) z₀ r] z₀) (𝓝 0) := by
  classical
  have hhm := hh.measurable
  set A : Ω → Set ℂ := fun ω => A₁ ω ∪ A₂ ω with hAdef
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hA₁c, hA₂c] with ω ⟨hs₁, ho₁⟩ ⟨hs₂, ho₂⟩
    refine ⟨union_subset hs₁ hs₂, ?_⟩
    have e : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
      ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
    simp only [hAdef]
    rw [e]; exact ho₁.inter ho₂
  -- the difference `D = g₀ − g₂` and its harmonic representative `u`
  set D : Ω → DistOn upperHalfPlaneOpens := fun ω => g₀ ω - g₂ ω with hDdef
  have hDm : Measurable D := LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp (hg₀m.mono h𝒥 le_rfl)).sub
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
        hA₁c hA₂c hunb h𝒥 h₂𝒥 h₁₂𝒥 hg₀m hg₀c hg₂ hR hn1.2.1 y l hl)
      by_cases hω : y ∈ layerSet (O p ω) (cen p.1) (rad p.2) n
      · rw [indicator_of_mem (show ω ∈ univ ∩ {ω | y ∈ layerSet (O p ω) (cen p.1) (rad p.2) n} from
          ⟨mem_univ _, hω⟩), indicator_of_mem (hlay ω hω)]
      · rw [indicator_of_notMem (fun h => hω h.2)]
        exact zero_le
  -- assembly
  have hBC' := ae_all_iff.2 fun p => ae_all_iff.2 (hBC p)
  filter_upwards [hBC', hA₁c, hA₂c, hDh] with ω hω h1 h2 hD
  obtain ⟨huh, hur⟩ := hu ω hD
  refine ⟨u ω, huh, fun φ hφ => ?_, fun z₀ hz₀ r hr => ?_⟩
  · rw [← hur φ hφ]
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

end InteractingSLE.Sec5.Aux61GPrime
