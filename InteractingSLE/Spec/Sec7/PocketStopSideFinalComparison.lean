/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideFinalKernel
import InteractingSLE.Spec.Sec7.SideHeightBoxProb

/-!
# Boundary comparison from a history-marked union

PROVE-STRIPSYS38. Aux. 35's retained-germ comparison (spec pp. 193–194).
The existing Proposition 3.8 moment bound and random-layer Borel–Cantelli theorem
apply to the two conditional Gaussian laws. The kernel is supplied by marked
avoidance of the union with both sets recorded, using `FinalKernel`. Neither
field determination nor conditional independence given the field is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open QuantumZipper LQGMetric LocalSets
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)
open GFF (layerSet bumpMass bumpMass_pos)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A₁ A₂ : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The boundary-decay part of Proposition 3.8 with the retained marked-union
kernel in place of its conditional-independence construction. -/
theorem ae_tendsto_sub_union_of_marked (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hmarked : WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma)
      (fun ω => A₁ ω ∪ A₂ ω) h P)
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
  obtain ⟨g₀, hg₀m, hg₀h, hg₀c⟩ := exists_condLaw_marked_union_germs hh hA₁ hA₂ h₁.2.1 h₂.2.1 hmarked
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

/-- Two local means have the same boundary values where their sets agree,
provided their union has the history-marked law retaining both sets. This is
Aux. 35's two-step route and contains no determination hypotheses. -/
theorem ae_tendsto_sub_of_marked_union (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A B : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    (hBm : Measurable[mΩ, hittingSigma] B) (hAloc : IsLocalSet A h P) (hBloc : IsLocalSet B h P)
    (hmarked : WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap A hittingSigma ⊔ MeasurableSpace.comap B hittingSigma)
      (fun ω => A ω ∪ B ω) h P)
    (hAunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hBunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (B ω)) z))
    {gA gB : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean A h P gA) (hgB : IsLocalSetMean B h P gB) :
    ∀ᵐ ω ∂P, ∀ vA vB : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd vA (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → gA ω φ = ∫ z, vA z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ B ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → gB ω φ = ∫ z, vB z * φ z) →
      ∀ p : ℂ, p ∈ A ω ∪ {z : ℂ | z.im = 0} → p ∈ B ω ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, B ω ∩ ball p r ⊆ A ω) → (∃ r > 0, A ω ∩ ball p r ⊆ B ω) →
      Tendsto (fun z => vA z - vB z) (𝓝[H \ (A ω ∪ B ω)] p) (𝓝 0) := by
  have hUm := measurable_union_hitting hAm hBm
  have hUreg := IsLocalSet.ae_relClosed_union hAloc hBloc
  have hUloc : IsLocalSet (fun ω => A ω ∪ B ω) h P :=
    ((isLocalSet_tfae hh hUm hUreg).out 1 4).1 hmarked.isAvoidanceLocal
  obtain ⟨gU, hgU⟩ := IsLocalSet.exists_isLocalSetMean hh hUm hUloc
  have hmarked' : WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap B hittingSigma ⊔ MeasurableSpace.comap A hittingSigma)
      (fun ω => B ω ∪ A ω) h P := by
    rw [sup_comm, show (fun ω => B ω ∪ A ω) = (fun ω => A ω ∪ B ω) from
      funext fun ω => union_comm _ _]
    exact hmarked
  have hgU' : IsLocalSetMean (fun ω => B ω ∪ A ω) h P gU := by
    rw [show (fun ω => B ω ∪ A ω) = (fun ω => A ω ∪ B ω) from funext fun ω => union_comm _ _]
    exact hgU
  have h1 := ae_tendsto_sub_union_of_marked hh hBm hAm hmarked' hBloc hAloc hAunb hgU' hgA
  have h2 := ae_tendsto_sub_union_of_marked hh hAm hBm hmarked hAloc hBloc hBunb hgU hgB
  filter_upwards [h1, h2, hAloc.2.1, hBloc.2.1] with
    ω ⟨ua, hua, huar, hual⟩ ⟨ub, hub, hubr, hubl⟩ hAo hBo vA vB hvA hvAr hvB hvBr
      p hpA hpB hBA hAB
  rw [union_comm (B ω) (A ω)] at hua huar hual
  have hO : IsOpen (H \ (A ω ∪ B ω)) := by
    have e : H \ (A ω ∪ B ω) = (H \ A ω) ∩ (H \ B ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_union, mem_inter_iff]
      tauto
    rw [e]
    exact hAo.2.inter hBo.2
  exact tendsto_sub_of_union_means hO (sdiff_subset_sdiff_right subset_union_left)
    (sdiff_subset_sdiff_right subset_union_right) hvA hvAr hvB hvBr hua huar hub hubr
    (hual p hpA hBA) (hubl p hpB hAB)

end InteractingSLE.Sec7.PocketStopSide
