/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinCompEv

/-!
# Proposition 3.8 per prime end: the geometry of the `A₁`-free layers and the moment bound

Packet PROVE-T14-SB2FIN, ruling R84. For the random domain `O' = compFree A₁ A₂ c R` (the `A₁`-free components of the
patch `U = (ℍ ∖ rc A₂) ∩ B(c, 4R)`, `SB2FinCompEv`):

* `isOpen_compFree`; the distance of a point of `O'` to the complement of `O'` is its distance to the complement of `U`
  (`infDist_compl_compFree`: a segment to another component leaves `U`), and on the small layers (`2·2^{-n} < R`)
  the layers of `O'` are the points of `O'` in the layers of `ℍ ∖ rc A₂` (`mem_layerSet_compFree`);
* joint measurability of the layers of `O'` (`measurableSet_layerSet_compFree`);
* **the moment bound** `lintegral_layer_indicator_le_comp`: the analogue of the landed
  `LocalSets.lintegral_layer_indicator_le` on the event `{y ∈ O'}` instead of `{A₁ ∩ U ⊆ A₂}` — the Green covariance of
  `ℍ ∖ (A₁ ∪ A₂)` is compared with that of the component of `y` in `U` (it misses `A₁`), which equals that of `U` for a
  test function supported in it (`zeroGFFTestCov_eq_of_isClopen`), and the landed Koebe bound does the rest.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.FinRel

open LocalSets
open QuantumZipper LQGMetric
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)
open GFF (layerSet bumpMass bumpMass_pos bumpFun)

/-! ### The geometry of `O'` -/

section Geom

variable {A₁ A₂ : Set ℂ} {c : ℂ} {R : ℝ}

/-- Points of one component of `U` share the membership in `O'`. -/
theorem mem_compFree_of_mem_component {y z : ℂ} (hy : y ∈ compFree A₁ A₂ c R)
    (hz : z ∈ connectedComponentIn (patchDom A₂ c R) y) : z ∈ compFree A₁ A₂ c R :=
  ⟨connectedComponentIn_subset _ _ hz, by rw [← connectedComponentIn_eq hz]; exact hy.2⟩

theorem isOpen_compFree : IsOpen (compFree A₁ A₂ c R) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  refine mem_of_superset (((isOpen_patchDom A₂ c R).connectedComponentIn).mem_nhds
    (mem_connectedComponentIn hy.1)) fun z hz => mem_compFree_of_mem_component hy hz

theorem nonempty_compl_patchDom : (patchDom A₂ c R)ᶜ.Nonempty := ⟨-Complex.I, fun h => by
  have : (0 : ℝ) < (-Complex.I).im := h.1.1
  rw [Complex.neg_im, Complex.I_im] at this
  linarith⟩

/-- **The distance to the complement of `O'` is the distance to the complement of `U`.** -/
theorem infDist_compl_compFree {y : ℂ} (hy : y ∈ compFree A₁ A₂ c R) :
    infDist y (compFree A₁ A₂ c R)ᶜ = infDist y (patchDom A₂ c R)ᶜ := by
  have hsub : (patchDom A₂ c R)ᶜ ⊆ (compFree A₁ A₂ c R)ᶜ := compl_subset_compl.2 (compFree_subset _ _ _ _)
  refine le_antisymm (infDist_le_infDist_of_subset hsub nonempty_compl_patchDom) ?_
  refine (le_infDist (nonempty_compl_patchDom.mono hsub)).2 fun z hz => ?_
  by_cases hzU : z ∈ patchDom A₂ c R
  · -- `z` lies in another component of `U`: the segment from `y` leaves `U`
    have hseg : ¬ segment ℝ y z ⊆ patchDom A₂ c R := by
      intro hs
      have hsub' := (convex_segment y z).isPreconnected.subset_connectedComponentIn
        (left_mem_segment ℝ y z) hs
      exact hz (mem_compFree_of_mem_component hy (hsub' (right_mem_segment ℝ y z)))
    obtain ⟨w, hw, hwU⟩ := not_subset.1 hseg
    calc infDist y (patchDom A₂ c R)ᶜ ≤ dist y w := infDist_le_dist_of_mem hwU
      _ ≤ dist y z := by
        have := mem_closedBall.1 (segment_subset_closedBall_left y z hw)
        rwa [dist_comm] at this
  · exact infDist_le_dist_of_mem hzU

theorem nonempty_compl_ball (c : ℂ) (r : ℝ) : (ball c r)ᶜ.Nonempty :=
  ⟨c + ((|r| + 1 : ℝ) : ℂ), fun h => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at h
    linarith [le_abs_self r]⟩

/-- The distance to the complement of `U` is the minimum of `compDist A₂` and the distance to the outside of the
ball. -/
theorem infDist_compl_patchDom (y : ℂ) :
    infDist y (patchDom A₂ c R)ᶜ = min (compDist A₂ y) (infDist y (ball c (4 * R))ᶜ) := by
  have e : (patchDom A₂ c R)ᶜ = (H \ relClosureH A₂)ᶜ ∪ (ball c (4 * R))ᶜ := by
    rw [patchDom, compl_inter]
  rw [e, compDist]
  have hne1 : (H \ relClosureH A₂)ᶜ.Nonempty := ⟨-Complex.I, fun h => by
    have : (0 : ℝ) < (-Complex.I).im := h.1
    rw [Complex.neg_im, Complex.I_im] at this
    linarith⟩
  simp only [Metric.infDist, infEDist_union]
  exact ENNReal.toReal_min (infEDist_ne_top hne1) (infEDist_ne_top (nonempty_compl_ball c _))

/-- A point of `B(c, 3R)` is at distance `≥ R` from the outside of `B(c, 4R)`. -/
theorem le_infDist_compl_ball {y : ℂ} (hy : dist y c < 3 * R) : R ≤ infDist y (ball c (4 * R))ᶜ := by
  refine (le_infDist (nonempty_compl_ball c _)).2 fun z hz => ?_
  rw [mem_compl_iff, mem_ball, not_lt] at hz
  have := dist_triangle z y c
  rw [dist_comm z y] at this
  linarith

/-- **On the small layers, the layers of `O'` are its points in the layers of `ℍ ∖ rc A₂`.** -/
theorem mem_layerSet_compFree {n : ℕ} (hn : 2 * (1 / 2 : ℝ) ^ n < R) {y : ℂ} :
    y ∈ layerSet (compFree A₁ A₂ c R) c R n ↔
      y ∈ compFree A₁ A₂ c R ∧ y ∈ layerSet (H \ relClosureH A₂) c R n := by
  constructor
  · rintro ⟨⟨⟨hyO, hyc⟩, h1⟩, h2⟩
    have h1' : (1 / 2 : ℝ) ^ (n + 2) ≤ infDist y (compFree A₁ A₂ c R)ᶜ := h1
    have h2'' : infDist y (compFree A₁ A₂ c R)ᶜ ≤ 2 * (1 / 2 : ℝ) ^ n := h2
    rw [infDist_compl_compFree hyO, infDist_compl_patchDom] at h1' h2''
    have hR := le_infDist_compl_ball (R := R) (mem_ball.1 hyc)
    have hmin : min (compDist A₂ y) (infDist y (ball c (4 * R))ᶜ) = compDist A₂ y := by
      refine min_eq_left (le_of_lt ?_)
      by_contra hge
      rw [min_eq_right (not_lt.1 hge)] at h2''
      linarith
    rw [hmin] at h1' h2''
    exact ⟨hyO, ⟨⟨⟨hyO.1.1, hyc⟩, h1'⟩, h2''⟩⟩
  · rintro ⟨hyO, ⟨⟨⟨-, hyc⟩, h1⟩, h2⟩⟩
    have hR := le_infDist_compl_ball (R := R) (mem_ball.1 hyc)
    have h2' : infDist y (H \ relClosureH A₂)ᶜ ≤ 2 * (1 / 2 : ℝ) ^ n := h2
    have hmin : min (compDist A₂ y) (infDist y (ball c (4 * R))ᶜ) = compDist A₂ y :=
      min_eq_left (by rw [compDist]; linarith)
    refine ⟨⟨⟨hyO, hyc⟩, ?_⟩, ?_⟩
    · show (1 / 2 : ℝ) ^ (n + 2) ≤ infDist y (compFree A₁ A₂ c R)ᶜ
      rw [infDist_compl_compFree hyO, infDist_compl_patchDom, hmin]
      exact h1
    · show infDist y (compFree A₁ A₂ c R)ᶜ ≤ 2 * (1 / 2 : ℝ) ^ n
      rw [infDist_compl_compFree hyO, infDist_compl_patchDom, hmin]
      exact h2

end Geom

/-! ### Measurability of the layers of `O'` -/

section LayerMeas

variable {Ω : Type*} [MeasurableSpace Ω] {A₁ A₂ : Ω → Set ℂ}

/-- **The layers of `O'` are jointly measurable.** -/
theorem measurableSet_layerSet_compFree (hA₁ : Measurable[_, hittingSigma] A₁)
    (hA₂ : Measurable[_, hittingSigma] A₂) (c : ℂ) (R : ℝ) (n : ℕ) :
    MeasurableSet {p : Ω × ℂ | p.2 ∈ layerSet (compFree (A₁ p.1) (A₂ p.1) c R) c R n} := by
  set m : Ω × ℂ → ℝ := fun p => min (compDist (A₂ p.1) p.2) (infDist p.2 (ball c (4 * R))ᶜ) with hm
  have hmm : Measurable m := (measurable_compDist hA₂).min
    ((continuous_infDist_pt _).measurable.comp measurable_snd)
  have e : {p : Ω × ℂ | p.2 ∈ layerSet (compFree (A₁ p.1) (A₂ p.1) c R) c R n} =
      {p : Ω × ℂ | p.2 ∈ compFree (A₁ p.1) (A₂ p.1) c R} ∩ {p | dist p.2 c < 3 * R} ∩
        {p | (1 / 2 : ℝ) ^ (n + 2) ≤ m p} ∩ {p | m p ≤ 2 * (1 / 2 : ℝ) ^ n} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, layerSet, mem_ball]
    constructor
    · rintro ⟨⟨⟨hO, hc⟩, h1⟩, h2⟩
      have h1' : (1 / 2 : ℝ) ^ (n + 2) ≤ infDist p.2 (compFree (A₁ p.1) (A₂ p.1) c R)ᶜ := h1
      have h2' : infDist p.2 (compFree (A₁ p.1) (A₂ p.1) c R)ᶜ ≤ 2 * (1 / 2 : ℝ) ^ n := h2
      rw [infDist_compl_compFree hO, infDist_compl_patchDom] at h1' h2'
      exact ⟨⟨⟨hO, hc⟩, h1'⟩, h2'⟩
    · rintro ⟨⟨⟨hO, hc⟩, h1⟩, h2⟩
      refine ⟨⟨⟨hO, hc⟩, ?_⟩, ?_⟩
      · show (1 / 2 : ℝ) ^ (n + 2) ≤ infDist p.2 (compFree (A₁ p.1) (A₂ p.1) c R)ᶜ
        rw [infDist_compl_compFree hO, infDist_compl_patchDom]
        exact h1
      · show infDist p.2 (compFree (A₁ p.1) (A₂ p.1) c R)ᶜ ≤ 2 * (1 / 2 : ℝ) ^ n
        rw [infDist_compl_compFree hO, infDist_compl_patchDom]
        exact h2
  rw [e]
  exact (((measurableSet_compFree hA₁ hA₂ c R).inter
    (measurableSet_lt (measurable_snd.dist measurable_const) measurable_const)).inter
    (measurableSet_le measurable_const hmm)).inter (measurableSet_le hmm measurable_const)

end LayerMeas

/-! ### The moment bound -/

section Moment

variable {Ω : Type*} {𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- A layer point has its bump ball inside the domain. -/
theorem closedBall_bumpRad_subset_of_layer {D : Set ℂ} {c y : ℂ} {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hn : tauHi R n ≤ 1 / 4) (hy : y ∈ layerSet D c R n) : closedBall y (bumpRad R n) ⊆ D :=
  (closedBall_subset_ball ((bumpRad_lt hR hn).trans_le hy.1.2)).trans ball_infDist_compl_subset

/-- **The pointwise exponential moment on the `A₁`-free part of a patch** (the component form of
`LocalSets.lintegral_layer_indicator_le`: the event `{y ∈ O'}` replaces `{A₁ ∩ U ⊆ A₂}`). -/
theorem lintegral_layer_indicator_le_comp {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A₁ A₂ : Ω → Set ℂ}
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hA₁c : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω))
    (hA₂c : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    (h𝒥 : 𝒥 ≤ mΩ) (h₂𝒥 : germSigma A₂ h ≤ 𝒥)
    (h₁₂𝒥 : MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma ≤ 𝒥)
    {g₀ g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₀m : Measurable[𝒥] g₀)
    (hg₀c : IsCondZeroBoundaryGFF P 𝒥 (fun ω => H \ (A₁ ω ∪ A₂ ω)) fun ω => h ω - g₀ ω)
    (hg₂ : IsLocalSetMean A₂ h P g₂) {c : ℂ} {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hn : tauHi R n ≤ 1 / 4) (y : ℂ) (l : ℝ) (hl : 2 * l ^ 2 * tauHi R n ≤ 1) :
    ∫⁻ ω, ({ω | y ∈ compFree (A₁ ω) (A₂ ω) c R} ∩
        {ω | y ∈ layerSet (H \ relClosureH (A₂ ω)) c R n}).indicator
      (fun ω => ENNReal.ofReal (Real.exp (l * (bumpPair (fun ω => g₀ ω - g₂ ω) (bumpRad R n)
        (bumpRad_pos hR n) (ω, y) / (bumpRad R n ^ 2 * bumpMass))))) ω ∂P ≤
      ENNReal.ofReal (Real.exp 1) := by
  set δ := bumpRad R n with hδdef
  have hδ : 0 < δ := bumpRad_pos hR n
  set m := δ ^ 2 * bumpMass with hm
  have hm0 : 0 < m := by have := bumpMass_pos; positivity
  set E := {ω | y ∈ compFree (A₁ ω) (A₂ ω) c R}
  set F := {ω | y ∈ layerSet (H \ relClosureH (A₂ ω)) c R n}
  by_cases hy : δ < y.im
  · set ψ := bumpTestH δ hδ y with hψ
    have hψc : ⇑ψ = bumpFun y δ := coe_bumpTestH_of_lt hδ hy
    have hAm : Measurable[mΩ, hittingSigma] fun ω => A₁ ω ∪ A₂ ω :=
      measurable_union_hitting hA₁ hA₂
    have hAc : ∀ᵐ ω ∂P, (A₁ ω ∪ A₂ ω) ⊆ H ∧ IsOpen (H \ (A₁ ω ∪ A₂ ω)) := by
      filter_upwards [hA₁c, hA₂c] with ω ⟨hs₁, ho₁⟩ ⟨hs₂, ho₂⟩
      refine ⟨union_subset hs₁ hs₂, ?_⟩
      have e : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
        ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
      rw [e]; exact ho₁.inter ho₂
    have hE : MeasurableSet[𝒥] E := h₁₂𝒥 _ (measurableSet_mem_compFree A₁ A₂ c R y)
    have hF : MeasurableSet[MeasurableSpace.comap A₂ hittingSigma] F :=
      measurableSet_mem_layerSet_compl A₂ c R n y
    have hκ : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ F →
        zeroGFFTestCov (H \ A₂ ω) ψ ψ - zeroGFFTestCov (H \ (A₁ ω ∪ A₂ ω)) ψ ψ ≤
          4 * tauHi R n * m ^ 2 := by
      filter_upwards [hA₁c, hA₂c, hunb] with ω h1 h2 hu hωE hωF
      have hrc := relClosureH_eq h2.1 h2.2
      have hrc1 := relClosureH_eq h1.1 h1.2
      have hωF' : y ∈ layerSet (H \ A₂ ω) c R n := by
        have := hωF; simp only [F, mem_ofPred_eq, hrc] at this; exact this
      obtain ⟨⟨⟨hyO, hyc⟩, hd1⟩, hd2⟩ := hωF'
      rw [mem_ball] at hyc
      set d := infDist y (H \ A₂ ω)ᶜ with hd
      have ht : (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ tauHi R n :=
        koebe_rpow_mono hR infDist_nonneg hd2
      have htlo : tauLo R n ≤ (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ :=
        koebe_rpow_mono hR (by positivity) hd1
      have hball : ball y R ⊆ ball c (4 * R) := fun z hz => by
        rw [mem_ball] at hz ⊢; have := dist_triangle z y c; linarith
      -- the bump support is inside a ball of radius `< d` around `y`
      have hδd : δ < (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * d := by
        have h3 : δ < tauLo R n * (1 / 2 : ℝ) ^ (n + 2) := by
          have := tauLo_pos hR n
          have : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 2) := by positivity
          rw [hδdef, bumpRad]; nlinarith
        have h4 : tauLo R n * (1 / 2 : ℝ) ^ (n + 2) ≤
            (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * d :=
          mul_le_mul htlo hd1 (by positivity) (le_trans (tauLo_pos hR n).le htlo)
        linarith
      have hψs : ∀ z, ψ z ≠ 0 → dist z y < (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * d := by
        intro z hz
        rw [hψc] at hz
        have hzy : dist z y < δ := by
          by_contra hge
          exact hz (GFF.bumpFun_eq_zero hδ (not_lt.1 hge))
        linarith
      have hG2 := zeroGFFTestCov_sub_le_of_component h2.2 isOpen_ball hu hyO hR hball
        (ht.trans hn) ψ (fun z => by rw [hψc]; exact GFF.bumpFun_nonneg y δ z) hψs
      have hint : ∫ z, ψ z = m := by rw [hψc]; exact GFF.integral_bumpFun hδ
      rw [hint] at hG2
      -- the component of `y` in the patch misses `A₁`
      have hEω : y ∈ compFree (A₁ ω) (A₂ ω) c R := hωE
      set U := patchDom (A₂ ω) c R with hUdef
      have hUe : U = (H \ A₂ ω) ∩ ball c (4 * R) := by rw [hUdef, patchDom, hrc]
      set W := connectedComponentIn U y with hWdef
      have hUo : IsOpen U := isOpen_patchDom _ _ _
      have hWo : IsOpen W := hUo.connectedComponentIn
      have hWU : W ⊆ U := connectedComponentIn_subset _ _
      have hWA : W ⊆ H \ (A₁ ω ∪ A₂ ω) := by
        intro z hz
        have hzU := hWU hz
        rw [hUe] at hzU
        refine ⟨hzU.1.1, fun h' => h'.elim (fun hz₁ => ?_) hzU.1.2⟩
        have := hEω.2
        rw [hrc1] at this
        exact Set.disjoint_left.1 this hz hz₁
      -- the bump support is inside `W`
      have hkd : (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * d < d := by
        have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd1
        have : (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 / 4 := ht.trans hn
        nlinarith
      have hdR : d < R := by
        have := GFF.infDist_lt_of_koebeScale_le (D := H \ A₂ ω) (x := y) hR (by
          unfold GFF.koebeScale; exact ht.trans hn)
        exact this
      have hcb : closedBall y ((2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * d) ⊆ U := by
        intro z hz
        have hzy : dist z y < d := lt_of_le_of_lt (mem_closedBall.1 hz) hkd
        rw [hUe]
        refine ⟨ball_infDist_compl_subset (mem_ball.2 hzy), ?_⟩
        rw [mem_ball]
        have := dist_triangle z y c
        linarith
      have hsuppW : tsupport ψ ⊆ W := by
        have hsub : tsupport ψ ⊆ closedBall y ((2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * d) :=
          closure_minimal (fun z hz => mem_closedBall.2 (hψs z hz).le) isClosed_closedBall
        exact hsub.trans (isPreconnected_closedBall.subset_connectedComponentIn
          (mem_closedBall_self (le_of_lt (hδ.trans hδd))) hcb)
      have hCc : ∀ z ∈ W, connectedComponentIn U z ⊆ W := fun z hz => by
        rw [hWdef, connectedComponentIn_eq hz]
      have hUH : U ⊆ H := fun z hz => hz.1.1
      have e1 := zeroGFFTestCov_eq_of_isClopen hUo hUH hWo hWU
        (isOpen_diff_of_forall_connectedComponentIn_subset hUo hCc) ψ hsuppW
      have hAo : IsOpen (H \ (A₁ ω ∪ A₂ ω)) := by
        have e : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
          ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
        rw [e]; exact h1.2.inter h2.2
      have hmono := zeroGFFTestCov_mono hWo hAo hWA sdiff_subset ψ
      rw [hUe] at e1
      have h5 : 4 * (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * m ^ 2 ≤
          4 * tauHi R n * m ^ 2 := by gcongr
      linarith
    have key := lintegral_indicator_exp_meanDiff_le (𝒥 := 𝒥) hh hAm hA₂ hAc hA₂c h𝒥 h₂𝒥 hg₀m hg₀c
      hg₂ ψ hE hF hκ (l / m)
    have e1 : ∀ ω, bumpPair (fun ω => g₀ ω - g₂ ω) δ (bumpRad_pos hR n) (ω, y) =
        g₀ ω ψ - g₂ ω ψ := fun ω => by
      simp only [bumpPair, hy, ↓reduceIte, sub_apply]
      rfl
    have e4 : ∀ ω, (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (l *
        (bumpPair (fun ω => g₀ ω - g₂ ω) δ (bumpRad_pos hR n) (ω, y) / m)))) ω =
        (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (l / m * (g₀ ω ψ - g₂ ω ψ)))) ω :=
      fun ω => by
        have : ∀ ω, l * (bumpPair (fun ω => g₀ ω - g₂ ω) δ (bumpRad_pos hR n) (ω, y) / m) =
            l / m * (g₀ ω ψ - g₂ ω ψ) := fun ω => by rw [e1]; ring
        simp only [this]
    rw [lintegral_congr e4]
    refine key.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have e3 : (l / m) ^ 2 * (4 * tauHi R n * m ^ 2) / 2 = 2 * l ^ 2 * tauHi R n := by
      field_simp
      ring
    rw [e3]; exact hl
  · have hF0 : ∀ ω, ω ∉ F := by
      intro ω hω
      exact hy ((closedBall_subset_H_iff hδ.le).1
        ((closedBall_bumpRad_subset hR hn hω).trans sdiff_subset))
    have h0 : ∀ ω, (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (l *
        (bumpPair (fun ω => g₀ ω - g₂ ω) δ hδ (ω, y) / m)))) ω = 0 := fun ω =>
      indicator_of_notMem (fun h => hF0 ω h.2) _
    calc _ = ∫⁻ _, (0 : ℝ≥0∞) ∂P := lintegral_congr h0
      _ = 0 := lintegral_zero
      _ ≤ _ := zero_le

end Moment

end InteractingSLE.Theorem14.SB.FinRel
