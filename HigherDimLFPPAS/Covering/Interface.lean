import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Covering.Lemma33

/-!
# Lemma 3.3: the interface adapter

This module applies D7's abstract good-radius covering estimate to the
`GoodAnnulus` events supplied by Lemma 3.2.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPPAS.Core
open scoped ENNReal

namespace HigherDimLFPPAS.Covering

private theorem fieldSigma0_le_recentredFieldSigmaRd
    {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {h : Ω → DistRd d}
    (U : TopologicalSpace.Opens (Rd d)) (z : Rd d) (r : ℝ) :
    HigherDimLQGMetric.fieldSigma0 h (U : Set (Rd d)) ≤
      HigherDimLQGMetric.fieldSigmaRd
        (fun ω => HigherDimLQGMetric.addConst (h ω)
          (-HigherDimLQGMetric.sphereAvg (h ω) r z)) U := by
  unfold HigherDimLQGMetric.fieldSigma0
  refine @Measurable.comap_le Ω _
    (HigherDimLQGMetric.fieldSigmaRd
      (fun ω => HigherDimLQGMetric.addConst (h ω)
        (-HigherDimLQGMetric.sphereAvg (h ω) r z)) U) _ _
    (@measurable_pi_iff Ω _ _
      (HigherDimLQGMetric.fieldSigmaRd
        (fun ω => HigherDimLQGMetric.addConst (h ω)
          (-HigherDimLQGMetric.sphereAvg (h ω) r z)) U) _ _ |>.2 fun φ => ?_)
  let ψ : HigherDimLQGMetric.TestOn U :=
    HigherDimLQGMetric.testOnOf U φ.1.1 φ.2
  have hsrc : Measurable[HigherDimLQGMetric.fieldSigmaRd
      (fun ω => HigherDimLQGMetric.addConst (h ω)
        (-HigherDimLQGMetric.sphereAvg (h ω) r z)) U]
      (fun ω => HigherDimLQGMetric.restrictTo U
        (HigherDimLQGMetric.addConst (h ω)
          (-HigherDimLQGMetric.sphereAvg (h ω) r z))) :=
    Measurable.of_comap_le le_rfl
  have hpair : Measurable[HigherDimLQGMetric.fieldSigmaRd
      (fun ω => HigherDimLQGMetric.addConst (h ω)
        (-HigherDimLQGMetric.sphereAvg (h ω) r z)) U]
      (fun ω => HigherDimLQGMetric.restrictTo U
        (HigherDimLQGMetric.addConst (h ω)
          (-HigherDimLQGMetric.sphereAvg (h ω) r z)) ψ) :=
    (HigherDimLQGMetric.measurable_distOn_apply ψ).comp hsrc
  have heq : (fun ω => h ω φ.1.1) = fun ω =>
      HigherDimLQGMetric.restrictTo U
        (HigherDimLQGMetric.addConst (h ω)
          (-HigherDimLQGMetric.sphereAvg (h ω) r z)) ψ := by
    funext ω
    rw [HigherDimLQGMetric.restrictTo_testOnOf]
    exact (HigherDimLQGMetric.addConst_apply_testRd0 (h ω)
      (-HigherDimLQGMetric.sphereAvg (h ω) r z) φ.1).symm
  rw [heq]
  exact hpair

private theorem ann_eq_shellOpen_eighth_eight {d : ℕ} (z : Rd d) (r : ℝ) :
    HigherDimLQGMetric.ann z (r / 8) (8 * r) =
      (HigherDimLQGMetric.shellOpen z ((8 : ℝ)⁻¹ * r) (8 * r) : Set (Rd d)) := by
  rw [HigherDimLQGMetric.ann_eq_ball_diff, HigherDimLQGMetric.shellOpen]
  congr 1
  congr 1
  ring

private theorem ae_all_finset {ι Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset ι) (Q : ι → Ω → Prop)
    (hQ : ∀ i ∈ s, ∀ᵐ ω ∂P, Q i ω) :
    ∀ᵐ ω ∂P, ∀ i ∈ s, Q i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards with ω
      simp
  | @insert a s has ih =>
      have hrest : ∀ i ∈ s, ∀ᵐ ω ∂P, Q i ω := by
        intro i hi
        exact hQ i (Finset.mem_insert_of_mem hi)
      filter_upwards [hQ a (Finset.mem_insert_self a s), ih hrest] with ω ha hs
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha
      · exact hs i hi

/-- Interface adapter of D7's abstract covering estimate for Lemma 3.3. -/
theorem lemma33_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h)
    (hm : Core.Lemma32Marginal κ ξ Q D P h)
    (hme : Core.Lemma32Meas κ ξ Q D P h) : Core.Lemma33Stmt κ ξ Q D P h := by
  classical
  have hd3 : 3 ≤ d := hS.dim
  have hd2 : 2 ≤ d := by omega
  obtain ⟨p, hp0, hp1, h26⟩ :=
    HigherDimLFPPAS.lemma33_good_radius_cover (d := d) hd2
  let p' : ℝ := max p (1 / 2)
  have hp'lt : p' < 1 := by
    dsimp [p']
    exact max_lt hp1 (by norm_num)
  obtain ⟨A, hA, hmarg⟩ := hm p' hp'lt
  refine ⟨A, hA, ?_⟩
  intro η u q₀ R hη hu huq hq₀ hR
  obtain ⟨εp, hεp, hmargE⟩ := hmarg η u q₀ hη hu huq hq₀
  obtain ⟨εs, hεs, hmeE⟩ := hme A η u q₀ hA hη hu huq hq₀
  let εa : ℝ := min εp εs
  let E : ℝ → Rd d → ℝ → Set Ω := fun ε z r =>
    if he : ε ∈ Ioo (0 : ℝ) εa ∧ r ∈ Core.window ε u then
      Classical.choose (hmeE ε
        ⟨he.1.1, lt_of_lt_of_le he.1.2
          (by dsimp [εa]; exact min_le_right _ _)⟩ z r he.2)
    else univ
  have hEdata (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) εa) (z : Rd d) (r : ℝ)
      (hr : r ∈ Core.window ε u) :
      MeasurableSet[HigherDimLQGMetric.fieldSigmaRd
        (fun ω => HigherDimLQGMetric.addConst (h ω)
          (-HigherDimLQGMetric.sphereAvg (h ω) r z))
        (HigherDimLQGMetric.shellOpen z ((8 : ℝ)⁻¹ * r) (8 * r))] (E ε z r) ∧
      {ω | Core.GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η
        (Core.cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r} =ᵐ[P] E ε z r := by
    have hεs' : ε ∈ Ioo (0 : ℝ) εs :=
      ⟨hε.1, lt_of_lt_of_le hε.2 (by dsimp [εa]; exact min_le_right _ _)⟩
    have hsource := hmeE ε hεs' z r hr
    have hFdata := Classical.choose_spec hsource
    have hσ : HigherDimLQGMetric.fieldSigma0 h
        (HigherDimLQGMetric.ann z (r / 8) (8 * r)) ≤
        HigherDimLQGMetric.fieldSigmaRd
          (fun ω => HigherDimLQGMetric.addConst (h ω)
            (-HigherDimLQGMetric.sphereAvg (h ω) r z))
          (HigherDimLQGMetric.shellOpen z ((8 : ℝ)⁻¹ * r) (8 * r)) := by
      rw [ann_eq_shellOpen_eighth_eight]
      exact fieldSigma0_le_recentredFieldSigmaRd
        (HigherDimLQGMetric.shellOpen z ((8 : ℝ)⁻¹ * r) (8 * r)) z r
    refine ⟨?_, ?_⟩
    · dsimp [E]
      rw [dif_pos ⟨hε, hr⟩]
      exact hσ _ hFdata.1
    · dsimp [E]
      rw [dif_pos ⟨hε, hr⟩]
      exact hFdata.2
  obtain ⟨C, hC, εd, hεd, hεdlt, hD7⟩ :=
    h26 P h hS.field u q₀ R hu huq hq₀ E
      (by
        intro ε hε z k hk
        have hr : HigherDimLFPPAS.d7ScaleRadius k ∈ Core.window ε u := by
          change (256 : ℝ) ^ (-k) ∈ Windows.winRadiusWindow ε u
          exact ⟨k, hk, rfl⟩
        by_cases hsmall : ε ∈ Ioo (0 : ℝ) εa
        · exact (hEdata ε hsmall z (HigherDimLFPPAS.d7ScaleRadius k) hr).1
        · have hrel : ¬ (ε ∈ Ioo (0 : ℝ) εa ∧
              HigherDimLFPPAS.d7ScaleRadius k ∈ Core.window ε u) := by
            rintro ⟨he, _⟩
            exact hsmall he
          have hEuniv : E ε z (HigherDimLFPPAS.d7ScaleRadius k) = univ := by
            dsimp [E]
            split
            · next he => exact False.elim (hrel he)
            · rfl
          rw [hEuniv]
          exact MeasurableSet.univ)
      (by
        intro ε hε z k hk
        have hr : HigherDimLFPPAS.d7ScaleRadius k ∈ Core.window ε u := by
          change (256 : ℝ) ^ (-k) ∈ Windows.winRadiusWindow ε u
          exact ⟨k, hk, rfl⟩
        by_cases hsmall : ε ∈ Ioo (0 : ℝ) εa
        · have hεp' : ε ∈ Ioo (0 : ℝ) εp :=
            ⟨hsmall.1, lt_of_lt_of_le hsmall.2 (by dsimp [εa]; exact min_le_left _ _)⟩
          have hdata := hEdata ε hsmall z (HigherDimLFPPAS.d7ScaleRadius k) hr
          calc
            ENNReal.ofReal p ≤ ENNReal.ofReal p' :=
              ENNReal.ofReal_le_ofReal (le_max_left p (1 / 2))
            _ ≤ P {ω | Core.GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η
                (Core.cRatio κ ξ Q ε (HigherDimLFPPAS.d7ScaleRadius k))
                (8 * ε ^ q₀) z (HigherDimLFPPAS.d7ScaleRadius k)} :=
              hmargE ε hεp' z (HigherDimLFPPAS.d7ScaleRadius k) hr
            _ = P (E ε z (HigherDimLFPPAS.d7ScaleRadius k)) :=
              measure_congr hdata.2
        · have hrel : ¬ (ε ∈ Ioo (0 : ℝ) εa ∧
              HigherDimLFPPAS.d7ScaleRadius k ∈ Core.window ε u) := by
            rintro ⟨he, _⟩
            exact hsmall he
          have hEuniv : E ε z (HigherDimLFPPAS.d7ScaleRadius k) = univ := by
            dsimp [E]
            split
            · next he => exact False.elim (hrel he)
            · rfl
          rw [hEuniv, measure_univ]
          calc
            ENNReal.ofReal p ≤ ENNReal.ofReal 1 :=
              ENNReal.ofReal_le_ofReal (le_of_lt hp1)
            _ = 1 := by simp)
  let ε₀ : ℝ := min εa εd
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    dsimp [εa]
    exact lt_min (lt_min hεp hεs) hεd
  refine ⟨C, ε₀, hε₀, ?_⟩
  intro ε hε Rε hRε hRsize
  have hεa : ε ∈ Ioo (0 : ℝ) εa := by
    refine ⟨hε.1, ?_⟩
    dsimp [ε₀] at hε
    exact lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hεp' : ε < εp := lt_of_lt_of_le hεa.2 (by dsimp [εa]; exact min_le_left _ _)
  have hεs' : ε < εs := lt_of_lt_of_le hεa.2 (by dsimp [εa]; exact min_le_right _ _)
  have hεd' : ε < εd := by
    dsimp [ε₀] at hε
    exact lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hWindowEq : Core.window ε u = Windows.winRadiusWindow ε u := rfl
  have hWindowMem (r : {r : ℝ // r ∈ Rε}) : r.1 ∈ Windows.winRadiusWindow ε u := by
    rw [← hWindowEq]
    exact hRε r.2
  let radiusIndex : {r : ℝ // r ∈ Rε} → ℤ := fun r =>
    Classical.choose ((Set.mem_image _ _ _).1 (hWindowMem r))
  have radiusIndex_spec (r : {r : ℝ // r ∈ Rε}) :
      radiusIndex r ∈ Windows.winRadiusIndices ε u ∧
        HigherDimLFPPAS.d7ScaleRadius (radiusIndex r) = r.1 := by
    dsimp [radiusIndex]
    exact Classical.choose_spec ((Set.mem_image _ _ _).1 (hWindowMem r))
  let S : Finset ℤ := Rε.attach.image radiusIndex
  have hidx_inj : ∀ a ∈ Rε.attach, ∀ b ∈ Rε.attach, radiusIndex a = radiusIndex b → a = b := by
    intro a ha b hb hab
    apply Subtype.ext
    calc
      a.1 = HigherDimLFPPAS.d7ScaleRadius (radiusIndex a) := (radiusIndex_spec a).2.symm
      _ = HigherDimLFPPAS.d7ScaleRadius (radiusIndex b) := congrArg _ hab
      _ = b.1 := (radiusIndex_spec b).2
  have hScard : S.card = Rε.card := by
    dsimp [S]
    calc
      (Rε.attach.image radiusIndex).card = Rε.attach.card :=
        Finset.card_image_of_injOn hidx_inj
      _ = Rε.card := by simp
  have hSwindow : ∀ k ∈ S, k ∈ Windows.winRadiusIndices ε u := by
    intro k hk
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
    exact (radiusIndex_spec r).1
  have hSsize : (Windows.winRadiusWindow ε u).ncard ≤ 4 * S.card := by
    calc
      (Windows.winRadiusWindow ε u).ncard ≤ 4 * Rε.card := by
        rw [← hWindowEq]
        exact hRsize
      _ = 4 * S.card := by rw [hScard]
  let B : ℝ := max (R + 1) 0
  let Z : Finset (Rd d) := HigherDimLQGMetric.shellGridBox d
    (⌈B / (ε ^ u / (100 * (d : ℝ)))⌉₊ + 1)
    (ε ^ u / (100 * (d : ℝ)))
  have hmeshEq : Core.mesh d ε u R =
      (HigherDimLQGMetric.gridPts (ε ^ u / (100 * (d : ℝ))) : Set (Rd d)) ∩
        Metric.ball (0 : Rd d) (R + 1) := rfl
  have hZbox : ∀ z ∈ Core.mesh d ε u R, z ∈ Z := by
    intro z hz
    have hB0 : 0 ≤ B := by dsimp [B]; exact le_max_right _ _
    have hBR : R + 1 ≤ B := by dsimp [B]; exact le_max_left _ _
    have hz' : z ∈ HigherDimLQGMetric.gridPts (ε ^ u / (100 * (d : ℝ))) ∩
        Metric.ball (0 : Rd d) B := by
      rw [hmeshEq] at hz
      exact ⟨hz.1, Metric.ball_subset_ball hBR hz.2⟩
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hεpos : 0 < ε := hε.1
    have hmeshpos : 0 < ε ^ u / (100 * (d : ℝ)) :=
      div_pos (Real.rpow_pos_of_pos hεpos u) (mul_pos (by norm_num) hdpos)
    exact HigherDimLQGMetric.grid_ball_subset_shellGridBox hmeshpos hB0 hz'
  have hAgree : ∀ᵐ ω ∂P, ∀ z ∈ Z, ∀ r ∈ Rε,
      (ω ∈ {ω | Core.GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η
          (Core.cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r} ↔ ω ∈ E ε z r) := by
    have hfinite := ae_all_finset (P := P) (Z.product Rε) (fun zr ω =>
        (ω ∈ {ω | Core.GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η
            (Core.cRatio κ ξ Q ε zr.2) (8 * ε ^ q₀) zr.1 zr.2} ↔
          ω ∈ E ε zr.1 zr.2)) (by
      intro zr hzr
      have hzmem : zr.1 ∈ Z := (Finset.mem_product.mp hzr).1
      have hrmem : zr.2 ∈ Rε := (Finset.mem_product.mp hzr).2
      have hεa' : ε ∈ Ioo (0 : ℝ) εa := ⟨hε.1, hεa.2⟩
      have hseteq : ∀ᵐ ω ∂P,
          ((ω ∈ ({ω | Core.GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η
            (Core.cRatio κ ξ Q ε zr.2) (8 * ε ^ q₀) zr.1 zr.2} : Set Ω)) =
          (ω ∈ E ε zr.1 zr.2)) :=
        (hEdata ε hεa' zr.1 zr.2 (hRε hrmem)).2
      have hae : ∀ᵐ ω ∂P,
          (ω ∈ {ω | Core.GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η
            (Core.cRatio κ ξ Q ε zr.2) (8 * ε ^ q₀) zr.1 zr.2} ↔
          ω ∈ E ε zr.1 zr.2) := by
        filter_upwards [hseteq] with ω hω
        exact Iff.of_eq hω
      exact hae)
    filter_upwards [hfinite] with ω hω
    intro z hz r hr
    exact hω (z, r) (Finset.mem_product.mpr ⟨hz, hr⟩)
  have hCoverRadius (ω : Ω) (z : Rd d) (hz : z ∈ Core.mesh d ε u R)
      (hω : ∀ z ∈ Z, ∀ r ∈ Rε,
        (ω ∈ {ω | Core.GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η
            (Core.cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r} ↔ ω ∈ E ε z r)) :
      (∀ r ∈ Rε, ω ∉ {ω | Core.GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η
          (Core.cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r}) ↔
      (∀ k ∈ S, ω ∉ E ε z (HigherDimLFPPAS.d7ScaleRadius k)) := by
    have hzZ : z ∈ Z := hZbox z hz
    constructor
    · intro hno k hk hgood
      obtain ⟨r, hr, hidx⟩ := Finset.mem_image.mp hk
      have hrad : HigherDimLFPPAS.d7ScaleRadius k = r.1 := by
        rw [← hidx]
        exact (radiusIndex_spec r).2
      rw [hrad] at hgood
      exact hno r.1 r.2 ((hω z hzZ r.1 r.2).mpr hgood)
    · intro hno r hr hgood
      let r' : {r : ℝ // r ∈ Rε} := ⟨r, hr⟩
      have hidx : radiusIndex r' ∈ S :=
        Finset.mem_image.mpr ⟨r', by simp, rfl⟩
      have hrad := (radiusIndex_spec r').2
      have hgood' : ω ∈ E ε z (HigherDimLFPPAS.d7ScaleRadius (radiusIndex r')) := by
        simpa only [hrad] using (hω z hzZ r hr).mp hgood
      exact hno (radiusIndex r') hidx hgood'
  let bad : Set Ω := {ω | ¬ ∀ z ∈ Core.mesh d ε u R, ∃ r ∈ Rε,
      Core.GoodAnnulus (D (h ω)) (Core.Meps κ ξ ε (h ω)) A η
        (Core.cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r}
  let badD7 : Set Ω := {ω | ∃ z ∈ HigherDimLQGMetric.gridPts
      (ε ^ u / (100 * (d : ℝ))) ∩ Metric.ball (0 : Rd d) (R + 1),
      ∀ k ∈ S, ω ∉ E ε z (HigherDimLFPPAS.d7ScaleRadius k)}
  have hbadEq : bad =ᵐ[P] badD7 := by
    filter_upwards [hAgree] with ω hω
    simp only [bad, badD7, Set.mem_setOf_eq]
    apply propext
    constructor
    · intro hbad
      push_neg at hbad
      obtain ⟨z, hz, hno⟩ := hbad
      have hz' : z ∈ HigherDimLQGMetric.gridPts
          (ε ^ u / (100 * (d : ℝ))) ∩ Metric.ball (0 : Rd d) (R + 1) := by
        rw [← hmeshEq]
        exact hz
      refine ⟨z, hz', ?_⟩
      exact (hCoverRadius ω z hz hω).mp hno
    · rintro ⟨z, hz, hno⟩
      have hz' : z ∈ Core.mesh d ε u R := by
        rw [hmeshEq]
        exact hz
      have hno' := (hCoverRadius ω z hz' hω).mpr hno
      push_neg
      exact ⟨z, hz', hno'⟩
  have hD7 := hD7 ε hε.1 hεd' S hSwindow hSsize
  have hbadBound : P badD7 ≤ ENNReal.ofReal (C * ε ^ u) := by
    simpa only [badD7] using hD7
  have htargetBound : P bad ≤ ENNReal.ofReal (C * ε ^ u) := by
    rw [measure_congr hbadEq]
    exact hbadBound
  simpa only [bad] using htargetBound

end HigherDimLFPPAS.Covering
