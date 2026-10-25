import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.GoodSiteV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingCore.Section4Counting




 













set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter LQGMetric.MetricGeometry
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
theorem subtractBumps_addFun_self {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (W : Finset (ℤ × ℤ)) (g : DistC) :
    EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W
      (LQGMetric.addFun g (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W)))
      = g := by
  unfold EndSaving.FiniteEvents.subtractBumpsV2
  rw [subTest_addFun, sub_self]
  have h0 : LQGMetric.testCont (0 : TestC) = 0 := by ext x; rfl
  rw [h0, addFun_zero]

 
theorem old_geo_count_pathwise {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z₀ Z₁ : Finset (ℤ × ℤ)) (hcfg : EndSaving.Interfaces.Configuration r b K₁ K₂ (Z₀ ∪ Z₁))
    (hdisj : Disjoint Z₀ Z₁) (g₀ : DistC)
    (hreg₀ : RegularAt D (ξ : ℝ) g₀) (hreg₀' : RegularAt D' (ξ : ℝ) g₀)
    (hregs : RegularAt D (ξ : ℝ)
      (LQGMetric.addFun g₀ (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z₀))))
    (cP : NNReal) (hcP : cPlus = cP) (hcmid0 : 0 ≤ cMid) (hcmid : cMid < cP)
    (hcomp₀ : ∀ x y : ℂ, D' g₀ (x, y) ≤ (cP : ℝ≥0∞) * D g₀ (x, y))
    (hF : EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z₀
      (LQGMetric.addFun g₀ (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z₀))))
    (hgood : ∀ i ∈ Z₁, EndSaving.FiniteEvents.GoodSiteV2 μ h D D' ξ Q cMid par pbar r b q K₁ K₂ obj i g₀) :
    ((cP : ℝ) - cMid) * par.Cinc * Z₁.card ≤ (1 + (cP : ℝ) * cSpent ξ par) * Z₀.card := by
  classical
  set f := LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z₀) with hf
  set g := LQGMetric.addFun g₀ f with hg
  set z : ℤ × ℤ → ℂ := fun i => LQGMetric.GM.gridPt ((r : ℝ) / 100) i with hz
  have hr0 : (0 : ℝ) < r := r.property
  have hξ : (0 : ℝ) ≤ ξ := ξ.property.le
  have hZ₀sub : Z₀ ⊆ Z₀ ∪ Z₁ := Finset.subset_union_left
  have hZ₁sub : Z₁ ⊆ Z₀ ∪ Z₁ := Finset.subset_union_right
  obtain ⟨hFbar, P, T, hUsub, _⟩ := hF
  have hU : EndSaving.FiniteEvents.UniqueSetGeodesic (D g₀) K₁ K₂ P T := by
    have := subtractBumps_addFun_self μ h D D' ξ Q cMid par pbar r obj Z₀ g₀
    rw [this] at hUsub
    exact hUsub
  obtain ⟨hZ₀ne, hconfig₀, hbr, hbrc, hnear, hlocal, _⟩ := hFbar
  have hfn : ∀ x, 0 ≤ f x := fun x => bumpSum_nonneg μ h D D' ξ Q cMid par pbar r obj Z₀ x
  have hfC : ∀ x, f x ≤ par.Cmax := fun x =>
    bumpSum_le_Cmax μ h D D' ξ Q cMid par pbar r obj b K₁ K₂ (Z₀ ∪ Z₁) Z₀ hcfg hZ₀sub x
  
  have hfzero : ∀ x, (∀ j ∈ Z₀, x ∉ ball (z j) (4 * (r : ℝ))) → f x = 0 := by
    intro x hx
    rw [hf, testCont_apply]
    apply bumpSum_zero_off_tubes
    intro j hj hxV
    apply hx j hj
    have h3 := ((obj j).V_annular).1 hxV
    rw [mem_ball]
    change (r : ℝ) < dist x (z j) ∧ dist x (z j) < 3 * (r : ℝ) at h3
    linarith [h3.2]
  have hfsph : ∀ x ∈ sphere (0 : ℂ) b, f x = 0 := by
    intro x hx
    apply hfzero
    intro j hj hxb
    exact Set.disjoint_left.mp (hcfg.2 j (hZ₀sub hj)) hxb (Or.inr hx)
  have hfW : ∀ i ∈ Z₁, ∀ x ∈ ball (z i) (4 * (r : ℝ)), f x = 0 := by
    intro i hi x hx
    apply hfzero
    intro j hj hxj
    have hji : j ≠ i := fun hji => Finset.disjoint_left.mp hdisj (hji ▸ hj) hi
    exact Set.disjoint_left.mp (hcfg.1 j (hZ₀sub hj) i (hZ₁sub hi) hji) hxj hx
  
  have hbr₀ : IsCircleAverage g₀ b 0 hbr := by
    have h1 := isCircleAverage_addFun_of_zero_sphere g (-f) b 0 hbr hbrc (by
      intro x hx
      simp only [ContinuousMap.neg_apply, hfsph x hx, neg_zero])
    rwa [hg, addFun_addFun_neg] at h1
  set B := scaleB ξ Q b q hbr with hB
  have hBpos : 0 < B := scaleB_pos ξ Q b q hbr
  
  have hGeo := EndSaving.FiniteEvents.SetGeodesic.isGeodesic (D g₀) K₁ K₂ P T hU.1
  have hu := hU.1.1.2.1
  have hT : 0 ≤ T := hGeo.1
  have hP : ContinuousOn P (Icc 0 T) := hreg₀.continuousOn ⟨hGeo.1, hGeo.2.1⟩
  have hout : ∀ i ∈ Z₀ ∪ Z₁, ∀ x ∈ K₁ ∪ K₂, x ∉ ball (z i) (4 * (r : ℝ)) := by
    intro i hi x hx hball
    exact Set.disjoint_left.mp (hcfg.2 i hi) hball (Or.inl hx)
  
  have hWg : ∀ p : ℂ × ℂ, D g p = weylScale ξ f (D g₀) p := by intro p; rw [hreg₀.weyl f]
  have hWg' : ∀ p : ℂ × ℂ, D' g p = weylScale ξ f (D' g₀) p := by intro p; rw [hreg₀'.weyl f]
  have hcompg := weyl_allPairs_transfer (D g₀) (D' g₀) (D g) (D' g) ξ hξ f hreg₀.forget
    hreg₀'.forget hWg hWg' hregs.length hfn cP hcomp₀
  have hmono : ∀ x y : ℂ, D g₀ (x, y) ≤ D g (x, y) :=
    EndSaving.Spent.metric_le_weyl (D g₀) (D g) ξ hξ f hreg₀.forget hWg hfn
  have hcomp'0 : ∀ x y : ℂ, D' g (x, y) ≤
      ((Real.toNNReal (Real.exp ((ξ : ℝ) * par.Cmax)) : NNReal) : ℝ≥0∞) * D' g₀ (x, y) :=
    fun x y => weyl_metric_le_exp (D' g₀) (D' g) ξ par.Cmax hξ f hreg₀'.forget hreg₀'.length
      hWg' hfC x y
  
  have hloc : ∀ i ∈ Z₀, ∃ c : ℝ, IsCircleAverage g r (z i) c ∧ EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q c hbr := by
    intro i hi
    obtain ⟨_, c, hc, hbin⟩ := hlocal i hi
    exact ⟨c, hc, hbin⟩
  choose! c hc hbin using hloc
  have hlen := old_geo_length_field μ h D D' ξ Q cMid par pbar r b K₁ K₂ obj Z₀ hconfig₀ g₀ hreg₀
    (fun i hi => (hlocal i hi).1) c hc B
    (fun i hi => by have := (hbin i hi).2; simp only [scaleN, hB, scaleB]; linarith) P T hU.1
  
  have hsc : ∀ i ∈ Z₁, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ T ∧
      (∀ u ∈ Icc s t, P u ∈ ball (z i) (4 * (r : ℝ))) ∧
      par.Cinc * B ≤ t - s ∧ D' g (P s, P t) ≤ ENNReal.ofReal (cMid * (t - s)) := by
    intro i hi
    obtain ⟨hbr', hrz, s, t, hbrc', _, hbin', hs0, hst, htT, hinside, hCinc, hs, ht, hshort⟩ :=
      goodSite_shortcut μ h D D' ξ Q cMid par pbar r b q K₁ K₂ obj i g₀ (hgood i hi) P T hU
        (hout i (hZ₁sub hi) _ (Or.inl hU.1.2.1)) (hout i (hZ₁sub hi) _ (Or.inr hU.1.2.2.1))
    have hbreq : hbr' = hbr := isCircleAverage_unique hbrc' hbr₀
    subst hbreq
    refine ⟨s, t, hs0, hst, htT, hinside, ?_, ?_⟩
    · have := hbin'.1
      have hN : B ≤ scaleN ξ Q r hrz := by simp only [hB, scaleB, scaleN]; linarith
      nlinarith [par.inc_pos]
    · calc D' g (P s, P t)
          ≤ (D' g).internal (ball (z i) (4 * (r : ℝ))) (⟨P s, hs⟩, ⟨P t, ht⟩) :=
            BiLipschitz.Barrier.edist_le_internal' (D' g) _ (⟨P s, hs⟩, ⟨P t, ht⟩)
        _ ≤ (D' g₀).internal (ball (z i) (4 * (r : ℝ))) (⟨P s, hs⟩, ⟨P t, ht⟩) :=
            weyl_internal_le_of_zero (D' g₀) (D' g) ξ f hreg₀'.forget hWg' _ hcomp'0 _
              (hfW i hi) _
        _ ≤ ENNReal.ofReal (cMid * (t - s)) := hshort
  choose! s t hs0 hst htT hinside hCinc hshort using hsc
  
  have hdisjI : ∀ i ∈ Z₁, ∀ j ∈ Z₁, i ≠ j → t i ≤ s j ∨ t j ≤ s i := by
    intro i hi j hj hij
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    set u := max (s i) (s j)
    have hui : u ∈ Icc (s i) (t i) := ⟨le_max_left _ _, max_le (hst i hi).le h1.le⟩
    have huj : u ∈ Icc (s j) (t j) := ⟨le_max_right _ _, max_le h2.le (hst j hj).le⟩
    exact Set.disjoint_left.mp (hcfg.1 i (hZ₁sub hi) j (hZ₁sub hj) hij)
      (hinside i hi u hui) (hinside j hj u huj)
  have hseg : ∀ i ∈ Z₁, ENNReal.ofReal (t i - s i) ≤ (D g).len P (s i) (t i) := by
    intro i hi
    have h1 : (D g₀).len P (s i) (t i) = ENNReal.ofReal (t i - s i) :=
      curveLength_of_hasUnitSpeedOn hu ⟨hs0 i hi, (hst i hi).le.trans (htT i hi)⟩
        ⟨(hs0 i hi).trans (hst i hi).le, htT i hi⟩
    rw [← h1]
    have := EndSaving.PathSurgery.curve_length_le_of_metric_le (D g) (D g₀) 1
      (fun x y => by rw [ENNReal.coe_one, one_mul]; exact hmono x y) P (s i) (t i)
    rwa [ENNReal.coe_one, one_mul] at this
  have hchain := shortcut_chain (D' g) (D g) cP hcompg P T hT Z₁ s t hst
    (fun i hi => ⟨hs0 i hi, htT i hi⟩) hdisjI (fun i => ENNReal.ofReal (t i - s i)) hseg
  
  set Lp := (D g).len P 0 T with hLp
  have hLpfin : Lp ≠ ⊤ := ne_top_of_le_ne_top (by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hlen
  have hsplit : ∀ i ∈ Z₁, (cP : ℝ≥0∞) * ENNReal.ofReal (t i - s i) =
      ENNReal.ofReal (cMid * (t i - s i)) + ENNReal.ofReal (((cP : ℝ) - cMid) * (t i - s i)) := by
    intro i hi
    have hpos : 0 ≤ t i - s i := (sub_pos.mpr (hst i hi)).le
    rw [← ENNReal.ofReal_add (mul_nonneg hcmid0 hpos) (mul_nonneg (by linarith) hpos),
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul cP.coe_nonneg]
    congr 1; ring
  have hsumfin : ∑ i ∈ Z₁, ENNReal.ofReal (cMid * (t i - s i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top
  have hsurgE : D' g (P 0, P T) + ∑ i ∈ Z₁, ENNReal.ofReal (((cP : ℝ) - cMid) * (t i - s i)) ≤
      (cP : ℝ≥0∞) * Lp := by
    have h1 : D' g (P 0, P T) + ∑ i ∈ Z₁, ENNReal.ofReal (((cP : ℝ) - cMid) * (t i - s i)) +
        ∑ i ∈ Z₁, ENNReal.ofReal (cMid * (t i - s i)) ≤
        (cP : ℝ≥0∞) * Lp + ∑ i ∈ Z₁, ENNReal.ofReal (cMid * (t i - s i)) := by
      calc _ = D' g (P 0, P T) + ∑ i ∈ Z₁, (cP : ℝ≥0∞) * ENNReal.ofReal (t i - s i) := by
            rw [add_assoc, ← Finset.sum_add_distrib]
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [hsplit i hi, add_comm]
        _ ≤ (cP : ℝ≥0∞) * Lp + ∑ i ∈ Z₁, D' g (P (s i), P (t i)) := hchain
        _ ≤ _ := by gcongr with i hi; exact hshort i hi
    exact (ENNReal.add_le_add_iff_right hsumfin).mp h1
  
  have hDt_le : OptimalConstants.Ratios.setDist (D' g) K₁ K₂ ≤ D' g (P 0, P T) :=
    iInf₂_le_of_le (P 0) hU.1.2.1 (iInf₂_le (P T) hU.1.2.2.1)
  have hDb_le : OptimalConstants.Ratios.setDist (D g) K₁ K₂ ≤ Lp := by
    refine (iInf₂_le_of_le (P 0) hU.1.2.1 (iInf₂_le (P T) hU.1.2.2.1)).trans ?_
    exact eVariationOn.edist_le ((D g).pt ∘ P) (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT)
  have hcPLfin : (cP : ℝ≥0∞) * Lp ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hLpfin
  have hDtfin : OptimalConstants.Ratios.setDist (D' g) K₁ K₂ ≠ ⊤ :=
    ne_top_of_le_ne_top hcPLfin (hDt_le.trans (le_self_add.trans hsurgE))
  have hDbfin : OptimalConstants.Ratios.setDist (D g) K₁ K₂ ≠ ⊤ := ne_top_of_le_ne_top hLpfin hDb_le
  set Dtilde := (OptimalConstants.Ratios.setDist (D' g) K₁ K₂).toReal
  set Dbump := (OptimalConstants.Ratios.setDist (D g) K₁ K₂).toReal
  set d := ((cP : ℝ) - cMid) * par.Cinc with hd
  have hd0 : 0 < d := mul_pos (by linarith) par.inc_pos
  have hnearR : (cP : ℝ) * Dbump - B ≤ Dtilde := by
    have h1 : (cP : ℝ≥0∞) * OptimalConstants.Ratios.setDist (D g) K₁ K₂ ≤
        OptimalConstants.Ratios.setDist (D' g) K₁ K₂ + ENNReal.ofReal B := by
      rw [← hcP]; exact tsub_le_iff_right.mp hnear
    have h2 := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hDbfin)
      (ENNReal.add_ne_top.mpr ⟨hDtfin, ENNReal.ofReal_ne_top⟩)).mpr h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hDtfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hBpos.le, ENNReal.coe_toReal] at h2
    linarith
  have hsumge : d * B * Z₁.card ≤ ∑ i ∈ Z₁, ((cP : ℝ) - cMid) * (t i - s i) := by
    rw [show d * B * Z₁.card = ∑ _i ∈ Z₁, d * B by rw [Finset.sum_const, nsmul_eq_mul]; ring]
    refine Finset.sum_le_sum fun i hi => ?_
    have := hCinc i hi
    rw [hd]
    nlinarith
  have hsurgR : Dtilde ≤ (cP : ℝ) * Lp.toReal - d * B * Z₁.card := by
    have h1 : OptimalConstants.Ratios.setDist (D' g) K₁ K₂ +
        ENNReal.ofReal (∑ i ∈ Z₁, ((cP : ℝ) - cMid) * (t i - s i)) ≤ (cP : ℝ≥0∞) * Lp := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i hi =>
        mul_nonneg (by linarith) (sub_pos.mpr (hst i hi)).le)]
      exact (add_le_add hDt_le le_rfl).trans hsurgE
    have h2 := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hDtfin, ENNReal.ofReal_ne_top⟩)
      hcPLfin).mpr h1
    rw [ENNReal.toReal_add hDtfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal
      (Finset.sum_nonneg fun i hi => mul_nonneg (by linarith) (sub_pos.mpr (hst i hi)).le),
      ENNReal.toReal_mul, ENNReal.coe_toReal] at h2
    linarith
  have hspentR : Lp.toReal ≤ T + cSpent ξ par * B * Z₀.card := by
    have h2 := (ENNReal.toReal_le_toReal hLpfin
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)).mpr hlen
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hT, ENNReal.toReal_ofReal (by
        have := cSpent_pos ξ par; positivity)] at h2
    exact h2
  have hmonoR : T ≤ Dbump := by
    have h1 : ENNReal.ofReal T ≤ OptimalConstants.Ratios.setDist (D g) K₁ K₂ := by
      rw [hU.1.2.2.2]
      exact iInf_mono fun x => iInf_mono fun _ => iInf_mono fun y => iInf_mono fun _ =>
        hmono x y
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hDbfin).mpr h1
    rwa [ENNReal.toReal_ofReal hT] at this
  have := EndSaving.CountingCore.finiteFamily_card_algebra Z₀ Z₁ B (cP : ℝ) (cSpent ξ par) d T Dbump Dtilde
    Lp.toReal hZ₀ne hBpos hd0 cP.coe_nonneg (cSpent_pos ξ par).le hnearR hsurgR hspentR hmonoR
  simpa only [hd] using this


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
