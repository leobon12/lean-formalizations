import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.ChainV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.SampleV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Spent.SurgeryReinstantiation




 









set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 

theorem weyl_len_le_exp (Dbase Dw : LSCMetric) (ξ M : ℝ) (hξ : 0 ≤ ξ)
    (F : C(ℂ, ℝ)) (hforget : Continuous (BiLipschitz.Barrier.forget Dbase))
    (hWeyl : ∀ p : ℂ × ℂ, Dw p = weylScale ξ F Dbase p)
    {P : ℝ → ℂ} {a b : ℝ} (hP : Dbase.IsCurve P a b)
    (hF : ∀ u ∈ Icc a b, F (P u) ≤ M) :
    Dw.len P a b ≤ ENNReal.ofReal (Real.exp (ξ * M)) * Dbase.len P a b := by
  obtain ⟨smin, _, smax, hsmax, _, _, hup⟩ :=
    Toolkit.WeylLength.weylCurveLength_trace_extrema Dbase ξ hξ F hforget hP
  have hlen : Dw.len P a b =
      HigherDimLQGMetric.curveLengthWith (fun x y : ℂ => Dw (x, y)) P a b := by
    rw [Dw.len_eq_curveLength, ← HigherDimLQGMetric.curveLengthWith_edist]
    rfl
  rw [hlen]
  have heq : (fun x y : ℂ => Dw (x, y)) =
      (fun x y : ℂ => weylScale ξ F Dbase (x, y)) := by
    funext x y
    exact hWeyl (x, y)
  rw [heq]
  refine hup.trans ?_
  gcongr
  exact hF smax hsmax

 

theorem separator_window {P : ℝ → ℂ} {T τ r : ℝ} {z : ℂ} {K : Set ℂ}
    (hP : ContinuousOn P (Icc 0 T)) (hr : 0 < r)
    (hP0 : P 0 ∉ ball z (3 * r)) (hPT : P T ∉ ball z (3 * r))
    (hτ : τ ∈ Icc 0 T) (hPτ : P τ ∈ ball z r) (hKc : IsClosed K)
    (hKann : K ⊆ {w | r < dist w z ∧ dist w z < 3 * r})
    (hsep : LQGMetric.Disconnects K (sphere z r) (sphere z (3 * r))) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < τ ∧ τ < t ∧ t ≤ T ∧ P s ∈ K ∧ P t ∈ K ∧
      ∀ u ∈ Icc s t, P u ∈ ball z (3 * r) := by
  have hr3 : r < 3 * r := by linarith
  have hτin : P τ ∈ closedBall z r := ball_subset_closedBall hPτ
  have hP0out : P 0 ∈ (ball z (3 * r))ᶜ := hP0
  have hPTout : P T ∈ (ball z (3 * r))ᶜ := hPT
  have hKnot : P τ ∉ K := by
    intro hk
    have := (hKann hk).1
    rw [mem_ball] at hPτ
    linarith
  
  set A : Set ℝ := Icc 0 τ ∩ P ⁻¹' K with hAdef
  set B : Set ℝ := Icc τ T ∩ P ⁻¹' K with hBdef
  have hPA : ContinuousOn P (Icc 0 τ) := hP.mono (Icc_subset_Icc le_rfl hτ.2)
  have hPB : ContinuousOn P (Icc τ T) := hP.mono (Icc_subset_Icc hτ.1 le_rfl)
  have hAc : IsClosed A := hPA.preimage_isClosed_of_isClosed isClosed_Icc hKc
  have hBc : IsClosed B := hPB.preimage_isClosed_of_isClosed isClosed_Icc hKc
  obtain ⟨u₀, hu₀, hu₀K⟩ := Toolkit.PlanarSeparation.pathHit_time hτ.1 hPA
    (Toolkit.PlanarSeparation.annularPath_hit_reverse hr hr3 hsep) hP0out hτin
  obtain ⟨v₀, hv₀, hv₀K⟩ := Toolkit.PlanarSeparation.pathHit_time hτ.2 hPB
    (Toolkit.PlanarSeparation.annularPath_hit hr hr3 hsep) hτin hPTout
  have hAne : A.Nonempty := ⟨u₀, hu₀, hu₀K⟩
  have hBne : B.Nonempty := ⟨v₀, hv₀, hv₀K⟩
  have hAbdd : BddAbove A := ⟨τ, fun u hu => hu.1.2⟩
  have hBbdd : BddBelow B := ⟨τ, fun u hu => hu.1.1⟩
  set s := sSup A with hsdef
  set t := sInf B with htdef
  have hsA : s ∈ A := hAc.csSup_mem hAne hAbdd
  have htB : t ∈ B := hBc.csInf_mem hBne hBbdd
  have hsτ : s < τ := lt_of_le_of_ne hsA.1.2 (by
    intro h
    exact hKnot (h ▸ hsA.2))
  have hτt : τ < t := lt_of_le_of_ne htB.1.1 (by
    intro h
    exact hKnot (h.symm ▸ htB.2))
  refine ⟨s, t, hsA.1.1, hsτ, hτt, htB.1.2, hsA.2, htB.2, ?_⟩
  intro u hu
  by_contra hout
  rcases le_total u τ with huτ | hτu
  · 
    have hu0 : 0 ≤ u := hsA.1.1.trans hu.1
    have hPu : ContinuousOn P (Icc u τ) := hP.mono (Icc_subset_Icc hu0 hτ.2)
    obtain ⟨v, hv, hvK⟩ := Toolkit.PlanarSeparation.pathHit_time huτ hPu
      (Toolkit.PlanarSeparation.annularPath_hit_reverse hr hr3 hsep) hout hτin
    have hvA : v ∈ A := ⟨⟨hu0.trans hv.1, hv.2⟩, hvK⟩
    have hvs : v ≤ s := le_csSup hAbdd hvA
    have hsu : s < u := by
      rcases hu.1.eq_or_lt with heq | hlt
      · exact absurd (heq ▸ (hKann hsA.2).2) (by simpa [mem_ball] using hout)
      · exact hlt
    linarith [hv.1]
  · have huT : u ≤ T := hu.2.trans htB.1.2
    have hPu : ContinuousOn P (Icc τ u) := hP.mono (Icc_subset_Icc hτ.1 huT)
    obtain ⟨v, hv, hvK⟩ := Toolkit.PlanarSeparation.pathHit_time hτu hPu
      (Toolkit.PlanarSeparation.annularPath_hit hr hr3 hsep) hτin hout
    have hvB : v ∈ B := ⟨⟨hv.1, hv.2.trans huT⟩, hvK⟩
    have htv : t ≤ v := csInf_le hBbdd hvB
    have hut : u < t := by
      rcases hu.2.eq_or_lt with heq | hlt
      · exact absurd (heq.symm ▸ (hKann htB.2).2) (by simpa [mem_ball] using hout)
      · exact hlt
    linarith [hv.2]

 

theorem upper_pathwise {ι : Type*} [DecidableEq ι]
    (Dh Dm : LSCMetric) (ξ Cmax : ℝ) (hξ : 0 ≤ ξ) (F : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget Dh))
    (hcont : ∀ {Q : ℝ → ℂ} {a b : ℝ}, Dh.IsCurve Q a b → ContinuousOn Q (Icc a b))
    (hWeyl : ∀ p : ℂ × ℂ, Dm p = weylScale ξ F Dh p)
    (hFnonpos : ∀ x : ℂ, F x ≤ 0)
    (P : ℝ → ℂ) {T : ℝ}
    (hG : IsGeodesicCurve (Dh.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (Dh.pt ∘ P) (Icc 0 T))
    (S : Finset ι) (z : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (ball (z i) (4 * r)) (ball (z j) (4 * r)))
    (hP0 : ∀ i ∈ S, P 0 ∉ ball (z i) (4 * r))
    (hPT : ∀ i ∈ S, P T ∉ ball (z i) (4 * r))
    (hhit : ∀ i ∈ S, ∃ τ ∈ Icc 0 T, P τ ∈ ball (z i) r)
    (V : ι → Set ℂ) (π : ι → ℝ → ℂ) (α β : ι → ℝ)
    (hπ : ∀ i ∈ S, Dh.IsCurve (π i) (α i) (β i))
    (hπV : ∀ i ∈ S, π i '' Icc (α i) (β i) ⊆ V i)
    (hπann : ∀ i ∈ S, π i '' Icc (α i) (β i) ⊆
      {w | r < dist w (z i) ∧ dist w (z i) < 3 * r})
    (hπsep : ∀ i ∈ S, LQGMetric.Disconnects (π i '' Icc (α i) (β i))
      (sphere (z i) r) (sphere (z i) (3 * r)))
    (hπF : ∀ i ∈ S, ∀ u ∈ Icc (α i) (β i), F (π i u) ≤ -Cmax)
    (L A : ι → ℝ≥0∞)
    (hπlen : ∀ i ∈ S, Dh.len (π i) (α i) (β i) ≤ L i)
    (hcross : ∀ i ∈ S, A i ≤
      OptimalConstants.Ratios.setDist Dh (V i) (sphere (z i) r ∪ sphere (z i) (3 * r))) :
    Dm (P 0, P T) + ∑ i ∈ S, A i ≤
      ENNReal.ofReal T + ∑ i ∈ S, ENNReal.ofReal (Real.exp (-(ξ * Cmax))) * L i := by
  have hPc : ContinuousOn P (Icc 0 T) := hcont ⟨hG.1, hG.2.1⟩
  have hT : 0 ≤ T := hG.1
  
  have hwin : ∀ i ∈ S, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ T ∧
      P s ∈ π i '' Icc (α i) (β i) ∧ P t ∈ π i '' Icc (α i) (β i) ∧
      (∀ u ∈ Icc s t, P u ∈ ball (z i) (3 * r)) ∧
      A i ≤ ENNReal.ofReal (t - s) := by
    intro i hi
    obtain ⟨τ, hτ, hPτ⟩ := hhit i hi
    have hKc : IsClosed (π i '' Icc (α i) (β i)) :=
      (isCompact_Icc.image_of_continuousOn (hcont (hπ i hi))).isClosed
    have h3 : ∀ x, x ∉ ball (z i) (4 * r) → x ∉ ball (z i) (3 * r) := by
      intro x hx hx3
      exact hx (ball_subset_ball (by linarith) hx3)
    obtain ⟨s, t, hs0, hsτ, hτt, htT, hsK, htK, hinside⟩ :=
      separator_window hPc hr (h3 _ (hP0 i hi)) (h3 _ (hPT i hi)) hτ hPτ hKc
        (hπann i hi) (hπsep i hi)
    refine ⟨s, t, hs0, hsτ.trans hτt, htT, hsK, htK, hinside, ?_⟩
    
    have hfc : ContinuousOn (fun u => dist (P u) (z i)) (Icc s τ) :=
      (continuous_dist.comp_continuousOn
        ((hPc.mono (Icc_subset_Icc hs0 hτ.2)).prodMk continuousOn_const))
    have hsfar : r ≤ dist (P s) (z i) := (hπann i hi hsK).1.le
    have hτnear : dist (P τ) (z i) ≤ r := (mem_ball.mp hPτ).le
    obtain ⟨u, huI, hur⟩ := intermediate_value_Icc' hsτ.le hfc ⟨hτnear, hsfar⟩
    have hsV : P s ∈ V i := hπV i hi hsK
    have husph : P u ∈ sphere (z i) r ∪ sphere (z i) (3 * r) :=
      Or.inl (mem_sphere.mpr hur)
    have hdist : Dh (P s, P u) = ENNReal.ofReal (u - s) :=
      hG.edist_eq_of_hasUnitSpeedOn hu ⟨hs0, hsτ.le.trans hτ.2⟩
        ⟨hs0.trans huI.1, huI.2.trans hτ.2⟩ huI.1
    calc A i ≤ OptimalConstants.Ratios.setDist Dh (V i) (sphere (z i) r ∪ sphere (z i) (3 * r)) :=
          hcross i hi
      _ ≤ Dh (P s, P u) := iInf₂_le_of_le (P s) hsV (iInf₂_le (P u) husph)
      _ = ENNReal.ofReal (u - s) := hdist
      _ ≤ ENNReal.ofReal (t - s) := by
          apply ENNReal.ofReal_le_ofReal
          linarith [huI.2]
  choose! s t hs0 hst htT hsK htK hinside hAst using hwin
  
  have hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i := by
    intro i hi j hj hij
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    set u := max (s i) (s j)
    have hui : u ∈ Icc (s i) (t i) := ⟨le_max_left _ _, max_le (hst i hi).le h1.le⟩
    have huj : u ∈ Icc (s j) (t j) := ⟨le_max_right _ _, max_le h2.le (hst j hj).le⟩
    have hbi := ball_subset_ball (by linarith : 3 * r ≤ 4 * r) (hinside i hi u hui)
    have hbj := ball_subset_ball (by linarith : 3 * r ≤ 4 * r) (hinside j hj u huj)
    exact Set.disjoint_left.mp (hball i hi j hj hij) hbi hbj
  
  have hgap : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ T →
      Dm (P x, P y) ≤ ENNReal.ofReal (y - x) := by
    intro x y hx hxy hy
    have h := EndSaving.PathSurgery.weyl_subpath_le Dh Dm ξ F hWeyl P (c := 0) hG hu hx hxy hy (by
      intro v _
      exact mul_nonpos_of_nonneg_of_nonpos hξ (hFnonpos _))
    simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using h
  have hchain := chain_bound S s t (fun x y => Dm (P x, P y))
    (fun x y => ENNReal.ofReal (y - x))
    (by intro x y w _ _; exact Dm.isExtMetric.2.2.2 _ _ _)
    (by
      intro x y w hxy hyw
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hxy) (sub_nonneg.mpr hyw)]
      congr 1
      ring)
    0 T hT hst (fun i hi => ⟨hs0 i hi, htT i hi⟩) hdisj
    (fun x y hx hxy hy _ => hgap x y hx hxy hy)
  simp only [sub_zero] at hchain
  
  have hshort : ∀ i ∈ S, Dm (P (s i), P (t i)) ≤
      ENNReal.ofReal (Real.exp (-(ξ * Cmax))) * L i := by
    intro i hi
    have htrace := Toolkit.PlanarSeparation.trace_dist_le_len Dm (π i) (hsK i hi) (htK i hi)
    have hw := weyl_len_le_exp Dh Dm ξ (-Cmax) hξ F hforget hWeyl (hπ i hi) (hπF i hi)
    calc Dm (P (s i), P (t i)) ≤ Dm.len (π i) (α i) (β i) := htrace
      _ ≤ ENNReal.ofReal (Real.exp (ξ * -Cmax)) * Dh.len (π i) (α i) (β i) := hw
      _ ≤ ENNReal.ofReal (Real.exp (-(ξ * Cmax))) * L i := by
          rw [mul_neg]
          gcongr
          exact hπlen i hi
  calc Dm (P 0, P T) + ∑ i ∈ S, A i
      ≤ Dm (P 0, P T) + ∑ i ∈ S, ENNReal.ofReal (t i - s i) := by
        gcongr with i hi
        exact hAst i hi
    _ ≤ ENNReal.ofReal T + ∑ i ∈ S, Dm (P (s i), P (t i)) := hchain
    _ ≤ ENNReal.ofReal T + ∑ i ∈ S, ENNReal.ofReal (Real.exp (-(ξ * Cmax))) * L i := by
        gcongr with i hi
        exact hshort i hi


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
