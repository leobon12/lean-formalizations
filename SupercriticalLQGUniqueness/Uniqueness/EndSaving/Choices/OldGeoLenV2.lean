import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.OldGeoV2




 









set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter LQGMetric.MetricGeometry
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
theorem len_add_of_le (D : LSCMetric) (P : ℝ → ℂ) {x y w : ℝ} (hxy : x ≤ y) (hyw : y ≤ w) :
    D.len P x w = D.len P x y + D.len P y w := by
  unfold LSCMetric.len
  simpa only [Set.univ_inter] using
    (eVariationOn.Icc_add_Icc (D.pt ∘ P) hxy hyw (mem_univ y)).symm

theorem old_geo_length_field {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z₀ : Finset (ℤ × ℤ)) (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z₀)
    (g₀ : DistC) (hreg₀ : RegularAt D (ξ : ℝ) g₀)
    (hE : ∀ i ∈ Z₀, LQGMetric.addFun g₀
      (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z₀)) ∈ (obj i).E)
    (c : ℤ × ℤ → ℝ)
    (hc : ∀ i ∈ Z₀, IsCircleAverage (LQGMetric.addFun g₀
      (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z₀))) r
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (c i))
    (B : ℝ) (hNB : ∀ i ∈ Z₀, scaleN ξ Q r (c i) ≤ 2 * B)
    (P : ℝ → ℂ) (T : ℝ) (hgeod : EndSaving.FiniteEvents.SetGeodesic (D g₀) K₁ K₂ P T) :
    (D (LQGMetric.addFun g₀
        (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z₀)))).len P 0 T ≤
      ENNReal.ofReal T + ENNReal.ofReal (cSpent ξ par * B * Z₀.card) := by
  set f := LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z₀) with hf
  set g := LQGMetric.addFun g₀ f with hg
  set d₀ := D g₀ with hd₀
  set Df := D g with hDf
  set z : ℤ × ℤ → ℂ := fun i => LQGMetric.GM.gridPt ((r : ℝ) / 100) i with hz
  have hr0 : (0 : ℝ) < r := r.property
  have hWeyl : ∀ p : ℂ × ℂ, Df p = weylScale ξ f d₀ p := by
    intro p; rw [hreg₀.weyl f]
  have hG : IsGeodesicCurve (d₀.pt ∘ P) 0 T := EndSaving.FiniteEvents.SetGeodesic.isGeodesic d₀ K₁ K₂ P T hgeod
  have hu : HasUnitSpeedOn (d₀.pt ∘ P) (Icc 0 T) := hgeod.1.2.1
  have hP : ContinuousOn P (Icc 0 T) := hreg₀.continuousOn ⟨hG.1, hG.2.1⟩
  have hT : 0 ≤ T := hG.1
  have hfn : ∀ x, 0 ≤ f x := fun x => bumpSum_nonneg μ h D D' ξ Q cMid par pbar r obj Z₀ x
  have hfC : ∀ x, f x ≤ par.Cmax := fun x =>
    bumpSum_le_Cmax μ h D D' ξ Q cMid par pbar r obj b K₁ K₂ Z₀ Z₀ hconfig le_rfl x
  have hout : ∀ i ∈ Z₀, ∀ x ∈ K₁ ∪ K₂, x ∉ ball (z i) (4 * (r : ℝ)) := by
    intro i hi x hx hball
    exact Set.disjoint_left.mp (hconfig.2 i hi) hball (Or.inl hx)
  have hP0 : ∀ i ∈ Z₀, P 0 ∉ ball (z i) (4 * (r : ℝ)) :=
    fun i hi => hout i hi (P 0) (Or.inl hgeod.2.1)
  have hPT : ∀ i ∈ Z₀, P T ∉ ball (z i) (4 * (r : ℝ)) :=
    fun i hi => hout i hi (P T) (Or.inr hgeod.2.2.1)
  have hO : ∀ i, IsOpen (ball (z i) (4 * (r : ℝ))) := fun i => isOpen_ball
  have hVO : ∀ i, closure (((obj i).V : Set ℂ)) ⊆ ball (z i) (4 * (r : ℝ)) := by
    intro i x hx
    have := ((obj i).closure_V_annulus hx).2
    rw [mem_ball]; linarith
  have hsite : ∀ i ∈ Z₀, ∃ hfin : (ovSet P T (ball (z i) (4 * (r : ℝ))) (obj i).V).Finite,
      (hfin.toFinset.card : ℝ) * par.Cacross ≤ par.Caround := fun i hi =>
    ov_finite_of_event (obj i) g (hE i hi) (c i) (hc i hi) d₀ hreg₀.barrier hreg₀.length f
      hWeyl hfn hfC (fun x hx hxV => bumpSum_zero_near_site μ h D D' ξ Q cMid par pbar r obj b
        K₁ K₂ Z₀ Z₀ hconfig le_rfl i hi x hx hxV) P hG hu (hP0 i hi) (hPT i hi)
  choose hfin _ using hsite
  set J := Z₀.attach.sigma (fun i => (hfin i.1 i.2).toFinset) with hJ
  have hmemJ : ∀ x ∈ J, x.2 ∈ ovSet P T (ball (z x.1.1) (4 * (r : ℝ))) (obj x.1.1).V := by
    intro x hx
    rw [hJ, Finset.mem_sigma] at hx
    exact (Set.Finite.mem_toFinset _).mp hx.2
  have hstJ : ∀ x ∈ J, x.2.2.1 < x.2.2.2.1 := fun x hx =>
    ov_window_lt hP (hO _) (hVO _) (hmemJ x hx)
  have hinJ : ∀ x ∈ J, 0 ≤ x.2.2.1 ∧ x.2.2.2.1 ≤ T := by
    intro x hx
    obtain ⟨he12, he34, _, _⟩ := exc_basic (hO _) (hVO _) (hmemJ x hx).1
    obtain ⟨h0, _, _, _, h4T, _⟩ := (hmemJ x hx).1
    exact ⟨h0.trans he12.le, he34.le.trans h4T⟩
  have hwin : ∀ x ∈ J, x.2.1 ≤ x.2.2.1 ∧ x.2.2.2.1 ≤ x.2.2.2.2 := by
    intro x hx
    obtain ⟨he12, he34, _, _⟩ := exc_basic (hO _) (hVO _) (hmemJ x hx).1
    exact ⟨he12.le, he34.le⟩
  have hdisjJ : ∀ x ∈ J, ∀ y ∈ J, x ≠ y → x.2.2.2.1 ≤ y.2.2.1 ∨ y.2.2.2.1 ≤ x.2.2.1 := by
    intro x hx y hy hxy
    have hord : x.2.2.2.2 ≤ y.2.1 ∨ y.2.2.2.2 ≤ x.2.1 := by
      by_cases hi : x.1 = y.1
      · have he : x.2 ≠ y.2 := by
          intro h; apply hxy; exact Sigma.ext hi (heq_of_eq h)
        have hyx : y.2 ∈ ovSet P T (ball (z x.1.1) (4 * (r : ℝ))) (obj x.1.1).V := hi ▸ hmemJ y hy
        rcases exc_eq_or_ordered (hO _) (hVO _) (hmemJ x hx).1 hyx.1 with h | h
        · exact absurd h he
        · exact h
      · have hne : x.1.1 ≠ y.1.1 := fun h => hi (Subtype.ext h)
        exact exc_ordered_of_disjoint (hO _) (hO _) (hVO _) (hVO _)
          (hconfig.1 _ x.1.2 _ y.1.2 hne) (hmemJ x hx).1 (hmemJ y hy).1
    obtain ⟨hx1, hx2⟩ := hwin x hx
    obtain ⟨hy1, hy2⟩ := hwin y hy
    rcases hord with h | h
    · left; linarith
    · right; linarith
  
  have hgap : ∀ a b' : ℝ, 0 ≤ a → a ≤ b' → b' ≤ T →
      (∀ x ∈ J, x.2.2.2.1 ≤ a ∨ b' ≤ x.2.2.1) → Df.len P a b' ≤ ENNReal.ofReal (b' - a) := by
    intro a b' ha hab hb hgapJ
    have hzero : ∀ v ∈ Icc a b', f (P v) = 0 := by
      intro v hv
      have hvI : v ∈ Icc 0 T := ⟨ha.trans hv.1, hv.2.trans hb⟩
      rw [hf, testCont_apply, bumpSum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      by_contra hne
      have hvV : P v ∈ ((obj i).V : Set ℂ) := by
        by_contra hnot; exact hne ((obj i).f_off_V _ hnot)
      obtain ⟨e, heS, hτv, hvσ⟩ := openVisit_mem_window hT hP (hO i) (hVO i) (hP0 i hi)
        (hPT i hi) hvI hvV
      have hxJ : (⟨⟨i, hi⟩, e⟩ : Σ _ : Z₀, ℝ × ℝ × ℝ × ℝ) ∈ J := by
        rw [hJ, Finset.mem_sigma]
        exact ⟨Finset.mem_attach _ _, (Set.Finite.mem_toFinset _).mpr heS⟩
      obtain ⟨hτV, hσV⟩ := exc_window_endpoints_not_open hP (hO i) (hVO i) heS.1
      rcases hgapJ _ hxJ with h | h
      · exact hσV ((le_antisymm hvσ (h.trans hv.1)) ▸ hvV)
      · exact hτV ((le_antisymm (hv.2.trans h) hτv) ▸ hvV)
    have hcurve : d₀.IsCurve P a b' := ⟨hab, hG.2.1.mono (Icc_subset_Icc ha hb)⟩
    rw [EndSaving.PathSurgery.weyl_len_eq_of_zero_trace d₀ Df ξ f hreg₀.forget hWeyl hcurve hzero]
    exact (curveLength_of_hasUnitSpeedOn hu ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩).le
  have hchain := chain_bound J (fun x => x.2.2.1) (fun x => x.2.2.2.1)
    (fun a b' => Df.len P a b') (fun a b' => ENNReal.ofReal (b' - a))
    (by intro a b' w hab hbw; exact (len_add_of_le Df P hab hbw).le)
    (by
      intro a b' w hab hbw
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hab) (sub_nonneg.mpr hbw)]
      congr 1; ring)
    0 T hT hstJ hinJ hdisjJ hgap
  simp only [sub_zero] at hchain
  
  have hsiteSum : ∀ i (hi : i ∈ Z₀), ∑ e ∈ (hfin i hi).toFinset, Df.len P e.2.1 e.2.2.1 ≤
      ENNReal.ofReal (cSpent ξ par * B) := by
    intro i hi
    rcases ((hfin i hi).toFinset).eq_empty_or_nonempty with hFe | ⟨e₀, he₀⟩
    · rw [hFe, Finset.sum_empty]; exact bot_le
    have he₀S := (Set.Finite.mem_toFinset _).mp he₀
    have hcontact : ∀ e ∈ ovSet P T (ball (z i) (4 * (r : ℝ))) (obj i).V,
        e.2.1 ∈ EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T ∧
        e.2.2.1 ∈ EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T := by
      intro e he
      obtain ⟨he12, he34, _, _⟩ := exc_basic (hO i) (hVO i) he.1
      obtain ⟨h0, _, h23, _, h4T, _, _, _, hτ, hσ, _, _⟩ := he.1
      exact ⟨⟨⟨h0.trans he12.le, h23.trans (he34.le.trans h4T)⟩, hτ⟩,
        ⟨⟨(h0.trans he12.le).trans h23, he34.le.trans h4T⟩, hσ⟩⟩
    have hne : (EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T).Nonempty :=
      ⟨_, (hcontact e₀ he₀S).1⟩
    obtain ⟨_, _, horder⟩ := EndSaving.Spent.closed_contact_extrema P ((obj i).V : Set ℂ) hP hne
    set S₀ := EndSaving.Spent.firstClosedContact P ((obj i).V : Set ℂ) T
    set T₀ := EndSaving.Spent.lastClosedContact P ((obj i).V : Set ℂ) T
    have hS₀T₀ : S₀ ≤ T₀ :=
      ((horder _ (hcontact e₀ he₀S).1).1).trans ((horder _ (hcontact e₀ he₀S).1).2)
    have hch := chain_bound (hfin i hi).toFinset (fun e => e.2.1) (fun e => e.2.2.1)
      (fun _ _ => (0 : ℝ≥0∞)) (fun a b' => Df.len P a b')
      (by intro _ _ _ _ _; simp)
      (by intro a b' w hab hbw; exact len_add_of_le Df P hab hbw)
      S₀ T₀ hS₀T₀
      (fun e he => ov_window_lt hP (hO i) (hVO i) ((Set.Finite.mem_toFinset _).mp he))
      (fun e he => ⟨(horder _ (hcontact e ((Set.Finite.mem_toFinset _).mp he)).1).1,
        (horder _ (hcontact e ((Set.Finite.mem_toFinset _).mp he)).2).2⟩)
      (by
        intro e he e' he' hee
        have hS := (Set.Finite.mem_toFinset _).mp he
        have hS' := (Set.Finite.mem_toFinset _).mp he'
        obtain ⟨hw1, hw2⟩ := (exc_basic (hO i) (hVO i) hS.1)
        obtain ⟨hw1', hw2'⟩ := (exc_basic (hO i) (hVO i) hS'.1)
        rcases exc_eq_or_ordered (hO i) (hVO i) hS.1 hS'.1 with h | h | h
        · exact absurd h hee
        · left; linarith [hS.1.2.2.1, hS'.1.2.1]
        · right; linarith [hS.1.2.1, hS'.1.2.2.1])
      (by intro _ _ _ _ _ _; exact bot_le)
    simp only [zero_add, Finset.sum_const_zero, add_zero] at hch
    exact hch.trans (spent_window_field (obj i) g (hE i hi) (c i) (hc i hi) d₀ hreg₀.barrier
      hreg₀.length f hWeyl hfn hfC P hG hu (hP0 i hi) (hPT i hi) hne B (hNB i hi))
  calc Df.len P 0 T ≤ Df.len P 0 T + ∑ x ∈ J, ENNReal.ofReal (x.2.2.2.1 - x.2.2.1) := le_self_add
    _ ≤ ENNReal.ofReal T + ∑ x ∈ J, Df.len P x.2.2.1 x.2.2.2.1 := hchain
    _ = ENNReal.ofReal T + ∑ i ∈ Z₀.attach,
          ∑ e ∈ (hfin i.1 i.2).toFinset, Df.len P e.2.1 e.2.2.1 := by
        rw [hJ, Finset.sum_sigma]
    _ ≤ ENNReal.ofReal T + ∑ _i ∈ Z₀.attach, ENNReal.ofReal (cSpent ξ par * B) := by
        gcongr with i _
        exact hsiteSum i.1 i.2
    _ = ENNReal.ofReal T + ENNReal.ofReal (cSpent ξ par * B * Z₀.card) := by
        rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul, ENNReal.ofReal_mul' (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, mul_comm]


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
