import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.Localize




 













set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

 

 

theorem path_hits_of_disconnects {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) {c : ℂ} {ρ σ : ℝ} (hρσ : ρ ≤ σ) {K : Set ℂ}
    (hK : Disconnects K (Metric.sphere c ρ) (Metric.sphere c σ))
    (hstart : dist (γ a) c ≤ ρ) (hend : σ ≤ dist (γ b) c) :
    ∃ t ∈ Icc a b, γ t ∈ K := by
  by_contra hno
  push Not at hno
  apply hK
  refine ⟨γ '' Icc a b, isPreconnected_Icc.image γ hγ, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hno t ht
  · have hf : ContinuousOn (fun t => dist (γ t) c) (Icc a b) :=
      continuous_dist.comp_continuousOn (hγ.prodMk continuousOn_const)
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hab hf ⟨hstart, hρσ.trans hend⟩
    exact ⟨γ t, ⟨t, ht, rfl⟩, Metric.mem_sphere.mpr hteq⟩
  · have hf : ContinuousOn (fun t => dist (γ t) c) (Icc a b) :=
      continuous_dist.comp_continuousOn (hγ.prodMk continuousOn_const)
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hab hf ⟨hstart.trans hρσ, hend⟩
    exact ⟨γ t, ⟨t, ht, rfl⟩, Metric.mem_sphere.mpr hteq⟩

 
theorem path_hits_of_disconnects_rev {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) {c : ℂ} {ρ σ : ℝ} (hρσ : ρ ≤ σ) {K : Set ℂ}
    (hK : Disconnects K (Metric.sphere c ρ) (Metric.sphere c σ))
    (hstart : σ ≤ dist (γ a) c) (hend : dist (γ b) c ≤ ρ) :
    ∃ t ∈ Icc a b, γ t ∈ K := by
  have h := path_hits_of_disconnects (γ := fun t => γ (a + b - t)) hab
    (hγ.comp (continuous_const.sub continuous_id).continuousOn
      (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)) hρσ hK
    (by simpa using hend) (by simpa using hstart)
  obtain ⟨t, ht, hK'⟩ := h
  exact ⟨a + b - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, hK'⟩

 

theorem eventOpen_isOpen (z : ℂ) (r : ℝ) : IsOpen (TwoScale.S36Events.eventOpen z r) :=
  Metric.isOpen_ball.sdiff Metric.isClosed_closedBall

theorem closure_eventOpen_subset (z : ℂ) (r : ℝ) :
    closure (TwoScale.S36Events.eventOpen z r) ⊆ TwoScale.S36Events.eventOpen z r ∪ TwoScale.S36Events.eventBoundary z r := by
  have hcl : IsClosed (Metric.closedBall z (2 * r) \ Metric.ball z (r / 2)) :=
    Metric.isClosed_closedBall.sdiff Metric.isOpen_ball
  refine (closure_minimal ?_ hcl).trans ?_
  · rintro y ⟨hy1, hy2⟩
    exact ⟨Metric.ball_subset_closedBall hy1, fun h => hy2 (Metric.ball_subset_closedBall h)⟩
  · rintro y ⟨hy1, hy2⟩
    rw [Metric.mem_closedBall] at hy1
    rw [Metric.mem_ball, not_lt] at hy2
    rcases eq_or_lt_of_le hy1 with h1 | h1
    · exact Or.inr (Or.inr (Metric.mem_sphere.mpr h1))
    rcases eq_or_lt_of_le hy2 with h2 | h2
    · exact Or.inr (Or.inl (Metric.mem_sphere.mpr h2.symm))
    exact Or.inl ⟨Metric.mem_ball.mpr h1, by rw [Metric.mem_closedBall, not_le]; exact h2⟩

theorem eventOpen_union_boundary (z : ℂ) {r : ℝ} (hr : 0 < r) :
    TwoScale.S36Events.eventOpen z r ∪ TwoScale.S36Events.eventBoundary z r = TwoScale.S36Events.eventCarrier z r := by
  ext y
  simp only [TwoScale.S36Events.eventOpen, TwoScale.S36Events.eventBoundary, TwoScale.S36Events.eventCarrier, mem_union, Set.mem_sdiff,
    Metric.mem_ball, Metric.mem_closedBall, Metric.mem_sphere, not_lt, not_le]
  constructor
  · rintro (⟨h1, h2⟩ | h | h)
    · exact ⟨h1.le, h2.le⟩
    · exact ⟨by rw [h]; linarith, h.ge⟩
    · exact ⟨h.le, by rw [h]; linarith⟩
  · rintro ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with h1 | h1
    · exact Or.inr (Or.inr h1)
    rcases eq_or_lt_of_le h2 with h2 | h2
    · exact Or.inr (Or.inl h2.symm)
    exact Or.inl ⟨h1, h2⟩

theorem eventMiddle_subset_open (z : ℂ) {r : ℝ} (hr : 0 < r) :
    TwoScale.S36Events.eventMiddle z r ⊆ TwoScale.S36Events.eventOpen z r := by
  rintro y ⟨h1, h2⟩
  rw [Metric.mem_ball] at h1
  rw [Metric.mem_closedBall, not_le] at h2
  exact ⟨Metric.mem_ball.mpr (by linarith), by rw [Metric.mem_closedBall, not_le]; linarith⟩

theorem middle_boundary_disjoint (z : ℂ) {r : ℝ} (hr : 0 < r) {x y : ℂ}
    (hx : x ∈ TwoScale.S36Events.eventMiddle z r) (hy : y ∈ TwoScale.S36Events.eventBoundary z r) : x ≠ y := by
  rintro rfl
  obtain ⟨h1, h2⟩ := hx
  rw [Metric.mem_ball] at h1
  rw [Metric.mem_closedBall, not_le] at h2
  rcases hy with hy | hy <;> (rw [Metric.mem_sphere] at hy; linarith)

 
theorem setDist_middle_pos (D : LSCMetric) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    0 < OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
  have hne : ({p : ℂ × ℂ | p.1 ∈ Metric.closedBall z (2 * r) ∧ p.2 ∈ Metric.closedBall z (2 * r) ∧
      r / 4 ≤ dist p.1 p.2}).Nonempty := by
    refine ⟨(z, z + r), Metric.mem_closedBall_self (by linarith), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
      linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
      linarith
  obtain ⟨c, hc, hcle⟩ := Toolkit.PathInfimum.compact_separated_pairs_pos D (isCompact_closedBall z (2 * r))
    (by linarith : (0 : ℝ) < r / 4) hne
  refine hc.trans_le (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  obtain ⟨hx1, hx2⟩ := hx
  rw [Metric.mem_ball] at hx1
  rw [Metric.mem_closedBall, not_le] at hx2
  have hyz : dist y z = r / 2 ∨ dist y z = 2 * r := by
    rcases hy with hy | hy <;> rw [Metric.mem_sphere] at hy
    · exact Or.inl hy
    · exact Or.inr hy
  refine hcle (x, y) (Metric.mem_closedBall.mpr (by linarith))
    (Metric.mem_closedBall.mpr (by rcases hyz with h | h <;> rw [h] <;> linarith)) ?_
  have htri := dist_triangle_right x y z
  have htri' := dist_triangle x y z
  have htri'' := dist_triangle y x z
  have hcomm : dist y x = dist x y := dist_comm y x
  rcases hyz with h | h
  · change r / 4 ≤ dist x y
    linarith
  · change r / 4 ≤ dist x y
    linarith

 

 

theorem curve_len_of_le_mul {d e : LSCMetric} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hle : ∀ x y, e (x, y) ≤ c * d (x, y)) {P : ℝ → ℂ} {a b : ℝ} (hP : d.IsCurve P a b) :
    e.IsCurve P a b ∧ e.len P a b ≤ c * d.len P a b := by
  refine ⟨⟨hP.1, ?_⟩, ?_⟩
  · intro t ht
    have hd := tendsto_iff_edist_tendsto_0.mp (hP.2 t ht)
    apply tendsto_iff_edist_tendsto_0.mpr
    have hmul : Tendsto (fun s => c * edist ((d.pt ∘ P) s) ((d.pt ∘ P) t))
        (𝓝[Icc a b] t) (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hd (Or.inr hc)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun s => hle _ _)
  · refine iSup_le fun p => ?_
    calc
      (∑ i ∈ Finset.range p.1, edist ((e.pt ∘ P) (p.2.1 (i + 1))) ((e.pt ∘ P) (p.2.1 i)))
          ≤ ∑ i ∈ Finset.range p.1, c * edist ((d.pt ∘ P) (p.2.1 (i + 1)))
              ((d.pt ∘ P) (p.2.1 i)) := Finset.sum_le_sum fun i _ => hle _ _
      _ = c * ∑ i ∈ Finset.range p.1, edist ((d.pt ∘ P) (p.2.1 (i + 1)))
              ((d.pt ∘ P) (p.2.1 i)) := by rw [Finset.mul_sum]
      _ ≤ c * d.len P a b := mul_le_mul' le_rfl (eVariationOn.sum_le p.2.2.1 p.2.2.2)

 

theorem intExt_le_of_separator {D : LSCMetric}
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), D.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hL : D.IsLengthSpace) {z v u : ℂ} {r ρ σ : ℝ} (hr : 0 < r) (hρσ : ρ ≤ σ)
    (hσM : Metric.closedBall v σ ⊆ TwoScale.S36Events.eventMiddle z r)
    (hFfar : ∀ y ∈ TwoScale.S36Events.eventBoundary z r, σ ≤ dist y v)
    (hu : dist u v ≤ ρ) (hρ0 : 0 ≤ ρ)
    {π : ℝ → ℂ} {α β : ℝ} (hπ : D.IsCurve π α β)
    (hπσ : ∀ τ ∈ Icc α β, π τ ∈ Metric.closedBall v σ)
    (hπsep : Disconnects (π '' Icc α β) (Metric.sphere v ρ) (Metric.sphere v σ))
    (hπlen : D.len π α β ≤ OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)) :
    intExt D (TwoScale.S36Events.eventOpen z r) u v ≤ D (u, v) := by
  set V := TwoScale.S36Events.eventOpen z r with hVdef
  set F := TwoScale.S36Events.eventBoundary z r with hFdef
  set M := TwoScale.S36Events.eventMiddle z r with hMdef
  have hVo : IsOpen V := eventOpen_isOpen z r
  have hVcl : closure V ⊆ V ∪ F := closure_eventOpen_subset z r
  have hFc : IsClosed F := isClosed_eventBoundary z r
  have hMV : M ⊆ V := eventMiddle_subset_open z hr
  have huV : u ∈ V := hMV (hσM (Metric.mem_closedBall.mpr (hu.trans hρσ)))
  have hvV : v ∈ V := hMV (hσM (Metric.mem_closedBall_self (hρ0.trans hρσ)))
  have hπV : ∀ τ ∈ Icc α β, π τ ∈ V := fun τ hτ => hMV (hσM (hπσ τ hτ))
  by_cases htop : D (u, v) = ⊤
  · rw [htop]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨γ, a, b, hγ, hγa, hγb, hlen⟩ :=
    hL u v (lt_top_iff_ne_top.mpr htop) ε (by exact_mod_cast hε)
  have hab : a ≤ b := hγ.1
  have hγc : ContinuousOn γ (Icc a b) := hcont γ a b hγ
  have hgoal : D.len γ a b ≤ D (u, v) + ε := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact hlen
  by_cases hmeet : ∃ t ∈ Icc a b, γ t ∈ F
  · 
    set T : Set ℝ := Icc a b ∩ γ ⁻¹' F with hTdef
    have hTc : IsClosed T := hγc.preimage_isClosed_of_isClosed isClosed_Icc hFc
    obtain ⟨t0, ht0, ht0F⟩ := hmeet
    have hTne : T.Nonempty := ⟨t0, ht0, ht0F⟩
    have hTbdd : BddBelow T := ⟨a, fun t ht => ht.1.1⟩
    have hTbdd' : BddAbove T := ⟨b, fun t ht => ht.1.2⟩
    set tm := sInf T with htm
    set tp := sSup T with htp
    have htmT : tm ∈ T := hTc.csInf_mem hTne hTbdd
    have htpT : tp ∈ T := hTc.csSup_mem hTne hTbdd'
    have htmtp : tm ≤ tp := csInf_le_csSup hTne hTbdd hTbdd'
    have hbefore : ∀ t ∈ Icc a b, t < tm → γ t ∉ F := fun t ht htlt hF =>
      (not_le_of_gt htlt) (csInf_le hTbdd ⟨ht, hF⟩)
    have hafter : ∀ t ∈ Icc a b, tp < t → γ t ∉ F := fun t ht htlt hF =>
      (not_le_of_gt htlt) (le_csSup hTbdd' ⟨ht, hF⟩)
    
    have hγtmfar : σ ≤ dist (γ tm) v := hFfar _ htmT.2
    have hγtpfar : σ ≤ dist (γ tp) v := hFfar _ htpT.2
    obtain ⟨s₁, hs₁, hs₁π⟩ := path_hits_of_disconnects htmT.1.1
      (hγc.mono (Icc_subset_Icc le_rfl htmT.1.2)) hρσ hπsep
      (by rw [hγa]; exact hu) hγtmfar
    obtain ⟨s₂, hs₂, hs₂π⟩ := path_hits_of_disconnects_rev htpT.1.2
      (hγc.mono (Icc_subset_Icc htpT.1.1 le_rfl)) hρσ hπsep hγtpfar
      (by rw [hγb, dist_self]; exact hρ0)
    obtain ⟨σ₁, hσ₁, hσ₁eq⟩ := hs₁π
    obtain ⟨σ₂, hσ₂, hσ₂eq⟩ := hs₂π
    have hs₁M : γ s₁ ∈ M := by rw [← hσ₁eq]; exact hσM (hπσ σ₁ hσ₁)
    have hs₂M : γ s₂ ∈ M := by rw [← hσ₂eq]; exact hσM (hπσ σ₂ hσ₂)
    have hs₁lt : s₁ < tm := lt_of_le_of_ne hs₁.2 fun h =>
      middle_boundary_disjoint z hr hs₁M (by rw [h]; exact htmT.2) rfl
    have hs₂gt : tp < s₂ := lt_of_le_of_ne hs₂.1 fun h =>
      middle_boundary_disjoint z hr hs₂M (by rw [← h]; exact htpT.2) rfl
    have has₁ : a ≤ s₁ := hs₁.1
    have hs₂b : s₂ ≤ b := hs₂.2
    
    have hpiece1 : ∀ t ∈ Icc a s₁, γ t ∈ V := by
      have hpre : IsPreconnected (γ '' Icc a s₁) :=
        isPreconnected_Icc.image γ (hγc.mono (Icc_subset_Icc le_rfl
          (hs₁lt.le.trans htmT.1.2)))
      have hsub := subset_of_preconnected_avoid hVo hVcl hpre
        (by
          rintro _ ⟨t, ht, rfl⟩
          exact hbefore t ⟨ht.1, ht.2.trans (hs₁lt.le.trans htmT.1.2)⟩
            (ht.2.trans_lt hs₁lt))
        ⟨γ a, ⟨a, ⟨le_rfl, has₁⟩, rfl⟩, by rw [hγa]; exact huV⟩
      exact fun t ht => hsub ⟨t, ht, rfl⟩
    have hpiece2 : ∀ t ∈ Icc s₂ b, γ t ∈ V := by
      have hpre : IsPreconnected (γ '' Icc s₂ b) :=
        isPreconnected_Icc.image γ (hγc.mono (Icc_subset_Icc
          (htpT.1.1.trans hs₂gt.le) le_rfl))
      have hsub := subset_of_preconnected_avoid hVo hVcl hpre
        (by
          rintro _ ⟨t, ht, rfl⟩
          exact hafter t ⟨(htpT.1.1.trans hs₂gt.le).trans ht.1, ht.2⟩
            (hs₂gt.trans_le ht.1))
        ⟨γ b, ⟨b, ⟨hs₂b, le_rfl⟩, rfl⟩, by rw [hγb]; exact hvV⟩
      exact fun t ht => hsub ⟨t, ht, rfl⟩
    
    have hint := LSCMetric.isExtMetric_internal D V
    have htri : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        intExt D V x w ≤ intExt D V x y + intExt D V y w := by
      intro x y w hx hy hw
      exact hint.2.2.2 ⟨x, hx⟩ ⟨y, hy⟩ ⟨w, hw⟩
    have hsymm : ∀ x y : ℂ, x ∈ V → y ∈ V → intExt D V x y = intExt D V y x := by
      intro x y hx hy
      exact hint.2.2.1 ⟨x, hx⟩ ⟨y, hy⟩
    have h1 : intExt D V u (γ s₁) ≤ D.len γ a s₁ := by
      have hc : D.IsCurve γ a s₁ := ⟨has₁, hγ.2.mono (Icc_subset_Icc le_rfl
        (hs₁lt.le.trans htmT.1.2))⟩
      have h := intExt_le_len hc hpiece1
      rwa [hγa] at h
    have h3 : intExt D V (γ s₂) v ≤ D.len γ s₂ b := by
      rw [← hγb]
      have hc : D.IsCurve γ s₂ b := ⟨hs₂b, hγ.2.mono (Icc_subset_Icc
        (htpT.1.1.trans hs₂gt.le) le_rfl)⟩
      exact intExt_le_len hc hpiece2
    have h2 : intExt D V (γ s₁) (γ s₂) ≤ D.len π α β := by
      rw [← hσ₁eq, ← hσ₂eq]
      rcases le_total σ₁ σ₂ with h12 | h21
      · have hc : D.IsCurve π σ₁ σ₂ := ⟨h12, hπ.2.mono (Icc_subset_Icc hσ₁.1 hσ₂.2)⟩
        exact (intExt_le_len hc fun τ hτ => hπV τ ⟨hσ₁.1.trans hτ.1, hτ.2.trans hσ₂.2⟩).trans
          (eVariationOn.mono _ (Icc_subset_Icc hσ₁.1 hσ₂.2))
      · have hc : D.IsCurve π σ₂ σ₁ := ⟨h21, hπ.2.mono (Icc_subset_Icc hσ₂.1 hσ₁.2)⟩
        rw [hsymm _ _ (hπV σ₁ hσ₁) (hπV σ₂ hσ₂)]
        exact (intExt_le_len hc fun τ hτ => hπV τ ⟨hσ₂.1.trans hτ.1, hτ.2.trans hσ₁.2⟩).trans
          (eVariationOn.mono _ (Icc_subset_Icc hσ₂.1 hσ₁.2))
    
    have hmid : D.len π α β ≤ D.len γ s₁ s₂ := by
      refine hπlen.trans ?_
      calc
        OptimalConstants.Ratios.setDist D M F ≤ D (γ s₁, γ tm) := iInf₂_le_of_le _ hs₁M
          (iInf₂_le (f := fun w (_ : w ∈ F) => D (γ s₁, w)) (γ tm) htmT.2)
        _ ≤ D.len γ s₁ tm := LSCMetric.apply_le_len D γ hs₁lt.le
        _ ≤ D.len γ s₁ s₂ := eVariationOn.mono _ (Icc_subset_Icc le_rfl (htmtp.trans hs₂gt.le))
    
    have hadd : D.len γ a s₁ + D.len γ s₁ s₂ + D.len γ s₂ b = D.len γ a b := by
      have hs₁s₂ : s₁ ≤ s₂ := hs₁lt.le.trans (htmtp.trans hs₂gt.le)
      have e1 := eVariationOn.Icc_add_Icc (D.pt ∘ γ) has₁ hs₁s₂ (s := univ) (mem_univ _)
      have e2 := eVariationOn.Icc_add_Icc (D.pt ∘ γ) (has₁.trans hs₁s₂) hs₂b (s := univ)
        (mem_univ _)
      simp only [univ_inter] at e1 e2
      change eVariationOn (D.pt ∘ γ) (Icc a s₁) + eVariationOn (D.pt ∘ γ) (Icc s₁ s₂) +
        eVariationOn (D.pt ∘ γ) (Icc s₂ b) = eVariationOn (D.pt ∘ γ) (Icc a b)
      rw [e1, e2]
    calc
      intExt D V u v ≤ intExt D V u (γ s₁) + intExt D V (γ s₁) v :=
        htri u (γ s₁) v huV (hMV hs₁M) hvV
      _ ≤ intExt D V u (γ s₁) + (intExt D V (γ s₁) (γ s₂) + intExt D V (γ s₂) v) :=
        add_le_add le_rfl (htri _ _ _ (hMV hs₁M) (hMV hs₂M) hvV)
      _ ≤ D.len γ a s₁ + (D.len γ s₁ s₂ + D.len γ s₂ b) :=
        add_le_add h1 (add_le_add (h2.trans hmid) h3)
      _ = D.len γ a b := by rw [← add_assoc, hadd]
      _ ≤ D (u, v) + ε := hgoal
  · 
    push Not at hmeet
    have hpre : IsPreconnected (γ '' Icc a b) := isPreconnected_Icc.image γ hγc
    have hsub := subset_of_preconnected_avoid hVo hVcl hpre
      (by rintro _ ⟨t, ht, rfl⟩; exact hmeet t ht)
      ⟨γ a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩, by rw [hγa]; exact huV⟩
    have hc := intExt_le_len hγ fun t ht => hsub ⟨t, ht, rfl⟩
    rw [hγa, hγb] at hc
    exact hc.trans hgoal

 

 
theorem closedBall_subset_carrier_of_middle {z x : ℂ} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ TwoScale.S36Events.eventMiddle z r) :
    Metric.closedBall x (r / 5) ⊆ TwoScale.S36Events.eventCarrier z r := by
  intro y hy
  obtain ⟨hx1, hx2⟩ := hx
  rw [Metric.mem_ball] at hx1
  rw [Metric.mem_closedBall, not_le] at hx2
  rw [Metric.mem_closedBall] at hy
  have h1 := dist_triangle y x z
  have h2 := dist_triangle x y z
  have h3 : dist x y = dist y x := dist_comm x y
  refine ⟨Metric.mem_closedBall.mpr (by linarith), ?_⟩
  rw [Metric.mem_ball, not_lt]
  linarith

theorem sphere_subset_middle {z : ℂ} {r s : ℝ} (hr : 0 < r) (hs1 : 3 * r / 4 < s)
    (hs2 : s < 3 * r / 2) : Metric.sphere z s ⊆ TwoScale.S36Events.eventMiddle z r := by
  intro y hy
  rw [Metric.mem_sphere] at hy
  exact ⟨Metric.mem_ball.mpr (by linarith), by rw [Metric.mem_closedBall, not_le]; linarith⟩

theorem sqrt_lt_tenth {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1 / 100) : Real.sqrt q < 1 / 10 := by
  rw [show (1 / 10 : ℝ) = Real.sqrt (1 / 100) by
    rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt hq0 hq

 

theorem shield_internal_eq {d e : LSCMetric}
    (hcd : ∀ (γ : ℝ → ℂ) (a b : ℝ), d.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hce : ∀ (γ : ℝ → ℂ) (a b : ℝ), e.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hLd : d.IsLengthSpace) (hLe : e.IsLengthSpace) {Cm Cp : ℝ} (hCm : 0 < Cm)
    (hCmp : Cm ≤ Cp)
    (hcmp : ∀ x y, ENNReal.ofReal Cm * d (x, y) ≤ e (x, y) ∧
      e (x, y) ≤ ENNReal.ofReal Cp * d (x, y))
    {z u v : ℂ} {r q : ℝ} (hr : 0 < r) (hq0 : 0 < q) (hq : q < 1 / 100)
    (hv : v ∈ Metric.sphere z r) (huv : dist u v ≤ q * r)
    (hm : OptimalConstants.Ratios.setDist d (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) < ⊤)
    (hsh : TwoScale.Consolidated.aroundAt d v (q * r) (Real.sqrt q * r) ≤ ENNReal.ofReal (Cm / (2 * Cp)) *
      OptimalConstants.Ratios.setDist d (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)) :
    intExt d (TwoScale.S36Events.eventOpen z r) u v = d (u, v) ∧
      intExt e (TwoScale.S36Events.eventOpen z r) u v = e (u, v) := by
  set M := TwoScale.S36Events.eventMiddle z r
  set F := TwoScale.S36Events.eventBoundary z r
  set m := OptimalConstants.Ratios.setDist d M F with hmdef
  have hCp : 0 < Cp := hCm.trans_le hCmp
  have hq1 : q < 1 := by linarith
  have hsq : Real.sqrt q < 1 / 10 := sqrt_lt_tenth hq0.le hq
  have hρσ : q * r ≤ Real.sqrt q * r :=
    mul_le_mul_of_nonneg_right (TwoScale.Consolidated.lt_sqrt_self hq0 hq1).le hr.le
  have hvM : v ∈ M := sphere_subset_middle hr (by linarith) (by linarith) hv
  have hσM : Metric.closedBall v (Real.sqrt q * r) ⊆ M := by
    intro y hy
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_sphere] at hv
    have h1 := dist_triangle y v z
    have h2 := dist_triangle v y z
    have h3 : dist v y = dist y v := dist_comm v y
    have hσ : Real.sqrt q * r < r / 10 := by nlinarith
    exact ⟨Metric.mem_ball.mpr (by linarith), by rw [Metric.mem_closedBall, not_le]; linarith⟩
  have hFfar : ∀ y ∈ F, Real.sqrt q * r ≤ dist y v := by
    intro y hy
    rw [Metric.mem_sphere] at hv
    have hσ : Real.sqrt q * r < r / 10 := by nlinarith
    have h1 := dist_triangle y v z
    have h2 := dist_triangle v y z
    have h3 : dist v y = dist y v := dist_comm v y
    rcases hy with hy | hy <;> rw [Metric.mem_sphere] at hy
    · linarith
    · linarith
  have hm0 : 0 < m := setDist_middle_pos d z hr
  have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hq0 hq1
  
  have hlt : ENNReal.ofReal (Cm / (2 * Cp)) * m < ENNReal.ofReal (Cm / Cp) * m := by
    refine (ENNReal.mul_lt_mul_iff_left hm0.ne' hm.ne).mpr ?_
    refine (ENNReal.ofReal_lt_ofReal_iff (div_pos hCm hCp)).mpr ?_
    rw [div_lt_div_iff₀ (by positivity) hCp]
    nlinarith
  have harnd : aroundDist d ⟨(v, (q * r, Real.sqrt q * r)), hvalid⟩ <
      ENNReal.ofReal (Cm / Cp) * m := by
    rw [← TwoScale.Consolidated.aroundAt_eq d v _ _ hvalid]
    exact hsh.trans_lt hlt
  unfold aroundDist at harnd
  simp only [iInf_lt_iff] at harnd
  obtain ⟨π, α, β, hπ, hπA, hπsep, hπlen⟩ := harnd
  have hπσ : ∀ τ ∈ Icc α β, π τ ∈ Metric.closedBall v (Real.sqrt q * r) := by
    intro τ hτ
    have h := hπA τ hτ
    exact Metric.ball_subset_closedBall h.1
  have hsep : Disconnects (π '' Icc α β) (Metric.sphere v (q * r))
      (Metric.sphere v (Real.sqrt q * r)) := hπsep
  have hk1 : ENNReal.ofReal (Cm / Cp) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr ((div_le_one hCp).mpr hCmp)
  
  have hdlen : d.len π α β ≤ m := by
    calc
      d.len π α β ≤ ENNReal.ofReal (Cm / Cp) * m := hπlen.le
      _ ≤ 1 * m := mul_le_mul' hk1 le_rfl
      _ = m := one_mul m
  have hd := intExt_le_of_separator hcd hLd hr hρσ hσM hFfar huv
    (mul_nonneg hq0.le hr.le) hπ hπσ hsep hdlen
  
  obtain ⟨hπe, hπelen⟩ := curve_len_of_le_mul (e := e) (d := d) ENNReal.ofReal_ne_top
    (fun x y => (hcmp x y).2) hπ
  have hme : ENNReal.ofReal Cm * m ≤ OptimalConstants.Ratios.setDist e M F := by
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    exact (mul_le_mul' le_rfl (iInf₂_le_of_le x hx
      (iInf₂_le (f := fun w (_ : w ∈ F) => d (x, w)) y hy))).trans (hcmp x y).1
  have helen : e.len π α β ≤ OptimalConstants.Ratios.setDist e M F := by
    calc
      e.len π α β ≤ ENNReal.ofReal Cp * d.len π α β := hπelen
      _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal (Cm / Cp) * m) := mul_le_mul' le_rfl hπlen.le
      _ = ENNReal.ofReal Cm * m := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCp.le]
        congr 2
        field_simp
      _ ≤ OptimalConstants.Ratios.setDist e M F := hme
  have he := intExt_le_of_separator hce hLe hr hρσ hσM hFfar huv
    (mul_nonneg hq0.le hr.le) hπe hπσ hsep helen
  exact ⟨le_antisymm hd (dist_le_intExt d _ u v), le_antisymm he (dist_le_intExt e _ u v)⟩

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
