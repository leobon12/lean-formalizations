import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.ExcursionV2




 












set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset LQGMetric.MetricGeometry Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

 
theorem ov_charged_intervals
    (d1 Dh : LSCMetric) (ξ C c : ℝ) (f : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, Dh p = weylScale ξ f d1 p)
    (P : ℝ → ℂ) {T : ℝ}
    (hG : IsGeodesicCurve (d1.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (d1.pt ∘ P) (Icc 0 T))
    (hP : ContinuousOn P (Icc 0 T))
    (z : ℂ) (r : ℝ) (hr : 0 < r) (V : TopologicalSpace.Opens ℂ)
    (hV : closure (V : Set ℂ) ⊆ ball z (3 * r))
    (hf0 : ∀ x ∈ ball z (4 * r), x ∉ (V : Set ℂ) → f x = 0)
    (hfC : ∀ x, ξ * f x ≤ C)
    (hcharge : ENNReal.ofReal c ≤ OptimalConstants.Ratios.setDist Dh (sphere z (3 * r)) (V : Set ℂ))
    (hc : 0 < c)
    {e : ℝ × ℝ × ℝ × ℝ} (he : e ∈ ovSet P T (ball z (4 * r)) V) :
    ∃ α ι ο β : ℝ, e.1 ≤ α ∧ α < ι ∧ ι ≤ ο ∧ ο < β ∧ β ≤ e.2.2.2 ∧
      ι ∈ EndSaving.Spent.closedContactTimes P (V : Set ℂ) T ∧
      ο ∈ EndSaving.Spent.closedContactTimes P (V : Set ℂ) T ∧
      c ≤ ι - α ∧ c ≤ β - ο := by
  have hO : IsOpen (ball z (4 * r)) := isOpen_ball
  have hVO : closure (V : Set ℂ) ⊆ ball z (4 * r) :=
    hV.trans (ball_subset_ball (by linarith))
  obtain ⟨he12, he34, _, _⟩ := exc_basic hO hVO he.1
  obtain ⟨h0, h12, h23, h34, h4T, hf1, hf4, hinside, _, _, _, _⟩ := he.1
  obtain ⟨t₀, ht₀, ht₀V⟩ := he.2
  have hr4 : (4 * r) ≠ 0 := by positivity
  have hd1 : dist (P e.1) z = 4 * r := by
    rw [frontier_ball z hr4] at hf1
    exact hf1
  have hd4 : dist (P e.2.2.2) z = 4 * r := by
    rw [frontier_ball z hr4] at hf4
    exact hf4
  have hdt₀ : dist (P t₀) z < 3 * r := mem_ball.mp (hV (subset_closure ht₀V))
  have hτ'T : e.1 ≤ T := h12.trans (h23.trans (h34.trans h4T))
  have ht₀T : t₀ ≤ T := ht₀.2.le.trans h4T
  have hdc : ContinuousOn (fun u => dist (P u) z) (Icc 0 T) :=
    continuous_dist.comp_continuousOn (hP.prodMk continuousOn_const)
  
  obtain ⟨α, hαI, hαd⟩ := intermediate_value_Icc' ht₀.1.le
    (hdc.mono (Icc_subset_Icc h0 ht₀T)) ⟨hdt₀.le, by rw [hd1]; linarith⟩
  obtain ⟨β, hβI, hβd⟩ := intermediate_value_Icc ht₀.2.le
    (hdc.mono (Icc_subset_Icc (h0.trans ht₀.1.le) h4T)) ⟨hdt₀.le, by rw [hd4]; linarith⟩
  simp only at hαd hβd
  have hαne : α ≠ e.1 := by
    intro h; rw [h, hd1] at hαd; linarith
  have hβne : β ≠ e.2.2.2 := by
    intro h; rw [h, hd4] at hβd; linarith
  have hαgt : e.1 < α := lt_of_le_of_ne hαI.1 (Ne.symm hαne)
  have hβlt : β < e.2.2.2 := lt_of_le_of_ne hβI.2 hβne
  have hαS : P α ∈ sphere z (3 * r) := mem_sphere.mpr hαd
  have hβS : P β ∈ sphere z (3 * r) := mem_sphere.mpr hβd
  have hnotV : ∀ x ∈ sphere z (3 * r), x ∉ (V : Set ℂ) := by
    intro x hx hxV
    have := mem_ball.mp (hV (subset_closure hxV))
    rw [mem_sphere.mp hx] at this
    exact lt_irrefl _ this
  have hfloc : ∀ v ∈ Icc α β, P v ∉ (V : Set ℂ) → f (P v) = 0 := by
    intro v hv hvV
    exact hf0 (P v) (hinside v ⟨hαgt.trans_le hv.1, hv.2.trans_lt hβlt⟩) hvV
  have hα0 : 0 ≤ α := h0.trans hαI.1
  
  have hentry := first_open_entry_charge_local d1 Dh ξ f hWeyl P (sphere z (3 * r))
    (V : Set ℂ) c C hG hu hα0 hαI.2 ht₀T hαS
    (fun v hv hvV => hfloc v ⟨hv.1, hv.2.trans hβI.1⟩ hvV) hfC (hnotV _ hαS) ht₀V hcharge
  have hexit := last_open_exit_charge_local d1 Dh ξ f hWeyl P (sphere z (3 * r))
    (V : Set ℂ) c C hG hu (h0.trans ht₀.1.le) hβI.1 (hβI.2.trans h4T) hβS
    (fun v hv hvV => hfloc v ⟨hαI.2.trans hv.1, hv.2⟩ hvV) hfC ht₀V (hnotV _ hβS) hcharge
  set ι := sInf {t ∈ Icc α t₀ | P t ∈ (V : Set ℂ)} with hι
  set ο := sSup {t ∈ Icc t₀ β | P t ∈ (V : Set ℂ)} with hο
  have hιt₀ : ι ≤ t₀ := csInf_le ⟨α, fun u hu => hu.1.1⟩ ⟨⟨hαI.2, le_rfl⟩, ht₀V⟩
  have ht₀ο : t₀ ≤ ο := le_csSup ⟨β, fun u hu => hu.1.2⟩ ⟨⟨le_rfl, hβI.1⟩, ht₀V⟩
  have hιcl : P ι ∈ closure (V : Set ℂ) :=
    EndSaving.PathSurgery.first_open_entry_mem_closure P (V : Set ℂ) hαI.2
      (hP.mono (Icc_subset_Icc hα0 ht₀T)) (hnotV _ hαS) ht₀V
  have hοcl : P ο ∈ closure (V : Set ℂ) :=
    last_open_visit_mem_closure P (V : Set ℂ) hβI.1
      (hP.mono (Icc_subset_Icc (h0.trans ht₀.1.le) (hβI.2.trans h4T))) ht₀V
  refine ⟨α, ι, ο, β, hαI.1, by linarith, hιt₀.trans ht₀ο, by linarith, hβI.2,
    ⟨⟨by linarith, hιt₀.trans ht₀T⟩, hιcl⟩,
    ⟨⟨h0.trans (ht₀.1.le.trans ht₀ο), by linarith [hβI.2]⟩, hοcl⟩, hentry, hexit⟩

 

theorem ov_finset_card_le
    (d1 Dh : LSCMetric) (ξ C c A : ℝ) (f : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, Dh p = weylScale ξ f d1 p)
    (P : ℝ → ℂ) {T : ℝ}
    (hG : IsGeodesicCurve (d1.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (d1.pt ∘ P) (Icc 0 T))
    (hP : ContinuousOn P (Icc 0 T))
    (z : ℂ) (r : ℝ) (hr : 0 < r) (V : TopologicalSpace.Opens ℂ)
    (hV : closure (V : Set ℂ) ⊆ ball z (3 * r))
    (hf0 : ∀ x ∈ ball z (4 * r), x ∉ (V : Set ℂ) → f x = 0)
    (hfC : ∀ x, ξ * f x ≤ C)
    (hcharge : ENNReal.ofReal c ≤ OptimalConstants.Ratios.setDist Dh (sphere z (3 * r)) (V : Set ℂ))
    (hc : 0 < c) (hcA : c ≤ A)
    (haround : ENNReal.ofReal (EndSaving.Spent.lastClosedContact P (V : Set ℂ) T -
      EndSaving.Spent.firstClosedContact P (V : Set ℂ) T) ≤ ENNReal.ofReal A)
    (F : Finset (ℝ × ℝ × ℝ × ℝ)) (hF : (F : Set (ℝ × ℝ × ℝ × ℝ)) ⊆ ovSet P T (ball z (4 * r)) V) :
    (F.card : ℝ) * c ≤ A := by
  have hA : 0 ≤ A := hc.le.trans hcA
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · subst hFe; simp [hA]
  have hO : IsOpen (ball z (4 * r)) := isOpen_ball
  have hVO : closure (V : Set ℂ) ⊆ ball z (4 * r) :=
    hV.trans (ball_subset_ball (by linarith))
  have hint : ∀ e, e ∈ ovSet P T (ball z (4 * r)) V →
      ∃ α ι ο β : ℝ, e.1 ≤ α ∧ α < ι ∧ ι ≤ ο ∧ ο < β ∧ β ≤ e.2.2.2 ∧
        ι ∈ EndSaving.Spent.closedContactTimes P (V : Set ℂ) T ∧
        ο ∈ EndSaving.Spent.closedContactTimes P (V : Set ℂ) T ∧
        c ≤ ι - α ∧ c ≤ β - ο := fun e he =>
    ov_charged_intervals d1 Dh ξ C c f hWeyl P hG hu hP z r hr V hV hf0 hfC hcharge hc he
  choose! α ι ο β hα hαι hιο hοβ hβ hιC hοC hcι hcβ using hint
  obtain ⟨e₀, he₀F, hmin⟩ := F.exists_min_image (fun e => e.1) hFne
  obtain ⟨e₁, he₁F, hmax⟩ := F.exists_max_image (fun e => e.1) hFne
  have hneC : (EndSaving.Spent.closedContactTimes P (V : Set ℂ) T).Nonempty :=
    ⟨ι e₀, hιC e₀ (hF he₀F)⟩
  obtain ⟨_, _, horder⟩ := EndSaving.Spent.closed_contact_extrema P (V : Set ℂ) hP hneC
  set S₀ := EndSaving.Spent.firstClosedContact P (V : Set ℂ) T with hS₀
  set T₀ := EndSaving.Spent.lastClosedContact P (V : Set ℂ) T with hT₀
  have hcontact : ∀ e ∈ F, e.2.1 ∈ EndSaving.Spent.closedContactTimes P (V : Set ℂ) T := by
    intro e heF
    obtain ⟨he12, he34, _, _⟩ := exc_basic hO hVO (hF heF).1
    obtain ⟨h0, _, h23, _, h4T, _, _, _, hτ, _, _, _⟩ := (hF heF).1
    exact ⟨⟨h0.trans he12.le, h23.trans (he34.le.trans h4T)⟩, hτ⟩
  have hordered : ∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → e.2.2.2 ≤ e'.1 ∨ e'.2.2.2 ≤ e.1 := by
    intro e heF e' he'F hne
    rcases exc_eq_or_ordered hO hVO (hF heF).1 (hF he'F).1 with h | h
    · exact absurd h hne
    · exact h
  have hτσ' : ∀ e ∈ F, e.2.1 ≤ e.2.2.2 := by
    intro e heF
    obtain ⟨_, he34, _, _⟩ := exc_basic hO hVO (hF heF).1
    exact (hF heF).1.2.2.1.trans he34.le
  have hσ'τ : ∀ e ∈ F, e.1 ≤ e.2.1 := fun e heF => (hF heF).1.2.1
  
  have hafterFirst : ∀ e ∈ F, e ≠ e₀ → e₀.2.2.2 ≤ e.1 := by
    intro e heF hne
    rcases hordered e heF e₀ he₀F hne with h | h
    · have h1 := hmin e heF
      have h2 : e.1 < e.2.2.2 := (exc_basic hO hVO (hF heF).1).1.trans_le (hτσ' e heF)
      linarith
    · exact h
  have hbeforeLast : ∀ e ∈ F, e ≠ e₁ → e.2.2.2 ≤ e₁.1 := by
    intro e heF hne
    rcases hordered e heF e₁ he₁F hne with h | h
    · exact h
    · have h1 := hmax e heF
      have h2 : e₁.1 < e₁.2.2.2 :=
        (exc_basic hO hVO (hF he₁F).1).1.trans_le (hτσ' e₁ he₁F)
      linarith
  let I : Finset ((ℝ × ℝ × ℝ × ℝ) ⊕ (ℝ × ℝ × ℝ × ℝ)) := (F.erase e₀).disjSum (F.erase e₁)
  let s : (ℝ × ℝ × ℝ × ℝ) ⊕ (ℝ × ℝ × ℝ × ℝ) → ℝ := Sum.elim α ο
  let t : (ℝ × ℝ × ℝ × ℝ) ⊕ (ℝ × ℝ × ℝ × ℝ) → ℝ := Sum.elim ι β
  have hS₀le : ∀ x ∈ EndSaving.Spent.closedContactTimes P (V : Set ℂ) T, S₀ ≤ x := fun x hx => (horder x hx).1
  have hleT₀ : ∀ x ∈ EndSaving.Spent.closedContactTimes P (V : Set ℂ) T, x ≤ T₀ := fun x hx => (horder x hx).2
  have hwin : ∀ x ∈ I, (∃ e ∈ F, x = Sum.inl e ∨ x = Sum.inr e) := by
    intro x hx
    rcases x with e | e
    · exact ⟨e, Finset.mem_of_mem_erase (Finset.inl_mem_disjSum.mp hx), Or.inl rfl⟩
    · exact ⟨e, Finset.mem_of_mem_erase (Finset.inr_mem_disjSum.mp hx), Or.inr rfl⟩
  have hsub : ∀ x ∈ I, ∀ e ∈ F, (x = Sum.inl e ∨ x = Sum.inr e) →
      e.1 ≤ s x ∧ t x ≤ e.2.2.2 := by
    intro x _ e heF hx
    rcases hx with rfl | rfl
    · exact ⟨hα e (hF heF), (hιο e (hF heF)).trans ((hοβ e (hF heF)).le.trans (hβ e (hF heF)))⟩
    · exact ⟨(hα e (hF heF)).trans ((hαι e (hF heF)).le.trans (hιο e (hF heF))), hβ e (hF heF)⟩
  have hstI : ∀ x ∈ I, s x < t x := by
    intro x hx
    rcases x with e | e
    · exact hαι e (hF (Finset.mem_of_mem_erase (Finset.inl_mem_disjSum.mp hx)))
    · exact hοβ e (hF (Finset.mem_of_mem_erase (Finset.inr_mem_disjSum.mp hx)))
  have hinI : ∀ x ∈ I, S₀ ≤ s x ∧ t x ≤ T₀ := by
    intro x hx
    rcases x with e | e
    · have heF := Finset.mem_erase.mp (Finset.inl_mem_disjSum.mp hx)
      refine ⟨?_, hleT₀ _ (hιC e (hF heF.2))⟩
      calc S₀ ≤ e₀.2.1 := hS₀le _ (hcontact e₀ he₀F)
        _ ≤ e₀.2.2.2 := hτσ' e₀ he₀F
        _ ≤ e.1 := hafterFirst e heF.2 heF.1
        _ ≤ α e := hα e (hF heF.2)
    · have heF := Finset.mem_erase.mp (Finset.inr_mem_disjSum.mp hx)
      refine ⟨hS₀le _ (hοC e (hF heF.2)), ?_⟩
      calc β e ≤ e.2.2.2 := hβ e (hF heF.2)
        _ ≤ e₁.1 := hbeforeLast e heF.2 heF.1
        _ ≤ e₁.2.1 := hσ'τ e₁ he₁F
        _ ≤ T₀ := hleT₀ _ (hcontact e₁ he₁F)
  have hdisjI : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → t x ≤ s y ∨ t y ≤ s x := by
    intro x hx y hy hxy
    obtain ⟨e, heF, hxe⟩ := hwin x hx
    obtain ⟨e', he'F, hye⟩ := hwin y hy
    by_cases hee : e = e'
    · subst hee
      rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
      · exact absurd rfl hxy
      · left; exact hιο e (hF heF)
      · right; exact hιο e (hF heF)
      · exact absurd rfl hxy
    · obtain ⟨hxs, hxt⟩ := hsub x hx e heF hxe
      obtain ⟨hys, hyt⟩ := hsub y hy e' he'F hye
      rcases hordered e heF e' he'F hee with h | h
      · left; linarith
      · right; linarith
  have hS₀T₀ : S₀ ≤ T₀ := (hS₀le _ (hιC e₀ (hF he₀F))).trans (hleT₀ _ (hιC e₀ (hF he₀F)))
  have htotal := disjoint_intervals_total_le I s t S₀ T₀ hS₀T₀ hstI hinI hdisjI
  have hTS : T₀ - S₀ ≤ A := (ENNReal.ofReal_le_ofReal_iff hA).mp haround
  have hsplit : ∑ x ∈ I, (t x - s x) =
      ∑ e ∈ F.erase e₀, (ι e - α e) + ∑ e ∈ F.erase e₁, (β e - ο e) := by
    simp only [I, Finset.sum_disjSum, s, t, Sum.elim_inl, Sum.elim_inr]
  have hlow₁ : ((F.erase e₀).card : ℝ) * c ≤ ∑ e ∈ F.erase e₀, (ι e - α e) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun e he => hcι e (hF (Finset.mem_of_mem_erase he))
  have hlow₂ : ((F.erase e₁).card : ℝ) * c ≤ ∑ e ∈ F.erase e₁, (β e - ο e) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun e he => hcβ e (hF (Finset.mem_of_mem_erase he))
  have hcard₀ : ((F.erase e₀).card : ℝ) = (F.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem he₀F, Nat.cast_sub (Finset.card_pos.mpr hFne), Nat.cast_one]
  have hcard₁ : ((F.erase e₁).card : ℝ) = (F.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem he₁F, Nat.cast_sub (Finset.card_pos.mpr hFne), Nat.cast_one]
  have hkey : 2 * ((F.card : ℝ) - 1) * c ≤ A := by
    have := hsplit ▸ htotal
    rw [hcard₀] at hlow₁
    rw [hcard₁] at hlow₂
    linarith
  have hF1 : (1 : ℝ) ≤ F.card := by exact_mod_cast Finset.card_pos.mpr hFne
  rcases eq_or_lt_of_le hF1 with h1 | h2
  · rw [← h1, one_mul]; exact hcA
  · have h2' : (2 : ℝ) ≤ F.card := by
      have : 1 < F.card := by exact_mod_cast h2
      exact_mod_cast this
    nlinarith


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
