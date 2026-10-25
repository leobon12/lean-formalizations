import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.CountV2




 










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset LQGMetric.MetricGeometry Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

 

theorem ovSet_finite_card
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
    (haround : (EndSaving.Spent.closedContactTimes P (V : Set ℂ) T).Nonempty →
      ENNReal.ofReal (EndSaving.Spent.lastClosedContact P (V : Set ℂ) T -
        EndSaving.Spent.firstClosedContact P (V : Set ℂ) T) ≤ ENNReal.ofReal A) :
    ∃ hfin : (ovSet P T (ball z (4 * r)) V).Finite,
      (hfin.toFinset.card : ℝ) * c ≤ A := by
  have hO : IsOpen (ball z (4 * r)) := isOpen_ball
  have hVO : closure (V : Set ℂ) ⊆ ball z (4 * r) :=
    hV.trans (ball_subset_ball (by linarith))
  have hA : 0 ≤ A := hc.le.trans hcA
  have hbound : ∀ F : Finset (ℝ × ℝ × ℝ × ℝ),
      (F : Set (ℝ × ℝ × ℝ × ℝ)) ⊆ ovSet P T (ball z (4 * r)) V → (F.card : ℝ) * c ≤ A := by
    intro F hF
    rcases F.eq_empty_or_nonempty with hFe | ⟨e, he⟩
    · subst hFe; simp [hA]
    · have hne : (EndSaving.Spent.closedContactTimes P (V : Set ℂ) T).Nonempty := by
        have hex := (hF he).1
        obtain ⟨he12, he34, _, _⟩ := exc_basic hO hVO hex
        obtain ⟨h0, _, h23, _, h4T, _, _, _, hτ, _, _, _⟩ := hex
        exact ⟨e.2.1, ⟨h0.trans he12.le, h23.trans (he34.le.trans h4T)⟩, hτ⟩
      exact ov_finset_card_le d1 Dh ξ C c A f hWeyl P hG hu hP z r hr V hV hf0 hfC
        hcharge hc hcA (haround hne) F hF
  have hfin : (ovSet P T (ball z (4 * r)) V).Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := exists_nat_gt (A / c)
    obtain ⟨F, hFs, hFc⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have := hbound F hFs
    rw [hFc] at this
    have hlt : A < n * c := by
      rw [div_lt_iff₀ hc] at hn
      exact hn
    linarith
  exact ⟨hfin, hbound _ (by simp)⟩

 
theorem ov_window_lt {P : ℝ → ℂ} {T : ℝ} {O : Set ℂ} {V : TopologicalSpace.Opens ℂ}
    (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O) (hVO : closure (V : Set ℂ) ⊆ O)
    {e : ℝ × ℝ × ℝ × ℝ} (he : e ∈ ovSet P T O V) : e.2.1 < e.2.2.1 := by
  obtain ⟨hτV, hσV⟩ := exc_window_endpoints_not_open hP hO hVO he.1
  obtain ⟨he12, he34, _, _⟩ := exc_basic hO hVO he.1
  obtain ⟨_, _, h23, _, _, _, _, _, _, _, hbefore, hafter⟩ := he.1
  obtain ⟨t, ht, htV⟩ := he.2
  have hτt : e.2.1 ≤ t := by
    by_contra h
    exact hbefore t ⟨ht.1, lt_of_not_ge h⟩ (subset_closure htV)
  have htσ : t ≤ e.2.2.1 := by
    by_contra h
    exact hafter t ⟨lt_of_not_ge h, ht.2⟩ (subset_closure htV)
  have hne : e.2.1 ≠ t := fun h => hτV (h ▸ htV)
  exact (lt_of_le_of_ne hτt hne).trans_le htσ

 
theorem lower0_pathwise {ι : Type*} [DecidableEq ι]
    (d1 d0 : LSCMetric) (ξ : ℝ) (fR : C(ℂ, ℝ))
    (hW0 : ∀ p : ℂ × ℂ, d0 p = weylScale ξ fR d1 p)
    (P : ℝ → ℂ) {T : ℝ}
    (hG : IsGeodesicCurve (d1.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (d1.pt ∘ P) (Icc 0 T))
    (hP : ContinuousOn P (Icc 0 T))
    (R : Finset ι) (z : ι → ℂ) (r : ℝ) (hr : 0 < r) (V : ι → TopologicalSpace.Opens ℂ)
    (hV : ∀ i ∈ R, closure ((V i : Set ℂ)) ⊆ ball (z i) (3 * r))
    (hball : ∀ i ∈ R, ∀ j ∈ R, i ≠ j →
      Disjoint (ball (z i) (4 * r)) (ball (z j) (4 * r)))
    (hP0 : ∀ i ∈ R, P 0 ∉ ball (z i) (4 * r))
    (hPT : ∀ i ∈ R, P T ∉ ball (z i) (4 * r))
    (hfR : ∀ x, (∀ i ∈ R, x ∉ (V i : Set ℂ)) → fR x = 0)
    (hfin : ∀ i ∈ R, (ovSet P T (ball (z i) (4 * r)) (V i)).Finite) :
    d0 (P 0, P T) ≤ ENNReal.ofReal T + ∑ i ∈ R.attach,
      ∑ e ∈ (hfin i.1 i.2).toFinset, d0 (P e.2.1, P e.2.2.1) := by
  have hT : 0 ≤ T := hG.1
  have hO : ∀ i, IsOpen (ball (z i) (4 * r)) := fun i => isOpen_ball
  have hVO : ∀ i ∈ R, closure ((V i : Set ℂ)) ⊆ ball (z i) (4 * r) :=
    fun i hi => (hV i hi).trans (ball_subset_ball (by linarith))
  set J := R.attach.sigma (fun i => (hfin i.1 i.2).toFinset) with hJ
  have hmemJ : ∀ x ∈ J, x.2 ∈ ovSet P T (ball (z x.1.1) (4 * r)) (V x.1.1) := by
    intro x hx
    rw [hJ, Finset.mem_sigma] at hx
    exact (Set.Finite.mem_toFinset _).mp hx.2
  have hst : ∀ x ∈ J, x.2.2.1 < x.2.2.2.1 := fun x hx =>
    ov_window_lt hP (hO _) (hVO _ x.1.2) (hmemJ x hx)
  have hin : ∀ x ∈ J, 0 ≤ x.2.2.1 ∧ x.2.2.2.1 ≤ T := by
    intro x hx
    obtain ⟨he12, he34, _, _⟩ := exc_basic (hO _) (hVO _ x.1.2) (hmemJ x hx).1
    obtain ⟨h0, _, _, _, h4T, _⟩ := (hmemJ x hx).1
    exact ⟨h0.trans he12.le, he34.le.trans h4T⟩
  have hwin : ∀ x ∈ J, x.2.1 ≤ x.2.2.1 ∧ x.2.2.2.1 ≤ x.2.2.2.2 := by
    intro x hx
    obtain ⟨he12, he34, _, _⟩ := exc_basic (hO _) (hVO _ x.1.2) (hmemJ x hx).1
    exact ⟨he12.le, he34.le⟩
  have hdisj : ∀ x ∈ J, ∀ y ∈ J, x ≠ y → x.2.2.2.1 ≤ y.2.2.1 ∨ y.2.2.2.1 ≤ x.2.2.1 := by
    intro x hx y hy hxy
    have hord : x.2.2.2.2 ≤ y.2.1 ∨ y.2.2.2.2 ≤ x.2.1 := by
      by_cases hi : x.1 = y.1
      · have he : x.2 ≠ y.2 := by
          intro h
          apply hxy
          exact Sigma.ext hi (heq_of_eq h)
        have hyx : y.2 ∈ ovSet P T (ball (z x.1.1) (4 * r)) (V x.1.1) := hi ▸ hmemJ y hy
        rcases exc_eq_or_ordered (hO _) (hVO _ x.1.2) (hmemJ x hx).1 hyx.1 with h | h
        · exact absurd h he
        · exact h
      · have hne : x.1.1 ≠ y.1.1 := fun h => hi (Subtype.ext h)
        exact exc_ordered_of_disjoint (hO _) (hO _) (hVO _ x.1.2) (hVO _ y.1.2)
          (hball _ x.1.2 _ y.1.2 hne) (hmemJ x hx).1 (hmemJ y hy).1
    obtain ⟨hx1, hx2⟩ := hwin x hx
    obtain ⟨hy1, hy2⟩ := hwin y hy
    rcases hord with h | h
    · left; linarith
    · right; linarith
  have hgap : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      (∀ x ∈ J, x.2.2.2.1 ≤ a ∨ b ≤ x.2.2.1) → d0 (P a, P b) ≤ ENNReal.ofReal (b - a) := by
    intro a b ha hab hb hgapJ
    have h := EndSaving.PathSurgery.weyl_subpath_le d1 d0 ξ fR hW0 P (c := 0) hG hu ha hab hb (by
      intro v hv
      have hvI : v ∈ Icc 0 T := ⟨ha.trans hv.1, hv.2.trans hb⟩
      have hzero : fR (P v) = 0 := by
        apply hfR
        intro i hi hvV
        obtain ⟨e, heS, hτv, hvσ⟩ := openVisit_mem_window hT hP (hO i) (hVO i hi)
          (hP0 i hi) (hPT i hi) hvI hvV
        have hxJ : (⟨⟨i, hi⟩, e⟩ : Σ _ : R, ℝ × ℝ × ℝ × ℝ) ∈ J := by
          rw [hJ, Finset.mem_sigma]
          exact ⟨Finset.mem_attach _ _, (Set.Finite.mem_toFinset _).mpr heS⟩
        obtain ⟨hτV, hσV⟩ := exc_window_endpoints_not_open hP (hO i) (hVO i hi) heS.1
        rcases hgapJ _ hxJ with h | h
        · have : v = e.2.2.1 := le_antisymm hvσ (h.trans hv.1)
          exact hσV (this ▸ hvV)
        · have : v = e.2.1 := le_antisymm (hv.2.trans h) hτv
          exact hτV (this ▸ hvV)
      rw [hzero, mul_zero])
    simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using h
  have hchain := chain_bound J (fun x => x.2.2.1) (fun x => x.2.2.2.1)
    (fun a b => d0 (P a, P b)) (fun a b => ENNReal.ofReal (b - a))
    (by intro a b c _ _; exact d0.isExtMetric.2.2.2 _ _ _)
    (by
      intro a b c hab hbc
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc)]
      congr 1
      ring)
    0 T hT hst hin hdisj hgap
  simp only [sub_zero] at hchain
  calc d0 (P 0, P T) ≤ d0 (P 0, P T) + ∑ x ∈ J, ENNReal.ofReal (x.2.2.2.1 - x.2.2.1) :=
        le_self_add
    _ ≤ ENNReal.ofReal T + ∑ x ∈ J, d0 (P x.2.2.1, P x.2.2.2.1) := hchain
    _ = ENNReal.ofReal T + ∑ i ∈ R.attach,
          ∑ e ∈ (hfin i.1 i.2).toFinset, d0 (P e.2.1, P e.2.2.1) := by
        rw [hJ, Finset.sum_sigma]


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
