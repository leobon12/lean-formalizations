import SupercriticalLQGUniqueness.B2.Median.SurgeryPred

 










set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Toolkit.CompactPathInfimum
open Uniqueness.Objects.AnnulusTails
open Uniqueness.Objects.AnnulusTails.ICurve

 
def surgeryRegion : Set ℂ := {z | 0 < z.im ∧ z.im < 1 ∧ -2 < z.re ∧ z.re < 3}

theorem isBounded_surgeryRegion : Bornology.IsBounded surgeryRegion := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr ⟨5, ?_⟩
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 5 := by
      have : |z.re| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
      have : |z.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith

 
def cfun {d : LSCMetric} (e : ICurve d.Space) : ℝ → ℂ := fun t => e.γ t

 
def ctr {d : LSCMetric} (e : ICurve d.Space) : Set ℂ := cfun e '' Icc e.a e.b

theorem cfun_isCurve {d : LSCMetric} (e : ICurve d.Space) : d.IsCurve (cfun e) e.a e.b :=
  icurve_isCurve d e

theorem cfun_len {d : LSCMetric} (e : ICurve d.Space) : d.len (cfun e) e.a e.b = e.len := rfl

theorem mem_ratRect_iff (u₀ : ℝ) (q : ℚ × ℚ × ℚ × ℚ) (z : ℂ) :
    z ∈ ratRect u₀ q ↔ (q.1 : ℝ) ≤ z.re ∧ z.re ≤ (q.2.1 : ℝ) ∧
      (q.2.2.1 : ℝ) - u₀ ≤ z.im ∧ z.im ≤ (q.2.2.2 : ℝ) - u₀ := Iff.rfl

 

theorem replace_low (d : LSCMetric) (u₀ : ℝ) (hu₀ : |u₀| < 1 / 100)
    (hR : SideRemovable d u₀) (qB : ℚ) (hqB : 2 / 3 < (qB : ℝ) - u₀) (hqB' : (qB : ℝ) - u₀ < 1)
    (E F : ℚ × ℚ × ℚ × ℚ) {P : ℝ → ℂ} {s t : ℝ} (hP : d.IsCurve P s t)
    (hfin : d.len P s t ≠ ∞) (hsq : ∀ u ∈ Icc s t, P u ∈ unitSquare)
    (hlow : ∀ u ∈ Icc s t, (P u).im < 2 / 3)
    (hE : P s ∈ ratRect u₀ E) (hF : P t ∈ ratRect u₀ F) {η : ℝ} (hη : 0 < η) :
    ∃ (Q : ℝ → ℂ) (a b : ℝ), d.IsCurve Q a b ∧
      (∀ u ∈ Icc a b, Q u ∈ surgeryRegion) ∧
      Q a ∈ ratRect u₀ E ∧ Q b ∈ ratRect u₀ F ∧
      d.len Q a b < d.len P s t + ENNReal.ofReal η := by
  have hu := abs_lt.mp hu₀
  let V : ℚ × ℚ × ℚ × ℚ := (-1, 2, -1, qB)
  have hle : upperPathInf d (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F) 0 ≤ d.len P s t := by
    unfold upperPathInf
    apply compactPathInf_le_of_curve d _ _ _ P s t hP
    · intro u hu'
      have h := hsq u hu'
      have hl := hlow u hu'
      refine ⟨?_, h.2.2.1⟩
      simp only [V, mem_ratRect_iff, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat]
      refine ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith⟩
    · exact ⟨hE, (hsq s (left_mem_Icc.mpr hP.1)).2.2.1⟩
    · exact ⟨hF, (hsq t (right_mem_Icc.mpr hP.1)).2.2.1⟩
  have hlt : upperPathInf d (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F) 0 <
      d.len P s t + ENNReal.ofReal η :=
    lt_of_le_of_lt hle (ENNReal.lt_add_right hfin (by simpa using hη))
  obtain ⟨Q, a, b, hQ, htr, ha, -, hb, -, hlen⟩ :=
    exists_upper_curve_of_continuousAt d _ _ _ (hR V E F).1 hlt
  refine ⟨Q, a, b, hQ, ?_, ha, hb, hlen⟩
  intro u hu'
  obtain ⟨hV, hpos⟩ := htr u hu'
  simp only [V, mem_ratRect_iff, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at hV
  exact ⟨hpos, by linarith [hV.2.2.2], by linarith [hV.1], by linarith [hV.2.1]⟩

 

theorem replace_high (d : LSCMetric) (u₀ : ℝ) (hu₀ : |u₀| < 1 / 100)
    (hR : SideRemovable d u₀) (qT : ℚ) (hqT : (qT : ℝ) - u₀ < 1 / 3) (hqT' : 0 < (qT : ℝ) - u₀)
    (E F : ℚ × ℚ × ℚ × ℚ) {P : ℝ → ℂ} {s t : ℝ} (hP : d.IsCurve P s t)
    (hfin : d.len P s t ≠ ∞) (hsq : ∀ u ∈ Icc s t, P u ∈ unitSquare)
    (hhigh : ∀ u ∈ Icc s t, 1 / 3 < (P u).im)
    (hE : P s ∈ ratRect u₀ E) (hF : P t ∈ ratRect u₀ F) {η : ℝ} (hη : 0 < η) :
    ∃ (Q : ℝ → ℂ) (a b : ℝ), d.IsCurve Q a b ∧
      (∀ u ∈ Icc a b, Q u ∈ surgeryRegion) ∧
      Q a ∈ ratRect u₀ E ∧ Q b ∈ ratRect u₀ F ∧
      d.len Q a b < d.len P s t + ENNReal.ofReal η := by
  have hu := abs_lt.mp hu₀
  let V : ℚ × ℚ × ℚ × ℚ := (-1, 2, qT, 2)
  have hle : lowerPathInf d (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F) 1 ≤ d.len P s t := by
    unfold lowerPathInf
    apply compactPathInf_le_of_curve d _ _ _ P s t hP
    · intro u hu'
      have h := hsq u hu'
      have hh := hhigh u hu'
      refine ⟨?_, h.2.2.2⟩
      simp only [V, mem_ratRect_iff, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat]
      refine ⟨by linarith [h.1], by linarith [h.2.1], by linarith, by linarith [h.2.2.2]⟩
    · exact ⟨hE, (hsq s (left_mem_Icc.mpr hP.1)).2.2.2⟩
    · exact ⟨hF, (hsq t (right_mem_Icc.mpr hP.1)).2.2.2⟩
  have hlt : lowerPathInf d (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F) 1 <
      d.len P s t + ENNReal.ofReal η :=
    lt_of_le_of_lt hle (ENNReal.lt_add_right hfin (by simpa using hη))
  obtain ⟨Q, a, b, hQ, htr, ha, -, hb, -, hlen⟩ :=
    exists_lower_curve_of_continuousAt d _ _ _ (hR V E F).2 hlt
  refine ⟨Q, a, b, hQ, ?_, ha, hb, hlen⟩
  intro u hu'
  obtain ⟨hV, hlt1⟩ := htr u hu'
  simp only [V, mem_ratRect_iff, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at hV
  exact ⟨by linarith [hV.2.2.1], hlt1, by linarith [hV.1], by linarith [hV.2.1]⟩

 
theorem exists_loop_icurve {d : LSCMetric} (hGL : GoodLoops d) {P : ℝ → ℂ} {a b : ℝ}
    (hP : d.IsCurve P a b) (hb : Bornology.IsBounded (P '' Icc a b))
    (hfin : d.len P a b ≠ ∞) (hne : P a ≠ P b) {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ (c : ℂ) (r : ℝ) (L : ICurve d.Space), 0 < r ∧ 3 * r < ρ ∧ dist (P a) c < r ∧
      (∀ w ∈ ctr L, r < dist w c ∧ dist w c < 2 * r) ∧
      Disconnects (ctr L) (sphere c r) (sphere c (2 * r)) ∧ L.len < ENNReal.ofReal η := by
  obtain ⟨c, r, hr, h3r, hdist, L, s, t, hL, hLin, hLdis, hLlen⟩ :=
    hGL P a b hP hb hfin hne ρ η hρ hη
  refine ⟨c, r, toICurve d L s t hL, hr, h3r, hdist, ?_, hLdis, hLlen⟩
  rintro w ⟨u, hu, rfl⟩
  exact hLin u hu

 
theorem exists_loop_icurve_at_end {d : LSCMetric} (hGL : GoodLoops d) {P : ℝ → ℂ} {a b : ℝ}
    (hP : d.IsCurve P a b) (hb : Bornology.IsBounded (P '' Icc a b))
    (hfin : d.len P a b ≠ ∞) (hne : P a ≠ P b) {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ (c : ℂ) (r : ℝ) (L : ICurve d.Space), 0 < r ∧ 3 * r < ρ ∧ dist (P b) c < r ∧
      (∀ w ∈ ctr L, r < dist w c ∧ dist w c < 2 * r) ∧
      Disconnects (ctr L) (sphere c r) (sphere c (2 * r)) ∧ L.len < ENNReal.ofReal η := by
  let e := (toICurve d P a b hP).rev
  have he : d.IsCurve (fun t => (e.γ t : ℂ)) e.a e.b := icurve_isCurve d e
  have htr : (fun t => (e.γ t : ℂ)) '' Icc e.a e.b = P '' Icc a b := by
    rw [icurve_trace_eq, trace_rev]; rfl
  have hlen : d.len (fun t => (e.γ t : ℂ)) e.a e.b = d.len P a b := by
    rw [icurve_len_eq, len_rev]; rfl
  have hsrc : (fun t => (e.γ t : ℂ)) e.a = P b := by
    show P (a + b - a) = P b
    rw [add_sub_cancel_left]
  have htgt : (fun t => (e.γ t : ℂ)) e.b = P a := by
    show P (a + b - b) = P a
    rw [add_sub_cancel_right]
  have := exists_loop_icurve hGL he (htr ▸ hb) (hlen ▸ hfin)
    (show (fun t => (e.γ t : ℂ)) e.a ≠ (fun t => (e.γ t : ℂ)) e.b from by
      rw [hsrc, htgt]; exact hne.symm) hρ hη
  simpa only [hsrc] using this

 

theorem exists_sep_radius (A : Finset ℂ)
    (hA : ∀ z ∈ A, 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 3 ∧
      (∀ z ∈ A, 3 * ρ ≤ z.re ∧ 3 * ρ ≤ 1 - z.re ∧ 3 * ρ ≤ z.im ∧ 3 * ρ ≤ 1 - z.im) ∧
      (∀ z ∈ A, ∀ z' ∈ A, z ≠ z' → 3 * ρ ≤ dist z z') := by
  have hg : Tendsto (fun ρ : ℝ => 3 * ρ) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using h0.const_mul 3
  have hev : ∀ c : ℝ, 0 < c → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 3 * ρ ≤ c := fun c hc =>
    (hg.eventually (eventually_lt_nhds hc)).mono fun _ h => h.le
  have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ z ∈ A,
      3 * ρ ≤ z.re ∧ 3 * ρ ≤ 1 - z.re ∧ 3 * ρ ≤ z.im ∧ 3 * ρ ≤ 1 - z.im := by
    refine (Filter.eventually_all_finset A).2 fun z hz => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hA z hz
    exact (hev _ h1).and ((hev _ (by linarith)).and ((hev _ h3).and (hev _ (by linarith))))
  have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ p ∈ A ×ˢ A, p.1 ≠ p.2 → 3 * ρ ≤ dist p.1 p.2 := by
    refine (Filter.eventually_all_finset (A ×ˢ A)).2 fun p _ => ?_
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun _ h => absurd hp h
    · exact (hev _ (dist_pos.mpr hp)).mono fun _ h _ => h
  have h3 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ≤ 1 / 3 :=
    (hev 1 one_pos).mono fun _ h => by linarith
  obtain ⟨ρ, ⟨⟨hρ1, hρ2⟩, hρ3⟩, hρ0⟩ := ((h1.and h2).and h3).and self_mem_nhdsWithin |>.exists
  exact ⟨ρ, hρ0, hρ3, hρ1, fun z hz z' hz' hzz' => hρ2 (z, z') (Finset.mk_mem_product hz hz') hzz'⟩

 

theorem icurve_meets_loop (d : LSCMetric) (e L : ICurve d.Space) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : Bornology.IsBounded (ctr e))
    (hL : Disconnects (ctr L) (sphere c r) (sphere c (2 * r)))
    {x y : ℂ} (hx : x ∈ ctr e) (hy : y ∈ ctr e)
    (hxin : x ∈ closedBall c r) (hyout : y ∉ ball c (2 * r)) :
    (ctr L ∩ ctr e).Nonempty := by
  have hcont : ContinuousOn (cfun e) (Icc e.a e.b) :=
    Uniqueness.Toolkit.PathInfimum.continuousOn_euclidean_of_bounded d (cfun e)
      (cfun_isCurve e) hb
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact meets_of_crosses_annulus hr e.le hcont hL hu hv hxin hyout

 
theorem dist_lt_of_loop_disk {z c w : ℂ} {r ρ : ℝ} (hz : dist z c < r) (h3 : 3 * r < ρ)
    (hw : dist w c < 2 * r) : dist w z < ρ := by
  have := dist_triangle w c z
  rw [dist_comm c z] at this
  linarith

 
theorem sum_len_cuts (d : LSCMetric) (P : ℝ → ℂ) (τ : ℕ → ℝ) (m : ℕ)
    (hmono : ∀ j < m, τ j < τ (j + 1)) :
    ∀ k ≤ m, ∑ j ∈ Finset.range k, d.len P (τ j) (τ (j + 1)) = d.len P (τ 0) (τ k) := by
  have hle : ∀ k ≤ m, τ 0 ≤ τ k := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (ih (by omega)).trans (hmono k (by omega)).le
  intro k hk
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    symm
    simp [LSCMetric.len, Set.Icc_self, eVariationOn.subsingleton _ Set.subsingleton_singleton]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    exact (LQGMetric.MetricGeometry.curveLength_add (d.pt ∘ P) (hle k (by omega))
      (hmono k (by omega)).le)

theorem abs_re_sub_le_dist (w z : ℂ) : |w.re - z.re| ≤ dist w z := by
  rw [Complex.dist_eq, ← Complex.sub_re]; exact Complex.abs_re_le_norm _

theorem abs_im_sub_le_dist (w z : ℂ) : |w.im - z.im| ≤ dist w z := by
  rw [Complex.dist_eq, ← Complex.sub_im]; exact Complex.abs_im_le_norm _

end SupercriticalLQGUniqueness.B2.Median
