import SupercriticalLQGUniqueness.B2.Median.SurgeryParts

 
















set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal
open LQGMetric (leftSide rightSide)

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Toolkit.CompactPathInfimum
open Uniqueness.Objects.AnnulusTails
open Uniqueness.Objects.AnnulusTails.ICurve


theorem exists_strip_curve_of_surgery (d : LSCMetric) (u₀ : ℝ) (hu₀ : |u₀| < 1 / 100)
    (hR : SideRemovable d u₀) (hGL : GoodLoops d)
    (hZ : crossingInf d ≠ ∞) (η : ℝ) (hη : 0 < η) :
    ∃ (G : ℝ → ℂ) (a b : ℝ), d.IsCurve G a b ∧ (G a).re < 0 ∧ 1 < (G b).re ∧
      (∀ t ∈ Icc a b, G t ∈ surgeryRegion) ∧
      d.len G a b ≤ crossingInf d + ENNReal.ofReal η := by
  classical
  have hu := abs_lt.mp hu₀
  haveI : Nonempty (ICurve d.Space) := ⟨icurveConst (d.pt 0)⟩
  set η' : ℝ := η / 3 with hη'
  have hη'0 : 0 < η' := by positivity
  
  obtain ⟨P, a₀, b₀, hP₀, hK₀, hA₀, hB₀, hlen₀⟩ :=
    exists_curve_of_compactPathInf_lt d unitSquare leftSide rightSide
      (L := crossingInf d + ENNReal.ofReal η')
      (ENNReal.lt_add_right hZ (by simpa using hη'0))
  obtain ⟨a, b, -, hab, -, hP, hsq, hPa, hPb, hint, hlenab⟩ :=
    exists_normalized_square_crossing d hP₀ hK₀ hA₀ hB₀
  have hlenP : d.len P a b < crossingInf d + ENNReal.ofReal η' := lt_of_le_of_lt hlenab hlen₀
  have hfinP : d.len P a b ≠ ∞ := ne_top_of_lt hlenP
  have hsqc : IsCompact unitSquare := by
    change IsCompact LQGMetric.Blueprint.closedUnitSquare
    exact LQGMetric.DFGPS.isCompact_closedUnitSquare
  have hcont : ContinuousOn P (Icc a b) :=
    Uniqueness.Toolkit.PathInfimum.continuousOn_euclidean_of_compact_trace d P hP hsqc
      (fun z ⟨u, hu, huz⟩ => huz ▸ hsq u hu)
  
  obtain ⟨m, τ, hm, hτ0, hτm, hτmono, hτstrip, hτside⟩ :=
    exists_one_sided_cuts hab hcont (fun t ht => ⟨(hsq t ht).2.2.1, (hsq t ht).2.2.2⟩)
  have hτlt : ∀ i j, i < j → j ≤ m → τ i < τ j := by
    intro i j hij hjm
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact (ih h (by omega)).trans (hτmono j (by omega))
      · subst h; exact hτmono i (by omega)
  have hτmem : ∀ j ≤ m, τ j ∈ Icc a b := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; rw [hτ0]; exact left_mem_Icc.mpr hab.le
    · refine ⟨hτ0 ▸ (hτlt 0 j h hj).le, ?_⟩
      rcases lt_or_eq_of_le hj with h' | h'
      · exact hτm ▸ (hτlt j m h' le_rfl).le
      · rw [h', hτm]
  have hτint : ∀ j, 0 < j → j < m → τ j ∈ Ioo a b := fun j h0 hj =>
    ⟨hτ0 ▸ hτlt 0 j h0 hj.le, hτm ▸ hτlt j m hj le_rfl⟩
  
  let av : ℕ → ℂ := fun j => P (τ j)
  let A : Finset ℂ := (Finset.Ioo 0 m).image av
  have hAmem : ∀ z ∈ A, ∃ j, 0 < j ∧ j < m ∧ av j = z := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨j, (Finset.mem_Ioo.mp hj).1, (Finset.mem_Ioo.mp hj).2, rfl⟩
  have hav : ∀ j, 0 < j → j < m → av j ∈ A := fun j h0 hj =>
    Finset.mem_image.mpr ⟨j, Finset.mem_Ioo.mpr ⟨h0, hj⟩, rfl⟩
  have hAprop : ∀ z ∈ A, 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1 := by
    intro z hz
    obtain ⟨j, h0, hj, rfl⟩ := hAmem z hz
    obtain ⟨hr0, hr1⟩ := hint (τ j) (hτint j h0 hj)
    obtain ⟨hi0, hi1⟩ := hτstrip j h0 hj
    exact ⟨hr0, hr1, hi0, hi1⟩
  obtain ⟨ρ₀, hρ₀, hρ₀3, hρA, hρsep⟩ := exists_sep_radius A hAprop
  
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set ηR : ℝ := η' / m with hηR
  set ηL : ℝ := η' / (m + 1) with hηL
  have hηR0 : 0 < ηR := div_pos hη'0 hm'
  have hηL0 : 0 < ηL := div_pos hη'0 (by positivity)
  
  have hloopA : ∀ z ∈ A, ∃ (c : ℂ) (r : ℝ) (L : ICurve d.Space), 0 < r ∧ 3 * r < ρ₀ ∧
      dist z c < r ∧ (∀ w ∈ ctr L, r < dist w c ∧ dist w c < 2 * r) ∧
      Disconnects (ctr L) (sphere c r) (sphere c (2 * r)) ∧ L.len < ENNReal.ofReal ηL := by
    intro z hz
    obtain ⟨j, h0, hj, rfl⟩ := hAmem z hz
    have hjb := hτmem j hj.le
    have hPj : d.IsCurve P (τ j) b := ⟨hjb.2, hP.2.mono (Icc_subset_Icc hjb.1 le_rfl)⟩
    have hbdd : Bornology.IsBounded (P '' Icc (τ j) b) :=
      hsqc.isBounded.subset (fun w ⟨u, hu, huw⟩ => huw ▸ hsq u ⟨hjb.1.trans hu.1, hu.2⟩)
    have hfin : d.len P (τ j) b ≠ ∞ :=
      ne_top_of_le_ne_top hfinP (LQGMetric.MetricGeometry.curveLength_mono _ hjb.1 le_rfl)
    have hne : P (τ j) ≠ P b := by
      intro h
      have h1 := (hint (τ j) (hτint j h0 hj)).2
      rw [h, hPb.1] at h1
      exact lt_irrefl _ h1
    exact exists_loop_icurve hGL hPj hbdd hfin hne hρ₀ hηL0
  choose! cA rA LA hrA h3rA hdA hLinA hLdisA hLlenA using hloopA
  have hKA : ∀ z ∈ A, ∃ q : ℚ × ℚ × ℚ × ℚ, z ∈ ratRect u₀ q ∧
      ratRect u₀ q ⊆ ball (cA z) (rA z) :=
    fun z hz => exists_ratRect_mem_subset_ball u₀ (hdA z hz)
  choose! qK hqKmem hqKsub using hKA
  have hKball : ∀ z ∈ A, ∀ w ∈ ratRect u₀ (qK z), dist w z < ρ₀ := by
    intro z hz w hw
    have h1 := hqKsub z hz hw
    rw [mem_ball] at h1
    exact dist_lt_of_loop_disk (hdA z hz) (h3rA z hz) (by linarith [hrA z hz])
  have hLball : ∀ z ∈ A, ∀ w ∈ ctr (LA z), dist w z < ρ₀ := fun z hz w hw =>
    dist_lt_of_loop_disk (hdA z hz) (h3rA z hz) (hLinA z hz w hw).2
  have hnotLball : ∀ z ∈ A, ∀ w, ρ₀ ≤ dist w z → w ∉ ball (cA z) (2 * rA z) := by
    intro z hz w hw hb
    rw [mem_ball] at hb
    exact absurd (dist_lt_of_loop_disk (hdA z hz) (h3rA z hz) hb) (not_lt.mpr hw)
  
  obtain ⟨qB, hqB⟩ := exists_rat_btwn (show 2 / 3 + u₀ < 3 / 4 + u₀ by linarith)
  obtain ⟨qT, hqT⟩ := exists_rat_btwn (show 1 / 4 + u₀ < 1 / 3 + u₀ by linarith)
  let rL : ℚ × ℚ × ℚ × ℚ := (0, 0, -1, 2)
  let rR : ℚ × ℚ × ℚ × ℚ := (1, 1, -1, 2)
  have hrL : ∀ w, w ∈ ratRect u₀ rL ↔ w.re = 0 ∧ -1 - u₀ ≤ w.im ∧ w.im ≤ 2 - u₀ := by
    intro w
    simp only [rL, mem_ratRect_iff, Rat.cast_zero, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨le_antisymm h2 h1, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩; exact ⟨h1.ge, h1.le, h3, h4⟩
  have hrR : ∀ w, w ∈ ratRect u₀ rR ↔ w.re = 1 ∧ -1 - u₀ ≤ w.im ∧ w.im ≤ 2 - u₀ := by
    intro w
    simp only [rR, mem_ratRect_iff, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨le_antisymm h2 h1, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩; exact ⟨h1.ge, h1.le, h3, h4⟩
  let Ej : ℕ → ℚ × ℚ × ℚ × ℚ := fun j => if j = 0 then rL else qK (av j)
  let Fj : ℕ → ℚ × ℚ × ℚ × ℚ := fun j => if j + 1 = m then rR else qK (av (j + 1))
  have hEmem : ∀ j < m, P (τ j) ∈ ratRect u₀ (Ej j) := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      simp only [Ej, if_pos rfl]
      rw [hτ0, hrL]
      exact ⟨hPa.1, by linarith [hPa.2.1], by linarith [hPa.2.2]⟩
    · simp only [Ej, if_neg h0]
      exact hqKmem _ (hav j (Nat.pos_of_ne_zero h0) hj)
  have hFmem : ∀ j < m, P (τ (j + 1)) ∈ ratRect u₀ (Fj j) := by
    intro j hj
    by_cases h1 : j + 1 = m
    · simp only [Fj, if_pos h1]
      rw [h1, hτm, hrR]
      exact ⟨hPb.1, by linarith [hPb.2.1], by linarith [hPb.2.2]⟩
    · simp only [Fj, if_neg h1]
      exact hqKmem _ (hav (j + 1) (Nat.succ_pos j) (by omega))
  have hrep : ∀ j < m, ∃ Q : ICurve d.Space, (∀ w ∈ ctr Q, w ∈ surgeryRegion) ∧
      cfun Q Q.a ∈ ratRect u₀ (Ej j) ∧ cfun Q Q.b ∈ ratRect u₀ (Fj j) ∧
      Q.len < d.len P (τ j) (τ (j + 1)) + ENNReal.ofReal ηR := by
    intro j hj
    have hj0 := hτmem j hj.le
    have hj1 := hτmem (j + 1) hj
    have hPj : d.IsCurve P (τ j) (τ (j + 1)) :=
      ⟨(hτmono j hj).le, hP.2.mono (Icc_subset_Icc hj0.1 hj1.2)⟩
    have hfin : d.len P (τ j) (τ (j + 1)) ≠ ∞ :=
      ne_top_of_le_ne_top hfinP (LQGMetric.MetricGeometry.curveLength_mono _ hj0.1 hj1.2)
    have hsqj : ∀ u ∈ Icc (τ j) (τ (j + 1)), P u ∈ unitSquare :=
      fun u hu => hsq u ⟨hj0.1.trans hu.1, hu.2.trans hj1.2⟩
    rcases hτside j hj with hlow | hhigh
    · obtain ⟨Q, a', b', hQ, htr, ha', hb', hlen⟩ := replace_low d u₀ hu₀ hR qB
        (by linarith [hqB.1]) (by linarith [hqB.2]) (Ej j) (Fj j) hPj hfin hsqj hlow
        (hEmem j hj) (hFmem j hj) hηR0
      refine ⟨toICurve d Q a' b' hQ, ?_, ha', hb', hlen⟩
      rintro w ⟨u, hu, rfl⟩
      exact htr u hu
    · obtain ⟨Q, a', b', hQ, htr, ha', hb', hlen⟩ := replace_high d u₀ hu₀ hR qT
        (by linarith [hqT.2]) (by linarith [hqT.1]) (Ej j) (Fj j) hPj hfin hsqj hhigh
        (hEmem j hj) (hFmem j hj) hηR0
      refine ⟨toICurve d Q a' b' hQ, ?_, ha', hb', hlen⟩
      rintro w ⟨u, hu, rfl⟩
      exact htr u hu
  choose! Qp hQpR hQpE hQpF hQplen using hrep
  have hQpfin : ∀ j < m, (Qp j).len ≠ ∞ := fun j hj => ne_top_of_lt (hQplen j hj)
  
  have hm1 : m - 1 < m := Nat.sub_lt hm one_pos
  have hm1' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  set s₀ : ℂ := cfun (Qp 0) (Qp 0).a with hs₀
  set e₀ : ℂ := cfun (Qp (m - 1)) (Qp (m - 1)).b with he₀
  have hs₀L : s₀.re = 0 := by
    have h := hQpE 0 hm
    simp only [Ej, if_pos rfl] at h
    exact ((hrL _).mp h).1
  have he₀R : e₀.re = 1 := by
    have h := hQpF (m - 1) hm1
    simp only [Fj, if_pos hm1'] at h
    exact ((hrR _).mp h).1
  have hs₀mem : s₀ ∈ ctr (Qp 0) := ⟨(Qp 0).a, left_mem_Icc.mpr (Qp 0).le, rfl⟩
  have he₀mem : e₀ ∈ ctr (Qp (m - 1)) :=
    ⟨(Qp (m - 1)).b, right_mem_Icc.mpr (Qp (m - 1)).le, rfl⟩
  have hs₀R := hQpR 0 hm s₀ hs₀mem
  have he₀R' := hQpR (m - 1) hm1 e₀ he₀mem
  set ρL : ℝ := min ρ₀ (min s₀.im (1 - s₀.im)) with hρL
  have hρL0 : 0 < ρL := lt_min hρ₀ (lt_min hs₀R.1 (by linarith [hs₀R.2.1]))
  have hρLle : ρL ≤ ρ₀ := min_le_left _ _
  have hρLim : ρL ≤ s₀.im ∧ ρL ≤ 1 - s₀.im :=
    ⟨(min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  set ρE : ℝ := min ρ₀ (min e₀.im (1 - e₀.im)) with hρE
  have hρE0 : 0 < ρE := lt_min hρ₀ (lt_min he₀R'.1 (by linarith [he₀R'.2.1]))
  have hρEle : ρE ≤ ρ₀ := min_le_left _ _
  have hρEim : ρE ≤ e₀.im ∧ ρE ≤ 1 - e₀.im :=
    ⟨(min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hbddQ : ∀ j < m, Bornology.IsBounded (ctr (Qp j)) := fun j hj =>
    isBounded_surgeryRegion.subset (fun w hw => hQpR j hj w hw)
  
  have hKre : ∀ z ∈ A, ∀ w ∈ ratRect u₀ (qK z), 2 * ρ₀ < w.re ∧ w.re < 1 - 2 * ρ₀ := by
    intro z hz w hw
    have h1 := hKball z hz w hw
    have h2 := hρA z hz
    have h3 := abs_lt.mp (lt_of_le_of_lt (abs_re_sub_le_dist w z) h1)
    constructor <;> linarith [h2.1, h2.2.1, h3.1, h3.2]
  
  have hstart : ∀ j < m, 0 < j → cfun (Qp j) (Qp j).a ∈ ratRect u₀ (qK (av j)) := by
    intro j hj h0
    have h := hQpE j hj
    simpa only [Ej, if_neg (Nat.pos_iff_ne_zero.mp h0)] using h
  have hend : ∀ j < m, j + 1 < m → cfun (Qp j) (Qp j).b ∈ ratRect u₀ (qK (av (j + 1))) := by
    intro j hj h1
    have h := hQpF j hj
    simpa only [Fj, if_neg (Nat.ne_of_lt h1)] using h
  have hendR : ∀ j < m, j + 1 = m → (cfun (Qp j) (Qp j).b).re = 1 := by
    intro j hj h1
    have h := hQpF j hj
    simp only [Fj, if_pos h1] at h
    exact ((hrR _).mp h).1
  have hstartL : (cfun (Qp 0) (Qp 0).a).re = 0 := hs₀L
  
  have hfin0 : d.len (cfun (Qp 0)) (Qp 0).a (Qp 0).b ≠ ∞ := hQpfin 0 hm
  have hne0 : cfun (Qp 0) (Qp 0).a ≠ cfun (Qp 0) (Qp 0).b := by
    intro h
    by_cases h1 : 0 + 1 = m
    · have := hendR 0 hm h1; rw [← h, hstartL] at this; norm_num at this
    · have h2 := (hKre _ (hav 1 one_pos (by omega)) _ (hend 0 hm (by omega))).1
      rw [← h, hstartL] at h2; linarith
  obtain ⟨c₀, r₀, L₀, hr₀, h3r₀, hd₀, hL₀in, hL₀dis, hL₀len⟩ :=
    exists_loop_icurve hGL (cfun_isCurve (Qp 0)) (hbddQ 0 hm) hfin0 hne0 hρL0 hηL0
  have hfinE : d.len (cfun (Qp (m - 1))) (Qp (m - 1)).a (Qp (m - 1)).b ≠ ∞ := hQpfin _ hm1
  have hneE : cfun (Qp (m - 1)) (Qp (m - 1)).a ≠ cfun (Qp (m - 1)) (Qp (m - 1)).b := by
    intro h
    have hE1 : (cfun (Qp (m - 1)) (Qp (m - 1)).b).re = 1 := hendR _ hm1 hm1'
    by_cases h0 : m - 1 = 0
    · have hs : (cfun (Qp (m - 1)) (Qp (m - 1)).a).re = 0 := by rw [h0]; exact hstartL
      rw [h, hE1] at hs; norm_num at hs
    · have h2 := (hKre _ (hav (m - 1) (Nat.pos_of_ne_zero h0) hm1) _
        (hstart (m - 1) hm1 (Nat.pos_of_ne_zero h0))).2
      rw [h, hE1] at h2; linarith
  obtain ⟨cE, rE, LE, hrE, h3rE, hdE, hLEin, hLEdis, hLElen⟩ :=
    exists_loop_icurve_at_end hGL (cfun_isCurve (Qp (m - 1))) (hbddQ _ hm1) hfinE hneE hρE0 hηL0
  obtain ⟨qL, hqLmem, hqLre, -, -⟩ :=
    exists_left_point_of_disconnects hr₀ hd₀ hL₀dis (fun q hq => (hL₀in q hq).1)
  obtain ⟨qR, hqRmem, hqRre, -, -⟩ :=
    exists_right_point_of_disconnects hrE hdE hLEdis (fun q hq => (hLEin q hq).1)
  
  let ℓ : ℕ → ICurve d.Space := fun j => if j = 0 then L₀ else if j = m then LE else LA (av j)
  let cℓ : ℕ → ℂ := fun j => if j = 0 then c₀ else if j = m then cE else cA (av j)
  let rℓ : ℕ → ℝ := fun j => if j = 0 then r₀ else if j = m then rE else rA (av j)
  have hℓ0 : ℓ 0 = L₀ := by simp [ℓ]
  have hℓm : ℓ m = LE := by simp [ℓ, Nat.pos_iff_ne_zero.mp hm]
  have hℓj : ∀ j, 0 < j → j < m → ℓ j = LA (av j) ∧ cℓ j = cA (av j) ∧ rℓ j = rA (av j) := by
    intro j h0 hj
    simp [ℓ, cℓ, rℓ, Nat.pos_iff_ne_zero.mp h0, Nat.ne_of_lt hj]
  have hcℓ0 : cℓ 0 = c₀ ∧ rℓ 0 = r₀ := by simp [cℓ, rℓ]
  have hcℓm : cℓ m = cE ∧ rℓ m = rE := by simp [cℓ, rℓ, Nat.pos_iff_ne_zero.mp hm]
  
  have hdis : ∀ j ≤ m, 0 < rℓ j ∧
      Disconnects (ctr (ℓ j)) (sphere (cℓ j) (rℓ j)) (sphere (cℓ j) (2 * rℓ j)) := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0; rw [hℓ0, hcℓ0.1, hcℓ0.2]; exact ⟨hr₀, hL₀dis⟩
    by_cases hjm : j = m
    · subst hjm; rw [hℓm, hcℓm.1, hcℓm.2]; exact ⟨hrE, hLEdis⟩
    obtain ⟨e1, e2, e3⟩ := hℓj j (Nat.pos_of_ne_zero h0) (by omega)
    rw [e1, e2, e3]
    have hz := hav j (Nat.pos_of_ne_zero h0) (by omega)
    exact ⟨hrA _ hz, hLdisA _ hz⟩
  have hℓlen : ∀ j ≤ m, (ℓ j).len < ENNReal.ofReal ηL := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0; rw [hℓ0]; exact hL₀len
    by_cases hjm : j = m
    · subst hjm; rw [hℓm]; exact hLElen
    rw [(hℓj j (Nat.pos_of_ne_zero h0) (by omega)).1]
    exact hLlenA _ (hav j (Nat.pos_of_ne_zero h0) (by omega))
  have hℓR : ∀ j ≤ m, ∀ w ∈ ctr (ℓ j), w ∈ surgeryRegion := by
    intro j hj w hw
    by_cases h0 : j = 0
    · subst h0
      rw [hℓ0] at hw
      have h1 := dist_lt_of_loop_disk hd₀ h3r₀ (hL₀in w hw).2
      have hre := abs_le.mp ((abs_re_sub_le_dist w s₀).trans h1.le)
      have him := abs_lt.mp (lt_of_le_of_lt (abs_im_sub_le_dist w s₀) h1)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hρLim.1, hρLim.2, hρLle, hρ₀3]
    by_cases hjm : j = m
    · subst hjm
      rw [hℓm] at hw
      have h1 := dist_lt_of_loop_disk hdE h3rE (hLEin w hw).2
      have hre := abs_le.mp ((abs_re_sub_le_dist w e₀).trans h1.le)
      have him := abs_lt.mp (lt_of_le_of_lt (abs_im_sub_le_dist w e₀) h1)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hρEim.1, hρEim.2, hρEle, hρ₀3]
    have hz := hav j (Nat.pos_of_ne_zero h0) (by omega)
    rw [(hℓj j (Nat.pos_of_ne_zero h0) (by omega)).1] at hw
    have h1 := hLball _ hz w hw
    have h2 := hρA _ hz
    have hre := abs_le.mp ((abs_re_sub_le_dist w (av j)).trans h1.le)
    have him := abs_le.mp ((abs_im_sub_le_dist w (av j)).trans h1.le)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  
  let deg : ℕ → Prop := fun j => 0 < j ∧ j + 1 < m ∧ av j = av (j + 1)
  have hdeg : ∀ j < m, deg j → ℓ (j + 1) = ℓ j := by
    intro j hj ⟨h0, h1, h2⟩
    rw [(hℓj j h0 hj).1, (hℓj (j + 1) (Nat.succ_pos j) h1).1, h2]
  
  have hin_start : ∀ j < m, cfun (Qp j) (Qp j).a ∈ closedBall (cℓ j) (rℓ j) := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0; rw [hcℓ0.1, hcℓ0.2]; exact mem_closedBall.mpr hd₀.le
    obtain ⟨-, e2, e3⟩ := hℓj j (Nat.pos_of_ne_zero h0) hj
    rw [e2, e3]
    exact ball_subset_closedBall (hqKsub _ (hav j (Nat.pos_of_ne_zero h0) hj)
      (hstart j hj (Nat.pos_of_ne_zero h0)))
  have hin_end : ∀ j < m, cfun (Qp j) (Qp j).b ∈ closedBall (cℓ (j + 1)) (rℓ (j + 1)) := by
    intro j hj
    by_cases h1 : j + 1 = m
    · have hj' : j = m - 1 := by omega
      subst hj'
      rw [h1, hcℓm.1, hcℓm.2]; exact mem_closedBall.mpr hdE.le
    obtain ⟨-, e2, e3⟩ := hℓj (j + 1) (Nat.succ_pos j) (by omega)
    rw [e2, e3]
    exact ball_subset_closedBall (hqKsub _ (hav (j + 1) (Nat.succ_pos j) (by omega))
      (hend j hj (by omega)))
  have hout_end : ∀ j < m, ¬ deg j →
      cfun (Qp j) (Qp j).b ∉ ball (cℓ j) (2 * rℓ j) := by
    intro j hj hnd
    set y := cfun (Qp j) (Qp j).b
    by_cases h0 : j = 0
    · subst h0
      rw [hcℓ0.1, hcℓ0.2]
      intro hb
      have h1 := dist_lt_of_loop_disk hd₀ h3r₀ (mem_ball.mp hb)
      have hre := abs_lt.mp (lt_of_le_of_lt (abs_re_sub_le_dist y s₀) h1)
      by_cases hm0 : 0 + 1 = m
      · have := hendR 0 hj hm0; linarith [hre.2, hρLle, hρ₀3]
      · have := (hKre _ (hav 1 one_pos (by omega)) _ (hend 0 hj (by omega))).1
        linarith [hre.2]
    obtain ⟨-, e2, e3⟩ := hℓj j (Nat.pos_of_ne_zero h0) hj
    rw [e2, e3]
    have hz := hav j (Nat.pos_of_ne_zero h0) hj
    apply hnotLball _ hz
    by_cases h1 : j + 1 = m
    · have := hendR j hj h1
      have h2 := hρA _ hz
      have h3 := abs_re_sub_le_dist y (av j)
      rw [abs_of_nonneg (by linarith [h2.2.1])] at h3
      linarith [h2.2.1]
    · have hz' := hav (j + 1) (Nat.succ_pos j) (by omega)
      have hne : av j ≠ av (j + 1) := fun h => hnd ⟨Nat.pos_of_ne_zero h0, by omega, h⟩
      have h2 := hρsep _ hz _ hz' hne
      have h3 := hKball _ hz' y (hend j hj (by omega))
      have h4 := dist_triangle (av j) y (av (j + 1))
      rw [dist_comm (av j) y] at h4
      linarith
  have hout_start : ∀ j < m, ¬ deg j →
      cfun (Qp j) (Qp j).a ∉ ball (cℓ (j + 1)) (2 * rℓ (j + 1)) := by
    intro j hj hnd
    set x := cfun (Qp j) (Qp j).a
    by_cases h1 : j + 1 = m
    · rw [h1, hcℓm.1, hcℓm.2]
      intro hb
      have h2 := dist_lt_of_loop_disk hdE h3rE (mem_ball.mp hb)
      have hre := abs_lt.mp (lt_of_le_of_lt (abs_re_sub_le_dist x e₀) h2)
      by_cases h0 : j = 0
      · subst h0
        have : x.re = 0 := hstartL
        linarith [hre.1, hρEle, hρ₀3]
      · have := (hKre _ (hav j (Nat.pos_of_ne_zero h0) hj) _
          (hstart j hj (Nat.pos_of_ne_zero h0))).2
        linarith [hre.1]
    obtain ⟨-, e2, e3⟩ := hℓj (j + 1) (Nat.succ_pos j) (by omega)
    rw [e2, e3]
    have hz' := hav (j + 1) (Nat.succ_pos j) (by omega)
    apply hnotLball _ hz'
    by_cases h0 : j = 0
    · subst h0
      have hx : x.re = 0 := hstartL
      have h2 := hρA _ hz'
      have h3 := abs_re_sub_le_dist x (av (0 + 1))
      rw [hx, zero_sub, abs_neg, abs_of_nonneg (by linarith [h2.1])] at h3
      linarith [h2.1]
    · have hz := hav j (Nat.pos_of_ne_zero h0) hj
      have hne : av j ≠ av (j + 1) := fun h => hnd ⟨Nat.pos_of_ne_zero h0, by omega, h⟩
      have h2 := hρsep _ hz _ hz' hne
      have h3 := hKball _ hz x (hstart j hj (Nat.pos_of_ne_zero h0))
      have h4 := dist_triangle (av j) x (av (j + 1))
      rw [dist_comm (av j) x] at h4
      linarith
  have hmeet : ∀ j < m, ¬ deg j →
      ((ℓ j).trace ∩ (Qp j).trace).Nonempty ∧ ((Qp j).trace ∩ (ℓ (j + 1)).trace).Nonempty := by
    intro j hj hnd
    have hxQ : cfun (Qp j) (Qp j).a ∈ ctr (Qp j) := ⟨(Qp j).a, left_mem_Icc.mpr (Qp j).le, rfl⟩
    have hyQ : cfun (Qp j) (Qp j).b ∈ ctr (Qp j) := ⟨(Qp j).b, right_mem_Icc.mpr (Qp j).le, rfl⟩
    obtain ⟨hr1, hd1⟩ := hdis j hj.le
    obtain ⟨hr2, hd2⟩ := hdis (j + 1) hj
    have m1 := icurve_meets_loop d (Qp j) (ℓ j) hr1 (hbddQ j hj) hd1 hxQ hyQ
      (hin_start j hj) (hout_end j hj hnd)
    have m2 := icurve_meets_loop d (Qp j) (ℓ (j + 1)) hr2 (hbddQ j hj) hd2 hyQ hxQ
      (hin_end j hj) (hout_start j hj hnd)
    obtain ⟨w₁, hw₁⟩ := m1
    obtain ⟨w₂, hw₂⟩ := m2
    exact ⟨⟨w₁, hw₁.1, hw₁.2⟩, ⟨w₂, hw₂.2, hw₂.1⟩⟩
  have hqLℓ : (qL : d.Space) ∈ (ℓ 0).trace := by rw [hℓ0]; exact hqLmem
  have hqRℓ : (qR : d.Space) ∈ (ℓ m).trace := by rw [hℓm]; exact hqRmem
  obtain ⟨Γ, hΓs, hΓt, hΓR, hΓlen⟩ := icurve_exists_glued m ℓ Qp deg hdeg hmeet
    (surgeryRegion : Set ℂ) (fun j hj w hw => hℓR j hj w hw)
    (fun j hj w hw => hQpR j hj w hw) hqLℓ hqRℓ
  
  refine ⟨cfun Γ, Γ.a, Γ.b, cfun_isCurve Γ, ?_, ?_, ?_, ?_⟩
  · have h : cfun Γ Γ.a = qL := hΓs
    rw [h]; linarith
  · have h : cfun Γ Γ.b = qR := hΓt
    rw [h]; linarith
  · intro t ht
    exact hΓR ⟨t, ht, rfl⟩
  · rw [cfun_len]
    have hsumQ : ∑ j ∈ Finset.range m, (Qp j).len ≤ d.len P a b + ENNReal.ofReal η' := by
      calc ∑ j ∈ Finset.range m, (Qp j).len
          ≤ ∑ j ∈ Finset.range m, (d.len P (τ j) (τ (j + 1)) + ENNReal.ofReal ηR) :=
            Finset.sum_le_sum fun j hj => (hQplen j (Finset.mem_range.mp hj)).le
        _ = d.len P a b + ENNReal.ofReal η' := by
            rw [Finset.sum_add_distrib, sum_len_cuts d P τ m hτmono m le_rfl, hτ0, hτm,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            congr 1
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m), hηR,
              mul_div_cancel₀ η' (ne_of_gt hm')]
    have hsumL : ∑ j ∈ Finset.range (m + 1), (ℓ j).len ≤ ENNReal.ofReal η' := by
      calc ∑ j ∈ Finset.range (m + 1), (ℓ j).len
          ≤ ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal ηL :=
            Finset.sum_le_sum fun j hj =>
              (hℓlen j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).le
        _ = ENNReal.ofReal η' := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hηL]
            congr 1
            push_cast
            field_simp
    calc Γ.len ≤ ∑ j ∈ Finset.range m, (Qp j).len + ∑ j ∈ Finset.range (m + 1), (ℓ j).len :=
          hΓlen
      _ ≤ (d.len P a b + ENNReal.ofReal η') + ENNReal.ofReal η' := add_le_add hsumQ hsumL
      _ ≤ ((crossingInf d + ENNReal.ofReal η') + ENNReal.ofReal η') + ENNReal.ofReal η' :=
          add_le_add (add_le_add hlenP.le le_rfl) le_rfl
      _ = crossingInf d + ENNReal.ofReal η := by
          rw [add_assoc, add_assoc, ← ENNReal.ofReal_add hη'0.le hη'0.le,
            ← ENNReal.ofReal_add hη'0.le (by positivity)]
          congr 2
          rw [hη']; ring

end SupercriticalLQGUniqueness.B2.Median
