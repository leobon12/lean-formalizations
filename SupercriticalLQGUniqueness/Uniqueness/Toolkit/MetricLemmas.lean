import SupercriticalLQGUniqueness.Frozen.WeylScale
import LQGMetric.Metric.CurveLength
import LQGMetric.Topo.Disconnect
import LQGMetric.Topo.RectCross
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Analysis.Convex.PathConnected




 
set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness
namespace LSCMetric


theorem eq_of_euclidean_and_metric_limits (D : LSCMetric) {u : ℕ → ℂ} {w x : ℂ}
    (hw : Filter.Tendsto u Filter.atTop (nhds w))
    (hd : Filter.Tendsto (fun n => (D.pt (u n))) Filter.atTop (nhds (D.pt x))) : w = x := by
  have hd0 : Filter.Tendsto (fun n => D (u n, x)) Filter.atTop (nhds 0) := by
    exact (tendsto_iff_edist_tendsto_0).mp hd
  have hpair : Filter.Tendsto (fun n => ((u n, x), D (u n, x))) Filter.atTop
      (nhds ((w, x), (0 : ENNReal))) := (hw.prodMk_nhds tendsto_const_nhds).prodMk_nhds hd0
  have hle : D (w, x) ≤ 0 :=
    D.lowerSemicontinuous.isClosed_epigraph.mem_of_tendsto hpair
      (Filter.Eventually.of_forall fun n => (show D (u n, x) ≤ D (u n, x) from le_rfl))
  exact D.isExtMetric.2.1 w x (le_zero_iff.mp hle)


theorem continuousOn_euclidean_of_bounded (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) (hbounded : Bornology.IsBounded (P '' Icc a b)) :
    ContinuousOn P (Icc a b) := by
  obtain ⟨R, hR⟩ := hbounded.subset_ball 0
  intro t ht
  change Filter.Tendsto P (nhdsWithin t (Icc a b)) (nhds (P t))
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hseq : ∀ᶠ n in Filter.atTop, P (ns n) ∈ Metric.closedBall 0 R := by
    filter_upwards [hns.eventually (self_mem_nhdsWithin)] with n hn
    exact Metric.ball_subset_closedBall (hR ⟨ns n, hn, rfl⟩)
  obtain ⟨w, hwK, φ, hφ, hw⟩ :=
    (isCompact_closedBall (0 : ℂ) R).tendsto_subseq' hseq.frequently
  refine ⟨φ, ?_⟩
  have hnsφ : Filter.Tendsto (ns ∘ φ) Filter.atTop (nhdsWithin t (Icc a b)) :=
    hns.comp hφ.tendsto_atTop
  have hD : Filter.Tendsto (fun n => D.pt (P (ns (φ n)))) Filter.atTop
      (nhds (D.pt (P t))) := by
    have hDwithin : Filter.Tendsto (D.pt ∘ P) (nhdsWithin t (Icc a b))
        (nhds (D.pt (P t))) := hP.2 t ht
    exact hDwithin.comp hnsφ
  have hweq : w = P t := D.eq_of_euclidean_and_metric_limits hw hD
  change Filter.Tendsto (fun n => P (ns (φ n))) Filter.atTop (nhds w) at hw
  simpa only [hweq] using hw


theorem compact_separated_pairs_pos (D : LSCMetric) {K : Set ℂ}
    (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hne : ({p : ℂ × ℂ | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ dist p.1 p.2}).Nonempty) :
    ∃ c : ENNReal, 0 < c ∧ ∀ p : ℂ × ℂ,
      p.1 ∈ K → p.2 ∈ K → δ ≤ dist p.1 p.2 → c ≤ D p := by
  let S : Set (ℂ × ℂ) := {p | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ dist p.1 p.2}
  have hS : IsCompact S := by
    have hclosed : IsClosed {p : ℂ × ℂ | δ ≤ dist p.1 p.2} := by
      exact isClosed_le continuous_const continuous_dist
    have hSeq : S = (K ×ˢ K) ∩ {p : ℂ × ℂ | δ ≤ dist p.1 p.2} := by
      ext p
      simp only [S, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod]
      tauto
    rw [hSeq]
    exact (hK.prod hK).inter_right hclosed
  obtain ⟨p, hp, hmin⟩ :=
    (D.lowerSemicontinuous.lowerSemicontinuousOn S).exists_isMinOn hne hS
  have hpne : p.1 ≠ p.2 := by
    intro heq
    have hsep : δ ≤ dist p.1 p.2 := hp.2.2
    rw [heq, dist_self] at hsep
    linarith
  have hDp : D p ≠ 0 := by
    intro hz
    exact hpne (D.isExtMetric.2.1 p.1 p.2 hz)
  refine ⟨D p, pos_iff_ne_zero.mpr hDp, ?_⟩
  intro q hq1 hq2 hqδ
  exact hmin ⟨hq1, hq2, hqδ⟩

theorem internal_le_len (D : LSCMetric) (Y : Set ℂ) (P : ℝ → ℂ) (a b : ℝ)
    (hP : D.IsCurve P a b) (hY : ∀ t ∈ Icc a b, P t ∈ Y) :
    D.internal Y (⟨P a, hY a ⟨le_rfl, hP.1⟩⟩,
      ⟨P b, hY b ⟨hP.1, le_rfl⟩⟩) ≤ D.len P a b := by
  unfold internal
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le hY <|
      iInf_le_of_le rfl <| iInf_le_of_le rfl le_rfl

theorem edist_le_len (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    D (P a, P b) ≤ D.len P a b := by
  exact LQGMetric.MetricGeometry.edist_le_curveLength (D.pt ∘ P) hab

theorem edist_le_internal (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) :
    D ((p.1 : ℂ), (p.2 : ℂ)) ≤ D.internal Y p := by
  unfold internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hY => le_iInf fun ha => le_iInf fun hb => ?_
  rw [← ha, ← hb]
  exact D.edist_le_len P hP.1


theorem sum_len_le_len (D : LSCMetric) (P : ℝ → ℂ) (a : ℝ)
    (σ τ : ℕ → ℝ) (hstart : a ≤ σ 0)
    (hseg : ∀ i, σ i ≤ τ i) (hsep : ∀ i, τ i ≤ σ (i + 1)) :
    ∀ (n : ℕ) (b : ℝ), (∀ i < n, τ i ≤ b) →
      (∑ i ∈ Finset.range n, D.len P (σ i) (τ i)) ≤ D.len P a b := by
  have hσmono : Monotone σ := monotone_nat_of_le_succ (fun i => (hseg i).trans (hsep i))
  intro n
  induction n with
  | zero =>
      intro b _
      simp only [Finset.sum_range_zero]
      exact bot_le
  | succ n ih =>
      intro b hb
      have hprev : ∀ i < n, τ i ≤ σ n := by
        intro i hi
        exact (hsep i).trans (hσmono (by omega))
      have han : a ≤ σ n := hstart.trans (hσmono (Nat.zero_le n))
      calc
        (∑ i ∈ Finset.range (n+1), D.len P (σ i) (τ i))
            = (∑ i ∈ Finset.range n, D.len P (σ i) (τ i)) + D.len P (σ n) (τ n) := by
                rw [Finset.sum_range_succ]
        _ ≤ D.len P a (σ n) + D.len P (σ n) (τ n) := add_le_add (ih (σ n) hprev) le_rfl
        _ = D.len P a (τ n) := by
            exact LQGMetric.MetricGeometry.curveLength_add (D.pt ∘ P) han (hseg n)
        _ ≤ D.len P a b := by
            exact LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P) le_rfl
              (hb n (Nat.lt_succ_self n))

end LSCMetric



theorem crossing_extract {P : ℝ → ℂ} {a b r R : ℝ} {z : ℂ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hrR : r < R) (ha : dist (P a) z < r) (hb : R < dist (P b) z) :
    ∃ σ τ : ℝ, a ≤ σ ∧ σ < τ ∧ τ ≤ b ∧ dist (P σ) z = r ∧
      dist (P τ) z = R ∧ ∀ u ∈ Icc σ τ, dist (P u) z ∈ Icc r R := by
  have hf : ContinuousOn (fun t => dist (P t) z) (Icc a b) := continuous_dist.comp_continuousOn (hP.prodMk continuousOn_const)
  obtain ⟨σ, τ, hασ, hστ, hτβ, hσ, hτ, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hab hf hrR.le ha.le hb.le
  refine ⟨σ, τ, hασ, ?_, hτβ, hσ, hτ, hbetween⟩
  exact lt_of_le_of_ne hστ (by
    intro heq
    have : r = R := by rw [← hσ, ← hτ, heq]
    exact hrR.ne this)

theorem crossing_extract_reverse {P : ℝ → ℂ} {a b r R : ℝ} {z : ℂ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hrR : r < R) (ha : R < dist (P a) z) (hb : dist (P b) z < r) :
    ∃ σ τ : ℝ, a ≤ σ ∧ σ < τ ∧ τ ≤ b ∧ dist (P σ) z = R ∧
      dist (P τ) z = r ∧ ∀ u ∈ Icc σ τ, dist (P u) z ∈ Icc r R := by
  have hf : ContinuousOn (fun t => dist (P t) z) (Icc a b) := continuous_dist.comp_continuousOn (hP.prodMk continuousOn_const)
  obtain ⟨σ, τ, hασ, hστ, hτβ, hσ, hτ, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing' hab hf hrR.le ha.le hb.le
  refine ⟨σ, τ, hασ, ?_, hτβ, hσ, hτ, hbetween⟩
  exact lt_of_le_of_ne hστ (by
    intro heq
    have : R = r := by rw [← hσ, ← hτ, heq]
    exact hrR.ne this.symm)

theorem acrossDist_le_internal (D : LSCMetric) (A : EuclideanAnnulus)
    (U : Set ℂ) (x y : ℂ) (hxA : x ∈ A.innerBoundary)
    (hyA : y ∈ A.outerBoundary) (hxU : x ∈ U) (hyU : y ∈ U) :
    acrossDist D A ≤ D.internal U (⟨x, hxU⟩, ⟨y, hyU⟩) := by
  calc
    acrossDist D A ≤ D (x, y) := by
      unfold acrossDist
      exact iInf_le_of_le x <| iInf_le_of_le hxA <|
        iInf_le_of_le y <| iInf_le_of_le hyA le_rfl
    _ ≤ D.internal U (⟨x, hxU⟩, ⟨y, hyU⟩) :=
      D.edist_le_internal U (⟨x, hxU⟩, ⟨y, hyU⟩)

theorem disconnects_implies_path_disconnects {K E F : Set ℂ}
    (h : Disconnects K E F) : LQGMetric.Disconnects K E F := by
  intro x y γ hx hy
  by_contra hdisj
  apply h
  refine ⟨Set.range γ, ?_, ?_, ?_, ?_⟩
  · exact isPreconnected_range γ.continuous
  · intro z hz hzK
    exact hdisj ⟨z, hz, hzK⟩
  · exact ⟨x, ⟨⟨0, by simp⟩, by simp⟩, hx⟩
  · exact ⟨y, ⟨⟨1, by simp⟩, by simp⟩, hy⟩




theorem radial_segment_formula (z u : ℂ) (r R : ℝ) (t : unitInterval) :
    Path.segment (z + r • u) (z + R • u) t = z + (r + (t : ℝ) * (R - r)) • u := by
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module']
  module

theorem disconnects_meets_radial_segment {K : Set ℂ} {z u : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hu : ‖u‖ = 1)
    (hK : Disconnects K (Metric.sphere z r) (Metric.sphere z R)) :
    ∃ t : unitInterval, Path.segment (z + r • u) (z + R • u) t ∈ K := by
  have hx : z + r • u ∈ Metric.sphere z r := by
    simp [hu, Real.norm_eq_abs,
      abs_of_nonneg hr]
  have hy : z + R • u ∈ Metric.sphere z R := by
    have hR : 0 ≤ R := hr.trans hrR
    simp [hu, Real.norm_eq_abs,
      abs_of_nonneg hR]
  obtain ⟨w, ⟨t, rfl⟩, hwK⟩ :=
    disconnects_implies_path_disconnects hK _ _
      (Path.segment (z + r • u) (z + R • u)) hx hy
  exact ⟨t, hwK⟩


theorem dist_opposite_radial (z : ℂ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dist (z + s • (1 : ℂ)) (z + t • (-1 : ℂ)) = s + t := by
  calc
    dist (z + s • (1 : ℂ)) (z + t • (-1 : ℂ)) = ‖((s + t : ℝ) : ℂ)‖ := by
      rw [dist_eq_norm]
      congr 1
      simp only [Complex.real_smul, mul_one, mul_neg]
      push_cast
      ring
    _ = s + t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (add_nonneg hs ht)]


theorem disconnects_has_opposite_points {K : Set ℂ} {z : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hK : Disconnects K (Metric.sphere z r) (Metric.sphere z R)) :
    ∃ x ∈ K, ∃ y ∈ K, 2 * r ≤ dist x y := by
  obtain ⟨t₁, ht₁K⟩ :=
    disconnects_meets_radial_segment hr hrR (u := (1 : ℂ)) (by simp) hK
  obtain ⟨t₂, ht₂K⟩ :=
    disconnects_meets_radial_segment hr hrR (u := (-1 : ℂ)) (by simp) hK
  let s₁ : ℝ := r + (t₁ : ℝ) * (R - r)
  let s₂ : ℝ := r + (t₂ : ℝ) * (R - r)
  have hs₁ : r ≤ s₁ := by
    have hd : 0 ≤ R - r := sub_nonneg.mpr hrR
    have ht : 0 ≤ (t₁ : ℝ) := t₁.property.1
    exact le_add_of_nonneg_right (mul_nonneg ht hd)
  have hs₂ : r ≤ s₂ := by
    have hd : 0 ≤ R - r := sub_nonneg.mpr hrR
    have ht : 0 ≤ (t₂ : ℝ) := t₂.property.1
    exact le_add_of_nonneg_right (mul_nonneg ht hd)
  refine ⟨z + s₁ • (1 : ℂ), ?_, z + s₂ • (-1 : ℂ), ?_, ?_⟩
  · rw [← radial_segment_formula]
    exact ht₁K
  · rw [← radial_segment_formula]
    exact ht₂K
  · rw [dist_opposite_radial z (hr.trans hs₁) (hr.trans hs₂)]
    linarith


theorem dist_real_translate (z : ℂ) (s : ℝ) :
    dist (z + s • (1 : ℂ)) z = |s| := by
  rw [dist_eq_norm, add_sub_cancel_left]
  rw [Complex.real_smul, mul_one, Complex.norm_real, Real.norm_eq_abs]


theorem disconnects_meets_pathConnected_crossing {K X : Set ℂ} {z : ℂ} {r R : ℝ}
    (hrR : r ≤ R) (hK : Disconnects K (Metric.sphere z r) (Metric.sphere z R))
    (hX : IsPathConnected X)
    (hin : (X ∩ Metric.closedBall z r).Nonempty)
    (hout : (X ∩ (Metric.ball z R)ᶜ).Nonempty) : (K ∩ X).Nonempty := by
  obtain ⟨x, hxX, hxr⟩ := hin
  obtain ⟨y, hyX, hyR⟩ := hout
  let γ := (hX.joinedIn x hxX y hyX).somePath
  have hγX : Set.range γ ⊆ X := by
    rintro w ⟨t, rfl⟩
    exact (hX.joinedIn x hxX y hyX).somePath_mem t
  obtain ⟨w, hwγ, hwK⟩ :=
    (LQGMetric.Disconnects.closedBall_compl_ball hrR
      (disconnects_implies_path_disconnects hK)) x y γ hxr hyR
  exact ⟨w, hwK, hγX hwγ⟩

theorem disconnects_small_chain {S S' : Set ℂ} {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : Disconnects S (Metric.sphere z ρ) (Metric.sphere z (2 * ρ)))
    (hS' : Disconnects S'
      (Metric.sphere (z + (3 / 2 * ρ) • (1 : ℂ)) ρ)
      (Metric.sphere (z + (3 / 2 * ρ) • (1 : ℂ)) (2 * ρ)))
    (hpc : IsPathConnected S') : (S ∩ S').Nonempty := by
  let z' : ℂ := z + (3 / 2 * ρ) • (1 : ℂ)
  have hρ2 : ρ ≤ 2 * ρ := by linarith
  obtain ⟨tL, htL⟩ :=
    disconnects_meets_radial_segment hρ.le hρ2 (u := (-1 : ℂ)) (by simp) hS'
  obtain ⟨tR, htR⟩ :=
    disconnects_meets_radial_segment hρ.le hρ2 (u := (1 : ℂ)) (by simp) hS'
  let sL : ℝ := ρ + (tL : ℝ) * ρ
  let sR : ℝ := ρ + (tR : ℝ) * ρ
  have hsL : ρ ≤ sL ∧ sL ≤ 2 * ρ := by
    dsimp [sL]
    have ht := tL.property
    constructor <;> nlinarith [mul_nonneg ht.1 hρ.le,
      mul_nonneg (sub_nonneg.mpr ht.2) hρ.le]
  have hsR : ρ ≤ sR ∧ sR ≤ 2 * ρ := by
    dsimp [sR]
    have ht := tR.property
    constructor <;> nlinarith [mul_nonneg ht.1 hρ.le,
      mul_nonneg (sub_nonneg.mpr ht.2) hρ.le]
  have hleft_eq : Path.segment (z' + ρ • (-1 : ℂ)) (z' + (2 * ρ) • (-1 : ℂ)) tL =
      z + (3 / 2 * ρ - sL) • (1 : ℂ) := by
    rw [radial_segment_formula]
    dsimp [z', sL]
    simp only [mul_one, mul_neg]
    push_cast
    ring
  have hright_eq : Path.segment (z' + ρ • (1 : ℂ)) (z' + (2 * ρ) • (1 : ℂ)) tR =
      z + (3 / 2 * ρ + sR) • (1 : ℂ) := by
    rw [radial_segment_formula]
    dsimp [z', sR]
    simp only [mul_one]
    push_cast
    ring
  have hleft : (S' ∩ Metric.closedBall z ρ).Nonempty := by
    refine ⟨z + (3 / 2 * ρ - sL) • (1 : ℂ), ?_, ?_⟩
    · rw [← hleft_eq]
      exact htL
    · change dist (z + (3 / 2 * ρ - sL) • (1 : ℂ)) z ≤ ρ
      rw [dist_real_translate]
      exact abs_le.mpr ⟨by linarith [hsL.2], by linarith [hsL.1]⟩
  have hright : (S' ∩ (Metric.ball z (2 * ρ))ᶜ).Nonempty := by
    refine ⟨z + (3 / 2 * ρ + sR) • (1 : ℂ), ?_, ?_⟩
    · rw [← hright_eq]
      exact htR
    · change ¬ dist (z + (3 / 2 * ρ + sR) • (1 : ℂ)) z < 2 * ρ
      rw [dist_real_translate, abs_of_nonneg (by linarith [hsR.1])]
      linarith [hsR.1]
  exact disconnects_meets_pathConnected_crossing hρ2 hS hpc hleft hright



theorem pathConnected_finite_chain (S : ℕ → Set ℂ)
    (n : ℕ) (hpc : ∀ i ≤ n, IsPathConnected (S i))
    (hmeet : ∀ i < n, (S i ∩ S (i + 1)).Nonempty) :
    IsPathConnected (⋃ i ∈ Finset.range (n + 1), S i) := by
  induction n with
  | zero => simpa using hpc 0 (by omega)
  | succ n ih =>
      have hUnion : (⋃ i ∈ Finset.range (n + 2), S i) =
          (⋃ i ∈ Finset.range (n + 1), S i) ∪ S (n + 1) := by
        ext x
        simp only [show n + 2 = (n + 1) + 1 by omega, Finset.range_add_one,
          Finset.mem_insert, Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨i, (rfl | hi), hxi⟩
          · exact Or.inr hxi
          · exact Or.inl ⟨i, hi, hxi⟩
        · rintro (⟨i, hi, hxi⟩ | hxi)
          · exact ⟨i, Or.inr hi, hxi⟩
          · exact ⟨n + 1, Or.inl rfl, hxi⟩
      rw [hUnion]
      have hpc' : ∀ i ≤ n, IsPathConnected (S i) :=
        fun i hi => hpc i (by omega)
      have hmeet' : ∀ i < n, (S i ∩ S (i + 1)).Nonempty :=
        fun i hi => hmeet i (by omega)
      refine (ih hpc' hmeet').union (hpc (n + 1) (by omega)) ?_
      obtain ⟨x, hx, hx'⟩ := hmeet n (by omega)
      refine ⟨x, ?_, hx'⟩
      exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2
        ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), hx⟩⟩

theorem eleven_small_trace_chain (S : ℕ → Set ℂ)
    (hdisc : ∀ j ≤ 10, Disconnects (S j)
      (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (1 / 15 : ℝ))
      (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (2 / 15 : ℝ)))
    (hpc : ∀ j ≤ 10, IsPathConnected (S j)) :
    IsPathConnected (⋃ j ∈ Finset.range 11, S j) := by
  apply pathConnected_finite_chain S 10 hpc
  intro j hj
  have hc : (((1 + ((j + 1 : ℕ) : ℝ) / 10 : ℝ) : ℂ)) =
      (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) +
        (3 / 2 * (1 / 15 : ℝ)) • (1 : ℂ) := by
    simp only [Nat.cast_add, Nat.cast_one, Complex.real_smul, mul_one]
    push_cast
    ring
  have hj := hdisc j (by omega)
  have hj1 := hdisc (j + 1) (by omega)
  rw [hc] at hj1
  rw [show (2 / 15 : ℝ) = 2 * (1 / 15 : ℝ) by ring] at hj hj1
  exact disconnects_small_chain (by norm_num : (0 : ℝ) < 1 / 15) hj hj1
    (hpc (j + 1) (by omega))

theorem first_small_trace_inside {S : Set ℂ}
    (hS : Disconnects S (Metric.sphere (1 : ℂ) (1 / 15 : ℝ))
      (Metric.sphere (1 : ℂ) (2 / 15 : ℝ))) :
    (S ∩ Metric.closedBall (0 : ℂ) 1).Nonempty := by
  obtain ⟨t, ht⟩ := disconnects_meets_radial_segment
    (by norm_num : (0 : ℝ) ≤ 1 / 15)
    (by norm_num : (1 / 15 : ℝ) ≤ 2 / 15)
    (u := (-1 : ℂ)) (by simp) hS
  refine ⟨Path.segment ((1 : ℂ) + (1 / 15 : ℝ) • (-1 : ℂ))
    ((1 : ℂ) + (2 / 15 : ℝ) • (-1 : ℂ)) t, ht, ?_⟩
  change dist _ 0 ≤ 1
  rw [radial_segment_formula]
  have heq : (1 : ℂ) + ((1 / 15 : ℝ) + (t : ℝ) * (2 / 15 - 1 / 15)) • (-1 : ℂ) =
      (((1 - (1 / 15 + (t : ℝ) / 15)) : ℝ) : ℂ) := by
    simp only [Complex.real_smul, mul_neg]
    push_cast
    ring
  rw [heq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by nlinarith [t.property.2], by nlinarith [t.property.1]⟩

theorem last_small_trace_outside {S : Set ℂ}
    (hS : Disconnects S (Metric.sphere (2 : ℂ) (1 / 15 : ℝ))
      (Metric.sphere (2 : ℂ) (2 / 15 : ℝ))) :
    (S ∩ (Metric.ball (0 : ℂ) 2)ᶜ).Nonempty := by
  obtain ⟨t, ht⟩ := disconnects_meets_radial_segment
    (by norm_num : (0 : ℝ) ≤ 1 / 15)
    (by norm_num : (1 / 15 : ℝ) ≤ 2 / 15)
    (u := (1 : ℂ)) (by simp) hS
  refine ⟨Path.segment ((2 : ℂ) + (1 / 15 : ℝ) • (1 : ℂ))
    ((2 : ℂ) + (2 / 15 : ℝ) • (1 : ℂ)) t, ht, ?_⟩
  change ¬ dist _ 0 < 2
  rw [radial_segment_formula]
  have heq : (2 : ℂ) + ((1 / 15 : ℝ) + (t : ℝ) * (2 / 15 - 1 / 15)) • (1 : ℂ) =
      (((2 + (1 / 15 + (t : ℝ) / 15)) : ℝ) : ℂ) := by
    simp only [Complex.real_smul, mul_one]
    push_cast
    ring
  rw [heq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by nlinarith [t.property.1])]
  nlinarith [t.property.1]

theorem large_intersects_eleven_chain {K : Set ℂ} (S : ℕ → Set ℂ)
    (hK : Disconnects K (Metric.sphere (0 : ℂ) 1) (Metric.sphere (0 : ℂ) 2))
    (hdisc : ∀ j ≤ 10, Disconnects (S j)
      (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (1 / 15 : ℝ))
      (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (2 / 15 : ℝ)))
    (hpc : ∀ j ≤ 10, IsPathConnected (S j)) :
    (K ∩ (⋃ j ∈ Finset.range 11, S j)).Nonempty := by
  have hfirst : (S 0 ∩ Metric.closedBall (0 : ℂ) 1).Nonempty := by
    apply first_small_trace_inside
    simpa using hdisc 0 (by omega)
  have hlast : (S 10 ∩ (Metric.ball (0 : ℂ) 2)ᶜ).Nonempty := by
    apply last_small_trace_outside
    convert hdisc 10 (by omega) using 1 <;> norm_num
  have hin : ((⋃ j ∈ Finset.range 11, S j) ∩
      Metric.closedBall (0 : ℂ) 1).Nonempty := by
    obtain ⟨x, hxS, hxB⟩ := hfirst
    exact ⟨x, Set.mem_iUnion.2 ⟨0, Set.mem_iUnion.2
      ⟨Finset.mem_range.mpr (by omega), hxS⟩⟩, hxB⟩
  have hout : ((⋃ j ∈ Finset.range 11, S j) ∩
      (Metric.ball (0 : ℂ) 2)ᶜ).Nonempty := by
    obtain ⟨x, hxS, hxB⟩ := hlast
    exact ⟨x, Set.mem_iUnion.2 ⟨10, Set.mem_iUnion.2
      ⟨Finset.mem_range.mpr (by omega), hxS⟩⟩, hxB⟩
  exact disconnects_meets_pathConnected_crossing (by norm_num : (1 : ℝ) ≤ 2)
    hK (eleven_small_trace_chain S hdisc hpc) hin hout

end SupercriticalLQGUniqueness
