import SupercriticalLQGUniqueness.B2.PfeLocal.InputsL5

 


















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum Uniqueness.Toolkit.PathInfimum

theorem l5_compactPathInf_le (D : LSCMetric) {K E F : Set ℂ}
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (hK : ∀ t ∈ Icc a b, P t ∈ K) (hE : P a ∈ E) (hF : P b ∈ F) :
    compactPathInf D K E F ≤ D.len P a b :=
  iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le hK <|
    iInf_le_of_le hE <| iInf_le_of_le hF le_rfl

theorem l5_compactPathInf_anti (D : LSCMetric) (K : Set ℂ) {E E' F F' : Set ℂ}
    (hE : E ⊆ E') (hF : F ⊆ F') : compactPathInf D K E' F' ≤ compactPathInf D K E F := by
  unfold compactPathInf
  exact iInf_mono fun P => iInf_mono fun a => iInf_mono fun b => iInf_mono fun _ =>
    iInf_mono fun _ => iInf_mono' fun hEa => ⟨hE hEa, iInf_mono' fun hFb => ⟨hF hFb, le_rfl⟩⟩

 
theorem l5_compactPathInf_le_liminf (D : LSCMetric) {K : Set ℂ} (hK : IsCompact K)
    {x y : ℂ} (E F : ℕ → Set ℂ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hEx : ∀ n, E n ⊆ Metric.closedBall x (r n)) (hFy : ∀ n, F n ⊆ Metric.closedBall y (r n)) :
    compactPathInf D K {x} {y} ≤
      liminf (fun n => compactPathInf D K (E n) (F n)) atTop := by
  refine le_of_forall_lt fun v hv => ?_
  obtain ⟨w, hvw, hw⟩ := exists_between hv
  have hwfin : w ≠ ∞ := ne_top_of_lt hw
  have htail : ∀ᶠ n in atTop, w ≤ compactPathInf D K (E n) (F n) := by
    by_contra hn
    rw [not_eventually] at hn
    obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hn
    have hbad' : ∀ n, compactPathInf D K (E (φ n)) (F (φ n)) < w :=
      fun n => lt_of_not_ge (hbad n)
    have hpaths : ∀ n, ∃ (P : ℝ → ℂ) (a b : ℝ),
        D.IsCurve P a b ∧ (∀ t ∈ Icc a b, P t ∈ K) ∧ P a ∈ E (φ n) ∧ P b ∈ F (φ n) ∧
        D.len P a b < w := by
      intro n
      unfold compactPathInf at hbad'
      obtain ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩ :=
        (by simpa only [iInf_lt_iff] using hbad' n)
      exact ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩
    choose P a b hP htrace hEa hFb hlen using hpaths
    have hfin : ∀ n, D.len (P n) (a n) (b n) ≠ ∞ := fun n => ne_top_of_lt (hlen n)
    have htrace' : ∀ n, P n '' Icc (a n) (b n) ⊆ K := by
      intro n z hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact htrace n t ht
    choose γ hγlen hγtrace hγlip using fun n =>
      exists_lipschitz_reparam D (P n) (hP n) (hfin n) (htrace' n)
    let Q : ℕ → unitInterval → ℂ := fun n t => γ n t
    have hQtrace : ∀ n t, Q n t ∈ K := fun n t => hγtrace n t
    have hQ0 : ∀ n, Q n 0 = P n (a n) := fun n => by
      change (γ n 0 : ℂ) = _
      rw [(γ n).source]
      rfl
    have hQ1 : ∀ n, Q n 1 = P n (b n) := fun n => by
      change (γ n 1 : ℂ) = _
      rw [(γ n).target]
      rfl
    have hQlip : ∀ n, LipschitzWith w.toNNReal (D.pt ∘ Q n) := by
      intro n
      have hmono : (D.len (P n) (a n) (b n)).toNNReal ≤ w.toNNReal :=
        ENNReal.toNNReal_mono hwfin (hlen n).le
      exact (hγlip n).weaken hmono
    have hQbound : ∀ n, D.len (fun t => Q n (projIcc 0 1 zero_le_one t)) 0 1 ≤ w := by
      intro n
      change LQGMetric.MetricGeometry.pathLength (γ n) ≤ w
      exact (hγlen n).le.trans (hlen n).le
    have hconst : Tendsto (fun _ : ℕ => D) atTop (𝓝 D) := tendsto_const_nhds
    obtain ⟨ψ, P₀, hψ, hlim, htrace₀⟩ := compact_trace_path_subseq hconst hK hQtrace hQlip
    have hDlip : LipschitzWith w.toNNReal (D.pt ∘ P₀) :=
      lipschitz_limit_of_epi hconst hlim (fun n => hQlip (ψ n))
    have hcurve : D.IsCurve (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 :=
      ⟨zero_le_one, (hDlip.continuous.comp continuous_projIcc).continuousOn⟩
    have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
        Tendsto (fun n => Q (ψ n) (projIcc 0 1 zero_le_one t)) atTop
          (𝓝 (P₀ (projIcc 0 1 zero_le_one t))) :=
      fun t _ => hlim.tendsto_at (projIcc 0 1 zero_le_one t)
    have hlen₀ := joint_len_le_liminf hconst hpoint
    have hlen₁ : D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ w :=
      hlen₀.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => hQbound (ψ n)))
    
    have hrφ : Tendsto (fun n => r (φ (ψ n))) atTop (𝓝 0) :=
      hr.comp (hφ.comp hψ).tendsto_atTop
    have hend : ∀ (z : ℂ) (S : ℕ → Set ℂ) (s : unitInterval),
        (∀ n, S n ⊆ Metric.closedBall z (r n)) → (∀ n, Q (ψ n) s ∈ S (φ (ψ n))) →
        P₀ s = z := by
      intro z S s hS hmem
      have h1 : Tendsto (fun n => Q (ψ n) s) atTop (𝓝 (P₀ s)) := hlim.tendsto_at s
      have h2 : Tendsto (fun n => Q (ψ n) s) atTop (𝓝 z) := by
        rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hrφ
        exact Metric.mem_closedBall.1 (hS _ (hmem n))
      exact tendsto_nhds_unique h1 h2
    have hx₀ : P₀ 0 = x := hend x E 0 hEx fun n => by
      rw [hQ0]; exact hEa (ψ n)
    have hy₀ : P₀ 1 = y := hend y F 1 hFy fun n => by
      rw [hQ1]; exact hFb (ψ n)
    have hInf : compactPathInf D K {x} {y} ≤
        D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 := by
      apply l5_compactPathInf_le D _ 0 1 hcurve
      · intro t _
        exact htrace₀ _
      · simp only [projIcc_left, mem_singleton_iff]; exact hx₀
      · simp only [projIcc_right, mem_singleton_iff]; exact hy₀
    exact (not_le_of_gt hw) (hInf.trans hlen₁)
  exact hvw.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) htail)

 

theorem l5_exists_rat_near (a : ℝ) (n : ℕ) : ∃ q : ℚ, |a - q| ≤ 1 / (2 * ((n : ℝ) + 1)) := by
  have hpos : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show a - 1 / (2 * ((n : ℝ) + 1)) < a by linarith)
  exact ⟨q, by rw [abs_le]; constructor <;> linarith⟩

 
def l5RatNear (a : ℝ) (n : ℕ) : ℚ := Classical.choose (l5_exists_rat_near a n)

theorem l5RatNear_spec (a : ℝ) (n : ℕ) : |a - l5RatNear a n| ≤ 1 / (2 * ((n : ℝ) + 1)) :=
  Classical.choose_spec (l5_exists_rat_near a n)

 
def l5ApproxBall (x : ℂ) (n : ℕ) : ℚ × ℚ × ℚ :=
  (l5RatNear x.re n, l5RatNear x.im n, 1 / ((n : ℚ) + 1))

theorem l5ApproxBall_center_dist (x : ℂ) (n : ℕ) :
    dist x ⟨((l5ApproxBall x n).1 : ℝ), ((l5ApproxBall x n).2.1 : ℝ)⟩ ≤ 1 / ((n : ℝ) + 1) := by
  have h1 := l5RatNear_spec x.re n
  have h2 := l5RatNear_spec x.im n
  calc dist x ⟨((l5ApproxBall x n).1 : ℝ), ((l5ApproxBall x n).2.1 : ℝ)⟩
      ≤ |x.re - l5RatNear x.re n| + |x.im - l5RatNear x.im n| := by
        rw [Complex.dist_eq]
        exact Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) := add_le_add h1 h2
    _ = 1 / ((n : ℝ) + 1) := by field_simp; ring

theorem l5ApproxBall_radius (x : ℂ) (n : ℕ) :
    (((l5ApproxBall x n).2.2 : ℚ) : ℝ) = 1 / ((n : ℝ) + 1) := by
  show ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) = _
  push_cast
  ring

theorem mem_l5ApproxBall (x : ℂ) (n : ℕ) : x ∈ l5Ball (l5ApproxBall x n) := by
  rw [l5Ball, Metric.mem_closedBall, l5ApproxBall_radius]
  exact l5ApproxBall_center_dist x n

theorem l5ApproxBall_subset (x : ℂ) (n : ℕ) :
    l5Ball (l5ApproxBall x n) ⊆ Metric.closedBall x (2 / ((n : ℝ) + 1)) := by
  intro z hz
  rw [l5Ball, Metric.mem_closedBall, l5ApproxBall_radius] at hz
  rw [Metric.mem_closedBall]
  have := l5ApproxBall_center_dist x n
  calc dist z x ≤ dist z _ + dist _ x := dist_triangle z _ x
    _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_le_add hz (by rw [dist_comm]; exact this)
    _ = 2 / ((n : ℝ) + 1) := by ring

theorem l5_tendsto_two_div : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  ring

 

theorem l5_compactPathInf_eq_liminf (D : LSCMetric) (q : ℚ × ℚ × ℚ × ℚ) (x y : ℂ) :
    compactPathInf D (l5Rect q) {x} {y} =
      liminf (fun n => l5Obs D (q, l5ApproxBall x n, l5ApproxBall y n)) atTop := by
  apply le_antisymm
  · exact l5_compactPathInf_le_liminf D (l5Rect_isCompact q) _ _ _ l5_tendsto_two_div
      (fun n => l5ApproxBall_subset x n) (fun n => l5ApproxBall_subset y n)
  · refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
    exact l5_compactPathInf_anti D _ (singleton_subset_iff.2 (mem_l5ApproxBall x n))
      (singleton_subset_iff.2 (mem_l5ApproxBall y n))

 
theorem l5_compactPathInf_eq_of_enc_eq {S : Set ℂ} {D D' : LSCMetric}
    (henc : l5Enc S D = l5Enc S D') {q : ℚ × ℚ × ℚ × ℚ} (hq : l5Rect q ⊆ S) (x y : ℂ) :
    compactPathInf D (l5Rect q) {x} {y} = compactPathInf D' (l5Rect q) {x} {y} := by
  rw [l5_compactPathInf_eq_liminf, l5_compactPathInf_eq_liminf]
  congr 1
  funext n
  have h := congrFun henc (q, l5ApproxBall x n, l5ApproxBall y n)
  rwa [l5Enc_of_subset D hq, l5Enc_of_subset D' hq] at h

 

theorem l5_len_eq_iSup_compactPathInf (D : LSCMetric) {K : Set ℂ} (P : ℝ → ℂ) {s t : ℝ}
    (hP : D.IsCurve P s t) (hK : ∀ u ∈ Icc s t, P u ∈ K) :
    D.len P s t = ⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc s t},
      ∑ i ∈ Finset.range p.1, compactPathInf D K {P (p.2.1 i)} {P (p.2.1 (i + 1))} := by
  apply le_antisymm
  · unfold LSCMetric.len eVariationOn
    refine iSup_mono fun p => Finset.sum_le_sum fun i _ => ?_
    change D (P (p.2.1 (i + 1)), P (p.2.1 i)) ≤ _
    rw [D.isExtMetric.2.2.1]
    refine le_iInf fun Q => le_iInf fun a => le_iInf fun b => le_iInf fun hQ =>
      le_iInf fun _ => le_iInf fun ha => le_iInf fun hb => ?_
    rw [mem_singleton_iff] at ha hb
    rw [← ha, ← hb]
    exact LQGMetric.MetricGeometry.edist_le_curveLength (D.pt ∘ Q) hQ.1
  · refine iSup_le fun p => ?_
    obtain ⟨n, u, hu, hus⟩ := p
    have hstep : ∀ i, compactPathInf D K {P (u i)} {P (u (i + 1))} ≤
        eVariationOn (D.pt ∘ P) (Icc (u i) (u (i + 1))) := by
      intro i
      have hle : u i ≤ u (i + 1) := hu (Nat.le_succ i)
      refine l5_compactPathInf_le D P (u i) (u (i + 1))
        ⟨hle, hP.2.mono (Icc_subset_Icc (hus i).1 (hus (i + 1)).2)⟩ (fun v hv => ?_)
        rfl rfl
      exact hK v ⟨(hus i).1.trans hv.1, hv.2.trans (hus (i + 1)).2⟩
    have hsum : ∀ m, ∑ i ∈ Finset.range m, eVariationOn (D.pt ∘ P) (Icc (u i) (u (i + 1))) =
        eVariationOn (D.pt ∘ P) (Icc (u 0) (u m)) := by
      intro m
      induction m with
      | zero => simp [eVariationOn.subsingleton]
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have h1 : u 0 ≤ u m := hu (Nat.zero_le m)
        have h2 : u m ≤ u (m + 1) := hu (Nat.le_succ m)
        have := eVariationOn.Icc_add_Icc (D.pt ∘ P) (s := univ) h1 h2 (mem_univ _)
        simpa only [univ_inter] using this
    calc ∑ i ∈ Finset.range n, compactPathInf D K {P (u i)} {P (u (i + 1))}
        ≤ ∑ i ∈ Finset.range n, eVariationOn (D.pt ∘ P) (Icc (u i) (u (i + 1))) :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = eVariationOn (D.pt ∘ P) (Icc (u 0) (u n)) := hsum n
      _ ≤ D.len P s t :=
          eVariationOn.mono _ (Icc_subset_Icc (hus 0).1 (hus n).2)

 

theorem l5_len_eq_of_enc_eq {S : Set ℂ} {D D' : LSCMetric} (henc : l5Enc S D = l5Enc S D')
    {q : ℚ × ℚ × ℚ × ℚ} (hq : l5Rect q ⊆ S) (P : ℝ → ℂ) {s t : ℝ}
    (hP : D.IsCurve P s t) (hP' : D'.IsCurve P s t) (hK : ∀ u ∈ Icc s t, P u ∈ l5Rect q) :
    D.len P s t = D'.len P s t := by
  rw [l5_len_eq_iSup_compactPathInf D P hP hK, l5_len_eq_iSup_compactPathInf D' P hP' hK]
  congr 1
  funext p
  refine Finset.sum_congr rfl fun i _ => ?_
  exact l5_compactPathInf_eq_of_enc_eq henc hq _ _

end SupercriticalLQGUniqueness.B2.PfeLocal
