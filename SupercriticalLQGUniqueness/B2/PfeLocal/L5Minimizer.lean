import SupercriticalLQGUniqueness.B2.PfeLocal.L5LenMeas
import SupercriticalLQGUniqueness.B2.PfeLocal.L3NonDawdle

 


















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum Uniqueness.Toolkit.PathInfimum LQGMetric.LM

 
theorem l5_exists_minimizer (D : LSCMetric) {K E F : Set ℂ} (hK : IsCompact K) (hE : IsClosed E)
    (hF : IsClosed F) (hfin : compactPathInf D K E F ≠ ∞) :
    ∃ P : ℝ → ℂ, D.IsCurve P 0 1 ∧ Continuous P ∧ (∀ t ∈ Icc (0 : ℝ) 1, P t ∈ K) ∧
      P 0 ∈ E ∧ P 1 ∈ F ∧ D.len P 0 1 = compactPathInf D K E F := by
  set A := compactPathInf D K E F with hAdef
  have hpaths : ∀ n : ℕ, ∃ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b ∧ (∀ t ∈ Icc a b, P t ∈ K) ∧ P a ∈ E ∧ P b ∈ F ∧
      D.len P a b < A + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro n
    have hlt : A < A + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
      ENNReal.lt_add_right hfin (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    rw [hAdef] at hlt
    unfold compactPathInf at hlt
    obtain ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩ := (by simpa only [iInf_lt_iff] using hlt)
    exact ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩
  choose P a b hP htrace hEa hFb hlen using hpaths
  have hle1 : ∀ n, A + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ A + 1 := fun n => by
    gcongr
    exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.succ_pos n)
  have hfinA1 : A + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hfin, ENNReal.one_ne_top⟩
  have hfinP : ∀ n, D.len (P n) (a n) (b n) ≠ ∞ := fun n =>
    ne_top_of_lt ((hlen n).trans_le (hle1 n))
  have htrace' : ∀ n, P n '' Icc (a n) (b n) ⊆ K := by
    intro n z hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact htrace n t ht
  choose γ hγlen hγtrace hγlip using fun n =>
    exists_lipschitz_reparam D (P n) (hP n) (hfinP n) (htrace' n)
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
  have hQlip : ∀ n, LipschitzWith (A + 1).toNNReal (D.pt ∘ Q n) := by
    intro n
    have hmono : (D.len (P n) (a n) (b n)).toNNReal ≤ (A + 1).toNNReal :=
      ENNReal.toNNReal_mono hfinA1 ((hlen n).le.trans (hle1 n))
    exact (hγlip n).weaken hmono
  have hQbound : ∀ n, D.len (fun t => Q n (projIcc 0 1 zero_le_one t)) 0 1 ≤
      A + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro n
    change LQGMetric.MetricGeometry.pathLength (γ n) ≤ _
    exact (hγlen n).le.trans (hlen n).le
  have hconst : Tendsto (fun _ : ℕ => D) atTop (𝓝 D) := tendsto_const_nhds
  obtain ⟨ψ, P₀, hψ, hlim, htrace₀⟩ := compact_trace_path_subseq hconst hK hQtrace hQlip
  have hDlip : LipschitzWith (A + 1).toNNReal (D.pt ∘ P₀) :=
    lipschitz_limit_of_epi hconst hlim (fun n => hQlip (ψ n))
  set P₁ : ℝ → ℂ := fun t => P₀ (projIcc 0 1 zero_le_one t)
  have hcurve : D.IsCurve P₁ 0 1 :=
    ⟨zero_le_one, (hDlip.continuous.comp continuous_projIcc).continuousOn⟩
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => Q (ψ n) (projIcc 0 1 zero_le_one t)) atTop (𝓝 (P₁ t)) :=
    fun t _ => hlim.tendsto_at (projIcc 0 1 zero_le_one t)
  have hlen₀ := joint_len_le_liminf hconst hpoint
  have hinv : Tendsto (fun n : ℕ => A + ((ψ n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 A) := by
    have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have h2 := (h1.comp hψ.tendsto_atTop)
    simpa using (tendsto_const_nhds (x := A)).add h2
  have hlen₁ : D.len P₁ 0 1 ≤ A := by
    refine hlen₀.trans ?_
    calc liminf (fun n => D.len (fun t => Q (ψ n) (projIcc 0 1 zero_le_one t)) 0 1) atTop
        ≤ liminf (fun n : ℕ => A + ((ψ n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n => hQbound (ψ n))
      _ = A := hinv.liminf_eq
  have hend : ∀ (S : Set ℂ), IsClosed S → ∀ s : unitInterval, (∀ n, Q (ψ n) s ∈ S) → P₀ s ∈ S :=
    fun S hS s hmem => hS.mem_of_tendsto (hlim.tendsto_at s) (Eventually.of_forall hmem)
  have hE₀ : P₁ 0 ∈ E := by
    simp only [P₁, projIcc_left]
    exact hend E hE 0 fun n => by rw [hQ0]; exact hEa (ψ n)
  have hF₀ : P₁ 1 ∈ F := by
    simp only [P₁, projIcc_right]
    exact hend F hF 1 fun n => by rw [hQ1]; exact hFb (ψ n)
  have hK₀ : ∀ t ∈ Icc (0 : ℝ) 1, P₁ t ∈ K := fun t _ => htrace₀ _
  refine ⟨P₁, hcurve, P₀.continuous.comp continuous_projIcc, hK₀, hE₀, hF₀,
    le_antisymm hlen₁ ?_⟩
  exact l5_compactPathInf_le D P₁ 0 1 hcurve hK₀ hE₀ hF₀

 
theorem l5_cut (D : LSCMetric) (P : ℝ → ℂ) {a t₁ t₂ b : ℝ} (ha : a ≤ t₁) (h12 : t₁ ≤ t₂)
    (hb : t₂ ≤ b) (hP : D.IsCurve P a b) (hy : P t₁ = P t₂) :
    ∃ Q : ℝ → ℂ, D.IsCurve Q a (b - (t₂ - t₁)) ∧
      D.len Q a (b - (t₂ - t₁)) = D.len P a t₁ + D.len P t₂ b ∧
      (∀ t ∈ Icc a (b - (t₂ - t₁)), Q t ∈ P '' Icc a b) ∧ Q a = P a ∧
      Q (b - (t₂ - t₁)) = P b := by
  classical
  set δ := t₂ - t₁ with hδ
  set e := b - δ with he
  have hδ0 : 0 ≤ δ := sub_nonneg.2 h12
  have h1e : t₁ ≤ e := by rw [he, hδ]; linarith
  set Q : ℝ → ℂ := fun t => if t ≤ t₁ then P t else P (t + δ)
  have hQ1 : EqOn Q P (Icc a t₁) := fun t ht => by simp only [Q, if_pos ht.2]
  have hQ2 : EqOn Q (P ∘ fun t => t + δ) (Icc t₁ e) := by
    intro t ht
    by_cases h : t ≤ t₁
    · have ht1 : t = t₁ := le_antisymm h ht.1
      simp only [Q, Function.comp_apply]
      rw [if_pos h, ht1, hy]
      congr 1
      rw [hδ]
      ring
    · simp only [Q, if_neg h, Function.comp_apply]
  have hmaps : MapsTo (fun t => t + δ) (Icc t₁ e) (Icc a b) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc1 : ContinuousOn (D.pt ∘ Q) (Icc a t₁) :=
    (hP.2.mono (Icc_subset_Icc le_rfl (h12.trans hb))).congr fun t ht => by
      simp only [Function.comp_apply, hQ1 ht]
  have hc2 : ContinuousOn (D.pt ∘ Q) (Icc t₁ e) :=
    (hP.2.comp (continuous_id.add continuous_const).continuousOn hmaps).congr fun t ht => by
      simp only [Function.comp_apply]
      rw [hQ2 ht]
      rfl
  have hunion : Icc a e = Icc a t₁ ∪ Icc t₁ e := (Icc_union_Icc_eq_Icc ha h1e).symm
  have hcurve : D.IsCurve Q a e := by
    refine ⟨ha.trans h1e, ?_⟩
    rw [hunion]
    exact hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc
  refine ⟨Q, hcurve, ?_, ?_, ?_, ?_⟩
  · unfold LSCMetric.len
    have hsplit := eVariationOn.Icc_add_Icc (D.pt ∘ Q) (s := univ) ha h1e (mem_univ _)
    simp only [univ_inter] at hsplit
    rw [← hsplit, eVariationOn.eq_of_eqOn (fun t ht => by simp only [Function.comp_apply,
      hQ1 ht] : EqOn (D.pt ∘ Q) (D.pt ∘ P) (Icc a t₁))]
    congr 1
    rw [eVariationOn.eq_of_eqOn (fun t ht => by
      simp only [Function.comp_apply]; rw [hQ2 ht]; rfl :
        EqOn (D.pt ∘ Q) ((D.pt ∘ P) ∘ fun t => t + δ) (Icc t₁ e))]
    rw [eVariationOn.comp_eq_of_monotoneOn _ _ (fun x _ y _ hxy => by linarith),
      image_add_const_Icc]
    congr 2 <;> simp [hδ, he]
  · intro t ht
    by_cases h : t ≤ t₁
    · simp only [Q, if_pos h]
      exact ⟨t, ⟨ht.1, h.trans (h12.trans hb)⟩, rfl⟩
    · simp only [Q, if_neg h]
      exact ⟨t + δ, hmaps ⟨(not_le.1 h).le, ht.2⟩, rfl⟩
  · simp only [Q, if_pos ha]
  · by_cases h : e ≤ t₁
    · have h' : e = t₁ := le_antisymm h h1e
      have hb' : t₂ = b := by rw [he, hδ] at h'; linarith
      simp only [Q, if_pos h]
      rw [h', hy, hb']
    · simp only [Q, if_neg h]
      congr 1
      rw [he]
      ring

 
theorem l5_minimizer_fiber_null (D : LSCMetric) {K E F : Set ℂ} (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) (hPe : ContinuousOn P (Icc a b)) (hK : ∀ t ∈ Icc a b, P t ∈ K)
    (hE : P a ∈ E) (hF : P b ∈ F) (hmin : D.len P a b ≤ compactPathInf D K E F)
    (hfin : D.len P a b ≠ ∞) (y : ℂ) :
    t17LenMeas (D.pt ∘ P) a b (Icc a b ∩ P ⁻¹' {y}) = 0 := by
  set T := Icc a b ∩ P ⁻¹' {y} with hT
  rcases T.eq_empty_or_nonempty with h0 | hne
  · rw [h0, measure_empty]
  have hTc : IsClosed T := hPe.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTk : IsCompact T := isCompact_Icc.of_isClosed_subset hTc inter_subset_left
  have hm1 := hTk.sInf_mem hne
  have hm2 := hTk.sSup_mem hne
  set t₁ := sInf T
  set t₂ := sSup T
  have hsub : T ⊆ Icc t₁ t₂ := fun t ht =>
    ⟨csInf_le hTk.bddBelow ht, le_csSup hTk.bddAbove ht⟩
  have h12 : t₁ ≤ t₂ := le_csSup hTk.bddAbove hm1
  have hy : P t₁ = P t₂ := by rw [hm1.2, hm2.2]
  have hc : T17Curve (D.pt ∘ P) a b := ⟨hP.1, hP.2, hfin⟩
  have hmeas : t17LenMeas (D.pt ∘ P) a b T ≤ D.len P t₁ t₂ :=
    t17LenMeas_le_of_subset hc hm1.1.1 h12 hm2.1.2 hsub
  obtain ⟨Q, hQ, hQlen, hQtr, hQa, hQb⟩ := l5_cut D P hm1.1.1 h12 hm2.1.2 hP hy
  have hadm : compactPathInf D K E F ≤ D.len Q a (b - (t₂ - t₁)) := by
    refine l5_compactPathInf_le D Q a _ hQ (fun t ht => ?_) (hQa ▸ hE) (hQb ▸ hF)
    obtain ⟨s, hs, hst⟩ := hQtr t ht
    exact hst ▸ hK s hs
  have hsplit : D.len P a b = D.len P a t₁ + D.len P t₁ t₂ + D.len P t₂ b := by
    unfold LSCMetric.len
    have e1 := eVariationOn.Icc_add_Icc (D.pt ∘ P) (s := univ) hm1.1.1 h12 (mem_univ _)
    have e2 := eVariationOn.Icc_add_Icc (D.pt ∘ P) (s := univ) (hm1.1.1.trans h12) hm2.1.2
      (mem_univ _)
    simp only [univ_inter] at e1 e2
    rw [← e2, ← e1]
  have hkey : D.len P a t₁ + D.len P t₂ b + D.len P t₁ t₂ ≤ D.len P a t₁ + D.len P t₂ b + 0 := by
    rw [add_zero]
    calc D.len P a t₁ + D.len P t₂ b + D.len P t₁ t₂ = D.len P a b := by rw [hsplit]; ring
      _ ≤ compactPathInf D K E F := hmin
      _ ≤ D.len Q a (b - (t₂ - t₁)) := hadm
      _ = D.len P a t₁ + D.len P t₂ b := hQlen
  have hfin' : D.len P a t₁ + D.len P t₂ b ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin ?_
    rw [hsplit]
    calc D.len P a t₁ + D.len P t₂ b ≤ D.len P a t₁ + D.len P t₁ t₂ + D.len P t₂ b := by
          gcongr; exact le_self_add
      _ = _ := rfl
  have hzero : D.len P t₁ t₂ ≤ 0 := (ENNReal.add_le_add_iff_left hfin').1 hkey
  exact le_antisymm (hmeas.trans hzero) bot_le

 
theorem l5_square_subset_ball (ε : ℝ) (hε : 0 < ε) (θ : ℝ × ℝ) (k : ℤ × ℤ) :
    t17Square ε θ k ⊆
      ball (⟨ε * (k.1 + θ.1 + 1 / 2), ε * (k.2 + θ.2 + 1 / 2)⟩ : ℂ) ε := by
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [mem_ball, Complex.dist_eq]
  set c : ℂ := ⟨ε * (k.1 + θ.1 + 1 / 2), ε * (k.2 + θ.2 + 1 / 2)⟩
  have hre : |(z - c).re| < ε / 2 := by
    simp only [Complex.sub_re, c]
    rw [abs_lt]; constructor <;> nlinarith
  have him : |(z - c).im| < ε / 2 := by
    simp only [Complex.sub_im, c]
    rw [abs_lt]; constructor <;> nlinarith
  calc ‖z - c‖ ≤ |(z - c).re| + |(z - c).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < ε / 2 + ε / 2 := add_lt_add hre him
    _ = ε := by ring

 

theorem l5_nondawdle (D : LSCMetric) {K E F : Set ℂ} (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) (hPe : ContinuousOn P (Icc a b)) (hK : ∀ t ∈ Icc a b, P t ∈ K)
    (hE : P a ∈ E) (hF : P b ∈ F) (hmin : D.len P a b ≤ compactPathInf D K E F)
    (hfin : D.len P a b ≠ ∞) :
    Tendsto (fun j : ℕ => ⨆ y : ℂ, t17LenMeas (D.pt ∘ P) a b
      (Icc a b ∩ P ⁻¹' ball y (1 / ((j : ℝ) + 1)))) atTop (𝓝 0) := by
  set μ := t17LenMeas (D.pt ∘ P) a b
  have hc : T17Curve (D.pt ∘ P) a b := ⟨hP.1, hP.2, hfin⟩
  have hfinμ : μ (Icc a b) ≠ ∞ := by rw [t17LenMeas_Icc hc]; exact hfin
  haveI : IsFiniteMeasure (μ.restrict (Icc a b)) := isFiniteMeasure_restrict.2 hfinμ
  have hfib : ∀ y : ℂ, μ.restrict (Icc a b) (Icc a b ∩ P ⁻¹' {y}) = 0 := by
    intro y
    exact le_antisymm ((Measure.restrict_le_self _).trans
      (l5_minimizer_fiber_null D P hP hPe hK hE hF hmin hfin y).le) bot_le
  have h := l3_sup_ball_tendsto_zero (μ.restrict (Icc a b)) P hPe hfib
  refine h.congr fun j => ?_
  congr 1
  funext y
  rw [Measure.restrict_apply' measurableSet_Icc, inter_assoc, inter_comm _ (Icc a b),
    ← inter_assoc, inter_self]

 
theorem l5_square_le_ball (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) (j : ℕ) (θ : ℝ × ℝ)
    (k : ℤ × ℤ) :
    pathLengthIn D P a b (t17Square (1 / ((j : ℝ) + 1)) θ k) ≤
      ⨆ y : ℂ, t17LenMeas (D.pt ∘ P) a b (Icc a b ∩ P ⁻¹' ball y (1 / ((j : ℝ) + 1))) := by
  have hε : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  refine le_iSup_of_le (⟨(1 / ((j : ℝ) + 1)) * (k.1 + θ.1 + 1 / 2),
    (1 / ((j : ℝ) + 1)) * (k.2 + θ.2 + 1 / 2)⟩ : ℂ) ?_
  unfold pathLengthIn
  refine measure_mono fun t ht => ⟨ht.2, l5_square_subset_ball _ hε θ k ht.1⟩

end SupercriticalLQGUniqueness.B2.PfeLocal
