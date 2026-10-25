import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf




 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace Uniqueness.TwoScale.S36Events

 

theorem compact_path_limit_moving {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D)) {K : Set ℂ}
    (hK : IsCompact K) {x y : ℕ → ℂ} {x₀ y₀ : ℂ}
    (hx : Tendsto x atTop (nhds x₀)) (hy : Tendsto y atTop (nhds y₀))
    {P : ℕ → unitInterval → ℂ} (htrace : ∀ n t, P n t ∈ K)
    (hends : ∀ n, P n 0 = x n ∧ P n 1 = y n)
    {M : NNReal} (hLip : ∀ n, LipschitzWith M ((G n).pt ∘ P n))
    {L : ENNReal}
    (hbound : ∀ n, (G n).len (fun t => P n (projIcc 0 1 zero_le_one t)) 0 1 ≤ L) :
    ∃ P₀ : C(unitInterval, ℂ),
      D.IsCurve (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ∧
      (∀ t, P₀ t ∈ K) ∧ P₀ 0 = x₀ ∧ P₀ 1 = y₀ ∧
      D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ L := by
  obtain ⟨φ, P₀, hφ, hlim, htrace₀⟩ :=
    Toolkit.CompactPathInfimum.compact_trace_path_subseq hG hK htrace hLip
  have hGφ : Tendsto (fun n => G (φ n)) atTop (nhds D) :=
    hG.comp hφ.tendsto_atTop
  have hDlip : LipschitzWith M (D.pt ∘ P₀) :=
    Toolkit.PathInfimum.lipschitz_limit_of_epi hGφ hlim (fun n => hLip (φ n))
  have hcurve : D.IsCurve (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    exact (hDlip.continuous.comp continuous_projIcc).continuousOn
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => P (φ n) (projIcc 0 1 zero_le_one t)) atTop
        (nhds (P₀ (projIcc 0 1 zero_le_one t))) :=
    fun t _ => hlim.tendsto_at (projIcc 0 1 zero_le_one t)
  have hlen := Toolkit.CompactPathInfimum.joint_len_le_liminf hGφ hpoint
  have hlen' : D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ L :=
    hlen.trans (liminf_le_of_frequently_le'
      (Frequently.of_forall fun n => hbound (φ n)))
  refine ⟨P₀, hcurve, htrace₀, ?_, ?_, hlen'⟩
  · have hstart : Tendsto (fun n => P (φ n) 0) atTop (nhds (P₀ 0)) :=
      hlim.tendsto_at 0
    have heq : (fun n => P (φ n) 0) = (fun n => x (φ n)) :=
      funext fun n => (hends (φ n)).1
    rw [heq] at hstart
    exact tendsto_nhds_unique hstart
      (by simpa only [Function.comp_def] using hx.comp hφ.tendsto_atTop)
  · have hend : Tendsto (fun n => P (φ n) 1) atTop (nhds (P₀ 1)) :=
      hlim.tendsto_at 1
    have heq : (fun n => P (φ n) 1) = (fun n => y (φ n)) :=
      funext fun n => (hends (φ n)).2
    rw [heq] at hend
    exact tendsto_nhds_unique hend
      (by simpa only [Function.comp_def] using hy.comp hφ.tendsto_atTop)


 
theorem compactPathInf_seq_liminf_moving {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D)) {K : Set ℂ} (hK : IsCompact K)
    {x y : ℕ → ℂ} {x₀ y₀ : ℂ}
    (hx : Tendsto x atTop (nhds x₀)) (hy : Tendsto y atTop (nhds y₀)) :
    Toolkit.CompactPathInfimum.compactPathInf D K {x₀} {y₀} ≤
      liminf (fun n => Toolkit.CompactPathInfimum.compactPathInf (G n) K {x n} {y n}) atTop := by
  refine le_of_forall_lt fun v hv => ?_
  obtain ⟨w, hvw, hw⟩ := exists_between hv
  have hwfin : w ≠ ∞ := ne_top_of_lt hw
  have htail : ∀ᶠ n in atTop, w ≤ Toolkit.CompactPathInfimum.compactPathInf (G n) K {x n} {y n} := by
    by_contra hn
    rw [not_eventually] at hn
    obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hn
    have hbad' : ∀ n, Toolkit.CompactPathInfimum.compactPathInf (G (φ n)) K {x (φ n)} {y (φ n)} < w :=
      fun n => lt_of_not_ge (hbad n)
    have hpaths : ∀ n, ∃ (P : ℝ → ℂ) (a b : ℝ),
        (G (φ n)).IsCurve P a b ∧
        (∀ t ∈ Icc a b, P t ∈ K) ∧ P a = x (φ n) ∧ P b = y (φ n) ∧
        (G (φ n)).len P a b < w := by
      intro n
      unfold Toolkit.CompactPathInfimum.compactPathInf at hbad'
      obtain ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩ :=
        (by simpa only [iInf_lt_iff] using hbad' n)
      exact ⟨P, a, b, hP, htr, Set.mem_singleton_iff.mp hEa,
        Set.mem_singleton_iff.mp hFb, hcost⟩
    choose P a b hP htrace hEa hFb hlen using hpaths
    have hfin : ∀ n, (G (φ n)).len (P n) (a n) (b n) ≠ ∞ :=
      fun n => ne_top_of_lt (hlen n)
    have htrace' : ∀ n, P n '' Icc (a n) (b n) ⊆ K := by
      intro n z hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact htrace n t ht
    choose γ hγlen hγtrace hγlip using fun n =>
      Toolkit.CompactPathInfimum.exists_lipschitz_reparam (G (φ n)) (P n) (hP n) (hfin n) (htrace' n)
    let Q : ℕ → unitInterval → ℂ := fun n t => γ n t
    have hQtrace : ∀ n t, Q n t ∈ K := fun n t => hγtrace n t
    have hQends : ∀ n, Q n 0 = x (φ n) ∧ Q n 1 = y (φ n) := by
      intro n
      change (γ n 0 : ℂ) = x (φ n) ∧ (γ n 1 : ℂ) = y (φ n)
      rw [(γ n).source, (γ n).target]
      exact ⟨hEa n, hFb n⟩
    have hQlip : ∀ n, LipschitzWith w.toNNReal
        ((G (φ n)).pt ∘ Q n) := by
      intro n
      have hmono : ((G (φ n)).len (P n) (a n) (b n)).toNNReal ≤ w.toNNReal :=
        ENNReal.toNNReal_mono hwfin (hlen n).le
      exact (hγlip n).weaken hmono
    have hQbound : ∀ n,
        (G (φ n)).len (fun t => Q n (projIcc 0 1 zero_le_one t)) 0 1 ≤ w := by
      intro n
      change LQGMetric.MetricGeometry.pathLength (γ n) ≤ w
      exact (hγlen n).le.trans (hlen n).le
    obtain ⟨P₀, hP₀, hK₀, hE₀, hF₀, hlen₀⟩ :=
      compact_path_limit_moving (hG.comp hφ.tendsto_atTop) hK
        (by simpa only [Function.comp_def] using hx.comp hφ.tendsto_atTop)
        (by simpa only [Function.comp_def] using hy.comp hφ.tendsto_atTop)
        hQtrace hQends hQlip hQbound
    have hInf : Toolkit.CompactPathInfimum.compactPathInf D K {x₀} {y₀} ≤
        D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 := by
      unfold Toolkit.CompactPathInfimum.compactPathInf
      apply iInf_le_of_le (fun t => P₀ (projIcc 0 1 zero_le_one t))
      apply iInf_le_of_le (0 : ℝ)
      apply iInf_le_of_le (1 : ℝ)
      apply iInf_le_of_le hP₀
      apply iInf_le_of_le ?_
      · exact iInf_le_of_le (Set.mem_singleton_iff.mpr (by simpa using hE₀)) <|
          iInf_le_of_le (Set.mem_singleton_iff.mpr (by simpa using hF₀)) le_rfl
      · intro t ht
        change P₀ (projIcc 0 1 zero_le_one t) ∈ K
        rw [projIcc_of_mem zero_le_one ht]
        exact hK₀ ⟨t, ht⟩
    exact (not_le_of_gt hw) (hInf.trans hlen₀)
  exact hvw.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) htail)

 
theorem compactPointInf_lsc {K : Set ℂ} (hK : IsCompact K) :
    LowerSemicontinuous (fun p : LSCMetric × (K × K) =>
      Toolkit.CompactPathInfimum.compactPathInf p.1 K {(p.2.1 : ℂ)} {(p.2.2 : ℂ)}) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) := by
    exact (continuous_fst.tendsto p).comp hG
  have hc₁ : Continuous (fun q : LSCMetric × (K × K) => (q.2.1 : ℂ)) := by
    fun_prop
  have hc₂ : Continuous (fun q : LSCMetric × (K × K) => (q.2.2 : ℂ)) := by
    fun_prop
  have hx : Tendsto (fun n => ((G n).2.1 : ℂ)) atTop (nhds (p.2.1 : ℂ)) :=
    (hc₁.tendsto p).comp hG
  have hy : Tendsto (fun n => ((G n).2.2 : ℂ)) atTop (nhds (p.2.2 : ℂ)) :=
    (hc₂.tendsto p).comp hG
  exact compactPathInf_seq_liminf_moving hm hK hx hy

 

theorem internal_compact_eq_compactPointInf (D : LSCMetric) {K : Set ℂ}
    (x y : K) :
    D.internal K (x, y) = Toolkit.CompactPathInfimum.compactPathInf D K {(x : ℂ)} {(y : ℂ)} := by
  simp only [LSCMetric.internal, Toolkit.CompactPathInfimum.compactPathInf, Set.mem_singleton_iff]

 
theorem internal_compact_joint_lsc {K : Set ℂ} (hK : IsCompact K) :
    LowerSemicontinuous (fun p : LSCMetric × (K × K) =>
      p.1.internal K (p.2.1, p.2.2)) := by
  convert compactPointInf_lsc hK using 1
  funext p
  exact internal_compact_eq_compactPointInf p.1 p.2.1 p.2.2

 
theorem internal_compact_joint_borel {K : Set ℂ} (hK : IsCompact K) :
    @Measurable (LSCMetric × (K × K)) ENNReal (borel _) inferInstance
      (fun p => p.1.internal K (p.2.1, p.2.2)) := by
  letI : MeasurableSpace (LSCMetric × (K × K)) := borel _
  letI : OpensMeasurableSpace (LSCMetric × (K × K)) := ⟨le_rfl⟩
  exact (internal_compact_joint_lsc hK).measurable


end Uniqueness.TwoScale.S36Events
end SupercriticalLQGUniqueness
