import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldGeoForward
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact




 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

theorem compact_internal_attained (D : LSCMetric) {K : Set ℂ}
    (hK : IsCompact K) (u v : K)
    (hfin : D.internal K (u, v) < ⊤) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ K) ∧
      P a = (u : ℂ) ∧ P b = (v : ℂ) ∧
      D.len P a b = D.internal K (u, v) := by
  let L : ENNReal := D.internal K (u, v)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hpaths : ∀ n, ∃ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b ∧ (∀ t ∈ Icc a b, P t ∈ K) ∧
      P a = (u : ℂ) ∧ P b = (v : ℂ) ∧
      D.len P a b < L + ENNReal.ofReal (ε n) := by
    intro n
    have hlt : L < L + ENNReal.ofReal (ε n) :=
      ENNReal.lt_add_right hfin.ne (ENNReal.ofReal_pos.mpr (hεpos n)).ne'
    unfold L LSCMetric.internal at hlt
    obtain ⟨P, a, b, hP, htrace, hu, hv, hlen⟩ :=
      (by simpa only [iInf_lt_iff] using hlt)
    exact ⟨P, a, b, hP, htrace, hu, hv, hlen⟩
  choose P a b hP htrace hu hv hlen using hpaths
  have hεle (n : ℕ) : ENNReal.ofReal (ε n) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    dsimp [ε]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 0 < (n : ℝ) + 1 := by linarith
    exact (div_le_one hden).mpr (by linarith)
  have hMfin : L + 1 ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨hfin.ne, ENNReal.one_ne_top⟩
  have hsum (n : ℕ) : L + ENNReal.ofReal (ε n) ≤ L + 1 := by
    simpa only [add_comm] using (add_le_add_left (hεle n) L)
  have hcurvefin (n : ℕ) : D.len (P n) (a n) (b n) ≠ ⊤ :=
    ne_top_of_le_ne_top hMfin ((hlen n).le.trans (hsum n))
  have htrace' (n : ℕ) : P n '' Icc (a n) (b n) ⊆ K := by
    rintro x ⟨t, ht, rfl⟩
    exact htrace n t ht
  choose γ hγlen hγtrace hγlip using fun n =>
    Toolkit.CompactPathInfimum.exists_lipschitz_reparam D (P n) (hP n) (hcurvefin n) (htrace' n)
  let Q : ℕ → unitInterval → ℂ := fun n t => γ n t
  have hQtrace : ∀ n t, Q n t ∈ K := fun n t => hγtrace n t
  have hQends : ∀ n, Q n 0 = (u : ℂ) ∧ Q n 1 = (v : ℂ) := by
    intro n
    change (γ n 0 : ℂ) = _ ∧ (γ n 1 : ℂ) = _
    rw [(γ n).source, (γ n).target]
    exact ⟨hu n, hv n⟩
  have hQlip : ∀ n, LipschitzWith (L + 1).toNNReal (D.pt ∘ Q n) := by
    intro n
    have hmono : (D.len (P n) (a n) (b n)).toNNReal ≤ (L + 1).toNNReal :=
      ENNReal.toNNReal_mono hMfin
        ((hlen n).le.trans (hsum n))
    exact (hγlip n).weaken hmono
  obtain ⟨φ, P₀, hφ, hlim, htrace₀⟩ :=
    Toolkit.CompactPathInfimum.compact_trace_path_subseq (G := fun _ => D)
      tendsto_const_nhds hK hQtrace hQlip
  have hDlip : LipschitzWith (L + 1).toNNReal (D.pt ∘ P₀) :=
    Toolkit.PathInfimum.lipschitz_limit_of_epi (G := fun _ => D) tendsto_const_nhds hlim
      (fun n => hQlip (φ n))
  let R : ℝ → ℂ := fun t => P₀ (projIcc 0 1 zero_le_one t)
  have hRcurve : D.IsCurve R 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    exact (hDlip.continuous.comp continuous_projIcc).continuousOn
  have hRtrace : ∀ t ∈ Icc (0 : ℝ) 1, R t ∈ K := by
    intro t ht
    exact htrace₀ (projIcc 0 1 zero_le_one t)
  have hRu : R 0 = (u : ℂ) := by
    have hstart := hlim.tendsto_at (0 : unitInterval)
    have hconst : (fun n => Q (φ n) 0) = fun _ => (u : ℂ) :=
      funext fun n => (hQends (φ n)).1
    rw [hconst] at hstart
    have h0 : P₀ 0 = (u : ℂ) :=
      tendsto_nhds_unique hstart tendsto_const_nhds
    have hp0 : projIcc 0 1 zero_le_one (0 : ℝ) = (0 : unitInterval) := by
      apply Subtype.ext
      rw [projIcc_of_mem zero_le_one (show (0 : ℝ) ∈ Icc 0 1 by norm_num)]
      rfl
    simpa only [R, hp0] using h0
  have hRv : R 1 = (v : ℂ) := by
    have hend := hlim.tendsto_at (1 : unitInterval)
    have hconst : (fun n => Q (φ n) 1) = fun _ => (v : ℂ) :=
      funext fun n => (hQends (φ n)).2
    rw [hconst] at hend
    have h1 : P₀ 1 = (v : ℂ) :=
      tendsto_nhds_unique hend tendsto_const_nhds
    have hp1 : projIcc 0 1 zero_le_one (1 : ℝ) = (1 : unitInterval) := by
      apply Subtype.ext
      rw [projIcc_of_mem zero_le_one (show (1 : ℝ) ∈ Icc 0 1 by norm_num)]
      rfl
    simpa only [R, hp1] using h1
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => Q (φ n) (projIcc 0 1 zero_le_one t)) atTop
        (nhds (R t)) :=
    fun t _ => hlim.tendsto_at (projIcc 0 1 zero_le_one t)
  have hlenlim : D.len R 0 1 ≤
      liminf (fun n => D.len (fun t => Q (φ n) (projIcc 0 1 zero_le_one t)) 0 1) atTop :=
    Toolkit.CompactPathInfimum.joint_len_le_liminf (G := fun _ => D) tendsto_const_nhds hpoint
  have hεlim : Tendsto (fun n => L + ENNReal.ofReal (ε (φ n))) atTop (nhds L) := by
    have he : Tendsto (fun n => ε n) atTop (nhds (0 : ℝ)) := by
      simpa only [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have he' : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (nhds (0 : ENNReal)) := by
      simpa using ENNReal.tendsto_ofReal he
    simpa only [Function.comp_def, add_zero] using
      ((tendsto_const_nhds (x := L)).add he').comp hφ.tendsto_atTop
  have hlenbound : D.len R 0 1 ≤ L := by
    apply hlenlim.trans
    rw [← hεlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
      (by isBoundedDefault) (by isBoundedDefault)
    ·
      change LQGMetric.MetricGeometry.pathLength (γ (φ n)) ≤ _
      exact (hγlen (φ n)).le.trans (hlen (φ n)).le
  have hLle : L ≤ D.len R 0 1 := by
    unfold L LSCMetric.internal
    exact iInf_le_of_le R <| iInf_le_of_le (0 : ℝ) <| iInf_le_of_le (1 : ℝ) <|
      iInf_le_of_le hRcurve <| iInf_le_of_le hRtrace <|
      iInf_le_of_le hRu <| iInf_le_of_le hRv le_rfl
  exact ⟨R, 0, 1, hRcurve, hRtrace, hRu, hRv, le_antisymm hlenbound hLle⟩

 
theorem compact_geodesic_iff_internal (D : LSCMetric) {K : Set ℂ}
    (hK : IsCompact K) (u v : K) :
    ((∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧
        (∀ t ∈ Icc a b, P t ∈ K) ∧
        P a = (u : ℂ) ∧ P b = (v : ℂ) ∧
        D.len P a b = D ((u : ℂ), (v : ℂ))) ∧
      D ((u : ℂ), (v : ℂ)) < ⊤) ↔
    D.internal K (u, v) ≤ D ((u : ℂ), (v : ℂ)) ∧
      D ((u : ℂ), (v : ℂ)) < ⊤ := by
  constructor
  · rintro ⟨⟨P, a, b, hP, htrace, hu, hv, hlen⟩, hfin⟩
    exact ⟨Objects.Shield.internal_le_of_compact_geodesic D K u v P a b
      hP htrace hu hv hlen, hfin⟩
  · rintro ⟨hle, hfin⟩
    obtain ⟨P, a, b, hP, htrace, hu, hv, hlen⟩ :=
      compact_internal_attained D hK u v (hle.trans_lt hfin)
    have hDle : D ((u : ℂ), (v : ℂ)) ≤ D.len P a b := by
      rw [← hu, ← hv]
      exact apply_le_len D P hP.1
    refine ⟨⟨P, a, b, hP, htrace, hu, hv, ?_⟩, hfin⟩
    exact le_antisymm (hlen ▸ hle) hDle

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
