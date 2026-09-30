import QuantumZipper.Proofs.Zipper.D3PlusN2RExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2 heart on the restricted index (Decision D36): `N2ZHeartWinStmt` from H2' and H3'

Task D36-IMPL, step (6). `n2ZHeartWin_of_nodes : N2HLatTVWinStmt → N2HModelDecompWinStmt →
N2ZHeartWinStmt`. Copy of `n2ZHeart_of_nodes` (`D3PlusN2HeartMain.lean`) on the restricted
window index `WinIdx K` (Decision D36), with the lateral datum `n2LatY X r` replaced by its
folded-circle reading `n2LatC X r` (`D3PlusN2RExt.lean`), whose independence from the radial
data is proved (`indepFun_n2LatC_n2RadR`), so H1 is not a hypothesis.

Route (DMS arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78): the model's restricted window
data are, off `{Tc < log K + 1}`, `heartFW (lateral data, radial data)` (H3'); the wedge's are a.s.
`heartWW (lateral window, radial path)`; lateral and radial data are independent on both sides;
mixing (`tvDist_indep_mix_le`) bounds the TV by the average lateral TV at the random scale
`r e^{−Tc}` (H2' plus `tendsto_prob_Tc_lt`) and the radial TV (`n2_radial_tv`). Own assembly of
the cited steps (as in `D3PlusN2HeartMain.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **The restricted heart node from the restricted H2 and H3 nodes** (H1 proved,
`indepFun_n2LatC_n2RadR`). -/
theorem n2ZHeartWin_of_nodes (hH2 : N2HLatTVWinStmt) (hH3 : N2HModelDecompWinStmt) :
    N2ZHeartWinStmt := by
  intro γ α r Ω _ P _ X Ω'' _ P'' _ X'' A hγ hγ2 hα hr hX hX'' hA hInd K hK
  refine ⟨fun L => aemeasurable_resFieldW_n2Emb hα hr hX K hK, ?_⟩
  set S := Real.log K with hSdef
  -- the wedge side
  have hV : P''.map (fun ω => resFieldW K (wedgeV γ X'' A ω)) =
      P''.map (fun ω => heartWW γ K (latY''W K X'' ω, radR'' K A ω)) :=
    Measure.map_congr (ae_resFieldW_wedgeV_eq hA hK)
  have hY''m : Measurable (latY''W K X'') := measurable_latY''W hX'' K hK
  have hR''m : AEMeasurable (radR'' K A) P'' :=
    (ZoomRadial.measurable_trunc S).comp_aemeasurable (ZoomRadial.aemeasurable_wedgePath hA)
  have hφ : Measurable fun x : FieldSample => fun i : WinIdx K => lateralPart x (winIdx K i) :=
    Measurable.of_eval fun i => by
      have : IsFiniteMeasure (winIdx K i) := (isAdmissibleH_winIdx K i).1
      exact WedgeTK.measurable_lateralPart_apply (winIdx K i)
  have hI'' : IndepFun (latY''W K X'') (radR'' K A) P'' := by
    have h := hInd.comp hφ (ZoomRadial.measurable_trunc S)
    exact h
  -- H2' gives a threshold
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have he : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨u, hu0, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (ENNReal.tendsto_nhds_zero.1 (hH2 r K P X P'' X'' hr hX hX'') (ε / 2) he)
  set T0 := Real.log (r / u) + 1 with hT0
  have hscale : ∀ τ : ℝ, T0 ≤ τ → r * Real.exp (-τ) ∈ Ioo 0 u := by
    intro τ hτ
    refine ⟨mul_pos hr (Real.exp_pos _), ?_⟩
    have h1 : Real.exp (-τ) ≤ Real.exp (-T0) := Real.exp_le_exp.2 (by linarith)
    have h2 : r * Real.exp (-T0) < u := by
      rw [hT0, neg_add, Real.exp_add, Real.exp_neg, Real.exp_log (div_pos hr hu0)]
      have : Real.exp (-1) < 1 := by
        have h := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
        rwa [Real.exp_zero] at h
      calc r * ((r / u)⁻¹ * Real.exp (-1)) = u * Real.exp (-1) := by field_simp
        _ < u * 1 := by gcongr
        _ = u := mul_one u
    calc r * Real.exp (-τ) ≤ r * Real.exp (-T0) := by gcongr
      _ < u := h2
  -- the vanishing error terms
  set rad : ℝ → ℝ≥0∞ := fun L => ENNReal.ofReal (2 * (P'' {ω | ∃ v ∈ Icc 0 S,
    n2Lev γ α L r ≤ A (-v) ω}).toReal) with hrad
  have hradT : Tendsto rad atTop (𝓝 0) := by
    have h := (n2_radial_tv (P := P) (X := X) hγ hα hr hX hA (Real.log_nonneg
      (by exact_mod_cast hK : (1 : ℝ) ≤ K))).1
    have h2 := ENNReal.tendsto_ofReal h
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  have hsum : Tendsto (fun L => P {ω | ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω <
      S + 1} + (P {ω | ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω < T0} + rad L))
      atTop (𝓝 0) := by
    have h := (tendsto_prob_Tc_lt hγ hα hr hX (S + 1)).add
      ((tendsto_prob_Tc_lt hγ hα hr hX T0).add hradT)
    simpa using h
  filter_upwards [(tendsto_n2Lev hγ α r).eventually_gt_atTop 0,
    ENNReal.tendsto_nhds_zero.1 hsum (ε / 2) he] with L hL hLs
  set Tc : Ω → ℝ := ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) with hTc
  set W : Ω → WinIdx K → ℝ := fun ω => resFieldW K (n2Emb γ α L r X ω) with hW
  set Y := n2LatC X r
  set R := n2RadR γ α L r K X
  have hYm : Measurable Y := measurable_n2LatC hX hr
  have hRm : AEMeasurable R P := aemeasurable_n2RadR hα hr hX hL K
  have hFm : AEMeasurable (fun ω => heartFW γ r K (Y ω, R ω)) P :=
    (measurable_heartFW γ r K hK).comp_aemeasurable (hYm.aemeasurable.prodMk hRm)
  -- (1) the model decomposition
  have t1 : TV.tvDist (P.map W) (P.map fun ω => heartFW γ r K (Y ω, R ω)) ≤
      P {ω | Tc ω < S + 1} := by
    have h := tvDist_map_le_of_coord (aemeasurable_resFieldW_n2Emb hα hr hX K hK) hFm
      {ω | S + 1 ≤ Tc ω} (fun i => by
        filter_upwards [hH3 γ α r P X hγ hγ2 hα hr hX K hK L hL i] with ω hω hmem
        rw [hω hmem, heartFW_n2LatC])
    have e : {ω | S + 1 ≤ Tc ω}ᶜ = {ω | Tc ω < S + 1} := by
      ext ω; simp only [mem_compl_iff, mem_setOf_eq, not_le]
    rw [e] at h
    exact h
  -- (2) the mixing
  set δ : ℝ × (ℝ → ℝ) → ℝ≥0∞ := fun t =>
    TV.tvDist (P.map fun ω => latWinW K (r * Real.exp (-t.1)) (Y ω)) (P''.map (latY''W K X''))
    with hδ
  have hδle : ∀ t, TV.tvDist ((P.map Y).map fun y => heartFW γ r K (y, t))
      ((P''.map (latY''W K X'')).map fun y => heartWW γ K (y, Prod.snd t)) ≤ δ t := by
    intro t
    have htr : Measurable fun v : WinIdx K → ℝ => v + heartPsiW (Qc γ) K t.2 :=
      Measurable.of_eval fun i => (measurable_pi_apply i).add_const _
    have e1 : (P.map Y).map (fun y => heartFW γ r K (y, t)) =
        (P.map fun ω => latWinW K (r * Real.exp (-t.1)) (Y ω)).map
          fun v => v + heartPsiW (Qc γ) K t.2 := by
      have hm1 : Measurable fun y : FieldSample => heartFW γ r K (y, t) :=
        (measurable_heartFW γ r K hK).comp (measurable_id.prodMk measurable_const)
      have hm2 : Measurable fun ω => latWinW K (r * Real.exp (-t.1)) (Y ω) :=
        ((measurable_latWinW_joint K hK).comp (measurable_const.prodMk measurable_id)).comp hYm
      rw [Measure.map_map hm1 hYm, Measure.map_map htr hm2]
      rfl
    have e2 : (P''.map (latY''W K X'')).map (fun y => heartWW γ K (y, Prod.snd t)) =
        (P''.map (latY''W K X'')).map fun v => v + heartPsiW (Qc γ) K t.2 := rfl
    rw [e1, e2]
    exact TV.tvDist_map_le htr
  have hδint : ∫⁻ t, δ t ∂(P.map R) ≤ ε / 2 + P {ω | Tc ω < T0} := by
    have hs : MeasurableSet {t : ℝ × (ℝ → ℝ) | t.1 < T0} :=
      measurableSet_lt measurable_fst measurable_const
    have hb : ∀ t, δ t ≤ ε / 2 + {t : ℝ × (ℝ → ℝ) | t.1 < T0}.indicator 1 t := by
      intro t
      by_cases ht : t.1 < T0
      · rw [indicator_of_mem (s := {t : ℝ × (ℝ → ℝ) | t.1 < T0}) ht]
        exact TV.tvDist_le_one.trans le_add_self
      · rw [indicator_of_notMem (s := {t : ℝ × (ℝ → ℝ) | t.1 < T0}) ht]
        have hδt : δ t = TV.tvDist (P.map fun ω => latWinW K (r * Real.exp (-t.1)) (n2LatY X r ω))
            (P''.map (latY''W K X'')) := by
          simp only [hδ, Y, latWinW_n2LatC]
        rw [hδt]
        exact (hu (hscale t.1 (not_lt.1 ht))).trans le_self_add
    calc ∫⁻ t, δ t ∂(P.map R) ≤ ∫⁻ t, (ε / 2 + {t : ℝ × (ℝ → ℝ) | t.1 < T0}.indicator 1 t)
          ∂(P.map R) := lintegral_mono hb
      _ = ε / 2 + P {ω | Tc ω < T0} := by
        rw [lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_one hs,
          measure_univ, mul_one, Measure.map_apply_of_aemeasurable hRm hs]
        rfl
  have t2 := tvDist_indep_mix_le hYm.aemeasurable hRm hY''m.aemeasurable hR''m
    (indepFun_n2LatC_n2RadR hα hr hX hL K) hI'' (measurable_heartFW γ r K hK)
    (measurable_heartWW γ K) measurable_snd δ hδle
  have t3 := tvDist_n2RadR_le (P := P) (X := X) hγ hα hr hX hA hL hK
  rw [hV]
  calc TV.tvDist (P.map W) (P''.map fun ω => heartWW γ K (latY''W K X'' ω, radR'' K A ω))
      ≤ TV.tvDist (P.map W) (P.map fun ω => heartFW γ r K (Y ω, R ω)) +
        TV.tvDist (P.map fun ω => heartFW γ r K (Y ω, R ω))
          (P''.map fun ω => heartWW γ K (latY''W K X'' ω, radR'' K A ω)) := TV.tvDist_triangle
    _ ≤ P {ω | Tc ω < S + 1} + ((ε / 2 + P {ω | Tc ω < T0}) + rad L) :=
        add_le_add t1 (t2.trans (add_le_add hδint t3))
    _ = ε / 2 + (P {ω | Tc ω < S + 1} + (P {ω | Tc ω < T0} + rad L)) := by ring
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl hLs
    _ = ε := ENNReal.add_halves ε

end D3Plus
end QuantumZipper
