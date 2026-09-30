import QuantumZipper.Proofs.Zipper.T13Hard3TWinGlue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD3-TWIN: `LSCCTWinIndStmt` from the pure Brownian node `HitPathIndStmt`

`D3Plus.lsccTWinInd_of_hitPath : HitPathIndStmt → LSCCTWinIndStmt`.

Route (Duplantier–Miller–Sheffield arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78), adapted
from `n2ZHeartWin_of_nodes` (`D3PlusN2RMix.lean`): off `{Tc < log K + 1}` the restricted window is
`heartFW (lateral, (Tc, ρ))` (H3', proved); the lateral data are independent of `(Tc, ρ)`
(`indepFun_n2LatC_n2RadR`); the mixing inequality `tvDist_indep_mix_le` replaces the lateral
window at the random scale `r e^{−Tc}` by an independent wedge lateral sample (H2', proved) at a
cost `∫ δ`, both for the pair `(W, Tc)` (against the product law `ν ⊗ (law Tc ⊗ law ρ)`, with the
extra cost `d_TV(law (Tc, ρ), law Tc ⊗ law ρ)`, controlled by `HitPathIndStmt`) and for `W` alone;
TV of products (`lscc_tvDist_prod_le`) closes. Own assembly of the cited steps.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **LSCC-TWIN-IND from the pure Brownian path/hitting-time independence.** -/
theorem lsccTWinInd_of_hitPath (h : HitPathIndStmt) : LSCCTWinIndStmt := by
  intro γ α r Ω _ P _ X hγ hγ2 hα hr hX K hK
  obtain ⟨Ω', m', P', Y', B', hP', hY', -⟩ :=
    NonVacuity.exists_wedge_indep_BM_uncond (γ := γ) hα
  obtain ⟨-, Ω'', _, P'', X'', A, hP'', hX'', hA, hI, -⟩ := hY'
  haveI := hP''
  set S := Real.log K with hSdef
  have hS0 : 0 ≤ S := Real.log_nonneg (by exact_mod_cast hK : (1 : ℝ) ≤ K)
  have hHP := (h α (Qc γ) P (zRadB X r) (isBrownianReal_zRadB hX hr) hα S hS0).comp
    (tendsto_n2Lev hγ α r)
  have hH2 := n2HLatTVWin_of_harm n2H2HarmWinStmt_holds
  have hH3 := n2HModelDecompWin_of_split n2H3SplitWinStmt_holds
  have hY''m : Measurable (latY''W K X'') := measurable_latY''W hX'' K hK
  set ν := P''.map (latY''W K X'') with hνdef
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have he2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have he : 0 < ε / 2 / 2 := ENNReal.half_pos he2.ne'
  obtain ⟨u, hu0, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (ENNReal.tendsto_nhds_zero.1 (hH2 r K P X P'' X'' hr hX hX'') (ε / 2 / 2 / 2)
      (ENNReal.half_pos he.ne'))
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
  have hsum : Tendsto (fun L => P {ω | ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω <
      S + 1} + (P {ω | ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω < T0} +
      TV.tvDist
        (P.map fun ω => (ZoomRadial.trunc S (ZoomRadial.zoomRadial α (Qc γ) (zRadB X r)
          (n2Lev γ α L r) ω), ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω))
        ((P.map fun ω => ZoomRadial.trunc S (ZoomRadial.zoomRadial α (Qc γ) (zRadB X r)
          (n2Lev γ α L r) ω)).prod
          (P.map fun ω => ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω))))
      atTop (𝓝 0) := by
    have h := (tendsto_prob_Tc_lt hγ hα hr hX (S + 1)).add
      ((tendsto_prob_Tc_lt hγ hα hr hX T0).add hHP)
    simpa using h
  filter_upwards [(tendsto_n2Lev hγ α r).eventually_gt_atTop 0,
    ENNReal.tendsto_nhds_zero.1 hsum (ε / 2 / 2 / 2) (ENNReal.half_pos he.ne')] with L hL hLs
  set Tc : Ω → ℝ := ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) with hTc
  set W : Ω → WinIdx K → ℝ := fun ω => resFieldW K (n2Emb γ α L r X ω) with hW
  set Y := n2LatC X r
  set R := n2RadR γ α L r K X
  set ρ : Ω → ℝ → ℝ := fun ω => (R ω).2 with hρ
  have hYm : Measurable Y := measurable_n2LatC hX hr
  have hRm : AEMeasurable R P := aemeasurable_n2RadR hα hr hX hL K
  have hTm : AEMeasurable Tc P := hRm.fst
  have hρm : AEMeasurable ρ P := hRm.snd
  have hWm : AEMeasurable W P := aemeasurable_resFieldW_n2Emb hα hr hX K hK
  have hFm : AEMeasurable (fun ω => heartFW γ r K (Y ω, R ω)) P :=
    (measurable_heartFW γ r K hK).comp_aemeasurable (hYm.aemeasurable.prodMk hRm)
  set M := (P.map Tc).prod (P.map ρ) with hM
  -- (1) the model decomposition, for the pair and for the window alone
  have hdec : ∀ i, ∀ᵐ ω ∂P, ω ∈ {ω | S + 1 ≤ Tc ω} → W ω i = heartFW γ r K (Y ω, R ω) i := by
    intro i
    filter_upwards [hH3 γ α r P X hγ hγ2 hα hr hX K hK L hL i] with ω hω hmem
    show resFieldW K (n2Emb γ α L r X ω) i = _
    rw [hω hmem, heartFW_n2LatC]
  have ecomp : {ω | S + 1 ≤ Tc ω}ᶜ = {ω | Tc ω < S + 1} := by
    ext ω; simp only [mem_compl_iff, mem_setOf_eq, not_le]
  have t1p : TV.tvDist (P.map fun ω => (W ω, Tc ω))
      (P.map fun ω => (heartFW γ r K (Y ω, R ω), Tc ω)) ≤ P {ω | Tc ω < S + 1} := by
    rw [← ecomp]; exact twin_tvDist_pair_le hWm hFm hTm _ hdec
  have t1 : TV.tvDist (P.map W) (P.map fun ω => heartFW γ r K (Y ω, R ω)) ≤
      P {ω | Tc ω < S + 1} := by
    rw [← ecomp]; exact tvDist_map_le_of_coord hWm hFm _ hdec
  -- (2) the lateral defect and its average
  set δ : ℝ × (ℝ → ℝ) → ℝ≥0∞ := fun t =>
    TV.tvDist (P.map fun ω => latWinW K (r * Real.exp (-t.1)) (Y ω)) ν with hδ
  have hlat : ∀ t : ℝ × (ℝ → ℝ), (P.map Y).map (fun y => heartFW γ r K (y, t)) =
      (P.map fun ω => latWinW K (r * Real.exp (-t.1)) (Y ω)).map
        fun v => v + heartPsiW (Qc γ) K t.2 := by
    intro t
    have htr : Measurable fun v : WinIdx K → ℝ => v + heartPsiW (Qc γ) K t.2 :=
      Measurable.of_eval fun i => (measurable_pi_apply i).add_const _
    have hm1 : Measurable fun y : FieldSample => heartFW γ r K (y, t) :=
      (measurable_heartFW γ r K hK).comp (measurable_id.prodMk measurable_const)
    have hm2 : Measurable fun ω => latWinW K (r * Real.exp (-t.1)) (Y ω) :=
      ((measurable_latWinW_joint K hK).comp (measurable_const.prodMk measurable_id)).comp hYm
    rw [Measure.map_map hm1 hYm, Measure.map_map htr hm2]
    rfl
  have hδint : ∫⁻ t, δ t ∂(P.map R) ≤ ε / 2 / 2 / 2 + P {ω | Tc ω < T0} := by
    have hs : MeasurableSet {t : ℝ × (ℝ → ℝ) | t.1 < T0} :=
      measurableSet_lt measurable_fst measurable_const
    have hb : ∀ t, δ t ≤ ε / 2 / 2 / 2 + {t : ℝ × (ℝ → ℝ) | t.1 < T0}.indicator 1 t := by
      intro t
      by_cases ht : t.1 < T0
      · rw [indicator_of_mem (s := {t : ℝ × (ℝ → ℝ) | t.1 < T0}) ht]
        exact TV.tvDist_le_one.trans le_add_self
      · rw [indicator_of_notMem (s := {t : ℝ × (ℝ → ℝ) | t.1 < T0}) ht]
        have hδt : δ t = TV.tvDist (P.map fun ω => latWinW K (r * Real.exp (-t.1)) (n2LatY X r ω))
            (P''.map (latY''W K X'')) := by
          simp only [hδ, Y, latWinW_n2LatC, hνdef]
        rw [hδt]
        exact (hu (hscale t.1 (not_lt.1 ht))).trans le_self_add
    calc ∫⁻ t, δ t ∂(P.map R) ≤ ∫⁻ t, (ε / 2 / 2 / 2 + {t : ℝ × (ℝ → ℝ) | t.1 < T0}.indicator 1 t)
          ∂(P.map R) := lintegral_mono hb
      _ = ε / 2 / 2 / 2 + P {ω | Tc ω < T0} := by
        rw [lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_one hs,
          measure_univ, mul_one, Measure.map_apply_of_aemeasurable hRm hs]
        rfl
  have hfst : ∀ (μ : Measure (ℝ → ℝ)) [IsProbabilityMeasure μ], (ν.prod μ).map Prod.fst = ν := by
    intro μ _; rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hfst' : ∀ (μ : Measure (ℝ × (ℝ → ℝ))) [IsProbabilityMeasure μ],
      (ν.prod μ).map Prod.fst = ν := by
    intro μ _; rw [Measure.map_fst_prod, measure_univ, one_smul]
  -- (3) mixing for the pair, against `ν ⊗ (law Tc ⊗ law ρ)`
  have hIpM : IndepFun (Prod.fst : (WinIdx K → ℝ) × (ℝ × (ℝ → ℝ)) → _) Prod.snd (ν.prod M) :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have hFp : Measurable fun p : FieldSample × (ℝ × (ℝ → ℝ)) => (heartFW γ r K p, p.2.1) :=
    (measurable_heartFW γ r K hK).prodMk (measurable_fst.comp measurable_snd)
  have hF''p : Measurable fun p : (WinIdx K → ℝ) × (ℝ × (ℝ → ℝ)) =>
      (heartWW γ K (p.1, p.2.2), p.2.1) :=
    ((measurable_heartWW γ K).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.comp measurable_snd)
  have t2 := tvDist_indep_mix_le hYm.aemeasurable hRm measurable_fst.aemeasurable
    measurable_snd.aemeasurable (indepFun_n2LatC_n2RadR hα hr hX hL K) hIpM hFp hF''p
    measurable_id δ (fun t => by
      rw [hfst']
      show TV.tvDist ((P.map Y).map (fun y => (heartFW γ r K (y, t), t.1)))
        (ν.map fun v => (v + heartPsiW (Qc γ) K t.2, t.1)) ≤ δ t
      have htr : Measurable fun v : WinIdx K → ℝ => (v + heartPsiW (Qc γ) K t.2, t.1) :=
        (Measurable.of_eval fun i => (measurable_pi_apply i).add_const _).prodMk measurable_const
      have e : (P.map Y).map (fun y => (heartFW γ r K (y, t), t.1)) =
          ((P.map fun ω => latWinW K (r * Real.exp (-t.1)) (Y ω)).map
            fun v => (v + heartPsiW (Qc γ) K t.2, t.1)) := by
        have hm2 : Measurable fun ω => latWinW K (r * Real.exp (-t.1)) (Y ω) :=
          ((measurable_latWinW_joint K hK).comp (measurable_const.prodMk measurable_id)).comp hYm
        have hm1 : Measurable fun y : FieldSample => (heartFW γ r K (y, t), t.1) :=
          ((measurable_heartFW γ r K hK).comp (measurable_id.prodMk measurable_const)).prodMk
            measurable_const
        rw [Measure.map_map hm1 hYm, Measure.map_map htr hm2]
        rfl
      rw [e]
      exact TV.tvDist_map_le htr)
  -- (4) mixing for the window alone, against `ν ⊗ law ρ`
  have hIpρ : IndepFun (Prod.fst : (WinIdx K → ℝ) × (ℝ → ℝ) → _) Prod.snd (ν.prod (P.map ρ)) :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have t3 := tvDist_indep_mix_le hYm.aemeasurable hRm measurable_fst.aemeasurable
    measurable_snd.aemeasurable (indepFun_n2LatC_n2RadR hα hr hX hL K) hIpρ
    (measurable_heartFW γ r K hK) (measurable_heartWW γ K) measurable_snd δ (fun t => by
      rw [hfst, hlat t]
      have htr : Measurable fun v : WinIdx K → ℝ => v + heartPsiW (Qc γ) K t.2 :=
        Measurable.of_eval fun i => (measurable_pi_apply i).add_const _
      exact TV.tvDist_map_le htr)
  have hRρ : (P.map R).map Prod.snd = P.map ρ :=
    AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hRm
  rw [hRρ, Measure.map_snd_prod, measure_univ, one_smul, TV.tvDist_self, add_zero] at t3
  rw [Measure.map_id, Measure.map_snd_prod, measure_univ, one_smul] at t2
  -- (5) the Brownian defect
  have tD : TV.tvDist (P.map R) M ≤ TV.tvDist (P.map fun ω => (ρ ω, Tc ω))
      ((P.map ρ).prod (P.map Tc)) := by
    have e1 : P.map R = (P.map fun ω => (ρ ω, Tc ω)).map Prod.swap := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable (hρm.prodMk hTm)]
      rfl
    rw [e1, hM, ← Measure.prod_swap]
    exact TV.tvDist_map_le measurable_swap
  -- (6) the product identity and the assembly
  have hprod := twin_map_prod_prod ν (P.map Tc) (P.map ρ) (measurable_heartWW γ K)
  have t4 : TV.tvDist (((ν.prod (P.map ρ)).map (heartWW γ K)).prod (P.map Tc))
      ((P.map W).prod (P.map Tc)) ≤ (∫⁻ t, δ t ∂(P.map R)) + P {ω | Tc ω < S + 1} := by
    refine lscc_tvDist_prod_le.trans ?_
    rw [TV.tvDist_self, add_zero]
    refine (TV.tvDist_triangle (ν := P.map fun ω => heartFW γ r K (Y ω, R ω))).trans
      (add_le_add ?_ ?_)
    · rw [TV.tvDist_comm]; exact t3
    · rw [TV.tvDist_comm]; exact t1
  have hLs' : P {ω | Tc ω < S + 1} + (P {ω | Tc ω < T0} +
      TV.tvDist (P.map fun ω => (ρ ω, Tc ω)) ((P.map ρ).prod (P.map Tc))) ≤ ε / 2 / 2 / 2 := hLs
  have hsmall : ε / 2 / 2 / 2 + ε / 2 / 2 / 2 + (ε / 2 / 2 / 2 + ε / 2 / 2 / 2) = ε / 2 := by
    rw [ENNReal.add_halves, ENNReal.add_halves]
  calc TV.tvDist (P.map fun ω => (W ω, Tc ω)) ((P.map W).prod (P.map Tc))
      ≤ TV.tvDist (P.map fun ω => (W ω, Tc ω)) (P.map fun ω => (heartFW γ r K (Y ω, R ω), Tc ω)) +
        (TV.tvDist (P.map fun ω => (heartFW γ r K (Y ω, R ω), Tc ω))
          ((ν.prod M).map fun q => (heartWW γ K (q.1, q.2.2), q.2.1)) +
        TV.tvDist ((ν.prod M).map fun q => (heartWW γ K (q.1, q.2.2), q.2.1))
          ((P.map W).prod (P.map Tc))) :=
        TV.tvDist_triangle.trans (add_le_add le_rfl TV.tvDist_triangle)
    _ ≤ P {ω | Tc ω < S + 1} + ((∫⁻ t, δ t ∂(P.map R) + TV.tvDist (P.map R) M) +
        ((∫⁻ t, δ t ∂(P.map R)) + P {ω | Tc ω < S + 1})) := by
        refine add_le_add t1p (add_le_add t2 ?_)
        rw [hM, hprod]; exact t4
    _ ≤ P {ω | Tc ω < S + 1} + (((ε / 2 / 2 / 2 + P {ω | Tc ω < T0}) +
          TV.tvDist (P.map fun ω => (ρ ω, Tc ω)) ((P.map ρ).prod (P.map Tc))) +
        ((ε / 2 / 2 / 2 + P {ω | Tc ω < T0}) + P {ω | Tc ω < S + 1})) :=
        add_le_add le_rfl (add_le_add (add_le_add hδint tD) (add_le_add hδint le_rfl))
    _ = (ε / 2 / 2 / 2 + ε / 2 / 2 / 2) + ((P {ω | Tc ω < S + 1} + (P {ω | Tc ω < T0} +
          TV.tvDist (P.map fun ω => (ρ ω, Tc ω)) ((P.map ρ).prod (P.map Tc)))) +
          (P {ω | Tc ω < S + 1} + P {ω | Tc ω < T0})) := by ring
    _ ≤ (ε / 2 / 2 / 2 + ε / 2 / 2 / 2) + (ε / 2 / 2 / 2 + ε / 2 / 2 / 2) := by
        refine add_le_add le_rfl (add_le_add hLs' ?_)
        refine le_trans ?_ hLs'
        gcongr
        exact le_self_add
    _ = ε / 2 := hsmall
    _ ≤ ε := ENNReal.half_le_self

end D3Plus
end QuantumZipper
