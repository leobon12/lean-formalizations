import QuantumZipper.Proofs.Zipper.T13Hard3Defs
import QuantumZipper.Proofs.Zipper.T13Hard3RemRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD3: `LSCCHeartStmt` from the window/hitting-time independence and the hitting spread

**Audit.** The existing reduction of `LSCCHeartStmt` through `LSCCIndWinStmt` /
`LSCCIndTripleStmt` asks for asymptotic independence of the embedded window (resp. the canonical
data) from the remainder `R_L = lsccR` of the log scale. But on the window event `R_L` is a
*function of the window*: `R_L = log r + log (scaleSur γ 0 K (window, 0))`
(`n2_scale_transfer`, `D3PlusN2ModelLocDet.lean`), whose limit law (that of the wedge) is not a
point mass; so the joint law stays at positive TV distance from the product of the marginals, and
both nodes are **false**. (They are also not needed.)

**Correct route** (Duplantier–Miller–Sheffield arXiv:1409.7055, proof of Props. 4.7–4.8,
pp. 77–79; Sheffield arXiv:1012.4797, proof of Prop. 1.6, p. 25). Write `W_L` for the restricted
window of the circle-average embedded model field and `T_L` for the embedding time. On the good
window event, off events of vanishing probability,

  `pairN1 L = Φ_K (W_L, T_L)`,  `Φ_K (v, t) = (gKW v, log r + log scaleSur(v) − t)`

(`N2Z-MODELLOC` for the first component, the remainder readout `LSCCRemReadStmt` for the second).
Hence `d_TV(pair_L, pair_{L+c})` is at most the bad-window probabilities, the two independence
defects `d_TV(law (W, T), law W ⊗ law T)` at `L` and `L + c` (**`LSCCTWinIndStmt`**, the strong
Markov / Williams step of DMS Prop. 4.7), `d_TV(law W_L, law W_{L+c})` (→ 0 by the proved
`n2ZHeartWinStmt_holds`) and `d_TV(law T_L, law T_{L+c})` (→ 0 by **`HitLevSpreadStmt`**).

Proved here: `D3Plus.lsccHeart_of_tWin`. Own elementary glue (coupling inequality, data
processing, TV of products).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **Node LSCC-TWIN-IND (strong Markov at the embedding time).** The restricted window of the
circle-average embedded model field is asymptotically independent of the embedding time `T_L`.
Source: Duplantier–Miller–Sheffield arXiv:1409.7055, Prop. 4.7 and its proof (p. 78: the field
after the embedding time is independent of it; the pre-hitting segment seen from `T_L` is
asymptotically independent of `T_L`, Williams path decomposition). -/
def LSCCTWinIndStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ K : ℕ, 0 < K → Tendsto (fun L => TV.tvDist
      (P.map fun ω => (resFieldW K (n2Emb γ α L r X ω),
        ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω))
      ((P.map fun ω => resFieldW K (n2Emb γ α L r X ω)).prod
        (P.map fun ω => ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω))) atTop (𝓝 0)

/-- The readout map of the rich zoomed pair from the restricted window and the embedding time. -/
def heartPhi (γ r : ℝ) (K R : ℕ) (p : (WinIdx K → ℝ) × ℝ) : ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ :=
  (gKW γ K R p.1, Real.log r + Real.log (scaleSur γ 0 K (liftWin K p.1, 0)) - p.2)

theorem measurable_heartPhi (γ r : ℝ) (K R : ℕ) : Measurable (heartPhi γ r K R) :=
  ((measurable_gKW γ K R).comp measurable_fst).prodMk
    ((measurable_const.add (Real.measurable_log.comp ((measurable_scaleSur γ 0 K).comp
      ((measurable_liftWin K).comp measurable_fst |>.prodMk measurable_const)))).sub measurable_snd)

/-- The pointwise readout: on the good window event, where the rich data and the remainder are
read off the window, the rich zoomed pair is `heartPhi (W_L, T_L)`. -/
theorem pairN1_eq_heartPhi {γ α r L : ℝ} {K R : ℕ} {Ω : Type*} {X : Ω → FieldSample} {ω : Ω}
    (h1 : TmRichN1 γ r R L (localZ X r ω, circData α fun _ => 0) =
      gK γ K R (resField K (n2Emb γ α L r X ω)))
    (h2 : lsccR γ r α L X ω =
      Real.log r + Real.log (scaleSur γ 0 K (resField K (n2Emb γ α L r X ω), 0))) :
    pairN1 γ r R L (localZ X r ω, circData α fun _ => 0) =
      heartPhi γ r K R (resFieldW K (n2Emb γ α L r X ω),
        ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω) := by
  set y := n2Emb γ α L r X ω
  have hv : ∀ i, resFieldW K y i = y (winIdx K i) := fun i => rfl
  have hS : scaleSur γ 0 (K : ℝ) (liftWin K (resFieldW K y), 0) =
      scaleSur γ 0 (K : ℝ) (resField K y, 0) :=
    scaleSur_eq_of_locModel_eq ((locModel_liftWin γ hv).symm.trans (by rfl))
  refine Prod.ext ?_ ?_
  · simp only [pairN1, heartPhi]
    rw [h1, gKW_eq_gK_of_resField]
  · simp only [pairN1, heartPhi]
    rw [hS, ← h2]
    simp only [lsccR, lsccS]
    ring

/-- **Abstract TV bound for two readouts through a common map** (own elementary glue: coupling
inequality `tvDist_map_le_of_ae_eq_off`, data processing `TV.tvDist_map_le`, triangle inequality
and `lscc_tvDist_prod_le`). -/
theorem tvDist_readout_le {Ω V E : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] (Φ : V × ℝ → E)
    (hΦ : Measurable Φ) {p p' : Ω → E} {w w' : Ω → V} {t t' : Ω → ℝ}
    (hp : AEMeasurable p P) (hp' : AEMeasurable p' P) (hw : AEMeasurable w P)
    (hw' : AEMeasurable w' P) (ht : AEMeasurable t P) (ht' : AEMeasurable t' P)
    (Bd Bd' : Set Ω) (hB : ∀ ω, ω ∉ Bd → p ω = Φ (w ω, t ω))
    (hB' : ∀ ω, ω ∉ Bd' → p' ω = Φ (w' ω, t' ω)) :
    TV.tvDist (P.map p) (P.map p') ≤
      P Bd + (((TV.tvDist (P.map fun ω => (w ω, t ω)) ((P.map w).prod (P.map t)) +
        TV.tvDist (P.map fun ω => (w' ω, t' ω)) ((P.map w').prod (P.map t'))) +
        (TV.tvDist (P.map w) (P.map w') + TV.tvDist (P.map t) (P.map t'))) + P Bd') := by
  have hwt : AEMeasurable (fun ω => (w ω, t ω)) P := hw.prodMk ht
  have hwt' : AEMeasurable (fun ω => (w' ω, t' ω)) P := hw'.prodMk ht'
  have h1 : TV.tvDist (P.map p) (P.map fun ω => Φ (w ω, t ω)) ≤ P Bd :=
    tvDist_map_le_of_ae_eq_off hp (hΦ.comp_aemeasurable hwt) Bd (Eventually.of_forall hB)
  have h3 : TV.tvDist (P.map fun ω => Φ (w' ω, t' ω)) (P.map p') ≤ P Bd' := by
    rw [TV.tvDist_comm]
    exact tvDist_map_le_of_ae_eq_off hp' (hΦ.comp_aemeasurable hwt') Bd' (Eventually.of_forall hB')
  have e1 : (P.map fun ω => Φ (w ω, t ω)) = (P.map fun ω => (w ω, t ω)).map Φ :=
    (AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hwt).symm
  have e2 : (P.map fun ω => Φ (w' ω, t' ω)) = (P.map fun ω => (w' ω, t' ω)).map Φ :=
    (AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hwt').symm
  have h2 : TV.tvDist (P.map fun ω => Φ (w ω, t ω)) (P.map fun ω => Φ (w' ω, t' ω)) ≤
      ((TV.tvDist (P.map fun ω => (w ω, t ω)) ((P.map w).prod (P.map t)) +
        TV.tvDist (P.map fun ω => (w' ω, t' ω)) ((P.map w').prod (P.map t'))) +
        (TV.tvDist (P.map w) (P.map w') + TV.tvDist (P.map t) (P.map t'))) := by
    rw [e1, e2]
    refine (TV.tvDist_map_le hΦ).trans ?_
    set J := P.map fun ω => (w ω, t ω)
    set J' := P.map fun ω => (w' ω, t' ω)
    set Q := (P.map w).prod (P.map t)
    set Q' := (P.map w').prod (P.map t')
    have hQ : TV.tvDist Q Q' ≤ TV.tvDist (P.map w) (P.map w') + TV.tvDist (P.map t) (P.map t') :=
      lscc_tvDist_prod_le
    calc TV.tvDist J J' ≤ TV.tvDist J Q + TV.tvDist Q J' := TV.tvDist_triangle
      _ ≤ TV.tvDist J Q + (TV.tvDist Q Q' + TV.tvDist Q' J') :=
          add_le_add le_rfl TV.tvDist_triangle
      _ = (TV.tvDist J Q + TV.tvDist J' Q') + TV.tvDist Q Q' := by
          rw [TV.tvDist_comm (μ := Q') (ν := J')]; ring
      _ ≤ _ := add_le_add le_rfl hQ
  calc TV.tvDist (P.map p) (P.map p')
      ≤ TV.tvDist (P.map p) (P.map fun ω => Φ (w ω, t ω)) +
          TV.tvDist (P.map fun ω => Φ (w ω, t ω)) (P.map p') := TV.tvDist_triangle
    _ ≤ TV.tvDist (P.map p) (P.map fun ω => Φ (w ω, t ω)) +
          (TV.tvDist (P.map fun ω => Φ (w ω, t ω)) (P.map fun ω => Φ (w' ω, t' ω)) +
            TV.tvDist (P.map fun ω => Φ (w' ω, t' ω)) (P.map p')) :=
        add_le_add le_rfl TV.tvDist_triangle
    _ ≤ _ := add_le_add h1 (add_le_add h2 h3)

/-- **LSCC-HEART from the window/hitting-time independence and the hitting-time spread.** All
other inputs are proved: the good-window bound (`lsccBadWinStmt_holds`), the readouts
(`n2ZModelLocStmt_holds`, `lsccRemRead_holds`), the window convergence (`n2ZHeartWinStmt_holds`). -/
theorem lsccHeart_of_tWin (hJ : LSCCTWinIndStmt) (hHit : HitLevSpreadStmt) : LSCCHeartStmt := by
  intro γ α r Ω _ P _ X c hγ hγ2 hα hr hX R
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set e1 := ε / 2 with he1d
  set e2 := e1 / 2 with he2d
  set e3 := e2 / 2 with he3d
  set a := e3 / 2 with had
  have he1 : 0 < e1 := ENNReal.half_pos hε.ne'
  have he2 : 0 < e2 := ENNReal.half_pos he1.ne'
  have he3 : 0 < e3 := ENNReal.half_pos he2.ne'
  have he4 : 0 < a := ENNReal.half_pos he3.ne'
  obtain ⟨K, hK, hbad⟩ := lsccBadWinStmt_holds γ α r P X R hγ hγ2 hα hr hX _ he3
  obtain ⟨Ω', m', P', Y', B', hP', hY', -⟩ :=
    NonVacuity.exists_wedge_indep_BM_uncond (γ := γ) hα
  obtain ⟨-, Ω'', _, P'', X'', A, hP'', hX'', hA, hI, -⟩ := hY'
  obtain ⟨hWm, hWtv⟩ :=
    n2ZHeartWinStmt_holds γ α r P X P'' X'' A hγ hγ2 hα hr hX hX'' hA hI K hK
  have hML := n2ZModelLocStmt_holds γ α r P X hγ hγ2 hα hr hX K R hK
  have hRR := lsccRemRead_holds γ α r P X hγ hγ2 hα hr hX K R hK
  have hJK := hJ γ α r P X hγ hγ2 hα hr hX K hK
  have hH := lsccSpreadHit_of_pure hHit γ α r P X c hγ hγ2 hα hr hX
  have sh : Tendsto (fun L : ℝ => L + c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_id
  have ev4 : ∀ {f : ℝ → ℝ≥0∞}, Tendsto f atTop (𝓝 0) →
      ∀ᶠ L in atTop, f L ≤ a ∧ f (L + c) ≤ a := fun hf =>
    (ENNReal.tendsto_nhds_zero.1 hf _ he4).and
      (sh.eventually (ENNReal.tendsto_nhds_zero.1 hf _ he4))
  -- the exceptional set at level `L`
  let Bd : ℝ → Set Ω := fun L =>
    {ω | resField K (n2Emb γ α L r X ω) ∉ n2Good γ K R} ∪
      ({ω | resField K (n2Emb γ α L r X ω) ∈ n2Good γ K R ∧
          TmRichN1 γ r R L (localZ X r ω, circData α fun _ => 0) ≠
            gK γ K R (resField K (n2Emb γ α L r X ω))} ∪
        {ω | resField K (n2Emb γ α L r X ω) ∈ n2Good γ K R ∧ lsccR γ r α L X ω ≠
          Real.log r + Real.log (scaleSur γ 0 K (resField K (n2Emb γ α L r X ω), 0))})
  have hBd : ∀ L ω, ω ∉ Bd L → pairN1 γ r R L (localZ X r ω, circData α fun _ => 0) =
      heartPhi γ r K R (resFieldW K (n2Emb γ α L r X ω),
        ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω) := by
    intro L ω hω
    have hg : resField K (n2Emb γ α L r X ω) ∈ n2Good γ K R := by
      by_contra h; exact hω (Or.inl h)
    have h1 : TmRichN1 γ r R L (localZ X r ω, circData α fun _ => 0) =
        gK γ K R (resField K (n2Emb γ α L r X ω)) := by
      by_contra h; exact hω (Or.inr (Or.inl ⟨hg, h⟩))
    have h2 : lsccR γ r α L X ω =
        Real.log r + Real.log (scaleSur γ 0 K (resField K (n2Emb γ α L r X ω), 0)) := by
      by_contra h; exact hω (Or.inr (Or.inr ⟨hg, h⟩))
    exact pairN1_eq_heartPhi h1 h2
  have hPB : ∀ L, P (Bd L) ≤ P {ω | resField K (n2Emb γ α L r X ω) ∉ n2Good γ K R} +
      (P {ω | resField K (n2Emb γ α L r X ω) ∈ n2Good γ K R ∧
          TmRichN1 γ r R L (localZ X r ω, circData α fun _ => 0) ≠
            gK γ K R (resField K (n2Emb γ α L r X ω))} +
        P {ω | resField K (n2Emb γ α L r X ω) ∈ n2Good γ K R ∧ lsccR γ r α L X ω ≠
          Real.log r + Real.log (scaleSur γ 0 K (resField K (n2Emb γ α L r X ω), 0))}) :=
    fun L => (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
  have hpm : ∀ L, AEMeasurable (fun ω => pairN1 γ r R L (localZ X r ω, circData α fun _ => 0)) P :=
    fun L => ((measurable_pairN1 γ r R L).comp
      ((measurable_localZ hX hr).prodMk measurable_const)).aemeasurable
  filter_upwards [hbad, sh.eventually hbad, ev4 hML, ev4 hRR, ev4 hJK, ev4 hWtv,
    ENNReal.tendsto_nhds_zero.1 hH _ he3] with L hb1 hb2 hm hrr hj hw hh
  have key := tvDist_readout_le (P := P) (heartPhi γ r K R) (measurable_heartPhi γ r K R)
    (hpm L) (hpm (L + c)) (hWm L) (hWm (L + c)) (aemeasurable_Tc_zRadB hX hr)
    (aemeasurable_Tc_zRadB hX hr) (Bd L) (Bd (L + c)) (hBd L) (hBd (L + c))
  have h43 : a + a = e3 := ENNReal.add_halves _
  have h32 : e3 + e3 = e2 := ENNReal.add_halves _
  have h21 : e2 + e2 = e1 := ENNReal.add_halves _
  have h10 : e1 + e1 = ε := ENNReal.add_halves _
  have hWb : TV.tvDist (P.map fun ω => resFieldW K (n2Emb γ α L r X ω))
      (P.map fun ω => resFieldW K (n2Emb γ α (L + c) r X ω)) ≤ a + a :=
    TV.tvDist_triangle.trans (add_le_add hw.1 (TV.tvDist_comm.le.trans hw.2))
  have hB1 : P (Bd L) ≤ e2 := by
    refine (hPB L).trans ((add_le_add hb1 (add_le_add hm.1 hrr.1)).trans ?_)
    rw [h43, h32]
  have hB2 : P (Bd (L + c)) ≤ e2 := by
    refine (hPB (L + c)).trans ((add_le_add hb2 (add_le_add hm.2 hrr.2)).trans ?_)
    rw [h43, h32]
  have hM := add_le_add (add_le_add hj.1 hj.2) (add_le_add hWb hh)
  rw [h43, h32] at hM
  have hM' := hM.trans ((add_le_add (ENNReal.half_le_self (a := e2)) le_rfl).trans h21.le)
  refine key.trans ((add_le_add hB1 (add_le_add hM' hB2)).trans (le_of_eq ?_))
  rw [show e2 + (e1 + e2) = e1 + (e2 + e2) by ring, h21, h10]

/-- **Rich D3⁺(ii) from LSCC-TWIN-IND and the hitting-time spread.** -/
theorem d3PlusIIRich_of_tWin (hJ : LSCCTWinIndStmt) (hHit : HitLevSpreadStmt) :
    D3PlusIIStmtRich :=
  d3PlusIIRich_of_lscConst (lscConstGen_locFieldFull_of_heart (lsccHeart_of_tWin hJ hHit))

/-- **Proposed sub-leaf of LSCC-TWIN-IND (pure Brownian form): the path seen from the first
passage time is asymptotically independent of that time.** For the drifted path
`Xc = L + √2 b + (α − Q)·` and its first passage time `Tc` below `0`, the re-centred path
`s ↦ Xc (Tc + s)`, truncated at `−S`, is asymptotically independent of `Tc` in total variation
as the level `L → ∞`. Source: strong Markov property for `s ≥ 0`; D. Williams, *Path decomposition
and continuity of local time for one-dimensional diffusions*, Proc. LMS 28 (1974), Thm 2.2
(time reversal from a first passage time) for `s < 0`; Duplantier–Miller–Sheffield
arXiv:1409.7055, proof of Prop. 4.7 (p. 78). Together with the lateral scale invariance of the
free field (the window's lateral part is independent of the radial path) it gives
`LSCCTWinIndStmt`. -/
def HitPathIndStmt : Prop :=
  ∀ (α Q : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ≥0 → Ω → ℝ), IsBrownianReal b P → α < Q → ∀ S : ℝ, 0 ≤ S →
    Tendsto (fun L => TV.tvDist
      (P.map fun ω => (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q b L ω),
        ZoomRadial.Tc α Q L b ω))
      ((P.map fun ω => ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q b L ω)).prod
        (P.map fun ω => ZoomRadial.Tc α Q L b ω))) atTop (𝓝 0)

end D3Plus
end QuantumZipper
