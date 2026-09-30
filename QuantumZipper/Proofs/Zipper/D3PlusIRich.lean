import QuantumZipper.Proofs.Zipper.D3PlusN1Core

/-!
# D3⁺(i) for the rich local data (decision D25): the conditioning layer

`d3PlusI_of_core` (`D3PlusIMarkov.lean`) needs measurability of `f ↦ TV(κ f, ν)`, proved there
(`measurable_tvDist_kernel`) only for a countably generated target. The rich local data of D25
take values in `(ℕ → ℝ) × (TestFun H → ℝ)`, whose product σ-algebra is not countably generated.
Here the measurability of the TV distance is **not needed at all**:

* `tendsto_lintegral_of_ae_tendsto_nonmeas`: if `m L ≤ 1` (not necessarily measurable) and
  `m L ω → 0` for a.e. `ω` as `L → ∞`, then the (lower) Lebesgue integrals `∫⁻ m L → 0`.
  Along any sequence `L_n → ∞` pick measurable `g_n ≤ m L_n` with the same lower integral
  (`exists_measurable_le_lintegral_eq`), and apply dominated convergence to `g_n`.
* In the two-sided bound only the *other* summand must be measurable for additivity of the lower
  integral (`lintegral_add_left`); those summands (`ω ↦ ∫ Φ(ω, ·) dν`, `ω ↦ ∫ Φ(ω, Tm_L(·, F ω))`)
  are measurable by joint measurability of `Φ`.

This gives `eventually_two_sided_of_factor_exc_nm` (as `eventually_two_sided_of_factor_exc`
without any measurability of the TV bound), hence `d3PlusIRich_of_N2 : D3PlusIN2RichStmt →
D3PlusIStmtRich` from `n1_rich`. Own elementary arguments (AGENT_GUIDE cost rule); the lower
integral device is mathlib's `exists_measurable_le_lintegral_eq`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **Dominated convergence for non-measurable bounded functions** (lower integrals; own
elementary proof). -/
theorem tendsto_lintegral_of_ae_tendsto_nonmeas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (m : ℝ → Ω → ℝ≥0∞) (h1 : ∀ L ω, m L ω ≤ 1)
    (hm : ∀ᵐ ω ∂P, Tendsto (fun L => m L ω) atTop (𝓝 0)) :
    Tendsto (fun L => ∫⁻ ω, m L ω ∂P) atTop (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro Ls hLs
  choose g hg hgle hgeq using fun n => exists_measurable_le_lintegral_eq P (m (Ls n))
  have hfun : (fun L => ∫⁻ ω, m L ω ∂P) ∘ Ls = fun n => ∫⁻ ω, g n ω ∂P := funext hgeq
  rw [hfun]
  have h := tendsto_lintegral_of_dominated_convergence (μ := P) (F := g) (f := fun _ => 0)
    (fun _ => 1) hg (fun n => ae_of_all _ fun ω => (hgle n ω).trans (h1 _ _))
    (by simp [measure_ne_top]) (by
      filter_upwards [hm] with ω hω
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hω.comp hLs)
        (fun n => bot_le) (fun n => hgle n ω))
  simpa using h

/-- **Conditioning layer without measurability of the TV distance** (own elementary proof; the
argument of `eventually_two_sided_of_factor`, with `tendsto_lintegral_of_ae_tendsto_nonmeas` in
place of dominated convergence for a measurable TV bound). -/
theorem eventually_two_sided_of_factor_nm {Ω S T E Ω' : Type*} {m𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace E]
    [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m𝒢 ≤ mΩ)
    {Z : Ω → S} (hZ : Measurable Z)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m𝒢 P)
    {F : Ω → T} (hF : Measurable[m𝒢] F) (Tm : ℝ → S × T → E) (hT : ∀ L, Measurable (Tm L))
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {W : Ω' → E} (hW : AEMeasurable W P')
    (hd : ∀ᵐ ω ∂P, Tendsto (fun L => TV.tvDist ((P.map Z).map fun s => Tm L (s, F ω))
      (P'.map W)) atTop (𝓝 0)) {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ L in atTop, ∀ Φ : Ω × E → ℝ≥0∞, Measurable[m𝒢.prod inferInstance] Φ →
      (∀ p, Φ p ≤ 1) →
      ∫⁻ ω, Φ (ω, Tm L (Z ω, F ω)) ∂P ≤ ∫⁻ ω, ∫⁻ ω', Φ (ω, W ω') ∂P' ∂P + η ∧
      ∫⁻ ω, ∫⁻ ω', Φ (ω, W ω') ∂P' ∂P ≤ ∫⁻ ω, Φ (ω, Tm L (Z ω, F ω)) ∂P + η := by
  set ν := P'.map W with hν
  set μZ := P.map Z with hμZ
  have hFm : Measurable[mΩ] F := hF.mono hm le_rfl
  have hsl : ∀ L (f : T), Measurable fun s => Tm L (s, f) := fun L f =>
    (hT L).comp (measurable_id.prodMk measurable_const)
  set m : ℝ → Ω → ℝ≥0∞ := fun L ω => min (TV.tvDist (μZ.map fun s => Tm L (s, F ω)) ν) 1
    with hm_def
  have hlim : Tendsto (fun L => ∫⁻ ω, m L ω ∂P) atTop (𝓝 0) :=
    tendsto_lintegral_of_ae_tendsto_nonmeas m (fun _ _ => min_le_right _ _) (by
      filter_upwards [hd] with ω hω
      simpa using hω.min (tendsto_const_nhds (x := (1 : ℝ≥0∞))))
  have hid : @Measurable Ω Ω mΩ m𝒢 id := fun s hs => hm s hs
  filter_upwards [hlim.eventually (gt_mem_nhds hη)] with L hL Φ hΦ h1
  have hΦ' : Measurable Φ :=
    @Measurable.comp (Ω × E) (Ω × E) ℝ≥0∞ _ (m𝒢.prod inferInstance) _ _ _ hΦ
      (hid.prodMap measurable_id)
  have hsec : ∀ ω, Measurable fun y => Φ (ω, y) := fun ω => hΦ'.comp measurable_prodMk_left
  have hΨ : Measurable[m𝒢.prod inferInstance] fun q : Ω × S => Φ (q.1, Tm L (q.2, F q.1)) :=
    hΦ.comp (measurable_fst.prodMk ((hT L).comp (measurable_snd.prodMk (hF.comp measurable_fst))))
  have hΨ' : Measurable fun q : Ω × S => Φ (q.1, Tm L (q.2, F q.1)) :=
    hΦ'.comp (measurable_fst.prodMk ((hT L).comp (measurable_snd.prodMk
      (hFm.comp measurable_fst))))
  have ha : Measurable fun ω => ∫⁻ s, Φ (ω, Tm L (s, F ω)) ∂μZ := hΨ'.lintegral_prod_right'
  have hb : Measurable fun ω => ∫⁻ y, Φ (ω, y) ∂ν := hΦ'.lintegral_prod_right'
  have hlhs : ∫⁻ ω, Φ (ω, Tm L (Z ω, F ω)) ∂P = ∫⁻ ω, ∫⁻ s, Φ (ω, Tm L (s, F ω)) ∂μZ ∂P :=
    lintegral_comp_indep hm hZ hind hΨ
  have hrhs : ∫⁻ ω, ∫⁻ ω', Φ (ω, W ω') ∂P' ∂P = ∫⁻ ω, ∫⁻ y, Φ (ω, y) ∂ν ∂P :=
    lintegral_congr fun ω => (lintegral_map' (hsec ω).aemeasurable hW).symm
  have hpt : ∀ ω, ∫⁻ s, Φ (ω, Tm L (s, F ω)) ∂μZ ≤ ∫⁻ y, Φ (ω, y) ∂ν + m L ω ∧
      ∫⁻ y, Φ (ω, y) ∂ν ≤ ∫⁻ s, Φ (ω, Tm L (s, F ω)) ∂μZ + m L ω := fun ω => by
    have heq : ∫⁻ y, Φ (ω, y) ∂(μZ.map fun s => Tm L (s, F ω)) =
        ∫⁻ s, Φ (ω, Tm L (s, F ω)) ∂μZ := lintegral_map (hsec ω) (hsl L (F ω))
    have htv : TV.tvDist (μZ.map fun s => Tm L (s, F ω)) ν ≤ m L ω :=
      le_min le_rfl TV.tvDist_le_one
    have htv' : TV.tvDist ν (μZ.map fun s => Tm L (s, F ω)) ≤ m L ω :=
      TV.tvDist_comm.le.trans htv
    rw [← heq]
    exact ⟨(TV.lintegral_le_lintegral_add_tvDist (hsec ω) fun y => h1 _).trans
        (add_le_add le_rfl htv),
      (TV.lintegral_le_lintegral_add_tvDist (hsec ω) fun y => h1 _).trans
        (add_le_add le_rfl htv')⟩
  rw [hlhs, hrhs]
  constructor
  · calc ∫⁻ ω, ∫⁻ s, Φ (ω, Tm L (s, F ω)) ∂μZ ∂P
        ≤ ∫⁻ ω, (∫⁻ y, Φ (ω, y) ∂ν + m L ω) ∂P := lintegral_mono fun ω => (hpt ω).1
      _ = ∫⁻ ω, ∫⁻ y, Φ (ω, y) ∂ν ∂P + ∫⁻ ω, m L ω ∂P := lintegral_add_left hb _
      _ ≤ _ := by gcongr
  · calc ∫⁻ ω, ∫⁻ y, Φ (ω, y) ∂ν ∂P
        ≤ ∫⁻ ω, (∫⁻ s, Φ (ω, Tm L (s, F ω)) ∂μZ + m L ω) ∂P := lintegral_mono fun ω => (hpt ω).2
      _ = ∫⁻ ω, ∫⁻ s, Φ (ω, Tm L (s, F ω)) ∂μZ ∂P + ∫⁻ ω, m L ω ∂P := lintegral_add_left ha _
      _ ≤ _ := by gcongr

/-- **Conditioning layer with an exceptional event, without measurability of the TV distance**
(own elementary proof; the argument of `eventually_two_sided_of_factor_exc`). -/
theorem eventually_two_sided_of_factor_exc_nm {Ω S T E Ω' : Type*} {m𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace E]
    [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m𝒢 ≤ mΩ)
    {Z : Ω → S} (hZ : Measurable Z)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m𝒢 P)
    {F : Ω → T} (hF : Measurable[m𝒢] F)
    (V : ℝ → Ω → E) (Tm : ℝ → S × T → E) (hT : ∀ L, Measurable (Tm L))
    (B : ℝ → Set Ω) (hV : ∀ L, ∀ᵐ ω ∂P, ω ∉ B L → V L ω = Tm L (Z ω, F ω))
    (hB : Tendsto (fun L => P (B L)) atTop (𝓝 0))
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {W : Ω' → E} (hW : AEMeasurable W P')
    (hd : ∀ᵐ ω ∂P, Tendsto (fun L => TV.tvDist ((P.map Z).map fun s => Tm L (s, F ω))
      (P'.map W)) atTop (𝓝 0)) {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ L in atTop, ∀ Φ : Ω × E → ℝ≥0∞, Measurable[m𝒢.prod inferInstance] Φ →
      (∀ p, Φ p ≤ 1) →
      ∫⁻ ω, Φ (ω, V L ω) ∂P ≤ ∫⁻ ω, ∫⁻ ω', Φ (ω, W ω') ∂P' ∂P + η ∧
      ∫⁻ ω, ∫⁻ ω', Φ (ω, W ω') ∂P' ∂P ≤ ∫⁻ ω, Φ (ω, V L ω) ∂P + η := by
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have h := eventually_two_sided_of_factor_nm hm hZ hind hF Tm hT hW hd hη2
  filter_upwards [h, hB.eventually (gt_mem_nhds hη2)] with L hL hBL Φ hΦ h1
  obtain ⟨h1', h2'⟩ := hL Φ hΦ h1
  set U := toMeasurable P (B L) with hU
  have hUm : MeasurableSet U := measurableSet_toMeasurable _ _
  have hint : ∫⁻ ω, U.indicator 1 ω ∂P = P (B L) := by
    rw [lintegral_indicator_one hUm, hU, measure_toMeasurable]
  have hind1 : Measurable (U.indicator (1 : Ω → ℝ≥0∞)) := measurable_const.indicator hUm
  have key : ∀ᵐ ω ∂P, Φ (ω, V L ω) ≤ Φ (ω, Tm L (Z ω, F ω)) + U.indicator 1 ω ∧
      Φ (ω, Tm L (Z ω, F ω)) ≤ Φ (ω, V L ω) + U.indicator 1 ω := by
    filter_upwards [hV L] with ω hω
    by_cases hωU : ω ∈ U
    · rw [indicator_of_mem hωU]
      exact ⟨(h1 _).trans le_add_self, (h1 _).trans le_add_self⟩
    · rw [hω fun hb => hωU (subset_toMeasurable _ _ hb)]
      exact ⟨le_self_add, le_self_add⟩
  constructor
  · calc ∫⁻ ω, Φ (ω, V L ω) ∂P
        ≤ ∫⁻ ω, (Φ (ω, Tm L (Z ω, F ω)) + U.indicator 1 ω) ∂P :=
          lintegral_mono_ae (key.mono fun ω hω => hω.1)
      _ = ∫⁻ ω, Φ (ω, Tm L (Z ω, F ω)) ∂P + P (B L) := by
          rw [lintegral_add_right _ hind1, hint]
      _ ≤ (∫⁻ ω, ∫⁻ ω', Φ (ω, W ω') ∂P' ∂P + η / 2) + η / 2 := by gcongr
      _ = _ := by rw [add_assoc, ENNReal.add_halves]
  · calc ∫⁻ ω, ∫⁻ ω', Φ (ω, W ω') ∂P' ∂P
        ≤ ∫⁻ ω, Φ (ω, Tm L (Z ω, F ω)) ∂P + η / 2 := h2'
      _ ≤ ∫⁻ ω, (Φ (ω, V L ω) + U.indicator 1 ω) ∂P + η / 2 := by
          have := lintegral_mono_ae (key.mono fun ω hω => hω.2)
          exact add_le_add this le_rfl
      _ = ∫⁻ ω, Φ (ω, V L ω) ∂P + P (B L) + η / 2 := by
          rw [lintegral_add_right _ hind1, hint]
      _ ≤ ∫⁻ ω, Φ (ω, V L ω) ∂P + η / 2 + η / 2 := by gcongr
      _ = _ := by rw [add_assoc, ENNReal.add_halves]

/-- **Node N2 for D25's rich data** (as `D3PlusIN2Stmt`, with `TmRichN1` and `locFieldFull`):
a.s., the law of the zoomed local model built from an independent copy of the local part and the
frozen macroscopic data `macroF ω` converges in total variation to the law of the wedge's rich
local data. -/
def D3PlusIN2RichStmt : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g : Ω → ℂ → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Y' : Ω' → FieldSample),
    Setup γ α r ρ₀ P X Ξ g → IsQuantumWedge γ α Y' P' → ∀ R : ℕ,
      ∀ᵐ ω ∂P, Tendsto (fun L => TV.tvDist
        ((P.map (localZ X r)).map fun s => TmRichN1 γ r R L (s, macroF α r ρ₀ X g ω))
        (P'.map fun ω' => locFieldFull R (Y' ω'))) atTop (𝓝 0)

/-- **D3⁺(i) for the rich local data from N2** (N1 `n1_rich`, L2 independence, D3⁺(iii) for the
bad-scale event, and the conditioning layer `eventually_two_sided_of_factor_exc_nm`). -/
theorem d3PlusIRich_of_N2 (h : D3PlusIN2RichStmt) : D3PlusIStmtRich := by
  intro γ α r ρ₀ Ω _ P _ X E' _ Ξ g Ω' _ P' _ Y' hS hW R η hη
  obtain ⟨hε₀, hF, hT, hBm, hV, hWm⟩ := n1_rich hS hW R
  have hexc := eventually_two_sided_of_factor_exc_nm (condSigma_le hS)
    (measurable_localZ hS.hX hS.hr) (indep_localZ_condSigma hS) hF
    (fun L ω => locFieldFull R (canonicalOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r)))
    (TmRichN1 γ r R) hT (badScale γ α r (r / (R + 1)) ρ₀ X g)
    (fun L => ae_of_all _ (hV L)) (tendsto_prob_badScale hS hε₀ hBm) hWm
    (h γ α r ρ₀ P X Ξ g P' Y' hS hW R) hη
  filter_upwards [hexc] with L hL Φ hΦ h1
  exact hL Φ hΦ h1

/-- Hence D23's D3⁺(i) also follows from the rich N2. -/
theorem d3PlusI_of_N2Rich (h : D3PlusIN2RichStmt) : D3PlusIStmt :=
  d3PlusI_of_rich (d3PlusIRich_of_N2 h)

end D3Plus
end QuantumZipper
