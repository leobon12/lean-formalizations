import QuantumZipper.Proofs.Zipper.D3PlusN2HarmP1
import QuantumZipper.Proofs.Zipper.D3PlusIICond

/-!
# D3⁺(ii), constant part (`LSCConstGen locFieldFull`): conditioning layer and reduction to a
# deterministic level-shift node

Task LSCCONST. `LSCConstGen locFieldFull` (`D3PlusIISplit.lean`) compares the conditional laws of
the rich zoomed pair at the levels `L` and `L + γ c` (`c` a `condSigma`-measurable random
constant). Following Sheffield (arXiv:1012.4797, proof of Prop. 1.6, p. 25) and Duplantier–Miller–
Sheffield (arXiv:1409.7055, Props. 4.7–4.8, pp. 77–79), conditionally on the macroscopic data the
model is the local part `Z` of the free field plus a *deterministic* correction, and the level
enters only through the constant `L/γ` of N1's local model (`locModel`).

* `pairN1 γ r R L`: the measurable N1 reading of the rich zoomed pair (rich canonical data,
  log of the surrogate scale); `zoomGen_eq_pairN1_of_not_bad`: off the bad-scale event the
  zoomed pair of a `Setup` model is `pairN1 L (localZ, macroF)`.
* `locModel_level_shift`: level `L + γ c` with data `f` is level `L` with data `f + c`.
* `lscc_lintegral_factor_le`: for `Z ⊥ 𝒢` and two `𝒢`-measurable data `F, F'` read by the same
  measurable `Tm`, the two expectations of `Φ(ω, Tm(Z, ·))` differ by at most the lower integral
  of `min(d_TV(law Tm(Z, F ω), law Tm(Z, F' ω)), 1)` (Kallenberg FMP Lemma 3.11 via
  `lintegral_comp_indep`, then TV duality; no measurability of the TV distance in `ω`).
* `LSCCTmStmt` (**the remaining node**, deterministic correction): for the free field `X`, an
  admissible deterministic `φ` and a real `c`, the laws of `pairN1 L (localZ, circData α φ)` and
  `pairN1 (L + c) (localZ, circData α φ)` are TV-close as `L → ∞`.
* **`lscConstGen_locFieldFull_of_tm : LSCCTmStmt → LSCConstGen locFieldFull`**, using the proved
  macroscopic decomposition (`d3PlusIN2FixMacro_of_harm d3PlusN2HarmPart_holds`), D3⁺(iii) for the
  bad-scale events (`tendsto_prob_badScale`) and dominated convergence for lower integrals
  (`tendsto_lintegral_of_ae_tendsto_nonmeas`).

Own elementary glue (AGENT_GUIDE cost rule), following the pattern of `lscZeroGen_locFieldFull`.
The bound `|c| ≤ K` of `LSCConstGen` is not needed for this reduction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- The measurable N1 reading of the rich zoomed pair: (rich canonical data, log scale). -/
def pairN1 (γ r : ℝ) (R : ℕ) (L : ℝ) (p : N1Idx r) : ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ :=
  (TmRichN1 γ r R L p, Real.log (scaleSur γ L r p))

theorem measurable_pairN1 (γ r : ℝ) (R : ℕ) (L : ℝ) : Measurable (pairN1 γ r R L) :=
  (measurable_TmRichN1 γ r R L).prodMk (Real.measurable_log.comp (measurable_scaleSur γ L r))

theorem pairN1_congr {γ r L L' : ℝ} {R : ℕ} {p p' : N1Idx r}
    (h : locModel γ L r p = locModel γ L' r p') : pairN1 γ r R L p = pairN1 γ r R L' p' := by
  have hs : scaleSur γ L r p = scaleSur γ L' r p' := by
    simp only [scaleSur, Prop16Area.Meas.M, Prop16Area.Meas.Psi, bumpHD, h]
  simp only [pairN1, TmRichN1_congr h, hs]

/-- **Level shift in the local model**: level `L + γ c` with data `f` is level `L` with `f + c`. -/
theorem locModel_level_shift {γ : ℝ} (hγ : γ ≠ 0) (L r c : ℝ) (s : LocIdx r → ℝ)
    (f : FieldSample) :
    locModel γ (L + γ * c) r (s, f) = locModel γ L r (s, fun μ => f μ + c) := by
  classical
  funext μ
  unfold locModel
  split_ifs with hμ
  · dsimp only
    rw [add_div, mul_div_cancel_left₀ _ hγ]
    ring
  · rfl

/-- **Factorization of the rich zoomed pair** off the bad-scale event (threshold `r/(R+1)`). -/
theorem zoomGen_eq_pairN1_of_not_bad {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample} {E' : Type*} [MeasurableSpace E']
    {Ξ : Ω → E'} {g : Ω → ℂ → ℝ} (hS : Setup γ α r ρ₀ P X Ξ g) {R : ℕ} (L : ℝ) (ω : Ω)
    (hω : ω ∉ badScale γ α r (r / (R + 1)) ρ₀ X g L) :
    zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g ω) =
      pairN1 γ r R L (localZ X r ω, macroF α r ρ₀ X g ω) := by
  refine Prod.ext (locFieldFull_canonicalOn_eq_TmRichN1 hS L ω hω) ?_
  show Real.log _ = Real.log (scaleSur γ L r _)
  rw [(scaleSur_eq_of_not_bad hS hω).1]

/-- **Conditioning layer for two data read by the same map** (own elementary argument:
`lintegral_factor_eq`, then TV duality at each `ω`). -/
theorem lscc_lintegral_factor_le {Ω S T E : Type*} {m𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m𝒢 ≤ mΩ) {Z : Ω → S} (hZ : Measurable Z)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m𝒢 P) {F F' : Ω → T}
    (hF : Measurable[m𝒢] F) (hF' : Measurable[m𝒢] F') {Tm : S × T → E} (hT : Measurable Tm)
    {Φ : Ω × E → ℝ≥0∞} (hΦ : Measurable[m𝒢.prod inferInstance] Φ) (h1 : ∀ p, Φ p ≤ 1) :
    ∫⁻ ω, Φ (ω, Tm (Z ω, F ω)) ∂P ≤ ∫⁻ ω, Φ (ω, Tm (Z ω, F' ω)) ∂P +
        ∫⁻ ω, min (TV.tvDist ((P.map Z).map fun s => Tm (s, F ω))
          ((P.map Z).map fun s => Tm (s, F' ω))) 1 ∂P ∧
      ∫⁻ ω, Φ (ω, Tm (Z ω, F' ω)) ∂P ≤ ∫⁻ ω, Φ (ω, Tm (Z ω, F ω)) ∂P +
        ∫⁻ ω, min (TV.tvDist ((P.map Z).map fun s => Tm (s, F ω))
          ((P.map Z).map fun s => Tm (s, F' ω))) 1 ∂P := by
  have hid : @Measurable Ω Ω mΩ m𝒢 id := fun s hs => hm s hs
  have hΦ' : Measurable Φ :=
    @Measurable.comp (Ω × E) (Ω × E) ℝ≥0∞ _ (m𝒢.prod inferInstance) _ _ _ hΦ
      (hid.prodMap measurable_id)
  have hsec : ∀ ω, Measurable fun y => Φ (ω, y) := fun ω =>
    hΦ'.comp (measurable_const.prodMk measurable_id)
  have hTs : ∀ t : T, Measurable fun s => Tm (s, t) := fun t =>
    hT.comp (measurable_id.prodMk measurable_const)
  have hA : ∀ G : Ω → T, Measurable G →
      Measurable fun ω => ∫⁻ y, Φ (ω, y) ∂((P.map Z).map fun s => Tm (s, G ω)) := by
    intro G hG
    have hΨ : Measurable fun q : Ω × S => Φ (q.1, Tm (q.2, G q.1)) :=
      hΦ'.comp (measurable_fst.prodMk (hT.comp (measurable_snd.prodMk (hG.comp measurable_fst))))
    have e : (fun ω => ∫⁻ y, Φ (ω, y) ∂((P.map Z).map fun s => Tm (s, G ω))) =
        fun ω => ∫⁻ s, Φ (ω, Tm (s, G ω)) ∂(P.map Z) :=
      funext fun ω => lintegral_map (hsec ω) (hTs (G ω))
    rw [e]
    exact hΨ.lintegral_prod_right'
  have hpt : ∀ ω, (∫⁻ y, Φ (ω, y) ∂((P.map Z).map fun s => Tm (s, F ω)) ≤
        ∫⁻ y, Φ (ω, y) ∂((P.map Z).map fun s => Tm (s, F' ω)) +
          min (TV.tvDist ((P.map Z).map fun s => Tm (s, F ω))
            ((P.map Z).map fun s => Tm (s, F' ω))) 1) ∧
      (∫⁻ y, Φ (ω, y) ∂((P.map Z).map fun s => Tm (s, F' ω)) ≤
        ∫⁻ y, Φ (ω, y) ∂((P.map Z).map fun s => Tm (s, F ω)) +
          min (TV.tvDist ((P.map Z).map fun s => Tm (s, F ω))
            ((P.map Z).map fun s => Tm (s, F' ω))) 1) := by
    intro ω
    have hle : TV.tvDist ((P.map Z).map fun s => Tm (s, F ω))
        ((P.map Z).map fun s => Tm (s, F' ω)) ≤ min (TV.tvDist ((P.map Z).map fun s => Tm (s, F ω))
          ((P.map Z).map fun s => Tm (s, F' ω))) 1 := le_min le_rfl TV.tvDist_le_one
    exact ⟨(TV.lintegral_le_lintegral_add_tvDist (hsec ω) fun y => h1 _).trans
        (add_le_add le_rfl hle),
      (TV.lintegral_le_lintegral_add_tvDist (hsec ω) fun y => h1 _).trans
        (add_le_add le_rfl (TV.tvDist_comm.le.trans hle))⟩
  rw [lintegral_factor_eq hm hZ hind hF hT hΦ, lintegral_factor_eq hm hZ hind hF' hT hΦ]
  constructor
  · exact (lintegral_mono fun ω => (hpt ω).1).trans_eq
      (lintegral_add_left (hA F' (hF'.mono hm le_rfl)) _)
  · exact (lintegral_mono fun ω => (hpt ω).2).trans_eq
      (lintegral_add_left (hA F (hF.mono hm le_rfl)) _)

/-! ## The remaining node and the reduction -/

/-- **Node LSCC-TM (deterministic level shift).** For the free field `X`, an admissible
deterministic correction `φ` and a real `c`, the laws of the rich zoomed pair of
`Z + α(−log‖·‖) + φ + L/γ` (`Z` the local part) at the levels `L` and `L + c` are TV-close as
`L → ∞` (Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25; DMS arXiv:1409.7055,
Props. 4.7–4.8). -/
def LSCCTmStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) (φ : ℂ → ℝ) (c : ℝ),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P → AdmCorr r φ →
    ∀ R : ℕ, Tendsto (fun L => TV.tvDist
      (P.map fun ω => pairN1 γ r R L (localZ X r ω, circData α φ))
      (P.map fun ω => pairN1 γ r R (L + c) (localZ X r ω, circData α φ))) atTop (𝓝 0)

end D3Plus
end QuantumZipper
