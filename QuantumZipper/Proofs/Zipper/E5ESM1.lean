import QuantumZipper.Proofs.Zipper.ESMInstUncond
import QuantumZipper.Proofs.Zipper.F1EmbedBasic
import QuantumZipper.Proofs.Probability.BrownianPathMeas

/-!
# E5-ESM, part 1: the driver germ at a length level time on the level space

Task E5-G0ESM (Theorem 1.3, node E5, blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, E-SM(b) and
E5 step (3); `handoff/E5.md` item 4). Sheffield, arXiv:1012.4797, §5.4 (pp. 66–72), proof of
Lemma 5.6: after the (Palm) collision time the driver continues as a Brownian motion independent
of the past (strong Markov property of the zipper at the length level times).

On the **level space** `ℝ≥0 × Ω̄` (`Ω̄` the completion of `(Ω, P)`) with the level measure
`μ ⊗ P̄` restricted to `{ℓ ≤ L⁻_T}` and normalized (`esmRr`), the germ
`D(ℓ, ω) = smPath B T_ℓ ω` (Brownian path restarted at the length level time
`T_ℓ = levelTime (lenA κ T B X) T ℓ`) is:

* a Brownian path on `[0, u₀]` (`Rr.map (pathRestr u₀ ∘ D) = W.map (pathRestr u₀)` for every
  Brownian coordinate measure `W`), and
* independent of every `V(ℓ, ω)` which is `𝓕_{T_ℓ}`-measurable for each `ℓ`,
* measurable, with continuous paths at every point.

These are exactly the fields `hDW`, `hind`, `hD`, `hDc` of `E5.ZoomModel` (`E5Main5.lean`), for
the reference measure `Rr` of the model. Source of the identity used:
`ESM.lintegral_levelTime_strongMarkov_lenA_compl_germ` (`ESMInstUncond.lean`), with the
pathwise continuity `hBc` (see its module flag). The passage from the product formula to
independence and to the law of the germ is own measure-theoretic bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- The level event `{ℓ ≤ L⁻_T}` on the level space `ℝ≥0 × Ω̄`. -/
def esmEvt (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω) :
    Set (ℝ≥0 × NullMeasurableSpace Ω P) :=
  {p | (p.1 : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal (ofCompl P p.2)}

/-- The (un-normalized) level measure `(μ ⊗ P̄)|_{ℓ ≤ L⁻_T}`. -/
def esmMeas (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (μ : Measure ℝ≥0) : Measure (ℝ≥0 × NullMeasurableSpace Ω P) :=
  (μ.prod P.completion).restrict (esmEvt κ T B X P)

/-- The normalized level measure `𝐑` of E-SM(b). -/
def esmRr (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (μ : Measure ℝ≥0) : Measure (ℝ≥0 × NullMeasurableSpace Ω P) :=
  (esmMeas κ T B X P μ univ)⁻¹ • esmMeas κ T B X P μ

/-- The driver germ at the length level time: `D(ℓ, ω) = smPath B T_ℓ ω`. -/
def esmGerm (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (p : ℝ≥0 × NullMeasurableSpace Ω P) : ℝ≥0 → ℝ :=
  smPath B (levelTime (lenA κ T B X) T.toNNReal p.1) (ofCompl P p.2)

/-- Undo `drvMap κ`: `f ↦ (t ↦ f t / √κ)`. -/
def unDrv (κ : ℝ) (f : ℝ → ℝ) : ℝ≥0 → ℝ := fun t => f t / Real.sqrt κ

lemma measurable_unDrv (κ : ℝ) : Measurable (unDrv κ) :=
  measurable_pi_iff.2 fun t => (measurable_pi_apply (t : ℝ)).div_const _

lemma unDrv_drvMap (hκ : 0 < κ) (p : ℝ≥0 → ℝ) : unDrv κ (drvMap κ p) = p := by
  funext t
  have h : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  simp only [unDrv, drvMap, Real.toNNReal_coe]
  field_simp

/-- `lenA` is adapted to `complFiltration` on the completed space (inputs as in E-SM). -/
lemma adapted_lenA_compl_e5 (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (s : ℝ≥0) :
    Measurable[complFiltration hB hX s]
      (lenA κ T (fun t => B t ∘ ofCompl P) (X ∘ ofCompl P) s) :=
  adapted_lenA hT.le (Wire2.ae_mem_lenGood hκ hκ4 hT (isBrownianReal_completion hB)
      (isFreeGFFModConstH_completion hX) (indepFun_completion hind))
    (complFiltration_spec hB hX hind).2.2 (hLad_lenMinus_uncond hκ hκ4 hB hX hind hBc)
    (hB5V_compl (B5.ae_b5v hκ hκ4 hT hB hX hind)) s

lemma measurable_lenA_compl_e5 (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (s : ℝ≥0) :
    Measurable (fun ω : NullMeasurableSpace Ω P => lenA κ T B X s (ofCompl P ω)) :=
  (adapted_lenA_compl_e5 hκ hκ4 hT hB hX hind hBc s).mono ((complFiltration hB hX).le s) le_rfl

lemma measurableSet_esmEvt (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) : MeasurableSet (esmEvt κ T B X P) :=
  measurableSet_le (measurable_coe_nnreal_ennreal.comp measurable_fst)
    ((measurable_lenA_compl_e5 hκ hκ4 hT hB hX hind hBc _).comp measurable_snd)

/-- **The germ is jointly measurable** on the level space. -/
theorem measurable_esmGerm (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) : Measurable (esmGerm κ T B X P) :=
  measurable_smPath (B := fun t (p : ℝ≥0 × NullMeasurableSpace Ω P) => B t (ofCompl P p.2))
    (fun p => hBc (ofCompl P p.2)) (fun t => (measurable_B_compl hB t).comp measurable_snd)
    (measurable_levelTime_uncurry (A := lenA κ T (fun t => B t ∘ ofCompl P) (X ∘ ofCompl P))
      (continuous_lenA hT.le) (monotone_lenA hT.le)
      (fun s => measurable_lenA_compl_e5 hκ hκ4 hT hB hX hind hBc s) T.toNNReal)

omit [IsProbabilityMeasure P] in
/-- **The germ has continuous paths at every point.** -/
theorem continuous_esmGerm (hBc : ∀ ω, Continuous (B · ω)) (p : ℝ≥0 × NullMeasurableSpace Ω P) :
    Continuous (esmGerm κ T B X P p) := by
  have h := hBc (ofCompl P p.2)
  exact (h.comp (continuous_const.add continuous_id)).sub continuous_const

/-! ## The E-SM product formula on the level space -/

/-- The level-weight test `H ℓ ω = 1_A(V(ℓ, ω))`. -/
def esmH {𝕍 : Type} (V : ℝ≥0 × Ω → 𝕍) (A : Set 𝕍) : ℝ≥0 → Ω → ℝ≥0∞ :=
  fun ℓ ω => A.indicator 1 (V (ℓ, ω))

/-- The path test `Ψ f = 1_S(φ(f/√κ))`. -/
def esmPsi (κ : ℝ) {𝕐 : Type} (φ : (ℝ≥0 → ℝ) → 𝕐) (S : Set 𝕐) : (ℝ → ℝ) → ℝ≥0∞ :=
  fun f => S.indicator 1 (φ (unDrv κ f))

omit [IsProbabilityMeasure P] in
lemma esm_ind_eq {𝕍 : Type} (V : ℝ≥0 × Ω → 𝕍) (A : Set 𝕍) {𝕐 : Type} (φ : (ℝ≥0 → ℝ) → 𝕐) (S : Set 𝕐)
    (hκ : 0 < κ) (ℓ : ℝ≥0) (ω : NullMeasurableSpace Ω P) :
    (((fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2)) ⁻¹' A ∩
        (fun p => φ (esmGerm κ T B X P p)) ⁻¹' S) ∩ esmEvt κ T B X P).indicator 1
        (ℓ, ω) =
      {ω' | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω'}.indicator (esmH V A ℓ) (ofCompl P ω) *
        esmPsi κ φ S (drvMap κ (smPath B (levelTime (lenA κ T B X) T.toNNReal ℓ)
          (ofCompl P ω))) := by
  simp only [esmPsi]
  rw [unDrv_drvMap hκ]
  have hGS : ∀ hS : (ℓ, ω) ∈ (fun p => φ (esmGerm κ T B X P p)) ⁻¹' S,
      φ (smPath B (levelTime (lenA κ T B X) T.toNNReal ℓ) (ofCompl P ω)) ∈ S :=
    fun hS => hS
  by_cases hm : (ℓ, ω) ∈ ((fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2)) ⁻¹' A ∩
        (fun p => φ (esmGerm κ T B X P p)) ⁻¹' S) ∩ esmEvt κ T B X P
  · rw [indicator_of_mem hm, indicator_of_mem (show ofCompl P ω ∈
        {ω' | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω'} from hm.2), esmH,
      indicator_of_mem (show V (ℓ, ofCompl P ω) ∈ A from hm.1.1), indicator_of_mem (hGS hm.1.2)]
    simp
  · rw [indicator_of_notMem hm]
    by_cases hE : ofCompl P ω ∈ {ω' | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω'}
    · rw [indicator_of_mem hE, esmH]
      by_cases hA : V (ℓ, ofCompl P ω) ∈ A
      · rw [indicator_of_mem hA, indicator_of_notMem (show φ
          (smPath B (levelTime (lenA κ T B X) T.toNNReal ℓ) (ofCompl P ω)) ∉ S from
            fun hS => hm ⟨⟨hA, hS⟩, hE⟩)]
        simp
      · rw [indicator_of_notMem hA]; simp
    · rw [indicator_of_notMem hE]; simp

/-- **The E-SM product formula on the level space**: for `V` jointly measurable and
`𝓕_{T_ℓ}`-measurable for each `ℓ`, the level measure of `{V ∈ A, φ(D) ∈ S}` (any measurable `φ` of the germ) factorizes as
(Brownian law of `S`) × (level measure of `{V ∈ A}`). -/
theorem esmMeas_factor (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (μ : Measure ℝ≥0) [SFinite μ]
    {𝕍 : Type} [MeasurableSpace 𝕍] {V : ℝ≥0 × Ω → 𝕍} (hV : Measurable V)
    (hVT : ∀ ℓ, Measurable[(complLevelStop hκ hκ4 hT hB hX hind hBc ℓ).measurableSpace]
      ((fun ω => V (ℓ, ω)) ∘ ofCompl P))
    {𝕐 : Type} [MeasurableSpace 𝕐] {φ : (ℝ≥0 → ℝ) → 𝕐} (hφ : Measurable φ)
    {A : Set 𝕍} (hA : MeasurableSet A) {S : Set 𝕐}
    (hS : MeasurableSet S) :
    esmMeas κ T B X P μ
        ((fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2)) ⁻¹' A ∩
          (fun p => φ (esmGerm κ T B X P p)) ⁻¹' S) =
      P.map (fun ω => φ (pathOf B ω)) S *
        esmMeas κ T B X P μ
          ((fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2)) ⁻¹' A) := by
  have hE := measurableSet_esmEvt hκ hκ4 hT hB hX hind hBc
  have hV₁ : Measurable fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2) :=
    hV.comp (measurable_fst.prodMk (measurable_ofCompl.comp measurable_snd))
  have hG : Measurable fun p => φ (esmGerm κ T B X P p) :=
    hφ.comp (measurable_esmGerm hκ hκ4 hT hB hX hind hBc)
  have hHm : Measurable (fun p : ℝ≥0 × Ω => esmH V A p.1 p.2) :=
    (measurable_one.indicator hA).comp hV
  have hHT : ∀ ℓ, Measurable[(complLevelStop hκ hκ4 hT hB hX hind hBc ℓ).measurableSpace]
      (esmH V A ℓ ∘ ofCompl P) := fun ℓ => (measurable_one.indicator hA).comp (hVT ℓ)
  have hΨ : ∀ S' : Set 𝕐, MeasurableSet S' → Measurable (esmPsi κ φ S') :=
    fun S' hS' => (measurable_one.indicator hS').comp
      (hφ.comp (measurable_unDrv κ))
  have key : ∀ S' : Set 𝕐, MeasurableSet S' →
      esmMeas κ T B X P μ
        ((fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2)) ⁻¹' A ∩
          (fun p => φ (esmGerm κ T B X P p)) ⁻¹' S') =
      ∫⁻ ω, ∫⁻ ℓ, {ω' | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω'}.indicator (esmH V A ℓ) ω *
        esmPsi κ φ S' (drvMap κ (smPath B (levelTime (lenA κ T B X) T.toNNReal ℓ) ω))
          ∂μ ∂P := by
    intro S' hS'
    have hM := (hV₁ hA).inter (hG hS')
    rw [esmMeas, Measure.restrict_apply hM, ← lintegral_indicator_one (hM.inter hE),
      lintegral_prod_symm' _ (measurable_one.indicator (hM.inter hE))]
    simp_rw [esm_ind_eq V A φ S' hκ]
    exact lintegral_completion (P := P) fun ω => ∫⁻ ℓ,
      {ω' | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω'}.indicator (esmH V A ℓ) ω *
        esmPsi κ φ S' (drvMap κ (smPath B (levelTime (lenA κ T B X) T.toNNReal ℓ) ω)) ∂μ
  have h2 : esmMeas κ T B X P μ
      ((fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2)) ⁻¹' A) =
      ∫⁻ ω, ∫⁻ ℓ, {ω' | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω'}.indicator (esmH V A ℓ) ω
        ∂μ ∂P := by
    have h := key univ MeasurableSet.univ
    rw [preimage_univ, inter_univ] at h
    rw [h]
    simp only [esmPsi, indicator_univ, Pi.one_apply, mul_one]
  have hfc : Measurable ((fun ω => φ (pathOf B ω)) ∘ ofCompl P) :=
    hφ.comp (measurable_pi_iff.2 fun t => measurable_B_compl hB t)
  have hf : AEMeasurable (fun ω => φ (pathOf B ω)) P :=
    hφ.comp_aemeasurable (IsBrownianReal.aemeasurable_pathOf hB)
  have h1 : ∫⁻ ω, esmPsi κ φ S (drive κ B ω) ∂P =
      P.map (fun ω => φ (pathOf B ω)) S := by
    have e : ∀ ω, esmPsi κ φ S (drive κ B ω) = S.indicator 1 (φ (pathOf B ω)) := by
      intro ω
      rw [← drvMap_path, esmPsi, unDrv_drvMap hκ]
      rfl
    simp_rw [e]
    rw [← lintegral_completion (P := P), ← map_completion hf, Measure.map_apply hfc hS]
    rw [← lintegral_indicator_one (hfc hS)]
    rfl
  rw [key S hS, lintegral_levelTime_strongMarkov_lenA_compl_germ hκ hκ4 hT hB hX hind hBc μ
    hHm hHT (hΨ S hS), h1, h2]

end E5
end QuantumZipper
