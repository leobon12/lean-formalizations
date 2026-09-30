import QuantumZipper.Proofs.Probability.StrongMarkov
import QuantumZipper.Proofs.Probability.GermZeroOne
import Mathlib.MeasureTheory.Function.Floor

/-!
# Length representation + strong Markov (E-SM-abs) and the germ-density lemma (E5a)

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, nodes **E-SM-abs** and **E5a**.

* `LengthMarkov.levelTime A S ℓ` is `T_ℓ = inf {s | ℓ ≤ A s} ∧ S` (with `inf ∅ = ∞`), written as
  `sInf {s | ℓ ≤ A s ∨ S ≤ s}`. `LengthMarkov.lintegral_levelTime_strongMarkov` is E-SM-abs.
* `LengthMarkov.GermDensity.germDensity` is E5a, with the supremum over `Γ` made explicit
  (the bound is uniform in `Γ`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LengthMarkov

open StrongMarkov

/-! ## E-SM-abs -/

section LevelTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `T_ℓ := inf {s | ℓ ≤ A s} ∧ S` (with `inf ∅ = ∞`). -/
noncomputable def levelTime (A : ℝ≥0 → Ω → ℝ≥0∞) (S ℓ : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf {s : ℝ≥0 | (ℓ : ℝ≥0∞) ≤ A s ω ∨ S ≤ s}

variable {A : ℝ≥0 → Ω → ℝ≥0∞}

lemma levelTime_le_iff (hAc : ∀ ω, Continuous fun s => A s ω)
    (hAmono : ∀ ω, Monotone fun s => A s ω) (S ℓ u : ℝ≥0) (ω : Ω) :
    levelTime A S ℓ ω ≤ u ↔ (ℓ : ℝ≥0∞) ≤ A u ω ∨ S ≤ u := by
  have hne : ({s : ℝ≥0 | (ℓ : ℝ≥0∞) ≤ A s ω ∨ S ≤ s}).Nonempty := ⟨S, Or.inr le_rfl⟩
  have hcl : IsClosed {s : ℝ≥0 | (ℓ : ℝ≥0∞) ≤ A s ω ∨ S ≤ s} :=
    (isClosed_le continuous_const (hAc ω)).union (isClosed_Ici (a := S))
  constructor
  · intro h
    rcases hcl.csInf_mem hne (OrderBot.bddBelow _) with h1 | h1
    · exact Or.inl (h1.trans (hAmono ω h))
    · exact Or.inr (h1.trans h)
  · intro h
    exact csInf_le (OrderBot.bddBelow _) h

lemma levelTime_le (hAc : ∀ ω, Continuous fun s => A s ω)
    (hAmono : ∀ ω, Monotone fun s => A s ω) (S ℓ : ℝ≥0) (ω : Ω) : levelTime A S ℓ ω ≤ S :=
  (levelTime_le_iff hAc hAmono S ℓ S ω).2 (Or.inr le_rfl)

lemma measurable_levelTime_uncurry (hAc : ∀ ω, Continuous fun s => A s ω)
    (hAmono : ∀ ω, Monotone fun s => A s ω) (hAm : ∀ s, Measurable (A s)) (S : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × Ω => levelTime A S p.1 p.2) := by
  refine measurable_of_Iic fun u => ?_
  have : (fun p : ℝ≥0 × Ω => levelTime A S p.1 p.2) ⁻¹' Set.Iic u =
      {p : ℝ≥0 × Ω | ((p.1 : ℝ≥0) : ℝ≥0∞) ≤ A u p.2} ∪ {_p | S ≤ u} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_setOf_eq]
    exact levelTime_le_iff hAc hAmono S p.1 u p.2
  rw [this]
  exact (measurableSet_le (measurable_coe_nnreal_ennreal.comp measurable_fst)
    ((hAm u).comp measurable_snd)).union (MeasurableSet.const _)

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- `T_ℓ` is a stopping time. -/
lemma isStoppingTime_levelTime (hAc : ∀ ω, Continuous fun s => A s ω)
    (hAmono : ∀ ω, Monotone fun s => A s ω) (hAad : ∀ s, Measurable[𝓕 s] (A s)) (S ℓ : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => (levelTime A S ℓ ω : WithTop ℝ≥0)) := by
  intro u
  show MeasurableSet[𝓕 u] {ω | (levelTime A S ℓ ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)}
  have : {ω | (levelTime A S ℓ ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
      {ω | (ℓ : ℝ≥0∞) ≤ A u ω} ∪ {_ω | S ≤ u} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, WithTop.coe_le_coe]
    exact levelTime_le_iff hAc hAmono S ℓ u ω
  rw [this]
  exact (measurableSet_le measurable_const (hAad u)).union (MeasurableSet.const _)

/-- `{ℓ ≤ A S} ∈ 𝓕_{T_ℓ}`. -/
lemma measurableSet_levelTime_event (hAc : ∀ ω, Continuous fun s => A s ω)
    (hAmono : ∀ ω, Monotone fun s => A s ω) (hAad : ∀ s, Measurable[𝓕 s] (A s)) (S ℓ : ℝ≥0) :
    MeasurableSet[(isStoppingTime_levelTime hAc hAmono hAad S ℓ).measurableSpace]
      {ω | (ℓ : ℝ≥0∞) ≤ A S ω} := by
  have hES : MeasurableSet[𝓕 S] {ω | (ℓ : ℝ≥0∞) ≤ A S ω} :=
    measurableSet_le measurable_const (hAad S)
  rw [IsStoppingTime.measurableSet]
  refine ⟨(le_iSup (fun t => 𝓕 t) S) _ hES, fun u => ?_⟩
  show MeasurableSet[𝓕 u] ({ω | (ℓ : ℝ≥0∞) ≤ A S ω} ∩
    {ω | (levelTime A S ℓ ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)})
  by_cases hSu : S ≤ u
  · have : {ω | (ℓ : ℝ≥0∞) ≤ A S ω} ∩
        {ω | (levelTime A S ℓ ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
        {ω | (ℓ : ℝ≥0∞) ≤ A S ω} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, WithTop.coe_le_coe, and_iff_left_iff_imp]
      exact fun _ => (levelTime_le hAc hAmono S ℓ ω).trans hSu
    rw [this]
    exact 𝓕.mono hSu _ hES
  · have : {ω | (ℓ : ℝ≥0∞) ≤ A S ω} ∩
        {ω | (levelTime A S ℓ ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
        {ω | (ℓ : ℝ≥0∞) ≤ A u ω} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, WithTop.coe_le_coe,
        levelTime_le_iff hAc hAmono, or_iff_left hSu]
      exact ⟨fun h => h.2, fun h => ⟨h.trans (hAmono ω (not_le.1 hSu).le), h⟩⟩
    rw [this]
    exact measurableSet_le measurable_const (hAad u)

variable {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- E-SM-abs for a fixed level `ℓ`. -/
theorem lintegral_indicator_mul_smPath_levelTime [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hAc : ∀ ω, Continuous fun s => A s ω) (hAmono : ∀ ω, Monotone fun s => A s ω)
    (hAad : ∀ s, Measurable[𝓕 s] (A s)) (S ℓ : ℝ≥0) {h : Ω → ℝ≥0∞}
    (hh : Measurable[(isStoppingTime_levelTime hAc hAmono hAad S ℓ).measurableSpace] h)
    {Ψ : (ℝ≥0 → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, {ω | (ℓ : ℝ≥0∞) ≤ A S ω}.indicator h ω * Ψ (smPath B (levelTime A S ℓ) ω) ∂P =
      (∫⁻ ω, Ψ (fun t => B t ω) ∂P) * ∫⁻ ω, {ω | (ℓ : ℝ≥0∞) ≤ A S ω}.indicator h ω ∂P := by
  set hT := isStoppingTime_levelTime hAc hAmono hAad S ℓ
  have hTle : hT.measurableSpace ≤ mΩ := hT.measurableSpace_le
  have hf : Measurable[hT.measurableSpace] ({ω | (ℓ : ℝ≥0∞) ≤ A S ω}.indicator h) :=
    hh.indicator (measurableSet_levelTime_event hAc hAmono hAad S ℓ)
  have hsm := measurable_smPath hBc hBm (measurable_of_isStoppingTime hT)
  have hindep : IndepFun ({ω | (ℓ : ℝ≥0∞) ≤ A S ω}.indicator h)
      (fun ω => Ψ (smPath B (levelTime A S ℓ) ω)) P :=
    (indepFun_smPath hB hBc hBm hind hT hf).comp measurable_id hΨ
  have hgm : AEMeasurable (fun ω => Ψ (smPath B (levelTime A S ℓ) ω)) P :=
    (hΨ.comp hsm).aemeasurable
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hf.mono hTle le_rfl).aemeasurable
    hgm hindep, mul_comm]
  congr 1
  have hmap := map_restrict_smPath_eq hB hBc hBm hind hT
    (@MeasurableSet.univ Ω hT.measurableSpace)
  rw [Measure.restrict_univ, measure_univ, one_smul] at hmap
  rw [← lintegral_map hΨ hsm, hmap, lintegral_map hΨ (measurable_path hBm)]

/-- **E-SM-abs.** For `B` pre-Brownian with continuous paths, adapted to `𝓕` with the
independence hypothesis `hind`, `A` continuous nondecreasing adapted, `T_ℓ = levelTime A S ℓ`,
`H` jointly measurable with `H ℓ` `𝓕_{T_ℓ}`-measurable, any s-finite `μ` on levels (e.g.
Lebesgue), and any measurable `Ψ ≥ 0` on path space:
`∫∫ 1{ℓ ≤ A S} H ℓ ω Ψ(smPath B T_ℓ ω) dμ(ℓ) dP = E[Ψ(B)] · ∫∫ 1{ℓ ≤ A S} H ℓ ω dμ(ℓ) dP`. -/
theorem lintegral_levelTime_strongMarkov [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hAc : ∀ ω, Continuous fun s => A s ω) (hAmono : ∀ ω, Monotone fun s => A s ω)
    (hAad : ∀ s, Measurable[𝓕 s] (A s)) (S : ℝ≥0) (μ : Measure ℝ≥0) [SFinite μ]
    {H : ℝ≥0 → Ω → ℝ≥0∞} (hH : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hHT : ∀ ℓ, Measurable[(isStoppingTime_levelTime hAc hAmono hAad S ℓ).measurableSpace]
      (H ℓ))
    {Ψ : (ℝ≥0 → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ A S ω}.indicator (H ℓ) ω *
        Ψ (smPath B (levelTime A S ℓ) ω) ∂μ ∂P =
      (∫⁻ ω, Ψ (fun t => B t ω) ∂P) *
        ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ A S ω}.indicator (H ℓ) ω ∂μ ∂P := by
  have hBm : ∀ t, Measurable (B t) := fun t => (hBad t).mono (𝓕.le t) le_rfl
  have hAm : ∀ s, Measurable (A s) := fun s => (hAad s).mono (𝓕.le s) le_rfl
  have hE : MeasurableSet {p : ℝ≥0 × Ω | ((p.1 : ℝ≥0) : ℝ≥0∞) ≤ A S p.2} :=
    measurableSet_le (measurable_coe_nnreal_ennreal.comp measurable_fst)
      ((hAm S).comp measurable_snd)
  have hI : Measurable (fun p : ℝ≥0 × Ω => {ω | (p.1 : ℝ≥0∞) ≤ A S ω}.indicator (H p.1) p.2) := by
    have : (fun p : ℝ≥0 × Ω => {ω | (p.1 : ℝ≥0∞) ≤ A S ω}.indicator (H p.1) p.2) =
        {p : ℝ≥0 × Ω | ((p.1 : ℝ≥0) : ℝ≥0∞) ≤ A S p.2}.indicator (fun p => H p.1 p.2) := by
      funext p
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [this]
    exact hH.indicator hE
  have hsmJ : Measurable (fun p : ℝ≥0 × Ω => smPath B (levelTime A S p.1) p.2) :=
    measurable_smPath (B := fun t (p : ℝ≥0 × Ω) => B t p.2) (fun p => hBc p.2)
      (fun t => (hBm t).comp measurable_snd) (measurable_levelTime_uncurry hAc hAmono hAm S)
  have hJ := hI.mul (hΨ.comp hsmJ)
  have hJs : AEMeasurable (Function.uncurry fun (ω : Ω) (ℓ : ℝ≥0) =>
      {ω | (ℓ : ℝ≥0∞) ≤ A S ω}.indicator (H ℓ) ω * Ψ (smPath B (levelTime A S ℓ) ω))
      (P.prod μ) := (hJ.comp measurable_swap).aemeasurable
  have hIs : AEMeasurable (Function.uncurry fun (ω : Ω) (ℓ : ℝ≥0) =>
      {ω | (ℓ : ℝ≥0∞) ≤ A S ω}.indicator (H ℓ) ω) (P.prod μ) :=
    (hI.comp measurable_swap).aemeasurable
  rw [lintegral_lintegral_swap hJs, lintegral_lintegral_swap hIs,
    ← lintegral_const_mul _ hI.lintegral_prod_right']
  refine lintegral_congr fun ℓ => ?_
  exact lintegral_indicator_mul_smPath_levelTime hB hBc hBm hind hAc hAmono hAad S ℓ (hHT ℓ) hΨ

end LevelTime

/-! ## E5a: the germ-density lemma -/

namespace GermDensity

open GermZeroOne

/-! ### Path operations -/

/-- Restriction of a path to `[0, c]`. -/
def pathRestr (c : ℝ≥0) (b : ℝ≥0 → ℝ) : Set.Iic c → ℝ := fun t => b t

lemma measurable_pathRestr (c : ℝ≥0) : Measurable (pathRestr c) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- Constant extension of a path on `[0, c]`. -/
def pathExt (c : ℝ≥0) (x : Set.Iic c → ℝ) : ℝ≥0 → ℝ := fun t => x ⟨min t c, Set.mem_Iic.2 (min_le_right _ _)⟩

lemma measurable_pathExt (c : ℝ≥0) : Measurable (pathExt c) :=
  measurable_pi_iff.2 fun t =>
    measurable_pi_apply (⟨min t c, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic c)

lemma pathExt_pathRestr_of_le {c t : ℝ≥0} (ht : t ≤ c) (b : ℝ≥0 → ℝ) :
    pathExt c (pathRestr c b) t = b t := by
  simp [pathExt, pathRestr, min_eq_left ht]

/-- Evaluation along dyadic ceilings; equals `b s` when `b` is continuous, and is jointly
measurable in `(b, s)`. -/
noncomputable def evalLim (b : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  limsup (fun j : ℕ => b (ItoLite.dyadicCeil j s)) atTop

lemma measurable_evalLim : Measurable (fun p : (ℝ≥0 → ℝ) × ℝ≥0 => evalLim p.1 p.2) := by
  refine Measurable.limsup fun j => ?_
  have h1 : Measurable (fun q : (ℝ≥0 → ℝ) × ℕ => q.1 ((q.2 : ℝ≥0) / 2 ^ j)) :=
    measurable_from_prod_countable_left fun k => measurable_pi_apply ((k : ℝ≥0) / 2 ^ j)
  have h2 : Measurable (fun p : (ℝ≥0 → ℝ) × ℝ≥0 => (p.1, ⌈p.2 * 2 ^ j⌉₊)) :=
    measurable_fst.prodMk (Nat.measurable_ceil.comp (measurable_snd.mul_const _))
  exact h1.comp h2

lemma evalLim_of_continuous {b : ℝ≥0 → ℝ} (hb : Continuous b) (s : ℝ≥0) : evalLim b s = b s :=
  ((hb.tendsto s).comp (ItoLite.tendsto_dyadicCeil s)).limsup_eq

lemma evalLim_congr {b b' : ℝ≥0 → ℝ} {c s : ℝ≥0} (hbb : ∀ t ≤ c, b t = b' t) (hs : s < c) :
    evalLim b s = evalLim b' s := by
  unfold evalLim
  refine Filter.limsup_congr ?_
  filter_upwards [(ItoLite.tendsto_dyadicCeil s).eventually (eventually_le_nhds hs)] with j hj
  exact hbb _ hj

/-- The Brownian rescaling `(a⁻¹ b(a² t))_{t ≤ S}`. -/
noncomputable def rescale (S a : ℝ≥0) (b : ℝ≥0 → ℝ) : Set.Iic S → ℝ := fun t => (a : ℝ)⁻¹ * b (a ^ 2 * t)

/-- A jointly measurable surrogate of `rescale`. -/
noncomputable def rescaleLim (S a : ℝ≥0) (b : ℝ≥0 → ℝ) : Set.Iic S → ℝ :=
  fun t => (a : ℝ)⁻¹ * evalLim b (a ^ 2 * t)

lemma measurable_rescaleLim (S : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℝ≥0 → ℝ) => rescaleLim S p.1 p.2) := by
  refine measurable_pi_iff.2 fun t => ?_
  have h1 : Measurable (fun p : ℝ≥0 × (ℝ≥0 → ℝ) => ((p.1 : ℝ))⁻¹) :=
    measurable_fst.coe_nnreal_real.inv
  have hq : Measurable (fun x : ℝ≥0 => x ^ 2 * (t : ℝ≥0)) :=
    ((continuous_pow 2).mul continuous_const).measurable
  have h3 : Measurable (fun p : ℝ≥0 × (ℝ≥0 → ℝ) => (p.2, p.1 ^ 2 * (t : ℝ≥0))) :=
    measurable_snd.prodMk (hq.comp measurable_fst)
  have h2 : Measurable (fun p : ℝ≥0 × (ℝ≥0 → ℝ) => evalLim p.2 (p.1 ^ 2 * (t : ℝ≥0))) :=
    (measurable_evalLim.comp h3 : Measurable ((fun q : (ℝ≥0 → ℝ) × ℝ≥0 => evalLim q.1 q.2) ∘
      (fun p : ℝ≥0 × (ℝ≥0 → ℝ) => (p.2, p.1 ^ 2 * (t : ℝ≥0)))))
  show Measurable (fun p : ℝ≥0 × (ℝ≥0 → ℝ) => ((p.1 : ℝ))⁻¹ * evalLim p.2 (p.1 ^ 2 * (t : ℝ≥0)))
  exact h1.mul h2

lemma rescaleLim_of_continuous {b : ℝ≥0 → ℝ} (hb : Continuous b) (S a : ℝ≥0) :
    rescaleLim S a b = rescale S a b := by
  funext t
  simp only [rescaleLim, rescale, evalLim_of_continuous hb]

lemma rescaleLim_congr {b b' : ℝ≥0 → ℝ} {c S a : ℝ≥0} (hbb : ∀ t ≤ c, b t = b' t)
    (ha : a ^ 2 * S < c) : rescaleLim S a b = rescaleLim S a b' := by
  funext t
  simp only [rescaleLim]
  rw [evalLim_congr hbb (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Set.mem_Iic.1 t.2) (by positivity)) ha)]

/-- Concatenation of a path on `[0, c]` with an increment path. -/
noncomputable def pathConcat (c : ℝ≥0) (x : Set.Iic c → ℝ) (β : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  fun t => if h : t ≤ c then x ⟨t, Set.mem_Iic.2 h⟩ else x ⟨c, Set.mem_Iic.2 le_rfl⟩ + β (t - c)

/-- The increment path after time `c`. -/
def pathShift (c : ℝ≥0) (b : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun s => b (c + s) - b c

lemma measurable_pathShift (c : ℝ≥0) : Measurable (pathShift c) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _)

lemma pathConcat_restr_shift (c : ℝ≥0) (b : ℝ≥0 → ℝ) :
    pathConcat c (pathRestr c b) (pathShift c b) = b := by
  funext t
  by_cases h : t ≤ c
  · simp [pathConcat, pathRestr, h]
  · simp only [pathConcat, pathRestr, pathShift, dif_neg h]
    rw [add_tsub_cancel_of_le (not_le.1 h).le]
    ring

lemma measurable_pathConcat (c : ℝ≥0) :
    Measurable (fun p : (Set.Iic c → ℝ) × (ℝ≥0 → ℝ) => pathConcat c p.1 p.2) := by
  refine measurable_pi_iff.2 fun t => ?_
  by_cases h : t ≤ c
  · have e : (fun p : (Set.Iic c → ℝ) × (ℝ≥0 → ℝ) => pathConcat c p.1 p.2 t) =
        fun p => p.1 ⟨t, Set.mem_Iic.2 h⟩ := by
      funext p; simp [pathConcat, h]
    rw [e]
    exact (measurable_pi_apply (⟨t, Set.mem_Iic.2 h⟩ : Set.Iic c)).comp measurable_fst
  · have e : (fun p : (Set.Iic c → ℝ) × (ℝ≥0 → ℝ) => pathConcat c p.1 p.2 t) =
        fun p => p.1 ⟨c, Set.mem_Iic.2 le_rfl⟩ + p.2 (t - c) := by
      funext p; simp [pathConcat, h]
    rw [e]
    exact ((measurable_pi_apply (⟨c, Set.mem_Iic.2 le_rfl⟩ : Set.Iic c)).comp
      measurable_fst).add ((measurable_pi_apply (t - c)).comp measurable_snd)

/-! ### Small integration helpers -/

lemma integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

lemma indicator_preimage_eq_mul {α β : Type*} (f : α → β) (A : Set β) (h : α → ℝ) (x : α) :
    (f ⁻¹' A).indicator h x = A.indicator 1 (f x) * h x := by
  by_cases hx : f x ∈ A
  · rw [Set.indicator_of_mem (show x ∈ f ⁻¹' A from hx), Set.indicator_of_mem hx]
    simp
  · rw [Set.indicator_of_notMem (show x ∉ f ⁻¹' A from hx), Set.indicator_of_notMem hx]
    simp

/-! ### Wiener measure: scaling and the simple Markov property -/

section Wiener

variable {W : Measure (ℝ≥0 → ℝ)}

lemma measurable_coord : ∀ t : ℝ≥0, Measurable (fun b : ℝ≥0 → ℝ => b t) :=
  fun t => measurable_pi_apply t

/-- Brownian scaling under `W`. -/
lemma integral_rescale (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) {S a : ℝ≥0}
    (ha : a ≠ 0) {G : (Set.Iic S → ℝ) → ℝ} (hG : Measurable G) :
    ∫ b, G (rescale S a b) ∂W = ∫ b, G (pathRestr S b) ∂W := by
  have hBr : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => (a : ℝ)⁻¹ * b (a ^ 2 * t)) W := by
    have := hW.smul (c := a ^ 2) (pow_ne_zero 2 ha)
    convert this using 4 with t b
    simp [Real.sqrt_sq a.coe_nonneg]
  have hmr : ∀ t, Measurable (fun b : ℝ≥0 → ℝ => (a : ℝ)⁻¹ * b (a ^ 2 * t)) :=
    fun t => (measurable_pi_apply _).const_mul _
  have hmap := map_path_eq_of_isPreBrownianReal hBr hW hmr measurable_coord
  beta_reduce at hmap
  let Φ : (ℝ≥0 → ℝ) → ℝ := fun x => G (pathRestr S x)
  have hΦ : Measurable Φ := hG.comp (measurable_pathRestr S)
  have e1 := integral_map (μ := W) (φ := fun b t => (a : ℝ)⁻¹ * b (a ^ 2 * t))
    (measurable_pi_iff.2 hmr).aemeasurable hΦ.aestronglyMeasurable
  have e2 := integral_map (μ := W) (φ := fun b t => b t)
    (measurable_pi_iff.2 measurable_coord).aemeasurable hΦ.aestronglyMeasurable
  rw [hmap] at e1
  exact e1.symm.trans e2

variable [IsProbabilityMeasure W]

/-- Simple Markov property of `W` at time `c`, in product form. -/
lemma map_restr_shift (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) (c : ℝ≥0) :
    W.map (fun b => (pathRestr c b, pathShift c b)) = (W.map (pathRestr c)).prod W := by
  have hind : IndepFun (pathRestr c) (pathShift c) W := (hW.indepFun_shift c).symm
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pathRestr c).aemeasurable
    (measurable_pathShift c).aemeasurable).1 hind]
  congr 1
  have h := map_path_eq_of_isPreBrownianReal (hW.shift c) hW
    (fun s => (measurable_pi_apply _).sub (measurable_pi_apply _)) measurable_coord
  calc W.map (pathShift c) = W.map (fun b (t : ℝ≥0) => b t) := h
    _ = W := Measure.map_id

/-- The explicit version of `E_W[ψ v | σ(b|[0,c])]`. -/
noncomputable def condDens (W : Measure (ℝ≥0 → ℝ)) (c : ℝ≥0) {𝕍 : Type*}
    (ψ : 𝕍 → (ℝ≥0 → ℝ) → ℝ) (v : 𝕍) (x : Set.Iic c → ℝ) : ℝ :=
  ∫ β, ψ v (pathConcat c x β) ∂W

variable {𝕍 : Type*} [MeasurableSpace 𝕍] {ψ : 𝕍 → (ℝ≥0 → ℝ) → ℝ}

lemma measurable_condDens (hψ : Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) => ψ p.1 p.2)) (c : ℝ≥0) :
    Measurable (fun p : 𝕍 × (Set.Iic c → ℝ) => condDens W c ψ p.1 p.2) := by
  have hf : Measurable (fun q : (𝕍 × (Set.Iic c → ℝ)) × (ℝ≥0 → ℝ) =>
      ψ q.1.1 (pathConcat c q.1.2 q.2)) :=
    hψ.comp (measurable_fst.fst.prodMk
      ((measurable_pathConcat c).comp (measurable_fst.snd.prodMk measurable_snd)))
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_condDens_apply (hψ : Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) => ψ p.1 p.2))
    (c : ℝ≥0) (v : 𝕍) : Measurable (condDens W c ψ v) :=
  (measurable_condDens hψ c).comp (measurable_const.prodMk measurable_id)

/-- The key identity: `condDens` reproduces `ψ v` against functions of `b|[0,c]`. -/
lemma integral_mul_eq_condDens (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    (hψ : Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) => ψ p.1 p.2)) (v : 𝕍) (hψi : Integrable (ψ v) W)
    (c : ℝ≥0) {g : (Set.Iic c → ℝ) → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    ∫ b, g (pathRestr c b) * ψ v b ∂W =
      ∫ b, g (pathRestr c b) * condDens W c ψ v (pathRestr c b) ∂W := by
  set π : (ℝ≥0 → ℝ) → (Set.Iic c → ℝ) × (ℝ≥0 → ℝ) := fun b => (pathRestr c b, pathShift c b)
  have hπ : Measurable π := (measurable_pathRestr c).prodMk (measurable_pathShift c)
  set F : (Set.Iic c → ℝ) × (ℝ≥0 → ℝ) → ℝ := fun q => g q.1 * ψ v (pathConcat c q.1 q.2)
  have hψv : Measurable (ψ v) := hψ.comp (measurable_const.prodMk measurable_id)
  have hFm : Measurable F := (hg.comp measurable_fst).mul (hψv.comp (measurable_pathConcat c))
  have hFπ : ∀ b, F (π b) = g (pathRestr c b) * ψ v b := fun b => by
    simp only [F, π, pathConcat_restr_shift]
  have hmap := map_restr_shift hW c
  have hFi : Integrable F ((W.map (pathRestr c)).prod W) := by
    rw [← hmap, integrable_map_measure hFm.aestronglyMeasurable hπ.aemeasurable]
    have hbd : ∀ᵐ b ∂W, ‖(g ∘ pathRestr c) b‖ ≤ C := Eventually.of_forall fun b => by
      rw [Function.comp_apply, Real.norm_eq_abs]; exact hgC _
    exact (hψi.bdd_mul (hg.comp (measurable_pathRestr c)).aestronglyMeasurable hbd).congr
      (Eventually.of_forall fun b => (hFπ b).symm)
  calc ∫ b, g (pathRestr c b) * ψ v b ∂W = ∫ b, F (π b) ∂W :=
        integral_congr_ae (Eventually.of_forall fun b => (hFπ b).symm)
    _ = ∫ q, F q ∂(W.map π) := (integral_map hπ.aemeasurable hFm.aestronglyMeasurable).symm
    _ = ∫ x, ∫ β, F (x, β) ∂W ∂(W.map (pathRestr c)) := by rw [hmap, integral_prod F hFi]
    _ = ∫ x, g x * condDens W c ψ v x ∂(W.map (pathRestr c)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [F, condDens]
        exact integral_const_mul _ _
    _ = ∫ b, g (pathRestr c b) * condDens W c ψ v (pathRestr c b) ∂W :=
        integral_map (measurable_pathRestr c).aemeasurable
          (hg.mul (measurable_condDens_apply hψ c v)).aestronglyMeasurable

omit [IsProbabilityMeasure W] in
lemma condDens_nonneg (hψ0 : ∀ v b, 0 ≤ ψ v b) (c : ℝ≥0) (v : 𝕍) (x : Set.Iic c → ℝ) :
    0 ≤ condDens W c ψ v x :=
  integral_nonneg fun _ => hψ0 _ _

lemma integral_condDens (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    (hψ : Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) => ψ p.1 p.2)) (v : 𝕍) (hψ1 : ∫ b, ψ v b ∂W = 1)
    (c : ℝ≥0) : ∫ b, condDens W c ψ v (pathRestr c b) ∂W = 1 := by
  have hψi : Integrable (ψ v) W := Integrable.of_integral_ne_zero (by rw [hψ1]; exact one_ne_zero)
  have h := integral_mul_eq_condDens hW hψ v hψi c (g := fun _ => (1 : ℝ)) measurable_const
    (C := 1) (fun _ => by simp)
  simp only [one_mul] at h
  rw [← h, hψ1]

lemma integrable_condDens (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    (hψ : Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) => ψ p.1 p.2)) (v : 𝕍) (hψ1 : ∫ b, ψ v b ∂W = 1)
    (c : ℝ≥0) : Integrable (fun b => condDens W c ψ v (pathRestr c b)) W :=
  Integrable.of_integral_ne_zero (by rw [integral_condDens hW hψ v hψ1 c]; exact one_ne_zero)

/-- `condDens` is a version of the conditional expectation on `σ(b|[0,c])`. -/
lemma condDens_ae_eq_condExp (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    (hψ : Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) => ψ p.1 p.2)) (v : 𝕍) (hψ1 : ∫ b, ψ v b ∂W = 1)
    (c : ℝ≥0) :
    (fun b => condDens W c ψ v (pathRestr c b)) =ᵐ[W]
      W[ψ v | bmPast (fun t (b : ℝ≥0 → ℝ) => b t) c] := by
  have hψi : Integrable (ψ v) W := Integrable.of_integral_ne_zero (by rw [hψ1]; exact one_ne_zero)
  have hle : bmPast (fun t (b : ℝ≥0 → ℝ) => b t) c ≤ MeasurableSpace.pi := bmPast_le measurable_coord c
  have hcdi := integrable_condDens hW hψ v hψ1 c
  refine ae_eq_condExp_of_forall_setIntegral_eq hle hψi (fun s _ _ => hcdi.integrableOn)
    (fun s hs _ => ?_) ?_
  · obtain ⟨A, hA, rfl⟩ := hs
    have key := integral_mul_eq_condDens hW hψ v hψi c (g := A.indicator 1)
      (measurable_one.indicator hA) (C := 1)
      (fun x => by by_cases hx : x ∈ A <;> simp [hx])
    have hpre : MeasurableSet (pathRestr c ⁻¹' A) := measurable_pathRestr c hA
    have e : ∀ f : (ℝ≥0 → ℝ) → ℝ, ∫ b in pathRestr c ⁻¹' A, f b ∂W =
        ∫ b, A.indicator 1 (pathRestr c b) * f b ∂W := by
      intro f
      rw [← integral_indicator hpre]
      exact integral_congr_ae (Eventually.of_forall fun b =>
        indicator_preimage_eq_mul (pathRestr c) A f b)
    show ∫ b in pathRestr c ⁻¹' A, condDens W c ψ v (pathRestr c b) ∂W =
      ∫ b in pathRestr c ⁻¹' A, ψ v b ∂W
    rw [e, e, key]
  · have : Measurable[bmPast (fun t (b : ℝ≥0 → ℝ) => b t) c]
        (fun b => condDens W c ψ v (pathRestr c b)) :=
      (measurable_condDens_apply hψ c v).comp (comap_measurable _)
    exact this.stronglyMeasurable.aestronglyMeasurable

end Wiener

/-! ### The germ-density lemma -/

variable {W : Measure (ℝ≥0 → ℝ)}

end GermDensity

end LengthMarkov
end QuantumZipper
