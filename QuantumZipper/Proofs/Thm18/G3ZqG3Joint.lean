import QuantumZipper.Proofs.Thm18.G3ZqG3Top
import QuantumZipper.Proofs.Thm18.G3ZqG2DisR
import QuantumZipper.Proofs.Thm18.R18G3TJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: weighted joint mixing of scheme `C` (T5-J)

Generalized copy (D92) of `g3TProfJointMix_weighted` (`R18G3TJoint.lean`) and of the wiring
`g3TProfJointMixStmt_of` (`R18G3THead.lean`), with the plain zooms replaced by abstract zooms `Z`
(at `x`) and `Z'` (at `R(x)`). Conditional independence of the two region zooms given the outside
field (`condIndepCE_twoHalfDisc_palm`, GFF Markov property) needs only joint measurability of the
zooms. The two properties of the plain zoom that the original uses beyond measurability are made
explicit hypotheses:

* `G3pRegionLocStmtZ` (**region locality**): on the margin event, the zoom of the region field
  and the zoom of the full field agree on each cylinder outside a set of small Palm probability,
  for large `C`. For the plain zoom this is `zoomLaw_mem_lawCyl_iff` (the zoom law reads the
  field on a ball of radius `R_s · scaleProxy`) combined with the area input
  `G3TProfAreaStmt` (`g3p_symmDiff_subset_area₁/₂`);
* `G3TProfMixTransferStmtZ` (**per-region transfer**, T5-R for abstract zooms): the G2 mixing
  body of the free scheme implies that of scheme `C` (plain: `G3TProfMixTransferStmt`, from
  `g3TCMStmt_holds` and `G3TCutToProfStmt`, whose `R` side `G3TCutToProfRStmt` is open even for
  the plain zoom).

Headlines: `g3TJointMixZ_of_bodyC`, and `g3UnscaledTransferZ_of_nodes`: the unscaled wedge
transfer with limit `μ(s) ν(t)` from the G2 fixed-point and zoom-locality nodes, the region
locality, the per-region transfer and the unscaled wedge comparison.

Sheffield, arXiv:1012.4797, proof of Thm. 1.8, p. 71. Own bookkeeping copied from the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-- The region zoom at `x` with the abstract zoom `Z`. -/
def g3pUZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (p : Ω₀ × ℝ) :
    LawD := Z i.C (restrictField (circIn i.t₁ i.r₁) (g3pField γ g p.1)) (g3pX γ g i p)

/-- The region zoom at `R(x)` with the abstract zoom `Z'`. -/
def g3pVZ (Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (p : Ω₀ × ℝ) :
    LawD := Z' i.C (restrictField (circIn i.t₂ i.r₂) (g3pField γ g p.1)) (g3pR γ g i p)

theorem measurable_g3pUZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : Measurable[sig₁ i] (g3pUZ Z γ g i) := by
  have h1 : Measurable[sig₁ i] fun p : Ω₀ × ℝ =>
      restrictField (circIn i.t₁ i.r₁) (g3pField γ g p.1) :=
    measurable_comp_fst_palm (measurable_g3pReg₁ γ g i)
  unfold g3pUZ
  exact Measurable.comp (g := fun q : FieldSample × ℝ => Z i.C q.1 q.2)
    (f := fun p : Ω₀ × ℝ => (restrictField (circIn i.t₁ i.r₁) (g3pField γ g p.1), g3pX γ g i p))
    (hZm i.C) (h1.prodMk (measurable_g3pX γ g i))

theorem measurable_g3pVZ (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : Measurable[sig₂ i] (g3pVZ Z' γ g i) := by
  have h1 : Measurable[sig₂ i] fun p : Ω₀ × ℝ =>
      restrictField (circIn i.t₂ i.r₂) (g3pField γ g p.1) :=
    measurable_comp_fst_palm (measurable_g3pReg₂ γ g i)
  unfold g3pVZ
  exact Measurable.comp (g := fun q : FieldSample × ℝ => Z' i.C q.1 q.2)
    (f := fun p : Ω₀ × ℝ => (restrictField (circIn i.t₂ i.r₂) (g3pField γ g p.1), g3pR γ g i p))
    (hZm' i.C) (h1.prodMk (measurable_g3pR γ g i))

/-- Conditional independence of the two region zooms given the outside field (GFF Markov
property; abstract zooms). -/
theorem condIndepCE_g3pZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) :
    CondIndepCE (outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂)
      (fun p => (g3pUZ Z γ g i p, g3pX γ g i p)) (fun p => (g3pVZ Z' γ g i p, g3pR γ g i p))
      (g3pPalmLaw γ g i) := by
  have : IsProbabilityMeasure ((gffBase.P.prod L₀).withDensity fun p => (g3pW γ g i p : ℝ≥0∞)) :=
    isProbabilityMeasure_g3p γ g i
  exact condIndepCE_twoHalfDisc_palm gffBase.gff i.r₁_pos i.r₂_pos i.dist_le (L₀ := L₀)
    (measurable_g3pW γ g i) (integrable_g3pW γ g i)
    ((measurable_g3pUZ hZm γ g i).prodMk (measurable_g3pX γ g i))
    ((measurable_g3pVZ hZm' γ g i).prodMk (measurable_g3pR γ g i))

/-- **Region locality of the abstract zooms on the margin event** (hypothesis; see the module
docstring). -/
def G3pRegionLocStmtZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
      (g3pPalmLaw γ (g3wProf γ) i).real
        ((g3pUZ Z γ (g3wProf γ) i ⁻¹' s ∩ g3pX γ (g3wProf γ) i ⁻¹' {x | |x - i.t₁| + m < i.r₁}) ∆
          (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩
            g3pX γ (g3wProf γ) i ⁻¹' {x | |x - i.t₁| + m < i.r₁})) ≤ ε ∧
      (g3pPalmLaw γ (g3wProf γ) i).real
        ((g3pVZ Z' γ (g3wProf γ) i ⁻¹' t ∩ g3pR γ (g3wProf γ) i ⁻¹' {x | |x - i.t₂| + m < i.r₂}) ∆
          (g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩
            g3pR γ (g3wProf γ) i ⁻¹' {x | |x - i.t₂| + m < i.r₂})) ≤ ε

/-- **T5-J, weighted conjunct, for abstract zooms**, from the mixing body of scheme `C` and region
locality (copy of `g3TProfJointMix_weighted`). -/
theorem g3TJointMixZ_of_bodyC (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    {γ : ℝ} {μ ν : Measure LawD} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hloc : G3pRegionLocStmtZ Z Z' γ)
    (hbC : G3FixMixBody μ ν (g3pPalmLaw γ (g3wProf γ)) (g3pX γ (g3wProf γ)) (g3pR γ (g3wProf γ))
      (g3pUfZ Z γ (g3wProf γ)) (g3pVfZ Z' γ (g3wProf γ))) :
    G3TJointMixZ Z Z' γ μ ν := by
  intro s hs t ht δ η m hm M ε hε
  set e₀ : ℝ := ε / (10 * (|M| + 1)) with he₀
  have he₀0 : 0 < e₀ := by positivity
  filter_upwards [hbC.1 s hs δ η m hm e₀ he₀0, hbC.2 t ht δ η m hm e₀ he₀0,
    hloc s hs t ht δ η m hm e₀ he₀0]
    with C hB1 hB2 hL i hi w hw hwM
  set g := g3wProf γ with hg
  set P := g3pPalmLaw γ g i with hP
  have h𝒢 := outsideSigmaPalm_le_g3 i
  set I₁ : Set ℝ := {x | |x - i.t₁| + m < i.r₁} with hI₁
  set I₂ : Set ℝ := {x | |x - i.t₂| + m < i.r₂} with hI₂
  have mI₁ : MeasurableSet I₁ :=
    measurableSet_lt (by fun_prop) measurable_const
  have mI₂ : MeasurableSet I₂ :=
    measurableSet_lt (by fun_prop) measurable_const
  have hX : Measurable (g3pX γ g i) := (measurable_g3pX γ g i).mono (sig_le_g3 i _ _) le_rfl
  have hR : Measurable (g3pR γ g i) := (measurable_g3pR γ g i).mono (sig_le_g3 i _ _) le_rfl
  have hU : Measurable (g3pUZ Z γ g i) := (measurable_g3pUZ hZm γ g i).mono (sig_le_g3 i _ _) le_rfl
  have hV : Measurable (g3pVZ Z' γ g i) := (measurable_g3pVZ hZm' γ g i).mono (sig_le_g3 i _ _) le_rfl
  have ms := measurableSet_lawCyl hs
  have mt := measurableSet_lawCyl ht
  have hE1 : MeasurableSet (g3pX γ g i ⁻¹' I₁) := hX mI₁
  have hE2 : MeasurableSet (g3pR γ g i ⁻¹' I₂) := hR mI₂
  have hA1 : MeasurableSet (g3pUZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) := (hU ms).inter hE1
  have hA2 : MeasurableSet (g3pVZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂) := (hV mt).inter hE2
  have hAf1 : MeasurableSet (g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) :=
    (measurable_g3pUfZ hZm γ g i ms).inter hE1
  have hAf2 : MeasurableSet (g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂) :=
    (measurable_g3pVfZ hZm' γ g i mt).inter hE2
  -- conditional independence
  have hci := condIndepCE_g3pZ hZm hZm' γ g i
  have hCA := hci _ _ (ms.prod mI₁) (mt.prod mI₂)
  have hCE := hci _ _ (MeasurableSet.univ.prod mI₁) (MeasurableSet.univ.prod mI₂)
  simp only [mk_preimage_prod, preimage_univ, univ_inter] at hCA hCE
  -- the symmetric differences
  have hd1 : P.real ((g3pUZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∆
      (g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁)) ≤ e₀ :=
    (hL i hi).1
  have hd2 : P.real ((g3pVZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂) ∆
      (g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂)) ≤ e₀ :=
    (hL i hi).2
  -- the mixing body for the region zooms
  have H₁ : ∀ G, MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |P.real ((g3pUZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩ G) -
        μ.real s * P.real (g3pX γ g i ⁻¹' I₁ ∩ G)| ≤ 2 * e₀ := fun G hG => by
    have h1 : |P.real ((g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩ G) -
        μ.real s * P.real (g3pX γ g i ⁻¹' I₁ ∩ G)| ≤ e₀ := hB1 i hi G hG
    have h2 := abs_real_inter_sub_le_of_symmDiff (P := P) hA1 hAf1 (h𝒢 _ hG)
    calc _ ≤ |P.real ((g3pUZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩ G) -
          P.real ((g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩ G)| +
          |P.real ((g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩ G) -
          μ.real s * P.real (g3pX γ g i ⁻¹' I₁ ∩ G)| := abs_sub_le _ _ _
      _ ≤ e₀ + e₀ := add_le_add (h2.trans hd1) h1
      _ = 2 * e₀ := by ring
  have H₂ : ∀ G, MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |P.real ((g3pVZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂) ∩ G) -
        ν.real t * P.real (g3pR γ g i ⁻¹' I₂ ∩ G)| ≤ 2 * e₀ := fun G hG => by
    have h1 : |P.real ((g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂) ∩ G) -
        ν.real t * P.real (g3pR γ g i ⁻¹' I₂ ∩ G)| ≤ e₀ := hB2 i hi G hG
    have h2 := abs_real_inter_sub_le_of_symmDiff (P := P) hA2 hAf2 (h𝒢 _ hG)
    calc _ ≤ |P.real ((g3pVZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂) ∩ G) -
          P.real ((g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂) ∩ G)| +
          |P.real ((g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂) ∩ G) -
          ν.real t * P.real (g3pR γ g i ⁻¹' I₂ ∩ G)| := abs_sub_le _ _ _
      _ ≤ e₀ + e₀ := add_le_add (h2.trans hd2) h1
      _ = 2 * e₀ := by ring
  have habs := abs_integral_inter_sub_le h𝒢 hA1 hA2 hE1 hE2 hCA hCE
    ⟨measureReal_nonneg, measureReal_le_one⟩ H₁ H₂ hw hwM (b := ν.real t)
  have hrep := abs_integral_indicator_sub_le (P := P) (hAf1.inter hAf2) (hA1.inter hA2)
    (hw.mono h𝒢 le_rfl) hwM
  have hsd : P.real (((g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩
      (g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂)) ∆
      ((g3pUZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩ (g3pVZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂))) ≤
      2 * e₀ := by
    have := real_inter_symmDiff_le (P := P) (g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁)
      (g3pUZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) (g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂)
      (g3pVZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂)
    rw [symmDiff_comm (g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁),
      symmDiff_comm (g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂)] at this
    linarith
  have eS : g3pUfZ Z γ g i ⁻¹' s ∩ g3pVfZ Z' γ g i ⁻¹' t ∩ g3pMarg γ g i m =
      (g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩ (g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂) :=
    inter_inter_inter_comm _ _ _ _
  have eM : g3pMarg γ g i m = g3pX γ g i ⁻¹' I₁ ∩ g3pR γ g i ⁻¹' I₂ := rfl
  obtain ⟨p₀⟩ := nonempty_of_isProbabilityMeasure P
  have hM0 : 0 ≤ M := (hwM p₀).1.trans (hwM p₀).2
  rw [eS, eM]
  have hfin : M * e₀ * 10 ≤ ε := by
    rw [he₀, abs_of_nonneg hM0]
    rw [show M * (ε / (10 * (M + 1))) * 10 = ε * (M / (M + 1)) by field_simp]
    exact mul_le_of_le_one_right hε.le ((div_le_one (by linarith)).2 (by linarith))
  calc _ ≤ |∫ p, ((g3pUfZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩
          (g3pVfZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂)).indicator w p ∂P -
        ∫ p, ((g3pUZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩
          (g3pVZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂)).indicator w p ∂P| +
      |∫ p, ((g3pUZ Z γ g i ⁻¹' s ∩ g3pX γ g i ⁻¹' I₁) ∩
          (g3pVZ Z' γ g i ⁻¹' t ∩ g3pR γ g i ⁻¹' I₂)).indicator w p ∂P -
        μ.real s * ν.real t *
          ∫ p, (g3pX γ g i ⁻¹' I₁ ∩ g3pR γ g i ⁻¹' I₂).indicator w p ∂P| := abs_sub_le _ _ _
    _ ≤ M * (2 * e₀) + M * (2 * (2 * e₀) + 2 * (2 * e₀)) :=
        add_le_add (hrep.trans (mul_le_mul_of_nonneg_left hsd hM0)) habs
    _ = M * e₀ * 10 := by ring
    _ ≤ ε := hfin

/-- **Per-region transfer for abstract zooms** (T5-R, `G3TProfMixTransferStmt` at a fixed `γ`;
hypothesis): the G2 mixing body of the free scheme implies that of scheme `C`, with the same
limit laws. -/
def G3TProfMixTransferStmtZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ μ ν : Measure LawD, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    G3FixMixBody μ ν (g3PalmLaw γ) (g3X γ) (g3R γ) (g3UfZ Z γ) (g3VfZ Z' γ) →
    G3FixMixBody μ ν (g3pPalmLaw γ (g3wProf γ)) (g3pX γ (g3wProf γ)) (g3pR γ (g3wProf γ))
      (g3pUfZ Z γ (g3wProf γ)) (g3pVfZ Z' γ (g3wProf γ))

end R18
end QuantumZipper
