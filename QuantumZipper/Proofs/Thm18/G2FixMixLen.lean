import QuantumZipper.Proofs.Thm18.G2FullMixGeo
import QuantumZipper.Proofs.Thm18.G2FullMixLeb
import QuantumZipper.Proofs.Thm18.G3Area

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 at fixed regions: removing the Palm normalization (length-rooted form)

`G2FixMixStmt γ` (`G2FullMixGeo.lean`) is conditional Proposition 5.5 (Sheffield,
arXiv:1012.4797, Prop. 5.5, p. 65, as used in the proof of Theorem 1.8, §5.4, p. 71) at fixed
regions, stated for the Palm law `g3PalmLaw γ i`. By `g3PalmLaw_apply_eq_lebesgue`
(`G2FullMixLeb.lean`) the Palm law is `Z⁻¹` times the **length-rooted measure**

  `g3LenRoot γ i = (P₀ ⊗ Leb)|{(ω, ℓ) : 0 < ℓ ≤ M(ω)}`,  `M = g3Mass = (ν₁ + ν₀)[−δ, 0]`,

("sample the field from `P₀` and the Palm length `ℓ` from Lebesgue measure on `(0, M(ω)]`",
the rooted measure `ν_h[−δ,0] dh` of Sheffield, Lemma 5.6, p. 66, written in the length
coordinate), and `Z = g3Z γ i = E M ∈ (0, ∞)` depends on `(δ, η)` only, not on the zoom level
`C`. Hence `G2FixMixStmt γ` follows from the same mixing statements for `g3LenRoot`
(`G2FixMixLenXStmt`, `G2FixMixLenRStmt`), in which no normalization and no Palm density occur:

* `g3LenRoot_apply`, `g3LenRoot_univ`, `g3PalmLaw_eq_smul_lenRoot`;
* `g3Z_eq_of_fst` (`Z` is independent of `C`);
* `g2FixMixStmt_of_len : G2FixMixLenXStmt γ μ → G2FixMixLenRStmt γ ν → G2FixMixStmt γ`.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

section LenRoot

variable (γ : ℝ) (i : G3Idx)

/-- The support `{(ω, ℓ) : 0 < ℓ ≤ M(ω)}` of the Palm law. -/
def g3Dom : Set (Ω₀ × ℝ) := {p | 0 < p.2 ∧ ENNReal.ofReal p.2 ≤ g3Mass γ i p.1}

theorem measurableSet_g3Dom : MeasurableSet (g3Dom γ i) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd)
      ((measurable_g3Mass γ i).comp measurable_fst))

/-- **The length-rooted measure**: `P₀ ⊗ Leb` on `{0 < ℓ ≤ M(ω)}`. -/
def g3LenRoot : Measure (Ω₀ × ℝ) := (gffBase.P.prod volume).restrict (g3Dom γ i)

theorem g3Dom_sec (ω : Ω₀) :
    {ℓ : ℝ | (ω, ℓ) ∈ g3Dom γ i} = Ioc 0 (g3Mass γ i ω).toReal := by
  have hM : g3Mass γ i ω ≠ ⊤ := (g3Mass_lt_top γ i ω).ne
  ext ℓ
  simp only [g3Dom, mem_ofPred_eq, mem_Ioc]
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · exact (ENNReal.ofReal_le_iff_le_toReal hM).1 h.2
  · exact (ENNReal.ofReal_le_iff_le_toReal hM).2 h.2

theorem g3LenRoot_apply {S : Set (Ω₀ × ℝ)} (hS : MeasurableSet S) :
    g3LenRoot γ i S = ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ S} ∩ Ioc 0 (g3Mass γ i ω).toReal)
      ∂gffBase.P := by
  rw [g3LenRoot, Measure.restrict_apply hS, Measure.prod_apply (hS.inter (measurableSet_g3Dom γ i))]
  refine lintegral_congr fun ω => ?_
  rw [← g3Dom_sec γ i ω]
  rfl

theorem g3LenRoot_univ : g3LenRoot γ i univ = g3Z γ i := by
  rw [g3LenRoot_apply γ i MeasurableSet.univ, g3Z_eq_lintegral_g3Mass]
  refine lintegral_congr fun ω => ?_
  rw [show {ℓ : ℝ | (ω, ℓ) ∈ (univ : Set (Ω₀ × ℝ))} = univ from rfl, univ_inter,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal (g3Mass_lt_top γ i ω).ne]

theorem isFiniteMeasure_g3LenRoot (hZ : g3Z γ i < ⊤) : IsFiniteMeasure (g3LenRoot γ i) :=
  ⟨by rw [g3LenRoot_univ]; exact hZ⟩

/-- **The Palm law is the normalized length-rooted measure.** -/
theorem g3PalmLaw_eq_smul_lenRoot (hZ : 0 < g3Z γ i ∧ g3Z γ i < ⊤) :
    g3PalmLaw γ i = (g3Z γ i)⁻¹ • g3LenRoot γ i := by
  ext S hS
  rw [g3PalmLaw_apply_eq_lebesgue γ i hZ hS, Measure.smul_apply, smul_eq_mul,
    g3LenRoot_apply γ i hS]

theorem g3PalmLaw_real_eq (hZ : 0 < g3Z γ i ∧ g3Z γ i < ⊤) (S : Set (Ω₀ × ℝ)) :
    (g3PalmLaw γ i).real S = ((g3Z γ i).toReal)⁻¹ * (g3LenRoot γ i).real S := by
  rw [g3PalmLaw_eq_smul_lenRoot γ i hZ, measureReal_def, measureReal_def, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]

end LenRoot

/-- The Palm normalization depends on `(δ, η)` only. -/
theorem g3Z_eq_of_fst {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3Z γ i = g3Z γ i' :=
  g3Z_congr (g3W0_congr h₁ h₂)

/-- **Conditional Proposition 5.5 at `x`, fixed regions, length-rooted form.** As the first half
of `G2FixMixStmt`, for the unnormalized length-rooted measure `g3LenRoot` (field from `P₀`, Palm
length `ℓ` Lebesgue on `(0, M(ω)]`). -/
def G2FixMixLenXStmt (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3LenRoot γ i).real (g3Uf γ i ⁻¹' s ∩ {p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G) -
        μ.real s * (g3LenRoot γ i).real ({p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G)| ≤ ε

/-- **Conditional Proposition 5.5 at `R(x)`, fixed regions, length-rooted form.** -/
def G2FixMixLenRStmt (γ : ℝ) (ν : Measure LawD) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3LenRoot γ i).real (g3Vf γ i ⁻¹' t ∩ {p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G) -
        ν.real t * (g3LenRoot γ i).real ({p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G)| ≤ ε

/-- Transfer of a length-rooted mixing bound to the Palm law (abstract in the events). -/
theorem palm_mix_of_len {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (δ η : ℝ) (c : ℝ)
    (A E : G3Idx → Set (Ω₀ × ℝ)) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ ε' > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
      ∀ G : Set (Ω₀ × ℝ), MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3LenRoot γ i).real (A i ∩ E i ∩ G) - c * (g3LenRoot γ i).real (E i ∩ G)| ≤ ε') :
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
      ∀ G : Set (Ω₀ × ℝ), MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3PalmLaw γ i).real (A i ∩ E i ∩ G) - c * (g3PalmLaw γ i).real (E i ∩ G)| ≤ ε := by
  by_cases h0 : ∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η
  · obtain ⟨i₀, hδ₀, hη₀⟩ := h0
    have hZ₀ := g3Z_pos_lt_top hγ hγ2 i₀
    set z : ℝ := (g3Z γ i₀).toReal with hz
    have hzpos : 0 < z := ENNReal.toReal_pos hZ₀.1.ne' hZ₀.2.ne
    filter_upwards [h (ε * z) (mul_pos hε hzpos)] with C hC i hi G hG
    have hi₁ : i.1.1 = i₀.1.1 := by rw [hi, hδ₀]
    have hi₂ : i.1.2.1 = i₀.1.2.1 := by rw [hi, hη₀]
    have hZi : g3Z γ i = g3Z γ i₀ := g3Z_eq_of_fst hi₁ hi₂
    have hZ := g3Z_pos_lt_top hγ hγ2 i
    rw [g3PalmLaw_real_eq γ i hZ, g3PalmLaw_real_eq γ i hZ, hZi, ← hz]
    have hb := hC i hi G hG
    have e : z⁻¹ * (g3LenRoot γ i).real (A i ∩ E i ∩ G) -
        c * (z⁻¹ * (g3LenRoot γ i).real (E i ∩ G)) =
        z⁻¹ * ((g3LenRoot γ i).real (A i ∩ E i ∩ G) - c * (g3LenRoot γ i).real (E i ∩ G)) := by
      ring
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hzpos)]
    calc z⁻¹ * |(g3LenRoot γ i).real (A i ∩ E i ∩ G) - c * (g3LenRoot γ i).real (E i ∩ G)|
        ≤ z⁻¹ * (ε * z) := mul_le_mul_of_nonneg_left hb (inv_pos.2 hzpos).le
      _ = ε := by field_simp
  · refine Eventually.of_forall fun C i hi => ?_
    exact absurd ⟨i, by rw [hi], by rw [hi]⟩ h0

/-- **`G2FixMixStmt` from its length-rooted form.** -/
theorem g2FixMixStmt_of_len {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ ν : Measure LawD}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hX : G2FixMixLenXStmt γ μ) (hR : G2FixMixLenRStmt γ ν) : G2FixMixStmt γ := by
  refine ⟨μ, ν, inferInstance, inferInstance, fun s hs δ η m hm ε hε => ?_,
    fun t ht δ η m hm ε hε => ?_⟩
  · exact palm_mix_of_len hγ hγ2 δ η (μ.real s) (fun i => g3Uf γ i ⁻¹' s)
      (fun i => {p | |g3X γ i p - i.t₁| + m < i.r₁}) hε
      (fun ε' hε' => hX s hs δ η m hm ε' hε')
  · exact palm_mix_of_len hγ hγ2 δ η (ν.real t) (fun i => g3Vf γ i ⁻¹' t)
      (fun i => {p | |g3R γ i p - i.t₂| + m < i.r₂}) hε
      (fun ε' hε' => hR t ht δ η m hm ε' hε')

end Thm18Asm
end QuantumZipper
