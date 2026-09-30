import QuantumZipper.Proofs.Thm18.G3PlDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b): Palm-window bookkeeping of scheme `C`

See `G3PlDefs.lean`. Here: the weight `w = 1{ℓ ≤ U} · Z/U` and its Palm integrals
(`g3pl_integral_eq`), the pointwise comparison of the scheme's Palm point and partner with the
honest ones read from `ν_C` (`g3pl_fine`), and the exceptional set bound (`g3pl_core`).
Own bookkeeping (AGENT_GUIDE cost rule); Sheffield, arXiv:1012.4797, p. 71.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The Palm mass `Z = E ν_C[−δ, 0]` of scheme `C`. -/
def g3plZ (γ δ : ℝ) : ℝ≥0∞ := ∫⁻ ω, g3plV γ ω (Icc (-δ) 0) ∂gffBase.P

/-- The Palm-window weight `w = 1{ℓ ≤ U} · Z/U` (D85). -/
def g3plW (γ δ U : ℝ) (p : Ω₀ × ℝ) : ℝ := if p.2 ≤ U then (g3plZ γ δ).toReal / U else 0

/-- The window event `ℓ ≤ U`. -/
def g3plWin (U : ℝ) : Set (Ω₀ × ℝ) := {p | p.2 ≤ U}

theorem measurableSet_g3plWin (U : ℝ) : MeasurableSet (g3plWin U) :=
  measurableSet_le measurable_snd measurable_const

theorem measurable_g3plW (γ δ U : ℝ) (i : G3Idx) :
    Measurable[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] (g3plW γ δ U) := by
  have hsnd : Measurable[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂]
      (Prod.snd : Ω₀ × ℝ → ℝ) := measurable_iff_comap_le.2 le_sup_right
  have hset : MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] {p : Ω₀ × ℝ | p.2 ≤ U} :=
    hsnd measurableSet_Iic
  exact Measurable.ite hset measurable_const measurable_const

theorem measurableSet_g3pMarg (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (m : ℝ) :
    MeasurableSet (g3pMarg γ g i m) := by
  have hX : Measurable (g3pX γ g i) := (measurable_g3pX γ g i).mono (sig_le_g3 i _ _) le_rfl
  have hR : Measurable (g3pR γ g i) := (measurable_g3pR γ g i).mono (sig_le_g3 i _ _) le_rfl
  exact (measurableSet_lt ((continuous_abs.measurable.comp (hX.sub measurable_const)).add measurable_const) measurable_const).inter
    (measurableSet_lt ((continuous_abs.measurable.comp (hR.sub measurable_const)).add measurable_const) measurable_const)

/-- **The weighted Palm integral as a Lebesgue mixture.** -/
theorem g3pl_integral_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {U : ℝ} (hU : 0 < U)
    {A : Set (Ω₀ × ℝ)} (hA : MeasurableSet A) :
    ∫ p, A.indicator (g3plW γ i.δ U) p ∂(g3pPalmLaw γ (g3wProf γ) i) =
      ((ENNReal.ofReal U)⁻¹ * ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ A ∩ g3plWin U} ∩
        Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∂gffBase.P).toReal := by
  have hZ := g3pZ_pos_lt_top hγ hγ2 i
  have hZe : g3pZ γ (g3wProf γ) i = g3plZ γ i.δ := g3pZ_eq_honest hγ hγ2 i
  have hS : MeasurableSet (A ∩ g3plWin U) := hA.inter (measurableSet_g3plWin U)
  have hw : A.indicator (g3plW γ i.δ U) =
      (A ∩ g3plWin U).indicator (fun _ => (g3plZ γ i.δ).toReal / U) := by
    funext p
    simp only [Set.indicator, g3plW, g3plWin, mem_inter_iff, mem_setOf_eq]
    by_cases h1 : p ∈ A <;> by_cases h2 : p.2 ≤ U <;> simp [h1, h2]
  set K := ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ A ∩ g3plWin U} ∩
    Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∂gffBase.P with hK
  have hKZ : K ≤ g3pZ γ (g3wProf γ) i := by
    rw [g3pZ_eq_lintegral_g3pMass]
    refine lintegral_mono fun ω => ?_
    refine (measure_mono inter_subset_right).trans ?_
    rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal (show g3pMass γ (g3wProf γ) i ω ≠ ⊤ from
      (g3pm_Icc_lt_top γ _ i ω _ _).ne)]
  have hKt : K ≠ ⊤ := (hKZ.trans_lt hZ.2).ne
  rw [hw, integral_indicator_const _ hS, measureReal_def,
    g3pPalmLaw_apply_eq_lebesgue γ _ i hZ hS, smul_eq_mul, ← hK, hZe,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hU.le]
  have hZ0 : (g3plZ γ i.δ).toReal ≠ 0 := by
    rw [← hZe]; exact (ENNReal.toReal_pos hZ.1.ne' hZ.2.ne).ne'
  field_simp

/-! ## The exceptional set -/

/-- The indicator that `ν[−δ/2, 0] < U` or `ν[0, 1/4] < U`. -/
def g3plBadE (δ U : ℝ) (ν : Measure ℝ) : ℝ≥0∞ :=
  open Classical in
  if ν (Icc (-(δ / 2)) 0) < ENNReal.ofReal U ∨ ν (Icc 0 (1 / 4)) < ENNReal.ofReal U then 1 else 0

/-- The bound for the exceptional Palm lengths. -/
def g3plBd (δ U m : ℝ) (ν : Measure ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal U * g3plBadE δ U ν + (min (ENNReal.ofReal U) (ν (Icc (-(3 * m)) 0)) +
    min (ENNReal.ofReal U) (ν (Icc 0 (3 * m))))

theorem measurable_g3plBadE (δ U : ℝ) : Measurable (g3plBadE δ U) := by
  classical
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt (Measure.measurable_coe measurableSet_Icc) measurable_const).union
    (measurableSet_lt (Measure.measurable_coe measurableSet_Icc) measurable_const)

theorem measurable_g3plBd (δ U m : ℝ) : Measurable (g3plBd δ U m) :=
  (measurable_const.mul (measurable_g3plBadE δ U)).add
    ((measurable_const.min (Measure.measurable_coe measurableSet_Icc)).add
      (measurable_const.min (Measure.measurable_coe measurableSet_Icc)))

/-- The exceptional Palm lengths. -/
def g3plN (δ U m : ℝ) (ν : Measure ℝ) : Set ℝ :=
  {ℓ | ℓ ∈ Ioc 0 U ∧ (g3plBadE δ U ν = 1 ∨ ENNReal.ofReal ℓ ≤ ν (Icc (-(3 * m)) 0) ∨
    ENNReal.ofReal ℓ ≤ ν (Icc 0 (3 * m)))}

theorem volume_g3plN_le (δ U m : ℝ) (ν : Measure ℝ) : volume (g3plN δ U m ν) ≤ g3plBd δ U m ν := by
  classical
  have hsub : g3plN δ U m ν ⊆ {ℓ | ℓ ∈ Ioc 0 U ∧ g3plBadE δ U ν = 1} ∪
      ({ℓ | ℓ ∈ Ioc 0 U ∧ ENNReal.ofReal ℓ ≤ ν (Icc (-(3 * m)) 0)} ∪
        {ℓ | ℓ ∈ Ioc 0 U ∧ ENNReal.ofReal ℓ ≤ ν (Icc 0 (3 * m))}) := by
    rintro ℓ ⟨h0, h | h | h⟩
    · exact Or.inl ⟨h0, h⟩
    · exact Or.inr (Or.inl ⟨h0, h⟩)
    · exact Or.inr (Or.inr ⟨h0, h⟩)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_
    ((measure_union_le _ _).trans (add_le_add (volume_Ioc_le_min _) (volume_Ioc_le_min _)))))
  by_cases hE : g3plBadE δ U ν = 1
  · rw [hE, mul_one]
    exact (measure_mono fun ℓ hℓ => hℓ.1).trans (by rw [Real.volume_Ioc, sub_zero])
  · have : {ℓ : ℝ | ℓ ∈ Ioc 0 U ∧ g3plBadE δ U ν = 1} = ∅ := by
      ext ℓ; simp [hE]
    rw [this, measure_empty]; exact bot_le

/-- **Fine Palm lengths.** On the F2-C event, off the exceptional set, the scheme's Palm length is
within the Palm mass, its Palm point and partner are the honest ones, and both lie a margin `m`
inside the two half-discs. -/
theorem g3pl_fine {γ : ℝ} (i : G3Idx) {ω : Ω₀} {U m ℓ : ℝ}
    (hm0 : 0 < m) (hmδ : m ≤ i.δ / 4) (hm16 : m ≤ 1 / 16) (hηm : i.η ≤ m)
    (hF1 : ∀ s ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4),
      (g3pν₁ γ (g3wProf γ) i ω + g3pν₀ γ (g3wProf γ) i ω) s = g3plV γ ω s)
    (hF2 : ∀ s ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4),
      (g3pν₀ γ (g3wProf γ) i ω + g3pν₂ γ (g3wProf γ) i ω) s = g3plV γ ω s)
    (hE : g3plBadE i.δ U (g3plV γ ω) ≠ 1) (hℓ : ℓ ∈ Ioc 0 U)
    (hl : g3plV γ ω (Icc (-(3 * m)) 0) < ENNReal.ofReal ℓ)
    (hr : g3plV γ ω (Icc 0 (3 * m)) < ENNReal.ofReal ℓ) :
    ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc (-i.δ) 0) ∧ ℓ ≤ (g3pMass γ (g3wProf γ) i ω).toReal ∧
      g3pX γ (g3wProf γ) i (ω, ℓ) = lenLeft (g3plV γ ω) ℓ ∧
      g3pR γ (g3wProf γ) i (ω, ℓ) = lenRight (g3plV γ ω) ℓ ∧
      (ω, ℓ) ∈ g3pMarg γ (g3wProf γ) i m := by
  classical
  have hη := i.hη; have hηδ := i.hηδ; have hδ4 := i.hδ
  have hδ : 0 < i.δ := hη.trans hηδ
  have hE' : ENNReal.ofReal U ≤ g3plV γ ω (Icc (-(i.δ / 2)) 0) ∧
      ENNReal.ofReal U ≤ g3plV γ ω (Icc 0 (1 / 4)) := by
    unfold g3plBadE at hE
    by_contra hc
    rw [not_and_or, not_le, not_le] at hc
    exact hE (if_pos hc)
  have hℓU : ENNReal.ofReal ℓ ≤ ENNReal.ofReal U := ENNReal.ofReal_le_ofReal hℓ.2
  have hL : ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc (-(i.δ / 2)) 0) := hℓU.trans hE'.1
  have hR : ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc 0 (1 / 4)) := hℓU.trans hE'.2
  have hwin1 : ∀ y, 0 < y → y ≤ i.δ → Icc (-y) 0 ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4) :=
    fun y _ hy t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hwin2 : ∀ y, 0 < y → y ≤ 1 / 4 → Icc 0 y ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4) :=
    fun y _ hy t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hLδ : ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc (-i.δ) 0) :=
    hL.trans (measure_mono (Icc_subset_Icc_left (by linarith)))
  have hmass : g3pMass γ (g3wProf γ) i ω = g3plV γ ω (Icc (-i.δ) 0) :=
    hF1 _ (hwin1 i.δ hδ le_rfl)
  have hX : g3pX γ (g3wProf γ) i (ω, ℓ) = lenLeft (g3plV γ ω) ℓ := by
    unfold g3pX
    exact (lenLeft_eq_of_agree (a := i.δ / 2) (by linarith)
      (by rw [hF1 _ (hwin1 _ (by linarith) (by linarith))]; exact hL)
      fun y hy hya => hF1 _ (hwin1 y hy (by linarith)))
  have hRR : g3pR γ (g3wProf γ) i (ω, ℓ) = lenRight (g3plV γ ω) ℓ := by
    unfold g3pR
    exact (lenRight_eq_of_agree (a := 1 / 4) (by norm_num)
      (by rw [hF2 _ (hwin2 _ (by norm_num) le_rfl)]; exact hR)
      fun y hy hya => hF2 _ (hwin2 y hy hya))
  have hx1 := neg_le_lenLeft (m := g3plV γ ω) (a := i.δ / 2) (by linarith) hL
  have hx2 := lenLeft_le_neg (m := g3plV γ ω) (a := i.δ / 2) (b := 3 * m) (by linarith) hL hl
  have hr1 := lenRight_le (m := g3plV γ ω) (a := 1 / 4) (by norm_num) hR
  have hr2 := le_lenRight (m := g3plV γ ω) (a := 1 / 4) (b := 3 * m) (by norm_num) hR hr
  refine ⟨hLδ, ?_, hX, hRR, ?_⟩
  · rw [hmass]
    exact (ENNReal.ofReal_le_iff_le_toReal (qBoundaryMeasure_Icc_lt_top γ _ _ _).ne).1 hLδ
  · show |g3pX γ (g3wProf γ) i (ω, ℓ) - i.t₁| + m < i.r₁ ∧
      |g3pR γ (g3wProf γ) i (ω, ℓ) - i.t₂| + m < i.r₂
    rw [hX, hRR]
    have ht1 : i.t₁ = -(i.δ + i.η) / 2 := rfl
    have hr1' : i.r₁ = (i.δ - i.η) / 2 + i.η / 4 := rfl
    have ht2 : i.t₂ = (1 / 2 + i.η) / 2 := rfl
    have hr2' : i.r₂ = (1 / 2 - i.η) / 2 + i.η / 4 := rfl
    constructor
    · have : |lenLeft (g3plV γ ω) ℓ - i.t₁| < i.r₁ - m :=
        abs_sub_lt_iff.2 ⟨by rw [ht1, hr1']; linarith, by rw [ht1, hr1']; linarith⟩
      linarith
    · have : |lenRight (g3plV γ ω) ℓ - i.t₂| < i.r₂ - m :=
        abs_sub_lt_iff.2 ⟨by rw [ht2, hr2']; linarith, by rw [ht2, hr2']; linarith⟩
      linarith

end R18
end QuantumZipper
