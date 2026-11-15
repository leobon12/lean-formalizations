/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelFullLevy
import InteractingSLE.Spec.Sec7.PhaseSelFullEntr

/-!
# §7.4, Aux. lemma 117 before a stopping lifetime, with a random initial word

Packet PROVE-STRIPSYS5 (specification §7.4, Aux. lemma 117, `source/spec/p337-384.md` L897–L939; Aux. lemma 122 uses it
"before the first collision with a distant mark … on an actual positive interval").

`exists_isWordEntrance_before`: let the coordinates be continuous adapted processes with the deterministic properties
of force images and a random initial word, and let every explicit coupling mean be a local martingale before
swallowing **and before a stopping lifetime `T`**. Then, on `Ω × Ω₀` with an independent Brownian motion on `Ω₀`,
there is a Brownian motion `B` of the product filtration, equal to `M/√κ` up to `T`, such that almost surely the
integrated driving and force equations hold on `[0, T')` for every `T' ≤ T` before which every colliding group has
total weight `≠ −2` (on each side).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSelFull

open MartChar Aux117

section Word

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w b b' : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0∞}

/-- `IsWordEntrance` depends on the noise path only before `T`. -/
theorem IsWordEntrance.congr_b (h : IsWordEntrance a xL xR ρL ρR w vL vR b T)
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → b t = b' t) : IsWordEntrance a xL xR ρL ρR w vL vR b' T :=
  { h with w_eq := fun t ht => by rw [← hb t ht]; exact h.w_eq t ht }

end Word

section Driver

variable {nL nR : ℕ} {Ω : Type*} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- The driver in terms of its martingale part, with a random initial word (`MartChar.driver_eq_sqrt_mul_sub`). -/
theorem driver_eq_martProc (hκ : 0 < κ) (hW0 : ∀ ω, W 0 ω = 0) (t : ℝ≥0) (ω : Ω) :
    W t ω = Real.sqrt κ * (martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ)
      - (1 / 2) * ((∑ i, ρL i * (VL i t ω - VL i 0 ω)) + ∑ i, ρR i * (VR i t ω - VR i 0 ω)) := by
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  rw [mul_div_cancel₀ _ hsk]
  simp only [martProc, martValue, jointρ, jointV, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hW0]
  ring

end Driver

section Lift

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀}

theorem stronglyAdapted_fst {𝓦 : Filtration ℝ≥0 m₀} {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted 𝓕 X) :
    StronglyAdapted (WholeField.prodFiltration 𝓕 𝓦) fun t (p : Ω × Ω₀) => X t p.1 := fun t =>
  (((hX t).measurable.comp (Measurable.of_comap_le le_rfl)).mono
    (WholeField.comap_fst_le_prodFiltration 𝓕 𝓦 t) le_rfl).stronglyMeasurable

theorem isStoppingTime_fst {𝓦 : Filtration ℝ≥0 m₀} {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T) :
    IsStoppingTime (WholeField.prodFiltration 𝓕 𝓦) fun p : Ω × Ω₀ => T p.1 := fun i =>
  WholeField.comap_fst_le_prodFiltration 𝓕 𝓦 i _ ⟨_, hT i, rfl⟩

end Lift

section Converse

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Aux. lemma 117 before a stopping lifetime, with a random initial word.** -/
theorem exists_isWordEntrance_before [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i)) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ ρL ρR W VL VR z)) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (B : ℝ≥0 → Ω × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓕 𝓦) B (P.prod P₀) ∧
        (∀ p, Continuous fun t => B t p) ∧
        (∀ (p : Ω × Ω₀) (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ T p.1 →
          B t p = martProc (jointρ ρL ρR) W (jointV VL VR) t p.1 / Real.sqrt κ) ∧
        ∀ᵐ p ∂(P.prod P₀), ∀ T' : ℝ≥0∞, T' ≤ T p.1 →
          (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T' →
            ColliderNe ρL (fun t => W t p.1) (fun i t => VL i t p.1) u ∧
              ColliderNe ρR (fun t => W t p.1) (fun j t => VR j t p.1) u) →
          IsWordEntrance κ (fun i => VL i 0 p.1) (fun j => VR j 0 p.1) ρL ρR (fun t => W t p.1)
            (fun i t => VL i t p.1) (fun j t => VR j t p.1) (fun t => B t p) T' := by
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, hB, hBc, hBeq⟩ := exists_brownian_continuation hκ hW0 hWc hWa hVLa
    hVRa hordL hordR hpathL hpathR hT hmart
  refine ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, hB, hBc, hBeq, ?_⟩
  set 𝓖 := WholeField.prodFiltration 𝓕 𝓦 with h𝓖
  have hBpre := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hW' : ∀ (t : ℝ≥0) (p : Ω × Ω₀), (t : WithTop ℝ≥0) ≤ T p.1 → W t p.1 = Real.sqrt κ * B t p
      - (1 / 2) * ((∑ i, ρL i * (VL i t p.1 - VL i 0 p.1)) + ∑ j, ρR j * (VR j t p.1 - VR j 0 p.1)) :=
    fun t p ht => by rw [hBeq p t ht]; exact driver_eq_martProc hκ hW0 t p.1
  have hL := ae_forceDefect_left_eq_zero_before (P := P.prod P₀) (𝓕 := 𝓖) (ρL := ρL) (ρR := ρR)
    (xL := fun p i => VL i 0 p.1) (xR := fun p j => VR j 0 p.1) (W := fun t p => W t p.1)
    (VL := fun i t p => VL i t p.1) (VR := fun j t p => VR j t p.1) hsk hBpre (isStoppingTime_fst hT) hW'
    (fun p => hWc p.1) (stronglyAdapted_fst hWa) (fun i => stronglyAdapted_fst (hVLa i))
    (fun j => stronglyAdapted_fst (hVRa j)) (fun p => hpathL p.1) (fun p => hpathR p.1)
    (fun p => hordL p.1) (fun p => hantiL p.1) (fun p => hmonoR p.1) (fun p => hmergeL p.1)
    (fun p => hidxL p.1) (fun p => hsep p.1)
  have hR := ae_forceDefect_right_eq_zero_before (P := P.prod P₀) (𝓕 := 𝓖) (ρL := ρL) (ρR := ρR)
    (xL := fun p i => VL i 0 p.1) (xR := fun p j => VR j 0 p.1) (W := fun t p => W t p.1)
    (VL := fun i t p => VL i t p.1) (VR := fun j t p => VR j t p.1) hsk hBpre (isStoppingTime_fst hT) hW'
    (fun p => hWc p.1) (stronglyAdapted_fst hWa) (fun i => stronglyAdapted_fst (hVLa i))
    (fun j => stronglyAdapted_fst (hVRa j)) (fun p => hpathL p.1) (fun p => hpathR p.1)
    (fun p => hordR p.1) (fun p => hantiL p.1) (fun p => hmonoR p.1) (fun p => hmergeR p.1)
    (fun p => hidxR p.1) (fun p => hsep p.1)
  filter_upwards [hL, hR] with p hLp hRp T' hT' hcol
  set b' : ℝ≥0 → ℝ := fun t => (W t p.1 + (1 / 2) * ((∑ i, ρL i * (VL i t p.1 - VL i 0 p.1)) +
    ∑ j, ρR j * (VR j t p.1 - VR j 0 p.1))) / Real.sqrt κ with hb'
  have hw' : ∀ t, W t p.1 = Real.sqrt κ * b' t
      - (1 / 2) * ((∑ i, ρL i * (VL i t p.1 - VL i 0 p.1)) + ∑ j, ρR j * (VR j t p.1 - VR j 0 p.1)) :=
    fun t => by simp only [hb']; field_simp; ring
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T' → (t : WithTop ℝ≥0) ≤ T p.1 := fun t ht => (ht.le.trans hT')
  have hE := isWordEntrance_of_forceDefect_eq_zero (a := κ) (b := b') (hW0 p.1) (fun i => rfl)
    (fun j => rfl) (hWc p.1) (hpathL p.1) (hpathR p.1) (hordL p.1) (hordR p.1) (hidxL p.1) (hidxR p.1) hw'
    (fun t ht i => hLp t (hlt t ht) (fun u hu0 hu => (hcol u hu0 ((ENNReal.coe_le_coe.2 hu).trans_lt ht)).1) i)
    (fun t ht j => hRp t (hlt t ht) (fun u hu0 hu => (hcol u hu0 ((ENNReal.coe_le_coe.2 hu).trans_lt ht)).2) j)
  refine IsWordEntrance.congr_b hE fun t ht => ?_
  have h := hW' t p (hlt t ht)
  simp only [hb']
  rw [div_eq_iff hsk]
  linarith

end Converse

end PhaseSelFull

end Sec7

end InteractingSLE
