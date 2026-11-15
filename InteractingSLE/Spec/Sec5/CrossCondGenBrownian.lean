/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenLim
import InteractingSLE.WangWu.ReverseContactImgLevy

/-!
# One Brownian motion for a contact word before killing

Packet PROVE-CROSSCOND-GEN. The Brownian-continuation argument of
`WangWu.ReverseContactImgLevy` uses no strict separation, so it applies to contact words.
The definitions `frzM`, the stopping-time helpers and generic Brownian-completion results
are reused directly; the only adapters below replace the geometric input by `IsContactWord`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open WangWu.ImgDrv MartChar Sec7.PhaseSelAdapt Sec7.PhaseSelFull Sec7.Aux117

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → ℝ≥0} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The killed martingale part is continuous before `T`. -/
theorem IsContactWord.continuousOn_martProc (hK : IsContactWord W VL VR T) (ρ : Fin nL ⊕ Fin nR → ℝ) (ω : Ω) :
    ContinuousOn (fun t => martProc ρ W (jointV VL VR) t ω) {t | (t : WithTop ℝ≥0) < T ω} := by
  have hVc : ∀ j, ContinuousOn (fun t => jointV VL VR j t ω) {t | (t : WithTop ℝ≥0) < T ω} := fun j => by
    cases j with
    | inl i => exact (hK.pathL ω i).1
    | inr i => exact (hK.pathR ω i).1
  simp only [martProc, martValue]
  exact ((hK.contW ω).sub continuousOn_const).add (continuousOn_const.mul
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((hVc j).sub continuousOn_const)))

variable (hκ : 0 < κ) (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
  (hK : IsContactWord W VL VR T) (hWa : StronglyAdapted 𝓖 W) (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i))
  (hVRa : ∀ j, StronglyAdapted 𝓖 (VR j)) (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0))
  (hσm : ∀ ω, Monotone (σ · ω)) (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
  (hσlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ σ n ω)
  (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
    (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
    (coupProc κ ρL ρR W VL VR z))
include hκ hnull hK hWa hVLa hVRa hσ hσm hσT hσlim hmart

/-- **The driving Brownian motion of a killed word, continued after the killing time.** On `Ω × Ω₀` there is a
Brownian motion `B` of the product filtration, with continuous paths and `B₀ = 0`, and a time-zero event `G` of full
measure on which the localizing times exhaust `[0, T)` and `B = M/√κ` before `T`. -/
theorem IsContactWord.exists_brownian :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (B : ℝ≥0 → Ω × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓖 𝓦) B (P.prod P₀) ∧ (∀ p, Continuous fun t => B t p) ∧
        (∀ p, B 0 p = 0) ∧ ∃ G : Set Ω, MeasurableSet[𝓖 0] G ∧ P Gᶜ = 0 ∧
          (∀ ω ∈ G, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ locN W VL VR σ n ω) ∧
          ∀ (p : Ω × Ω₀) (t : ℝ≥0), p.1 ∈ G → (t : WithTop ℝ≥0) < T p.1 →
            B t p = martProc (jointρ ρL ρR) W (jointV VL VR) t p.1 / Real.sqrt κ := by
  classical
  set ρ := jointρ ρL ρR with hρ
  set V := jointV VL VR with hV
  -- the good event
  set Good : Set Ω := {ω | (∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ σ n ω) ∧
    ∀ T₀ : ℝ≥0, T ω = T₀ → ∃ L, Tendsto (fun t => martProc ρ W V t ω) (𝓝[<] T₀) (𝓝 L)} with hGood
  have hgood : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hσlim, hK.ae_tendsto_martProc hσT hσ hWa hVLa hVRa hκ hmart hσm hσlim] with ω h1 h2
    exact ⟨h1, h2⟩
  set N := toMeasurable P Goodᶜ with hN
  have hN0 : P N = 0 := by rw [hN, measure_toMeasurable]; exact ae_iff.1 hgood
  set G := Nᶜ with hGdef
  have hG0 : MeasurableSet[𝓖 0] G := (hnull N (measurableSet_toMeasurable _ _) hN0).compl
  have hGsub : ∀ ω ∈ G, ω ∈ Good := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl]; exact hN0
  have hGex : ∀ ω ∈ G, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ locN W VL VR σ n ω :=
    fun ω hω u hu => hK.exists_le_locN hσT hσm (hGsub ω hω).1 hu
  -- the frozen noise
  set Bv : ℝ≥0 → Ω → ℝ := fun t ω => frzM ρ W V T G t ω / Real.sqrt κ with hBvdef
  have hBvc : ∀ ω, Continuous fun t => Bv t ω := fun ω =>
    (continuous_frzM (fun ω _ => hK.continuousOn_martProc ρ ω) (fun ω hω => (hGsub ω hω).2) ω).div_const _
  have hT0 : ∀ ω, ((0 : ℝ≥0) : WithTop ℝ≥0) < T ω := fun ω =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 zero_le) (hσT 0 ω)
  have hBv0 : ∀ ω, Bv 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hBvdef, frzM_of_lt hω (hT0 ω), martProc, martValue, sub_self, mul_zero,
        Finset.sum_const_zero, add_zero, zero_div]
    · simp only [hBvdef, frzM_of_notMem hω, zero_div]
  -- the stopping times
  set S : ℕ → Ω → ℝ≥0 := fun m ω => if ω ∈ G then locN W VL VR σ m ω else 0 with hSdef
  have hSmono : ∀ ω, Monotone fun m => S m ω := fun ω m m' hmm' => by
    by_cases hω : ω ∈ G
    · simp only [hSdef, hω, ↓reduceIte]
      exact hK.locN_mono hσT hσm ω hmm'
    · simp only [hSdef, hω, ↓reduceIte, le_refl]
  have hSst : ∀ m, IsStoppingTime 𝓖 fun ω => (S m ω : WithTop ℝ≥0) := fun m => by
    convert isStoppingTime_ite hG0 (hK.isStoppingTime_locN hσT hσ hWa hVLa hVRa m) using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [hSdef, hω, ↓reduceIte]
    · simp [hSdef, hω]
  have hSm : ∀ (m : ℕ) (u : ℝ≥0), Measurable[(fun _ : ℕ => 𝓖) m u] fun ω => min u (S m ω) := fun m u =>
    measurable_min_of_isStoppingTime (hSst m) u
  -- the exponential martingales
  have hexp : ∀ m (a : ℝ), Martingale (fun t ω => Real.exp (a * Bv (min t (S m ω)) ω -
      a ^ 2 * ((min t (S m ω) : ℝ≥0) : ℝ) / 2)) ((fun _ : ℕ => 𝓖) m) P := by
    intro m a
    have hMM := hK.martingale_lifeLoc_sys hσT hσ hWa hVLa hVRa hκ hmart m
    have hE : Martingale (fun t ω => Real.exp (a * (martProc ρ (sysW W (σ m)) (sysV W VL VR (σ m))
        (min t (locN W VL VR σ m ω)) ω / Real.sqrt κ) - a ^ 2 * ((min t (locN W VL VR σ m ω) : ℝ≥0) : ℝ) / 2))
        𝓖 P :=
      martingale_exp_lifeLoc hκ (fun ω => hK.continuous_sysW (hσT m) ω) (hK.continuous_sysV hσT m) hMM.1 hMM.2 a
    have h1 := Sec6.Prop65.martingale_indicator_of_measurable hE hG0
    have h2 := Sec6.Prop65.martingale_indicator_of_measurable (martingale_const 𝓖 P (1 : ℝ)) hG0.compl
    convert h1.add h2 using 1
    funext t ω
    simp only [Pi.add_apply]
    by_cases hω : ω ∈ G
    · have hle : min t (locN W VL VR σ m ω) ≤ locN W VL VR σ m ω := min_le_right _ _
      have hlt : ((min t (locN W VL VR σ m ω) : ℝ≥0) : WithTop ℝ≥0) < T ω :=
        lt_of_le_sys (hσT m) (hle.trans (locN_le_σ m ω))
      rw [indicator_of_mem hω, indicator_of_notMem (not_not.2 hω)]
      simp only [hSdef, hω, ↓reduceIte, hBvdef, frzM_of_lt hω hlt, add_zero]
      rw [hK.martProc_sys_eq hσT ρ (hle.trans (locN_le_σ m ω))]
    · rw [indicator_of_notMem hω, indicator_of_mem (show ω ∈ Gᶜ from hω)]
      simp only [hSdef, hω, ↓reduceIte, min_zero, hBvdef, frzM_of_notMem hω, zero_div, mul_zero,
        NNReal.coe_zero, sub_zero, Real.exp_zero, zero_add]
  have hTC := WholeField.isTCExpMartingale_annClock (𝒢 := fun _ : ℕ => 𝓖) (fun _ => monotone_const) hSmono hSm
    hBvc hBv0 hexp
  rw [iSupFiltration_const] at hTC
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, β, hβ, hβc, hβ0⟩ := OneForce.exists_filteredBrownian
  obtain ⟨hB, hBc⟩ := WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise hTC
    (LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hβ) hβc hβ0
  refine ⟨Ω₀, m₀, P₀, hP₀, 𝓦, _, hB, hBc, fun p => ?_, G, hG0, hGc, hGex, fun p t hpG ht => ?_⟩
  · simp only [WholeField.complNoise, WholeField.annClock_zero, hBv0, hβ0, sub_self, zero_add]
  · obtain ⟨m, hm⟩ := hGex p.1 hpG t ht
    have hSm' : t ≤ S m p.1 := by simp only [hSdef, hpG, ↓reduceIte]; exact hm
    have hc : WholeField.annClock S t p.1 = t := WholeField.annClock_eq_of_le hSm'
    rw [WholeField.complNoise_of_eq hc]
    simp only [hc, hBvdef, frzM_of_lt hpG ht]

end Main

end InteractingSLE.Sec5.CrossCond.Gen
