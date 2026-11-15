/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactImgLim
import InteractingSLE.Spec.Sec7.PhaseSelFullWord
import InteractingSLE.Spec.Sec6.Prop65Glue
import InteractingSLE.Spec.Sec7.ContinuityProb3Coding

/-!
# The image driver of the contact step, part 3: Wang–Wu Lemma 2.11 up to the killing time

Packet PROVE-WW-B16, step B5 of PROVE-WW-B15's plan. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`,
ruling R31), Lemma 2.11 (text dump L477–L560): "Suppose the harmonic-mean formula (1.3) holds and, for every fixed `z`
before swallowing, `η_t(z)` is a continuous local martingale … Stop before the first collision whose total weight on
either side is at most −2. Then every reciprocal force gap is locally absolutely integrable, the full force-image integral
equations (1.2) hold, and `W` satisfies (1.1) for a Brownian motion in the given filtration, up to the stopped
lifetime."

**`IsKilledWord.exists_isWordEntrance`** (Lemma 2.11 for a killed word): let `(W, VL, VR)` be a killed word before `T`
(`IsKilledWord`: the deterministic properties of geometric force images before `T`, strictly separated from the driver
at positive times), adapted to a filtration `𝓖` whose time-zero σ-algebra contains the null sets, with explicit
coupling means that are local martingales before `min (swallowTime z) T`, and let `σₙ < T` be stopping times increasing
to `T`. Then on `Ω × Ω₀` (an independent Brownian motion on `Ω₀`) there is a Brownian motion `B` of the product
filtration such that almost surely the integrated driving and force equations of the (random) word `(V₀)` hold on
`[0, T)` driven by `B` (`Sec7.Aux117.IsWordEntrance`).

**Proof.** The martingale part `M` has a limit at a finite `T` (`ae_tendsto_martProc`); frozen there (`frzM`), it
satisfies the exponential-martingale identities along the localizing times `locN n` (landed
`martingale_exp_lifeLoc` for the continued systems), so `WholeField.isTCExpMartingale_annClock` and
`IsTCExpMartingale.isFilteredBrownianReal_complNoise` continue `M/√κ` after `T` by an independent Brownian motion.
The local Tanaka step before a stopping time (`Sec7.PhaseSelFull.ae_forceDefect_left_eq_zero_before`) applied to the
`n`-th continued system before `locN n` removes the singular force motion; the integrated equations of the continued
systems on `[0, locN n)` are transferred to the killed word on `[0, T)` (`isWordEntrance_of_seq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

namespace ImgDrv

open MartChar Sec7.PhaseSelAdapt Sec7.PhaseSelFull Sec7.Aux117

/-! ### Transfer of the integrated equations from an exhausting sequence -/

section Transfer

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}
  {wn : ℕ → ℝ≥0 → ℝ} {vLn : ℕ → Fin nL → ℝ≥0 → ℝ} {vRn : ℕ → Fin nR → ℝ≥0 → ℝ} {s : ℕ → ℝ≥0}

theorem eqOn_toNNReal_of_le {f g : ℝ≥0 → ℝ} {t S : ℝ≥0} (htS : t ≤ S) (h : ∀ r : ℝ≥0, r ≤ S → f r = g r) :
    EqOn (fun x : ℝ => f x.toNNReal) (fun x : ℝ => g x.toNNReal) (uIcc 0 (t : ℝ)) := fun x hx => by
  rw [uIcc_of_le t.coe_nonneg] at hx
  exact h _ ((Real.toNNReal_le_iff_le_coe.2 hx.2).trans htS)

/-- **The integrated equations on `[0, T)` from an exhausting sequence of paths**: if paths that agree with
`(w, vL, vR)` up to `s n` satisfy the integrated equations on `[0, s n)`, and every `t < T` is below some `s n`, then
`(w, vL, vR)` satisfies them on `[0, T)`. -/
theorem isWordEntrance_of_seq (hE : ∀ n, IsWordEntrance a xL xR ρL ρR (wn n) (vLn n) (vRn n) b (s n))
    (hagree : ∀ n (t : ℝ≥0), t ≤ s n → wn n t = w t ∧ (∀ i, vLn n i t = vL i t) ∧ ∀ j, vRn n j t = vR j t)
    (hex : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∃ n, t < s n) :
    IsWordEntrance a xL xR ρL ρR w vL vR b T := by
  have hag0 := hagree 0 0 zero_le
  have hlt : ∀ n (t : ℝ≥0), t < s n → (t : ℝ≥0∞) < (s n : ℝ≥0∞) := fun n t h => by exact_mod_cast h
  have hopen : ∀ n, IsOpen {t : ℝ≥0 | t < s n} := fun n => isOpen_Iio
  -- continuity transfers through the eventual agreement
  have hcont : ∀ {f : ℝ≥0 → ℝ} {fn : ℕ → ℝ≥0 → ℝ},
      (∀ n, ContinuousOn (fn n) {t | (t : ℝ≥0∞) < s n}) → (∀ n (t : ℝ≥0), t ≤ s n → fn n t = f t) →
      ContinuousOn f {t | (t : ℝ≥0∞) < T} := by
    intro f fn hc hag t ht
    obtain ⟨n, hn⟩ := hex t ht
    have hca : ContinuousAt (fn n) t := (hc n).continuousAt (by
      refine (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds ?_
      exact hlt n t hn)
    have hev : fn n =ᶠ[𝓝 t] f := by
      filter_upwards [(hopen n).mem_nhds hn] with r hr
      exact hag n r (le_of_lt hr)
    exact (hca.congr hev).continuousWithinAt
  refine
    { w_zero := by rw [← hag0.1]; exact (hE 0).w_zero
      vL_zero := fun i => by rw [← hag0.2.1 i]; exact (hE 0).vL_zero i
      vR_zero := fun j => by rw [← hag0.2.2 j]; exact (hE 0).vR_zero j
      continuousOn_w := hcont (fun n => (hE n).continuousOn_w) fun n t ht => (hagree n t ht).1
      continuousOn_vL := fun i => hcont (fun n => (hE n).continuousOn_vL i) fun n t ht => (hagree n t ht).2.1 i
      continuousOn_vR := fun j => hcont (fun n => (hE n).continuousOn_vR j) fun n t ht => (hagree n t ht).2.2 j
      antitone_vL := fun t ht => ?_
      vL_le_w := fun t ht i => ?_
      w_le_vR := fun t ht j => ?_
      monotone_vR := fun t ht => ?_
      integrable_gapL := fun t ht i => ?_
      integrable_gapR := fun t ht j => ?_
      w_eq := fun t ht => ?_
      vL_eq := fun t ht i => ?_
      vR_eq := fun t ht j => ?_
      volume_collisionL := fun i => ?_
      volume_collisionR := fun j => ?_ }
  · obtain ⟨n, hn⟩ := hex t ht
    intro i i' hii'
    show vL i' t ≤ vL i t
    rw [← (hagree n t hn.le).2.1 i, ← (hagree n t hn.le).2.1 i']
    exact (hE n).antitone_vL t (hlt n t hn) hii'
  · obtain ⟨n, hn⟩ := hex t ht
    rw [← (hagree n t hn.le).2.1 i, ← (hagree n t hn.le).1]
    exact (hE n).vL_le_w t (hlt n t hn) i
  · obtain ⟨n, hn⟩ := hex t ht
    rw [← (hagree n t hn.le).2.2 j, ← (hagree n t hn.le).1]
    exact (hE n).w_le_vR t (hlt n t hn) j
  · obtain ⟨n, hn⟩ := hex t ht
    intro j j' hjj'
    show vR j t ≤ vR j' t
    rw [← (hagree n t hn.le).2.2 j, ← (hagree n t hn.le).2.2 j']
    exact (hE n).monotone_vR t (hlt n t hn) hjj'
  · obtain ⟨n, hn⟩ := hex t ht
    refine ((hE n).integrable_gapL t (hlt n t hn) i).congr fun x hx => ?_
    have hx' : x ∈ uIcc 0 (t : ℝ) := uIoc_subset_uIcc hx
    have e1 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).1) hx'
    have e2 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).2.1 i) hx'
    simp only at e1 e2
    rw [e1, e2]
  · obtain ⟨n, hn⟩ := hex t ht
    refine ((hE n).integrable_gapR t (hlt n t hn) j).congr fun x hx => ?_
    have hx' : x ∈ uIcc 0 (t : ℝ) := uIoc_subset_uIcc hx
    have e1 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).1) hx'
    have e2 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).2.2 j) hx'
    simp only at e1 e2
    rw [e1, e2]
  · obtain ⟨n, hn⟩ := hex t ht
    have h := (hE n).w_eq t (hlt n t hn)
    rw [(hagree n t hn.le).1] at h
    have eL : ∀ i, (∫ x in (0 : ℝ)..t, ρL i / (wn n x.toNNReal - vLn n i x.toNNReal)) =
        ∫ x in (0 : ℝ)..t, ρL i / (w x.toNNReal - vL i x.toNNReal) := fun i =>
      intervalIntegral.integral_congr fun x hx => by
        have e1 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).1) hx
        have e2 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).2.1 i) hx
        simp only at e1 e2
        simp only [e1, e2]
    have eR : ∀ j, (∫ x in (0 : ℝ)..t, ρR j / (wn n x.toNNReal - vRn n j x.toNNReal)) =
        ∫ x in (0 : ℝ)..t, ρR j / (w x.toNNReal - vR j x.toNNReal) := fun j =>
      intervalIntegral.integral_congr fun x hx => by
        have e1 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).1) hx
        have e2 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).2.2 j) hx
        simp only at e1 e2
        simp only [e1, e2]
    rw [h]
    simp only [eL, eR]
  · obtain ⟨n, hn⟩ := hex t ht
    have h := (hE n).vL_eq t (hlt n t hn) i
    rw [(hagree n t hn.le).2.1 i] at h
    rw [h]
    congr 1
    refine intervalIntegral.integral_congr fun x hx => ?_
    have e1 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).1) hx
    have e2 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).2.1 i) hx
    simp only at e1 e2
    simp only [e1, e2]
  · obtain ⟨n, hn⟩ := hex t ht
    have h := (hE n).vR_eq t (hlt n t hn) j
    rw [(hagree n t hn.le).2.2 j] at h
    rw [h]
    congr 1
    refine intervalIntegral.integral_congr fun x hx => ?_
    have e1 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).1) hx
    have e2 := eqOn_toNNReal_of_le hn.le (fun r hr => (hagree n r hr).2.2 j) hx
    simp only at e1 e2
    simp only [e1, e2]
  · refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null fun n => (hE n).volume_collisionL i)
    obtain ⟨hx0, hxT, hxe⟩ := hx
    obtain ⟨n, hn⟩ := hex _ hxT
    refine mem_iUnion.2 ⟨n, hx0, hlt n _ hn, ?_⟩
    rw [(hagree n _ hn.le).1, (hagree n _ hn.le).2.1 i]
    exact hxe
  · refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null fun n => (hE n).volume_collisionR j)
    obtain ⟨hx0, hxT, hxe⟩ := hx
    obtain ⟨n, hn⟩ := hex _ hxT
    refine mem_iUnion.2 ⟨n, hx0, hlt n _ hn, ?_⟩
    rw [(hagree n _ hn.le).1, (hagree n _ hn.le).2.2 j]
    exact hxe

end Transfer

/-! ### Stopping-time helpers -/

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

open scoped Classical in
theorem isStoppingTime_ite {G : Set Ω} (hG : MeasurableSet[𝓖 0] G) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓖 fun ω => (((if ω ∈ G then τ ω else 0 : ℝ≥0)) : WithTop ℝ≥0) := by
  classical
  intro u
  have e : {ω | (((if ω ∈ G then τ ω else 0 : ℝ≥0)) : WithTop ℝ≥0) ≤ u} =
      (G ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ u}) ∪ Gᶜ := by
    ext ω
    by_cases h : ω ∈ G
    · simp [h]
    · simp only [h, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, false_and, mem_compl_iff,
        not_false_eq_true, or_true, iff_true]
      exact WithTop.coe_le_coe.2 zero_le
  rw [e]
  exact ((𝓖.mono zero_le _ hG).inter (hτ u)).union (𝓖.mono zero_le _ hG).compl

theorem measurable_min_of_isStoppingTime {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0))
    (u : ℝ≥0) : Measurable[𝓖 u] fun ω => min u (τ ω) := by
  refine measurable_of_Iic (mδ := 𝓖 u) fun x => ?_
  by_cases hx : u ≤ x
  · have : (fun ω => min u (τ ω)) ⁻¹' Iic x = univ := by
      ext ω; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]; exact (min_le_left _ _).trans hx
    rw [this]; exact @MeasurableSet.univ _ (𝓖 u)
  · rw [not_le] at hx
    have : (fun ω => min u (τ ω)) ⁻¹' Iic x = {ω | (τ ω : WithTop ℝ≥0) ≤ x} := by
      ext ω
      simp only [mem_preimage, mem_Iic, min_le_iff, mem_ofPred_eq, WithTop.coe_le_coe]
      exact ⟨fun h => h.resolve_left (not_le.2 hx), Or.inr⟩
    rw [this]
    exact 𝓖.mono hx.le _ (hτ x)

end Stop

/-! ### The martingale part frozen at the killing time -/

section Frozen

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

open scoped Classical in
/-- **The martingale part frozen at the killing time**: on `G`, `M` before `T` and its left limit at a finite `T`
afterwards; `0` off `G`. -/
def frzM (ρ : Fin nL ⊕ Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (V : Fin nL ⊕ Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (G : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then
    (if T ω = ⊤ then martProc ρ W V t ω
    else Sec7.RandRestart.extendAt (fun s => martProc ρ W V s ω) (T ω).untopA
      (limUnder (𝓝[<] (T ω).untopA) fun s => martProc ρ W V s ω) t)
  else 0

variable {ρ : Fin nL ⊕ Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {V : Fin nL ⊕ Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0} {G : Set Ω}

theorem untopA_eq_of_eq_coe {x : WithTop ℝ≥0} {T₀ : ℝ≥0} (h : x = T₀) : x.untopA = T₀ := by
  have hne : x ≠ ⊤ := by rw [h]; exact WithTop.coe_ne_top
  exact WithTop.coe_injective ((MartChar.coe_untopA_of_ne_top hne).trans h)

theorem frzM_of_lt {ω : Ω} (hω : ω ∈ G) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < T ω) :
    frzM ρ W V T G t ω = martProc ρ W V t ω := by
  classical
  simp only [frzM, hω, ↓reduceIte]
  by_cases hT : T ω = ⊤
  · simp only [hT, ↓reduceIte]
  · simp only [hT, ↓reduceIte, Sec7.RandRestart.extendAt]
    have hT' : T ω = ((T ω).untopA : WithTop ℝ≥0) := (MartChar.coe_untopA_of_ne_top hT).symm
    have htT : t < (T ω).untopA := by rw [hT'] at ht; exact WithTop.coe_lt_coe.1 ht
    simp only [htT, ↓reduceIte]

theorem frzM_of_notMem {ω : Ω} (hω : ω ∉ G) (t : ℝ≥0) : frzM ρ W V T G t ω = 0 := by
  classical
  simp only [frzM, hω, ↓reduceIte]

theorem continuous_frzM (hc : ∀ ω ∈ G, ContinuousOn (fun t => martProc ρ W V t ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hlim : ∀ ω ∈ G, ∀ T₀ : ℝ≥0, T ω = T₀ → ∃ L, Tendsto (fun t => martProc ρ W V t ω) (𝓝[<] T₀) (𝓝 L))
    (ω : Ω) : Continuous fun t => frzM ρ W V T G t ω := by
  classical
  by_cases hω : ω ∈ G
  · simp only [frzM, hω, ↓reduceIte]
    by_cases hT : T ω = ⊤
    · simp only [hT, ↓reduceIte]
      refine continuousOn_univ.1 ((hc ω hω).mono fun t _ => ?_)
      show (t : WithTop ℝ≥0) < T ω
      rw [hT]; exact WithTop.coe_lt_top t
    · simp only [hT, ↓reduceIte]
      set T₀ := (T ω).untopA with hT₀
      have hTeq : T ω = (T₀ : WithTop ℝ≥0) := (MartChar.coe_untopA_of_ne_top hT).symm
      obtain ⟨L, hL⟩ := hlim ω hω T₀ hTeq
      refine Sec7.RandRestart.continuous_extendAt ?_ ?_
      · refine (hc ω hω).mono fun t ht => ?_
        show (t : WithTop ℝ≥0) < T ω
        rw [hTeq]; exact WithTop.coe_lt_coe.2 ht
      · by_cases hnb : (𝓝[<] T₀).NeBot
        · rw [hL.limUnder_eq]; exact hL
        · rw [Filter.not_neBot.1 hnb]; exact tendsto_bot
  · simp only [frzM, hω, ↓reduceIte]
    exact continuous_const

end Frozen

/-! ### The Brownian motion continued after the killing time -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → ℝ≥0} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The killed martingale part is continuous before `T`. -/
theorem IsKilledWord.continuousOn_martProc (hK : IsKilledWord W VL VR T) (ρ : Fin nL ⊕ Fin nR → ℝ) (ω : Ω) :
    ContinuousOn (fun t => martProc ρ W (jointV VL VR) t ω) {t | (t : WithTop ℝ≥0) < T ω} := by
  have hVc : ∀ j, ContinuousOn (fun t => jointV VL VR j t ω) {t | (t : WithTop ℝ≥0) < T ω} := fun j => by
    cases j with
    | inl i => exact (hK.pathL ω i).1
    | inr i => exact (hK.pathR ω i).1
  simp only [martProc, martValue]
  exact ((hK.contW ω).sub continuousOn_const).add (continuousOn_const.mul
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((hVc j).sub continuousOn_const)))

variable (hκ : 0 < κ) (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
  (hK : IsKilledWord W VL VR T) (hWa : StronglyAdapted 𝓖 W) (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i))
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
theorem IsKilledWord.exists_brownian :
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

/-- **Wang–Wu Lemma 2.11 for a killed word** (up to the stopped lifetime). Let `(W, VL, VR)` be a killed word before
`T`, adapted to `𝓖` (whose time-zero σ-algebra contains the null sets), with explicit coupling means that are local
martingales before `min (swallowTime z) T`, and let `σₙ < T` be stopping times increasing to `T` almost surely. Then on
`Ω × Ω₀` there is a Brownian motion `B` of the product filtration such that, almost surely, the integrated driving and
force equations of the random word `(V₀)` hold on `[0, T)` driven by `B`. -/
theorem IsKilledWord.exists_isWordEntrance :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (B : ℝ≥0 → Ω × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓖 𝓦) B (P.prod P₀) ∧ (∀ p, Continuous fun t => B t p) ∧
        ∀ᵐ p ∂(P.prod P₀), IsWordEntrance κ (fun i => VL i 0 p.1) (fun j => VR j 0 p.1) ρL ρR
          (fun t => W t p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1) (fun t => B t p) (T p.1 : ℝ≥0∞) := by
  classical
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, hB, hBc, hB0, G, hG0, hGc, hGex, hBeq⟩ :=
    hK.exists_brownian hκ hnull hWa hVLa hVRa hσ hσm hσT hσlim hmart
  refine ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, hB, hBc, ?_⟩
  set 𝓘 := WholeField.prodFiltration 𝓖 𝓦 with h𝓘
  have hBpre := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  set S : ℕ → Ω → ℝ≥0 := fun m ω => if ω ∈ G then locN W VL VR σ m ω else 0 with hSdef
  have hSst : ∀ m, IsStoppingTime 𝓖 fun ω => (S m ω : WithTop ℝ≥0) := fun m => by
    convert isStoppingTime_ite hG0 (hK.isStoppingTime_locN hσT hσ hWa hVLa hVRa m) using 1
  -- the integrated equations of the `n`-th continued system before `locN n`
  have hTan : ∀ n, ∀ᵐ p ∂(P.prod P₀), p.1 ∈ G → IsWordEntrance κ (fun i => VL i 0 p.1) (fun j => VR j 0 p.1)
      ρL ρR (fun t => sysW W (σ n) t p.1) (fun i t => sysVL W VL (σ n) i t p.1)
      (fun j t => sysVR W VR (σ n) j t p.1) (fun t => B t p) (locN W VL VR σ n p.1 : ℝ≥0∞) := by
    intro n
    have hς : IsStoppingTime 𝓘 fun p : Ω × Ω₀ => (S n p.1 : WithTop ℝ≥0) := isStoppingTime_fst (hSst n)
    have hW' : ∀ (t : ℝ≥0) (p : Ω × Ω₀), (t : WithTop ℝ≥0) ≤ (S n p.1 : WithTop ℝ≥0) →
        sysW W (σ n) t p.1 = Real.sqrt κ * B t p - (1 / 2) * ((∑ i, ρL i * (sysVL W VL (σ n) i t p.1 - VL i 0 p.1))
          + ∑ j, ρR j * (sysVR W VR (σ n) j t p.1 - VR j 0 p.1)) := by
      intro t p ht
      by_cases hpG : p.1 ∈ G
      · have htl : t ≤ locN W VL VR σ n p.1 := by
          simp only [hSdef, hpG, ↓reduceIte] at ht; exact WithTop.coe_le_coe.1 ht
        have htσ : t ≤ σ n p.1 := htl.trans (locN_le_σ n p.1)
        have htT : (t : WithTop ℝ≥0) < T p.1 := lt_of_le_sys (hσT n) htσ
        have hVL' : ∀ i, sysVL W VL (σ n) i t p.1 = VL i t p.1 := fun i => hK.sysVL_of_le (hσT n) htσ i
        have hVR' : ∀ j, sysVR W VR (σ n) j t p.1 = VR j t p.1 := fun j => hK.sysVR_of_le (hσT n) htσ j
        rw [sysW_of_le htσ, hBeq p t hpG htT]
        simp only [hVL', hVR']
        exact driver_eq_martProc hκ hK.w_zero t p.1
      · have ht0 : t = 0 := by
          simp only [hSdef, hpG, ↓reduceIte] at ht
          exact le_antisymm (WithTop.coe_le_coe.1 ht) zero_le
        subst ht0
        have hVL' : ∀ i, sysVL W VL (σ n) i 0 p.1 = VL i 0 p.1 := fun i => hK.sysVL_of_le (hσT n) zero_le i
        have hVR' : ∀ j, sysVR W VR (σ n) j 0 p.1 = VR j 0 p.1 := fun j => hK.sysVR_of_le (hσT n) zero_le j
        simp only [sysW_zero hK.w_zero, hB0 p, hVL', hVR', sub_self, mul_zero, Finset.sum_const_zero, add_zero]
    have hL := ae_forceDefect_left_eq_zero_before (P := P.prod P₀) (𝓕 := 𝓘) (ρL := ρL) (ρR := ρR)
      (xL := fun p i => VL i 0 p.1) (xR := fun p j => VR j 0 p.1) (W := fun t p => sysW W (σ n) t p.1)
      (VL := fun i t p => sysVL W VL (σ n) i t p.1) (VR := fun j t p => sysVR W VR (σ n) j t p.1) hsk hBpre hς hW'
      (fun p => hK.continuous_sysW (hσT n) p.1) (stronglyAdapted_fst (hK.stronglyAdapted_sysW (hσT n) (hσ n) hWa))
      (fun i => stronglyAdapted_fst (hK.stronglyAdapted_sysVL (hσT n) (hσ n) hWa hVLa i))
      (fun j => stronglyAdapted_fst (hK.stronglyAdapted_sysVR (hσT n) (hσ n) hWa hVRa j))
      (fun p i => hK.isForcePath_sysVL (hσT n) p.1 i) (fun p j => hK.isForcePath_sysVR (hσT n) p.1 j)
      (fun _ t _ => contV_left_le_contW t) (fun p i => hK.antitone_sysVL (hσT n) p.1 i)
      (fun p j => hK.monotone_sysVR (hσT n) p.1 j) (fun p i j s t hst h => hK.merge_sysVL (hσT n) p.1 i j s t hst h)
      (fun p t => hK.antitone_idx_sysVL (hσT n) p.1 t) (fun p t ht i j h => hK.sep_sys (hσT n) p.1 t ht i j h)
    have hR := ae_forceDefect_right_eq_zero_before (P := P.prod P₀) (𝓕 := 𝓘) (ρL := ρL) (ρR := ρR)
      (xL := fun p i => VL i 0 p.1) (xR := fun p j => VR j 0 p.1) (W := fun t p => sysW W (σ n) t p.1)
      (VL := fun i t p => sysVL W VL (σ n) i t p.1) (VR := fun j t p => sysVR W VR (σ n) j t p.1) hsk hBpre hς hW'
      (fun p => hK.continuous_sysW (hσT n) p.1) (stronglyAdapted_fst (hK.stronglyAdapted_sysW (hσT n) (hσ n) hWa))
      (fun i => stronglyAdapted_fst (hK.stronglyAdapted_sysVL (hσT n) (hσ n) hWa hVLa i))
      (fun j => stronglyAdapted_fst (hK.stronglyAdapted_sysVR (hσT n) (hσ n) hWa hVRa j))
      (fun p i => hK.isForcePath_sysVL (hσT n) p.1 i) (fun p j => hK.isForcePath_sysVR (hσT n) p.1 j)
      (fun _ t _ => contW_le_contV_right t) (fun p i => hK.antitone_sysVL (hσT n) p.1 i)
      (fun p j => hK.monotone_sysVR (hσT n) p.1 j) (fun p i j s t hst h => hK.merge_sysVR (hσT n) p.1 i j s t hst h)
      (fun p t => hK.monotone_idx_sysVR (hσT n) p.1 t) (fun p t ht i j h => hK.sep_sys (hσT n) p.1 t ht i j h)
    filter_upwards [hL, hR] with p hLp hRp hpG
    have hSp : S n p.1 = locN W VL VR σ n p.1 := by simp only [hSdef, hpG, ↓reduceIte]
    have hcolL : ∀ u : ℝ≥0, 0 < u → ColliderNe ρL (fun t => sysW W (σ n) t p.1)
        (fun i t => sysVL W VL (σ n) i t p.1) u := fun u hu => by
      unfold ColliderNe
      rw [Finset.filter_false_of_mem fun i _ => (hK.sysVL_lt_sysW (hσT n) p.1 hu i).ne, Finset.sum_empty]
      norm_num
    have hcolR : ∀ u : ℝ≥0, 0 < u → ColliderNe ρR (fun t => sysW W (σ n) t p.1)
        (fun j t => sysVR W VR (σ n) j t p.1) u := fun u hu => by
      unfold ColliderNe
      rw [Finset.filter_false_of_mem fun j _ => (hK.sysW_lt_sysVR (hσT n) p.1 hu j).ne', Finset.sum_empty]
      norm_num
    set b' : ℝ≥0 → ℝ := fun t => (sysW W (σ n) t p.1 + (1 / 2) * ((∑ i, ρL i * (sysVL W VL (σ n) i t p.1 -
      VL i 0 p.1)) + ∑ j, ρR j * (sysVR W VR (σ n) j t p.1 - VR j 0 p.1))) / Real.sqrt κ with hb'
    have hw' : ∀ t, sysW W (σ n) t p.1 = Real.sqrt κ * b' t - (1 / 2) * ((∑ i, ρL i *
        (sysVL W VL (σ n) i t p.1 - VL i 0 p.1)) + ∑ j, ρR j * (sysVR W VR (σ n) j t p.1 - VR j 0 p.1)) :=
      fun t => by simp only [hb']; field_simp; ring
    have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (locN W VL VR σ n p.1 : ℝ≥0∞) →
        (t : WithTop ℝ≥0) ≤ (S n p.1 : WithTop ℝ≥0) := fun t ht => by
      rw [hSp]; exact WithTop.coe_le_coe.2 (ENNReal.coe_lt_coe.1 ht).le
    have hE := isWordEntrance_of_forceDefect_eq_zero (a := κ) (b := b') (xL := fun i => VL i 0 p.1)
      (xR := fun j => VR j 0 p.1) (sysW_zero hK.w_zero p.1) (fun i => hK.sysVL_of_le (hσT n) zero_le i)
      (fun j => hK.sysVR_of_le (hσT n) zero_le j) (hK.continuous_sysW (hσT n) p.1)
      (fun i => hK.isForcePath_sysVL (hσT n) p.1 i) (fun j => hK.isForcePath_sysVR (hσT n) p.1 j)
      (fun t _ => contV_left_le_contW t) (fun t _ => contW_le_contV_right t)
      (hK.antitone_idx_sysVL (hσT n) p.1) (hK.monotone_idx_sysVR (hσT n) p.1) hw'
      (fun t ht i => hLp t (hle t ht) (fun u hu _ => hcolL u hu) i)
      (fun t ht j => hRp t (hle t ht) (fun u hu _ => hcolR u hu) j)
    refine IsWordEntrance.congr_b hE fun t ht => ?_
    have h := hW' t p (hle t ht)
    simp only [hb']
    rw [div_eq_iff hsk]
    linarith
  -- the killed word before `T`
  have hGae : ∀ᵐ p ∂(P.prod P₀), p.1 ∈ G :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hGc)
  filter_upwards [ae_all_iff.2 hTan, hGae] with p hp hpG
  refine isWordEntrance_of_seq (wn := fun n t => sysW W (σ n) t p.1)
    (vLn := fun n i t => sysVL W VL (σ n) i t p.1) (vRn := fun n j t => sysVR W VR (σ n) j t p.1)
    (s := fun n => locN W VL VR σ n p.1) (fun n => hp n hpG) (fun n t ht => ?_) (fun t ht => ?_)
  · have htσ : t ≤ σ n p.1 := ht.trans (locN_le_σ n p.1)
    exact ⟨sysW_of_le htσ, fun i => hK.sysVL_of_le (hσT n) htσ i, fun j => hK.sysVR_of_le (hσT n) htσ j⟩
  · obtain ⟨r, htr, hrT⟩ := WithTop.lt_iff_exists_coe_btwn.1 (show (t : WithTop ℝ≥0) < T p.1 from ht)
    obtain ⟨n, hn⟩ := hGex p.1 hpG r hrT
    exact ⟨n, lt_of_lt_of_le (WithTop.coe_lt_coe.1 htr) hn⟩

end Main

end ImgDrv

end InteractingSLE.WangWu
