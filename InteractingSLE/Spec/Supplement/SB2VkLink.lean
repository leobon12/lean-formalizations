/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkFrz

/-!
# SB2(1)'s version half: the remainder link of the frozen trace

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The driver statement's `link` clause:
`IsRemainderLink (launchChart) η ζ L (Γ + m) Vg` for the frozen capacity reparametrization `Γ` of the driven family.

* **`ae_lift_chart`**: almost surely at a launch on the entrance event, the lift reads the flow through the launch
  chart: `c⁻¹(flowLift r + m) = η(T_L + r)` whenever `flowLift r + m ∈ ℍ` and `T_L + r < ζ` (from the line records
  `Vc.ae_lineGeom_liftOf`);
* `exists_relClock`: the relative physical time `τ` of the family's parameter (`id` when `ζ = ∞`, `clockOf ℓ` when
  `ζ < ∞`);
* **`isRemainderLink_frz`** (deterministic): for a driven family equal to the lift (`ζ = ∞`) or to its `relCurve`
  (`ζ < ∞`), with `ζ < ∞` whenever the lifetime is finite, the frozen capacity reparametrization plus `m` is linked
  to the flow. The clock is `σ s = τ (capInv ρ s)` before the lifetime and `ℓ + (s − Vg)` after a finite one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vk

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- `clockOf ℓ x → ℓ` as `x → ∞`. -/
theorem tendsto_clockOf_atTop (ℓ : ℝ) : Tendsto (clockOf ℓ) atTop (𝓝 ℓ) := by
  have h1 : Tendsto (fun x : ℝ => (1 + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have h2 : Tendsto (fun x : ℝ => ℓ * (1 - (1 + x)⁻¹)) atTop (𝓝 (ℓ * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub h1)
  rw [sub_zero, mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold clockOf
  have hx1 : (1 + x) ≠ 0 := by positivity
  field_simp
  ring

/-- **The relative physical time of the family's parameter.** -/
theorem exists_relClock {ρ γ : ℝ → ℂ} {TL Z : ℝ≥0∞} (hTZ : TL < Z) (h1 : Z = ⊤ → EqOn ρ γ (Ici 0))
    (h2 : Z ≠ ⊤ → EqOn ρ (relCurve γ (Z.toReal - TL.toReal)) (Ici 0)) :
    ∃ τ : ℝ → ℝ, ContinuousOn τ (Ici 0) ∧ StrictMonoOn τ (Ici 0) ∧ τ 0 = 0 ∧ (∀ x, 0 ≤ x → 0 ≤ τ x) ∧
      (∀ x, 0 ≤ x → ((TL.toNNReal + (τ x).toNNReal : ℝ≥0) : ℝ≥0∞) < Z) ∧ (∀ x, 0 ≤ x → ρ x = γ (τ x)) ∧
      (Z ≠ ⊤ → Tendsto τ atTop (𝓝 (Z.toReal - TL.toReal)) ∧ ∀ x, 0 ≤ x → τ x < Z.toReal - TL.toReal) := by
  by_cases hZ : Z = ⊤
  · refine ⟨id, continuousOn_id, strictMono_id.strictMonoOn _, rfl, fun x hx => hx, fun x _ => ?_,
      fun x hx => h1 hZ hx, fun h' => absurd hZ h'⟩
    rw [hZ]; exact ENNReal.coe_lt_top
  · have hTL : TL ≠ ⊤ := ne_top_of_lt hTZ
    set ℓ : ℝ := Z.toReal - TL.toReal with hℓ
    have hℓ0 : 0 < ℓ := by rw [hℓ, sub_pos]; exact (ENNReal.toReal_lt_toReal hTL hZ).2 hTZ
    have hlt : ∀ x, 0 ≤ x → clockOf ℓ x < ℓ := fun x hx => (clockOf_mem_Ico hℓ0 hx).2
    refine ⟨clockOf ℓ, continuousOn_clockOf ℓ, strictMonoOn_clockOf hℓ0, clockOf_zero ℓ,
      fun x hx => clockOf_nonneg hℓ0 hx, fun x hx => ?_, fun x hx => h2 hZ hx,
      fun _ => ⟨tendsto_clockOf_atTop ℓ, hlt⟩⟩
    rw [← ENNReal.coe_toNNReal hZ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add,
      Real.coe_toNNReal _ (clockOf_nonneg hℓ0 hx)]
    have e1 : Z.toReal = (Z.toNNReal : ℝ) := rfl
    have e2 : TL.toReal = (TL.toNNReal : ℝ) := rfl
    have := hlt x hx
    have hℓ' : ℓ = (Z.toNNReal : ℝ) - (TL.toNNReal : ℝ) := by rw [hℓ, e1, e2]
    linarith

section Link

variable {c : Chart} {η : ℝ≥0 → ℂ} {Z : ℝ≥0∞} {L m : ℝ} {γ : ℝ≥0 → ℂ} {ρ : ℝ → ℂ}

/-- The inverse clock of a driven curve is continuous below its lifetime, on `ℝ≥0`. -/
theorem continuousAt_capInv_coe (hρ : IsDrivenCurve ρ) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < capLife ρ) :
    ContinuousAt (fun t : ℝ≥0 => capInv ρ t) s := by
  have hs' : ENNReal.ofReal (s : ℝ) < capLife ρ := by rwa [ENNReal.ofReal_coe_nnreal]
  have h := (hρ.continuousWithinAt_capInv s.2 hs').comp NNReal.continuous_coe.continuousWithinAt
    (mapsTo_univ_iff.2 fun t => show (t : ℝ) ∈ Ici 0 from t.2)
  exact (continuousWithinAt_univ _ _).1 h

/-- **The remainder link of the frozen capacity reparametrization.** -/
theorem isRemainderLink_frz (hρ : IsDrivenCurve ρ) (h1 : Z = ⊤ → EqOn ρ (Vd.liftR γ) (Ici 0))
    (h2 : Z ≠ ⊤ → EqOn ρ (relCurve (Vd.liftR γ) (Z.toReal - (firstVisit η Z L).toReal)) (Ici 0))
    (hfin : capLife ρ ≠ ⊤ → Z ≠ ⊤)
    (hlift : ∀ r : ℝ≥0, (((firstVisit η Z L).toNNReal + r : ℝ≥0) : ℝ≥0∞) < Z → γ r + m ∈ H →
      c.2.1 (γ r + m) = η ((firstVisit η Z L).toNNReal + r)) :
    IsRemainderLink c η Z L (fun s => frz (capTrace ρ) (capLife ρ) s + m) (capLife ρ) := by
  intro hTZ
  obtain ⟨τ, hτc, hτm, hτ0, hτnn, hτlt, hρτ, hτfin⟩ := exists_relClock hTZ h1 h2
  set TL := firstVisit η Z L with hTLdef
  -- the trace reads the lift at `τ (capInv ρ s)`
  have hread : ∀ s : ℝ≥0, (s : ℝ≥0∞) < capLife ρ →
      frz (capTrace ρ) (capLife ρ) s = γ (τ (capInv ρ s)).toNNReal := fun s hs => by
    rw [frz_of_lt hs]
    unfold capTrace
    rw [hρτ _ (capInv_nonneg ρ s)]
    rfl
  -- `τ ∘ capInv` is continuous below the lifetime
  have hcτ : ∀ s : ℝ≥0, (s : ℝ≥0∞) < capLife ρ → ContinuousAt (fun t : ℝ≥0 => τ (capInv ρ t)) s := fun s hs =>
    (continuousWithinAt_univ _ _).1 ((hτc _ (capInv_nonneg ρ s)).comp (f := fun t : ℝ≥0 => capInv ρ t)
      (continuousAt_capInv_coe hρ hs).continuousWithinAt fun t _ => capInv_nonneg ρ t)
  have hmono : ∀ s s' : ℝ≥0, s < s' → (s' : ℝ≥0∞) < capLife ρ →
      (τ (capInv ρ s)).toNNReal < (τ (capInv ρ s')).toNNReal := fun s s' hss' hs' => by
    have h1' := hρ.capInv_lt_capInv s.2 (NNReal.coe_lt_coe.2 hss') (by rwa [ENNReal.ofReal_coe_nnreal])
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (hτnn _ (capInv_nonneg ρ s))).2
      (hτm (capInv_nonneg ρ s) (capInv_nonneg ρ s') h1')
  have hσ0 : (τ (capInv ρ ((0 : ℝ≥0) : ℝ))).toNNReal = 0 := by
    rw [NNReal.coe_zero, hρ.capInv_of_nonpos le_rfl, hτ0, Real.toNNReal_zero]
  by_cases hV : capLife ρ = ⊤
  · -- infinite lifetime: `σ = τ ∘ capInv`
    have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < capLife ρ := fun s => by rw [hV]; exact ENNReal.coe_lt_top
    refine ⟨fun s => (τ (capInv ρ s)).toNNReal, hσ0, fun s s' hss' => hmono s s' hss' (hlt s'),
      continuous_real_toNNReal.comp (continuous_iff_continuousAt.2 fun s => hcτ s (hlt s)), fun s => ⟨?_, ?_⟩⟩
    · exact ⟨fun _ => hτlt _ (capInv_nonneg ρ s), fun _ => hlt s⟩
    · intro hs hH
      beta_reduce at hH ⊢
      rw [hread s hs] at hH ⊢
      exact hlift _ (hτlt _ (capInv_nonneg ρ s)) hH
  · -- finite lifetime `v`: `σ = τ ∘ capInv` before `v`, then `ℓ + (s − v)`
    have hZ : Z ≠ ⊤ := hfin hV
    obtain ⟨hτlim, hτℓ⟩ := hτfin hZ
    set ℓ : ℝ := Z.toReal - TL.toReal with hℓ
    obtain ⟨v, hv⟩ : ∃ v : ℝ≥0, capLife ρ = v := ⟨_, (ENNReal.coe_toNNReal hV).symm⟩
    have hv0 : 0 < v := by have := capLife_pos hρ; rw [hv] at this; exact_mod_cast this
    have hℓ0 : 0 < ℓ := by have := hτℓ 0 le_rfl; rwa [hτ0] at this
    have hltv : ∀ s : ℝ≥0, s < v → (s : ℝ≥0∞) < capLife ρ := fun s hs => by
      rw [hv]; exact ENNReal.coe_lt_coe.2 hs
    classical
    set σ : ℝ≥0 → ℝ≥0 := fun s => if s < v then (τ (capInv ρ s)).toNNReal else ℓ.toNNReal + (s - v) with hσdef
    have hσl : ∀ s, s < v → σ s = (τ (capInv ρ s)).toNNReal := fun s hs => by simp only [hσdef, hs, ↓reduceIte]
    have hσr : ∀ s, v ≤ s → σ s = ℓ.toNNReal + (s - v) := fun s hs => by
      simp only [hσdef, not_lt.2 hs, ↓reduceIte]
    have hτℓ' : ∀ s : ℝ≥0, (τ (capInv ρ s)).toNNReal < ℓ.toNNReal := fun s =>
      (Real.toNNReal_lt_toNNReal_iff_of_nonneg (hτnn _ (capInv_nonneg ρ s))).2 (hτℓ _ (capInv_nonneg ρ s))
    -- the inverse clock tends to `∞` at the lifetime
    have hinv : Tendsto (fun t : ℝ≥0 => capInv ρ t) (𝓝[<] v) atTop := by
      refine tendsto_atTop.2 fun M => ?_
      set M' : ℝ := max M 0
      have hM' : 0 ≤ M' := le_max_right _ _
      have hcl := hρ.ofReal_capClock_lt hM'
      rw [hv] at hcl
      have hc0 := hρ.capClock_nonneg hM'
      have hcv : (capClock ρ M').toNNReal < v := by
        rw [← ENNReal.coe_lt_coe]; exact hcl
      filter_upwards [Ioo_mem_nhdsLT hcv] with t ht
      have hct : capClock ρ M' < t := by
        have := NNReal.coe_lt_coe.2 ht.1
        rwa [Real.coe_toNNReal _ hc0] at this
      have := hρ.capInv_lt_capInv hc0 hct (by rw [ENNReal.ofReal_coe_nnreal]; exact hltv t ht.2)
      rw [hρ.capInv_eq hM'] at this
      exact (le_max_left M 0).trans this.le
    refine ⟨σ, by rw [hσl 0 hv0]; exact hσ0, ?_, ?_, fun s => ⟨?_, ?_⟩⟩
    · -- strictly increasing
      intro s s' hss'
      by_cases hs' : s' < v
      · rw [hσl s (hss'.trans hs'), hσl s' hs']; exact hmono s s' hss' (hltv s' hs')
      · rw [not_lt] at hs'
        rw [hσr s' hs']
        by_cases hs : s < v
        · rw [hσl s hs]; exact lt_of_lt_of_le (hτℓ' s) le_self_add
        · rw [not_lt] at hs
          rw [hσr s hs]
          exact add_lt_add_of_le_of_lt le_rfl (tsub_lt_tsub_right_of_le hs hss')
    · -- continuous
      rw [continuous_iff_continuousAt]
      intro s
      rcases lt_trichotomy s v with hs | hs | hs
      · have hev : (fun t : ℝ≥0 => (τ (capInv ρ t)).toNNReal) =ᶠ[𝓝 s] σ := by
          filter_upwards [Iio_mem_nhds hs] with t ht
          exact (hσl t ht).symm
        exact (continuous_real_toNNReal.continuousAt.comp (hcτ s (hltv s hs))).congr hev
      · subst hs
        have hσs : σ s = ℓ.toNNReal := by rw [hσr s le_rfl, tsub_self, add_zero]
        refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
        · show Tendsto σ (𝓝[<] s) (𝓝 (σ s))
          rw [hσs]
          refine (continuous_real_toNNReal.tendsto ℓ |>.comp (hτlim.comp hinv)).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact (hσl t ht).symm
        · show Tendsto σ (𝓝[>] s) (𝓝 (σ s))
          have hc : Continuous fun t : ℝ≥0 => ℓ.toNNReal + (t - s) :=
            continuous_const.add (continuous_id.sub continuous_const)
          have := (hc.tendsto s).mono_left (nhdsWithin_le_nhds (s := Ioi s))
          rw [tsub_self, add_zero] at this
          rw [hσs]
          refine this.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact (hσr t (le_of_lt ht)).symm
      · have hev : (fun t : ℝ≥0 => ℓ.toNNReal + (t - v)) =ᶠ[𝓝 s] σ := by
          filter_upwards [Ioi_mem_nhds hs] with t ht
          exact (hσr t (le_of_lt ht)).symm
        exact ((continuous_const.add (continuous_id.sub continuous_const)).continuousAt).congr hev
    · -- alive iff before the physical life
      rw [hv]
      constructor
      · intro hs
        rw [hσl s (ENNReal.coe_lt_coe.1 hs)]
        exact hτlt _ (capInv_nonneg ρ s)
      · intro hlt'
        by_contra hs
        rw [ENNReal.coe_lt_coe, not_lt] at hs
        rw [hσr s hs, ← ENNReal.coe_toNNReal hZ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add,
          NNReal.coe_add, Real.coe_toNNReal _ hℓ0.le] at hlt'
        have e1 : Z.toReal = (Z.toNNReal : ℝ) := rfl
        have e2 : TL.toReal = (TL.toNNReal : ℝ) := rfl
        rw [hℓ, e1, e2] at hlt'
        linarith [(s - v).2]
    · intro hs hH
      rw [hv] at hs
      have hs' : s < v := ENNReal.coe_lt_coe.1 hs
      beta_reduce at hH ⊢
      rw [hread s (hltv s hs')] at hH ⊢
      rw [hσl s hs']
      exact hlift _ (hτlt _ (capInv_nonneg ρ s)) hH

end Link

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The lift reads the flow through the launch chart**, almost surely at a launch on the entrance event. -/
theorem ae_lift_chart (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ r : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ ω →
        Ve.flowLift κ b jumps E k u η ζ ω r + (launchEntry κ b jumps E (k + 1) u ω : ℂ) ∈ H →
        (Lv.launchChart κ b jumps E (k + 1) ω).2.1
            (Ve.flowLift κ b jumps E k u η ζ ω r + (launchEntry κ b jumps E (k + 1) u ω : ℂ)) =
          η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r) := by
  filter_upwards [Vc.ae_lineGeom_liftOf h13 hS3 HP] with ω hrec hl hT r hr hH
  have hTL : Ve.entT κ b jumps E k u η ζ ω ≠ ⊤ := ne_top_of_lt hT
  set t₀ : ℝ≥0 := (Ve.entT κ b jumps E k u η ζ ω).toNNReal with ht₀
  have hcoe : ((t₀ : ℝ≥0) : ℝ≥0∞) = Ve.entT κ b jumps E k u η ζ ω := ENNReal.coe_toNNReal hTL
  have e2 : (Ve.entT κ b jumps E k u η ζ ω).toReal = (t₀ : ℝ) := rfl
  -- a horizon beyond `r`
  obtain ⟨T, S₁, hTζ, hvis, hS₁, hS₁T, hrS⟩ : ∃ (T : ℝ≥0) (S₁ : ℝ), (T : ℝ≥0∞) ≤ ζ ω ∧
      Ve.entT κ b jumps E k u η ζ ω < T ∧ 0 < S₁ ∧ (Ve.entT κ b jumps E k u η ζ ω).toReal + S₁ < T ∧
      (r : ℝ) < S₁ := by
    by_cases hζ : ζ ω = ⊤
    · refine ⟨t₀ + r + 2, r + 1, by rw [hζ]; exact le_top, ?_, by positivity, ?_, by linarith⟩
      · rw [← hcoe, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; push_cast; linarith [r.2]
      · rw [e2]; push_cast; linarith
    · set Zt : ℝ≥0 := (ζ ω).toNNReal with hZt
      have hZc : ((Zt : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
      have hr' : (t₀ : ℝ) + r < Zt := by
        rw [← hZc, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add] at hr; exact hr
      refine ⟨Zt, ((r : ℝ) + (Zt - t₀)) / 2, hZc.le, ?_, ?_, ?_, ?_⟩
      · rw [← hcoe, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; linarith [r.2]
      · linarith [r.2]
      · rw [e2]; linarith
      · linarith
  obtain ⟨p, g, β', γ, tL, Wr, ηr, -, ⟨-, -, hgi, -, -⟩, ⟨-, -, -, -, htL, -, -, hlift⟩, hag, -, hlo⟩ :=
    hrec hl T hTζ hvis S₁ hS₁ hS₁T
  have htL' : t₀ = tL := by
    have := congrArg ENNReal.toNNReal htL
    rw [ENNReal.toNNReal_coe] at this
    exact this.symm
  have hγr : Ve.flowLift κ b jumps E k u η ζ ω r = γ r := by
    rw [hlo r hrS, ← htL']
    rfl
  have hγH : γ r ∈ H := by
    have h' : 0 < (Ve.flowLift κ b jumps E k u η ζ ω r + (launchEntry κ b jumps E (k + 1) u ω : ℂ)).im := hH
    rw [Complex.add_im, Complex.ofReal_im, add_zero, hγr] at h'
    exact h'
  have h1 := hgi hγH
  rw [hlift r, Lw.shiftChart_inv, hag (tL + r) (by push_cast; linarith)] at h1
  rw [hγr, htL']
  exact (sub_left_inj.1 h1).symm

end

end InteractingSLE.Theorem14.SB.Vk
