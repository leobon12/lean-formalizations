/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VmSafe

/-!
# SB2(1)'s version half: transience in the launch chart

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half; the endpoint `Vk.SB2RelEndpointStatement`). This is
the part of the endpoint common to every option of decision D4: on `{ζ = ∞}` the flow's lift cannot converge to a
finite point. Hence a finite limit of the relative trace at a finite relative lifetime forces `ζ < ∞`.

* `eqOn_closedH_of_eqOn_H`: two functions continuous on `{0 ≤ Im}` that agree on `ℍ` agree on `{0 ≤ Im}`;
* **`ae_lift_inv`**: almost surely at a launch on the entrance event, one continuous extension `g` of the shifted
  chart's inverse reads the flow from the whole lift: `g (flowLift r) = η (T_L + r) − u` before the life, and the lift
  stays in `{0 ≤ Im}` (the line records `Vc.ae_lineGeom_liftOf`, glued along horizons);
* **`ae_not_tendsto_lift_of_top`**: almost surely there, if `ζ = ∞` the lift has no finite limit at `∞` (physical
  transience `Lw.ae_flowLine_regular`, Theorem 1.3);
* **`ae_ne_top_of_capTrace_tendsto`**: for the driven family `ρ`, a finite left limit of `capTrace ρ` at a finite
  `capLife ρ` forces `ζ < ∞`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vn

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- **Functions continuous on the closed half-plane are determined by their values on `ℍ`.** -/
theorem eqOn_closedH_of_eqOn_H {f g : ℂ → ℂ} (hf : ContinuousOn f {z | 0 ≤ z.im})
    (hg : ContinuousOn g {z | 0 ≤ z.im}) (h : EqOn f g H) : EqOn f g {z | 0 ≤ z.im} := by
  intro w hw
  set v : ℕ → ℂ := fun n => w + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hv
  have hvH : ∀ n, v n ∈ H := fun n => by
    show 0 < (v n).im
    simp only [hv, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hw' : (0 : ℝ) ≤ w.im := hw
    linarith
  have hvS : ∀ n, v n ∈ {z : ℂ | 0 ≤ z.im} := fun n =>
    show (0 : ℝ) ≤ (v n).im from le_of_lt (show (0 : ℝ) < (v n).im from hvH n)
  have hvt : Tendsto v atTop (𝓝 w) := by
    have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝 ((0 : ℝ) * Complex.I)) :=
      ((Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).mul_const _
    have := (tendsto_const_nhds (x := w)).add h1
    simpa [hv] using this
  have hvt' : Tendsto v atTop (𝓝[{z : ℂ | 0 ≤ z.im}] w) :=
    tendsto_nhdsWithin_iff.2 ⟨hvt, Eventually.of_forall hvS⟩
  have hf' := (hf w hw).tendsto.comp hvt'
  have hg' := (hg w hw).tendsto.comp hvt'
  have he : (f ∘ v) = (g ∘ v) := funext fun n => h (hvH n)
  rw [he] at hf'
  exact tendsto_nhds_unique hf' hg'

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **One extension of the chart's inverse reads the flow from the whole lift.** -/
theorem ae_lift_inv (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧ ∀ r : ℝ≥0,
        (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ ω →
        0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
        g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r) - u := by
  filter_upwards [Vc.ae_lineGeom_liftOf h13 hS3 HP] with ω hrec hl hT
  have hTL : Ve.entT κ b jumps E k u η ζ ω ≠ ⊤ := ne_top_of_lt hT
  set t₀ : ℝ≥0 := (Ve.entT κ b jumps E k u η ζ ω).toNNReal with ht₀
  have hcoe : ((t₀ : ℝ≥0) : ℝ≥0∞) = Ve.entT κ b jumps E k u η ζ ω := ENNReal.coe_toNNReal hTL
  have e2 : (Ve.entT κ b jumps E k u η ζ ω).toReal = (t₀ : ℝ) := rfl
  -- a record with a horizon beyond any given relative time `r` before the life
  have hrecAt : ∀ r : ℝ≥0, ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ ω → ∃ (T : ℝ≥0) (S₁ : ℝ), (T : ℝ≥0∞) ≤ ζ ω ∧
      Ve.entT κ b jumps E k u η ζ ω < T ∧ 0 < S₁ ∧ (Ve.entT κ b jumps E k u η ζ ω).toReal + S₁ < T ∧
      (r : ℝ) < S₁ := by
    intro r hr
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
  -- the facts of one record at a relative time below its horizon
  have hread : ∀ r : ℝ≥0, ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ ω → ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
      EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
      0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
      g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω (t₀ + r) - u := by
    intro r hr
    obtain ⟨T, S₁, hTζ, hvis, hS₁, hS₁T, hrS⟩ := hrecAt r hr
    obtain ⟨p, g, β', γ, tL, Wr, ηr, -, ⟨-, hgc, hgi, -, -⟩, ⟨-, -, -, -, htL, hγp, -, hlift⟩, hag, -, hlo⟩ :=
      hrec hl T hTζ hvis S₁ hS₁ hS₁T
    have htL' : t₀ = tL := by
      have := congrArg ENNReal.toNNReal htL
      rw [ENNReal.toNNReal_coe] at this
      exact this.symm
    have hγr : Ve.flowLift κ b jumps E k u η ζ ω r = γ r := by
      rw [hlo r hrS, ← htL']
      rfl
    refine ⟨g, hgc, hgi, by rw [hγr]; exact hγp.2.2.1 r, ?_⟩
    rw [hγr, hlift r, htL', hag (tL + r) (by push_cast; linarith)]
  -- one extension for all times
  obtain ⟨g₀, hg₀c, hg₀i⟩ : ∃ g₀ : ℂ → ℂ, ContinuousOn g₀ {z | 0 ≤ z.im} ∧
      EqOn g₀ (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H := by
    have h0 : ((t₀ + 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [add_zero, hcoe]; exact hT
    obtain ⟨g, hgc, hgi, -, -⟩ := hread 0 h0
    exact ⟨g, hgc, hgi⟩
  refine ⟨g₀, hg₀c, fun r hr => ?_⟩
  obtain ⟨g, hgc, hgi, him, hval⟩ := hread r hr
  refine ⟨him, ?_⟩
  rw [eqOn_closedH_of_eqOn_H hg₀c hgc (hg₀i.trans hgi.symm) him]
  exact hval

/-- **Transience in the launch chart**: on `{ζ = ∞}` the lift has no finite limit at `∞`. -/
theorem ae_not_tendsto_lift_of_top (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω → ζ ω = ⊤ →
      ∀ z : ℂ, ¬ Tendsto (Ve.flowLift κ b jumps E k u η ζ ω) atTop (𝓝 z) := by
  filter_upwards [ae_lift_inv h13 hS3 HP, Lw.ae_flowLine_regular h13 HP.kappa_pos HP.flow]
    with ω hinv hreg hl hT hζ z hz
  obtain ⟨g, hgc, hg⟩ := hinv hl hT
  set t₀ : ℝ≥0 := (Ve.entT κ b jumps E k u η ζ ω).toNNReal with ht₀
  have hlt : ∀ r : ℝ≥0, ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ ω := fun r => by rw [hζ]; exact ENNReal.coe_lt_top
  have hS : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hmem : ∀ r, Ve.flowLift κ b jumps E k u η ζ ω r ∈ {z : ℂ | 0 ≤ z.im} := fun r => (hg r (hlt r)).1
  have hzS : z ∈ {z : ℂ | 0 ≤ z.im} := hS.mem_of_tendsto hz (Eventually.of_forall hmem)
  have hz' : Tendsto (Ve.flowLift κ b jumps E k u η ζ ω) atTop (𝓝[{z : ℂ | 0 ≤ z.im}] z) :=
    tendsto_nhdsWithin_iff.2 ⟨hz, Eventually.of_forall hmem⟩
  -- the flow converges, against transience
  have hη : Tendsto (fun r : ℝ≥0 => η ω (t₀ + r)) atTop (𝓝 (g z + u)) := by
    have := ((hgc z hzS).tendsto.comp hz').add_const (u : ℂ)
    refine this.congr fun r => ?_
    simp only [Function.comp_apply, (hg r (hlt r)).2, sub_add_cancel]
  have htr : Tendsto (fun r : ℝ≥0 => ‖η ω (t₀ + r)‖) atTop atTop :=
    (hreg.2.2.2.2 hζ).comp (tendsto_atTop_mono (fun r => le_add_self) tendsto_id)
  exact not_tendsto_atTop_of_tendsto_nhds (hη.norm) htr

/-- The capacity clock of a driven curve increases to its finite lifetime from below. -/
theorem tendsto_capClock_nhdsLT {ρ : ℝ → ℂ} (hρ : IsDrivenCurve ρ) {v : ℝ≥0} (hv : capLife ρ = v) :
    Tendsto (fun r : ℝ≥0 => (capClock ρ r).toNNReal) atTop (𝓝[<] v) := by
  have hlt : ∀ r : ℝ≥0, (capClock ρ r).toNNReal < v := fun r => by
    have := hρ.ofReal_capClock_lt r.2
    rw [hv] at this
    exact ENNReal.coe_lt_coe.1 this
  have hmono : Monotone fun r : ℝ≥0 => (capClock ρ r).toNNReal := fun r r' hrr' =>
    Real.toNNReal_le_toNNReal (hρ.strictMonoOn_capClock.monotoneOn r.2 r'.2 hrr')
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩, Eventually.of_forall hlt⟩
  · have ha' : (a : ℝ≥0∞) < capLife ρ := by rw [hv]; exact ENNReal.coe_lt_coe.2 ha
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 ha'
    filter_upwards [eventually_ge_atTop (n : ℝ≥0)] with r hr
    refine lt_of_lt_of_le ?_ (hmono hr)
    have : (a : ℝ≥0∞) < ((capClock ρ ((n : ℝ≥0) : ℝ)).toNNReal : ℝ≥0∞) := by
      rw [NNReal.coe_natCast]; exact hn
    exact ENNReal.coe_lt_coe.1 this
  · exact Eventually.of_forall fun r => (hlt r).trans ha

/-- **A finite limit of the family's capacity trace at a finite lifetime forces `ζ < ∞`.** -/
theorem ae_ne_top_of_capTrace_tendsto (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      IsDrivenCurve (ρ ω) → capLife (ρ ω) ≠ ⊤ → ∀ z : ℂ,
        Tendsto (capTrace (ρ ω)) (𝓝[<] (capLife (ρ ω)).toNNReal) (𝓝 z) → ζ ω ≠ ⊤ := by
  filter_upwards [hρ, ae_not_tendsto_lift_of_top h13 hS3 HP] with ω hρω hnt hl hT hd hV z hz hζ
  have h1 := (hρω hl hT).1 hζ
  have hc := tendsto_capClock_nhdsLT hd (ENNReal.coe_toNNReal hV).symm
  refine hnt hl hT hζ z ((hz.comp hc).congr fun r => ?_)
  show ρ ω (capInv (ρ ω) ((capClock (ρ ω) r).toNNReal : ℝ)) = _
  rw [Real.coe_toNNReal _ (hd.capClock_nonneg r.coe_nonneg), hd.capInv_eq r.coe_nonneg,
    h1 (show (r : ℝ) ∈ Ici 0 from r.coe_nonneg)]
  show Ve.flowLift κ b jumps E k u η ζ ω (r : ℝ).toNNReal = _
  rw [Real.toNNReal_coe]

end

end InteractingSLE.Theorem14.SB.Vn
