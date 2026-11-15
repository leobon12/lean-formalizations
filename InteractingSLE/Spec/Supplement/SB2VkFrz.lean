/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkEnd

/-!
# SB2(1)'s version half: the measurable driver frozen at the relative lifetime

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). From the measurable driven family `ρ`
(`Vk.exists_drivenFamily`) and the named endpoint input (`Vk.SB2RelEndpointStatement`):

* `exists_relTime`, **`capTrace_capClock`** (deterministic): the capacity reparametrization of the family reads the
  lift at its own capacity time, `capTrace ρ (capClock γ s) = γ s` before the remaining life;
* `capLife_pos`: a driven curve has positive lifetime;
* **`exists_frozenDriver`**: a driver `W`, measurable at every time, from `0`, continuous at **every** sample, `0` off
  a good event `G ∩ D.event` (`G` measurable, conull), equal on it to the canonical driver `segDriver ρ` before the
  relative lifetime `relLife`, and there a generating trace on `[0, relLife]` (the frozen capacity reparametrization)
  with a global Loewner trace that reads the lift in its capacity clock.

The canonical driver is `GB6.CoordB.drivenDriver` of `ρ` (replaced off the good event by the vertical segment, as in
`Lk.exists_measurable_driver_of_drivenCurves`). Its left limit at a finite lifetime is the limit along
`relLife (1 − 2^{-(n+1)})`, measurable through `Vj.exists_jointly_measurable`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vk

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- A driven curve has positive lifetime. -/
theorem capLife_pos {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) : 0 < Sec7.Lemma71C.capLife γ :=
  lt_of_le_of_lt (zero_le) (hγ.ofReal_capClock_lt le_rfl)

/-- **The relative time of a lift time** before the remaining life: `capClock γ s = capClock ρ r` and `ρ r = γ s`. -/
theorem exists_relTime {ρ γ : ℝ → ℂ} {TL Z : ℝ≥0∞} (hTZ : TL < Z) (h1 : Z = ⊤ → EqOn ρ γ (Ici 0))
    (h2 : Z ≠ ⊤ → EqOn ρ (relCurve γ (Z.toReal - TL.toReal)) (Ici 0)) {s : ℝ≥0}
    (hs : ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < Z) :
    ∃ r : ℝ, 0 ≤ r ∧ capClock γ s = capClock ρ r ∧ ρ r = γ s := by
  by_cases hZ : Z = ⊤
  · exact ⟨s, s.2, (capClock_congr_Ici (h1 hZ) s).symm, h1 hZ (show (s : ℝ) ∈ Ici 0 from s.2)⟩
  · have hTL : TL ≠ ⊤ := ne_top_of_lt hTZ
    set ℓ : ℝ := Z.toReal - TL.toReal with hℓ
    have hsℓ : (s : ℝ) < ℓ := by
      rw [← ENNReal.coe_toNNReal hZ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add] at hs
      have e1 : Z.toReal = (Z.toNNReal : ℝ) := rfl
      have e2 : TL.toReal = (TL.toNNReal : ℝ) := rfl
      rw [hℓ, e1, e2]; linarith
    have hℓs : 0 < ℓ - s := sub_pos.2 hsℓ
    have hℓ0 : 0 < ℓ := lt_of_le_of_lt s.2 hsℓ
    set r : ℝ := s / (ℓ - s) with hr
    have hr0 : 0 ≤ r := div_nonneg s.2 hℓs.le
    have hcl : clockOf ℓ r = s := by
      rw [hr]; unfold clockOf
      have hne : ℓ - (s : ℝ) ≠ 0 := hℓs.ne'
      have h1' : 1 + (s : ℝ) / (ℓ - s) = ℓ / (ℓ - s) := by field_simp; ring
      rw [h1', div_div_div_cancel_right₀ hne]
      field_simp
    refine ⟨r, hr0, ?_, ?_⟩
    · rw [capClock_congr_Ici (h2 hZ) r, capClock_relCurve hℓ0 hr0, hcl]
    · rw [h2 hZ (show r ∈ Ici 0 from hr0)]
      show γ (clockOf ℓ r) = γ s
      rw [hcl]

/-- **The capacity reparametrization reads the lift at its capacity time.** -/
theorem capTrace_capClock {ρ γ : ℝ → ℂ} (hρ : IsDrivenCurve ρ) {TL Z : ℝ≥0∞} (hTZ : TL < Z)
    (h1 : Z = ⊤ → EqOn ρ γ (Ici 0)) (h2 : Z ≠ ⊤ → EqOn ρ (relCurve γ (Z.toReal - TL.toReal)) (Ici 0)) {s : ℝ≥0}
    (hs : ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < Z) :
    capTrace ρ (capClock γ s).toNNReal = γ s ∧
      ENNReal.ofReal (capClock γ s) < Sec7.Lemma71C.capLife ρ := by
  obtain ⟨r, hr0, hc, hρr⟩ := exists_relTime hTZ h1 h2 hs
  refine ⟨?_, by rw [hc]; exact hρ.ofReal_capClock_lt hr0⟩
  unfold capTrace
  rw [Real.coe_toNNReal _ (hc ▸ hρ.capClock_nonneg hr0), hc, hρ.capInv_eq hr0, hρr]

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- `(1 − 2^{-(n+1)}) v` increases to `v` from below. -/
theorem tendsto_frac_nhdsLT {v : ℝ≥0} (hv : 0 < v) :
    Tendsto (fun n : ℕ => v * (1 - (1 / 2 : ℝ≥0) ^ (n + 1))) atTop (𝓝[<] v) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0) ^ (n + 1)) atTop (𝓝 0) :=
    (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have h1 : Tendsto (fun n : ℕ => v * (1 - (1 / 2 : ℝ≥0) ^ (n + 1))) atTop (𝓝 (v * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hp)
  rw [tsub_zero, mul_one] at h1
  refine tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun n => ?_⟩
  exact mul_lt_of_lt_one_right hv (tsub_lt_self one_pos (pow_pos (by norm_num) _))

/-- **The measurable driver frozen at the relative lifetime.** -/
theorem exists_frozenDriver (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (hEnd : SB2RelEndpointStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) {ρ : Ω → ℝ → ℂ}
    (hρm : ∀ r, 0 ≤ r → Measurable fun ω => ρ ω r)
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∃ (W : ℝ≥0 → Ω → ℝ) (G : Set Ω), MeasurableSet G ∧ P Gᶜ = 0 ∧
      (∀ q, Measurable (W q)) ∧ (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun q => W q ω) ∧
      (∀ q ω, ω ∉ G ∩ D.event → W q ω = 0) ∧
      ∀ ω ∈ G ∩ D.event, ω ∈ launchSet κ b jumps E (k + 1) ∧ Ve.entT κ b jumps E k u η ζ ω < ζ ω ∧
        IsDrivenCurve (ρ ω) ∧ Sec7.Lemma71C.capLife (ρ ω) = relLife κ b jumps E k u η ζ ω ∧
        (∀ q : ℝ≥0, (q : ℝ≥0∞) < relLife κ b jumps E k u η ζ ω → W q ω = segDriver (ρ ω) q) ∧
        (relLife κ b jumps E k u η ζ ω ≠ ⊤ → ζ ω ≠ ⊤) ∧
        IsGeneratingTrace (fun q => W q ω) (relLife κ b jumps E k u η ζ ω)
          (frz (capTrace (ρ ω)) (relLife κ b jumps E k u η ζ ω)) ∧
        ∃ ηr : ℝ → ℂ, IsLoewnerTrace (fun r : ℝ => W r.toNNReal ω) ηr ∧
          ∀ s : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
            ηr (capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s) =
              Ve.flowLift κ b jumps E k u η ζ ω s := by
  classical
  obtain ⟨G, hGm, hGnull, hG⟩ := Vf.exists_measurable_conull ((D.ae_mem_event_iff).and (hρ.and
    ((ae_isDrivenCurve_family h13 hS3 HP hρ).and ((ae_capLife_eq h13 hS3 HP hρ).and
      (hEnd κ b jumps P h E k u ψ η ζ HP)))))
  have hEv : MeasurableSet D.event := (D.lineFiltC HP).le 0 _ (D.marks_le_lineFiltC HP 0 _ (D.measurableSet_event HP))
  set Gs := G ∩ D.event with hGsdef
  have hGs : MeasurableSet Gs := hGm.inter hEv
  -- the facts on the good event
  have hfact : ∀ ω ∈ Gs, ω ∈ launchSet κ b jumps E (k + 1) ∧ Ve.entT κ b jumps E k u η ζ ω < ζ ω := by
    intro ω hω
    have hl := D.event_subset hω.2
    exact ⟨hl, ((hG ω hω.1).1 hl).1 hω.2⟩
  -- the family, replaced off the good event
  set ρ' : Ω → ℝ → ℂ := fun ω => if ω ∈ Gs then ρ ω else fun t : ℝ => (t : ℂ) * Complex.I with hρ'def
  have hρ'eq : ∀ ω ∈ Gs, ρ' ω = ρ ω := fun ω hω => by simp only [hρ'def, hω, ↓reduceIte]
  have hρ'd : ∀ ω, IsDrivenCurve (ρ' ω) := fun ω => by
    by_cases hω : ω ∈ Gs
    · rw [hρ'eq ω hω]
      obtain ⟨hl, hT⟩ := hfact ω hω
      exact (hG ω hω.1).2.2.1 hl hT
    · simp only [hρ'def, hω, ↓reduceIte]; exact Lk.isDrivenCurve_vert
  have hρ'm : ∀ t, 0 ≤ t → Measurable fun ω => ρ' ω t := fun t ht => by
    have e : (fun ω => ρ' ω t) = fun ω => if ω ∈ Gs then ρ ω t else (t : ℂ) * Complex.I := by
      funext ω; by_cases hω : ω ∈ Gs <;> simp [hρ'def, hω]
    rw [e]
    exact Measurable.ite hGs (hρm t ht) measurable_const
  -- the canonical driver and its lifetime
  set Wr : ℝ≥0 → Ω → ℝ := Supp8.GB6.CoordB.drivenDriver ρ' with hWrdef
  set U : Ω → ℝ≥0∞ := fun ω => Sec7.Lemma71C.capLife (ρ' ω) with hUdef
  have hWrm : ∀ q, Measurable (Wr q) := Supp8.GB6.CoordB.measurable_drivenDriver hρ'd hρ'm
  have hUm : Measurable U := Supp8.GB6.CoordB.measurable_capLife hρ'd hρ'm
  have hWrc : ∀ ω, ContinuousOn (fun q => Wr q ω) {t | (t : ℝ≥0∞) < U ω} :=
    Supp8.GB6.CoordB.continuousOn_drivenDriver hρ'd
  have hWr0 : ∀ ω, Wr 0 ω = 0 := Supp8.GB6.CoordB.drivenDriver_zero hρ'd
  have hgen : ∀ ω, ∀ T : ℝ≥0∞, T < U ω → IsGeneratingTrace (fun q => Wr q ω) T (capTrace (ρ' ω)) :=
    fun ω T hT => Sec5.CrossRestart.isGeneratingTrace_congr_drive ((hρ'd ω).isGeneratingTrace hT)
      fun t ht => Supp8.GB6.CoordB.drivenDriver_eq (lt_trans ht hT)
  have hU0 : ∀ ω, 0 < U ω := fun ω => capLife_pos (hρ'd ω)
  -- the facts on the good event, in terms of `U`
  have hUeq : ∀ ω ∈ Gs, U ω = relLife κ b jumps E k u η ζ ω := fun ω hω => by
    obtain ⟨hl, hT⟩ := hfact ω hω
    show Sec7.Lemma71C.capLife (ρ' ω) = _
    rw [hρ'eq ω hω]
    exact (hG ω hω.1).2.2.2.1 hl hT
  have hread : ∀ ω ∈ Gs, ∀ s : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
      capTrace (ρ' ω) (capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s).toNNReal =
        Ve.flowLift κ b jumps E k u η ζ ω s ∧
      ENNReal.ofReal (capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s) < U ω := by
    intro ω hω s hs
    obtain ⟨hl, hT⟩ := hfact ω hω
    obtain ⟨h1, h2⟩ := (hG ω hω.1).2.1 hl hT
    have hd : IsDrivenCurve (ρ ω) := hρ'eq ω hω ▸ hρ'd ω
    have := capTrace_capClock hd hT h1 h2 hs
    have hU' : U ω = Sec7.Lemma71C.capLife (ρ ω) := by
      show Sec7.Lemma71C.capLife (ρ' ω) = _
      rw [hρ'eq ω hω]
    refine ⟨?_, hU' ▸ this.2⟩
    rw [hρ'eq ω hω, this.1]
    show Ve.flowLift κ b jumps E k u η ζ ω (s : ℝ).toNNReal = _
    rw [Real.toNNReal_coe]
  have hlim : ∀ ω ∈ Gs, U ω ≠ ⊤ → (∃ x, Tendsto (fun q => Wr q ω) (𝓝[<] (U ω).toNNReal) (𝓝 x)) ∧
      ∃ z, Tendsto (capTrace (ρ' ω)) (𝓝[<] (U ω).toNNReal) (𝓝 z) := by
    intro ω hω hUt
    obtain ⟨hl, hT⟩ := hfact ω hω
    have hU := hUeq ω hω
    obtain ⟨-, hlim⟩ := (hG ω hω.1).2.2.2.2 hl hT (hU ▸ hUt)
    obtain ⟨x, z, hx, hz⟩ := hlim (fun q => Wr q ω) (capTrace (ρ' ω)) (hWr0 ω) (hU ▸ hWrc ω)
      (fun T hT' => hgen ω T (hU ▸ hT')) fun s hs => (hread ω hω s hs).1
    rw [← hU] at hx hz
    exact ⟨⟨x, hx⟩, z, hz⟩
  -- the left limit at a finite lifetime, measurable
  set S := Gs ∩ {ω | U ω ≠ ⊤} with hSdef
  have hSm : MeasurableSet S := hGs.inter (measurableSet_eq_fun hUm measurable_const).compl
  obtain ⟨F, hFm, hF⟩ := Vj.exists_jointly_measurable (f := fun ω T => ((Wr T ω : ℝ) : ℂ))
    fun T => Complex.measurable_ofReal.comp (hWrm T)
  set dn : ℕ → Ω → ℝ≥0 := fun n ω => (U ω).toNNReal * (1 - (1 / 2 : ℝ≥0) ^ (n + 1)) with hdndef
  have hdnm : ∀ n, Measurable (dn n) := fun n => (ENNReal.measurable_toNNReal.comp hUm).mul_const _
  set g : ℕ → Ω → ℝ := fun n ω => if ω ∈ S then (F (ω, dn n ω)).re else 0 with hgdef
  have hgm : ∀ n, Measurable (g n) := fun n =>
    Measurable.ite hSm (Complex.measurable_re.comp (hFm.comp (measurable_id.prodMk (hdnm n)))) measurable_const
  set Lf : Ω → ℝ := fun ω => if ω ∈ S then limUnder (𝓝[<] (U ω).toNNReal) (fun q => Wr q ω) else 0 with hLfdef
  have hLfm : Measurable Lf := by
    refine measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ S
    · simp only [hgdef, hLfdef, hω, ↓reduceIte]
      obtain ⟨⟨x, hx⟩, -⟩ := hlim ω hω.1 hω.2
      have hv0 : 0 < (U ω).toNNReal := ENNReal.toNNReal_pos (hU0 ω).ne' hω.2
      have : (𝓝[<] (U ω).toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hv0⟩
      rw [hx.limUnder_eq]
      refine (hx.comp (tendsto_frac_nhdsLT hv0)).congr fun n => ?_
      have hlt : ((dn n ω : ℝ≥0) : ℝ≥0∞) < U ω := by
        rw [← ENNReal.coe_toNNReal hω.2, ENNReal.coe_lt_coe]
        exact mul_lt_of_lt_one_right hv0 (tsub_lt_self one_pos (pow_pos (by norm_num) _))
      have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < U ω} := isOpen_lt ENNReal.continuous_coe continuous_const
      have hca : ContinuousAt (fun T => ((Wr T ω : ℝ) : ℂ)) (dn n ω) :=
        Complex.continuous_ofReal.continuousAt.comp ((hWrc ω).continuousAt (hopen.mem_nhds hlt))
      show Wr (dn n ω) ω = (F (ω, dn n ω)).re
      rw [hF ω (dn n ω) hca, Complex.ofReal_re]
    · simp only [hgdef, hLfdef, hω, ↓reduceIte]
      exact tendsto_const_nhds
  -- the frozen driver
  set W : ℝ≥0 → Ω → ℝ := fun q ω => if ω ∈ Gs then frz (fun q => Wr q ω) (U ω) q else 0 with hWdef
  have hWG : ∀ ω ∈ Gs, (fun q => W q ω) = frz (fun q => Wr q ω) (U ω) := fun ω hω => by
    funext q; simp only [hWdef, hω, ↓reduceIte]
  have hWm : ∀ q, Measurable (W q) := by
    intro q
    have e : W q = fun ω => if ω ∈ Gs then (if (q : ℝ≥0∞) < U ω then Wr q ω else Lf ω) else 0 := by
      funext ω
      by_cases hω : ω ∈ Gs
      · simp only [hWdef, hω, ↓reduceIte, frz]
        by_cases hq : (q : ℝ≥0∞) < U ω
        · simp only [hq, ↓reduceIte]
        · have hUt : U ω ≠ ⊤ := fun h' => hq (h' ▸ ENNReal.coe_lt_top)
          simp only [hq, ↓reduceIte, hLfdef, show ω ∈ S from ⟨hω, hUt⟩]
      · simp only [hWdef, hω, ↓reduceIte]
    rw [e]
    exact Measurable.ite hGs (Measurable.ite (measurableSet_lt measurable_const hUm) (hWrm q) hLfm)
      measurable_const
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ Gs
    · simp only [hWdef, hω, ↓reduceIte]
      rw [frz_of_lt (by exact_mod_cast hU0 ω)]
      exact hWr0 ω
    · simp only [hWdef, hω, ↓reduceIte]
  have hWc : ∀ ω, Continuous fun q => W q ω := fun ω => by
    by_cases hω : ω ∈ Gs
    · rw [hWG ω hω]
      exact continuous_frz (hU0 ω) (hWrc ω) fun h' => (hlim ω hω h').1
    · have e : (fun q => W q ω) = fun _ => 0 := by funext q; simp only [hWdef, hω, ↓reduceIte]
      rw [e]; exact continuous_const
  refine ⟨W, G, hGm, hGnull, hWm, hW0, hWc, fun q ω hω => by simp only [hWdef, show ω ∉ Gs from hω, ↓reduceIte],
    fun ω hω => ?_⟩
  obtain ⟨hl, hT⟩ := hfact ω hω
  have hU := hUeq ω hω
  have hd : IsDrivenCurve (ρ ω) := hρ'eq ω hω ▸ hρ'd ω
  have hcl : Sec7.Lemma71C.capLife (ρ ω) = relLife κ b jumps E k u η ζ ω := hρ'eq ω hω ▸ hU
  have hρ'ω := hρ'eq ω hω
  refine ⟨hl, hT, hd, hcl, fun q hq => ?_, fun h' => ((hG ω hω.1).2.2.2.2 hl hT h').1, ?_, ?_⟩
  · have hq' : (q : ℝ≥0∞) < U ω := by rw [hU]; exact hq
    simp only [hWdef, show ω ∈ Gs from hω, ↓reduceIte]
    rw [frz_of_lt hq', hWrdef, Supp8.GB6.CoordB.drivenDriver_eq hq', hρ'ω]
  · rw [hWG ω hω, ← hU, ← hρ'ω]
    exact isGeneratingTrace_frz (hU0 ω) (hgen ω) fun h' => (hlim ω hω h').2
  · obtain ⟨ηr, hηr, hηeq⟩ := exists_loewnerTrace_frz (hU0 ω) (hWr0 ω) (hWrc ω) (hgen ω) (hlim ω hω)
    rw [← hWG ω hω] at hηr
    refine ⟨ηr, hηr, fun s hs => ?_⟩
    obtain ⟨hr1, hr2⟩ := hread ω hω s hs
    obtain ⟨r, hr0, hc, -⟩ := exists_relTime hT ((hG ω hω.1).2.1 hl hT).1 ((hG ω hω.1).2.1 hl hT).2 hs
    have hnn : 0 ≤ capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s := by
      rw [hc]; exact hd.capClock_nonneg hr0
    have hlt : ((capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s).toNNReal : ℝ≥0∞) < U ω := hr2
    have := hηeq _ hlt
    rw [Real.coe_toNNReal _ hnn] at this
    rw [this, hr1]

end

end InteractingSLE.Theorem14.SB.Vk
