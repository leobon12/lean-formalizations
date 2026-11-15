/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6NestWire
import InteractingSLE.Spec.Sec7.OuterGeomInf
import InteractingSLE.Spec.Sec7.SideVisR7Anchor

/-!
# R.6's nested pockets at deterministic relative times

PROVE-R6-NESTED. The candidate transfer of `R6NestWire` is stated at rational **original** times, where the outer
pocket's relative capacity `visitClock … t` is random, while the R.5 word of the outer pocket
(`PocketStopSide.PocketStopPhaseSideLimit`, the antecedent of every R.6 input) is available only at deterministic
relative capacity times. Here the selection is moved to deterministic relative times: at a certified visit with the
tip in a nested pocket `U` (`R6Nest.nestEvent`), the physical tip of the erased traversal stays in `U` and off the
certified frontiers for nearby relative times, so some **rational relative capacity time** `q` has the physical tip
in `U` (`nestRelEvent`). The resulting named input `TwoSeedNestRelInput(Inf)` asks the zero phase only at such a
deterministic time `q`, where the outer word is supplied by the antecedent itself; R.6's comparison then needs the
inner pocket at the original stopping time of relative capacity `q` (supplement p. 475: R.5 "at an enlarged stopping
time"). The anchor form of R.6's selection `SideVis.TwoSeedSharedAnchorInput(Inf)` follows.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Nest

open PocketTraversal Lemma71C PocketStop PocketWordAssembly PocketSeedOpen
  PocketCoupling PocketJordan Hsd PhaseClause PocketStopField PocketMarks SideVis HOuter WangWu PocketCoord

section Defs

variable {Ω : Type*}

/-- **The physical tip of the erased traversal** of the bounded pocket at the relative time `u` (the parameter of
`travAll`; its relative capacity is `capClock (travAll …) u`). -/
def relTip (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (u : ℝ) (ω : Ω) : ℂ :=
  Sec6.erasedPath (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
    (clockOf (Sec6.pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))) u)

/-- **The physical tip of the erased traversal** of the pocket opening at the flow seed. -/
def relTipInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (u : ℝ) (ω : Ω) : ℂ :=
  Sec6.erasedPathInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
    (clockOf (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u)

/-- **The nested-pocket event at the rational relative capacity time `q`** (bounded outer pocket): `q` is a positive
live relative capacity, the inner pair `(R', L')` is in global order with change parameter `rt s`, its pocket is
contained in the outer pocket, and the physical tip at relative capacity `q` lies in it and off both certified
frontiers. -/
def nestRelEvent (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ)
    (βR βL R' L' : Ω → ℝ≥0 → ℂ) (s q : ℚ) : Set Ω :=
  {ω | 0 < q ∧ ((StripSys.rt q : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
    IsChangeConfig (R' ω) (L' ω) (StripSys.rt s) ∧
    cfPocket (R' ω) (L' ω) (StripSys.rt s) ⊆ cfPocket (R ω) (L ω) r ∧
    ∃ u : ℝ, 0 ≤ u ∧ capClock (travAll R L r η ψ ω) u = q ∧
      relTip R L r η u ω ∈ cfPocket (R' ω) (L' ω) (StripSys.rt s) ∧
      negInv (relTip R L r η u ω) ∉ range (βR ω) ∪ range (βL ω)}

/-- **The nested-pocket event at the rational relative capacity time `q`** (pocket opening at the flow seed). -/
def nestRelEventInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ)
    (βR βL R' L' : Ω → ℝ≥0 → ℂ) (s q : ℚ) : Set Ω :=
  {ω | 0 < q ∧ ((StripSys.rt q : ℝ≥0) : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧
    IsChangeConfig (R' ω) (L' ω) (StripSys.rt s) ∧
    cfPocket (R' ω) (L' ω) (StripSys.rt s) ⊆ cfPocket (R ω) (L ω) r ∧
    ∃ u : ℝ, 0 ≤ u ∧ capClock (travAllInf R L r η ψ ω) u = q ∧
      relTipInf R L r η u ω ∈ cfPocket (R' ω) (L' ω) (StripSys.rt s) ∧
      negInv (relTipInf R L r η u ω) ∉ range (βR ω) ∪ range (βL ω)}

/-- **Named, unproved R.6 transfer for one nested candidate at a deterministic relative time** (bounded outer
pocket): for every coherent phase word with a continuous phase, at each rational relative capacity time `q` and
rational inner parameter `s`, almost surely on the test, if the physical tip at relative capacity `q` lies in the
inner pocket of `(R', L')` at `rt s` (contained in the outer pocket, off the certified frontiers), then the phase at
`q` is zero. The outer word at `q` is the antecedent itself. -/
def TwoSeedNestRelInput (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (βR βL R' L' : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAll R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∀ q s : ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ nestRelEvent R L r η ψ βR βL R' L' s q →
        δ (StripSys.rt q) ω = 0

/-- **Named, unproved R.6 transfer for one nested candidate at a deterministic relative time** (pocket opening at
the flow seed). -/
def TwoSeedNestRelInputInf (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (βR βL R' L' : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAllInf R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∀ q s : ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ nestRelEventInf R L r η ψ βR βL R' L' s q →
        δ (StripSys.rt q) ω = 0

end Defs

section Select

variable {Ω : Type*}

/-- A driven curve whose physical tip function `g` is continuous at a relative time `u₀ ≥ 0` with `g u₀` in an open
set `O`: some positive rational relative capacity time has a preimage `u ≥ 0` with `g u ∈ O`. -/
theorem exists_rat_capClock_mem {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {g : ℝ → ℂ} {u₀ : ℝ} (hu₀ : 0 ≤ u₀)
    (hg : ContinuousAt g u₀) {O : Set ℂ} (hO : IsOpen O) (hgO : g u₀ ∈ O) :
    ∃ q : ℚ, 0 < q ∧ ∃ u : ℝ, 0 ≤ u ∧ capClock γ u = q ∧ g u ∈ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hg.preimage_mem_nhds (hO.mem_nhds hgO))
  set u₁ := u₀ + ε / 2 with hu₁
  have h01 : u₀ < u₁ := by rw [hu₁]; linarith
  have hlt := hγ.strictMonoOn_capClock (mem_Ici.2 hu₀) (mem_Ici.2 (hu₀.trans h01.le)) h01
  obtain ⟨q, hq₀, hq₁⟩ := exists_rat_btwn hlt
  obtain ⟨u, hu, hcu⟩ := intermediate_value_Icc h01.le
    (hγ.continuousOn_capClock.mono fun x hx => mem_Ici.2 (hu₀.trans hx.1)) ⟨hq₀.le, hq₁.le⟩
  refine ⟨q, ?_, u, hu₀.trans hu.1, hcu, hball ?_⟩
  · exact_mod_cast lt_of_le_of_lt (hγ.capClock_nonneg hu₀) hq₀
  · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hu.1)]
    linarith [hu.2]

/-- `m(z) = −1/z` is continuous off `0`. -/
theorem continuousOn_negInv : ContinuousOn negInv {0}ᶜ := fun z hz => by
  have : ContinuousAt (fun w : ℂ => -w⁻¹) z := (continuousAt_inv₀ hz).neg
  exact this.continuousWithinAt

/-- **The nested pocket at a rational relative time** (bounded outer pocket, pathwise): a certified visit at the
original time `t` with the tip in a nested pocket gives a rational relative capacity time `q` whose physical tip is
in the same nested pocket and off the certified frontiers. -/
theorem exists_rat_nestRelEvent {R L R' L' βR βL : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ}
    {ψ : Ω → ℂ → ℂ} {W : ℝ → ℝ} {ω : Ω} (hc : IsOuterCfg (R ω) (L ω) r W (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hβR : Sec5.Prop55Half.IsSeedProper (βR ω))
    (hβL : Sec5.Prop55Half.IsSeedProper (βL ω)) {t : ℝ} (hvis : ω ∈ visitEvent R L r η βR βL t) {s : ℚ}
    (hnest : ω ∈ nestEvent R L r η R' L' s t) :
    ∃ q : ℚ, ω ∈ nestRelEvent R L r η ψ βR βL R' L' s q := by
  obtain ⟨htV, hβ⟩ := hvis
  obtain ⟨hcfg', htU, hsub⟩ := hnest
  have hP := hc.erase
  have hγ := (hc.props hψ).1
  set C := cfPocket (R ω) (L ω) r with hCdef
  set τ := firstHit (η ω) (cfArcR (R ω) (L ω) r 1) with hτdef
  set σ := firstHit (η ω) (cfArcR (R ω) (L ω) r 0) with hσdef
  set L₀ := Sec6.pocketClock (η ω) C τ σ σ with hL₀def
  have hL₀ : 0 < L₀ := hP.clock_σ_pos
  set v₀ := Sec6.pocketClock (η ω) C τ σ t with hv₀def
  have hv₀ : 0 < v₀ := erasure_clock_pos_of_visit hP htV
  have hv₀L : v₀ < L₀ := hP.clock_lt_clock_σ ⟨htV.1.1.le, htV.1.2⟩
  set u₀ := v₀ / (L₀ - v₀) with hu₀def
  have hu₀ : 0 < u₀ := div_pos hv₀ (sub_pos.2 hv₀L)
  have hcl : clockOf L₀ u₀ = v₀ := PocketLife.clockOf_div_sub hL₀ hv₀L
  have htip : relTip R L r η u₀ ω = η ω t := by
    show Sec6.erasedPath (η ω) C τ σ (clockOf L₀ u₀) = η ω t
    rw [hcl, Sec6.erasedPath, hP.fibre_clock_of_mem htV]
  have hg : ContinuousAt (fun u => relTip R L r η u ω) u₀ := by
    have h1 : ContinuousAt (clockOf L₀) u₀ := (continuousOn_clockOf L₀).continuousAt (Ici_mem_nhds hu₀)
    have h2 : ContinuousAt (Sec6.erasedPath (η ω) C τ σ) (clockOf L₀ u₀) := by
      rw [hcl]
      exact hP.continuousOn_erasedPath.continuousAt (Icc_mem_nhds hv₀ hv₀L)
    exact h2.comp h1
  have hη0 : η ω t ≠ 0 := ne_zero_of_mem_cfPocket hc.conf htV.2
  set O := cfPocket (R' ω) (L' ω) (StripSys.rt s) ∩
    (({0} : Set ℂ)ᶜ ∩ negInv ⁻¹' (range (βR ω) ∪ range (βL ω))ᶜ) with hOdef
  have hO : IsOpen O := (OuterGeom.isOpen_cfPocket hcfg'.isChangeConfigInc).inter
    (continuousOn_negInv.isOpen_inter_preimage isOpen_compl_singleton
      (hβR.isClosed_range.union hβL.isClosed_range).isOpen_compl)
  have hgO : relTip R L r η u₀ ω ∈ O := by
    rw [htip]
    exact ⟨htU, hη0, hβ⟩
  obtain ⟨q, hq, u, hu, hcu, hgu⟩ := exists_rat_capClock_mem hγ hu₀.le hg hO hgO
  have hlive := hγ.ofReal_capClock_lt hu
  rw [hcu] at hlive
  exact ⟨q, hq, hlive, hcfg', hsub, u, hu, hcu, hgu.1, hgu.2.2⟩

/-- **The nested pocket at a rational relative time** (pocket opening at the flow seed, pathwise). -/
theorem exists_rat_nestRelEventInf {R L R' L' βR βL : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ}
    {ψ : Ω → ℂ → ℂ} {W : ℝ → ℝ} {ω : Ω} (hc : IsOuterCfgInf (R ω) (L ω) r W (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hβR : Sec5.Prop55Half.IsSeedProper (βR ω))
    (hβL : Sec5.Prop55Half.IsSeedProper (βL ω)) {t : ℝ} (hvis : ω ∈ visitEventInf R L r η βR βL t) {s : ℚ}
    (hnest : ω ∈ nestEvent R L r η R' L' s t) :
    ∃ q : ℚ, ω ∈ nestRelEventInf R L r η ψ βR βL R' L' s q := by
  obtain ⟨htV, hβ⟩ := hvis
  obtain ⟨hcfg', htU, hsub⟩ := hnest
  have hP := hc.erase
  have hγ := (hc.props hψ).1
  set C := cfPocket (R ω) (L ω) r with hCdef
  set τ := firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) with hτdef
  set L₀ := Sec6.clockEnd (η ω) C τ with hL₀def
  have hL₀ : 0 < L₀ := hP.clockEnd_pos
  set v₀ := Sec6.pocketClockInf (η ω) C τ t with hv₀def
  have hv₀ : 0 < v₀ := erasureInf_clock_pos_of_visit hP htV
  have hv₀L : v₀ < L₀ := hP.clock_lt_clockEnd htV.1.le
  set u₀ := v₀ / (L₀ - v₀) with hu₀def
  have hu₀ : 0 < u₀ := div_pos hv₀ (sub_pos.2 hv₀L)
  have hcl : clockOf L₀ u₀ = v₀ := PocketLife.clockOf_div_sub hL₀ hv₀L
  have htip : relTipInf R L r η u₀ ω = η ω t := by
    show Sec6.erasedPathInf (η ω) C τ (clockOf L₀ u₀) = η ω t
    rw [hcl, Sec6.erasedPathInf, hP.fibre_clock_of_mem htV]
  have hg : ContinuousAt (fun u => relTipInf R L r η u ω) u₀ := by
    have h1 : ContinuousAt (clockOf L₀) u₀ := (continuousOn_clockOf L₀).continuousAt (Ici_mem_nhds hu₀)
    have h2 : ContinuousAt (Sec6.erasedPathInf (η ω) C τ) (clockOf L₀ u₀) := by
      rw [hcl]
      exact hP.continuousOn_erasedPath.continuousAt (Ico_mem_nhds hv₀ hv₀L)
    exact h2.comp h1
  have hη0 : η ω t ≠ 0 := ne_zero_of_mem_cfPocket hc.conf htV.2
  set O := cfPocket (R' ω) (L' ω) (StripSys.rt s) ∩
    (({0} : Set ℂ)ᶜ ∩ negInv ⁻¹' (range (βR ω) ∪ range (βL ω))ᶜ) with hOdef
  have hO : IsOpen O := (OuterGeom.isOpen_cfPocket hcfg'.isChangeConfigInc).inter
    (continuousOn_negInv.isOpen_inter_preimage isOpen_compl_singleton
      (hβR.isClosed_range.union hβL.isClosed_range).isOpen_compl)
  have hgO : relTipInf R L r η u₀ ω ∈ O := by
    rw [htip]
    exact ⟨htU, hη0, hβ⟩
  obtain ⟨q, hq, u, hu, hcu, hgu⟩ := exists_rat_capClock_mem hγ hu₀.le hg hO hgO
  have hlive := hγ.ofReal_capClock_lt hu
  rw [hcu] at hlive
  exact ⟨q, hq, hlive, hcfg', hsub, u, hu, hcu, hgu.1, hgu.2.2⟩

end Select

section Anchor

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω]
  {P : Measure Ω} {k rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
  {βR βL R' L' : Ω → ℝ≥0 → ℂ}

/-- **R.6's selection in anchor form from the relative-time candidate transfer** (bounded outer pocket): the
countably many candidate statements (rational relative times and rational inner parameters) are intersected
first; then a certified visit (Aux. 42 for the counterflow), its nested pocket and a nearby rational relative time
are selected pathwise. -/
theorem twoSeedSharedAnchorInput_of_nestRel {W : Ω → ℝ → ℝ}
    (hnest : TwoSeedNestRelInput k rL rR 𝓦 P R L r η G h₀ u βR βL R' L')
    (hcfg : ∀ ω ∈ G, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (h42 : ∀ᵐ ω ∂P, Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η ω s) ⊤)
    (hβ : ∀ᵐ ω ∂P, Sec5.Prop55Half.IsSeedProper (βR ω) ∧ Sec5.Prop55Half.IsSeedProper (βL ω))
    (hcover : ∀ t : ℚ, ∀ᵐ ω ∂P, ω ∈ G → ω ∈ visitEvent R L r η βR βL t →
      ∃ s : ℚ, ω ∈ nestEvent R L r η R' L' s t) :
    TwoSeedSharedAnchorInput k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ _ _ hphase hcont
  have hall : ∀ p : ℚ × ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ nestRelEvent R L r η ψ βR βL R' L' p.2 p.1 →
      δ (StripSys.rt p.1) ω = 0 := fun p => hnest A hA hAG hPA ψ hJ hPt n hn a δ hphase hcont p.1 p.2
  filter_upwards [ae_all_iff.2 hall, ae_all_iff.2 hcover, h42, hβ] with ω hω hcov h42ω hβω hωA _
  obtain ⟨t, ht, -, -⟩ := exists_rat_visitEvent (hcfg ω (hAG hωA)) (hJ ω hωA) h42ω hβω.1 hβω.2
  obtain ⟨s, hs⟩ := hcov t (hAG hωA) ht
  obtain ⟨q, hq⟩ := exists_rat_nestRelEvent (hcfg ω (hAG hωA)) (hJ ω hωA) hβω.1 hβω.2 ht hs
  refine ⟨StripSys.rt q, ?_, hq.2.1, hω (q, s) hωA hq⟩
  rw [StripSys.rt, Real.toNNReal_pos]
  exact_mod_cast hq.1

/-- **R.6's selection in anchor form from the relative-time candidate transfer** (pocket opening at the flow
seed). -/
theorem twoSeedSharedAnchorInputInf_of_nestRel {W : Ω → ℝ → ℝ}
    (hnest : TwoSeedNestRelInputInf k rL rR 𝓦 P R L r η G h₀ u βR βL R' L')
    (hcfg : ∀ ω ∈ G, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (h42 : ∀ᵐ ω ∂P, Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η ω s) ⊤)
    (hβ : ∀ᵐ ω ∂P, Sec5.Prop55Half.IsSeedProper (βR ω) ∧ Sec5.Prop55Half.IsSeedProper (βL ω))
    (hcover : ∀ t : ℚ, ∀ᵐ ω ∂P, ω ∈ G → ω ∈ visitEventInf R L r η βR βL t →
      ∃ s : ℚ, ω ∈ nestEvent R L r η R' L' s t) :
    TwoSeedSharedAnchorInputInf k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ _ _ hphase hcont
  have hall : ∀ p : ℚ × ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ nestRelEventInf R L r η ψ βR βL R' L' p.2 p.1 →
      δ (StripSys.rt p.1) ω = 0 := fun p => hnest A hA hAG hPA ψ hJ hPt n hn a δ hphase hcont p.1 p.2
  filter_upwards [ae_all_iff.2 hall, ae_all_iff.2 hcover, h42, hβ] with ω hω hcov h42ω hβω hωA _
  obtain ⟨t, ht, -, -⟩ := exists_rat_visitEventInf (hcfg ω (hAG hωA)) (hJ ω hωA) h42ω hβω.1 hβω.2
  obtain ⟨s, hs⟩ := hcov t (hAG hωA) ht
  obtain ⟨q, hq⟩ := exists_rat_nestRelEventInf (hcfg ω (hAG hωA)) (hJ ω hωA) hβω.1 hβω.2 ht hs
  refine ⟨StripSys.rt q, ?_, hq.2.1, hω (q, s) hωA hq⟩
  rw [StripSys.rt, Real.toNNReal_pos]
  exact_mod_cast hq.1

end Anchor

end InteractingSLE.Sec7.R6Nest
