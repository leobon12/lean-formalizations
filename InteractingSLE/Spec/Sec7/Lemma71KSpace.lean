/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71KSeg

/-!
# Lemma 7.1's pocket construction on a given three-curve space

Packet PROVE-LEMMA71K. Specification §7.1 (`source/spec/p193-240.md` L576–L606, pp. 222–224). On every space satisfying
`Lemma72B.IsThreeCurveSpace` this file builds, from the outer curves and the middle curve only:

* the pocket `C` (PROVE-LEMMA71J), its chart `c` (`exists_pocketChart_of_isThreeCurveSpace`), both functions of
  `(β, α)` (clause (S1) of `Lemma72B.IsPocketChartData`), with `∂C ∩ ℍ ⊆ β ∪ α` almost surely (S2);
* the **mapped middle-curve segment** `γ'`, a segment curve (`Lemma71C.IsSegCurve`) for every `ω`, whose coordinates are
  measurable for `σ(β) ∨ σ(α) ∨ σ(γ) ∨ 𝒩` (the input of (S3)), and which almost surely is the boundary value of the
  chart along the middle curve's traversal of the pocket.

`IsPocketConstruction` collects these properties; **`exists_isPocketConstruction`** proves them on every three-curve
space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71K

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

section Space

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The pocket construction of Lemma 7.1** (its chart and mapped-segment part) on a space carrying the outer curves
`β`, `α` and the middle curve `γ`: the pocket `C ω` (open, connected, simply connected, in `ℍ`) and its chart `c ω`
(conformal onto `ℍ`, lift a continuous branch of `arg ψ′`), with closed-ball events, forward map and lift measurable for
`σ(β, α)`; almost surely `C ω` is between the outer curves with `∂C ∩ ℍ ⊆ β ∪ α`; the mapped segment `γ' ω` is a
segment curve for every `ω`, with coordinates measurable for `σ(β) ∨ σ(α) ∨ σ(γ) ∨ 𝒩`; almost surely the pocket is a
marked pocket `[a', b']` of the right wall `α`, the chart is `Ψ ∘ cayley` for a boundary map `Ψ` (continuous and
injective on `closure (cayley '' C) ∖ {α̃ b'}`, `ℍ̄`-valued, `0` at the opening point, `∞` at the closing point), and
`γ' ω u = Ψ (segPt (γ ω) … u)` is the boundary value of the chart at the middle curve's segment point; the mapped
segment is the image of the middle curve in the closed pocket (minus the closing point):
`γ' ω '' [0, ∞) = Ψ '' (cayley '' range (γ ω) ∩ (closure (cayley '' C ω) ∖ {α̃ b'}))`. -/
def IsPocketConstruction (P : Measure Ω) (β α γ : Ω → ℝ≥0 → ℂ) (C : Ω → Set ℂ) (c : Ω → Chart)
    (γ' : Ω → ℝ → ℂ) : Prop :=
  (∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H) ∧
    (∀ (z : ℂ) (r : ℝ), MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | closedBall z r ⊆ C ω}) ∧
    (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = C ω) ∧
    (∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
    (∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
    (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
    (∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (L z).im) ∧
    (∀ᵐ ω ∂P, C ω ∈ betweenComponents (range (α ω)) (range (β ω))) ∧
    (∀ᵐ ω ∂P, frontier (C ω) ∩ H ⊆ range (β ω) ∪ range (α ω)) ∧
    (∀ ω, Lemma71C.IsSegCurve (γ' ω)) ∧
    (∀ u, Measurable[MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
      MeasurableSpace.comap γ MeasurableSpace.pi ⊔ Ito.nullSets P] fun ω => γ' ω u) ∧
    ∀ᵐ ω ∂P, ∃ (a' b' : ℝ) (Ψ : ℂ → ℂ), IsMarkedPocket (α ω) (C ω) a' b' ∧
      ContinuousOn Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}) ∧
      InjOn Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}) ∧
      MapsTo Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}) Hbar ∧ Ψ (wallPt (α ω) a') = 0 ∧
      Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C ω) \ {wallPt (α ω) b'}] (wallPt (α ω) b')) atTop ∧
      (∀ x ∈ C ω, (c ω).1 x = Ψ (cayley x)) ∧
      (∀ u, 0 ≤ u → segPt (γ ω) (closure (cayley '' C ω)) u ∈ closure (cayley '' C ω) \ {wallPt (α ω) b'} ∧
        γ' ω u = Ψ (segPt (γ ω) (closure (cayley '' C ω)) u)) ∧
      γ' ω '' Ici 0 = Ψ '' (cayley '' range (γ ω) ∩ (closure (cayley '' C ω) \ {wallPt (α ω) b'}))

variable {κ θ₁ θ₂ a b : ℝ} {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
  {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}

omit mΩ in
/-- `σ(β, α) ≤ σ(β) ∨ σ(α) ∨ σ(γ)`. -/
theorem comap_pair_le (β α γ : Ω → ℝ≥0 → ℂ) :
    MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤
      MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
        MeasurableSpace.comap γ MeasurableSpace.pi := by
  have e := MeasurableSpace.comap_prodMk (mβ := MeasurableSpace.pi) (mγ := MeasurableSpace.pi) β α
  exact e.le.trans le_sup_left

/-- **The pocket construction of Lemma 7.1 on every three-curve space, with the pocket and the chart read off the
outer curves** through a canonical pocket chart on wall pairs (`IsWallPairChart`): `C ω = Cw (β ω, α ω)`,
`c ω = cw (β ω, α ω)`. Applied to two middle curves between the same outer curves it gives the same pocket and chart.
No named input. -/
theorem isPocketConstruction_of_wallPairChart {e : ℕ → ℂ} {Cw : WallPair → Set ℂ} {Np : WallPair → ℕ}
    {Nx Ny : ℕ → WallPair → ℕ} {cw : WallPair → Chart} (hW : IsWallPairChart e Cw Np Nx Ny cw)
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) :
    ∃ γ' : Ω → ℝ → ℂ, IsPocketConstruction P β α γ (fun ω => Cw (toWallPair (β ω) (α ω)))
      (fun ω => cw (toWallPair (β ω) (α ω))) γ' := by
  classical
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, -, -, hγ62, hae⟩ := hS'
  obtain ⟨hπm, hCm, hfm, hlm, hbetw, hfr, hmark⟩ := pocketChart_of_isThreeCurveSpace hW hS
  obtain ⟨he, hNpw, -, -, hCw, -, hNpC, -, -, -, hconf, hdom, hbij, -, -, hlc, hL, -, -, -⟩ := hW
  set C : Ω → Set ℂ := fun ω => Cw (toWallPair (β ω) (α ω)) with hCdef
  set c : Ω → Chart := fun ω => cw (toWallPair (β ω) (α ω)) with hcdef
  have hC : ∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H := fun ω => hCw _
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hCH : ∀ ω, C ω ⊆ H := fun ω => (hC ω).2.2.2
  have hle := comap_pair_le β α γ
  have hmem : ∀ z, MeasurableSet[MeasurableSpace.comap β MeasurableSpace.pi ⊔
      MeasurableSpace.comap α MeasurableSpace.pi ⊔ MeasurableSpace.comap γ MeasurableSpace.pi] {ω | z ∈ C ω} :=
    fun z => hle _ (@Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) C hCo hCm z)
  have hγm : ∀ t, Measurable[MeasurableSpace.comap β MeasurableSpace.pi ⊔
      MeasurableSpace.comap α MeasurableSpace.pi ⊔ MeasurableSpace.comap γ MeasurableSpace.pi] fun ω => γ ω t :=
    fun t => ((measurable_pi_apply t).comp (comap_measurable γ)).mono le_sup_right le_rfl
  have hset : ∀ z, {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := fun z => by
    ext ω
    show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
    rw [hdom]
  have hf : ∀ z, Measurable[MeasurableSpace.comap β MeasurableSpace.pi ⊔
      MeasurableSpace.comap α MeasurableSpace.pi ⊔ MeasurableSpace.comap γ MeasurableSpace.pi]
      ({ω | z ∈ C ω}.indicator fun ω => (c ω).1 z) := fun z => by
    rw [← hset z]
    exact (hfm z).mono hle le_rfl
  have hw := fun u => @measurable_segPt Ω (MeasurableSpace.comap β MeasurableSpace.pi ⊔
      MeasurableSpace.comap α MeasurableSpace.pi ⊔ MeasurableSpace.comap γ MeasurableSpace.pi) C hCo hCH hmem e he
    γ hγ62.1 hγm u
  obtain ⟨g, hgm, hg⟩ := @exists_measurable_boundaryValues Ω (MeasurableSpace.comap β MeasurableSpace.pi ⊔
      MeasurableSpace.comap α MeasurableSpace.pi ⊔ MeasurableSpace.comap γ MeasurableSpace.pi) C hCo hCH hmem e he
    (fun ω => Np (toWallPair (β ω) (α ω))) ((hNpw.comp hπm).mono hle le_rfl) (fun ω => hNpC _)
    (fun ω => (c ω).1) hf (fun u ω => segPt (γ ω) (closure (cayley '' C ω)) u) hw
  -- the pathwise good event
  set Good : Ω → Prop := fun ω => Lemma71C.IsSegCurve (g ω) ∧ ∃ (a' b' : ℝ) (Ψ : ℂ → ℂ),
      IsMarkedPocket (α ω) (C ω) a' b' ∧
      ContinuousOn Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}) ∧
      InjOn Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}) ∧
      MapsTo Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}) Hbar ∧ Ψ (wallPt (α ω) a') = 0 ∧
      Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C ω) \ {wallPt (α ω) b'}] (wallPt (α ω) b')) atTop ∧
      (∀ x ∈ C ω, (c ω).1 x = Ψ (cayley x)) ∧
      (∀ u, 0 ≤ u → segPt (γ ω) (closure (cayley '' C ω)) u ∈ closure (cayley '' C ω) \ {wallPt (α ω) b'} ∧
        g ω u = Ψ (segPt (γ ω) (closure (cayley '' C ω)) u)) ∧
      g ω '' Ici 0 = Ψ '' (cayley '' range (γ ω) ∩ (closure (cayley '' C ω) \ {wallPt (α ω) b'})) with hGooddef
  have hgood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hae, hbetw, hmark] with ω hω hCω hmω
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hord, hγα, hγβ⟩ := hω
    obtain ⟨a', b', hM, Ψ, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq⟩ := hmω
    have hΨC : ∀ z ∈ C ω, Ψ (cayley z) ∈ H := fun z hz => by
      rw [← hΨeq z hz]
      exact (hbij _).2.mapsTo hz
    obtain ⟨-, -, -, hseg, hsc, hrange⟩ := isSegCurve_of_isMarkedPocket hord
      (Lemma71I.interior_contact_eq_empty hγα) (Lemma71I.interior_contact_eq_empty hγβ) hCω hM hΨc hΨi hΨH hΨ0
      hΨinf hΨC
    have hpb : wallPt (α ω) b' ∈ frontier (cayley '' C ω) := hM.2.2.2.2.2.2.1
    have hDo : IsOpen (cayley '' C ω) := Lemma71F.isOpen_cayley_image (hCo ω) (hCH ω)
    have hDsub : cayley '' C ω ⊆ closure (cayley '' C ω) \ {wallPt (α ω) b'} := fun x hx =>
      ⟨subset_closure hx, fun hxq => by
        have hxb : x = wallPt (α ω) b' := mem_singleton_iff.1 hxq
        have hpb' := hpb
        rw [hDo.frontier_eq] at hpb'
        exact hpb'.2 (hxb ▸ hx)⟩
    have hgeq : ∀ u, 0 ≤ u → g ω u = Ψ (segPt (γ ω) (closure (cayley '' C ω)) u) := fun u hu =>
      hg ω u Ψ _ hDsub (hseg u hu).1 (hΨc _ (hseg u hu)) hΨeq
    refine ⟨isSegCurve_congr hsc fun u hu => (hgeq u hu).symm, a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq,
      fun u hu => ⟨hseg u hu, hgeq u hu⟩, ?_⟩
    rw [← hrange]
    exact Set.image_congr fun u hu => hgeq u hu
  -- the null set off which the construction is the pathwise one
  set N₀ := toMeasurable P {ω | ¬ Good ω} with hN₀def
  have hN₀m : MeasurableSet N₀ := measurableSet_toMeasurable P _
  have hN₀P : P N₀ = 0 := by
    rw [hN₀def, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hgoodN : ∀ ω, ω ∉ N₀ → Good ω := fun ω hω => by
    by_contra hng
    exact hω (subset_toMeasurable P _ hng)
  have hnotN : ∀ᵐ ω ∂P, ω ∉ N₀ := measure_eq_zero_iff_ae_notMem.1 hN₀P
  set γ' : Ω → ℝ → ℂ := fun ω => if ω ∈ N₀ then fun u : ℝ => (u : ℂ) * I else g ω with hγ'def
  have hγ'g : ∀ ω, ω ∉ N₀ → γ' ω = g ω := fun ω hω => by simp only [hγ'def, hω, ↓reduceIte]
  refine ⟨γ', hC, hCm, fun ω => hconf _, fun ω => hdom _, hfm, hlm, fun ω => hlc _, fun ω => hL _, hbetw, hfr,
    fun ω => ?_, fun u => ?_, ?_⟩
  · by_cases hω : ω ∈ N₀
    · simp only [hγ'def, hω, ↓reduceIte]
      exact isSegCurve_ofReal_mul_I
    · rw [hγ'g ω hω]
      exact (hgoodN ω hω).1
  · have hN₀n : MeasurableSet[MeasurableSpace.comap β MeasurableSpace.pi ⊔
        MeasurableSpace.comap α MeasurableSpace.pi ⊔ MeasurableSpace.comap γ MeasurableSpace.pi ⊔
        Ito.nullSets P] N₀ :=
      (le_sup_right : Ito.nullSets P ≤ _) _ (MeasurableSpace.measurableSet_generateFrom ⟨hN₀m, hN₀P⟩)
    have he' : (fun ω => γ' ω u) = N₀.piecewise (fun _ => (u : ℂ) * I) fun ω => g ω u := by
      funext ω
      by_cases hω : ω ∈ N₀
      · simp only [hγ'def, hω, ↓reduceIte, Set.piecewise_eq_of_mem]
      · simp only [hγ'def, hω, ↓reduceIte, Set.piecewise_eq_of_notMem, not_false_eq_true]
    rw [he']
    exact Measurable.piecewise hN₀n measurable_const ((hgm u).mono le_sup_left le_rfl)
  · filter_upwards [hnotN] with ω hω
    obtain ⟨-, a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, hseg, hrange⟩ := hgoodN ω hω
    refine ⟨a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, fun u hu => ⟨(hseg u hu).1, ?_⟩, ?_⟩
    · rw [hγ'g ω hω]
      exact (hseg u hu).2
    · rw [hγ'g ω hω]
      exact hrange

/-- **The pocket construction of Lemma 7.1 exists on every three-curve space** (chart and mapped segment; no named
input). -/
theorem exists_isPocketConstruction (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) :
    ∃ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ), IsPocketConstruction P β α γ C c γ' := by
  obtain ⟨e, Cw, Np, Nx, Ny, cw, hW⟩ := exists_isWallPairChart
  obtain ⟨γ', hγ'⟩ := isPocketConstruction_of_wallPairChart hW hS
  exact ⟨_, _, γ', hγ'⟩

end Space

end InteractingSLE.Sec7.Lemma71K
