/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72CIndep
import InteractingSLE.Spec.Sec7.Lemma72BMain

/-!
# Lemma 7.1's joint law on the three-curve space: (iii) from the conditional pocket coupling

Packet PROVE-LEMMA72C. Specification §7.1, proof of Lemma 7.1 (`source/spec/p193-240.md` L598–L620, pp. 224–226) and
of Lemma 7.2 (L622–L640, pp. 226–227).

`Lemma72B.PocketJointStatement` asks, on every three-curve space, for the pocket construction of Lemma 7.1
(`Lemma72B.IsPocketChartData`), the pulled-back field `h_ψ`, the locality (L) of the mapped hulls for `h_ψ`, and the
independence (iii) of `(history, h_ψ)` from the exterior record `Q = ((β, α), h|_{ℍ ∖ C̄})`.

This file **eliminates (iii)** (the source's component-pair factorization, Aux. lemma 46, with the successive
conditioning over all pockets and the full-curve kernels of every component field). By the uniqueness of the joint law
of two-seed couplings (Aux. lemmas 50–51 for `κ < 8`, `Lemma72CIndep`), (iii) follows as soon as the pair
`(W, h_ψ)` is the optional hull coupling of Lemma 7.1 **also under `P[· | G]`** for every event `G` of the exterior
record of positive probability, with a filtration containing the pocket filtration. This is the conditional form of
the pocket coupling ("The identical argument … conditionally on `A`", p. 226; on the marked union of the outer curves
and the middle prefix the field in the pocket is the coupling mean plus a zero-boundary GFF, and the exterior record
is a function of the outer curves and of the field off `C̄`, which lies in the germ σ-algebra of that marked union):

* `isTwoSeedCouplingOf_of_pocketChart`: the clauses of the chart-form pocket coupling under a probability measure
  `μ`, with the locality of the hulls, make `(h_ψ, killed history)` a two-seed coupling under `μ`
  (`Lemma71J.exists_isOptionalHullCoupling_of_pocketChart`);
* `PocketCondStatement` (**named input**): on every three-curve space, the pocket construction and `h_ψ`, such that
  for every event `G` of `σ(Q)` of positive probability the chart coupling clause and the locality of the hulls hold
  under `P[· | G]` for some right-continuous filtration `𝓖_G ⊇ 𝓖` containing the `P[· | G]`-null sets;
* **`pocketJointStatement_of_cond`**: `PocketCondStatement → Lemma72B.PocketJointStatement` ((L) is the case
  `G = Ω`; (iii) is `Lemma72C.indepFun_of_forall_cond_isTwoSeedCouplingOf`).

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H Hbar fwdHull chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma72C

open LawUnique

/-! ### The pocket coupling under one measure -/

section Pocket

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {κ θ₁ θ₂ : ℝ} {γ : Ω → ℝ → ℂ} {W : ℝ≥0 → Ω → ℝ}
  {T : Ω → ℝ≥0∞} {h hψ : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {a k : ℝ}

/-- **The chart-form pocket coupling is a two-seed coupling of `(h_ψ, killed history)`** under the measure `μ`: the
clauses of `Lemma71C.Lemma71PocketChartStatement` (with the null sets of `μ` in `𝓖₀`), the chart transport `h_ψ` and
the locality of the hulls for `h_ψ` at the stopping times of `𝓖` before `T`
(`Lemma71J.exists_isOptionalHullCoupling_of_pocketChart`;
the killed driving history of its global driver is almost surely that of `(W, T)`). -/
theorem isTwoSeedCouplingOf_of_pocketChart (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (hnull : ∀ s, MeasurableSet s → μ s = 0 → MeasurableSet[𝓖 0] s)
    (hγ : ∀ᵐ ω ∂μ, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) Hbar ∧
      γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅)
    (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W)
    (hK : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
      fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t))
    (hh : Measurable h) (hcc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcf : Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂)
      (fun _ : Fin 1 => cpf2RhoR κ θ₁) μ 𝓖 W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR)
      T c a k h)
    (ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (hψ ω))
    (hloc : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂μ, (τ ω : ℝ≥0∞) < T ω) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) hψ μ) :
    IsTwoSeedCouplingOf κ (cpf2RhoL κ θ₂) (cpf2RhoR κ θ₁) μ hψ
      (killedHistory W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T) := by
  have hψe : hψ = fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω) := funext fun ω =>
    IsChartTransport.eq_chartTransport (hcc ω)
      (Chart.locallyIntegrableOn_of_continuousOn ((hcc ω).continuousOn_lift_inv (hliftc ω))) (ht ω)
  subst hψe
  obtain ⟨W', B, ζ, hC, htr, hhist⟩ := Lemma71J.exists_isOptionalHullCoupling_of_pocketChart hκ hκ4 hθ₁ hθ₂ hnull
    hγ hW0 hc hWa hK hh hcc hdom hfwd hliftm hliftc hcf hloc
  exact ⟨𝓖, W', MartChar.geomL W' LP.twoSeedXL, MartChar.geomR W' LP.twoSeedXR, B, ζ, hC,
    htr.mono fun ω hω => by obtain ⟨η, hη, -⟩ := hω; exact ⟨η, hη⟩, hhist⟩

end Pocket

/-! ### The named input and the reduction -/

/-- **Named input: Lemma 7.1's pocket coupling, conditionally on the exterior record** (specification §7.1,
pp. 221–226). For `0 < κ < 4`, `θ₁ < 0 < θ₂` and boundary values `a, b` large enough for Proposition 5.5, on every
three-curve space there are
* the pocket construction (`Lemma72B.IsPocketChartData`) and the pulled-back field `h_ψ` (`IsChartTransport`, `σ = 1`);
* for every event `G` of the exterior record `Q = ((β, α), h|_{ℍ ∖ C̄})` (`Lemma72B.pocketRecord`) of positive
  probability, a right-continuous filtration `𝓖_G ⊇ 𝓖` containing the `P[· | G]`-null sets at time `0`, for which
  under `P[· | G]` the chart coupling clause of the two-seed word with the (CPF2) weights holds and the mapped hulls
  `K_τ` are local sets of `h_ψ` at the stopping times `τ < T` of `𝓖_G` (p. 224–225: "the history-locality statement
  of Lemma 6.2 applies to the revealed outer curves and the middle prefix […] the optional history marking of the
  original coupling supplies the required history locality"; the exterior record is a function of the outer curves
  and of the field off `C̄`, which is part of the germ of the marked union `ℍ ∖ ψ⁻¹(ℍ ∖ K_τ)`, so conditioning on
  its events keeps the conditional law of the field in `ψ⁻¹(ℍ ∖ K_τ)` and the history marking). -/
def PocketCondStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ a b : ℝ, θ₁ < 0 → 0 < θ₂ →
    sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a → sleLambda κ - θ₁ * chiC κ ≤ b →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ →
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (γ' : Ω → ℝ → ℂ) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (c : Ω → Chart) (a' k : ℝ)
      (hψ : Ω → DistOn upperHalfPlaneOpens),
      Lemma72B.IsPocketChartData κ θ₁ θ₂ P β α γ h 𝓖 γ' W T c a' k ∧
      (∀ ω, IsChartTransport (c ω) 1 a' k (h ω) (hψ ω)) ∧
      ∀ G : Set Ω, MeasurableSet[MeasurableSpace.comap
          (Lemma72B.pocketRecord β α (fun ω => ((c ω).dom : Set ℂ)) h) inferInstance] G → P G ≠ 0 →
        ∃ 𝓖G : Filtration ℝ≥0 mΩ, 𝓖G.IsRightContinuous ∧ 𝓖 ≤ 𝓖G ∧
          (∀ s, MeasurableSet s → P[|G] s = 0 → MeasurableSet[𝓖G 0] s) ∧
          Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂)
            (fun _ : Fin 1 => cpf2RhoR κ θ₁) (P[|G]) 𝓖G W (MartChar.geomL W LP.twoSeedXL)
            (MartChar.geomR W LP.twoSeedXR) T c a' k h ∧
          ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖G τ → (∀ᵐ ω ∂(P[|G]), (τ ω : ℝ≥0∞) < T ω) →
            IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) hψ (P[|G])

/-- **`Lemma72B.PocketJointStatement` from the conditional pocket coupling.** The locality (L) is the case `G = Ω`
(a stopping time of `𝓖` is one of `𝓖_Ω ⊇ 𝓖`). For (iii): under `P` and under every `P[· | G]`, `G ∈ σ(Q)` of positive
probability, `(h_ψ, killed history)` is a two-seed coupling (`isTwoSeedCouplingOf_of_pocketChart`; the almost sure
clauses of the pocket data pass to `P[· | G] ≪ P`, the `𝓖₀`-measurability and the adaptedness to `𝓖_G ⊇ 𝓖`), so its law
is the same under all of them (Aux. lemma 51, `κ < 4 < 8`, both (CPF2) weights `> −2`), and it is independent of `Q`
(`indepFun_of_forall_cond_isTwoSeedCouplingOf`). Conditional helper. -/
theorem pocketJointStatement_of_cond (hPC : PocketCondStatement.{u}) : Lemma72B.PocketJointStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb Ω mΩ P hP h u₀ β α γ ζβ ζα ζγ h3
  obtain ⟨𝓖, γ', W, T, c, a', k, hψ, hpd, ht, hcond⟩ := hPC κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀ β α γ ζβ ζα ζγ h3
  have hpd' := hpd
  obtain ⟨-, -, -, -, -, -, hβ, hα, -, -⟩ := h3
  obtain ⟨-, -, hγ', hW0, hc, hWa, hK, hh, hcc, hdom, hfwd, hliftm, hliftc, -, hCm', -, -, -, -⟩ := hpd'
  set Q := Lemma72B.pocketRecord β α (fun ω => ((c ω).dom : Set ℂ)) h with hQdef
  have hQm : Measurable Q := by
    have hβα : Measurable fun ω => (β ω, α ω) :=
      (measurable_pi_iff.2 hβ.2.2.2.1).prodMk (measurable_pi_iff.2 hα.2.2.2.1)
    have hmem0 := @Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) (fun ω => ((c ω).dom : Set ℂ))
      (fun ω => (c ω).dom.isOpen) hCm'
    refine Lemma72B.measurable_pocketRecord hβ.2.2.2.1 hα.2.2.2.1 hh fun φ => hβα.comap_le _ ?_
    exact @Lemma72B.measurableSet_disjoint_closure_of_mem Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) (fun ω => ((c ω).dom : Set ℂ))
      (fun ω => (c ω).dom.isOpen) hmem0 _ φ.hasCompactSupport
  have hHm : Measurable (killedHistory W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T) := by
    have hX := Coupling.isMeasurableKilledDriving_of_adaptedBefore hWa
      (fun i => Lemma71C.adaptedBefore_geomL hc hWa LP.twoSeedXL i)
      (fun i => Lemma71C.adaptedBefore_geomR hc hWa LP.twoSeedXR i)
    exact measurable_killedHistory hX
  -- the pocket coupling under `P[· | G]`
  have hcoup : ∀ G : Set Ω, MeasurableSet[MeasurableSpace.comap Q inferInstance] G → P G ≠ 0 →
      IsTwoSeedCouplingOf κ (cpf2RhoL κ θ₂) (cpf2RhoR κ θ₁) (P[|G]) hψ
        (killedHistory W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T) := by
    intro G hG hPG
    have : IsProbabilityMeasure (P[|G]) := cond_isProbabilityMeasure hPG
    obtain ⟨𝓖G, h𝓖G, hle, hnullG, hcfG, hlocG⟩ := hcond G hG hPG
    have hac : P[|G] ≪ P := cond_absolutelyContinuous
    exact isTwoSeedCouplingOf_of_pocketChart hκ hκ4 hθ₁ hθ₂ hnullG (hac.ae_le hγ') hW0 hc
      (Ito.adaptedBefore_mono hle hWa) (hac.ae_le hK) hh hcc (fun z => hle 0 _ (hdom z))
      (fun z => (hfwd z).mono (hle 0) le_rfl) (fun z => (hliftm z).mono (hle 0) le_rfl) hliftc hcfG ht hlocG
  have hPuniv : P univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
  have hGuniv : MeasurableSet[MeasurableSpace.comap Q inferInstance] (univ : Set Ω) := MeasurableSet.univ
  refine ⟨𝓖, γ', W, T, c, a', k, hψ, hpd, ht, ?_, ?_⟩
  · -- (L): the case `G = Ω`
    intro τ hτ hτT
    obtain ⟨𝓖U, -, hle, -, -, hlocU⟩ := hcond univ hGuniv hPuniv
    have hτU : IsStoppingTime 𝓖U τ := fun i => hle i _ (hτ i)
    have hloc := hlocU τ hτU (by rwa [cond_univ])
    rwa [cond_univ] at hloc
  · -- (iii): uniqueness of the joint law under every conditioning
    have hPc := hcoup univ hGuniv hPuniv
    rw [cond_univ] at hPc
    exact indepFun_of_forall_cond_isTwoSeedCouplingOf hQm hκ (by linarith) (neg_two_lt_cpf2RhoL hκ hκ4 hθ₂)
      (neg_two_lt_cpf2RhoR hκ hκ4 hθ₁) hHm hPc hcoup

end InteractingSLE.Sec7.Lemma72C
