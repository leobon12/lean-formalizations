/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71QClause
import InteractingSLE.Spec.Sec7.Lemma71PWire
import InteractingSLE.Spec.Sec7.Prop74BMain
import InteractingSLE.Spec.Sec7.Lemma72CMain
import InteractingSLE.Spec.Sec7.Prop74ProofWord

/-!
# Lemma 7.1 for a given pocket construction: the pulled-back field carries the mapped segment as a flow line

Packet PROVE-LEMMA71S. Specification §7.1, Lemma 7.1 and its proof (`source/spec/p193-240.md` L576–L620, pp. 221–226):
"what we will argue holds for all such `C` simultaneously"; "The conditional law of `η_ψ` is `SLE_κ(ρ^L; ρ^R)` with
seed weights (CPF2) … It is a continuous simple path in `ℍ̄` and tends to `∞` at the end of its capacity lifetime. The
joint pair with `h_ψ` has the original coupling specification … its full joint law is independent of the two outer
curves"; Figure 7.1 (right).

PROVE-LEMMA71Q derived the fixed-time chart clause of Lemma 7.1 (`Lemma72E.PocketClauseStatement`) for the pocket
construction of PROVE-LEMMA71K. Its argument works for **every** pocket construction (`Lemma71K.IsPocketConstruction`)
with the inherited branch; this file records that (`isChartCouplingCharFunConst_of_middleLanding`) and turns the
clause into the flow-line statement of Proposition 7.4's input:

* `isChartCouplingCharFunConst_of_middleLanding`: the fixed-time chart clause on a given pocket construction, for
  every `σ(β, α)`-measurable branch shift that is almost surely the inherited branch;
* `exists_isFlowLine_of_clause`: from that clause, the mapped segment (capacity parametrization) is the zero-angle flow
  line of the pulled-back field `h_ψ` (`Lemma71J.exists_global_pocketChart`,
  `Lemma71J.exists_isOptionalHullCoupling_pocket`, `isFlowLine_prop74Data_iff`,
  `Lemma71.exists_isGeneratingTrace_of_fwdHull_eq`), complete and proper with range the mapped segment, and `h_ψ` is
  independent of `(β, α)` (Lemma 7.2's (iii): `Lemma72C.indepFun_of_forall_cond_isTwoSeedCouplingOf` with the
  conditional coupling `Lemma72E.exists_cond_of_isPocketConstruction`);
* **`lemma71FixedChartStatement_of_middleLanding`**: `Prop74B.Lemma71FixedChartStatement` from the §4.2 reference and
  `Lemma71Q.MiddleLandingStatement`; **`lemma71FixedChartStatement_of_midRealOff`**: the same from PROVE-LEMMA71P's
  deterministic `Lemma71P.MidRealOffStatement`.

Conditional helpers (R43/R48: no Theorem 1.2/1.3, no `*_of_param`); they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71S

open QuantumZipper (H Hbar chiC fwdHull)
open MartChar Coupling Lemma71C Lemma71D Lemma71E Lemma71K Sec6 LocalSets Lemma71G Lemma71L Lemma71M Lemma71N
open LawUnique

/-! ### The fixed-time clause on a given pocket construction -/

section Clause

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- **Lemma 7.1's fixed-time chart clause on a given pocket construction** (the argument of
`Lemma71Q.pocketClauseStatement_of_middleLanding`, which works for every pocket construction and every
`σ(β, α)`-measurable branch shift that is almost surely the inherited branch): the capacity data
`Lemma71L.exists_capData`, the side limits along the middle curve `Lemma71Q.pocketCurveSideStatement_of_middleLanding`,
those of the active component `Lemma71Q.sideLimit_of_curveSide`, the prime-end premise `Lemma71Q.primeEnd_of_sideLimit`
and `Lemma71M.isChartCouplingCharFunConst_of_primeEnd_ind` (`a' = 0`, `k = χ`). -/
theorem isChartCouplingCharFunConst_of_middleLanding (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hL : Lemma71Q.MiddleLandingStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) (hpc : IsPocketConstruction P β α γ C c γ')
    {n : Ω → ℤ} (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n)
    (hN : ∀ᵐ ω ∂P, IsPocketBranch (β ω) (α ω) (c ω) (n ω)) :
    IsChartCouplingCharFunConst κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) 0 (chiC κ) h := by
  obtain ⟨G, M, Y, hG, hM, hY, hMiff, hGeq, hYeq⟩ := exists_capData hS hpc
  have hcurve := Lemma71Q.pocketCurveSideStatement_of_middleLanding href hL κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀
    β α γ ζβ ζα ζγ hS C c γ' hpc G M Y hG hM hY hMiff hGeq hYeq n hn hN
  exact isChartCouplingCharFunConst_of_primeEnd_ind hS hpc hG hM hY hMiff hGeq hYeq
    (c' := fun ω => shiftLift (c ω) (n ω)) (fun _ => rfl) (fun _ => rfl)
    (measurable_chartAvoid_pocket hS hpc hn _ _ 0)
    (Lemma71Q.primeEnd_of_sideLimit hS hpc hG hM hY
      (Lemma71Q.sideLimit_of_curveSide href hκ hκ4 hθ₁ hθ₂ ha hb hS hpc hMiff hGeq hYeq hN hcurve))

end Clause

/-! ### From the clause to the flow line -/

section Flow

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The trivial translate: `IsTranslateAddConst 0 (0 · s) X X`. -/
theorem isTranslateAddConst_zero_zero (X : DistOn upperHalfPlaneOpens) (s : ℝ) :
    IsTranslateAddConst 0 (0 * s) X X := by
  intro φ φ' hφ
  have e : φ' = φ := by
    ext z
    rw [hφ z, Complex.ofReal_zero, add_zero]
  rw [e, zero_mul, zero_mul, add_zero]

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The seed weights of the zero-angle flow line of the Figure 7.1 (right) data are the (CPF2) weights. -/
theorem cpf2_weights_eq (hκ : 0 < κ) :
    (fun _ : Fin 1 => (θ₂ * chiC κ - sleLambda κ - 0 * chiC κ) / sleLambda κ - 1) =
        (fun _ : Fin 1 => cpf2RhoL κ θ₂) ∧
      (fun _ : Fin 1 => (-sleLambda κ - θ₁ * chiC κ + 0 * chiC κ) / sleLambda κ - 1) =
        (fun _ : Fin 1 => cpf2RhoR κ θ₁) := by
  have hl := (Sec4.sleLambda_pos hκ).ne'
  refine ⟨funext fun _ => ?_, funext fun _ => ?_⟩
  · simp only [cpf2RhoL]
    field_simp
    ring
  · simp only [cpf2RhoR]
    field_simp
    ring

/-- **Lemma 7.1 on a given pocket construction, from the fixed-time chart clause.** On a three-curve space with a
pocket construction `(C, c, γ')` and a `σ(β, α)`-measurable branch shift `n` for which the fixed-time chart clause holds
(`a' = 0`, `k = χ`), the capacity parametrization `η` of the mapped segment is the zero-angle flow line of the
pulled-back field `h_ψ = chartField (shiftLift c n) 0 χ h` for the data of Figure 7.1 (right), with lifetime `∞`; it is
a proper curve with range the mapped segment; and `h_ψ` is independent of the outer curves. -/
theorem exists_isFlowLine_of_clause (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) (hpc : IsPocketConstruction P β α γ C c γ')
    {n : Ω → ℤ} (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n)
    (hcf : IsChartCouplingCharFunConst κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) 0 (chiC κ) h) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsFlowLine κ (prop74Data (θ₂ * chiC κ - sleLambda κ) (-sleLambda κ - θ₁ * chiC κ)) {0} 0 0 P
        (fun ω => chartField (shiftLift (c ω) (n ω)) 0 (chiC κ) (h ω)) η ζ ∧
      IndepFun (fun ω => chartField (shiftLift (c ω) (n ω)) 0 (chiC κ) (h ω)) (fun ω => (β ω, α ω)) P ∧
      ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Supp9B.IsProperCurve (η ω) ∧ range (η ω) = γ' ω '' Ici 0 := by
  classical
  -- the pocket data (`Lemma71K.isPocketChartData_of_isPocketConstruction`)
  have hpd := isPocketChartData_of_isPocketConstruction hS hpc hn hcf
  obtain ⟨h𝓖rc, hnull, hγ', hW0, hc, hWa, hK, hh, hcc, hdom, hfwd, hliftm, hliftc, hcfG, hCm', -, -, -, -⟩ := hpd
  set hψ : Ω → DistOn upperHalfPlaneOpens := fun ω => chartField (shiftLift (c ω) (n ω)) 0 (chiC κ) (h ω)
    with hψdef
  have ht : ∀ ω, IsChartTransport (shiftLift (c ω) (n ω)) 1 0 (chiC κ) (h ω) (hψ ω) := fun ω =>
    isChartTransport_chartField (hcc ω) (hliftc ω) 0 (chiC κ) (h ω)
  have hψe : hψ = fun ω => Chart.chartTransport (hcc ω) 1 0 (chiC κ) (h ω) := funext fun ω => by
    show chartField _ _ _ _ = _
    simp only [chartField, hcc ω, ↓reduceDIte]
  -- (L): the mapped hulls are local sets of `h_ψ` at the stopping times of the pocket filtration (`G = Ω`)
  have hloc : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P) τ →
      (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < capLife (γ' ω)) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => segDriver (γ' ω) s.toNNReal) ((τ ω).untopD 0 : ℝ≥0)) hψ P := by
    intro τ hτ hτT
    have hPuniv : P univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
    obtain ⟨𝓖U, -, hle, -, -, hlocU⟩ := Lemma72E.exists_cond_of_isPocketConstruction hS hpc hn hcf univ
      MeasurableSet.univ hPuniv
    have hτU : IsStoppingTime 𝓖U τ := fun i => hle i _ (hτ i)
    have h1 := hlocU τ hτU (by rwa [cond_univ])
    rwa [cond_univ] at h1
  -- the global driver and the optional hull coupling (`Lemma71J`)
  obtain ⟨W', G, -, hGae, hGW, hW'0, hW'c, hW'a, hK', hcf'⟩ :=
    Lemma71J.exists_global_pocketChart hκ hκ4 hθ₁ hθ₂ hnull hγ' hW0 hc hWa hK hh hcc hdom hfwd hliftm hliftc hcfG
  have hloc' : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P) τ → (∀ᵐ ω ∂P, τ ω ≠ ⊤) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => W' s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
        (fun ω => Chart.chartTransport (hcc ω) 1 0 (chiC κ) (h ω)) P := by
    intro τ hτ hfin
    have hlt : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < capLife (γ' ω) := by
      filter_upwards [hfin, hGae] with ω h1 hω
      rw [(hGW ω hω).1]
      exact lt_top_iff_ne_top.2 h1
    rw [← hψe]
    refine Sec7.IsLocalSet.congr_ae (hloc τ hτ hlt) ?_
    filter_upwards [hGae] with ω hω
    have hp : (fun s : ℝ => W' s.toNNReal ω) = fun s : ℝ => segDriver (γ' ω) s.toNNReal :=
      funext fun s => (hGW ω hω).2 _
    rw [hp]
  obtain ⟨B, ζ, hC, hζ, -⟩ := Lemma71J.exists_isOptionalHullCoupling_pocket hκ hκ4 hθ₁ hθ₂ hnull hγ' hW'0 hW'c
    hW'a hK' hh hcc hdom hfwd hliftm hliftc hcf' hloc'
  have hζe : ζ = fun _ => ⊤ := funext hζ
  -- the capacity parametrization of the mapped segment
  set Good : Ω → (ℝ≥0 ≃o ℝ≥0) → Prop := fun ω e =>
    IsGeneratingTrace (fun s : ℝ≥0 => W' s ω) ⊤ (fun s => γ' ω (e.symm s)) ∧
      Tendsto (fun s : ℝ≥0 => ‖γ' ω (e.symm s)‖) atTop atTop with hGooddef
  set η : Ω → ℝ≥0 → ℂ := fun ω =>
    if hω : ∃ e, Good ω e then fun s => γ' ω (hω.choose.symm s) else fun _ => 0 with hηdef
  have hgood : ∀ᵐ ω ∂P, ∃ e, Good ω e := by
    filter_upwards [hγ', hK'] with ω hγω hKω
    obtain ⟨hγc, hγi, hγH, hγ0, hγinf, hγR⟩ := hγω
    have hW0' : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by
      show W' (0 : ℝ).toNNReal ω = 0
      rw [Real.toNNReal_zero, hW'0]
    obtain ⟨e, -, htr, hinf⟩ := Lemma71.exists_isGeneratingTrace_of_fwdHull_eq
      (W := fun s : ℝ => W' s.toNNReal ω) ((hW'c ω).comp continuous_real_toNNReal) hW0' hγc hγi hγH hγ0 hγinf hγR
      hKω
    refine ⟨e, ?_, hinf⟩
    simpa only [Real.toNNReal_coe] using htr
  have hηspec : ∀ ω, (∃ e, Good ω e) → ∃ e, Good ω e ∧ η ω = fun s => γ' ω (e.symm s) := fun ω hω =>
    ⟨hω.choose, hω.choose_spec, by simp only [hηdef, hω, ↓reduceDIte]⟩
  -- the flow line (`isFlowLine_prop74Data_iff`, `θ = 0`)
  have hflow : IsFlowLine κ (prop74Data (θ₂ * chiC κ - sleLambda κ) (-sleLambda κ - θ₁ * chiC κ)) {0} 0 0 P hψ η
      (fun _ => ⊤) := by
    obtain ⟨eL, eR⟩ := cpf2_weights_eq (θ₁ := θ₁) (θ₂ := θ₂) hκ
    have hC' : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR
        (fun _ : Fin 1 => (θ₂ * chiC κ - sleLambda κ - 0 * chiC κ) / sleLambda κ - 1)
        (fun _ : Fin 1 => (-sleLambda κ - θ₁ * chiC κ + 0 * chiC κ) / sleLambda κ - 1) P
        (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
          (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P) W'
        (MartChar.geomL W' LP.twoSeedXL) (MartChar.geomR W' LP.twoSeedXR) B (fun _ => ⊤) hψ := by
      rw [eL, eR, hψe, ← hζe]
      exact hC
    refine isFlowLine_prop74Data_iff.2 ⟨hψ, _, W', MartChar.geomL W' LP.twoSeedXL, MartChar.geomR W' LP.twoSeedXR,
      B, fun ω => isTranslateAddConst_zero_zero (hψ ω) (chiC κ), hC', ?_⟩
    filter_upwards [hgood] with ω hω
    obtain ⟨e, he, hηe⟩ := hηspec ω hω
    rw [hηe]
    simpa only [Complex.ofReal_zero, sub_zero] using he.1
  -- (iii): `h_ψ` is independent of the outer curves (`Lemma72C`)
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, -, -⟩ := hS'
  set Q := Lemma72B.pocketRecord β α (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ)) h with hQdef
  have hQm : Measurable Q := by
    have hβα : Measurable fun ω => (β ω, α ω) :=
      (measurable_pi_iff.2 hβ62.2.2.2.1).prodMk (measurable_pi_iff.2 hα62.2.2.2.1)
    have hmem0 := @Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ))
      (fun ω => (shiftLift (c ω) (n ω)).dom.isOpen) hCm'
    refine Lemma72B.measurable_pocketRecord hβ62.2.2.2.1 hα62.2.2.2.1 hh fun φ => hβα.comap_le _ ?_
    exact @Lemma72B.measurableSet_disjoint_closure_of_mem Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ))
      (fun ω => (shiftLift (c ω) (n ω)).dom.isOpen) hmem0 _ φ.hasCompactSupport
  have hHm : Measurable (killedHistory (fun s ω => segDriver (γ' ω) s)
      (MartChar.geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (MartChar.geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) fun ω => capLife (γ' ω)) := by
    have hX := Coupling.isMeasurableKilledDriving_of_adaptedBefore hWa
      (fun i => Lemma71C.adaptedBefore_geomL hc hWa LP.twoSeedXL i)
      (fun i => Lemma71C.adaptedBefore_geomR hc hWa LP.twoSeedXR i)
    exact measurable_killedHistory hX
  have hcoup : ∀ G : Set Ω, MeasurableSet[MeasurableSpace.comap Q inferInstance] G → P G ≠ 0 →
      Lemma72C.IsTwoSeedCouplingOf κ (cpf2RhoL κ θ₂) (cpf2RhoR κ θ₁) (P[|G]) hψ
        (killedHistory (fun s ω => segDriver (γ' ω) s)
          (MartChar.geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
          (MartChar.geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) fun ω => capLife (γ' ω)) := by
    intro G hG hPG
    have : IsProbabilityMeasure (P[|G]) := cond_isProbabilityMeasure hPG
    obtain ⟨𝓖G, h𝓖G, hle, hnullG, hcfG', hlocG⟩ :=
      Lemma72E.exists_cond_of_isPocketConstruction hS hpc hn hcf G hG hPG
    have hac : P[|G] ≪ P := cond_absolutelyContinuous
    exact Lemma72C.isTwoSeedCouplingOf_of_pocketChart hκ hκ4 hθ₁ hθ₂ hnullG (hac.ae_le hγ') hW0 hc
      (Ito.adaptedBefore_mono hle hWa) (hac.ae_le hK) hh hcc (fun z => hle 0 _ (hdom z))
      (fun z => (hfwd z).mono (hle 0) le_rfl) (fun z => (hliftm z).mono (hle 0) le_rfl) hliftc hcfG' ht hlocG
  have hPc := hcoup univ MeasurableSet.univ (by rw [measure_univ]; exact one_ne_zero)
  rw [cond_univ] at hPc
  have hind := Lemma72C.indepFun_of_forall_cond_isTwoSeedCouplingOf hQm hκ (by linarith)
    (neg_two_lt_cpf2RhoL hκ hκ4 hθ₂) (neg_two_lt_cpf2RhoR hκ hκ4 hθ₁) hHm hPc hcoup
  have hind' : IndepFun hψ (fun ω => (β ω, α ω)) P := hind.comp measurable_snd measurable_fst
  -- the curve
  refine ⟨η, fun _ => ⊤, hflow, hind', ?_⟩
  filter_upwards [hgood, hγ'] with ω hω hγω
  obtain ⟨hγc, hγi, hγH, -, -, -⟩ := hγω
  obtain ⟨e, he, hηe⟩ := hηspec ω hω
  refine ⟨rfl, ?_, ?_⟩
  · rw [hηe]
    refine ⟨?_, ?_, fun t => hγH (e.symm t).2, he.2⟩
    · exact hγc.comp_continuous (NNReal.continuous_coe.comp e.symm.continuous) fun s => (e.symm s).2
    · intro s₁ s₂ h12
      exact e.symm.injective (NNReal.coe_injective (hγi (e.symm s₁).2 (e.symm s₂).2 h12))
  · rw [hηe]
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨e.symm s, (e.symm s).2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨e u.toNNReal, ?_⟩
      show γ' ω (e.symm (e u.toNNReal) : ℝ) = γ' ω u
      rw [e.symm_apply_apply, Real.coe_toNNReal _ hu]

end Flow

/-! ### The fixed-chart Lemma 7.1 -/

/-- **`Prop74B.Lemma71FixedChartStatement` (Lemma 7.1 for one middle curve and a given pocket construction)** from the
§4.2 reference and the geometric half of the middle-curve side limits (`Lemma71Q.MiddleLandingStatement`): the
inherited branch is `Lemma71O.pocketBranchStatement`, the clause `isChartCouplingCharFunConst_of_middleLanding`, the
flow line `exists_isFlowLine_of_clause`. Conditional helper. -/
theorem lemma71FixedChartStatement_of_middleLanding (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hL : Lemma71Q.MiddleLandingStatement.{u}) : Prop74B.Lemma71FixedChartStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb Ω mΩ P hP h u₀ β α γ ζβ ζα ζγ hS C c γ' hpc
  obtain ⟨n, hn, hN⟩ := Lemma71O.pocketBranchStatement κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀ β α γ ζβ ζα ζγ hS
    C c γ' hpc
  exact ⟨n, hn, exists_isFlowLine_of_clause hκ hκ4 hθ₁ hθ₂ hS hpc hn
    (isChartCouplingCharFunConst_of_middleLanding href hL hκ hκ4 hθ₁ hθ₂ ha hb hS hpc hn hN)⟩

/-- **`Prop74B.Lemma71FixedChartStatement` from the §4.2 reference and PROVE-LEMMA71P's deterministic
`Lemma71P.MidRealOffStatement`** (`Lemma71P.middleLandingStatement_of_midRealOff`). Conditional helper. -/
theorem lemma71FixedChartStatement_of_midRealOff (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hoff : Lemma71P.MidRealOffStatement) : Prop74B.Lemma71FixedChartStatement.{u} :=
  lemma71FixedChartStatement_of_middleLanding href (Lemma71P.middleLandingStatement_of_midRealOff hoff)

end InteractingSLE.Sec7.Lemma71S
