/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4Chain

/-!
# Theorem GW4: the completion of each traversal (infinite relative lifetime, nonvanishing tips)

Packet PROVE-T14-GW4S. The named input `GW4Ident.GW4CompletionStatement` of PROVE-T14-GW4R (Theorem GW4's proof,
p. 639: "The relative endpoint is the designated `x_C`, hence is infinity in the reversed chart. All cumulative groups
are greater than `−2` by GW3. At a proposed finite relative lifetime, integrated nonexplosion and bounded-coordinate
localization would bound the whole relative hull, contradicting that endpoint. The relative lifetime is infinite.")
is proved here from

* the component law input `GW4RelativeLawStatement` (some centred counterflow `W_C` of the component field, with
  infinite lifetime, has the relative hulls `Φ(K'_{T_L s} ∩ R⁻¹(C))` for some clock `T_L`: the "integrated
  nonexplosion" of the source is its infinite lifetime);
* **`GW4FillStatement`** (new named input, the filled-pocket clause): if the counterflow reaches the exit `x_C` at a
  finite time `σ`, then `C` is filled by then, `R⁻¹(C) ⊆ K'_σ` (GB11's proof, p. 556: "If it follows `C`, its two
  whole boundary arcs have been visited by `τ`. Its interior is then separated from the original target and is
  already filled", applied to `C` itself at `σ`). It follows from the deterministic **`GW4FillDetStatement`** and the
  barrier input (`gw4FillStatement_of_barrier`);
* **`CounterflowNoReturnStatement`** (new named input): a centred counterflow with infinite lifetime does not return
  to its starting point at positive times (the tips of the completion statement are the ambient and relative traces);
* Theorem 1.3 (the traces).

## The argument for `S = ∞` (`eq_top_of_law_fill`, deterministic)

Let `A(t) = Φ(K'_t ∩ R⁻¹(C))` (monotone in `t`) and suppose the maximal parametrization `(S, W_rel, T)` has `S < ∞`.
For `s' ≥ S`: if `T_L(s') < σ`, then `T(s) > T_L(s')` for some `s < S` (as `T(s) → σ`), so
`K^{W_C}_{s'} = A(T_L s') ⊆ A(T s) = K^{W_rel}_s`; then `K^{W_C}_s ⊆ K^{W_rel}_s`, hence equal (equal capacity), while
`K^{W_C}_s ⊊ K^{W_C}_{s'}` — a contradiction. So `T_L(s') ≥ σ`, in particular `σ < ∞`; by the fill,
`A(T_L s') = Φ(R⁻¹(C))` for all `s' ≥ S`, so `K^{W_C}_S = K^{W_C}_{S+1}`, contradicting strict hull growth.

## Main results

* `eq_top_of_law_fill` (deterministic core);
* **`gw4CompletionStatement_of_law`** : `GW4CompletionStatement` from the law input, the fill, the no-return input and
  Theorem 1.3;
* `gw4FillStatement_of_barrier` : the fill from the barrier input and its deterministic form;
* **`gw4RelativeChainStatement_of_law`** : the relative chain with GB10 discharged (`GB10.gb10Statement`) and the
  completion replaced by its inputs; `componentKernels_of_law` : the frozen component-kernel anchor's conclusion
  (binders verbatim) from the finest inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Ident

open GW4Traverse

/-! ### The two new named inputs -/

/-- **Named input: a centred counterflow does not return to its start.** For `0 < κ < 4`, every GFF with piecewise
constant boundary data and every centred counterflow of it with infinite lifetime (on any probability space), almost
surely every continuous generating trace on `[0, ∞]` is nonzero at positive times (the physical counterflow does not
come back to its source). Used for the ambient counterflow and for the component counterflow `W_C`. -/
def CounterflowNoReturnStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q h b jumps →
    ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ Q h W ζ → (∀ᵐ ω ∂Q, ζ ω = ⊤) →
      ∀ᵐ ω ∂Q, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0

/-- **Named input: the filled pocket, deterministic form** (GB11's proof, p. 556: "If it follows `C`, its two whole
boundary arcs have been visited by `τ`. Its interior is then separated from the original target and is already
filled"; here for `C` itself at its exit time). Under GB11's barrier input, for every between-component `C` with a
component chart and exit `x_C`: if the physical counterflow visits `x_C` at a finite time `σ`, then the whole
pocket is filled by then, `R⁻¹(C) ⊆ K'_σ` (`R(z) = −1/z` the counterflow chart). -/
def GW4FillDetStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ c : Chart, IsComponentChart (range αR) (range αL) C c →
    ∀ xC : ℂ, Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) → GB11.firstVisit γ xC < ⊤ →
      relDom C ⊆ fwdHull (fun r : ℝ => W' r.toNNReal) (GB11.firstVisit γ xC).toNNReal

/-- **The filled pocket in the setting of Theorem GW4** (binders and component data of `GW4CompletionStatement`,
verbatim): `ν`-almost surely, for every generating trace of the ambient counterflow and the exit `x_C` of the chart,
a finite exit time `σ` fills the pocket, `R⁻¹(C) ⊆ K'_σ`. -/
def GW4FillStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ c : Chart, IsComponentChart R L C c →
          ∀ᵐ ω ∂ν, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ →
            ∀ xC : ℂ, Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) → GB11.firstVisit γ xC < ⊤ →
              relDom C ⊆ fwdHull (fun r : ℝ => W' r.toNNReal ω) (GB11.firstVisit γ xC).toNNReal

/-! ### The deterministic core -/

/-- The punctured left approach to a positive extended real is seen by `ℝ≥0`. -/
theorem neBot_comap_coe_nhdsLT {S : ℝ≥0∞} (hS : 0 < S) :
    (comap (fun s : ℝ≥0 => (s : ℝ≥0∞)) (𝓝[<] S)).NeBot := by
  refine comap_neBot fun t ht => ?_
  obtain ⟨a, haS, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hS).1 ht
  obtain ⟨r, har, hrS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 haS
  exact ⟨r, hsub ⟨har, hrS⟩⟩

/-- **`S = ∞` from the law input and the filled pocket** (deterministic; the argument is in the module docstring).
`W_C` is a continuous driver from `0` whose hulls are the relative hulls `A(T_L s)`; `(S, W_rel, T)` is a maximal
relative parametrization. -/
theorem eq_top_of_law_fill {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {c : Chart} {C : Set ℂ} {xC : ℂ} {S : ℝ≥0∞}
    {Wrel : ℝ≥0 → ℝ} {T : ℝ≥0 → ℝ≥0} (hP : GB11.IsGB11RelParam W' γ c C xC S Wrel T)
    {WC : ℝ≥0 → ℝ} (hWC : Continuous WC) (hWC0 : WC 0 = 0) {TL : ℝ≥0 → ℝ≥0}
    (hL : ∀ s : ℝ≥0, fwdHull (fun r : ℝ => WC r.toNNReal) s =
      relMapC c '' (fwdHull (fun r : ℝ => W' r.toNNReal) (TL s) ∩ relDom C))
    (hfill : GB11.firstVisit γ xC < ⊤ →
      relDom C ⊆ fwdHull (fun r : ℝ => W' r.toNNReal) (GB11.firstVisit γ xC).toNNReal) :
    S = ⊤ := by
  obtain ⟨hS0, hWc, -, -, -, -, hTlim, hK⟩ := hP
  set A : ℝ≥0 → Set ℂ := fun t => relMapC c '' (fwdHull (fun r : ℝ => W' r.toNNReal) t ∩ relDom C) with hA
  have hAm : Monotone A := monotone_relHull c C _
  have hWCc : Continuous (fun r : ℝ => WC r.toNNReal) := hWC.comp continuous_real_toNNReal
  have hWCc0 : (fun r : ℝ => WC r.toNNReal) 0 = 0 := by simp [hWC0]
  by_contra hStop
  set Sr : ℝ≥0 := S.toNNReal with hSrdef
  have hSr : (Sr : ℝ≥0∞) = S := ENNReal.coe_toNNReal hStop
  -- (1) beyond `S` the law clock is past the exit time
  have h1 : ∀ s' : ℝ≥0, Sr ≤ s' → GB11.firstVisit γ xC ≤ TL s' := by
    intro s' hs'
    by_contra hlt
    push Not at hlt
    have hne := neBot_comap_coe_nhdsLT hS0
    have hev : ∀ᶠ s : ℝ≥0 in comap (fun s : ℝ≥0 => (s : ℝ≥0∞)) (𝓝[<] S),
        (TL s' : ℝ≥0∞) < ((T s : ℝ≥0) : ℝ≥0∞) :=
      hTlim.eventually (lt_mem_nhds hlt)
    have hev2 : ∀ᶠ s : ℝ≥0 in comap (fun s : ℝ≥0 => (s : ℝ≥0∞)) (𝓝[<] S), (s : ℝ≥0∞) < S :=
      preimage_mem_comap self_mem_nhdsWithin
    obtain ⟨s, hsT, hsS⟩ := (hev.and hev2).exists
    have hsSr : s < Sr := by rw [← hSr] at hsS; exact_mod_cast hsS
    have hss' : (s : ℝ) < s' := by exact_mod_cast hsSr.trans_le hs'
    have hsub : fwdHull (fun r : ℝ => WC r.toNNReal) s' ⊆ fwdHull (fun r : ℝ => Wrel r.toNNReal) s := by
      rw [hL s', hK s hsS]
      exact hAm (le_of_lt (by exact_mod_cast hsT))
    -- a continuous frozen version of `W_rel` on `[0, s₂]`, `s < s₂ < S`
    obtain ⟨s₂, hss₂, hs₂S⟩ := exists_between hsSr
    have hWc₂ : ContinuousOn Wrel (Iic s₂) := hWc.mono fun r hr => by
      show (r : ℝ≥0∞) < S
      rw [← hSr]; exact_mod_cast lt_of_le_of_lt hr hs₂S
    have hVc : Continuous (frozenDrive Wrel s₂) :=
      continuous_frozenDrive (by simpa only [Real.toNNReal_coe] using hWc₂)
    have hVK : fwdHull (fun r : ℝ => Wrel r.toNNReal) s = fwdHull (frozenDrive Wrel s₂) s :=
      fwdHull_eq_of_eqOn s.coe_nonneg (by exact_mod_cast hss₂) fun r hr => (frozenDrive_eq hr).symm
    have heq : fwdHull (fun r : ℝ => WC r.toNNReal) s = fwdHull (frozenDrive Wrel s₂) s :=
      GW4Ident.fwdHull_eq_of_subset hWCc hVc s.coe_nonneg
        (((QuantumZipper.fwdHull_mono).1 hss'.le).trans (hsub.trans hVK.le))
    have hss := QuantumZipper.RS.fwdHull_ssubset hWCc hWCc0 s.coe_nonneg hss'
    exact (ssubset_irrefl _) (hss.trans_subset (hsub.trans (hVK.trans heq.symm).le))
  -- (2) the exit time is finite and the pocket is filled at every later law time
  have hσ : GB11.firstVisit γ xC < ⊤ := lt_of_le_of_lt (h1 Sr le_rfl) ENNReal.coe_lt_top
  have hAfull : ∀ s' : ℝ≥0, Sr ≤ s' → A (TL s') = relMapC c '' relDom C := by
    intro s' hs'
    have hle : (GB11.firstVisit γ xC).toNNReal ≤ TL s' := by
      simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top (h1 s' hs')
    have hsub : relDom C ⊆ fwdHull (fun r : ℝ => W' r.toNNReal) (TL s') :=
      (hfill hσ).trans ((QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 hle))
    simp only [hA, inter_eq_right.2 hsub]
  have hss := QuantumZipper.RS.fwdHull_ssubset hWCc hWCc0 Sr.coe_nonneg
    (show (Sr : ℝ) < ((Sr + 1 : ℝ≥0) : ℝ) by push_cast; linarith)
  rw [hL Sr, hL (Sr + 1)] at hss
  change A (TL Sr) ⊂ A (TL (Sr + 1)) at hss
  rw [hAfull Sr le_rfl, hAfull (Sr + 1) le_self_add] at hss
  exact (ssubset_irrefl _) hss

/-! ### The completion statement -/

/-- **Theorem GW4's completion of each traversal** (conditional helper with a distinct name;
`GW4CompletionStatement`) from the component law input, the filled pocket, the no-return input and Theorem 1.3.
`S = ∞` is `eq_top_of_law_fill`. The ambient tip at `T s`, `s > 0`, is the trace `γ(T s)` (`T s > T 0 ≥ 0`), nonzero
by no-return; with `S = ∞` the relative driver is the law input's `W_C` (both have the monotone relative hulls,
`eq_of_fwdHull_eq_comp`), so the relative tip is the trace of `W_C` at `s`, nonzero by no-return under `ν`. -/
theorem gw4CompletionStatement_of_law (h13 : Exist.Theorem13Statement.{u}) (hL : GW4RelativeLawStatement.{u})
    (hF : GW4FillStatement.{u}) (hN : CounterflowNoReturnStatement.{u}) : GW4CompletionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    ((ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ').and
      (hN κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'))
  filter_upwards [hamb, hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hambω hLω hFω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨WC, ζC, hcdC, hζC, hlawC⟩ := hLω C hCm c hC bC jumpsC hch htr hpc hbd hgff
  filter_upwards [hambω, hlawC, ae_trace_of_isCenteredCounterflowDriver h13 hκ hcdC hζC,
    hN κ hκ hκ4 bC jumpsC hpc ν hC hgff WC ζC hcdC hζC, hFω C hCm c hch] with ω hambω' hlawω htrC hnoC hfillω
  intro γ hγ xC hxC S Wrel T hpar
  obtain ⟨⟨hW'c, hW'0, -⟩, hno⟩ := hambω'
  obtain ⟨TL, hTL⟩ := hlawω
  obtain ⟨hWCc, hWC0, γC, hγC, -⟩ := htrC
  have hS : S = ⊤ := eq_top_of_law_fill hpar hWCc hWC0 hTL (hfillω γ hγ xC hxC)
  subst hS
  obtain ⟨hWrelc, hWrel0, hTm, -, hKrel⟩ := hpar.global
  have hne : (𝓝[H] (0 : ℂ)).NeBot := neBot_nhdsWithin_H_zero
  refine ⟨rfl, fun s hs => ⟨fun p hp => ?_, fun q hq => ?_⟩⟩
  · have htip := hγ.tendsto_fwdMapInv_tip hW'c.continuousOn hW'0 (t := T s) ENNReal.coe_lt_top
    rw [tendsto_nhds_unique hp htip]
    exact hno γ hγ (T s) (lt_of_le_of_lt zero_le (hTm hs))
  · have heqW : Wrel = fun t => WC t ω :=
      eq_of_fwdHull_eq_comp (monotone_relHull c C _) hWrelc hWCc hWrel0 hKrel hTL
    subst heqW
    have htipC := hγC.tendsto_fwdMapInv_tip hWCc.continuousOn hWC0 (t := s) ENNReal.coe_lt_top
    rw [tendsto_nhds_unique hq htipC]
    exact hnoC γC hγC s hs

/-- **The filled pocket in GW4's setting from the barrier input** and the deterministic `GW4FillDetStatement`
(Theorem 1.3 gives the ambient driver's continuity, moved to `ν`). -/
theorem gw4FillStatement_of_barrier (h13 : Exist.Theorem13Statement.{u}) (hB : GW4BarrierStatement.{u})
    (hD : GW4FillDetStatement) : GW4FillStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    (ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ')
  filter_upwards [hamb, hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hambω hBω
  intro R L ν C hCm c hch
  obtain ⟨αR, αL, hαR, hαL, hbar⟩ := hBω
  filter_upwards [hambω, hbar] with ω hambω' hbarω
  intro γ hγ xC hxC hσ
  obtain ⟨hW'c, hW'0, -⟩ := hambω'
  have hCm' : C ∈ betweenComponents (range αR) (range αL) := by rw [hαR, hαL]; exact hCm
  have hch' : IsComponentChart (range αR) (range αL) C c := by rw [hαR, hαL]; exact hch
  exact hD (fun t => W' t ω) γ hW'c hW'0 hγ αR αL (hbarω γ hγ) C hCm' c hch' xC hxC hσ

end GW4Ident

end Theorem14

end InteractingSLE
