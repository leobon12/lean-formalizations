/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerLaw

/-!
# The corrected forward inputs: member identities on forward marks

Packet PROVE-T15-FCKER2. `FCKerLaw` shows that the member field of `FCK2CapForwardInputs` cannot hold on a
non-null meeting branch: its limit `projFactor · e^{i X(Ξ)}` is not a limit of conditional expectations. What K2's
input (L) (`HasSafeMembers`) needs is only the member identity on the capacity events. The corrected interface
`HasFCK2CapForwardMembers` asks for exactly that at the forward marks: on every event of `𝓜 t` inside the
protected set `Av t`, `∫ X = c ∫ Y`, with the same censored versions of the capacity events and eventual protection
along the strict upper dyadic times as `HasFCK2CapForwardKernel`. This is the form the physical later lines supply
(the member identities of `DomainMarkov.Aux79.hasSafeMembers_of_lineMembers`).

* `HasFCK2CapForwardMembers`, `setIntegral_eq_of_fcCapForwardMembers`;
* `FCK2CapForwardInputsC` (Gaussian field unchanged, member field corrected), `bdrySafeInputs_of_fcCapForwardInputsC`;
* `FirstContactK2ForwardKernelsCStatement` (the corrected source statement),
  `firstContactK2CapacitySafeLawsStatement_of_forwardKernelsC`;
* `firstContactCanonCondDetStatement_of_capacitySafeLaws_thm12_thm13_lemma76` and
  `firstContactCanonCondDetStatement_of_forwardKernelsC_thm12_thm13_lemma76`: the determination wiring of
  `FCK2Term` with the corrected input (physical terminal access is proved there).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb

open LQGMetric LQGMetric.MarkovZB WangWu.ChartConst DomainMarkov DomainMarkov.K2 Coupling LocalSets
open RetAux79 Sec7.PocketTraversal

universe u

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Forward member data for a capacity pairing.** At every physical line `t` the member identity `∫_E X = c ∫_E Y`
holds on every event `E` of the forward marks `𝓜 t` inside the protected set `Av t`; every censored capacity event
has a.s. versions in the forward marks; protected along the strict upper dyadic times of `τ` on `S`. -/
def HasFCK2CapForwardMembers (P : Measure Ω) (m : MeasurableSpace Ω) (S : Set Ω) (X Y : Ω → ℂ) (c : ℂ) : Prop :=
  let _ : MeasurableSpace Ω := mΩ
  ∃ (𝓜 : ℝ≥0 → MeasurableSpace Ω) (Av : ℝ≥0 → Set Ω) (τ : Ω → ℝ≥0),
    (∀ t, 𝓜 t ≤ mΩ) ∧ Measurable τ ∧
    (∀ t E, MeasurableSet[𝓜 t] E → (∀ᵐ ω ∂P, ω ∈ E → ω ∈ Av t) →
      ∫ ω in E, X ω ∂P = c * ∫ ω in E, Y ω ∂P) ∧
    (∀ D, MeasurableSet[m] D → (∀ᵐ ω ∂P, ω ∈ D → ω ∈ S) →
      ∀ n k, ∃ B, MeasurableSet[𝓜 (dyq n k)] B ∧
        B =ᵐ[P] (D ∩ {ω | dyIdx n (τ ω) = k} ∩ Av (dyq n k))) ∧
    (∀ᵐ ω ∂P, ω ∈ S → ∀ᶠ n in atTop, ω ∈ Av (dyF n (τ ω)))

/-- **The member identity on every censored capacity event** from forward member data. -/
theorem setIntegral_eq_of_fcCapForwardMembers [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {S : Set Ω} {X Y : Ω → ℂ} {c : ℂ}
    (hX : Integrable X P) (hXb : ∀ᵐ ω ∂P, ‖X ω‖ ≤ 1) (hY : Integrable Y P) (hYb : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ 1)
    (h : HasFCK2CapForwardMembers (mΩ := mΩ) P m S X Y c) {D : Set Ω}
    (hD : MeasurableSet[m] D) (hs : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ S) :
    ∫ ω in D, X ω ∂P = c * ∫ ω in D, Y ω ∂P := by
  classical
  let _ : MeasurableSpace Ω := mΩ
  obtain ⟨𝓜, Av, τ, h𝓜, hτ, hline, hread, hev⟩ := h
  have hDm : MeasurableSet D := hm _ hD
  have hmeas := hread D hD hs
  set Dk : ℕ → ℕ → Set Ω := fun n k => D ∩ {ω | dyIdx n (τ ω) = k} ∩ Av (dyq n k) with hDk_def
  have hDk : ∀ n k, NullMeasurableSet (Dk n k) P := fun n k => by
    obtain ⟨B, hBm, hBeq⟩ := hmeas n k
    exact (h𝓜 _ _ hBm).nullMeasurableSet.congr hBeq
  set Dn : ℕ → Set Ω := fun n => ⋃ k, Dk n k with hDn_def
  have hDn : ∀ n, NullMeasurableSet (Dn n) P := fun n => NullMeasurableSet.iUnion (hDk n)
  have hmemDn : ∀ n ω, ω ∈ Dn n ↔ ω ∈ D ∧ ω ∈ Av (dyF n (τ ω)) := fun n ω => by
    simp only [hDn_def, hDk_def, mem_iUnion, mem_inter_iff, mem_ofPred_eq, dyF]
    constructor
    · rintro ⟨k, ⟨hD', rfl⟩, hA⟩
      exact ⟨hD', hA⟩
    · rintro ⟨hD', hA⟩
      exact ⟨_, ⟨hD', rfl⟩, hA⟩
  have hdisj : ∀ n, Pairwise (Function.onFun (AEDisjoint P) (Dk n)) := fun n k l hkl => by
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun ω hk hl => hkl ?_)
    exact hk.1.2.symm.trans hl.1.2
  -- the identity on the pieces and on their union
  have hpiece : ∀ n k, ∫ ω in Dk n k, X ω ∂P = c * ∫ ω in Dk n k, Y ω ∂P := by
    intro n k
    obtain ⟨B, hBm, hBeq⟩ := hmeas n k
    rw [← setIntegral_congr_set hBeq, ← setIntegral_congr_set hBeq]
    refine hline (dyq n k) B hBm ?_
    filter_upwards [hBeq] with ω hω hωB
    exact (Eq.mp hω hωB).2
  have hunion : ∀ n, ∫ ω in Dn n, X ω ∂P = c * ∫ ω in Dn n, Y ω ∂P := fun n => by
    rw [integral_iUnion_ae (hDk n) (hdisj n) hX.integrableOn,
      integral_iUnion_ae (hDk n) (hdisj n) hY.integrableOn, ← tsum_mul_left]
    exact tsum_congr fun k => hpiece n k
  -- the limits
  have hlimit : ∀ Z : Ω → ℂ, Integrable Z P → (∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) →
      Tendsto (fun n => ∫ ω in Dn n, Z ω ∂P) atTop (𝓝 (∫ ω in D, Z ω ∂P)) := by
    intro Z hZ hZb
    simp only [← integral_indicator₀ (hDn _), ← integral_indicator hDm]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => hZ.aestronglyMeasurable.indicator₀ (hDn n)) (integrable_const 1) (fun n => ?_) ?_
    · filter_upwards [hZb] with ω hω
      by_cases hn : ω ∈ Dn n
      · rw [indicator_of_mem hn]; exact hω
      · rw [indicator_of_notMem hn, norm_zero]; exact zero_le_one
    · filter_upwards [hs, hev] with ω hsω hω
      by_cases hωD : ω ∈ D
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hω (hsω hωD)] with n hn
        change D.indicator Z ω = (Dn n).indicator Z ω
        rw [indicator_of_mem hωD, indicator_of_mem ((hmemDn n ω).2 ⟨hωD, hn⟩)]
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
        change D.indicator Z ω = (Dn n).indicator Z ω
        rw [indicator_of_notMem hωD, indicator_of_notMem fun h => hωD ((hmemDn n ω).1 h).1]
  exact tendsto_nhds_unique ((hlimit X hX hXb).congr fun n => (hunion n).symm |> Eq.symm)
    ((hlimit Y hY hYb).const_mul c)

/-- **Corrected forward inputs for one canonical chart path.** The Gaussian field is `FCK2CapForwardInputs.gaussian`
verbatim; the member field asks for the member identity on the forward marks (`HasFCK2CapForwardMembers`) instead of
a kernel limit (which `FCKerLaw.measure_eq_zero_of_fcCapForwardInputs` refutes on a non-null meeting branch). -/
structure FCK2CapForwardInputsC {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (κ θ : ℝ) (d : PairData Ω) (β : Ω → BoundaryWord)
    (Hc : Ω → DistOn upperHalfPlaneOpens) (U : Ω → ℝ≥0∞)
    (W : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  gaussian : ∀ (a : ForceWordType) (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0),
    HasFCK2CapForwardKernel P (𝓕 q)
      {ω | ω ∈ fcTypeBranch κ θ (meetSet d) β a ∧ ω ∈ avoidSet W U ψ q}
      (fun ω => Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) ψ : ℂ)))
      (cfAt κ W (bheProc κ a.rhoL a.rhoR W
        (geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
        (geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))) ψ 1 (fun _ => q))
  members : ∀ (q : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ QuantumZipper.H →
    ∀ (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
    HasFCK2CapForwardMembers P (𝓕 q)
      {ω | ω ∈ meetSet d ∧ (q : ℝ≥0∞) < U ω ∧
        Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) q)}
      (fun ω => Complex.exp (Complex.I *
        (Exist.flowField 0 (θ * chiC κ) (Hc ω) (lapTest (ballsOpen Fb) f + Ξ) : ℂ)))
      (fun ω => Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) Ξ : ℂ)))
      (projFactor (ballsOpen Fb) f Ξ)

/-- The corrected member data give K2's (L). -/
theorem hasSafeMembers_of_fcCapForwardMembers [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {F : Set Ω} {U : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hker : ∀ (q : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ QuantumZipper.H →
      ∀ (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
      HasFCK2CapForwardMembers P (𝓕 q)
        {ω | ω ∈ F ∧ (q : ℝ≥0∞) < U ω ∧
          Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) q)}
        (fun ω => Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)))
        (fun ω => Complex.exp (Complex.I * (X ω Ξ : ℂ))) (projFactor (ballsOpen Fb) f Ξ)) :
    HasSafeMembers P 𝓕 F U W X := by
  intro q Fb hFb D hD hs f Ξ
  exact setIntegral_eq_of_fcCapForwardMembers (𝓕.le q)
    (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply _).comp hX))
    (ae_of_all P (fun ω => by rw [Complex.norm_exp_I_mul_ofReal]))
    (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply _).comp hX))
    (ae_of_all P (fun ω => by rw [Complex.norm_exp_I_mul_ofReal]))
    (hker q Fb hFb f Ξ) hD hs

/-- The corrected forward inputs give both capacity safe laws (K2's (S) and (L)). -/
theorem bdrySafeInputs_of_fcCapForwardInputsC [IsProbabilityMeasure P] {κ θ : ℝ} {d : PairData Ω}
    {β : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens}
    {U : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} {W : ℝ≥0 → Ω → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} (hHc : Measurable Hc)
    (h : FCK2CapForwardInputsC P κ θ d β Hc U W 𝓕) :
    FCK2BdrySafeInputs P κ θ d β Hc U γ W 𝓕 := by
  have hm := (Exist.measurable_flowField 0 (θ * chiC κ)).comp hHc
  exact ⟨fun a => hasSafeLaw_of_fcCapForwardKernels hm (h.gaussian a),
    hasSafeMembers_of_fcCapForwardMembers hm h.members⟩

/-- **The corrected forward-kernel source statement**: `FirstContactK2ForwardKernelsStatement` with the member field
in the identity form `FCK2CapForwardInputsC`. Named unproved input (the original statement is refuted by
`FCKerLaw.measure_meetSet_eq_zero_of_forwardKernels`). -/
def FirstContactK2ForwardKernelsCStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [_mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord, Measurable[retSigma d P] β →
      (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) →
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
      (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
      Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    ∀ W₁ W₂ : ℝ≥0 → Ω → ℝ,
      ∀ (hm₁ : ∀ t, Measurable (W₁ t)) (hm₂ : ∀ t, Measurable (W₂ t)),
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      (FCK2CapForwardInputsC P κ θ₁ d β (hd.chartField κ h) U₁ W₁
        (fcRetainedDriverFiltration P hd W₁ hm₁)) ∧
        (FCK2CapForwardInputsC P κ θ₂ d β (hd.chartField κ h) U₂ W₂
          (fcRetainedDriverFiltration P hd W₂ hm₂))

/-- The corrected forward inputs supply the unchanged capacity safe-law statement. -/
theorem firstContactK2CapacitySafeLawsStatement_of_forwardKernelsC
    (hForward : FirstContactK2ForwardKernelsCStatement.{u}) :
    FirstContactK2CapacitySafeLawsStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨K₁, K₂⟩ := hForward κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  exact ⟨bdrySafeInputs_of_fcCapForwardInputsC (hd.measurable_chartField κ hh.1) K₁,
    bdrySafeInputs_of_fcCapForwardInputsC (hd.measurable_chartField κ hh.1) K₂⟩

/-- First-contact determination from the capacity safe laws alone (with Theorems 1.2–1.3 and Lemma 7.6): the
physical terminal access and every collision check are the proved `FCK2Term` results. -/
theorem firstContactCanonCondDetStatement_of_capacitySafeLaws_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u})
    (hSafe : FirstContactK2CapacitySafeLawsStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_capacitySafeLaws_terminalCollision_thm12_thm13_lemma76
    h12 h13 h12₀ h13₀ h76 hSafe
    (firstContactK2TerminalCollisionStatement_of_terminalAccess
      (firstContactK2TerminalAccessStatement_of_physicalTerminalAccess
        (lemma75Statement_of_thm12_thm13 h12 h13)
        (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76)
        firstContact_retainedRangeEntranceStatement
        (firstContactK2PhysicalTerminalAccessStatement
          (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76))))

/-- First-contact determination from the corrected forward inputs (replaces
`firstContactCanonCondDetStatement_of_forwardKernels_thm12_thm13_lemma76`, whose input is refuted). -/
theorem firstContactCanonCondDetStatement_of_forwardKernelsC_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u})
    (hForward : FirstContactK2ForwardKernelsCStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_capacitySafeLaws_thm12_thm13_lemma76 h12 h13 h12₀ h13₀ h76
    (firstContactK2CapacitySafeLawsStatement_of_forwardKernelsC hForward)

end InteractingSLE.Restart.FCPlumb
