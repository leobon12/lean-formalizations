/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseContPocket
import InteractingSLE.Spec.Sec7.PhaseClausePocket

/-!
# Aux. lemma 122 on one pocket test for a general word: R.5 up to phase forces zero phase

PROVE-SIDE-ANCHOR. Specification §7.4.1, Aux. lemma 122 (`source/spec/p385-432.md`, pp. 389–391) and Astra's
follow-up 5 §3.2 (R73, `source/external/AstraIG1/ig1_followup5.txt` L456–L483): "If `−2 < r_L, r_R < 2A − 2 = k − 6`,
Aux. 122 forces zero phase."

PROVE-PHASECLAUSE proved Aux. lemma 122's retained hypothesis (M) for **two-seed** pocket words
(`PhaseClause.twoSeedPhaseMeansAt_of_stop`), and PROVE-PHASECONT the constancy of the phase for every word
(`PhaseCont.exists_const_phase_of_stop`). The late pockets of Theorems 1.2–1.3 carry the three- and four-mark words
`(wordL1 | wordL2; wordR2)` with random marks read through the Jordan coordinate. This file proves the phase selection
for a **general word with random time-zero marks** on one pocket test:

* the constant phase `c` (PHASECONT) and its measurable lattice version `c₁` read off the retained kernels
  (`PhaseClause.exists_measurableSet_iff_phase`, `aemeasurable_of_forall_pos_iff`);
* the retained filtration `𝓗_q = (𝓦 ∨ prefix events up to q) ∨ σ(c₁)` on the test subtype and the phase clause of the
  phase-`c₁` word (`PhaseClause.isPhaseCouplingCharFun_chartTransport`);
* Aux. lemma 122's hypotheses before the lifetime (`PhaseMart.hasPhaseMeansBefore_of_phaseCharFun`) and Aux. lemma 122
  itself (`PhaseSide.ae_phase_eq_zero_of_hasPhaseMeans`): `c₁ = 0`, hence `δ_q = 0` on the live event.

The marks must be measurable for the walls' σ-algebra on the test, with the seeds at `0`, the distant left marks
negative, the distant right marks positive (the source's "initial information fixing the word and its marked
positions", p. 390), and the seed weights in `(−2, κ − 6)`.

## Main results

* **`ae_phase_eq_zero_of_stop`**.

Conditional helper; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideAnc

open PocketStop PocketTraversal PocketAdapt Lemma71C LocalSets WholeField PocketCoupling PocketUnionPt PhaseSel
  Lemma725RefChart PocketStopField Lemma725RefSafe PhaseMart PhaseClause MartChar

universe u

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Aux. lemma 122 on one pocket test, for a general word with random time-zero marks** (specification pp.
389–391; follow-up 5 §3.2). On a walls-event `A` of positive probability with the pocket stop data of
`PhaseCont.exists_const_phase_of_stop`, R.5 up to phase (`hside`, phase `δ_q`) for a word `(ρL; ρR)` with seed weights
in `(−2, κ − 6)` and walls-measurable ordered marks (seeds at `0`, distant left marks negative, distant right marks
positive) forces `δ_q = 0` almost surely on the live event at every positive time. -/
theorem ae_phase_eq_zero_of_stop [IsProbabilityMeasure P] {κ : ℝ} (hκ : 4 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hrL : -2 < ρL 0) (hrL' : ρL 0 < κ - 6) (hrR : -2 < ρR 0)
    (hrR' : ρR 0 < κ - 6) (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] fun ω : A => xL ω)
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] fun ω : A => xR ω)
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hxLd : ∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0) (hxRd : ∀ ω ∈ A, ∀ j : Fin nR, 0 < xR ω j.succ)
    (hxLi : ∀ ω ∈ A, Antitone (xL ω)) (hxRi : ∀ ω ∈ A, Monotone (xR ω))
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR
      (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) (δ q) q) :
    ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = 0 := by
  classical
  have hκ0 : 0 < κ := by linarith
  obtain ⟨c, hconst⟩ := PhaseCont.exists_const_phase_of_stop hκ h𝓦 hA hPA hγ hγm hCo hCH hψ hCm hψm hCin hFo hgeo
    hh₀ hu hub hn hU hside
  set ch : Ω → Chart := fun ω => shiftChart (pChart A C ψ ω) (n ω) with hchdef
  obtain ⟨hcc, hdom, hfwd, hliftm, hliftc, -, -, -, 𝓜, M, ⟨h𝓜, h𝓜pre, hK⟩, hmean⟩ :=
    pocketChartPhaseData_of_stop hκ0 (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) h𝓦 hA hγ hγm hCo hCH hψ hCm hψm
      hFo hgeo hh₀ hu hub hn hU hside
  set hf : Ω → DistOn upperHalfPlaneOpens := fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u with hfdef
  have hfm : Measurable hf := measurable_add_const hh₀.measurable _ (fun _ => rfl)
  have hAm : MeasurableSet A := h𝓦 _ hA
  have hP' : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm hPA.ne'
  -- the relative history filtration on `A`
  have h𝓔 : MeasurableSpace.comap Subtype.val 𝓦 ≤ (inferInstance : MeasurableSpace A) :=
    MeasurableSpace.comap_mono h𝓦
  have hdrive : ∀ ω : A, IsDrivenCurve (γ ω) := fun ω => hγ ω ω.2
  have hm : ∀ r n k, MeasurableSet (prefixEvent (fun ω : A => γ ω) r n k) := fun r n k =>
    PocketMeas.measurableSet_prefixEvent hdrive hγm r n k
  set 𝓗₀ := prefixFilt (MeasurableSpace.comap Subtype.val 𝓦) h𝓔 (fun ω : A => γ ω) hm with h𝓗₀def
  have hpre₀ : IsPrefixAdapted 𝓗₀ (fun ω : A => γ ω) := isPrefixAdapted_prefixFilt h𝓔 hm
  have h0 : MeasurableSpace.comap Subtype.val 𝓦 ≤ 𝓗₀ 0 := le_prefixFilt_zero h𝓔 hm
  have hxL₀ : Measurable[𝓗₀ 0] fun ω : A => xL ω := hxLm.mono h0 le_rfl
  have hxR₀ : Measurable[𝓗₀ 0] fun ω : A => xR ω := hxRm.mono h0 le_rfl
  have h𝓗𝓜 : ∀ q, 𝓗₀ q ≤ MeasurableSpace.comap Subtype.val (𝓜 q) := fun q => by
    show prefixSigma _ (fun ω : A => γ ω) q ≤ _
    rw [← comap_locPrefixSigma]
    exact MeasurableSpace.comap_mono (h𝓜pre q)
  have h𝓜' : ∀ q, MeasurableSpace.comap (Subtype.val : A → Ω) (𝓜 q) ≤ (inferInstance : MeasurableSpace A) :=
    fun q => MeasurableSpace.comap_mono (h𝓜 q)
  have hA𝓜 : ∀ q, MeasurableSet[𝓜 q] A := fun q =>
    h𝓜pre q _ ((le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ q) _ hA)
  have h𝒢𝓜 : ∀ q, 𝓗₀ 0 ≤ MeasurableSpace.comap Subtype.val (𝓜 q) := fun q =>
    (𝓗₀.mono (zero_le (a := q))).trans (h𝓗𝓜 q)
  -- the chart on `A`
  have hind : ∀ {β : Type} [Zero β] [MeasurableSpace β] (z : ℂ) (f : Ω → ℂ → β),
      Measurable[𝓦] ({ω | z ∈ (ch ω).dom}.indicator fun ω => f ω z) →
      Measurable[𝓗₀ 0] ({ω : A | z ∈ (ch ω).dom}.indicator fun ω => f ω z) := fun z f hf' => by
    have e : ({ω : A | z ∈ (ch ω).dom}.indicator fun ω => f ω z) =
        ({ω | z ∈ (ch ω).dom}.indicator fun ω => f ω z) ∘ Subtype.val := by
      funext ω
      by_cases hz : z ∈ (ch ω).dom
      · simp only [Function.comp_apply, indicator_of_mem (show ω ∈ {ω : A | z ∈ (ch ω).dom} from hz),
          indicator_of_mem (show (ω : Ω) ∈ {ω | z ∈ (ch ω).dom} from hz)]
      · simp only [Function.comp_apply, indicator_of_notMem (show ω ∉ {ω : A | z ∈ (ch ω).dom} from hz),
          indicator_of_notMem (show (ω : Ω) ∉ {ω | z ∈ (ch ω).dom} from hz)]
    rw [e]
    exact (hf'.comp (comap_measurable (Subtype.val : A → Ω))).mono h0 le_rfl
  have hdomA : ∀ z, MeasurableSet[𝓗₀ 0] {ω : A | z ∈ (ch ω).dom} := fun z => h0 _ ⟨_, hdom z, rfl⟩
  have hfwdA := fun z => hind z (fun ω => (ch ω).1) (hfwd z)
  have hliftA := fun z => hind z (fun ω => (ch ω).2.2) (hliftm z)
  have hh' : Measurable fun ω : A => hf ω := hfm.comp measurable_subtype_coe
  -- the kernel and the phase mean identification on `A`
  have hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      (q : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (ch ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
      condExp (MeasurableSpace.comap Subtype.val (𝓜 q)) (condSub P A)
          (fun ω : A => Complex.exp (Complex.I * (hf ω φ : ℂ))) ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((ch ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q))
            φ φ : ℝ) : ℂ)) := fun q φ => by
    have hint : Integrable (fun ω => Complex.exp (Complex.I * (hf ω φ : ℂ))) P :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hfm)
    filter_upwards [condExp_condSub_ae_eq (h𝓜 q) (hA𝓜 q) hPA.ne' hint, ae_condSub_of_ae hAm (hK q φ)]
      with ω h1 h2 hq hs
    rw [h1]
    exact h2 ω.2 hq hs
  have hmean' : ∀ (q : ℝ≥0) (ψ' : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      ω ∈ Restart.DomainMarkov.avoidSet (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => capLife (γ ω)) ψ' q →
      Chart.chartTransport (hcc ω) 1 a (chiC κ) (M q ω) ψ' =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (phaseProc κ ρL ρR (fun t (ω : A) => segDriver (γ ω) t)
            (geomLW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xL ω)
            (geomRW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xR ω)
            (fun ω : A => δ q ω) ω q) z * ψ' z := fun q ψ' => by
    filter_upwards [ae_condSub_of_ae hAm (hmean q ψ')] with ω hω hav
    exact hω ω.2 hav (hcc ω)
  -- the phase read from the retained σ-algebras at positive times
  have hcA : ∀ q : ℝ≥0, 0 < q → ∀ᵐ (ω : A) ∂(condSub P A), (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = c ω :=
    fun q hq => by
      filter_upwards [ae_condSub_of_ae hAm (hconst q hq)] with ω hω hl
      exact hω ω.2 hl
  have hread : ∀ c₀ : A → ℝ, (∀ q : ℝ≥0, 0 < q → ∀ᵐ (ω : A) ∂(condSub P A), (q : ℝ≥0∞) < capLife (γ ω) →
      δ q ω = c₀ ω) → ∀ q : ℝ≥0, 0 < q → ∀ B : Set ℝ, MeasurableSet B → ∃ S : Set A,
        MeasurableSet[MeasurableSpace.comap Subtype.val (𝓜 q)] S ∧
        ∀ᵐ (ω : A) ∂(condSub P A), (q : ℝ≥0∞) < capLife (γ ω) → (c₀ ω ∈ B ↔ ω ∈ S) :=
    fun c₀ hc₀ q hq B hB => exists_measurableSet_iff_phase (P := condSub P A) (ρL := ρL) (ρR := ρR) hκ0
      (𝓗 := 𝓗₀) hdrive hpre₀ hxL₀ hxR₀ (c := fun ω : A => ch ω)
      (fun ω : A => hcc ω) hdomA hfwdA hliftA (fun ω : A => hliftc ω) hh' a (chiC κ) hq
      (fun q => MeasurableSpace.comap Subtype.val (𝓜 q)) (h𝓜' q) (h𝒢𝓜 q) (h𝓗𝓜 q) (fun ω : A => M q ω)
      (hcond q) (d := fun ω : A => δ q ω) (hmean' q) (hc₀ q hq) hB
  have hae : AEMeasurable (fun ω : A => c ω) (condSub P A) :=
    aemeasurable_of_forall_pos_iff hdrive hpre₀ (fun q => MeasurableSpace.comap Subtype.val (𝓜 q)) h𝓜'
      (hread (fun ω : A => c ω) hcA)
  -- the phase is lattice-valued
  have hlatA : ∀ᵐ (ω : A) ∂(condSub P A), ∃ m : ℤ, c ω = m * phaseStep κ := by
    have h1 : ∀ k : ℕ, ∀ᵐ (ω : A) ∂(condSub P A),
        (((1 / ((k : ℝ) + 1)).toNNReal : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, c ω = m * phaseStep κ := by
      intro k
      have hq : 0 < (1 / ((k : ℝ) + 1)).toNNReal := Real.toNNReal_pos.2 (by positivity)
      filter_upwards [ae_condSub_of_ae hAm (hside _).1, hcA _ hq] with ω h1 h2 hl
      obtain ⟨m, hm⟩ := h1 ω.2 hl
      exact ⟨m, (h2 hl).symm.trans hm⟩
    filter_upwards [ae_all_iff.2 h1] with ω hω
    obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (PocketPhaseMeans.capLife_pos (hdrive ω))
    have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr0'
    exact hω k (lt_trans (ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe (by positivity)).2 hk)) hr)
  -- a measurable lattice version `c₁` of the phase
  set c₂ : A → ℝ := hae.mk _ with hc₂def
  have hc₂m : Measurable c₂ := hae.measurable_mk
  have hc₂e : (fun ω : A => c ω) =ᵐ[condSub P A] c₂ := hae.ae_eq_mk
  set Lat : Set ℝ := range fun m : ℤ => (m : ℝ) * phaseStep κ with hLat
  have hLatm : MeasurableSet Lat := (countable_range _).measurableSet
  set c₁ : A → ℝ := fun ω => if c₂ ω ∈ Lat then c₂ ω else 0 with hc₁def
  have hc₁m : Measurable c₁ := Measurable.ite (hc₂m hLatm) hc₂m measurable_const
  have hc₁lat : ∀ ω : A, ∃ m : ℤ, c₁ ω = m * phaseStep κ := fun ω => by
    by_cases hL : c₂ ω ∈ Lat
    · obtain ⟨m, hm⟩ := hL
      refine ⟨m, ?_⟩
      simp only [hc₁def, show c₂ ω ∈ Lat from ⟨m, hm⟩, ↓reduceIte]
      exact hm.symm
    · exact ⟨0, by simp only [hc₁def, hL, ↓reduceIte, Int.cast_zero, zero_mul]⟩
  have hc₁e : ∀ᵐ (ω : A) ∂(condSub P A), c₁ ω = c ω := by
    filter_upwards [hc₂e, hlatA] with ω h1 h2
    have hL : c₂ ω ∈ Lat := by
      obtain ⟨m, hm⟩ := h2
      exact ⟨m, hm.symm.trans h1⟩
    simp only [hc₁def, hL, ↓reduceIte]
    exact h1.symm
  have hc₁A : ∀ q : ℝ≥0, 0 < q → ∀ᵐ (ω : A) ∂(condSub P A), (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = c₁ ω :=
    fun q hq => by
      filter_upwards [hcA q hq, hc₁e] with ω h1 h2 hl
      rw [h1 hl, h2]
  -- the retained filtration: the relative history and the phase
  let 𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace A) :=
    { seq := fun q => 𝓗₀ q ⊔ MeasurableSpace.comap c₁ inferInstance
      mono' := fun _ _ hst => sup_le_sup_right (𝓗₀.mono hst) _
      le' := fun q => sup_le (𝓗₀.le q) hc₁m.comap_le }
  have h𝓗₀𝓗 : ∀ q, 𝓗₀ q ≤ 𝓗 q := fun q => le_sup_left
  have hpre : IsPrefixAdapted 𝓗 (fun ω : A => γ ω) := fun r n k => h𝓗₀𝓗 r _ (hpre₀ r n k)
  have h𝓗𝓖 : ∀ q, 𝓗 q ≤ usualAugmentation 𝓗 (condSub P A) q := fun q => Ito.le_usualAugmentation 𝓗 _ q
  have hc₁0 : Measurable[usualAugmentation 𝓗 (condSub P A) 0] c₁ :=
    (comap_measurable c₁).mono ((le_sup_right : MeasurableSpace.comap c₁ inferInstance ≤
      𝓗₀ 0 ⊔ MeasurableSpace.comap c₁ inferInstance).trans (h𝓗𝓖 0)) le_rfl
  have hxL𝓖 : Measurable[usualAugmentation 𝓗 (condSub P A) 0] fun ω : A => xL ω :=
    hxL₀.mono ((h𝓗₀𝓗 0).trans (h𝓗𝓖 0)) le_rfl
  have hxR𝓖 : Measurable[usualAugmentation 𝓗 (condSub P A) 0] fun ω : A => xR ω :=
    hxR₀.mono ((h𝓗₀𝓗 0).trans (h𝓗𝓖 0)) le_rfl
  have hT : ∀ q : ℝ≥0, 0 < q → ∀ D : Set A, MeasurableSet[𝓗 q] D →
      (∀ᵐ ω ∂(condSub P A), ω ∈ D → (q : ℝ≥0∞) < capLife (γ ω)) →
      ∃ D' : Set A, MeasurableSet[MeasurableSpace.comap Subtype.val (𝓜 q)] D' ∧ D =ᵐ[condSub P A] D' :=
    fun q hq D hD hDL => exists_ae_eq_of_sup_comap (P := condSub P A) (𝓐 := 𝓗₀ q)
      (𝓑 := MeasurableSpace.comap Subtype.val (𝓜 q)) (h𝓗𝓜 q) (L := {ω : A | (q : ℝ≥0∞) < capLife (γ ω)})
      (measurableSet_lt_capLife hpre₀ (fun ω => (hdrive ω).zero) q) (hread c₁ hc₁A q hq) hD hDL
  -- the phase clause
  have hcf := isPhaseCouplingCharFun_chartTransport (P := condSub P A) (ρL := ρL) (ρR := ρR) hκ0 (𝓗 := 𝓗)
    hdrive hpre (hxLm.mono (h0.trans (h𝓗₀𝓗 0)) le_rfl) (hxRm.mono (h0.trans (h𝓗₀𝓗 0)) le_rfl)
    (c := fun ω : A => ch ω) (fun ω : A => hcc ω) (fun q => MeasurableSpace.comap Subtype.val (𝓜 q)) h𝓜' h𝒢𝓜
    hdomA hfwdA hliftA (fun ω : A => hliftc ω) hh' a (chiC κ) hT (fun q (ω : A) => M q ω) hcond
    (d := fun q (ω : A) => δ q ω) hmean' hc₁0 hc₁A
  -- integrable pairings
  have hX : Measurable fun ω : A => Chart.chartTransport (hcc ω) 1 a (chiC κ) (hf ω) :=
    Chart.measurable_chartTransport_random' (fun ω : A => hcc ω) (fun z => 𝓗₀.le 0 _ (hdomA z))
      (fun z => (hfwdA z).mono (𝓗₀.le 0) le_rfl) (fun z => (hliftA z).mono (𝓗₀.le 0) le_rfl)
      (fun ω : A => hliftc ω) hh' 1 a (chiC κ)
  have hWc : ∀ ω : A, ContinuousOn (fun s => segDriver (γ ω) s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ ω)} :=
    fun ω => (hdrive ω).segDriver_spec.2.1
  have hz0 : ∀ ω : A, geomLW (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => xL ω) 0 0 ω = 0 ∧
      geomRW (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => xR ω) 0 0 ω = 0 := fun ω =>
    geomLW_geomRW_zero_of_seed (T := fun ω : A => capLife (γ ω)) (W := fun t (ω : A) => segDriver (γ ω) t)
      (fun ω => (hdrive ω).segDriver_spec.1) hWc (xL := fun ω : A => xL ω) (xR := fun ω : A => xR ω)
      (fun ω => hseedL ω ω.2) (fun ω => hseedR ω ω.2) (PocketPhaseMeans.capLife_pos (hdrive ω))
  have hseed : ∀ ω : A, geomRW (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => xR ω) 0 0 ω -
      segDriver (γ ω) 0 ≤ geomLW (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => xL ω) 0 0 ω -
      segDriver (γ ω) 0 := fun ω => by
    rw [(hz0 ω).1, (hz0 ω).2]
  have hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω : A => Chart.chartTransport (hcc ω) 1 a (chiC κ) (hf ω) φ) (condSub P A) := fun φ =>
    integrable_apply_of_isPhaseCouplingCharFun hcf
      (ae_of_all _ fun ω => ⟨PocketPhaseMeans.capLife_pos (hdrive ω), (hdrive ω).segDriver_spec.2.1,
        (hdrive ω).segDriver_spec.1⟩) hseed φ ((LQGMetric.measurable_distOn_apply φ).comp hX)
  -- Aux. lemma 122's hypotheses for the phase `c₁`
  have hpre𝓖 : IsPrefixAdapted (usualAugmentation 𝓗 (condSub P A)) (fun ω : A => γ ω) := fun r n k =>
    h𝓗𝓖 r _ (hpre r n k)
  have hM := hasPhaseMeansBefore_of_phaseCharFun (P := condSub P A) (𝓖 := usualAugmentation 𝓗 (condSub P A))
    (W := fun t (ω : A) => segDriver (γ ω) t) (T := fun ω : A => capLife (γ ω)) (xL := fun ω : A => xL ω)
    (xR := fun ω : A => xR ω) (d := fun _ ω => c₁ ω) hκ0
    (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0) (fun ω => (hdrive ω).segDriver_spec.1)
    (fun ω => PocketPhaseMeans.capLife_pos (hdrive ω)) hWc (adaptedBefore_segDriver_of_isDrivenCurve hdrive hpre𝓖)
    (Eventually.of_forall fun ω hfin C => PocketLife.exists_lt_abs_segDriver (hdrive ω) (hunb ω ω.2) hfin C)
    hxL𝓖 hxR𝓖 hint hc₁0 (fun _ _ _ => rfl) hcf
  -- Aux. lemma 122
  have hk6 : 2 * (κ / 2 - 2) - 2 = κ - 6 := by ring
  have hzero := PhaseSide.ae_phase_eq_zero_of_hasPhaseMeans (P := condSub P A)
    (𝓕 := usualAugmentation 𝓗 (condSub P A)) (γ := fun ω : A => γ ω) (ρL := ρL) (ρR := ρR)
    (xL := fun ω : A => xL ω) (xR := fun ω : A => xR ω) (d := fun _ ω => c₁ ω) hκ hrL (by rw [hk6]; exact hrL')
    hrR (by rw [hk6]; exact hrR') hdrive (fun ω => hunb ω ω.2) hpre𝓖 hxL𝓖 hxR𝓖 (fun ω => hseedL ω ω.2)
    (fun ω => hseedR ω ω.2) (fun ω => hxLd ω ω.2) (fun ω => hxRd ω ω.2) (fun ω => hxLi ω ω.2)
    (fun ω => hxRi ω ω.2) (fun t ω _ _ => hc₁lat ω) hM
  -- back to the phase `δ` and to the ambient space
  intro q hq
  refine PocketMartLife.ae_of_ae_condSub hAm (p := fun ω => (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = 0) ?_
  filter_upwards [hzero, hc₁A q hq] with ω h1 h2 hl
  rw [h2 hl]
  exact h1 q hq hl

end InteractingSLE.Sec7.SideAnc
