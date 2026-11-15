/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseContKernel
import InteractingSLE.Spec.Sec7.PhaseContPair
import InteractingSLE.Spec.Sec7.PhaseContLattice

/-!
# Theorem 1.2's R.7: the pocket phase is constant on the positive lifetime

Packet PROVE-PHASECONT. Astra's follow-up 5 §3.2 (R73, `source/external/AstraIG1/ig1_followup5.txt` L456–L483): "The
adopted mean continuity and the continuous Loewner coordinates make the quotient in (3.2) continuous in positive time.
It is lattice-valued, hence constant on the positive lifetime."

On one pocket test (the data of `PhaseClause.pocketChartPhaseData_of_stop`), R.5 up to phase (the phase `δ_q`, a
lattice-valued function at each fixed `q`) already determines a constant phase: no continuity input is needed.

**Proof.** Fix `0 < s < t`, a far bump `ψ_N` and a safe level `1/(m+1)`. For `s ≤ q < r ≤ t` the pocket kernel at `r`
holds given a σ-algebra containing the kernel σ-algebra at `q` (the germ of `K_q` retained, `PhaseContKernel`), so the
tested means `μ_p = farMean_p(δ_p) = a_p + δ_p J_p` have Gaussian increments on the event that `ψ_N` is safe at `r`
(`PhaseContPair`), with `a`, `J > 0` continuous along the path (`farMean_farGap_props`). A lattice-valued phase with
these increments does not change (`PhaseContLattice.ae_eq_of_increment_tail`): `δ_s = δ_t` almost surely where `ψ_N` is
safe at `t`. Every live point is safe for some `(N, m)` (`PhaseClause.exists_mem_safeSet_farBump`), so `δ_s = δ_t`
almost surely on the live event at `t`, and pairwise equality gives one constant (`exists_const_of_pairwise`).

## Main results

* **`exists_const_phase_of_stop`**: on one pocket test, the phase is almost surely one constant on the positive
  lifetime.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
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

namespace InteractingSLE.Sec7.PhaseCont

open PocketStop PocketTraversal PocketAdapt Lemma71C LocalSets WholeField PocketCoupling PocketUnionPt PhaseSel
  Lemma725RefChart PocketStopField Lemma725RefSafe PhaseMart PhaseClause Coupling Restart.DomainMarkov

universe u

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The pocket phase is almost surely one constant on the positive lifetime** (follow-up 5 §3.2), on one pocket test
with the data of `PhaseClause.pocketChartPhaseData_of_stop` and R.5 up to phase (`hside`), given in addition that the
open subsets of `ℍ` inside the pocket are walls' events (`hCin`). -/
theorem exists_const_phase_of_stop [IsProbabilityMeasure P] {κ : ℝ} (hκ : 4 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    (hPA : 0 < P A) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
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
    ∃ c : Ω → ℝ, ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = c ω := by
  classical
  have hκ0 : 0 < κ := by linarith
  set ch : Ω → Chart := fun ω => shiftChart (pChart A C ψ ω) (n ω) with hchdef
  obtain ⟨hcc, hdom, hfwd, hliftm, hliftc, -⟩ := pocketChartPhaseData_of_stop hκ0 (ρL := ρL) (ρR := ρR)
    (xL := xL) (xR := xR) h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hFo hgeo hh₀ hu hub hn hU hside
  -- the retained kernels, one family for every earlier time `q₀`
  choose Mr hMr using fun q₀ : ℝ≥0 => pocketChartPhaseData_retain hκ0 (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR)
    h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin hFo hgeo hh₀ hu hub hn hU hside q₀
  set 𝓜r : ℝ≥0 → ℝ≥0 → MeasurableSpace Ω := fun q₀ p =>
    germSigma (activeCompl A γ ch p) h₀ ⊔ (locPrefixSigma 𝓦 A γ p ⊔ germSigma (activeCompl A γ ch (min q₀ p)) h₀) ⊔
      Ito.nullSets P with h𝓜rdef
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
  have h𝓗𝓜 : ∀ q₀ p, 𝓗₀ p ≤ MeasurableSpace.comap Subtype.val (𝓜r q₀ p) := fun q₀ p => by
    show prefixSigma _ (fun ω : A => γ ω) p ≤ _
    rw [← comap_locPrefixSigma]
    exact MeasurableSpace.comap_mono ((hMr q₀).1.2.1 p)
  have h𝓜' : ∀ q₀ p, MeasurableSpace.comap (Subtype.val : A → Ω) (𝓜r q₀ p) ≤
      (inferInstance : MeasurableSpace A) := fun q₀ p => MeasurableSpace.comap_mono ((hMr q₀).1.1 p)
  have hA𝓜 : ∀ q₀ p, MeasurableSet[𝓜r q₀ p] A := fun q₀ p =>
    (hMr q₀).1.2.1 p _ ((le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ p) _ hA)
  have h𝓜qr : ∀ q r : ℝ≥0, q ≤ r → 𝓜r q q ≤ 𝓜r q r := fun q r hqr => by
    simp only [h𝓜rdef, min_self, min_eq_left hqr]
    refine sup_le (sup_le (le_sup_right.trans (le_sup_right.trans le_sup_left)) ?_) le_sup_right
    exact (sup_le_sup_right (locPrefixSigma_mono 𝓦 A γ hqr) _).trans (le_sup_right.trans le_sup_left)
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
  -- the kernels and the phase mean identification on `A`
  have hcondA : ∀ (q₀ p : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      (p : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (ch ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) p) →
      condExp (MeasurableSpace.comap Subtype.val (𝓜r q₀ p)) (condSub P A)
          (fun ω : A => Complex.exp (Complex.I * (hf ω φ : ℂ))) ω =
        Complex.exp (Complex.I * (Mr q₀ p ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((ch ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) p))
            φ φ : ℝ) : ℂ)) := fun q₀ p φ => by
    have hint : Integrable (fun ω => Complex.exp (Complex.I * (hf ω φ : ℂ))) P :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hfm)
    filter_upwards [condExp_condSub_ae_eq ((hMr q₀).1.1 p) (hA𝓜 q₀ p) hPA.ne' hint,
      ae_condSub_of_ae hAm ((hMr q₀).1.2.2 p φ)] with ω h1 h2 hq hs
    rw [h1]
    exact h2 ω.2 hq hs
  have hmeanA : ∀ (q₀ p : ℝ≥0) (ψ' : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      ω ∈ avoidSet (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => capLife (γ ω)) ψ' p →
      Chart.chartTransport (hcc ω) 1 a (chiC κ) (Mr q₀ p ω) ψ' =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) p
          (phaseProc κ ρL ρR (fun t (ω : A) => segDriver (γ ω) t)
            (geomLW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xL ω)
            (geomRW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xR ω)
            (fun ω : A => δ p ω) ω p) z * ψ' z := fun q₀ p ψ' => by
    filter_upwards [ae_condSub_of_ae hAm ((hMr q₀).2 p ψ')] with ω hω hav
    exact hω ω.2 hav (hcc ω)
  -- pairwise equality of the phase on `A`
  have hWc : ∀ ω : A, ContinuousOn (fun t => segDriver (γ ω) t) {t : ℝ≥0 | (t : ℝ≥0∞) < capLife (γ ω)} :=
    fun ω => (hdrive ω).segDriver_spec.2.1
  have hpairA : ∀ s t : ℝ≥0, 0 < s → s < t → ∀ᵐ (ω : A) ∂(condSub P A),
      (t : ℝ≥0∞) < capLife (γ ω) → δ s ω = δ t ω := by
    intro s t hs hst
    have hnm : ∀ N m : ℕ, ∀ᵐ (ω : A) ∂(condSub P A),
        ω ∈ safeSet (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => capLife (γ ω)) univ (farBump N)
          (1 / ((m : ℝ) + 1)) t → δ s ω = δ t ω := by
      intro N m
      have hδm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      refine ae_eq_of_increment_tail (P := condSub P A) (phaseStep_ne_zero hκ)
        (L := fun p => safeSet (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => capLife (γ ω)) univ
          (farBump N) (1 / ((m : ℝ) + 1)) p)
        (μ := fun p (ω : A) => farMean κ ρL ρR (fun ω : A => γ ω) (fun ω : A => xL ω) (fun ω : A => xR ω) N p
          (δ p ω) ω)
        (a := fun p (ω : A) => farMean κ ρL ρR (fun ω : A => γ ω) (fun ω : A => xL ω) (fun ω : A => xR ω) N p 0 ω)
        (J := fun p (ω : A) => farGap κ ρL ρR (fun ω : A => γ ω) (fun ω : A => xL ω) (fun ω : A => xR ω) N p ω)
        (δ := fun p (ω : A) => δ p ω) hst (farConst_pos N m) ?_ ?_ ?_ ?_ ?_
      · intro q r hqr ω hω
        exact ⟨mem_univ ω, isSafeAt_self_of (hω.2.anti (hWc ω) (tsupport_subset_H _) hqr)⟩
      · intro q _ _
        exact Eventually.of_forall fun ω _ => farMean_eq_add_mul _ _ _ N q _ ω
      · intro q _ _
        filter_upwards [ae_condSub_of_ae hAm (hside q).1] with ω hω hωL
        exact hω ω.2 hωL.2.1
      · exact Eventually.of_forall fun ω hω => farMean_farGap_props hκ0 hdrive _ _ N hδm hs hω
      · intro q r hsq hqr hrt b hb
        exact measure_farMean_increment_le (P := condSub P A) hκ0 hdrive hpre₀ (c := fun ω : A => ch ω)
          (fun ω => hcc ω) hdomA hfwdA hliftA (fun ω => hliftc ω) hh' a (chiC κ) hqr
          (fun p => MeasurableSpace.comap Subtype.val (𝓜r q p))
          (MeasurableSpace.comap_mono (h𝓜qr q r hqr.le)) (h𝓜' q r) (h𝓗𝓜 q q) (h𝓗𝓜 q r)
          (fun ω : A => Mr q q ω) (fun ω : A => Mr q r ω) (hcondA q q) (hcondA q r) (hmeanA q q) (hmeanA q r) N m hb
    filter_upwards [ae_all_iff.2 fun N => ae_all_iff.2 fun m => hnm N m] with ω hω hlive
    obtain ⟨N, m, hNm⟩ := exists_mem_safeSet_farBump hdrive hlive
    exact hω N m hNm
  -- back to the ambient space, and one constant
  refine exists_const_of_pairwise (T := fun ω => capLife (γ ω))
    (fun ω hω => PocketPhaseMeans.capLife_pos (hγ ω hω)) fun s t hs hst => ?_
  exact PocketMartLife.ae_of_ae_condSub hAm (p := fun ω => (t : ℝ≥0∞) < capLife (γ ω) → δ s ω = δ t ω)
    (hpairA s t hs hst)

end InteractingSLE.Sec7.PhaseCont
