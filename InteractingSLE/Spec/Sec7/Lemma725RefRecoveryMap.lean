/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefRecoveryCore
import InteractingSLE.Spec.Sec7.Lemma72
import InteractingSLE.Spec.Sec2.RestartMarkov

/-!
# The ambient recovery as a Borel map

Packet PROVE-LEMMA725REF5. Specification §7.4, Aux. lemma 125's proof (`source/spec/p385-432.md` L197–L250, p. 398):
"The pair `(ℰ, H_C)` determines the entire ambient field"; Astra's shortcut note, Proposition 2.1 step 3
(`source/external/AstraIG1/ig1_shortcuts_audited.txt` L276–L285): "`h_B` is recorded; the interior field determines
the restriction of `h_C` to `C` […] Countable determining tests and the measurable subsequence construction on p. 398
give a Borel recovery map. No boundary-supported residual distribution is omitted, since the full exterior projection
was retained."

**`exists_recovery_of_condGFF`**: let `h = g + X` where `g` (the exterior projection) is `𝓦`-measurable and `X` is,
conditionally on `𝓦`, a zero-boundary GFF on a random open `U_ω` inside the domain of a `𝓦`-measurable random
conformal chart `c` on a `𝓦`-event `A` (Aux. lemma 124's decomposition `h = h_B + h_C`, `Law(h_C | ℰ) = GFF₀(C)`).
If `𝓦` is generated up to null sets by a standard Borel record `E₀`, then almost surely on `A` the field `h` is a
Borel function of `E₀` and the transported field `chartTransport c 1 a k h`.

Proof: with `Z = (E₀, chartTransport h)` and `𝓜 = σ(Z) ∨ 𝒩`, every pairing `h(φ)` is, on `A`, the almost sure limit
`g(φ) + lim_n [(chartTransport h)(g_{J_n}) − (chartTransport 0)(g_{J_n}) − g(pushTest g_{J_n})]`
(`exists_ae_tendsto_pushTest`), a `𝓜`-measurable function; hence `1_A h` is `𝓜`-measurable
(`𝒟'(ℍ)` carries the cylinder σ-algebra) and the Doob–Dynkin lemma up to null sets
(`Lemma72.isAEDeterminedBy_of_measurable_sup_nullSets`, `𝒟'(ℍ)` standard Borel) gives the Borel map.

Conditional helper; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Sec7.Lemma725RefRecovery

open Chart

section Map

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The σ-algebra `σ(Z) ∨ 𝒩` of a record `Z` and the `P`-null sets. -/
@[instance_reducible]
def recSigma (P : Measure Ω) {β : Type*} [MeasurableSpace β] (Z : Ω → β) : MeasurableSpace Ω :=
  MeasurableSpace.comap Z inferInstance ⊔ Ito.nullSets P

/-- **The ambient recovery** (p. 398; Astra's Proposition 2.1 step 3). If `h − g` is, conditionally on `𝓦`, a
zero-boundary GFF on `U_ω`, with `g` `𝓦`-measurable and `U_ω` inside the domain of the `𝓦`-measurable random conformal
chart `c_ω` on the `𝓦`-event `A`, and `𝓦` is generated up to null sets by the standard Borel record `E₀`, then
almost surely on `A`, `h = F(E₀, chartTransport c 1 a k h)` for a Borel `F`. -/
theorem exists_recovery_of_condGFF [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓦] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    {h g : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hg : Measurable[𝓦] g)
    {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUH : ∀ ω, U ω ⊆ H) (hUA : ∀ ω ∈ A, U ω ⊆ (c ω).dom)
    (hcond : IsCondZeroBoundaryGFF P 𝓦 U fun ω => h ω - g ω)
    {ε₀ : Type*} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) (a k : ℝ) :
    ∃ F : ε₀ × DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens, Measurable F ∧
      ∀ᵐ ω ∂P, ω ∈ A → h ω = F (E₀ ω, chartTransport (hc ω) 1 a k (h ω)) := by
  classical
  set Ht : Ω → DistOn upperHalfPlaneOpens := fun ω => chartTransport (hc ω) 1 a k (h ω) with hHtdef
  have hHt : Measurable Ht := measurable_chartTransport_random' hc (fun z => h𝓦 _ (hdom z))
    (fun z => (hfwd z).mono h𝓦 le_rfl) (fun z => (hliftm z).mono h𝓦 le_rfl) hliftc hh 1 a k
  set R : Ω → DistOn upperHalfPlaneOpens := fun ω => chartTransport (hc ω) 1 a k 0 with hRdef
  have hR : Measurable[𝓦] R := @measurable_chartTransport_random' Ω 𝓦 c hc hdom hfwd hliftm hliftc
    (fun _ => 0) measurable_const 1 a k
  set Z : Ω → ε₀ × DistOn upperHalfPlaneOpens := fun ω => (E₀ ω, Ht ω) with hZdef
  have hZ : Measurable Z := (hE₀.mono h𝓦 le_rfl).prodMk hHt
  have hZc : Measurable[MeasurableSpace.comap Z inferInstance] Z := comap_measurable Z
  have hle1 : MeasurableSpace.comap Z inferInstance ≤ recSigma P Z := le_sup_left
  have hE₀Z : MeasurableSpace.comap E₀ inferInstance ≤ MeasurableSpace.comap Z inferInstance :=
    (measurable_fst.comp hZc).comap_le
  have h𝓦m : 𝓦 ≤ recSigma P Z := hgen.trans (sup_le_sup_right hE₀Z _)
  have hrecle : recSigma P Z ≤ mΩ := sup_le hZ.comap_le (Ito.nullSets_le P)
  have hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[recSigma P Z] s := fun s hs h0 =>
    (le_sup_right : Ito.nullSets P ≤ recSigma P Z) _ (MeasurableSpace.measurableSet_generateFrom ⟨hs, h0⟩)
  have hX : Measurable fun ω => h ω - g ω := LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((LQGMetric.measurable_distOn_apply φ).comp hh).sub
      (((LQGMetric.measurable_distOn_apply φ).comp hg).mono h𝓦 le_rfl)
  -- the pairing identity `h(pushTest ψ) = Ht(ψ) − R(ψ)`
  have hpair : ∀ ω (ψ : TestOn upperHalfPlaneOpens), h ω (pushTest (hc ω) ψ) = Ht ω ψ - R ω ψ := fun ω ψ => by
    simp only [hHtdef, hRdef, chartTransport_apply', zero_apply]
    ring
  -- every pairing of `1_A h` is `σ(Z) ∨ 𝒩`-measurable
  have hcoord : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable[recSigma P Z] fun ω => A.indicator (fun ω => h ω φ) ω := by
    intro φ
    obtain ⟨J, hJm, hconv⟩ := exists_ae_tendsto_pushTest h𝓦 hA hc hdom hfwd hX hUo hUH hUA hcond φ
    set Y : ℕ → Ω → ℝ := fun n ω => (Ht ω (genIdx (J n ω)) - R ω (genIdx (J n ω))) -
      g ω (pushTest (hc ω) (genIdx (J n ω))) with hYdef
    have hYm : ∀ n, Measurable[recSigma P Z] (Y n) := by
      intro n
      have hJ' : Measurable[recSigma P Z] (J n) := (hJm n).mono h𝓦m le_rfl
      have h1 : Measurable[recSigma P Z] fun ω => Ht ω (genIdx (J n ω)) :=
        @Ito.measurable_comp_index Ω ℝ (recSigma P Z) _ (fun ω j => Ht ω (genIdx j))
          (fun j => (((LQGMetric.measurable_distOn_apply (genIdx j)).comp
            (measurable_snd.comp hZc)).mono hle1 le_rfl)) (J n) hJ'
      have h2 : Measurable[recSigma P Z] fun ω => R ω (genIdx (J n ω)) :=
        @Ito.measurable_comp_index Ω ℝ (recSigma P Z) _ (fun ω j => R ω (genIdx j))
          (fun j => ((LQGMetric.measurable_distOn_apply (genIdx j)).comp hR).mono h𝓦m le_rfl) (J n) hJ'
      have h3 : Measurable[recSigma P Z] fun ω => g ω (pushTest (hc ω) (genIdx (J n ω))) :=
        @Ito.measurable_comp_index Ω ℝ (recSigma P Z) _ (fun ω j => g ω (pushTest (hc ω) (genIdx j)))
          (fun j => (@RandomTest.measurable_apply_of_forall_measurable Ω 𝓦 upperHalfPlaneOpens g hg
            (fun ω => pushTest (hc ω) (genIdx j))
            (fun z => @measurable_pushTest_apply Ω 𝓦 c hc hdom hfwd (genIdx j) z)).mono h𝓦m le_rfl)
          (J n) hJ'
      exact (h1.sub h2).sub h3
    set L : Ω → ℝ := A.indicator fun ω => g ω φ + limUnder atTop fun n => Y n ω with hLdef
    have hLm : Measurable[recSigma P Z] L := by
      refine Measurable.indicator ?_ (h𝓦m _ hA)
      exact (((LQGMetric.measurable_distOn_apply φ).comp hg).mono h𝓦m le_rfl).add
        (@StronglyMeasurable.limUnder ℕ Ω ℝ (recSigma P Z) _ _ atTop _ Y _ _
          fun n => (hYm n).stronglyMeasurable).measurable
    have hLe : L =ᵐ[P] A.indicator fun ω => h ω φ := by
      filter_upwards [hconv] with ω hω
      by_cases hωA : ω ∈ A
      · rw [hLdef, indicator_of_mem hωA, indicator_of_mem hωA]
        have hY : Tendsto (fun n => Y n ω) atTop (𝓝 (h ω φ - g ω φ)) := by
          refine (hω hωA).congr fun n => ?_
          simp only [hYdef, ← hpair, sub_apply]
        rw [hY.limUnder_eq]
        ring
      · rw [hLdef, indicator_of_notMem hωA, indicator_of_notMem hωA]
    exact Sec2.Restart.measurable_of_ae_eq_of_null hrecle hnull hLm
      (((LQGMetric.measurable_distOn_apply φ).comp hh).indicator (h𝓦 _ hA)) hLe
  -- the field restricted to `A` is `σ(Z) ∨ 𝒩`-measurable
  set Yd : Ω → DistOn upperHalfPlaneOpens := fun ω => if ω ∈ A then h ω else 0 with hYddef
  have hYd : Measurable[MeasurableSpace.comap Z inferInstance ⊔ Ito.nullSets P] Yd := by
    refine (@LQGMetric.measurable_distOn_iff upperHalfPlaneOpens Ω (recSigma P Z) Yd).2 fun φ => ?_
    have e : (fun ω => Yd ω φ) = fun ω => A.indicator (fun ω => h ω φ) ω := by
      funext ω
      by_cases hωA : ω ∈ A
      · simp only [hYddef, hωA, ↓reduceIte, indicator_of_mem hωA]
      · simp only [hYddef, hωA, ↓reduceIte, indicator_of_notMem hωA, zero_apply]
    rw [e]
    exact hcoord φ
  obtain ⟨F, hF, hFe⟩ := Lemma72.isAEDeterminedBy_of_measurable_sup_nullSets hZ hYd
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFe] with ω hω hωA
  have : Yd ω = h ω := by simp only [hYddef, hωA, ↓reduceIte]
  exact this.symm.trans hω

end Map

end InteractingSLE.Sec7.Lemma725RefRecovery
