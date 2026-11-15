/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LMeanRet
import InteractingSLE.Spec.Supplement.GB6LMeanChain
import InteractingSLE.Spec.Supplement.BW1PropChain

/-!
# BW1's union mean, part 2: the relative chain of a record and the union mean

Packet PROVE-BW1-LINEMEAN. GB6's union mean with every earlier hull identity
(`Supp8.GB6LMean.ae_eqOn_unionMean_gb6_hull`) reads the retained prefix from GB6's flow `(Wα, ζα)` at a FIXED own time
`s` with an interior tip `α(s) ∈ ℍ`. BW1 retains the completed piece, read from its RECORD: driver `rdrv r`, own time
`recS r`, the trace ending on `ℝ`. A good sample of BW1's relative exploration (`BW1Ver.IsGoodSample`: positive own
time, the retained chart, a global trace of the record driver, a complete counterflow trace) carries everything the
chain needs, with `0 < recS r` in place of the interior tip (`BW1Prop.exists_relChain_trace_close`):

* **`exists_relChain_rec_hull`**: the relative chain at a counterflow time `t` before the contact, with every earlier
  hull identity (`HullsUpTo`), the disjoint closures and the tip limit (deterministic; the proof of
  `Supp8.GB6LMean.exists_relChain_tip_hull` with the record's own time);
* `isRelConfigOff_rec`: the relative configuration of a good sample (`Q3Rel.isRelConfigOff_gb6` with the chart of
  the sample);
* **`ae_eqOn_unionMean_bw`**: the union mean on the good samples before the contact, for a retained set given
  through the record and the retained mean `hind₁` for an arbitrary record word `β` (the proof of
  `ae_eqOn_unionMean_gb6_hull`, the generic union lemma `Q3Chain.ae_eqOn_unionMean_of_relConfigOff_ver`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.BW1LMean

open Exist.StagedLaw BW1Ver
open Supp8.GB6 (relMap relInv relClock firstContactTime sphereInv)
open Supp8.Q3Rel (invHull relLog relBad IsRelConfigOff)
open Supp8.Q3Kernel Supp8.Q3Chain LocalSets
open Supp8.GB6LMean (HullsUpTo)

/-! ### The relative chain of a good sample -/

section Sample

/-- **The relative chain of a record at a counterflow time, with every earlier hull identity.** On a good sample
(record `r`, record trace `A`, counterflow driver `w` with trace `γ`), for `0 < t < t₁ < T_c` (`T_c` the first contact
with the retained prefix): a globally continuous relative driver `Wr` from `0` with a continuous Loewner trace
generates `Ψ(K'_{t'})` at `a(t')` for every `t' ≤ t` (`Ψ = relMap (rdrv r) (recS r)`, `a` the relative clock), with
`a(t) > 0`, disjoint closures at `t` and the tip limit. -/
theorem exists_relChain_rec_hull {r : RecData} {A : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hg : IsGoodSample r A w γ) {t t₁ : ℝ≥0} (ht0 : 0 < t) (htt₁ : t < t₁)
    (ht₁ : (t₁ : ℝ≥0∞) < contactT γ A (recS r)) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      0 < relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t ∧
      relMap (rdrv r) (recS r) '' fwdHull (fun x : ℝ => w x.toNNReal) t =
        fwdHull Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t) ∧
      HullsUpTo (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) Wr t ∧
      Disjoint (closure (fwdHull (rdrv r) (recS r)))
        (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (fun x : ℝ => w x.toNNReal) t)) ∧
      Tendsto (fun y => fwdMap (fun x : ℝ => w x.toNNReal) t
        (relInv (rdrv r) (recS r) (fwdMapInv Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t) y)))
        (𝓝[H] 0) (𝓝 0) := by
  set U := rdrv r with hUdef
  set s := recS r with hsdef
  set Tc := contactT γ A s with hTcdef
  set Wc : ℝ → ℝ := fun x => w x.toNNReal with hWcdef
  have hU : Continuous U := continuous_rdrv r
  have hU0 : U 0 = 0 := rdrv_zero r
  have hw := hg.cont
  have hw0 := hg.zero
  have hγ := hg.ctrace
  have hΨ := hg.chart
  have hWcc : Continuous Wc := hw.comp continuous_real_toNNReal
  have hWc0 : Wc 0 = 0 := by simp [hWcdef, hw0]
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hg.pos
  have hst₂ : (s : ℝ) < (s : ℝ) + 1 := by linarith
  have hUeq : ∀ x ∈ Icc (0 : ℝ) ((s : ℝ) + 1), U x = (fun u : ℝ≥0 => rdrv r u) x.toNNReal := fun x hx => by
    simp only [hUdef, Real.coe_toNNReal x hx.1]
  have hwα0 : (fun u : ℝ≥0 => rdrv r u) 0 = 0 := by simp only [NNReal.coe_zero, rdrv_zero]
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hK, ha0, hsm, hac, hd⟩ :=
    BW1Prop.exists_relChain_trace_close hg.trace (continuous_rdrv_nn r).continuousOn hwα0 ENNReal.coe_lt_top hs0
      hU hU0 hst₂ hUeq hγ hw hw0 ht₁
  set a : ℝ → ℝ := relClock U s Wc with hadef
  have htTc : (t : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 htt₁.le) ht₁
  have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := lt_of_le_of_lt bot_le htTc
  have hu : 0 < a t := by
    have := hsm h0Tc htTc ht0
    simpa [ha0] using this
  have hKt := hK t htt₁.le
  have hdt := hd t htTc
  have hdA : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (fwdHull Wc T)) (closure (invHull U s)) :=
    fun T hT => Supp8.Q3Rel.disjoint_closure_invHull hU hs0.le (hd T hT)
  have hγL := isLoewnerTrace_of_isGeneratingTrace hγ
  have hSbK := Supp8.Q3Rel.relBad_notMem_closure hU hU0 hs0.le hWcc t.2 hKt (hdA t htTc)
  obtain ⟨hgp, hA0⟩ := goodPt_zero_and_notMem hΨ hWcc t.2 hWr hWr0 hηr hu hKt (hdA t htTc) hSbK
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hu, hKt, fun t' ht' => hK t' (ht'.trans htt₁.le), hdt, ?_⟩
  refine tendsto_tip_of_later hΨ hWcc hWc0 hγL t.2 hWr hWr0 hηr hu.le hKt (hdA t htTc) hgp hA0 fun δ hδ => ?_
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hcont : ContinuousAt (fun t : ℝ≥0 => a t) t := hac.continuousAt (hopen.mem_nhds htTc)
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.1 hcont δ hδ
  set ε : ℝ := min (min δ η) ((t₁ : ℝ) - t) / 2 with hεdef
  have htt₁' : (t : ℝ) < t₁ := by exact_mod_cast htt₁
  have hε0 : 0 < ε := by
    have : 0 < min (min δ η) ((t₁ : ℝ) - t) := lt_min (lt_min hδ hη) (by linarith)
    rw [hεdef]; linarith
  have hεδ : ε < δ := by
    have := min_le_left (min δ η) ((t₁ : ℝ) - t)
    have := min_le_left δ η
    rw [hεdef]; linarith
  have hεη : ε < η := by
    have := min_le_left (min δ η) ((t₁ : ℝ) - t)
    have := min_le_right δ η
    rw [hεdef]; linarith
  have hεt : ε < (t₁ : ℝ) - t := by
    have := min_le_right (min δ η) ((t₁ : ℝ) - t)
    rw [hεdef]; linarith
  set t' : ℝ≥0 := ⟨(t : ℝ) + ε, by positivity⟩ with ht'def
  have ht'v : (t' : ℝ) = t + ε := rfl
  have htt' : t < t' := by rw [← NNReal.coe_lt_coe, ht'v]; linarith
  have ht't₁ : t' ≤ t₁ := by rw [← NNReal.coe_le_coe, ht'v]; linarith
  have ht'Tc : (t' : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht't₁) ht₁
  have hdist : dist t' t < η := by
    rw [NNReal.dist_eq, ht'v, add_sub_cancel_left, abs_of_pos hε0]
    exact hεη
  have hau : a t < a t' := hsm htTc ht'Tc htt'
  have hau' : a t' < a t + δ := by
    have := hηb hdist
    rw [Real.dist_eq] at this
    linarith [le_abs_self (a t' - a t)]
  refine ⟨t', a t', by rw [ht'v]; linarith, by rw [ht'v]; linarith, hau, hau', hK t' ht't₁, ?_⟩
  exact Set.disjoint_of_subset_left subset_closure
    (Set.disjoint_of_subset_right subset_closure (hdA t' ht'Tc))

/-- **The relative configuration of a good sample** (`Q3Rel.isRelConfigOff_gb6` with the retained chart of the
sample). -/
theorem isRelConfigOff_rec {r : RecData} {A : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hg : IsGoodSample r A w γ) {t : ℝ≥0} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {χ lam : ℝ} {β₀ βE βu : ℝ → ℝ}
    {S₀ SE Su : Finset ℝ} {G₀ GE G v : ℂ → ℝ} (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t)
    (hK : relMap (rdrv r) (recS r) '' fwdHull (fun x : ℝ => w x.toNNReal) t =
      fwdHull Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t))
    (hd : Disjoint (closure (fwdHull (rdrv r) (recS r)))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (fun x : ℝ => w x.toNNReal) t)))
    (htip : Tendsto (fun y => fwdMap (fun x : ℝ => w x.toNNReal) t
      (relInv (rdrv r) (recS r) (fwdMapInv Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t) y)))
      (𝓝[H] 0) (𝓝 0))
    (hG₀ : IsBoundedHarmonicExtension β₀ S₀ G₀) (hGE : IsBoundedHarmonicExtension βE SE GE)
    (hG : IsBoundedHarmonicExtension βu Su G)
    (hsE : Supp8.BHMean.IsSideWord βE SE (fwdMapInv (fun x : ℝ => w x.toNNReal) t)
      (fwdHull (fun x : ℝ => w x.toNNReal) t) lam)
    (hsu : Supp8.BHMean.IsSideWord βu Su (fwdMapInv Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t))
      (fwdHull Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t)) lam)
    (hflow : Supp8.BHMean.IsFlowedWord βu β₀ Su S₀
      (fwdMapInv Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t))
      (fwdHull Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t)))
    (hv : ∀ z, v z = G (fwdMap Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t)
        (relMap (rdrv r) (recS r) z)) -
      χ * ((logDerivFwd Wr (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t)
        (relMap (rdrv r) (recS r) z)).im + (relLog (rdrv r) (recS r) z).im)) :
    IsRelConfigOff (invHull (rdrv r) (recS r)) (relMap (rdrv r) (recS r)) (relInv (rdrv r) (recS r))
      (relLog (rdrv r) (recS r)) (relBad (rdrv r) (recS r)) (fun x : ℝ => w x.toNNReal) Wr
      (fun x : ℝ => γ x.toNNReal) ηr t (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t) χ lam
      β₀ βE βu S₀ SE Su G₀ GE G v := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hWc : Continuous fun x : ℝ => w x.toNNReal := hg.cont.comp continuous_real_toNNReal
  have hWc0 : (fun x : ℝ => w x.toNNReal) 0 = 0 := by simp [hg.zero]
  have hd' := Supp8.Q3Rel.disjoint_closure_invHull hU (recS r).coe_nonneg hd
  exact ⟨hg.chart, hWc, hWc0, isLoewnerTrace_of_isGeneratingTrace hg.ctrace, t.2, hWr, hWr0, hηr, hu, hK, hd',
    Supp8.Q3Rel.relBad_notMem_closure hU hU0 (recS r).coe_nonneg hWc t.2 hK hd', htip, hG₀, hGE, hG, hsE, hsu,
    hflow, hv⟩

/-- **The relative chain of a record at a counterflow time** (the conclusion of `exists_relChain_rec_hull`, as a
predicate of the pair `(Wr, ηr)`). -/
def IsRecChain (r : RecData) (w : ℝ≥0 → ℝ) (t : ℝ≥0) (p : (ℝ → ℝ) × (ℝ → ℂ)) : Prop :=
  Continuous p.1 ∧ p.1 0 = 0 ∧ IsLoewnerTrace p.1 p.2 ∧
    0 < relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t ∧
    relMap (rdrv r) (recS r) '' fwdHull (fun x : ℝ => w x.toNNReal) t =
      fwdHull p.1 (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t) ∧
    HullsUpTo (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) p.1 t ∧
    Disjoint (closure (fwdHull (rdrv r) (recS r)))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (fun x : ℝ => w x.toNNReal) t)) ∧
    Tendsto (fun y => fwdMap (fun x : ℝ => w x.toNNReal) t
      (relInv (rdrv r) (recS r) (fwdMapInv p.1 (relClock (rdrv r) (recS r) (fun x : ℝ => w x.toNNReal) t) y)))
      (𝓝[H] 0) (𝓝 0)

theorem exists_isRecChain {r : RecData} {A : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hg : IsGoodSample r A w γ) {t : ℝ≥0} (ht0 : 0 < t) (htc : (t : ℝ≥0∞) < contactT γ A (recS r)) :
    ∃ p, IsRecChain r w t p := by
  obtain ⟨t₁, htt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htc
  obtain ⟨Wr, ηr, hR⟩ := exists_relChain_rec_hull hg ht0 (ENNReal.coe_lt_coe.1 htt₁) ht₁
  exact ⟨(Wr, ηr), hR⟩

end Sample

/-! ### The union mean on the good samples -/

section Union

/-- **BW1's union mean on the good samples before the contact** (`Supp8.GB6LMean.ae_eqOn_unionMean_gb6_hull` with
the retained prefix read from a record). Counterflow frame: the counterflow is an optional hull coupling of its word
`(b′, J′)` at `16/κ` (field `h′`, driver `W`, infinite lifetime), `A` is a retained set equal to the inverted record
hull `invHull (rdrv r) (recS r)` on the event `D` of good samples (record `rec`, traces `Ar`, `γ`) before the contact,
`K` is the counterflow hull at `t > 0`, and the retained mean `hind₁` holds on `D` for a record word `β`. Then a.s.
on `D` there are a relative chain `Wr` generating every relative hull up to `a(t)` and a bounded harmonic extension `G`
of `β`'s flowed counterflow data, such that every harmonic representative `wU` of the union mean satisfies
`wU + 𝔥⁰ = G ∘ g̃_u ∘ Ψ − χ(16/κ) (Im log g̃_u′ ∘ Ψ + Im relLog)` off `A ∪ K`. -/
theorem ae_eqOn_unionMean_bw {κ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {rec : Ω → RecData} {Ar γ : Ω → ℝ≥0 → ℂ} (β : Ω → Restart.BoundaryWord)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL (16 / κ) b' J' 0 0)
      (flowLineRhoR (16 / κ) b' J' 0 0) P 𝓕 W VL VR B ζ h')
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P)
    (t : ℝ≥0) (ht0 : 0 < t) (D : Set Ω)
    (hD : ∀ ω ∈ D, IsGoodSample (rec ω) (Ar ω) (W · ω) (γ ω) ∧
      (t : ℝ≥0∞) < contactT (γ ω) (Ar ω) (recS (rec ω)))
    {A : Ω → Set ℂ} (hAeq : ∀ ω ∈ D, A ω = invHull (rdrv (rec ω)) (recS (rec ω)))
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    {K : Ω → Set ℂ} (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) t)
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] K)
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h' u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ K ω) (WholeField.centredField h' u₀) P)
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ K ω) (WholeField.centredField h' u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField h' u₀) P g₁)
    (hg₂ : IsLocalSetMean K (WholeField.centredField h' u₀) P g₂)
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D →
      ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension (cfData (16 / κ) (β ω).fn (β ω).jumps)
          (cfJumps (β ω).fn (β ω).jumps) G₀ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => G₀ (relMap (rdrv (rec ω)) (recS (rec ω)) z) -
              chiC (16 / κ) * (relLog (rdrv (rec ω)) (recS (rec ω)) z).im)
            (H \ A ω)) :
    ∀ᵐ ω ∂P, ω ∈ D →
      ∃ (Wr : ℝ → ℝ) (G : ℂ → ℝ), Continuous Wr ∧ Wr 0 = 0 ∧
        HullsUpTo (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) Wr t ∧
        IsBoundedHarmonicExtension
          (cfFlowedData (16 / κ) (β ω).fn (β ω).jumps Wr
            (relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) t))
          (cfFlowedJumps (β ω).fn (β ω).jumps Wr
            (relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) t)) G ∧
        ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ K ω)) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) →
            g ω φ = ∫ z, wU z * φ z) →
          EqOn (fun z => wU z + u₀ z)
            (fun z => G (fwdMap Wr (relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) t)
                (relMap (rdrv (rec ω)) (recS (rec ω)) z)) -
              chiC (16 / κ) *
                ((logDerivFwd Wr (relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) t)
                  (relMap (rdrv (rec ω)) (recS (rec ω)) z)).im +
                  (relLog (rdrv (rec ω)) (recS (rec ω)) z).im))
            (H \ (A ω ∪ K ω)) := by
  classical
  -- the per-sample relative chain, chosen
  set pr : Ω → (ℝ → ℝ) × (ℝ → ℂ) := fun ω => Classical.epsilon (IsRecChain (rec ω) (W · ω) t) with hpr
  have hprs : ∀ ω ∈ D, IsRecChain (rec ω) (W · ω) t (pr ω) := fun ω hω =>
    Classical.epsilon_spec (exists_isRecChain (hD ω hω).1 ht0 (hD ω hω).2)
  set uc : Ω → ℝ := fun ω => relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) t with huc
  -- the three bounded harmonic extensions
  set G₀ : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) (β ω).fn (β ω).jumps 0 0) (flowLineRhoR (16 / κ) (β ω).fn (β ω).jumps 0 0)
    (flowLineXL (β ω).fn (β ω).jumps 0) (flowLineXR (β ω).fn (β ω).jumps 0)).choose with hG₀
  set GE : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0)
    (fun i => Exist.StagedLaw.markPosL (fun r : ℝ => W r.toNNReal ω) t (flowLineXL b' J' 0 i))
    (fun j => Exist.StagedLaw.markPos (fun r : ℝ => W r.toNNReal ω) t (flowLineXR b' J' 0 j))).choose with hGE
  set G : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) (β ω).fn (β ω).jumps 0 0) (flowLineRhoR (16 / κ) (β ω).fn (β ω).jumps 0 0)
    (fun i => Exist.StagedLaw.markPosL (pr ω).1 (uc ω) (flowLineXL (β ω).fn (β ω).jumps 0 i))
    (fun j => Exist.StagedLaw.markPos (pr ω).1 (uc ω) (flowLineXR (β ω).fn (β ω).jumps 0 j))).choose with hG
  have hG₀s : ∀ ω, IsBoundedHarmonicExtension (cfData (16 / κ) (β ω).fn (β ω).jumps)
      (cfJumps (β ω).fn (β ω).jumps) (G₀ ω) := fun ω => by
    rw [coe_cfJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  have hGEs : ∀ ω, IsBoundedHarmonicExtension (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t) (GE ω) := fun ω => by
    rw [cfFlowedJumps, flowedJumps, coe_initJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  have hGs : ∀ ω, IsBoundedHarmonicExtension (cfFlowedData (16 / κ) (β ω).fn (β ω).jumps (pr ω).1 (uc ω))
      (cfFlowedJumps (β ω).fn (β ω).jumps (pr ω).1 (uc ω)) (G ω) := fun ω => by
    rw [cfFlowedJumps, flowedJumps, coe_initJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  -- the candidate mean
  set v : Ω → ℂ → ℝ := fun ω z =>
    G ω (fwdMap (pr ω).1 (uc ω) (relMap (rdrv (rec ω)) (recS (rec ω)) z)) -
      chiC (16 / κ) * ((logDerivFwd (pr ω).1 (uc ω) (relMap (rdrv (rec ω)) (recS (rec ω)) z)).im +
        (relLog (rdrv (rec ω)) (recS (rec ω)) z).im) with hv
  -- the configuration on `D`
  have hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigOff (A ω) (relMap (rdrv (rec ω)) (recS (rec ω)))
      (relInv (rdrv (rec ω)) (recS (rec ω))) (relLog (rdrv (rec ω)) (recS (rec ω)))
      (relBad (rdrv (rec ω)) (recS (rec ω))) (fun r : ℝ => W r.toNNReal ω) (pr ω).1
      (fun r : ℝ => γ ω r.toNNReal) (pr ω).2 ((fun _ : Ω => (t : ℝ)) ω) (uc ω) (chiC (16 / κ))
      (Real.pi / Real.sqrt (16 / κ)) (cfData (16 / κ) (β ω).fn (β ω).jumps)
      (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedData (16 / κ) (β ω).fn (β ω).jumps (pr ω).1 (uc ω)) (cfJumps (β ω).fn (β ω).jumps)
      (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedJumps (β ω).fn (β ω).jumps (pr ω).1 (uc ω)) (G₀ ω) (GE ω) (G ω) (v ω) := by
    refine Eventually.of_forall fun ω hωD => ?_
    obtain ⟨hgω, -⟩ := hD ω hωD
    obtain ⟨hWr, hWr0, hηr, hu, hK, -, hd, htip⟩ := hprs ω hωD
    rw [hAeq ω hωD]
    have hWc : Continuous fun r : ℝ => W r.toNNReal ω := hgω.cont.comp continuous_real_toNNReal
    have hWc0 : (fun r : ℝ => W r.toNNReal ω) 0 = 0 := by simp [hgω.zero]
    have hη := isLoewnerTrace_of_isGeneratingTrace hgω.ctrace
    exact isRelConfigOff_rec hgω hWr hWr0 hηr hu.le hK hd htip (hG₀s ω) (hGEs ω) (hGs ω)
      (isSideWord_cfFlowedData hη hWc hWc0 t.2 (16 / κ)) (isSideWord_cfFlowedData hηr hWr hWr0 hu.le (16 / κ))
      (isFlowedWord_cfFlowedData hηr hWr hWr0 hu (16 / κ)) fun z => rfl
  -- locality and topology of the counterflow hull
  obtain ⟨hX, hker⟩ := hC.2.2.2
  have hτζ : ∀ᵐ ω ∂P, ((((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hK' : IsLocalSet (fun ω => fwdHull (fun r : ℝ => W r.toNNReal ω) t) h' P := by
    have h1 := (hker (fun _ => ((t : ℝ≥0) : WithTop ℝ≥0)) (isStoppingTime_const _ t) hτζ).1
    simpa only [WithTop.untopD_coe] using h1
  have hlK : IsLocalSet K (WholeField.centredField h' u₀) P := by
    refine Coupling.IsLocalSet.congr_set
      (WholeField.IsLocalSet.sub_dist hK' (WholeField.isHarmonicDistOn_smoothDist hu₀.1)) ?_
    filter_upwards [hKeq] with ω hω
    simp only [hω]
  have hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ω)) z) := by
    filter_upwards [hKeq, hW] with ω hω hWω
    rw [hω]
    exact Sec5.GlueCond.not_isBounded_lowerUnion_of_isHPHull
      (isHPHull_fwdHull (hWω.1.comp continuous_real_toNNReal) t.coe_nonneg)
  -- the two partial means
  have hind₂ := ae_eqOn_cfMean (by positivity) hC hζ hu₀ hh0 t hKeq hKm hg₂
  have hmain := ae_eqOn_unionMean_of_relConfigOff_ver hh0 hu₀.1 hu₀.2.1 hAm hKm hdA hlA hlK hlU hunbA hunbK hg hg₁
    hg₂ (D := D) (by filter_upwards [hKeq] with ω hω _ using hω) hcfg
    (by
      filter_upwards [hind₁] with ω hω hωD w₁ hw₁ hr₁
      exact hω hωD (G₀ ω) (hG₀s ω) w₁ hw₁ hr₁)
    (by
      filter_upwards [hind₂, hW] with ω hω hWω hωD w₂ hw₂ hr₂
      exact hω hWω.1 hWω.2 (GE ω) (hGEs ω) w₂ hw₂ hr₂)
  filter_upwards [hmain] with ω hω hωD
  obtain ⟨h1, h2, -, -, -, h6, -, -⟩ := hprs ω hωD
  exact ⟨(pr ω).1, G ω, h1, h2, h6, hGs ω, fun wU hwU hrU => hω hωD wU hwU hrU⟩

end Union

end InteractingSLE.Theorem14.BW1LMean
