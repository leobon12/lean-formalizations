/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76FChart
import InteractingSLE.Spec.Restart.R1GlueMain

/-!
# Lemma 7.6: retained data built from the retained histories

Packet PROVE-T15-CLOSE1 (2). (R1) conditions on the germs of the stopped union and the two retained killed histories
`cstHist` (`Lemma76FMark.lean`). The retained chart must be measurable for that σ-algebra. Here G7's retained data is
rebuilt from the **stopped capped paths** `ηcᵢ(· ∧ u)`, which are functions of the retained histories:

* `hproj` (reflection of the lower half-plane; the identity on `ℍ̄`), `stopPath ηc a = hproj ∘ ηc(· ∧ a)`;
* **`stopRet`**: the retained data of the two stopped paths, good event = the second tip is not visited earlier;
* **`isMeasGood_stopRet`**: it is measurable retained data for every σ-algebra containing the retained histories;
* **`retPairSet`**, **`measurableSet_retPairSet`**: the disjoint-pair event read from the retained histories (chart
  event, first tip adherent to the domain, disjoint prefixes, both stops before the lifetimes).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76F

open Supp7 Restart Sec6

/-! ### Stopped paths -/

/-- Reflection of the lower half-plane (the identity on `ℍ̄`). -/
def hproj (z : ℂ) : ℂ := ⟨z.re, |z.im|⟩

theorem continuous_hproj : Continuous hproj := by
  have e : hproj = fun z : ℂ => (z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * I :=
    funext fun z => Complex.ext (by simp [hproj]) (by simp [hproj])
  rw [e]
  fun_prop

theorem hproj_mem_Hbar (z : ℂ) : hproj z ∈ Hbar := show (0 : ℝ) ≤ |z.im| from abs_nonneg _

theorem hproj_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : hproj z = z :=
  Complex.ext rfl (show |z.im| = z.im from abs_of_nonneg hz)

theorem hproj_ofReal (x : ℝ) : hproj (x : ℂ) = x := hproj_of_im_nonneg (by simp)

variable {Ω : Type*}

/-- The path `ηc` stopped at `a`, reflected into `ℍ̄`. -/
def stopPath (ηc : Ω → ℝ≥0 → ℂ) (a : ℝ≥0) : Ω → ℝ≥0 → ℂ := fun ω t => hproj (ηc ω (min t a))

theorem continuous_stopPath {ηc : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (ηc ω)) (a : ℝ≥0) (ω : Ω) :
    Continuous (stopPath ηc a ω) :=
  continuous_hproj.comp ((hc ω).comp (continuous_id.min continuous_const))

/-- **The retained data of two stopped paths**; good event: the second tip is not visited earlier. -/
def stopRet (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (u r : ℝ≥0) : RetData Ω :=
  ⟨{ω | ∀ t < r, stopPath ηc₂ r ω t ≠ stopPath ηc₂ r ω r}, stopPath ηc₁ u, stopPath ηc₂ r, u, r⟩

theorem isRetGood_stopRet {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    {x₁ x₂ : ℝ} (h0₁ : ∀ ω, ηc₁ ω 0 = x₁) (h0₂ : ∀ ω, ηc₂ ω 0 = x₂) {u r : ℝ≥0} {ω : Ω}
    (hω : ω ∈ (stopRet ηc₁ ηc₂ u r).G) :
    IsRetGood ((stopRet ηc₁ ηc₂ u r).η₁ ω) u ((stopRet ηc₁ ηc₂ u r).η₂ ω) r := by
  refine ⟨(continuous_stopPath hc₁ u ω).continuousOn, (continuous_stopPath hc₂ r ω).continuousOn,
    fun t _ => hproj_mem_Hbar _, fun t _ => hproj_mem_Hbar _, ?_, ?_, hω⟩
  · show (hproj (ηc₁ ω (min 0 u))).im = 0
    rw [min_eq_left zero_le, h0₁, hproj_ofReal]; simp
  · show (hproj (ηc₂ ω (min 0 r))).im = 0
    rw [min_eq_left zero_le, h0₂, hproj_ofReal]; simp

/-! ### Measurability for the retained σ-algebra -/

/-- **A first revisit of the endpoint is a countable condition.** -/
theorem measurableSet_tipFree {m : MeasurableSpace Ω} {f : Ω → ℝ≥0 → ℂ} (hf : ∀ t, Measurable[m] fun ω => f ω t)
    (hc : ∀ ω, Continuous (f ω)) (r : ℝ≥0) : MeasurableSet[m] {ω | ∀ t < r, f ω t ≠ f ω r} := by
  have heq : {ω | ∀ t < r, f ω t ≠ f ω r}ᶜ =
      ⋃ q : {q : ℚ // (q : ℝ).toNNReal < r}, (univ ∩ {ω | ∃ s ≤ (fun _ : Ω => ((q : ℚ) : ℝ).toNNReal) ω,
        ∃ t ≤ (fun _ : Ω => (0 : ℝ≥0)) ω, f ω s = (fun ω (_ : ℝ≥0) => f ω r) ω t}) := by
    ext ω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_not, mem_iUnion, univ_inter, exists_prop]
    constructor
    · rintro ⟨t, ht, he⟩
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < r from ht)
      have hq0 : (0 : ℝ) ≤ q := le_trans t.2 hq1.le
      refine ⟨⟨q, ?_⟩, t, ?_, 0, le_rfl, he⟩
      · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq2
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq1.le
    · rintro ⟨⟨q, hq⟩, s, hs, t, -, he⟩
      exact ⟨s, lt_of_le_of_lt hs hq, he⟩
  have hm : MeasurableSet[m] {ω | ∀ t < r, f ω t ≠ f ω r}ᶜ := by
    rw [heq]
    refine MeasurableSet.iUnion fun q => ?_
    exact @measurableSet_inter_exists_eq Ω m univ MeasurableSet.univ f (fun ω (_ : ℝ≥0) => f ω r) hf
      (fun _ => hf r) _ _ measurable_const measurable_const (fun ω _ => (hc ω).continuousOn)
      (fun _ _ => continuousOn_const)
  exact hm.of_compl

variable {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}

/-- The stopped path at a fixed time is read from the retained killed history. -/
theorem stopPath_eq_recon (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (ω : Ω) (t : ℝ≥0) :
    stopPath ηc₁ u ω t = hproj (Restart.recon (cstHist ηc₁ ηc₂ ζ₁ ζ₂ u r ω).1.1 (min t u)) := by
  show hproj (ηc₁ ω (min t u)) = hproj (Restart.recon (histOf (pathCoord (ηc₁ ω)) u) (min t u))
  rw [recon_histOf (T' := ⊤) (by simpa using hc₁ ω) le_top
    (ENNReal.coe_le_coe.2 (min_le_right t u))]

theorem stopPath_eq_recon' (hc₂ : ∀ ω, Continuous (ηc₂ ω)) (ω : Ω) (t : ℝ≥0) :
    stopPath ηc₂ r ω t = hproj (Restart.recon (cstHist ηc₁ ηc₂ ζ₁ ζ₂ u r ω).2.1 (min t r)) := by
  show hproj (ηc₂ ω (min t r)) = hproj (Restart.recon (histOf (pathCoord (ηc₂ ω)) r) (min t r))
  rw [recon_histOf (T' := ⊤) (by simpa using hc₂ ω) le_top
    (ENNReal.coe_le_coe.2 (min_le_right t r))]

/-- **The stopped retained data is measurable for every σ-algebra containing the retained histories.** -/
theorem isMeasGood_stopRet {𝒦 : MeasurableSpace Ω}
    (h𝒦 : MeasurableSpace.comap (cstHist ηc₁ ηc₂ ζ₁ ζ₂ u r) inferInstance ≤ 𝒦)
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω)) {x₁ x₂ : ℝ} (h0₁ : ∀ ω, ηc₁ ω 0 = x₁)
    (h0₂ : ∀ ω, ηc₂ ω 0 = x₂) : @RetData.IsMeasGood Ω 𝒦 (stopRet ηc₁ ηc₂ u r) := by
  have hR : Measurable[𝒦] (cstHist ηc₁ ηc₂ ζ₁ ζ₂ u r) := (comap_measurable _).mono h𝒦 le_rfl
  have hm₁ : ∀ t, Measurable[𝒦] fun ω => (stopRet ηc₁ ηc₂ u r).η₁ ω t := fun t => by
    let _ : MeasurableSpace Ω := 𝒦
    have e : (fun ω => (stopRet ηc₁ ηc₂ u r).η₁ ω t) =
        fun ω => hproj (Restart.recon (cstHist ηc₁ ηc₂ ζ₁ ζ₂ u r ω).1.1 (min t u)) :=
      funext fun ω => stopPath_eq_recon hc₁ ω t
    rw [e]
    exact continuous_hproj.measurable.comp
      ((Restart.measurable_recon _).comp (measurable_fst.comp (measurable_fst.comp hR)))
  have hm₂ : ∀ t, Measurable[𝒦] fun ω => (stopRet ηc₁ ηc₂ u r).η₂ ω t := fun t => by
    let _ : MeasurableSpace Ω := 𝒦
    have e : (fun ω => (stopRet ηc₁ ηc₂ u r).η₂ ω t) =
        fun ω => hproj (Restart.recon (cstHist ηc₁ ηc₂ ζ₁ ζ₂ u r ω).2.1 (min t r)) :=
      funext fun ω => stopPath_eq_recon' hc₂ ω t
    rw [e]
    exact continuous_hproj.measurable.comp
      ((Restart.measurable_recon _).comp (measurable_fst.comp (measurable_snd.comp hR)))
  exact @RetData.IsMeasGood.mk Ω 𝒦 (stopRet ηc₁ ηc₂ u r)
    (measurableSet_tipFree hm₂ (continuous_stopPath hc₂ r) r) hm₁ hm₂
    (fun ω hω => isRetGood_stopRet hc₁ hc₂ h0₁ h0₂ hω)

/-! ### The disjoint-pair event of retained data -/

/-- **The disjoint-pair event of retained data with lifetime records `L₁`, `L₂`**: the chart event, the first tip
adherent to the domain, disjoint prefixes, both cutoffs before the lifetimes. -/
def pairSet (d : RetData Ω) (L₁ L₂ : Ω → ℝ≥0∞) : Set Ω :=
  d.E ∩ {ω | d.η₁ ω d.u ∈ closure (d.D ω)} ∩ {ω | ¬ ∃ s ≤ d.u, ∃ t ≤ d.r, d.η₁ ω s = d.η₂ ω t} ∩
    {ω | (d.u : ℝ≥0∞) < L₁ ω ∧ (d.r : ℝ≥0∞) < L₂ ω}

theorem measurableSet_pairSet [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) {L₁ L₂ : Ω → ℝ≥0∞}
    (hL₁ : Measurable L₁) (hL₂ : Measurable L₂) : MeasurableSet (pairSet d L₁ L₂) := by
  have hex := measurableSet_inter_exists_eq hd.measurableSet_G hd.meas₁ hd.meas₂ (c₁ := fun _ => d.u)
    (c₂ := fun _ => d.r) measurable_const measurable_const
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hd.good ω hω).1)
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hd.good ω hω).2.1)
  have hcl := measurableSet_mem_closure hd.isOpen_D hd.measurableSet_mem_D (hd.meas₁ d.u)
  have heq : pairSet d L₁ L₂ = d.E ∩ {ω | d.η₁ ω d.u ∈ closure (d.D ω)} ∩
      (d.G \ (d.G ∩ {ω | ∃ s ≤ d.u, ∃ t ≤ d.r, d.η₁ ω s = d.η₂ ω t})) ∩
      ({ω | (d.u : ℝ≥0∞) < L₁ ω} ∩ {ω | (d.r : ℝ≥0∞) < L₂ ω}) := by
    ext ω
    simp only [pairSet, mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, not_and]
    constructor
    · rintro ⟨⟨⟨hE, hc⟩, hn⟩, h1, h2⟩
      exact ⟨⟨⟨hE, hc⟩, RetData.E_subset_G hE, fun _ => hn⟩, h1, h2⟩
    · rintro ⟨⟨⟨hE, hc⟩, hG, hn⟩, h1, h2⟩
      exact ⟨⟨⟨hE, hc⟩, hn hG⟩, h1, h2⟩
  rw [heq]
  exact ((hd.measurableSet_E.inter hcl).inter (hd.measurableSet_G.diff hex)).inter
    ((measurableSet_lt measurable_const hL₁).inter (measurableSet_lt measurable_const hL₂))

/-- **The disjoint-pair event is the disjoint-pair predicate** of the retained paths, on the good event. -/
theorem mem_pairSet_iff [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) {L₁ L₂ : Ω → ℝ≥0∞} {ω : Ω}
    (hG : ω ∈ d.G) :
    ω ∈ pairSet d L₁ L₂ ↔ Lemma76Exit.IsDisjointPair (d.η₁ ω) (L₁ ω) d.u (d.η₂ ω) (L₂ ω) d.r := by
  constructor
  · rintro ⟨⟨⟨hE, hc⟩, hn⟩, h1, h2⟩
    have hD := hd.D_of_mem hE
    have hE' := hE
    obtain ⟨⟨⟨-, hH⟩, -⟩, hcl⟩ := hE'
    refine ⟨h1, h2, hH, ?_, ?_, ?_⟩
    · refine Set.disjoint_left.2 ?_
      rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
      exact hn ⟨s, hs.2, t, ht.2, he.symm⟩
    · have : d.η₂ ω d.r ∈ closure (d.DOf d.E₀ ω) := hcl
      rw [hd.DOf_of_mem RetData.E₀_subset_G hE.1] at this
      exact this
    · rw [← hD]; exact (hc : d.η₁ ω d.u ∈ closure (d.D ω))
  · intro hp
    have hE := mem_E_of_isDisjointPair hd hG (fun s _ => rfl) (fun t _ => rfl) hp
    refine ⟨⟨⟨hE, ?_⟩, ?_⟩, hp.1, hp.2.1⟩
    · show d.η₁ ω d.u ∈ closure (d.D ω)
      rw [hd.D_of_mem hE]; exact hp.2.2.2.2.2
    · rintro ⟨s, hs, t, ht, he⟩
      exact Set.disjoint_left.1 hp.2.2.2.1 ⟨s, ⟨zero_le, hs⟩, rfl⟩ ⟨t, ⟨zero_le, ht⟩, he.symm⟩

end Lemma76F

end Sec7

end InteractingSLE
