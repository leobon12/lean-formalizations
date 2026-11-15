/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1Glue
import InteractingSLE.Spec.Restart.R1Flow

/-!
# (R1) gluing: the retained histories of the uncapped pair and the bounded grid boxes

Packet PROVE-RESTART-CPL7. Lemma 7.7's proof (p. 284–285) first treats bounded terminal times and then covers "finite
common-contact realizations […] by countably many bounded grid boxes" (Aux. 77's proof, p. 288). Here:

* **the retained labelled histories** `retHist d` of the two paths of measurable pair data `d` (CPL4's `PairData`),
  stopped at their first contact (`⊤` if they never meet), with their killing records; the conditioning σ-algebra
  `retSigma d P = mΩ ⊓ aeSigma (comap (retHist d)) P` (the history σ-algebra, completed by null sets);
* **the meeting boxes** `meetBox d m` (first contact `(s₀, t₀)` with `s₀, t₀ < m` before both lifetimes), read from the
  retained histories, and **the meeting branch** `meetSet d = ⋃ₘ meetBox d m` (a first contact with two nonempty
  continuations);
* the deterministic comparison of the first contact of two paths with that of their **capped** versions
  `γ(· ∧ ζ ∧ m)` (`isFirstContact_capped`, `isFirstContact_of_capped`);
* **`ae_retHist_eq_fcHist`**: almost surely, on the box `m` the retained histories are exactly CPL6's capped retained
  histories `fcHist`, and the box is read from them in the same way;
* **`measurableSet_aeSigma_inter_meetBox`**: on the box `m`, every set of `𝒦 ⊔ retSigma d P` is, up to a null set, a set
  of the capped σ-algebra `𝒦 ⊇ comap fcHist` (the hypothesis of `ae_condExp_eq_of_trace`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6

/-! ### Killing records and stopped histories -/

theorem lifeRec_eq_top_iff_of_ne_top {ζ T : ℝ≥0∞} (hT : T ≠ ⊤) : lifeRec ζ T = ⊤ ↔ T < ζ := by
  unfold lifeRec
  split_ifs with h
  · exact ⟨fun h' => absurd (h'.symm ▸ h) (by simpa using hT), fun h' => absurd h (not_le.2 h')⟩
  · exact ⟨fun _ => not_le.1 h, fun _ => rfl⟩

theorem histOf_congr {c c' : ℚ≥0 → ℂ} {T : ℝ≥0∞} (h : ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ T) → c q = c' q) :
    histOf c T = histOf c' T := by
  refine Prod.ext rfl (funext fun q => ?_)
  simp only [histOf, stopCoord]
  split_ifs with hq
  · exact h q hq
  · rfl

/-! ### First contacts of capped paths -/

section Capped

variable {γ₁ γ₂ γc₁ γc₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {m : ℝ≥0}

/-- **A first contact inside the box is the first contact of the capped paths.** -/
theorem isFirstContact_capped (hc₁ : ∀ t, γc₁ t = γ₁ (capTime m ζ₁ t)) (hc₂ : ∀ t, γc₂ t = γ₂ (capTime m ζ₂ t))
    {s₀ t₀ : ℝ≥0} (hfc : IsFirstContact γ₁ ζ₁ γ₂ ζ₂ s₀ t₀) (hs : s₀ ≤ m) (ht : t₀ ≤ m) :
    IsFirstContact γc₁ ⊤ γc₂ ⊤ s₀ t₀ := by
  have e₁ : capTime m ζ₁ s₀ = s₀ := capTime_of_le m ζ₁ (le_min hfc.1 (ENNReal.coe_le_coe.2 hs))
  have e₂ : capTime m ζ₂ t₀ = t₀ := capTime_of_le m ζ₂ (le_min hfc.2.1 (ENNReal.coe_le_coe.2 ht))
  refine ⟨le_top, le_top, by rw [hc₁, hc₂, e₁, e₂]; exact hfc.2.2.1, fun s t _ _ he => ?_⟩
  rw [hc₁, hc₂] at he
  obtain ⟨a, b⟩ := hfc.2.2.2 _ _ (capTime_le m ζ₁ s) (capTime_le m ζ₂ t) he
  exact ⟨a.trans (min_le_left _ _), b.trans (min_le_left _ _)⟩

/-- **A first contact of the capped paths inside the box, before both lifetimes, is the first contact of the paths**,
provided the paths have a first contact whenever they meet (Lemma 7.7's common first point). -/
theorem isFirstContact_of_capped (hc₁ : ∀ t, γc₁ t = γ₁ (capTime m ζ₁ t))
    (hc₂ : ∀ t, γc₂ t = γ₂ (capTime m ζ₂ t))
    (hfcu : HasContact γ₁ ζ₁ γ₂ ζ₂ → ∃ s₀ t₀ : ℝ≥0, IsFirstContact γ₁ ζ₁ γ₂ ζ₂ s₀ t₀)
    {σ₁ σ₂ : ℝ≥0} (hcfc : IsFirstContact γc₁ ⊤ γc₂ ⊤ σ₁ σ₂) (hσ₁ : σ₁ < m) (hσ₂ : σ₂ < m)
    (hζ₁ : (σ₁ : ℝ≥0∞) < ζ₁) (hζ₂ : (σ₂ : ℝ≥0∞) < ζ₂) :
    IsFirstContact γ₁ ζ₁ γ₂ ζ₂ σ₁ σ₂ := by
  have e₁ : capTime m ζ₁ σ₁ = σ₁ := capTime_of_le m ζ₁ (le_min hζ₁.le (ENNReal.coe_le_coe.2 hσ₁.le))
  have e₂ : capTime m ζ₂ σ₂ = σ₂ := capTime_of_le m ζ₂ (le_min hζ₂.le (ENNReal.coe_le_coe.2 hσ₂.le))
  have hmeet : γ₁ σ₁ = γ₂ σ₂ := by
    have := hcfc.2.2.1
    rwa [hc₁, hc₂, e₁, e₂] at this
  obtain ⟨s₀, t₀, hfc⟩ := hfcu ⟨σ₁, σ₂, hζ₁.le, hζ₂.le, hmeet⟩
  obtain ⟨hs₀, ht₀⟩ := hfc.2.2.2 σ₁ σ₂ hζ₁.le hζ₂.le hmeet
  have hc := isFirstContact_capped hc₁ hc₂ hfc (hs₀.trans hσ₁.le) (ht₀.trans hσ₂.le)
  obtain ⟨h1, h2⟩ := hcfc.2.2.2 s₀ t₀ le_top le_top hc.2.2.1
  rwa [le_antisymm hs₀ h1, le_antisymm ht₀ h2] at hfc

end Capped

/-! ### The retained histories of pair data -/

section Defs

variable {Ω : Type*} (d : PairData Ω)

open scoped Classical in
/-- The first-contact time of the first path, `⊤` off the contact event. -/
def fcTime₁ (ω : Ω) : ℝ≥0∞ := if ω ∈ d.E then (d.s₀ ω : ℝ≥0∞) else ⊤

open scoped Classical in
/-- The first-contact time of the second path, `⊤` off the contact event. -/
def fcTime₂ (ω : Ω) : ℝ≥0∞ := if ω ∈ d.E then (d.t₀ ω : ℝ≥0∞) else ⊤

/-- **The retained labelled histories at the first contact** (Lemma 7.8: "Retain both labelled selected histories"):
the two killed histories of the paths of `d`, stopped at their first contact (in full if they never meet). -/
def retHist (ω : Ω) : KHist × KHist :=
  (khistOf (pathCoord (d.η₁ ω)) (d.ζ₁ ω) (fcTime₁ d ω), khistOf (pathCoord (d.η₂ ω)) (d.ζ₂ ω) (fcTime₂ d ω))

/-- The box of recorded first contacts below `m` before both lifetimes. -/
def boxSet (m : ℝ≥0) : Set (KHist × KHist) := {y | y.1.1.1 < m ∧ y.2.1.1 < m ∧ y.1.2 = ⊤ ∧ y.2.2 = ⊤}

/-- **The meeting box `m`**: a first contact `(s₀, t₀)` with `s₀, t₀ < m` before both lifetimes, read from the
retained histories. -/
def meetBox (m : ℕ) : Set Ω := retHist d ⁻¹' boxSet m

/-- **The meeting branch**: a first contact with two nonempty continuations (the union of the boxes). -/
def meetSet : Set Ω := ⋃ m : ℕ, meetBox d m

/-- **The retained σ-algebra**: the σ-algebra of the retained histories, completed by null sets (inside `mΩ`). -/
@[instance_reducible]
def retSigma [mΩ : MeasurableSpace Ω] (P : Measure Ω) : MeasurableSpace Ω :=
  mΩ ⊓ aeSigma (MeasurableSpace.comap (retHist d) inferInstance) P

variable {d}

theorem mem_meetBox_iff {m : ℕ} {ω : Ω} : ω ∈ meetBox d m ↔
    ω ∈ d.E ∧ d.s₀ ω < m ∧ d.t₀ ω < m ∧ (d.s₀ ω : ℝ≥0∞) < d.ζ₁ ω ∧ (d.t₀ ω : ℝ≥0∞) < d.ζ₂ ω := by
  simp only [meetBox, boxSet, retHist, khistOf, histOf, mem_preimage, mem_ofPred_eq, fcTime₁, fcTime₂]
  by_cases hE : ω ∈ d.E
  · simp only [hE, ↓reduceIte, true_and, lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top]
    norm_cast
  · simp only [hE, ↓reduceIte, false_and, iff_false]
    exact fun h => absurd h.1 (by simp)

theorem mem_meetSet_iff {ω : Ω} : ω ∈ meetSet d ↔
    ω ∈ d.E ∧ (d.s₀ ω : ℝ≥0∞) < d.ζ₁ ω ∧ (d.t₀ ω : ℝ≥0∞) < d.ζ₂ ω := by
  simp only [meetSet, mem_iUnion, mem_meetBox_iff]
  constructor
  · rintro ⟨m, hE, -, -, h1, h2⟩
    exact ⟨hE, h1, h2⟩
  · rintro ⟨hE, h1, h2⟩
    obtain ⟨m, hm⟩ := exists_nat_gt (max (d.s₀ ω) (d.t₀ ω))
    exact ⟨m, hE, (le_max_left _ _).trans_lt hm, (le_max_right _ _).trans_lt hm, h1, h2⟩

theorem measurableSet_boxSet (m : ℝ≥0) : MeasurableSet (boxSet m) := by
  have h1 : Measurable fun y : KHist × KHist => y.1.1.1 := measurable_fst.comp (measurable_fst.comp measurable_fst)
  have h2 : Measurable fun y : KHist × KHist => y.2.1.1 := measurable_fst.comp (measurable_fst.comp measurable_snd)
  have h3 : Measurable fun y : KHist × KHist => y.1.2 := measurable_snd.comp measurable_fst
  have h4 : Measurable fun y : KHist × KHist => y.2.2 := measurable_snd.comp measurable_snd
  exact (measurableSet_lt h1 measurable_const).inter ((measurableSet_lt h2 measurable_const).inter
    ((h3 (measurableSet_singleton ⊤)).inter (h4 (measurableSet_singleton ⊤))))

variable [mΩ : MeasurableSpace Ω]

theorem PairData.IsMeasGood.measurable_retHist (hd : d.IsMeasGood) : Measurable (retHist d) := by
  have hE := hd.measurableSet_E
  have hτ₁ : Measurable (fcTime₁ d) := Measurable.ite hE (measurable_coe_nnreal_ennreal.comp hd.measurable_s₀)
    measurable_const
  have hτ₂ : Measurable (fcTime₂ d) := Measurable.ite hE (measurable_coe_nnreal_ennreal.comp hd.measurable_t₀)
    measurable_const
  have h₁ : Measurable fun ω => pathCoord (d.η₁ ω) := Measurable.of_eval fun q => hd.meas₁ q
  have h₂ : Measurable fun ω => pathCoord (d.η₂ ω) := Measurable.of_eval fun q => hd.meas₂ q
  have hk : Measurable fun p : (ℚ≥0 → ℂ) × ℝ≥0∞ × ℝ≥0∞ => khistOf p.1 p.2.1 p.2.2 :=
    (measurable_histOf.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).prodMk
      (measurable_lifeRec.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
  have e₁ := hk.comp (h₁.prodMk (hd.measζ₁.prodMk hτ₁))
  have e₂ := hk.comp (h₂.prodMk (hd.measζ₂.prodMk hτ₂))
  dsimp only [Function.comp_def] at e₁ e₂
  exact e₁.prodMk e₂

theorem retSigma_le (P : Measure Ω) : retSigma d P ≤ mΩ := inf_le_left

theorem PairData.IsMeasGood.comap_retHist_le_retSigma (hd : d.IsMeasGood) (P : Measure Ω) :
    MeasurableSpace.comap (retHist d) inferInstance ≤ retSigma d P :=
  le_inf hd.measurable_retHist.comap_le (le_aeSigma _ P)

theorem PairData.IsMeasGood.measurableSet_meetBox (hd : d.IsMeasGood) (P : Measure Ω) (m : ℕ) :
    MeasurableSet[retSigma d P] (meetBox d m) :=
  hd.comap_retHist_le_retSigma P _ ⟨_, measurableSet_boxSet _, rfl⟩

theorem PairData.IsMeasGood.measurableSet_meetSet (hd : d.IsMeasGood) (P : Measure Ω) :
    MeasurableSet[retSigma d P] (meetSet d) :=
  MeasurableSet.iUnion fun m => hd.measurableSet_meetBox P m

end Defs

/-! ### The retained histories on the boxes are the capped ones -/

section Compare

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : PairData Ω}

theorem lt_of_lt_cutLife {ζ : ℝ≥0∞} {m : ℝ≥0} {s : ℝ≥0} (hm : s < m) (h : (s : ℝ≥0∞) < cutLife ζ m) :
    (s : ℝ≥0∞) < ζ := by
  unfold cutLife at h
  split_ifs at h with hζ
  · exact h
  · exact (ENNReal.coe_lt_coe.2 hm).trans (not_le.1 hζ)

theorem lt_cutLife {ζ : ℝ≥0∞} {m : ℝ≥0} {s : ℝ≥0} (h : (s : ℝ≥0∞) < ζ) :
    (s : ℝ≥0∞) < cutLife ζ m := by
  unfold cutLife
  split_ifs with hζ
  · exact h
  · exact ENNReal.coe_lt_top

/-- **On the box `m`, the retained histories are the capped retained histories** (deterministic form, at a good
outcome: the paths of `d` agree with `η` on the available interval, `ηc` is the `m`-capped `η`). -/
theorem retHist_eq_fcHist_of_good (hd : d.IsMeasGood) {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hcc₁ : ∀ ω, Continuous (ηc₁ ω)) (hcc₂ : ∀ ω, Continuous (ηc₂ ω)) (m : ℕ) {ω : Ω} (hG : ω ∈ d.G)
    (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω t = η₂ ω t)
    (hc₁ : ∀ t, ηc₁ ω t = η₁ ω (capTime m (d.ζ₁ ω) t)) (hc₂ : ∀ t, ηc₂ ω t = η₂ ω (capTime m (d.ζ₂ ω) t)) :
    (ω ∈ meetBox d m ↔
        fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω ∈ boxSet m) ∧
      (ω ∈ meetBox d m →
        retHist d ω = fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω) := by
  -- the uncapped paths have a first contact whenever they meet
  have hfcu : HasContact (η₁ ω) (d.ζ₁ ω) (η₂ ω) (d.ζ₂ ω) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (d.ζ₁ ω) (η₂ ω) (d.ζ₂ ω) s₀ t₀ := fun hc => by
    obtain ⟨s₀, t₀, h, -⟩ := (hd.good ω hG).2.2.2.2.2.2 ((hasContact_congr ha₁ ha₂).2 hc)
    exact ⟨s₀, t₀, (isFirstContact_congr ha₁ ha₂).1 h⟩
  -- so do the capped ones
  have hfcc : (∃ s t : ℝ≥0, ηc₁ ω s = ηc₂ ω t) → ∃ s₀ t₀ : ℝ≥0, IsFirstContact (ηc₁ ω) ⊤ (ηc₂ ω) ⊤ s₀ t₀ := by
    rintro ⟨s, t, hst⟩
    rw [hc₁, hc₂] at hst
    obtain ⟨s₀, t₀, hfc⟩ := hfcu ⟨_, _, capTime_le _ _ s, capTime_le _ _ t, hst⟩
    obtain ⟨h1, h2⟩ := hfc.2.2.2 _ _ (capTime_le _ _ s) (capTime_le _ _ t) hst
    exact ⟨s₀, t₀, isFirstContact_capped hc₁ hc₂ hfc (h1.trans (capTime_le_cap _ _ s))
      (h2.trans (capTime_le_cap _ _ t))⟩
  obtain ⟨σ₁, σ₂, hσ⟩ := exists_isFCPair hfcc
  obtain ⟨hr₁, hr₂⟩ := fcLine_eq (η₁ := ηc₁) (η₂ := ηc₂) (hcc₁ ω) (hcc₂ ω) hσ
  have hF : fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω =
      (khistOf (pathCoord (ηc₁ ω)) (cutLife (d.ζ₁ ω) m) σ₁,
        khistOf (pathCoord (ηc₂ ω)) (cutLife (d.ζ₂ ω) m) σ₂) := by
    simp only [fcHist, hr₁, hr₂]
  -- the forward direction, with the equality of histories
  have hfwd : ω ∈ meetBox d m →
      retHist d ω = fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω := by
    intro hω
    obtain ⟨hE, hs, ht, hsζ, htζ⟩ := mem_meetBox_iff.1 hω
    have hfc := (isFirstContact_congr ha₁ ha₂).1 (hd.isFirstContact hE)
    have hcfc := isFirstContact_capped hc₁ hc₂ hfc hs.le ht.le
    obtain ⟨e₁, e₂⟩ := fcLine_eq (η₁ := ηc₁) (η₂ := ηc₂) (hcc₁ ω) (hcc₂ ω)
      (σ₁ := d.s₀ ω) (σ₂ := d.t₀ ω) (Or.inl ⟨_, _, hcfc, rfl, rfl⟩)
    have hσ₁ : σ₁ = d.s₀ ω := hr₁.symm.trans e₁
    have hσ₂ : σ₂ = d.t₀ ω := hr₂.symm.trans e₂
    rw [hF, hσ₁, hσ₂]
    simp only [retHist, fcTime₁, fcTime₂, hE, ↓reduceIte, khistOf]
    refine Prod.ext (Prod.ext (histOf_congr fun q hq => ?_) ?_) (Prod.ext (histOf_congr fun q hq => ?_) ?_)
    · have hqs : (q : ℝ≥0) ≤ d.s₀ ω := ENNReal.coe_le_coe.1 hq
      rw [pathCoord, pathCoord, ha₁ _ (hq.trans hsζ.le), hc₁, capTime_of_le]
      exact le_min (hq.trans hsζ.le) (ENNReal.coe_le_coe.2 (hqs.trans hs.le))
    · rw [(lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).2 hsζ,
        (lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).2 (lt_cutLife hsζ)]
    · have hqt : (q : ℝ≥0) ≤ d.t₀ ω := ENNReal.coe_le_coe.1 hq
      rw [pathCoord, pathCoord, ha₂ _ (hq.trans htζ.le), hc₂, capTime_of_le]
      exact le_min (hq.trans htζ.le) (ENNReal.coe_le_coe.2 (hqt.trans ht.le))
    · rw [(lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).2 htζ,
        (lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).2 (lt_cutLife htζ)]
  refine ⟨⟨fun hω => ?_, fun hb => ?_⟩, hfwd⟩
  · have hb : retHist d ω ∈ boxSet m := hω
    rwa [hfwd hω] at hb
  · rw [hF] at hb
    obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hb
    simp only [khistOf, histOf] at hb₁ hb₂ hb₃ hb₄
    rcases hσ with ⟨s₀, t₀, hcfc, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · have hs : s₀ < (m : ℝ≥0) := ENNReal.coe_lt_coe.1 hb₁
      have ht : t₀ < (m : ℝ≥0) := ENNReal.coe_lt_coe.1 hb₂
      have hsζ := lt_of_lt_cutLife hs ((lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).1 hb₃)
      have htζ := lt_of_lt_cutLife ht ((lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).1 hb₄)
      have hfc := isFirstContact_of_capped hc₁ hc₂ hfcu hcfc hs ht hsζ htζ
      obtain ⟨hE, e₁, e₂⟩ := PairData.eq_of_isFirstContact hG ((isFirstContact_congr ha₁ ha₂).2 hfc)
      exact mem_meetBox_iff.2 ⟨hE, e₁ ▸ hs, e₂ ▸ ht, e₁ ▸ hsζ, e₂ ▸ htζ⟩
    · exact absurd hb₁ (by simp)

/-- **Almost surely, on the box `m` the retained histories are the capped ones**, and the box is read from the capped
histories in the same way. -/
theorem ae_retHist_eq_fcHist (hd : d.IsMeasGood) {P : Measure Ω} {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hcc₁ : ∀ ω, Continuous (ηc₁ ω)) (hcc₂ : ∀ ω, Continuous (ηc₂ ω)) (m : ℕ)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω t = η₂ ω t)
    (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (d.ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (d.ζ₂ ω) t)) :
    ∀ᵐ ω ∂P, (retHist d ω ∈ boxSet m ↔
        fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω ∈ boxSet m) ∧
      (retHist d ω ∈ boxSet m →
        retHist d ω = fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω) := by
  filter_upwards [hae, hag₁, hag₂] with ω ⟨hG, ha₁, ha₂⟩ hc₁ hc₂
  exact retHist_eq_fcHist_of_good hd hcc₁ hcc₂ m hG ha₁ ha₂ hc₁ hc₂

end Compare

/-! ### The trace of the enlarged σ-algebra on a box -/

section TraceBox

variable {Ω : Type*} {𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The sets whose trace on `A` is, up to a null set, a set of `𝒦`. -/
@[instance_reducible]
def traceSigma (𝒦₀ : MeasurableSpace Ω) (P : @Measure Ω mΩ) (A : Set Ω)
    (hA : MeasurableSet[aeSigma 𝒦₀ P] A) : MeasurableSpace Ω where
  MeasurableSet' B := MeasurableSet[aeSigma 𝒦₀ P] (B ∩ A)
  measurableSet_empty := by
    rw [empty_inter]
    exact @MeasurableSet.empty _ (aeSigma 𝒦₀ P)
  measurableSet_compl B hB := by
    have e : Bᶜ ∩ A = A ∩ (B ∩ A)ᶜ := by ext; simp; tauto
    rw [e]
    exact @MeasurableSet.inter _ (aeSigma 𝒦₀ P) _ _ hA (@MeasurableSet.compl _ _ (aeSigma 𝒦₀ P) hB)
  measurableSet_iUnion f hf := by
    rw [iUnion_inter]
    exact @MeasurableSet.iUnion _ _ (aeSigma 𝒦₀ P) _ _ hf

/-- **The trace on a box.** If `A = Ψ⁻¹ S` and, almost surely, `Ψ` and `F` agree on `A` and read `S` in the same way,
with `comap F ≤ 𝒦`, then on `A` every set of `𝒦 ⊔ (mΩ ⊓ aeSigma (comap Ψ) P)` is, up to a null set, a `𝒦`-set. -/
theorem measurableSet_aeSigma_inter_of_ae {Y : Type*} [MeasurableSpace Y] {Ψ F : Ω → Y}
    (hF : MeasurableSpace.comap F inferInstance ≤ 𝒦) {S : Set Y} (hS : MeasurableSet S)
    (hae : ∀ᵐ ω ∂P, (Ψ ω ∈ S ↔ F ω ∈ S) ∧ (Ψ ω ∈ S → Ψ ω = F ω)) (B : Set Ω)
    (hB : MeasurableSet[𝒦 ⊔ (mΩ ⊓ aeSigma (MeasurableSpace.comap Ψ inferInstance) P)] B) :
    MeasurableSet[aeSigma 𝒦 P] (B ∩ Ψ ⁻¹' S) := by
  have hpre : ∀ C : Set Y, Ψ ⁻¹' C ∩ Ψ ⁻¹' S =ᵐ[P] F ⁻¹' (C ∩ S) := fun C => by
    filter_upwards [hae] with ω ⟨h1, h2⟩
    simp only [mem_inter_iff, mem_preimage, eq_iff_iff]
    constructor
    · rintro ⟨hC, hSΨ⟩
      exact ⟨h2 hSΨ ▸ hC, h1.1 hSΨ⟩
    · rintro ⟨hC, hSF⟩
      have hSΨ := h1.2 hSF
      exact ⟨(h2 hSΨ).symm ▸ hC, hSΨ⟩
  have hA : MeasurableSet[aeSigma 𝒦 P] (Ψ ⁻¹' S) := by
    refine ⟨F ⁻¹' S, hF _ ⟨S, hS, rfl⟩, ?_⟩
    have := hpre univ
    rwa [preimage_univ, univ_inter, univ_inter] at this
  have hle : 𝒦 ⊔ (mΩ ⊓ aeSigma (MeasurableSpace.comap Ψ inferInstance) P) ≤ traceSigma 𝒦 P (Ψ ⁻¹' S) hA := by
    refine sup_le (fun B hB => ?_) (fun B hB => ?_)
    · exact @MeasurableSet.inter _ (aeSigma 𝒦 P) _ _ (le_aeSigma 𝒦 P B hB) hA
    · obtain ⟨B', ⟨C, hC, rfl⟩, hBB'⟩ := (inf_le_right :
        mΩ ⊓ aeSigma (MeasurableSpace.comap Ψ inferInstance) P ≤ _) B hB
      refine ⟨F ⁻¹' (C ∩ S), hF _ ⟨C ∩ S, hC.inter hS, rfl⟩, ?_⟩
      exact (hBB'.inter EventuallyEqSet.rfl).trans (hpre C)
  exact hle B hB

end TraceBox

end Restart

end InteractingSLE
