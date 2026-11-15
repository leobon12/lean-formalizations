/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLuDense
import InteractingSLE.Spec.Supplement.SBLzMeas
import InteractingSLE.Spec.Supplement.SBLyPath
import InteractingSLE.Spec.Restart.ChartMeasFlow

/-!
# SB3's measurability inputs (I2), (I2′)

Packet PROVE-T14-SBLEAVES6. The stage claim and the truncation claim of SB3's induction are S1 events quantified over
the stops of the upper flow line (and over the truncations of the new piece). Their null-measurability follows from
PROVE-T14-SBLEAVES5's coded S1 relation (`Lz.S1Rel`) once every datum is read off a measurable code:

* `nullMeasurableSet_imp_isOneSided`: an S1 event restricted to a measurable event is null-measurable when, almost
  surely on the event, the path agrees up to the stop with a continuous path measurable at each time and the set has a
  measurable dense family;
* `stopSeq`, `forall_le_iff_stopSeq`: `∀ a ≤ ζ` reduces to countably many measurable stops (S1 is antitone in the stop);
* `exists_frozen_version_of_isFlowLine`: the flow line frozen at its lifetime has a version measurable at each time and
  continuous almost surely (the trace reconstructed from the driving history, `LP.drivingTrace`);
* the claims as functions of the walk's driver family (`stageClaimD`, `truncClaimD`), their null-measurability for
  drivers with regular launches at every sample (`nullMeasurableSet_claimsD`), and the passage to the a.s. regular
  staged history by changing the drivers on a null set (`nullMeasurableSet_claims`);
* **`sb3StageMeasCfStatement`**: the named input `Ly.SB3StageMeasCfStatement` holds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

universe u

namespace InteractingSLE.Theorem14.SB.LuM

open Exist.Staged Exist.StagedLaw

/-! ### S1 events on a measurable event -/

/-- **S1 events restricted to a measurable event are null-measurable** when, almost surely on the event, the path
agrees up to the stop with a continuous path `β` measurable at each time and the set has a measurable dense family. -/
theorem nullMeasurableSet_imp_isOneSided {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {G : Set Ω} (hG : MeasurableSet G) {A : Ω → Set ℂ} {β η : Ω → ℝ≥0 → ℂ} {a : Ω → ℝ≥0} {d : Ω → ℕ → ℂ}
    (hβ : ∀ t, Measurable fun ω => β ω t) (hd : Measurable d) (ha : Measurable a)
    (hrep : ∀ᵐ ω ∂P, ω ∈ G → Continuous (β ω) ∧ (∀ t ≤ a ω, β ω t = η ω t) ∧ range (d ω) ⊆ A ω ∧
      A ω ⊆ closure (range (d ω))) :
    NullMeasurableSet {ω | ω ∈ G → IsOneSided (A ω) (η ω) (a ω)} P := by
  have hZ : Measurable fun ω => ((Theorem15D5.encC (β ω), d ω), a ω) :=
    ((measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => hβ _).prodMk hd).prodMk ha
  have hS : NullMeasurableSet {ω | ∃ y, (((Theorem15D5.encC (β ω), d ω), a ω), y) ∈ Lz.S1Rel} P :=
    nullMeasurableSet_preimage_setOf_exists hZ.aemeasurable Lz.measurableSet_s1Rel
  refine (hG.compl.nullMeasurableSet.union (hG.nullMeasurableSet.inter hS)).congr ?_
  refine Filter.eventuallyEqSet_iff.mpr ?_
  filter_upwards [hrep] with ω hω
  by_cases hωG : ω ∈ G
  · obtain ⟨hc, hag, hdA, hAd⟩ := hω hωG
    have e : IsOneSided (A ω) (η ω) (a ω) ↔ ∃ y, (((Theorem15D5.encC (β ω), d ω), a ω), y) ∈ Lz.S1Rel := by
      rw [← Lz.isOneSided_iff_exists hc hdA hAd]
      exact ⟨Lz.isOneSided_congr fun t ht => (hag t ht).symm, Lz.isOneSided_congr hag⟩
    simp only [mem_union, mem_compl_iff, hωG, not_true_eq_false, false_or, mem_inter_iff, true_and,
      mem_ofPred_eq, true_imp_iff]
    exact e.symm
  · simp only [mem_union, mem_compl_iff, hωG, not_false_eq_true, true_or, false_imp_iff]

/-! ### Countably many stops -/

/-- The stops controlling `∀ a ≤ ζ`: all integers when `ζ = ∞`, the finite lifetime otherwise. -/
def stopSeq (ζ : ℝ≥0∞) (n : ℕ) : ℝ≥0 := if ζ = ⊤ then (n : ℝ≥0) else ζ.toNNReal

theorem stopSeq_le (ζ : ℝ≥0∞) (n : ℕ) : (stopSeq ζ n : ℝ≥0∞) ≤ ζ := by
  unfold stopSeq
  split_ifs with h
  · rw [h]; exact le_top
  · exact ENNReal.coe_toNNReal_le_self

/-- **`∀ a ≤ ζ` through countably many stops**, for a property antitone in the stop. -/
theorem forall_le_iff_stopSeq {ζ : ℝ≥0∞} {p : ℝ≥0 → Prop} (hp : ∀ a a', p a' → a ≤ a' → p a) :
    (∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ → p a) ↔ ∀ n : ℕ, p (stopSeq ζ n) := by
  refine ⟨fun h n => h _ (stopSeq_le ζ n), fun h a ha => ?_⟩
  by_cases hζ : ζ = ⊤
  · refine hp a _ (h ⌈a⌉₊) ?_
    simp only [stopSeq, hζ, ↓reduceIte]
    exact Nat.le_ceil a
  · refine hp a _ (h 0) ?_
    simp only [stopSeq, hζ, ↓reduceIte]
    simpa using ENNReal.toNNReal_mono hζ ha

theorem measurable_stopSeq {Ω : Type*} [MeasurableSpace Ω] {ζ : Ω → ℝ≥0∞} (hζ : Measurable ζ) (n : ℕ) :
    Measurable fun ω => stopSeq (ζ ω) n := by
  classical
  unfold stopSeq
  exact Measurable.ite (measurableSet_eq_fun hζ measurable_const) measurable_const hζ.ennreal_toNNReal

/-! ### A measurable frozen version of a flow line -/

section Flow

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- Freezing at `ζ` is continuous. -/
theorem continuous_freeze (ζ : ℝ≥0∞) : Continuous fun t : ℝ≥0 => (min (t : ℝ≥0∞) ζ).toNNReal := by
  by_cases hζ : ζ = ⊤
  · subst hζ
    have e : (fun t : ℝ≥0 => (min (t : ℝ≥0∞) ⊤).toNNReal) = fun t => t := by
      funext t
      simp
    rw [e]
    exact continuous_id'
  · have e : (fun t : ℝ≥0 => (min (t : ℝ≥0∞) ζ).toNNReal) = fun t => min t ζ.toNNReal := by
      funext t
      rw [← ENNReal.coe_toNNReal hζ, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
    rw [e]
    exact continuous_id.min continuous_const

/-- **A measurable frozen version of a flow line**: a path measurable at each time, almost surely continuous, which
agrees almost surely with the flow line on its closed available interval (the trace reconstructed from the driving
history, as in `Restart.exists_measurable_version_of_isFlowLine`, frozen at the lifetime). -/
theorem exists_frozen_version_of_isFlowLine (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∃ η' : Ω → ℝ≥0 → ℂ, (∀ t, Measurable fun ω => η' ω t) ∧
      ∀ᵐ ω ∂P, Continuous (η' ω) ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ ω → η' ω s = η ω s := by
  classical
  have hζ := Restart.measurable_lifetime_of_isFlowLine hη
  obtain ⟨_, 𝓕, W, _, _, _, -, hcoup, htr⟩ := hη
  have hW := hcoup.1.2.1
  set W' : ℝ≥0 → Ω → ℝ := fun t ω => if (t : ℝ≥0∞) < ζ ω then W t ω else 0 with hW'
  have hW'm : ∀ t, Measurable (W' t) := fun t => Restart.measurable_ite_of_adaptedBefore hW t
  have hpm : Measurable fun ω => (ζ ω, fun s => W' s ω) :=
    hζ.prodMk (measurable_pi_iff.2 fun s => hW'm s)
  refine ⟨fun ω t => (x : ℂ) + (LP.drivingTrace (ζ ω, fun s => W' s ω)).2 t, fun t => ?_, ?_⟩
  · exact measurable_const.add
      ((measurable_pi_apply t).comp (measurable_snd.comp (LP.measurable_drivingTrace.comp hpm)))
  · filter_upwards [htr, hcoup.1.2.2.2.2] with ω hω hpath
    obtain ⟨hw0, -, -, hcw, -⟩ := hpath
    have he := LP.drivingTrace_eq hω hcw hw0 (w' := fun s => W' s ω) fun r hr => by
      simp only [hW', hr, ↓reduceIte]
    rw [he]
    refine ⟨continuous_const.add (hω.2.1.comp_continuous (continuous_freeze (ζ ω)) fun t => ?_), fun s hs => ?_⟩
    · show ((min (t : ℝ≥0∞) (ζ ω)).toNNReal : ℝ≥0∞) ≤ ζ ω
      exact ENNReal.coe_toNNReal_le_self.trans (min_le_right _ _)
    · simp only [min_eq_left hs, ENNReal.toNNReal_coe]
      ring

end Flow

/-! ### Dense families of unions and of the bridge -/

/-- Dense families of two sets give one of their union. -/
theorem dense_sumElim {ι ι' : Type*} {A B : Set ℂ} {f : ι → ℂ} {g : ι' → ℂ} (hf : range f ⊆ A)
    (hA : A ⊆ closure (range f)) (hg : range g ⊆ B) (hB : B ⊆ closure (range g)) :
    range (Sum.elim f g) ⊆ A ∪ B ∧ A ∪ B ⊆ closure (range (Sum.elim f g)) := by
  rw [Set.Sum.elim_range]
  exact ⟨union_subset_union hf hg, union_subset (hA.trans (closure_mono subset_union_left))
    (hB.trans (closure_mono subset_union_right))⟩

open Classical in
/-- The dense family of the bridge `[u, 0]`: `u` and its rational points (`0` elsewhere). -/
def ufam (u : ℝ) : Option ℚ → ℂ
  | none => u
  | some q => if (q : ℝ) ∈ Icc u 0 then (q : ℂ) else 0

theorem range_ufam_subset {u : ℝ} (hu : u ≤ 0) : range (ufam u) ⊆ ((↑) : ℝ → ℂ) '' Icc u 0 := by
  rintro _ ⟨_ | q, rfl⟩
  · exact ⟨u, ⟨le_rfl, hu⟩, rfl⟩
  · simp only [ufam]
    split_ifs with h
    · exact ⟨q, h, by simp⟩
    · exact ⟨0, ⟨hu, le_rfl⟩, by simp⟩

theorem subset_closure_range_ufam {u : ℝ} (hu : u ≤ 0) :
    ((↑) : ℝ → ℂ) '' Icc u 0 ⊆ closure (range (ufam u)) := by
  rcases hu.lt_or_eq with hu' | rfl
  · rintro _ ⟨x, hx, rfl⟩
    have hxr := GW2aCont.Icc_subset_closure_rat hu' hx
    refine closure_mono ?_ (image_closure_subset_closure_image Complex.continuous_ofReal ⟨x, hxr, rfl⟩)
    rintro _ ⟨y, ⟨hy, q, rfl⟩, rfl⟩
    refine ⟨some q, ?_⟩
    simp only [ufam, hy, ↓reduceIte, Complex.ofReal_ratCast]
  · rintro _ ⟨x, hx, rfl⟩
    rw [Icc_self, mem_singleton_iff] at hx
    subst hx
    exact subset_closure ⟨none, rfl⟩

/-- An enumeration of a countable family keeps its range. -/
theorem range_comp_surj {ι : Type*} {e : ℕ → ι} (he : Function.Surjective e) (f : ι → ℂ) :
    range (f ∘ e) = range f :=
  he.range_comp f

/-! ### The claims as functions of the walk's drivers -/

section Claims

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- Instruction `j` of the lower walk with drivers `D` launches (`Lx.LowerLaunch`). -/
def launchD (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) : Prop :=
  (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (j + 1)).2.2.2.1 j ≠ none

/-- A live stage (`Lx.LowerLive`). -/
def liveD (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : Prop :=
  ∀ j < k, launchD κ b jumps D j → (D j).2 ≠ ⊤

/-- The retained lower prefix with the bridge (`lowerPrefix`). -/
def preD (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u : ℝ) : Set ℂ :=
  SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D k ∪ ((↑) : ℝ → ℂ) '' Icc u 0

/-- The stage claim at one sample, as a function of the drivers. -/
def stageClaimD (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u : ℝ)
    (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : Prop :=
  liveD κ b jumps D k → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ → IsOneSided (preD κ b jumps D k u) η a

/-- The truncation claim at one sample, as a function of the drivers. -/
def truncClaimD (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u : ℝ)
    (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : Prop :=
  liveD κ b jumps D k → launchD κ b jumps D k → ∀ d a : ℝ≥0, (d : ℝ≥0∞) ≤ (D k).2 → (a : ℝ≥0∞) ≤ ζ →
    IsOneSided (preD κ b jumps D k u ∪ ptSet κ b jumps (-(Real.pi / 2)) true D k d) η a

theorem sb3StageClaim_iff {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {ω : Ω} :
    Lx.SB3StageClaim κ b jumps E k u η ζ ω ↔
      stageClaimD κ b jumps (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k u (η ω) (ζ ω) :=
  Iff.rfl

theorem sb3TruncClaim_iff {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {ω : Ω} :
    Lx.SB3TruncClaim κ b jumps E k u η ζ ω ↔
      truncClaimD κ b jumps (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k u (η ω) (ζ ω) :=
  Iff.rfl

/-- `ptSet` grows with the truncation time. -/
theorem ptSet_mono {θ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {d d' : ℝ≥0} (h : d ≤ d') :
    ptSet κ b jumps θ right D k d ⊆ ptSet κ b jumps θ right D k d' :=
  image_mono (image_mono (Icc_subset_Icc_right h))

/-- **The stage claim through countably many stops.** -/
theorem stageClaimD_iff {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} :
    stageClaimD κ b jumps D k u η ζ ↔
      ∀ n : ℕ, liveD κ b jumps D k → IsOneSided (preD κ b jumps D k u) η (stopSeq ζ n) := by
  unfold stageClaimD
  rw [forall_le_iff_stopSeq (p := fun a => IsOneSided (preD κ b jumps D k u) η a) fun a a' h hle => h.of_le hle]
  exact ⟨fun h n hl => h hl n, fun h hl n => h n hl⟩

/-- **The truncation claim through countably many truncations and stops.** -/
theorem truncClaimD_iff {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} :
    truncClaimD κ b jumps D k u η ζ ↔
      ∀ m n : ℕ, liveD κ b jumps D k ∧ launchD κ b jumps D k →
        IsOneSided (preD κ b jumps D k u ∪ ptSet κ b jumps (-(Real.pi / 2)) true D k (stopSeq (D k).2 m)) η
          (stopSeq ζ n) := by
  have hQ : ∀ d d' a a' : ℝ≥0, IsOneSided (preD κ b jumps D k u ∪
      ptSet κ b jumps (-(Real.pi / 2)) true D k d') η a' → d ≤ d' → a ≤ a' →
      IsOneSided (preD κ b jumps D k u ∪ ptSet κ b jumps (-(Real.pi / 2)) true D k d) η a :=
    fun d d' a a' h hd ha => (h.of_le ha).mono (union_subset_union_right _ (ptSet_mono hd))
  have hd : ∀ d : ℝ≥0, (∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ →
      IsOneSided (preD κ b jumps D k u ∪ ptSet κ b jumps (-(Real.pi / 2)) true D k d) η a) ↔
      ∀ n : ℕ, IsOneSided (preD κ b jumps D k u ∪ ptSet κ b jumps (-(Real.pi / 2)) true D k d) η
        (stopSeq ζ n) := fun d =>
    forall_le_iff_stopSeq fun a a' h hle => hQ d d a a' h le_rfl hle
  unfold truncClaimD
  have e := forall_le_iff_stopSeq (ζ := (D k).2) (p := fun d => ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ →
      IsOneSided (preD κ b jumps D k u ∪ ptSet κ b jumps (-(Real.pi / 2)) true D k d) η a)
    fun d d' h hle a ha => hQ d d' a a (h a ha) hle le_rfl
  constructor
  · intro h m n hl
    exact (hd _).1 ((e.1 fun d hd' a ha => h hl.1 hl.2 d a hd' ha) m) n
  · intro h hl hL d a hd' ha
    exact e.2 (fun m => (hd _).2 fun n => h m n ⟨hl, hL⟩) d hd' a ha

end Claims

/-! ### Null-measurability for drivers with regular launches -/

section MeasD

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P]

/-- The dense family of the retained lower prefix with the bridge. -/
def lfam (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u : ℝ) :
    PIdx ⊕ Option ℚ → ℂ :=
  Sum.elim (pfam κ b jumps (-(Real.pi / 2)) true D k) (ufam u)

theorem dense_lfam {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D)
    (hreg : ∀ j, IsRegularDriver (D j)) (k : ℕ) {u : ℝ} (hu : u ≤ 0) :
    range (lfam κ b jumps D k u) ⊆ preD κ b jumps D k u ∧
      preD κ b jumps D k u ⊆ closure (range (lfam κ b jumps D k u)) :=
  dense_sumElim (by rintro _ ⟨i, rfl⟩; exact pfam_mem hP hreg k i) (subset_closure_range_pfam hP hreg k)
    (range_ufam_subset hu) (subset_closure_range_ufam hu)

theorem launchD_measurableSet (hb : IsPiecewiseConstantBoundaryData b jumps) {F : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hF : ∀ j, Measurable (F j)) (hreg : ∀ j ω, IsRegularDriver (F j ω)) (j : ℕ) :
    MeasurableSet {ω | launchD κ b jumps (fun j => F j ω) j} :=
  (runMeasStatement κ b jumps hb _ F hF hreg j).1

theorem liveD_measurableSet (hb : IsPiecewiseConstantBoundaryData b jumps) {F : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hF : ∀ j, Measurable (F j)) (hreg : ∀ j ω, IsRegularDriver (F j ω)) (k : ℕ) :
    MeasurableSet {ω | liveD κ b jumps (fun j => F j ω) k} := by
  have e : {ω | liveD κ b jumps (fun j => F j ω) k} = ⋂ j ∈ Finset.range k,
      ({ω | launchD κ b jumps (fun j => F j ω) j}ᶜ ∪ {ω | (F j ω).2 = ⊤}ᶜ) := by
    ext ω
    simp only [liveD, mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [e]
  exact MeasurableSet.biInter (Finset.countable_toSet _) fun j _ =>
    (launchD_measurableSet hb hF hreg j).compl.union
      (measurableSet_eq_fun (measurable_snd.comp (hF j)) measurable_const).compl

/-- **SB3's two claims are null-measurable for drivers with regular launches at every sample**, given a version of
the flow line measurable at each time and almost surely continuous and equal to it up to its lifetime. -/
theorem nullMeasurableSet_claimsD (hb : IsPiecewiseConstantBoundaryData b jumps)
    {F : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hF : ∀ j, Measurable (F j)) (hreg : ∀ j ω, IsRegularDriver (F j ω))
    (hP : ∀ ω, RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) fun j => F j ω)
    {u : ℝ} (hu : u ≤ 0) {η η' : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hζ : Measurable ζ)
    (hη'm : ∀ t, Measurable fun ω => η' ω t)
    (hη' : ∀ᵐ ω ∂P, Continuous (η' ω) ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ ω → η' ω s = η ω s) (k : ℕ) :
    NullMeasurableSet {ω | stageClaimD κ b jumps (fun j => F j ω) k u (η ω) (ζ ω)} P ∧
      NullMeasurableSet {ω | truncClaimD κ b jumps (fun j => F j ω) k u (η ω) (ζ ω)} P := by
  have hLive := liveD_measurableSet (κ := κ) hb hF hreg k
  have hLaunch := launchD_measurableSet (κ := κ) hb hF hreg k
  have hregω : ∀ ω j, IsRegularDriver (F j ω) := fun ω j => hreg j ω
  -- the prefix family
  obtain ⟨e₁, he₁⟩ := exists_surjective_nat (PIdx ⊕ Option ℚ)
  have hlm : ∀ i, Measurable fun ω => lfam κ b jumps (fun j => F j ω) k u i := by
    rintro (i | i)
    · exact measurable_pfam hb hF hreg hP k i
    · exact measurable_const
  have hd₁ : Measurable fun ω => lfam κ b jumps (fun j => F j ω) k u ∘ e₁ :=
    measurable_pi_iff.2 fun n => hlm (e₁ n)
  have hstop : ∀ n, ∀ᵐ ω ∂P, Continuous (η' ω) ∧ (∀ t ≤ stopSeq (ζ ω) n, η' ω t = η ω t) := fun n => by
    filter_upwards [hη'] with ω ⟨hc, he⟩
    exact ⟨hc, fun t ht => he t ((ENNReal.coe_le_coe.2 ht).trans (stopSeq_le _ n))⟩
  constructor
  · have e : {ω | stageClaimD κ b jumps (fun j => F j ω) k u (η ω) (ζ ω)} = ⋂ n : ℕ,
        {ω | ω ∈ {ω | liveD κ b jumps (fun j => F j ω) k} →
          IsOneSided (preD κ b jumps (fun j => F j ω) k u) (η ω) (stopSeq (ζ ω) n)} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter]
      exact stageClaimD_iff
    rw [e]
    refine NullMeasurableSet.iInter fun n => nullMeasurableSet_imp_isOneSided hLive hη'm hd₁
      (measurable_stopSeq hζ n) ?_
    filter_upwards [hstop n] with ω ⟨hc, he⟩ _
    obtain ⟨h1, h2⟩ := dense_lfam (hP ω) (hregω ω) k hu
    rw [range_comp_surj he₁]
    exact ⟨hc, he, h1, h2⟩
  · obtain ⟨e₂, he₂⟩ := exists_surjective_nat ((PIdx ⊕ Option ℚ) ⊕ Option ℚ)
    have e : {ω | truncClaimD κ b jumps (fun j => F j ω) k u (η ω) (ζ ω)} = ⋂ m : ℕ, ⋂ n : ℕ,
        {ω | ω ∈ {ω | liveD κ b jumps (fun j => F j ω) k} ∩ {ω | launchD κ b jumps (fun j => F j ω) k} →
          IsOneSided (preD κ b jumps (fun j => F j ω) k u ∪
            ptSet κ b jumps (-(Real.pi / 2)) true (fun j => F j ω) k (stopSeq (F k ω).2 m)) (η ω)
            (stopSeq (ζ ω) n)} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff]
      exact truncClaimD_iff
    rw [e]
    refine NullMeasurableSet.iInter fun m => NullMeasurableSet.iInter fun n => ?_
    have hdm : Measurable fun ω => stopSeq (F k ω).2 m := measurable_stopSeq (measurable_snd.comp (hF k)) m
    have htm : ∀ i, Measurable fun ω => Sum.elim (lfam κ b jumps (fun j => F j ω) k u)
        (tfam κ b jumps (-(Real.pi / 2)) true (fun j => F j ω) k (stopSeq (F k ω).2 m)) i := by
      rintro (i | i)
      · exact hlm i
      · exact measurable_tfam hb hF hreg hP k hdm i
    refine nullMeasurableSet_imp_isOneSided (hLive.inter hLaunch) hη'm
      (d := fun ω => Sum.elim (lfam κ b jumps (fun j => F j ω) k u)
        (tfam κ b jumps (-(Real.pi / 2)) true (fun j => F j ω) k (stopSeq (F k ω).2 m)) ∘ e₂)
      (measurable_pi_iff.2 fun j => htm (e₂ j)) (measurable_stopSeq hζ n) ?_
    filter_upwards [hstop n] with ω ⟨hc, he⟩ hG
    obtain ⟨h1, h2⟩ := dense_lfam (hP ω) (hregω ω) k hu
    obtain ⟨h3, h4⟩ := dense_sumElim h1 h2
      (by rintro _ ⟨i, rfl⟩; exact tfam_mem (hP ω) (hregω ω) hG.2 (stopSeq_le _ m) i)
      (ptSet_subset_closure (hP ω) (hregω ω) hG.2 (stopSeq_le _ m))
    rw [range_comp_surj he₂]
    exact ⟨hc, he, h3, h4⟩

end MeasD

/-! ### From the almost surely regular staged history -/

section Transfer

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The constant driver with zero lifetime (its piece is the root alone). -/
def zeroDrv0 : (ℝ≥0 → ℝ) × ℝ≥0∞ := (fun _ => 0, 0)

theorem isRegularDriver_zeroDrv0 : IsRegularDriver zeroDrv0 :=
  ⟨continuousOn_const, rfl, fun _ _ => rfl, fun _ hpos => absurd hpos (lt_irrefl 0)⟩

theorem pieceRegular_zeroDrv0 (t : ℝ≥0∞) : GW1P.PieceRegular zeroDrv0.1 (min t zeroDrv0.2) := by
  have e : min t zeroDrv0.2 = 0 := min_eq_right zero_le
  rw [e]
  refine ⟨rfl, continuousOn_const, fun _ => 0, ⟨rfl, continuousOn_const, fun s hs => ?_⟩, fun h => ?_⟩
  · exact absurd hs (not_lt.2 zero_le)
  · exact absurd h ENNReal.zero_ne_top

/-- **SB3's two claims are null-measurable** for a measurable staged lower walk, regular at every sample as a driver
and almost surely with regular launched pieces (`StagedPiecesRegular`), and a flow line from `u ≤ 0`: the drivers are
changed on a null set into drivers with regular launches at every sample (`nullMeasurableSet_claimsD`). -/
theorem nullMeasurableSet_claims {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (hb : IsPiecewiseConstantBoundaryData b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ j, Measurable (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j))
    (hR : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hreg : ∀ j ω, IsRegularDriver (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω))
    {u ψ : ℝ} (hu : u ≤ 0) {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps u ψ P h η ζ) (k : ℕ) :
    NullMeasurableSet {ω | Lx.SB3StageClaim κ b jumps E k u η ζ ω} P ∧
      NullMeasurableSet {ω | Lx.SB3TruncClaim κ b jumps E k u η ζ ω} P := by
  classical
  obtain ⟨M, hMae, hMm, hMreg⟩ := Eventually.exists_measurable_mem hR
  set F : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j ω =>
    if ω ∈ M then E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω else zeroDrv0 with hFdef
  have hF : ∀ j, Measurable (F j) := fun j => Measurable.ite hMm (hE j) measurable_const
  have hregF : ∀ j ω, IsRegularDriver (F j ω) := fun j ω => by
    by_cases hω : ω ∈ M
    · simp only [hFdef, hω, ↓reduceIte]; exact hreg j ω
    · simp only [hFdef, hω, ↓reduceIte]; exact isRegularDriver_zeroDrv0
  have hEq : ∀ ω ∈ M, (fun j => F j ω) = fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω :=
    fun ω hω => funext fun j => by simp only [hFdef, hω, ↓reduceIte]
  have hPF : ∀ ω, RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) fun j => F j ω := by
    intro ω
    by_cases hω : ω ∈ M
    · rw [hEq ω hω]
      intro j c θ hl
      obtain ⟨hi, -, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ _ hl
      exact hMreg ω hω j θ _ c hi hl
    · have e : (fun j => F j ω) = fun _ => zeroDrv0 := funext fun j => by simp only [hFdef, hω, ↓reduceIte]
      rw [e]
      intro j c θ _
      exact pieceRegular_zeroDrv0 _
  obtain ⟨η', hη'm, hη'⟩ := exists_frozen_version_of_isFlowLine hη
  have hζ := Restart.measurable_lifetime_of_isFlowLine hη
  obtain ⟨h1, h2⟩ := nullMeasurableSet_claimsD (P := P) hb hF hregF hPF hu hζ hη'm hη' k
  constructor
  · refine h1.congr ?_
    filter_upwards [hMae] with ω hω
    show stageClaimD κ b jumps (fun j => F j ω) k u (η ω) (ζ ω) = Lx.SB3StageClaim κ b jumps E k u η ζ ω
    rw [hEq ω hω]
    rfl
  · refine h2.congr ?_
    filter_upwards [hMae] with ω hω
    show truncClaimD κ b jumps (fun j => F j ω) k u (η ω) (ζ ω) = Lx.SB3TruncClaim κ b jumps E k u η ζ ω
    rw [hEq ω hω]
    rfl

end Transfer

/-! ### The named inputs -/

/-- **SB3's measurability inputs (I2), (I2′) in the counterflow setting hold** (`Ly.SB3StageMeasCfStatement`). -/
theorem sb3StageMeasCfStatement : Ly.SB3StageMeasCfStatement.{u} := by
  intro κ _ _ b jumps hb Ω _ _ P _ h _ _ _ _ _ E hE hR hreg u ψ hu _ _ _ η ζ hη _
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  exact ⟨fun k => (nullMeasurableSet_claims hb (hE _ hspec).1 (hR _ hspec) (hreg _) hu hη k).1,
    fun k => (nullMeasurableSet_claims hb (hE _ hspec).1 (hR _ hspec) (hreg _) hu hη k).2⟩

end InteractingSLE.Theorem14.SB.LuM
