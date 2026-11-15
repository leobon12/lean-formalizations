/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw2Drv
import InteractingSLE.Spec.Exist.StagedLawPast

/-!
# Measurable random states of a staged run

Packet PROVE-STAGEDLAW2. A random state `S : Ω → ExplState` is **measurable** (`IsMeasState`) when its status has
measurable fibres, its current point, angle and records are measurable, the forward chart map is measurable at every
point, the chart sends real points to real points, and a measurable event `K` splits `Ω` into constant charts (on
the real line) and charts with a good profile on both sides of the records (`IsGoodProfile`: the chart is
continuous, strictly increasing and unbounded on `(recR, ∞)` and, reflected, on `(−∞, recL)`).

This file proves the closure properties that do not involve a Loewner stage: the initial state, piecewise
combination over measurable events and over the status, status changes, the move to the target and the move along a
connector to a point taken from a fixed finite set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged

/-! ### Accessors and the chart profile -/

/-- The chart of a state. -/
abbrev stChart (s : ExplState) : Chart := s.2.2.2.2.1
/-- The status of a state. -/
abbrev stStatus (s : ExplState) : ExplStatus := s.2.2.2.2.2.1
/-- The current point of a state. -/
abbrev stPt (s : ExplState) : ℝ := s.2.2.2.2.2.2.1
/-- The angle of a state. -/
abbrev stAngle (s : ExplState) : ℝ := s.2.2.2.2.2.2.2.1
/-- The right record of a state. -/
abbrev stRecR (s : ExplState) : ℝ := s.2.2.2.2.2.2.2.2.1
/-- The left record of a state. -/
abbrev stRecL (s : ExplState) : ℝ := s.2.2.2.2.2.2.2.2.2

/-- The right real profile of a chart. -/
def rProf (c : Chart) : ℝ → ℝ := fun x => (c.1 x).re

/-- The left real profile of a chart, reflected (`x ↦ −Re c(−x)`). -/
def lProf (c : Chart) : ℝ → ℝ := fun x => -(c.1 ((-x : ℝ) : ℂ)).re

/-- The chart sends real points to real points. -/
def IsRealChart (c : Chart) : Prop := ∀ x : ℝ, (c.1 x).im = 0

/-- The chart is constant on the real line. -/
def IsConstChart (c : Chart) : Prop := ∀ x : ℝ, c.1 x = c.1 0

/-- **A good profile** on both sides of the records. -/
def IsGoodProfile (s : ExplState) : Prop :=
  RightGood (rProf (stChart s)) (stRecR s) ∧ RightGood (lProf (stChart s)) (-stRecL s)

theorem IsRealChart.eq_ofReal {c : Chart} (hc : IsRealChart c) (x : ℝ) : c.1 x = (rProf c x : ℂ) :=
  Complex.ext (by simp [rProf]) (by simp [hc x])

/-- **A measurable random state.** -/
def IsMeasState {Ω : Type*} [MeasurableSpace Ω] (S : Ω → ExplState) : Prop :=
  (∀ st : ExplStatus, MeasurableSet {ω | stStatus (S ω) = st}) ∧ Measurable (fun ω => stPt (S ω)) ∧
    Measurable (fun ω => stAngle (S ω)) ∧ Measurable (fun ω => stRecR (S ω)) ∧
    Measurable (fun ω => stRecL (S ω)) ∧ (∀ z : ℂ, Measurable fun ω => (stChart (S ω)).1 z) ∧
    (∀ ω, IsRealChart (stChart (S ω))) ∧
    ∃ K : Set Ω, MeasurableSet K ∧ (∀ ω ∈ K, IsConstChart (stChart (S ω))) ∧ ∀ ω ∉ K, IsGoodProfile (S ω)

section Generic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Measurability through a finite-valued point**: if `x ω` lies in a fixed finite set with measurable fibres,
`ω ↦ g (x ω) ω` is measurable when each `g c` is. -/
theorem measurable_finite_choice {β : Type*} [MeasurableSpace β] (F : Finset ℝ) {x : Ω → ℝ}
    (hx : ∀ ω, x ω ∈ F) (hxm : ∀ c, MeasurableSet {ω | x ω = c}) {g : ℝ → Ω → β} (hg : ∀ c, Measurable (g c)) :
    Measurable fun ω => g (x ω) ω := by
  intro B hB
  have e : (fun ω => g (x ω) ω) ⁻¹' B = ⋃ c ∈ F, {ω | x ω = c} ∩ g c ⁻¹' B := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_prop]
    exact ⟨fun h => ⟨x ω, hx ω, rfl, h⟩, fun ⟨c, _, hc, h⟩ => hc ▸ h⟩
  rw [e]
  exact MeasurableSet.biUnion F.countable_toSet fun c _ => (hxm c).inter (hg c hB)

/-- **Piecewise combination** of measurable random states over a measurable event. -/
theorem IsMeasState.piecewise {S₁ S₂ : Ω → ExplState} (h₁ : IsMeasState S₁) (h₂ : IsMeasState S₂) {A : Set Ω}
    (hA : MeasurableSet A) [∀ ω, Decidable (ω ∈ A)] : IsMeasState (A.piecewise S₁ S₂) := by
  obtain ⟨hs₁, hp₁, ha₁, hR₁, hL₁, hc₁, hr₁, K₁, hK₁, hK₁c, hK₁g⟩ := h₁
  obtain ⟨hs₂, hp₂, ha₂, hR₂, hL₂, hc₂, hr₂, K₂, hK₂, hK₂c, hK₂g⟩ := h₂
  have hpw : ∀ {β : Type} [MeasurableSpace β] (g : ExplState → β), Measurable (fun ω => g (S₁ ω)) →
      Measurable (fun ω => g (S₂ ω)) → Measurable fun ω => g (A.piecewise S₁ S₂ ω) := fun g h1 h2 => by
    have e : (fun ω => g (A.piecewise S₁ S₂ ω)) = A.piecewise (fun ω => g (S₁ ω)) fun ω => g (S₂ ω) := by
      funext ω; by_cases hω : ω ∈ A <;> simp [hω]
    rw [e]; exact h1.piecewise hA h2
  refine ⟨fun st => ?_, hpw _ hp₁ hp₂, hpw _ ha₁ ha₂, hpw _ hR₁ hR₂, hpw _ hL₁ hL₂,
    fun z => hpw (fun s => (stChart s).1 z) (hc₁ z) (hc₂ z),
    fun ω => ?_, (A ∩ K₁) ∪ (Aᶜ ∩ K₂), (hA.inter hK₁).union (hA.compl.inter hK₂), fun ω hω => ?_, fun ω hω => ?_⟩
  · have e : {ω | stStatus (A.piecewise S₁ S₂ ω) = st} =
        (A ∩ {ω | stStatus (S₁ ω) = st}) ∪ (Aᶜ ∩ {ω | stStatus (S₂ ω) = st}) := by
      ext ω; by_cases hω : ω ∈ A <;> simp [hω]
    rw [e]; exact (hA.inter (hs₁ st)).union (hA.compl.inter (hs₂ st))
  · by_cases hω : ω ∈ A
    · rw [piecewise_eq_of_mem _ _ _ hω]; exact hr₁ ω
    · rw [piecewise_eq_of_notMem _ _ _ hω]; exact hr₂ ω
  · rcases hω with ⟨hωA, hωK⟩ | ⟨hωA, hωK⟩
    · rw [piecewise_eq_of_mem _ _ _ hωA]; exact hK₁c ω hωK
    · rw [piecewise_eq_of_notMem _ _ _ hωA]; exact hK₂c ω hωK
  · by_cases hωA : ω ∈ A
    · rw [piecewise_eq_of_mem _ _ _ hωA]; exact hK₁g ω fun h => hω (Or.inl ⟨hωA, h⟩)
    · rw [piecewise_eq_of_notMem _ _ _ hωA]; exact hK₂g ω fun h => hω (Or.inr ⟨hωA, h⟩)

/-- Agreement with a measurable random state on a measurable event, and with another one off it. -/
theorem IsMeasState.of_cases {S S₁ S₂ : Ω → ExplState} (h₁ : IsMeasState S₁) (h₂ : IsMeasState S₂) {A : Set Ω}
    (hA : MeasurableSet A) (he₁ : ∀ ω ∈ A, S ω = S₁ ω) (he₂ : ∀ ω ∉ A, S ω = S₂ ω) : IsMeasState S := by
  classical
  have e : S = A.piecewise S₁ S₂ := by
    funext ω
    by_cases hω : ω ∈ A
    · rw [piecewise_eq_of_mem _ _ _ hω, he₁ ω hω]
    · rw [piecewise_eq_of_notMem _ _ _ hω, he₂ ω hω]
  rw [e]
  exact h₁.piecewise h₂ hA

/-- **A state that only changes the status** (to a measurable new status). -/
theorem IsMeasState.of_status {S S' : Ω → ExplState} (h : IsMeasState S)
    (hst : ∀ st : ExplStatus, MeasurableSet {ω | stStatus (S' ω) = st}) (hc : ∀ ω, stChart (S' ω) = stChart (S ω))
    (hp : ∀ ω, stPt (S' ω) = stPt (S ω)) (ha : ∀ ω, stAngle (S' ω) = stAngle (S ω))
    (hR : ∀ ω, stRecR (S' ω) = stRecR (S ω)) (hL : ∀ ω, stRecL (S' ω) = stRecL (S ω)) : IsMeasState S' := by
  obtain ⟨-, hp₁, ha₁, hR₁, hL₁, hc₁, hr₁, K, hK, hKc, hKg⟩ := h
  refine ⟨hst, ?_, ?_, ?_, ?_, fun z => ?_, fun ω => ?_, K, hK, fun ω hω => ?_, fun ω hω => ?_⟩
  · simp_rw [hp]; exact hp₁
  · simp_rw [ha]; exact ha₁
  · simp_rw [hR]; exact hR₁
  · simp_rw [hL]; exact hL₁
  · simp_rw [hc]; exact hc₁ z
  · rw [hc]; exact hr₁ ω
  · rw [hc]; exact hKc ω hω
  · have := hKg ω hω
    unfold IsGoodProfile at this ⊢
    rw [hc, hR, hL]; exact this

theorem measurableSet_status_const (st₀ : ExplStatus) (st : ExplStatus) :
    MeasurableSet {_ω : Ω | st₀ = st} := MeasurableSet.const _

/-- **Splitting by the status**: a random state agreeing on each status fibre of `S` with a measurable random state
is measurable. -/
theorem IsMeasState.of_status_cases {S S' : Ω → ExplState} (hS : ∀ st, MeasurableSet {ω | stStatus (S ω) = st})
    {T : ExplStatus → Ω → ExplState} (hT : ∀ st, IsMeasState (T st))
    (he : ∀ ω, S' ω = T (stStatus (S ω)) ω) : IsMeasState S' := by
  classical
  have hcomp : ∀ {β : Type} [MeasurableSpace β] (g : ExplState → β), (∀ st, Measurable fun ω => g (T st ω)) →
      Measurable fun ω => g (S' ω) := fun g hg B hB => by
    have e : (fun ω => g (S' ω)) ⁻¹' B =
        ⋃ st : ExplStatus, {ω | stStatus (S ω) = st} ∩ (fun ω => g (T st ω)) ⁻¹' B := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq, he ω]
      exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨st, hst, h⟩ => hst ▸ h⟩
    rw [e]
    exact MeasurableSet.iUnion fun st => (hS st).inter (hg st hB)
  choose K hK hKc hKg using fun st => (hT st).2.2.2.2.2.2.2
  refine ⟨fun st' => ?_, hcomp _ fun st => (hT st).2.1, hcomp _ fun st => (hT st).2.2.1,
    hcomp _ fun st => (hT st).2.2.2.1, hcomp _ fun st => (hT st).2.2.2.2.1,
    fun z => hcomp (fun s => (stChart s).1 z) fun st => (hT st).2.2.2.2.2.1 z,
    fun ω => by rw [he ω]; exact (hT _).2.2.2.2.2.2.1 ω,
    ⋃ st, {ω | stStatus (S ω) = st} ∩ K st, MeasurableSet.iUnion fun st => (hS st).inter (hK st),
    fun ω hω => ?_, fun ω hω => ?_⟩
  · have e : {ω | stStatus (S' ω) = st'} =
        ⋃ st : ExplStatus, {ω | stStatus (S ω) = st} ∩ {ω | stStatus (T st ω) = st'} := by
      ext ω
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, he ω]
      exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨st, hst, h⟩ => hst ▸ h⟩
    rw [e]
    exact MeasurableSet.iUnion fun st => (hS st).inter ((hT st).1 st')
  · obtain ⟨st, hst, hωK⟩ := mem_iUnion.1 hω
    rw [he ω, show stStatus (S ω) = st from hst]
    exact hKc st ω hωK
  · rw [he ω]
    exact hKg _ ω fun h => hω (mem_iUnion.2 ⟨_, rfl, h⟩)

end Generic


/-- **Splitting a map by the status.** -/
theorem measurable_status_cases {Ω : Type*} [MeasurableSpace Ω] {S : Ω → ExplState}
    (hS : ∀ st, MeasurableSet {ω | stStatus (S ω) = st}) {β : Type*} [MeasurableSpace β]
    {g : ExplStatus → Ω → β} (hg : ∀ st, Measurable (g st)) : Measurable fun ω => g (stStatus (S ω)) ω := by
  intro B hB
  have e : (fun ω => g (stStatus (S ω)) ω) ⁻¹' B = ⋃ st : ExplStatus, {ω | stStatus (S ω) = st} ∩ g st ⁻¹' B := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨st, hst, h⟩ => hst ▸ h⟩
  rw [e]
  exact MeasurableSet.iUnion fun st => (hS st).inter (hg st hB)

/-! ### Boundary data -/

/-- A function continuous off a finite set is measurable. -/
theorem measurable_of_continuousOn_compl_finset {f : ℝ → ℝ} (J : Finset ℝ) (hf : ContinuousOn f (↑J)ᶜ) :
    Measurable f := by
  refine measurable_of_isOpen fun V hV => ?_
  have e : f ⁻¹' V = ((↑J)ᶜ ∩ f ⁻¹' V) ∪ (f ⁻¹' V ∩ ↑J) := by
    ext y; by_cases hy : y ∈ (J : Set ℝ) <;> simp [hy]
  rw [e]
  exact (hf.isOpen_inter_preimage J.finite_toSet.isClosed.isOpen_compl hV).measurableSet.union
    (J.finite_toSet.subset inter_subset_right).measurableSet

theorem measurable_leftLim_of_pcbd {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) :
    Measurable (PiecewiseConstantBoundaryData.leftLim b) := by
  refine measurable_of_continuousOn_compl_finset J fun y hy => ?_
  have hev : ∀ᶠ z in 𝓝 y, PiecewiseConstantBoundaryData.leftLim b z = b y := by
    filter_upwards [(J.finite_toSet.isClosed.isOpen_compl).mem_nhds hy, hb y hy] with z hz hbz
    rw [leftLim_eq_of_notMem hb hz, hbz]
  have hy' := hev.self_of_nhds
  exact (continuousAt_const.congr (hev.mono fun z hz => (hz.trans hy'.symm).symm)).continuousWithinAt

theorem measurable_rightLim_of_pcbd {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) :
    Measurable (PiecewiseConstantBoundaryData.rightLim b) := by
  refine measurable_of_continuousOn_compl_finset J fun y hy => ?_
  have hev : ∀ᶠ z in 𝓝 y, PiecewiseConstantBoundaryData.rightLim b z = b y := by
    filter_upwards [(J.finite_toSet.isClosed.isOpen_compl).mem_nhds hy, hb y hy] with z hz hbz
    rw [rightLim_eq_of_notMem hb hz, hbz]
  have hy' := hev.self_of_nhds
  exact (continuousAt_const.congr (hev.mono fun z hz => (hz.trans hy'.symm).symm)).continuousWithinAt

/-! ### Basic transitions -/

section Basic

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurableSet_status_of_const {S' : Ω → ExplState} {st₀ : ExplStatus} (h : ∀ ω, stStatus (S' ω) = st₀)
    (st : ExplStatus) : MeasurableSet {ω | stStatus (S' ω) = st} := by
  simp_rw [h]; exact MeasurableSet.const _

theorem rightGood_add_const (a c : ℝ) : RightGood (fun x => x + c) a :=
  ⟨fun x _ y _ hxy => by simp only; linarith, (continuous_id.add continuous_const).continuousOn,
    fun M => ⟨max (a + 1) (M - c + 1), by linarith [le_max_left (a + 1) (M - c + 1)],
      by linarith [le_max_right (a + 1) (M - c + 1)]⟩⟩

/-- **The initial state is measurable.** -/
theorem isMeasState_init (x₀ : ℝ) : IsMeasState (fun _ : Ω => ExplState.init x₀) := by
  refine ⟨fun st => MeasurableSet.const _, measurable_const, measurable_const, measurable_const, measurable_const,
    fun z => measurable_const, fun ω x => ?_, ∅, MeasurableSet.empty, fun ω h => absurd h (notMem_empty ω),
    fun ω _ => ⟨?_, ?_⟩⟩
  · simp [ExplState.init, Chart.recenter, Chart.id]
  · refine (rightGood_add_const x₀ (-x₀)).congr fun x _ => ?_
    simp [ExplState.init, Chart.recenter, Chart.id, rProf, sub_eq_add_neg]
  · refine (rightGood_add_const (-x₀) x₀).congr fun x _ => ?_
    simp [ExplState.init, Chart.recenter, Chart.id, lProf, add_comm]

/-- **Setting the status to dead.** -/
theorem IsMeasState.setDead {S : Ω → ExplState} (h : IsMeasState S) : IsMeasState fun ω => setDead (S ω) :=
  h.of_status (measurableSet_status_of_const fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

/-- **Following the boundary to the target.** -/
theorem IsMeasState.moveToEnd {S : Ω → ExplState} (h : IsMeasState S) (right : Bool) :
    IsMeasState fun ω => ExplState.moveToEnd (S ω) right :=
  h.of_status (measurableSet_status_of_const fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

/-- **Moving along a connector to a point from a fixed finite set.** -/
theorem IsMeasState.moveAlong {S : Ω → ExplState} (h : IsMeasState S) (right : Bool) (F : Finset ℝ)
    {x : Ω → ℝ} (hx : ∀ ω, x ω ∈ F) (hxm : ∀ c, MeasurableSet {ω | x ω = c}) (am : Bool) :
    IsMeasState fun ω => ExplState.moveAlong (S ω) right (x ω) am := by
  obtain ⟨-, hp, ha, hR, hL, hc, hr, K, hK, hKc, hKg⟩ := h
  have hxmeas : Measurable x := measurable_finite_choice F hx hxm (g := fun c _ => c) fun _ => measurable_const
  have hcx : Measurable fun ω => ((stChart (S ω)).1 (x ω)).re :=
    measurable_finite_choice F hx hxm (g := fun c ω => ((stChart (S ω)).1 c).re)
      fun c => Complex.measurable_re.comp (hc c)
  refine ⟨measurableSet_status_of_const fun _ => rfl, hxmeas, ha, ?_, ?_, fun z => ?_, fun ω y => ?_, K, hK,
    fun ω hω y => ?_, fun ω hω => ⟨?_, ?_⟩⟩
  · cases right
    · exact hR
    · exact hR.max hxmeas
  · cases right
    · exact hL.min hxmeas
    · exact hL
  · exact (hc z).sub (Complex.measurable_ofReal.comp hcx)
  · show ((stChart (S ω)).1 y - (((stChart (S ω)).1 (x ω)).re : ℂ)).im = 0
    rw [Complex.sub_im, hr ω y, Complex.ofReal_im, sub_zero]
  · show (stChart (S ω)).1 y - (((stChart (S ω)).1 (x ω)).re : ℂ) =
      (stChart (S ω)).1 ((0 : ℝ) : ℂ) - (((stChart (S ω)).1 (x ω)).re : ℂ)
    rw [hKc ω hω y, Complex.ofReal_zero]
  · obtain ⟨hgR, -⟩ := hKg ω hω
    have h1 := hgR.sub_const ((stChart (S ω)).1 (x ω)).re
    cases right
    · exact h1.congr fun y _ => by simp [rProf, ExplState.moveAlong, Chart.recenter]
    · exact (h1.mono_of_le (le_max_left _ _)).congr fun y _ => by
        simp [rProf, ExplState.moveAlong, Chart.recenter]
  · obtain ⟨-, hgL⟩ := hKg ω hω
    have h1 := hgL.sub_const (-((stChart (S ω)).1 (x ω)).re)
    cases right
    · refine (h1.mono_of_le ?_).congr fun y _ => ?_
      · show -stRecL (S ω) ≤ -min (stRecL (S ω)) (x ω)
        exact neg_le_neg (min_le_left _ _)
      · simp only [lProf, ExplState.moveAlong, Chart.recenter, Complex.sub_re, Complex.ofReal_re]
        ring
    · refine h1.congr fun y _ => ?_
      simp only [lProf, ExplState.moveAlong, Chart.recenter, Complex.sub_re, Complex.ofReal_re]
      ring

end Basic

end StagedLaw

end Exist

end InteractingSLE
