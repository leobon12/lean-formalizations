import MatedCRTHarmonic.CellScaling.Model
import MatedCRTHarmonic.MatedCRT.GraphMeasurability
import MatedCRTHarmonic.Harmonic.Walk

/-!
# Measurable walk weights for mesh graphs

The candidate dart labels form a fixed countable space, independent of the path. Summing their
measurable active-dart indicators gives a measurable extended-real degree, and hence measurable
weights for each fixed candidate transition.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellScaling

abbrev MeshGridEdgeCode := ℤ × ℤ × Bool
abbrev MeshGridDartCode := MeshGridEdgeCode × Bool
abbrev MeshGridStateCode := ℤ ⊕ MeshGridDartCode

def meshGridDartSourceCode (d : MeshGridDartCode) : ℤ :=
  if d.2 then d.1.2.1 else d.1.1

def meshGridStateVertexCode : MeshGridStateCode → ℤ
  | Sum.inl x => x
  | Sum.inr d => if d.2 then d.1.1 else d.1.2.1

def meshGridEncodeMatedState {ε : ℝ} {ω : MatedCRT.Path2}
    {hlf : MatedCRT.IsLocallyFinite ε ω}
    (s : (MatedCRT.graph ε ω hlf).State) : MeshGridStateCode :=
  Sum.elim Sum.inl (fun d => Sum.inr (d.1.1, d.2)) s

theorem meshGridStateVertexCode_encode {ε : ℝ} {ω : MatedCRT.Path2}
    {hlf : MatedCRT.IsLocallyFinite ε ω}
    (s : (MatedCRT.graph ε ω hlf).State) :
    meshGridStateVertexCode (meshGridEncodeMatedState s) =
      (MatedCRT.graph ε ω hlf).stateVertex s := by
  cases s with
  | inl x => rfl
  | inr d => cases d with
    | mk e b => cases b <;> rfl

theorem meshGridDartSourceCode_encode {ε : ℝ} {ω : MatedCRT.Path2}
    {hlf : MatedCRT.IsLocallyFinite ε ω}
    (d : (MatedCRT.graph ε ω hlf).Dart) :
    meshGridDartSourceCode (d.1.1, d.2) =
      (MatedCRT.graph ε ω hlf).dsrc d := by
  cases d with
  | mk e b => cases b <;> rfl

def meshGridDartActiveAt (ε : ℝ) (ω : MatedCRT.Path2) (x : ℤ)
    (d : MeshGridDartCode) : Prop :=
  MatedCRT.edgePredicate ε ω d.1 = true ∧ meshGridDartSourceCode d = x

noncomputable def meshGridRawDegree (ε : ℝ) (ω : MatedCRT.Path2) (x : ℤ) : ℝ≥0∞ := by
  classical
  exact ∑' d : MeshGridDartCode, if meshGridDartActiveAt ε ω x d then 1 else 0

noncomputable def meshGridCandidateTransitionWeight (ε : ℝ) (x : ℤ)
    (d : MeshGridDartCode) (ω : MatedCRT.Path2) : ℝ≥0∞ := by
  classical
  exact if meshGridDartActiveAt ε ω x d then (meshGridRawDegree ε ω x)⁻¹ else 0

noncomputable def meshGridCodeTransitionWeight (ε : ℝ) (s t : MeshGridStateCode)
    (ω : MatedCRT.Path2) : ℝ≥0∞ :=
  match t with
  | Sum.inl _ => 0
  | Sum.inr d => meshGridCandidateTransitionWeight ε (meshGridStateVertexCode s) d ω

noncomputable def meshGridCodePrefixWeight (ε : ℝ) (x : ℤ)
    (s : ℕ → MeshGridStateCode) (n : ℕ) (ω : MatedCRT.Path2) : ℝ≥0∞ := by
  classical
  exact if s 0 = Sum.inl x then
    ∏ i ∈ Finset.range n, meshGridCodeTransitionWeight ε (s i) (s (i + 1)) ω
  else 0

private theorem measurableSet_meshDartActiveAt (ε : ℝ) (x : ℤ) (d : MeshGridDartCode) :
    MeasurableSet {ω : MatedCRT.Path2 | meshGridDartActiveAt ε ω x d} := by
  classical
  have hEval : Measurable (fun ω : MatedCRT.Path2 => MatedCRT.edgePredicate ε ω d.1) :=
    (MatedCRT.matedCRT_edgePredicate_measurable_holds ε).eval (a := d.1)
  have hEdge : MeasurableSet {ω : MatedCRT.Path2 | MatedCRT.edgePredicate ε ω d.1 = true} :=
    (measurableSet_singleton true).preimage hEval
  by_cases hs : meshGridDartSourceCode d = x
  · simpa [meshGridDartActiveAt, hs] using hEdge
  · simp [meshGridDartActiveAt, hs]

/-- The degree obtained by counting active candidate darts is Borel in the Brownian path. -/
theorem measurable_meshGridRawDegree (ε : ℝ) (x : ℤ) :
    Measurable (fun ω : MatedCRT.Path2 => meshGridRawDegree ε ω x) := by
  classical
  unfold meshGridRawDegree
  apply Measurable.ennreal_tsum
  intro d
  have hs := measurableSet_meshDartActiveAt ε x d
  exact Measurable.ite hs measurable_const measurable_const

/-- On locally finite data, the countable-code degree is exactly the edge-end degree of the
frozen mesh graph. -/
theorem meshGridRawDegree_eq_graph_deg (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (x : ℤ) :
    meshGridRawDegree ε ω x =
      ((MatedCRT.graph ε ω hlf).deg x : ℝ≥0∞) := by
  classical
  let G := MatedCRT.graph ε ω hlf
  let A : Set MeshGridDartCode := {d | meshGridDartActiveAt ε ω x d}
  let B : Set G.Dart := {d | G.dsrc d = x}
  have hedge (e : MeshGridEdgeCode) :
      MatedCRT.edgePredicate ε ω e = true ↔ MatedCRT.IsEdge ε ω e := by
    simp [MatedCRT.edgePredicate]
  have hactive (d : G.Dart) :
      meshGridDartActiveAt ε ω x (d.1.1, d.2) ↔ G.dsrc d = x := by
    rcases d with ⟨⟨e, he⟩, b⟩
    change (MatedCRT.edgePredicate ε ω e = true ∧
      (if b then e.2.1 else e.1) = x) ↔ (if b then e.2.1 else e.1) = x
    simp [MatedCRT.edgePredicate, he]
  let f : B → A := fun d =>
    ⟨(d.1.1.1, d.1.2), (hactive d.1).2 d.2⟩
  let g : A → B := fun c =>
    ⟨(⟨c.1.1, (hedge c.1.1).mp c.2.1⟩, c.1.2),
      (hactive (⟨⟨c.1.1, (hedge c.1.1).mp c.2.1⟩, c.1.2⟩ : G.Dart)).mp c.2⟩
  have hfg : Function.LeftInverse g f := by
    intro d
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  have hgf : Function.RightInverse g f := by
    intro c
    apply Subtype.ext
    rfl
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    calc
      a.1 = (g (f a)).1 := congrArg Subtype.val (hfg a).symm
      _ = (g (f b)).1 := congrArg (fun y => (g y).1) hab
      _ = b.1 := congrArg Subtype.val (hfg b)
  have hsurj : Function.Surjective f := by
    intro c
    exact ⟨g c, hgf c⟩
  let eAB : B ≃ A := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hB : B = (G.outDarts x : Set G.Dart) := by
    ext d
    simp [B, Harmonic.mem_outDarts]
  have hBfinite : B.Finite := by
    rw [hB]
    exact (G.outDarts x).finite_toSet
  letI : Fintype B := hBfinite.fintype
  letI : Fintype A := Fintype.ofEquiv B eAB
  have hsum : meshGridRawDegree ε ω x = ∑' c : A, (1 : ℝ≥0∞) := by
    unfold meshGridRawDegree
    have hindicator : (fun d : MeshGridDartCode =>
        if meshGridDartActiveAt ε ω x d then (1 : ℝ≥0∞) else 0) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext d
      by_cases hd : d ∈ A
      · have hactive : meshGridDartActiveAt ε ω x d := by simpa [A] using hd
        rw [if_pos hactive, Set.indicator_of_mem hd]
      · have hactive : ¬ meshGridDartActiveAt ε ω x d := by simpa [A] using hd
        rw [if_neg hactive, Set.indicator_of_notMem hd]
    rw [hindicator, ← tsum_subtype A (fun _ => (1 : ℝ≥0∞))]
  calc
    meshGridRawDegree ε ω x = ∑' c : A, (1 : ℝ≥0∞) := hsum
    _ = (Fintype.card A : ℝ≥0∞) := by simp [tsum_fintype]
    _ = (Fintype.card B : ℝ≥0∞) := by rw [Fintype.card_congr eAB.symm]
    _ = ((G.outDarts x).card : ℝ≥0∞) := by
      let eb : B ≃ {d : G.Dart // d ∈ G.outDarts x} := {
        toFun := fun d => ⟨d.1, (Harmonic.mem_outDarts G).mpr d.2⟩
        invFun := fun d => ⟨d.1, (Harmonic.mem_outDarts G).mp d.2⟩
        left_inv := by intro d; apply Subtype.ext; rfl
        right_inv := by intro d; apply Subtype.ext; rfl }
      rw [Fintype.card_congr eb]
      simp
    _ = ((G.deg x : ℕ) : ℝ≥0∞) := by simp [LFMultigraph.deg]

private theorem meshGridStepMeasure_singleton_start_eq_zero {V E : Type*}
    (G : LFMultigraph V E) (x y : V) :
    G.stepMeasure x {Harmonic.startState G y} = 0 := by
  have hnot : Harmonic.startState G y ∉ Harmonic.outStates G x := by
    rintro ⟨d, hd, heq⟩
    exact (Harmonic.startState_ne_dartState G y d) heq
  have hsub : ({Harmonic.startState G y} : Set G.State) ⊆ (Harmonic.outStates G x)ᶜ := by
    intro s hs
    have hsy : s = Harmonic.startState G y := Set.mem_singleton_iff.mp hs
    subst s
    exact hnot
  exact measure_mono_null hsub (Harmonic.stepMeasure_notOut G x)

private theorem meshGridStepMeasure_singleton_dart_eq_zero {V E : Type*}
    (G : LFMultigraph V E) (x : V) (d : G.Dart) (hsrc : G.dsrc d ≠ x) :
    G.stepMeasure x {Harmonic.dartState G d} = 0 := by
  have hnot : Harmonic.dartState G d ∉ Harmonic.outStates G x := by
    rintro ⟨d', hd', heq⟩
    have hde : d = d' := Harmonic.dartState_injective G heq
    exact hsrc (hde.symm ▸ hd')
  have hsub : ({Harmonic.dartState G d} : Set G.State) ⊆ (Harmonic.outStates G x)ᶜ := by
    intro s hs
    have hsd : s = Harmonic.dartState G d := Set.mem_singleton_iff.mp hs
    subst s
    exact hnot
  exact measure_mono_null hsub (Harmonic.stepMeasure_notOut G x)

private theorem meshGridCandidateTransitionWeight_eq_stepMeasure {ε : ℝ}
    (ω : MatedCRT.Path2) (hlf : MatedCRT.IsLocallyFinite ε ω) (x : ℤ)
    (d : (MatedCRT.graph ε ω hlf).Dart) :
    meshGridCandidateTransitionWeight ε x (d.1.1, d.2) ω =
      (MatedCRT.graph ε ω hlf).stepMeasure x
        {Harmonic.dartState (MatedCRT.graph ε ω hlf) d} := by
  let G := MatedCRT.graph ε ω hlf
  by_cases hsrc : G.dsrc d = x
  · have hactive : meshGridDartActiveAt ε ω x (d.1.1, d.2) := by
      constructor
      · simp [MatedCRT.edgePredicate, d.1.2]
      · rw [meshGridDartSourceCode_encode]
        exact hsrc
    unfold meshGridCandidateTransitionWeight
    rw [if_pos hactive, meshGridRawDegree_eq_graph_deg ε ω hlf x,
      Harmonic.stepMeasure_singleton_dartState G hsrc]
  · have hinactive : ¬ meshGridDartActiveAt ε ω x (d.1.1, d.2) := by
      intro h
      have hsource : meshGridDartSourceCode (d.1.1, d.2) = G.dsrc d := by
        simpa [G] using meshGridDartSourceCode_encode d
      exact hsrc (hsource.symm.trans h.2)
    unfold meshGridCandidateTransitionWeight
    rw [if_neg hinactive]
    exact (meshGridStepMeasure_singleton_dart_eq_zero G x d hsrc).symm

private theorem meshGridCodeTransitionWeight_eq_walkKernel {ε : ℝ}
    (ω : MatedCRT.Path2) (hlf : MatedCRT.IsLocallyFinite ε ω)
    (a b : (MatedCRT.graph ε ω hlf).State) :
    meshGridCodeTransitionWeight ε (meshGridEncodeMatedState a)
      (meshGridEncodeMatedState b) ω =
        (MatedCRT.graph ε ω hlf).walkKernel a {b} := by
  let G := MatedCRT.graph ε ω hlf
  cases b with
  | inl y =>
    change 0 = G.walkKernel a {Harmonic.startState G y}
    rw [Harmonic.walkKernel_apply,
      meshGridStepMeasure_singleton_start_eq_zero G (G.stateVertex a) y]
  | inr d =>
    change meshGridCandidateTransitionWeight ε
      (meshGridStateVertexCode (meshGridEncodeMatedState a)) (d.1.1, d.2) ω =
      G.walkKernel a {Harmonic.dartState G d}
    have hvertex : meshGridStateVertexCode (meshGridEncodeMatedState a) =
        G.stateVertex a := by
      simpa [G] using meshGridStateVertexCode_encode a
    rw [hvertex]
    rw [Harmonic.walkKernel_apply]
    exact meshGridCandidateTransitionWeight_eq_stepMeasure ω hlf (G.stateVertex a) d

/-- The finite-state cylinder mass of the edge-end walk is exactly the fixed-code prefix product.
This is `Markov.chainLaw_cylinder` with each one-step mass rewritten as its measurable edge-code
weight. -/
theorem meshGridWalkLaw_stateCylinder (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (x : ℤ)
    (s : ℕ → (MatedCRT.graph ε ω hlf).State) (n : ℕ) :
    (MatedCRT.graph ε ω hlf).walkLaw x
        {path | ∀ i ≤ n, path i = s i} =
      meshGridCodePrefixWeight ε x (fun i => meshGridEncodeMatedState (s i)) n ω := by
  classical
  let G := MatedCRT.graph ε ω hlf
  rw [Harmonic.walkLaw_eq, Markov.chainLaw_cylinder]
  have hprod : (∏ i ∈ Finset.range n, G.walkKernel (s i) {s (i + 1)}) =
      ∏ i ∈ Finset.range n,
        meshGridCodeTransitionWeight ε (meshGridEncodeMatedState (s i))
          (meshGridEncodeMatedState (s (i + 1))) ω := by
    apply Finset.prod_congr rfl
    intro i hi
    exact (meshGridCodeTransitionWeight_eq_walkKernel ω hlf (s i) (s (i + 1))).symm
  rw [hprod]
  have hcodeStart : meshGridEncodeMatedState (s 0) = Sum.inl x ↔
      s 0 = Harmonic.startState G x := by
    cases s0 : s 0 with
    | inl y =>
      simp only [meshGridEncodeMatedState, s0, Harmonic.startState, Sum.elim_inl]
      constructor
      · intro h
        exact congrArg Sum.inl (Sum.inl.inj h)
      · intro h
        exact congrArg Sum.inl (Sum.inl.inj h)
    | inr d => simp [meshGridEncodeMatedState, s0, Harmonic.startState]
  unfold meshGridCodePrefixWeight
  have hstartFactor :
      (if s 0 = Harmonic.startState G x then (1 : ℝ≥0∞) else 0) =
        (if meshGridEncodeMatedState (s 0) = Sum.inl x then 1 else 0) := by
    by_cases hs : s 0 = Harmonic.startState G x
    · have hc := hcodeStart.mpr hs
      rw [if_pos hs, if_pos hc]
    · have hc : meshGridEncodeMatedState (s 0) ≠ Sum.inl x :=
        fun hc => hs (hcodeStart.mp hc)
      rw [if_neg hs, if_neg hc]
  rw [hstartFactor]
  by_cases hc : meshGridEncodeMatedState (s 0) = Sum.inl x <;> simp [hc]

/-- Every fixed candidate edge-end transition has a measurable simple-random-walk weight,
using the countable-code degree. -/
theorem measurable_meshGridCandidateTransitionWeight (ε : ℝ) (x : ℤ) (d : MeshGridDartCode) :
    Measurable (meshGridCandidateTransitionWeight ε x d) := by
  classical
  have hdeg := measurable_meshGridRawDegree ε x
  have hinv : Measurable (fun ω : MatedCRT.Path2 => (meshGridRawDegree ε ω x)⁻¹) := by
    exact measurable_inv.comp hdeg
  unfold meshGridCandidateTransitionWeight
  exact Measurable.ite (measurableSet_meshDartActiveAt ε x d) hinv measurable_const

/-- The finite-prefix weight associated with any fixed sequence of candidate edge-end states is
Borel. This is the product expansion used by `Markov.chainLaw_cylinder`; the only data-dependent
terms are the fixed-edge indicators and the countable-code degrees above. -/
theorem measurable_meshGridCodePrefixWeight (ε : ℝ) (x : ℤ) (s : ℕ → MeshGridStateCode) (n : ℕ) :
    Measurable (meshGridCodePrefixWeight ε x s n) := by
  classical
  have hprod : Measurable (fun ω : MatedCRT.Path2 =>
      ∏ i ∈ Finset.range n, meshGridCodeTransitionWeight ε (s i) (s (i + 1)) ω) := by
    apply Finset.measurable_prod (Finset.range n)
    intro i hi
    cases s (i + 1) with
    | inl y =>
      change Measurable (fun _ : MatedCRT.Path2 => (0 : ℝ≥0∞))
      exact measurable_const
    | inr d =>
      change Measurable (meshGridCandidateTransitionWeight ε (meshGridStateVertexCode (s i)) d)
      exact measurable_meshGridCandidateTransitionWeight ε (meshGridStateVertexCode (s i)) d
  unfold meshGridCodePrefixWeight
  split_ifs
  · exact hprod
  · exact measurable_const

end MatedCRTHarmonic.CellScaling
