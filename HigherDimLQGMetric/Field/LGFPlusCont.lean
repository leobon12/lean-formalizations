import HigherDimLQGMetric.Field.Measurable
import HigherDimLQGMetric.Frozen.IsLGFPlusCont
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont

/-!
# The input classes are closed under adding constants and continuous functions

Packet F1 (algebra of `addFun`/`addConst`, applied to the frozen input classes). For the frozen
predicates `IsWholeSpaceLGF`, `IsLGFPlusCont`, `IsLGFPlusBddCont`:

* `IsWholeSpaceLGF.of_apply_eq`: the LGF property only sees the pairings with mean-zero test
  functions; hence `IsWholeSpaceLGF.addConst` (an LGF has an arbitrary, possibly random, additive
  constant, [1] §1.1);
* `IsWholeSpaceLGF.isLGFPlusBddCont`, `IsLGFPlusBddCont.isLGFPlusCont`;
* `IsLGFPlusCont.addFun`, `IsLGFPlusCont.addConst` (random measurable `f`, `c`), and the bounded
  versions `IsLGFPlusBddCont.addFun`, `IsLGFPlusBddCont.addConst`.

Port of LQGMetric's `Field/GFFInvariance.lean` (`IsWholePlaneGFF.addConst`) and
`Papers/GM/S1/StrongWeak.lean` (`isGFFPlusCont_of_isWholePlaneGFF`); own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The LGF property only depends on the pairings with mean-zero test functions. -/
theorem IsWholeSpaceLGF.of_apply_eq {h h' : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (hm : Measurable h') (heq : ∀ ω (φ : TestRd0 d), h' ω φ.1 = h ω φ.1) :
    IsWholeSpaceLGF h' P := by
  have e : (fun (φ : TestRd0 d) (ω : Ω) => h' ω φ.1) = fun φ ω => h ω φ.1 :=
    funext fun φ => funext fun ω => heq ω φ
  have e' : ∀ φ : TestRd0 d, (fun ω => h' ω φ.1) = fun ω => h ω φ.1 :=
    fun φ => funext fun ω => heq ω φ
  refine ⟨hm, ?_, fun φ => ?_, fun φ ψ => ?_⟩
  · rw [e]; exact hh.gaussian
  · rw [e' φ]; exact hh.centered φ
  · rw [e' φ, e' ψ]; exact hh.covariance_eq φ ψ

/-- Adding a (random, measurable) constant to an LGF gives an LGF. -/
theorem IsWholeSpaceLGF.addConst {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P) {c : Ω → ℝ}
    (hc : Measurable c) : IsWholeSpaceLGF (fun ω => addConst (h ω) (c ω)) P :=
  hh.of_apply_eq (Measurable.addConst hh.measurable hc) fun _ φ =>
    addConst_apply_testRd0 _ _ φ

theorem IsWholeSpaceLGF.isLGFPlusBddCont {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P) :
    IsLGFPlusBddCont h P := by
  refine ⟨hh.measurable, fun _ => 0, measurable_const, fun _ => ⟨0, fun _ => by simp⟩, ?_⟩
  simpa only [ofCont_zero, sub_zero] using hh

theorem IsLGFPlusBddCont.isLGFPlusCont {h : Ω → DistRd d} (hh : IsLGFPlusBddCont h P) :
    IsLGFPlusCont h P :=
  ⟨hh.1, hh.2.choose, hh.2.choose_spec.1, hh.2.choose_spec.2.2⟩

theorem IsWholeSpaceLGF.isLGFPlusCont {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P) :
    IsLGFPlusCont h P :=
  hh.isLGFPlusBddCont.isLGFPlusCont

theorem IsLGFPlusCont.measurable {h : Ω → DistRd d} (hh : IsLGFPlusCont h P) : Measurable h :=
  hh.1

theorem IsLGFPlusBddCont.measurable {h : Ω → DistRd d} (hh : IsLGFPlusBddCont h P) :
    Measurable h :=
  hh.1

theorem addFun_sub_ofCont_add (h : DistRd d) (f g : C(Rd d, ℝ)) :
    addFun h g - ofCont (f + g) = h - ofCont f := by
  rw [addFun, ofCont_add]
  abel

/-- Adding a (random, measurable) continuous function to an LGF plus a continuous function gives
an LGF plus a continuous function. -/
theorem IsLGFPlusCont.addFun {h : Ω → DistRd d} (hh : IsLGFPlusCont h P) {g : Ω → C(Rd d, ℝ)}
    (hg : Measurable g) : IsLGFPlusCont (fun ω => addFun (h ω) (g ω)) P := by
  obtain ⟨hm, f, hf, hlgf⟩ := hh
  refine ⟨Measurable.addFun hm hg, fun ω => f ω + g ω, hf.add hg, ?_⟩
  simpa only [addFun_sub_ofCont_add] using hlgf

theorem IsLGFPlusCont.addConst {h : Ω → DistRd d} (hh : IsLGFPlusCont h P) {c : Ω → ℝ}
    (hc : Measurable c) : IsLGFPlusCont (fun ω => addConst (h ω) (c ω)) P :=
  hh.addFun (measurable_const_continuousMap.comp hc)

/-- The bounded version: adding a measurable continuous function that is bounded for each `ω`. -/
theorem IsLGFPlusBddCont.addFun {h : Ω → DistRd d} (hh : IsLGFPlusBddCont h P)
    {g : Ω → C(Rd d, ℝ)} (hg : Measurable g) (hgb : ∀ ω, ∃ M : ℝ, ∀ z, |g ω z| ≤ M) :
    IsLGFPlusBddCont (fun ω => addFun (h ω) (g ω)) P := by
  obtain ⟨hm, f, hf, hfb, hlgf⟩ := hh
  refine ⟨Measurable.addFun hm hg, fun ω => f ω + g ω, hf.add hg, fun ω => ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hfb ω
    obtain ⟨M', hM'⟩ := hgb ω
    exact ⟨M + M', fun z => (abs_add_le _ _).trans (add_le_add (hM z) (hM' z))⟩
  · simpa only [addFun_sub_ofCont_add] using hlgf

theorem IsLGFPlusBddCont.addConst {h : Ω → DistRd d} (hh : IsLGFPlusBddCont h P) {c : Ω → ℝ}
    (hc : Measurable c) : IsLGFPlusBddCont (fun ω => addConst (h ω) (c ω)) P :=
  hh.addFun (measurable_const_continuousMap.comp hc) fun ω => ⟨|c ω|, fun _ => le_rfl⟩

end HigherDimLQGMetric
