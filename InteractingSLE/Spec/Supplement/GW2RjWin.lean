/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjKer
import InteractingSLE.Spec.Supplement.GW2RvPkg
import InteractingSLE.Spec.Supplement.GW2RvSlow
import InteractingSLE.Spec.Supplement.GW2SkRec
import InteractingSLE.Spec.Restart.FlowCodeMain

/-!
# Every slow stage variable avoids its angle regions and never returns to its start (decision D33)

PROVE-GW2-ROOTX round 9. D3's slow stage variable `n` of `(l, a)` at a good root (`GW2Rv.slowStageVarX` on the
root-`x` instance of version `n + 1` of the version family `ver`, with the choice family `ch`) is safe on time-ordered
histories (`InstInputsX.goodX`, `lowCapStopX_good_family`, `GoodX.isSafe`). So, almost surely, for EVERY history,
candidate and version at once, on the record event:

* **`ae_slowVarG_noBad_noReturn`**: no visit of `avoidQ κ 0 (β rec)` (round 8's `IsSafe.ae_not_badQ`) and no return to
  `0` (`IsSafe.ae_not_returnQ`) before the cap;
* `badQ_mono`, `badQ_congr`, `returnQ_mono`, `returnQ_congr`: the rational readings are monotone in the horizon and
  read the path only before it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rq GW2Rv GW2Rz GW2Sde GW2Sdh GW2Sdx

/-! ### The rational readings -/

theorem visitBefore_mono {Γ : ℝ≥0 → ℂ} {T T' : ℝ≥0∞} (hTT : T ≤ T') {A : Set ℂ} (h : SB.Wf.visitBefore Γ T A) :
    SB.Wf.visitBefore Γ T' A := by
  obtain ⟨t, ht, hq⟩ := h
  exact ⟨t, ht.trans_le hTT, hq⟩

theorem visitBefore_congr {Γ Γ' : ℝ≥0 → ℂ} {T : ℝ≥0∞} (hΓ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → Γ t = Γ' t)
    {A : Set ℂ} (h : SB.Wf.visitBefore Γ T A) : SB.Wf.visitBefore Γ' T A := by
  obtain ⟨t, ht, hq⟩ := h
  refine ⟨t, ht, fun n => ?_⟩
  obtain ⟨q, hqt, hd⟩ := hq n
  refine ⟨q, hqt, ?_⟩
  rwa [← hΓ q (lt_of_le_of_lt (by exact_mod_cast hqt) ht)]

theorem badQ_mono {κ θ : ℝ} {β : BoundaryWord} {Γ : ℝ≥0 → ℂ} {T T' : ℝ≥0∞} (hTT : T ≤ T')
    (h : BadQ κ θ β Γ T) : BadQ κ θ β Γ T' := by
  rcases h with ⟨a₁, a₂, ha, hv⟩ | ⟨a₁, a₂, ha, hv⟩ | ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩
  · exact Or.inl ⟨a₁, a₂, ha, visitBefore_mono hTT hv⟩
  · exact Or.inr (Or.inl ⟨a₁, a₂, ha, visitBefore_mono hTT hv⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, visitBefore_mono hTT hv⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, visitBefore_mono hTT hv⟩))

theorem badQ_congr {κ θ : ℝ} {β : BoundaryWord} {Γ Γ' : ℝ≥0 → ℂ} {T : ℝ≥0∞}
    (hΓ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → Γ t = Γ' t) (h : BadQ κ θ β Γ T) : BadQ κ θ β Γ' T := by
  rcases h with ⟨a₁, a₂, ha, hv⟩ | ⟨a₁, a₂, ha, hv⟩ | ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩
  · exact Or.inl ⟨a₁, a₂, ha, visitBefore_congr hΓ hv⟩
  · exact Or.inr (Or.inl ⟨a₁, a₂, ha, visitBefore_congr hΓ hv⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, visitBefore_congr hΓ hv⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, visitBefore_congr hΓ hv⟩))

theorem returnQ_mono {Γ : ℝ≥0 → ℂ} {T T' : ℝ≥0∞} (hTT : T ≤ T') (h : ReturnQ Γ T) : ReturnQ Γ T' := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, visitBefore_mono (tsub_le_tsub_right hTT _) hm⟩

theorem returnQ_congr {Γ Γ' : ℝ≥0 → ℂ} {T : ℝ≥0∞} (hΓ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → Γ t = Γ' t)
    (h : ReturnQ Γ T) : ReturnQ Γ' T := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, visitBefore_congr (fun t ht => hΓ _ (coe_add_lt_of_lt_sub ht)) hm⟩

/-! ### The slow stage variables -/

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})

/-- **D3's slow stage variable `n` of `(l, a)`** at a root with `0 ≤ x`. -/
abbrev slowVarG (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hx : 0 ≤ rootPt r.1) (n : ℕ) : StageVar Ω :=
  slowStageVarX h13 c r l a ((ver Ω c r l a).isA hx) (fun _ => ch Ω c r l a) n

variable {h13 ver ch}

/-- **The slow stage variables are safe** on time-ordered histories at good roots. -/
theorem slowVarG_isSafe (hI : InstInputsX h13 ver ch) {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} (hTO : HistOrdered c r l) (h : GoodRoot c r) (a n : ℕ) :
    (slowVarG h13 ver ch c r l a h.1 n).IsSafe c.κ c.P (slowVarG h13 ver ch c r l a h.1 n).record :=
  (hI.goodX hTO h a (n + 1)).isSafe (lowCapStopX_good_family h13 c r l a ((ver Ω c r l a).isA h.1)
    (fun _ => ch Ω c r l a) h.1 (ver Ω c r l a).mono (ver Ω c r l a).fin ((ver Ω c r l a).strict h.1)
    (fun n => hI.goodX hTO h a (n + 1)) n)

theorem measurable_slowVarG_record (hI : InstInputsX h13 ver ch) {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} (hTO : HistOrdered c r l) (h : GoodRoot c r) (a n : ℕ) :
    Measurable (slowVarG h13 ver ch c r l a h.1 n).record :=
  GW2Rd.measurable_augRec (measurable_stageEncRec c r l) (hI.goodX hTO h a (n + 1)).measurable_pre

/-- **No bad visit and no return**, almost surely, for every history, candidate and version, on the record event. -/
theorem ae_slowVarG_noBad_noReturn (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hI : InstInputsX h13 ver ch) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (h : GoodRoot c r) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ), HistOrdered c r l →
      (slowVarG h13 ver ch c r l a h.1 n).record ω ∈ (slowVarG h13 ver ch c r l a h.1 n).E →
        ¬ BadQ c.κ 0 ((slowVarG h13 ver ch c r l a h.1 n).β ((slowVarG h13 ver ch c r l a h.1 n).record ω))
            (fun q => LP.traceAt q (fun u => (slowVarG h13 ver ch c r l a h.1 n).R u ω))
            ((slowVarG h13 ver ch c r l a h.1 n).V ω) ∧
          ¬ ReturnQ (fun q => LP.traceAt q (fun u => (slowVarG h13 ver ch c r l a h.1 n).R u ω))
            ((slowVarG h13 ver ch c r l a h.1 n).V ω) := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hFd := Restart.isCanonicalDriverCode_driverCode h12p₀ c.hκ 0 h13₀
  refine ae_all_iff.2 fun l => ae_all_iff.2 fun a => ae_all_iff.2 fun n => ?_
  by_cases hTO : HistOrdered c r l
  · have hv := slowVarG_isSafe hI hTO h a n
    have hrecm := measurable_slowVarG_record hI hTO h a n
    filter_upwards [hv.ae_not_badQ h12p h13 c.hκ c.hκ4 hFd hrecm,
      hv.ae_not_returnQ h12p h13 c.hκ c.hκ4 hFd hrecm] with ω h1 h2 _ hE
    exact ⟨h1 hE, h2 hE⟩
  · exact Eventually.of_forall fun ω hTO' => absurd hTO' hTO

end InteractingSLE.Theorem14.GW2Rj
