/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdeRecord
import InteractingSLE.Spec.Supplement.GW2SdeGauss

/-!
# GW2's retained stopped SDE: what one stage must supply

Packet PROVE-GW2-SDE. This small module states EXACTLY what the SDE half of JOINTDET's R11 pair consumes from the
per-stage work (PROVE-GW2-RELDET's stage chain and version, PROVE-GW2-STAGEMEAN's union mean and threshold, fed through
`GW2Rd.hasRelSafe_of_lines_rec`):

* `StageVar`: the stage relative variable of one future piece — the stage record `record`, the stage word `β` read
  off it, the good record event `E`, the stage relative field `Hr`, the relative driver `R`, its cap `V`, the engine's
  path rules `ρ`, `ρs`, and the physical (local) stop `stop` with its stopping rule `stopRule`;
* **`StageVar.IsSafe κ P rec`**: K2's safe law on every word type for the joint law of `(rec, (Hr, R, V))`
  (`Supp8.Q3Stop.HasRelSafe`), the engine's stop conditions and the protection of the physical stop — the hypotheses
  of `ae_exists_isStopped_of_relSafe` except the time-`0` conditional field law, which K2's (S) clause already
  contains (`ae_condExp_eq_gaussCF_of_relSafe`);
* `StageVar.IsSafe.ae_exists_isStopped`: the stopped SDE of the physical piece under `condExpKernel P (comap rec)`;
* `chooseDyn`: local dynamics with a PRESCRIBED driver and stop, chosen when stopped dynamics with that driver and stop
  exist (so the comparison data fix the physical driver and stop independently of the SDE proof, and the buffer half
  can be proved about them: `chooseDyn_W`, `chooseDyn_stop`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sde

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId

/-- **The stage relative variable of one future piece** (data only): the stage record, the stage word read off it,
the good record event, the stage relative field, driver and cap, the engine's path rules for the cap, and the physical
stop with its stopping rule of the record and the killed relative path. -/
structure StageVar (Ω : Type u) where
  record : Ω → RecData
  β : RecData → BoundaryWord
  E : Set RecData
  Hr : Ω → DistOn upperHalfPlaneOpens
  R : ℝ≥0 → Ω → ℝ
  V : Ω → ℝ≥0∞
  ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  stop : Ω → ℝ≥0∞
  stopRule : RecData → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞

/-- **K2's safe stage law of a stage variable for the record `rec`**: the inputs of
`ae_exists_isStopped_of_relSafe` other than the time-`0` field law (K2's (S), (L), threshold and integrability on every
word type; sorted words on the record event; the cap a positive announced path rule; the physical stop a protected
stopping rule). -/
structure StageVar.IsSafe {Ω : Type u} [MeasurableSpace Ω] (v : StageVar Ω) (κ : ℝ) (P : Measure Ω)
    (rec : Ω → RecData) : Prop where
  measurable_β : Measurable v.β
  measurableSet_E : MeasurableSet v.E
  countable_wordType : (range fun r : RecData => wordType κ (v.β r)).Countable
  isSorted : ∀ r ∈ v.E, (v.β r).IsSorted
  measurable_Hr : Measurable v.Hr
  measurable_R : ∀ t, Measurable (v.R t)
  continuous_R : ∀ ω, Continuous fun t => v.R t ω
  R_zero : ∀ ω, v.R 0 ω = 0
  measurable_V : Measurable v.V
  relSafe : ∀ w : WordType, HasRelSafe κ w v.β v.E (P.map fun ω => (rec ω, relVar v.Hr v.R v.V ω))
  V_pos : ∀ᵐ ω ∂P, rec ω ∈ v.E → 0 < v.V ω
  measurable_ρ : Measurable v.ρ
  isPathRule_ρ : IsPathRule v.ρ
  V_eq : ∀ᵐ ω ∂P, v.V ω = v.ρ (rec ω, fun u => v.R u ω)
  measurable_ρs : ∀ n, Measurable (v.ρs n)
  isPathRule_ρs : ∀ n, IsPathRule (v.ρs n)
  ρs_ne_top : ∀ n x, v.ρs n x ≠ ⊤
  ρs_mono : ∀ x, Monotone fun n => v.ρs n x
  ρs_lt : ∀ᵐ ω ∂P, rec ω ∈ v.E → ∀ n, v.ρs n (rec ω, fun u => v.R u ω) < v.V ω
  ρs_iSup : ∀ᵐ ω ∂P, rec ω ∈ v.E → ⨆ n, v.ρs n (rec ω, fun u => v.R u ω) = v.V ω
  stopRule_meas : ∀ (x : RecData) (t : ℝ≥0), MeasurableSet[pathKilledSigma t] {e | v.stopRule x e ≤ (t : ℝ≥0∞)}
  measurable_stop : Measurable v.stop
  stop_eq : ∀ᵐ ω ∂P, v.stop ω = v.stopRule (rec ω) ((fun t => v.R t ω), v.V ω)
  stop_le : ∀ᵐ ω ∂P, rec ω ∈ v.E → v.stop ω ≤ v.V ω
  stop_lt : ∀ᵐ ω ∂P, rec ω ∈ v.E → v.stop ω ≠ ⊤ → v.stop ω < v.V ω

/-- **The stopped SDE of a safe stage variable** under the regular conditional law given its record. -/
theorem StageVar.IsSafe.ae_exists_isStopped (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode κ 0 Fd)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {rec : Ω → RecData} (hrecm : Measurable rec) {v : StageVar Ω} (hv : v.IsSafe κ P rec) :
    ∀ᵐ ω₀ ∂P, rec ω₀ ∈ v.E → ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ},
      FCDet.IsFlowType κ 0 (v.β (rec ω₀)) xL xR ρL ρR →
      ∃ d : GW2JDetR11.LocalDynamics Ω nL nR, d.W = v.R ∧ d.stop = v.stop ∧
        d.IsStopped (condExpKernel P (MeasurableSpace.comap rec inferInstance) ω₀) κ xL ρL xR ρR :=
  ae_exists_isStopped_of_relSafe h12p h13 hκ hFd hv.measurable_β hv.measurableSet_E hv.countable_wordType
    hv.isSorted hrecm hv.measurable_Hr hv.measurable_R hv.continuous_R hv.R_zero hv.measurable_V hv.relSafe
    hv.V_pos hv.measurable_ρ hv.isPathRule_ρ hv.V_eq hv.measurable_ρs hv.isPathRule_ρs hv.ρs_ne_top hv.ρs_mono
    hv.ρs_lt hv.ρs_iSup (fun φ => ae_condExp_eq_gaussCF_of_relSafe hκ hv.measurable_β hv.measurableSet_E
      hv.countable_wordType hv.isSorted hrecm hv.measurable_Hr hv.measurable_R hv.measurable_V hv.relSafe hv.V_pos φ)
    v.stopRule hv.stopRule_meas hv.measurable_stop hv.stop_eq hv.stop_le
    hv.stop_lt

/-! ### Local dynamics with a prescribed driver and stop -/

/-- **Local dynamics with the prescribed driver `R` and stop `τ`**: stopped dynamics with exactly this driver and stop
when they exist (chosen), otherwise trivial data with the same driver and stop. -/
def chooseDyn {Ω : Type u} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} (μ : Measure Ω) (κ : ℝ)
    (xL ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ) (R : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) :
    GW2JDetR11.LocalDynamics Ω nL nR :=
  open Classical in
  if h : ∃ d : GW2JDetR11.LocalDynamics Ω nL nR, d.W = R ∧ d.stop = τ ∧ d.IsStopped μ κ xL ρL xR ρR then
    h.choose
  else
    { filtration := { seq := fun _ => ⊥, mono' := fun _ _ _ => le_rfl, le' := fun _ => bot_le }
      W := R
      VL := fun _ _ _ => 0
      VR := fun _ _ _ => 0
      B := fun _ _ => 0
      stop := τ }

section ChooseDyn

variable {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ} {μ : Measure Ω} {κ : ℝ} {xL ρL : Fin nL → ℝ}
  {xR ρR : Fin nR → ℝ} {R : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞}

/-- The chosen dynamics have the prescribed driver. -/
@[simp] theorem chooseDyn_W : (chooseDyn μ κ xL ρL xR ρR R τ).W = R := by
  unfold chooseDyn
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

/-- The chosen dynamics have the prescribed stop. -/
@[simp] theorem chooseDyn_stop : (chooseDyn μ κ xL ρL xR ρR R τ).stop = τ := by
  unfold chooseDyn
  split_ifs with h
  · exact h.choose_spec.2.1
  · rfl

/-- If stopped dynamics with the prescribed driver and stop exist, the chosen ones are stopped dynamics. -/
theorem isStopped_chooseDyn
    (h : ∃ d : GW2JDetR11.LocalDynamics Ω nL nR, d.W = R ∧ d.stop = τ ∧ d.IsStopped μ κ xL ρL xR ρR) :
    (chooseDyn μ κ xL ρL xR ρR R τ).IsStopped μ κ xL ρL xR ρR := by
  unfold chooseDyn
  split_ifs
  exact h.choose_spec.2.2

end ChooseDyn

end InteractingSLE.Theorem14.GW2Sde
