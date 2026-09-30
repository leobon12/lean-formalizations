import QuantumZipper.Proofs.Zipper.Cor15BCases
import QuantumZipper.Proofs.Zipper.Cor15GroupZero
import QuantumZipper.Proofs.Zipper.ESMLMeas

/-!
# D35: Corollary 1.5(b), the positive-time group identities — core statement and tools

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
The paper calls the corollary immediate from Theorems 1.2–1.4: the configuration
`c = (𝔥₀ + h̃, η)` is a stationary object, unzipping `D_a` maps it to a configuration of the
same kind, and zipping `U_a` is the (a.s.) inverse of unzipping; the group law of
`Z^CAP_t` is then the group law of `D_a` and of its inverses.

Decision D35 (`DECISIONS.md`): we isolate exactly that implicit content as one core statement,
`Cor15GenuineStmt`, made of two halves, each on the *same* probability space:

* `Cor15MarkovStmt` (Markov property of unzipping): `D_a c` is a.s. `ConfigEq` to a genuine
  configuration `(𝔥₀ + X', √κ B')` (Brownian `B'`, free field `X'` modulo constants, independent);
* `Cor15ZipOntoStmt` (every genuine configuration is an unzipping): there is a genuine
  configuration `c''` with `D_a c''` a.s. `ConfigEq` to `c` (then `c'' ≈ U_a c` by the proved
  round trip `U_a D_a ≈ id`).

With these, all three remaining positive-time inputs of `Cor15BCases` are pure pathwise
algebra (`Cor15GrpReduce`) from the proved facts at genuine configurations: the round trip
`U_t D_t c ≈ c` (`ae_configEq_zipCapUp_zipCapDown`), the unzipping semigroup
(`theorem1_5b_nonpos`), `U_0 c ≈ c` (`ae_zipCapUp_zero_eq`), and the literal congruences of
`U_t`, `D_t` under `ConfigEq` (below).

This file: the core statements, `ConfigEq` symmetry/transitivity, the congruence of `D_t`
(own elementary argument: the Loewner forward flow on `[0,t]` reads the driver only on
`[0,t]`), and the three proved facts restated for an arbitrary genuine setup.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

/-- The genuine configuration `(𝔥₀ + X ω, √κ B ω)` of the Corollary 1.5 setup. -/
abbrev grpCfg (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) :
    FieldSample × (ℝ → ℝ) :=
  (ofFun (h0rev κ) + X ω, drive κ B ω)

/-- The hypotheses of Corollary 1.5 on a pair `(B, X)`. -/
def IsGrpSetup {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (X : Ω → FieldSample) : Prop :=
  IsBrownianReal B P ∧ IsFreeGFFModConstH X P ∧ IndepFun (pathOf B) X P

/-- **Core, half 1 (Markov property of capacity unzipping).** For every genuine setup and
every `a > 0`, the unzipped configuration `D_a c` is a.s. `ConfigEq` to a genuine configuration
on the same probability space. (Theorem 1.2 in full-field form plus the independence of the
Brownian increments after time `a`.) -/
def Cor15MarkovStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a → ∃ (B' : ℝ≥0 → Ω → ℝ) (X' : Ω → FieldSample), IsGrpSetup P B' X' ∧
      ∀ᵐ ω ∂P, ConfigEq (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)) (grpCfg κ B' X' ω)

/-! ## `ConfigEq` is an equivalence relation -/

theorem grpEq_symm {c c' : FieldSample × (ℝ → ℝ)} (h : ConfigEq c c') : ConfigEq c' c :=
  ⟨fun k z => (h.1 k z).symm, fun u hu => (h.2 u hu).symm⟩

theorem grpEq_trans {c c' c'' : FieldSample × (ℝ → ℝ)} (h : ConfigEq c c')
    (h' : ConfigEq c' c'') : ConfigEq c c'' :=
  ⟨fun k z => (h.1 k z).trans (h'.1 k z), fun u hu => (h.2 u hu).trans (h'.2 u hu)⟩

/-! ## Congruence of unzipping (own elementary argument) -/

/-- The swallowing time reads the driver only on `[0,∞)`. -/
theorem grp_swallowTime_congr {W W' : ℝ → ℝ} (h : ∀ u, 0 ≤ u → W u = W' u) (z : ℂ) :
    swallowTime W z = swallowTime W' z := by
  unfold swallowTime
  congr 2
  ext T
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hT, u, hu⟩
    exact ⟨hT, u, isForwardSol_congr_drive (fun r hr => h r hr.1) hu⟩
  · rintro ⟨hT, u, hu⟩
    exact ⟨hT, u, isForwardSol_congr_drive (fun r hr => (h r hr.1).symm) hu⟩

/-- The inverse forward map at time `t ≥ 0` reads the driver only on `[0,∞)` (no continuity
needed). -/
theorem grp_fwdMapInv_congr {W W' : ℝ → ℝ} (h : ∀ u, 0 ≤ u → W u = W' u) {t : ℝ} (ht : 0 ≤ t) :
    fwdMapInv W t = fwdMapInv W' t := by
  have hHull : fwdHull W t = fwdHull W' t := by
    ext z
    simp only [fwdHull, Set.mem_ofPred_eq, grp_swallowTime_congr h z]
  have hMap : fwdMap W t = fwdMap W' t :=
    funext fun z => ESM.fwdMap_congr_drive_ext ht (fun r hr => h r hr.1) z
  funext w
  unfold fwdMapInv
  rw [hHull, hMap]

/-- **Unzipping respects `ConfigEq`, literally.** -/
theorem zipCapDown_congr_grpEq {γ t : ℝ} (ht : 0 ≤ t) {x x' : FieldSample × (ℝ → ℝ)}
    (h : ConfigEq x x') : zipCapDown γ t x = zipCapDown γ t x' := by
  unfold zipCapDown
  rw [coordChange_congr_regEq h.1, grp_fwdMapInv_congr h.2 ht]
  congr 1
  funext s
  rw [h.2 _ (by positivity), h.2 t ht]

/-! ## The proved facts at an arbitrary genuine setup -/

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- Round trip `U_t D_t c ≈ c` (Theorem 1.3; `ae_configEq_zipCapUp_zipCapDown`). -/
theorem grp_roundTrip (h13 : theorem1_3) (hκ : 0 < κ) (hκ4 : κ < 4) (hS : IsGrpSetup P B X)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ConfigEq (zipCapUp (Real.sqrt κ) t (zipCapDown (Real.sqrt κ) t (grpCfg κ B X ω)))
      (grpCfg κ B X ω) :=
  ae_configEq_zipCapUp_zipCapDown P B X h13 RS.rohdeSchrammSimple cor15RezipFieldStmt_holds
    hκ hκ4 hS.1 hS.2.1 hS.2.2 ht

/-- Unzipping semigroup `D_{a+b} c ≈ D_b (D_a c)` (unconditional; `theorem1_5b_nonpos`). -/
theorem grp_unzipSemigroup (hS : IsGrpSetup P B X) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂P, ConfigEq (zipCapDown (Real.sqrt κ) (a + b) (grpCfg κ B X ω))
      (zipCapDown (Real.sqrt κ) b (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) := by
  filter_upwards [theorem1_5b_nonpos κ P B X hS.1 hS.2.1 hS.2.2 (s := -b) (t := -a)
    (by linarith) (by linarith)] with ω h
  rw [zipCap_of_neg (show -b + -a < 0 by linarith), zipCap_of_neg (show -a < 0 by linarith),
    zipCap_of_neg (show -b < 0 by linarith), neg_neg, neg_neg,
    show -(-b + -a) = a + b by ring] at h
  exact h

/-- `U_0 c ≈ c` (unconditional; `ae_zipCapUp_zero_eq`). -/
theorem grp_zipZero (hS : IsGrpSetup P B X) :
    ∀ᵐ ω ∂P, ConfigEq (zipCapUp (Real.sqrt κ) 0 (grpCfg κ B X ω)) (grpCfg κ B X ω) := by
  filter_upwards [ae_zipCapUp_zero_eq κ P B X hS.1 hS.2.1] with ω ⟨h1, h2⟩
  exact ⟨fun k z => congrFun (congrFun h1 k) z, fun u _ => congrFun h2 u⟩

end Cor15Group
end QuantumZipper
