import QuantumZipper.Proofs.Zipper.E5Main2
import QuantumZipper.Proofs.Zipper.D3PlusProb

/-!
# E5-MAIN, part 3: the zoom model and its TV-limit (E5 steps (2), (4), (5))

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, node **E5**. After step (1) (E4 + L2) and the
identification of step (3) (E-SM(b): `𝐏 = w · 𝐑`, germ `⊥ M` and Wiener under `𝐑`), the zoomed
configuration is read on an abstract probability space `(Ω₁, Q)` as the **zoom model**
`(zLoc C (X' ω) (g ω), drvWin (rescale R a D))`: the local canonical data of the D3⁺ model field
`zoomModel γ α C ρ₀ X' g` on the half-disc, together with the driver germ `D` rescaled by the
local scale `a = zScale C (X' ω) (g ω)`, on the capacity window `[0, R]` (scaled by `√κ`).

`tvNear_model` proves that the model functional is TV-near the target
`E_{P'} E_W Γ(locField R Y, drvWin (b|_{[0,R]}))`, from
* D3⁺(ii) (LSC, hypothesis `hII`) to replace the true correction `g` by the germ-free `g₀`
  (step (2)); the bound `|g − g₀| ≤ K` is only required outside a `condSigma`-measurable bad set
  of probability `≤ ε` (the corrections are switched to `g₀` there, which keeps harmonicity);
* D3⁺(iii) (`d3PlusIII_tendsto_prob`, proved) for the positivity and smallness of the scale;
* E5a/E5-DENS (`tvNear_germ`) for the germ (step (4));
* D3⁺(i) (hypothesis `hI`) for the field (step (5)).

Own bookkeeping, following the blueprint's route (Sheffield, arXiv:1012.4797, §5.4, pp. 66–72,
uses Girsanov/Williams time reversal instead).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity D3Plus

/-- The driver window: `s ↦ √κ · f(min s R)`. -/
def drvWin (κ : ℝ) (R : ℕ) (f : Iic (R : ℝ≥0) → ℝ) : ℝ≥0 → ℝ := fun s =>
  Real.sqrt κ * pathExt (R : ℝ≥0) f s

theorem measurable_drvWin (κ : ℝ) (R : ℕ) : Measurable (drvWin κ R) :=
  measurable_pi_iff.2 fun s => ((measurable_pi_apply s).comp (measurable_pathExt _)).const_mul _

/-- The local scale of the model field at level `C`. -/
def zScale (γ α r : ℝ) (ρ₀ : Measure ℂ) (C : ℝ) (x : FieldSample) (g : ℂ → ℝ) : ℝ :=
  scaleParamOn γ (zoomModel γ α C ρ₀ x g) (halfDisc r)

/-- The local canonical data of the model field at level `C`. -/
def zLoc {F : Type} (fr : ℕ → FieldSample → F) (γ α r : ℝ) (ρ₀ : Measure ℂ) (R : ℕ) (C : ℝ)
    (x : FieldSample) (g : ℂ → ℝ) : F :=
  fr R (canonicalOn γ (zoomModel γ α C ρ₀ x g) (halfDisc r))

/-- The generic `zoomPair` (local canonical data read by `fr`, log of the local scale). -/
def zoomPairG {F : Type} (fr : ℕ → FieldSample → F) (γ α L r : ℝ) (R : ℕ) (ρ₀ : Measure ℂ)
    (x : FieldSample) (g : ℂ → ℝ) : F × ℝ :=
  (fr R (canonicalOn γ (zoomModel γ α L ρ₀ x g) (halfDisc r)),
    Real.log (scaleParamOn γ (zoomModel γ α L ρ₀ x g) (halfDisc r)))

/-- **D3⁺(i) for a general local field readout `fr`** (`D3PlusIStmt` is `fr = TV.locField`,
`D3PlusIStmtRich` is `fr = locFieldFull`). -/
def D3IG {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F) : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g : Ω → ℂ → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Y' : Ω' → FieldSample),
    D3Plus.Setup γ α r ρ₀ P X Ξ g → IsQuantumWedge γ α Y' P' →
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ L in atTop,
      ∀ Φ : Ω × F → ℝ≥0∞, Measurable[(condSigma Ξ X r).prod inferInstance] Φ →
        (∀ p, Φ p ≤ 1) →
        let lhs := ∫⁻ ω, Φ (ω, fr R
          (canonicalOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r))) ∂P
        let rhs := ∫⁻ ω, ∫⁻ ω', Φ (ω, fr R (Y' ω')) ∂P' ∂P
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

/-- **D3⁺(ii) (LSC) for a general local field readout `fr`**. -/
def D3IIG {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F) : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g g' : Ω → ℂ → ℝ) (K : ℝ),
    D3Plus.Setup γ α r ρ₀ P X Ξ g → D3Plus.Setup γ α r ρ₀ P X Ξ g' →
    (∀ ω, ∀ z ∈ Metric.ball (0 : ℂ) r ∩ Hbar, |g ω z - g' ω z| ≤ K) →
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ L in atTop,
      ∀ Φ : Ω × (F × ℝ) → ℝ≥0∞, Measurable[(condSigma Ξ X r).prod inferInstance] Φ →
        (∀ p, Φ p ≤ 1) →
        let lhs := ∫⁻ ω, Φ (ω, zoomPairG fr γ α L r R ρ₀ (X ω) (g ω)) ∂P
        let rhs := ∫⁻ ω, Φ (ω, zoomPairG fr γ α L r R ρ₀ (X ω) (g' ω)) ∂P
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

variable {Ω₁ : Type} [MeasurableSpace Ω₁] {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F)

/-- The zoom-model integrand. -/
def modelInt (κ γ α r : ℝ) (ρ₀ : Measure ℂ) (R : ℕ) (X' : Ω₁ → FieldSample)
    (g : Ω₁ → ℂ → ℝ) (D : Ω₁ → ℝ≥0 → ℝ) (C : ℝ) (Γ : F × (ℝ≥0 → ℝ) → ℝ≥0∞) (ω : Ω₁) :
    ℝ≥0∞ :=
  Γ (zLoc fr γ α r ρ₀ R C (X' ω) (g ω),
    drvWin κ R (LengthMarkov.GermDensity.rescale (R : ℝ≥0) (zScale γ α r ρ₀ C (X' ω) (g ω)).toNNReal (D ω)))

/-- The model integrand read through `zoomPair` (the form tested by D3⁺(ii)). -/
def pairInt (κ γ α r : ℝ) (ρ₀ : Measure ℂ) (R : ℕ) (X' : Ω₁ → FieldSample)
    (g : Ω₁ → ℂ → ℝ) (D : Ω₁ → ℝ≥0 → ℝ) (C : ℝ) (Γ : F × (ℝ≥0 → ℝ) → ℝ≥0∞) (ω : Ω₁) :
    ℝ≥0∞ :=
  Γ ((zoomPairG fr γ α C r R ρ₀ (X' ω) (g ω)).1,
    drvWin κ R (rescaleLim (R : ℝ≥0) (Real.exp (zoomPairG fr γ α C r R ρ₀ (X' ω) (g ω)).2).toNNReal
      (D ω)))

/-- The model integrand with the germ replaced by an independent Wiener path. -/
def germInt (κ γ α r : ℝ) (ρ₀ : Measure ℂ) (R : ℕ) (W : Measure (ℝ≥0 → ℝ))
    (X' : Ω₁ → FieldSample) (g : Ω₁ → ℂ → ℝ) (C : ℝ) (Γ : F × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (ω : Ω₁) : ℝ≥0∞ :=
  ∫⁻ b, Γ (zLoc fr γ α r ρ₀ R C (X' ω) (g ω), drvWin κ R (pathRestr (R : ℝ≥0) b)) ∂W

/-- The target functional `E_{P'} E_W Γ(locField R Y, drvWin (b|_{[0,R]}))`. -/
def targetF (κ : ℝ) (R : ℕ) (W : Measure (ℝ≥0 → ℝ)) {Ω' : Type*} [MeasurableSpace Ω']
    (P' : Measure Ω') (Y : Ω' → FieldSample) : ℝ → (F × (ℝ≥0 → ℝ) → ℝ≥0∞) → ℝ≥0∞ :=
  fun _ Γ => ∫⁻ ω', ∫⁻ b, Γ (fr R (Y ω'), drvWin κ R (pathRestr (R : ℝ≥0) b)) ∂W ∂P'

/-- The D3⁺(iii) bad set at level `C` and threshold `ε`. -/
def scaleBad (γ α r : ℝ) (ρ₀ : Measure ℂ) (X' : Ω₁ → FieldSample) (g : Ω₁ → ℂ → ℝ) (ε C : ℝ) :
    Set Ω₁ :=
  {ω | ¬ (0 < zScale γ α r ρ₀ C (X' ω) (g ω) ∧ zScale γ α r ρ₀ C (X' ω) (g ω) < ε)}

variable {γ α r κ : ℝ} {ρ₀ : Measure ℂ} {Q : Measure Ω₁} [IsProbabilityMeasure Q]
  {X' : Ω₁ → FieldSample} {E' : Type} [MeasurableSpace E'] {Ξ : Ω₁ → E'}

theorem measurableSet_scaleBad {g : Ω₁ → ℂ → ℝ}
    (hm : ∀ C, Measurable fun ω => zScale γ α r ρ₀ C (X' ω) (g ω)) (ε C : ℝ) :
    MeasurableSet (scaleBad γ α r ρ₀ X' g ε C) :=
  ((measurableSet_lt measurable_const (hm C)).inter
    (measurableSet_lt (hm C) measurable_const)).compl

theorem tendsto_scaleBad {g : Ω₁ → ℂ → ℝ} (hS : D3Plus.Setup γ α r ρ₀ Q X' Ξ g)
    (hm : ∀ C, Measurable fun ω => zScale γ α r ρ₀ C (X' ω) (g ω)) {ε : ℝ} (hε : 0 < ε)
    (Cs : ℕ → ℝ) (hCs : Tendsto Cs atTop atTop) :
    Tendsto (fun n => Q (scaleBad γ α r ρ₀ X' g ε (Cs n))) atTop (𝓝 0) :=
  d3PlusIII_tendsto_prob hS hCs hε fun n => (measurableSet_scaleBad hm ε (Cs n)).nullMeasurableSet

/-- Step A: on the event `0 < scale`, the model integrand equals its `zoomPair` form. -/
theorem tvNear_model_pair {g : Ω₁ → ℂ → ℝ} (hS : D3Plus.Setup γ α r ρ₀ Q X' Ξ g)
    (hm : ∀ C, Measurable fun ω => zScale γ α r ρ₀ C (X' ω) (g ω)) (R : ℕ)
    {D : Ω₁ → ℝ≥0 → ℝ} (hDc : ∀ ω, Continuous (D ω)) :
    TVNear (fun C Γ => ∫⁻ ω, modelInt fr κ γ α r ρ₀ R X' g D C Γ ω ∂Q)
      (fun C Γ => ∫⁻ ω, pairInt fr κ γ α r ρ₀ R X' g D C Γ ω ∂Q) := by
  refine TVNear.of_eq_off _ _ (scaleBad γ α r ρ₀ X' g 1) (measurableSet_scaleBad hm 1)
    (fun C Γ h1 ω => h1 _) (fun C Γ h1 ω => h1 _) ?_
    (fun Cs hCs => tendsto_scaleBad hS hm one_pos Cs hCs)
  intro C Γ ω hω
  simp only [scaleBad, Set.mem_ofPred_eq, not_not] at hω
  simp only [modelInt, pairInt, zoomPairG, zLoc]
  have h0 : 0 < scaleParamOn γ (zoomModel γ α C ρ₀ (X' ω) (g ω)) (halfDisc r) := hω.1
  rw [Real.exp_log h0, rescaleLim_of_continuous (hDc ω)]
  rfl

/-- Step B (LSC, D3⁺(ii)): the `zoomPair` forms for two corrections at uniform distance `≤ K`. -/
theorem tvNear_pair_lsc (hII : D3IIG fr) {g g' : Ω₁ → ℂ → ℝ}
    (hS : D3Plus.Setup γ α r ρ₀ Q X' Ξ g) (hS' : D3Plus.Setup γ α r ρ₀ Q X' Ξ g') {K : ℝ}
    (hK : ∀ ω, ∀ z ∈ Metric.ball (0 : ℂ) r ∩ Hbar, |g ω z - g' ω z| ≤ K) (R : ℕ)
    {D : Ω₁ → ℝ≥0 → ℝ} (hDm : Measurable[condSigma Ξ X' r] D) :
    TVNear (fun C Γ => ∫⁻ ω, pairInt fr κ γ α r ρ₀ R X' g D C Γ ω ∂Q)
      (fun C Γ => ∫⁻ ω, pairInt fr κ γ α r ρ₀ R X' g' D C Γ ω ∂Q) := by
  intro η hη
  have h := hII γ α r ρ₀ Q X' Ξ g g' K hS hS' hK R η hη
  filter_upwards [h] with C hC Γ hΓ hΓ1
  refine hC (fun p => Γ (p.2.1, drvWin κ R (rescaleLim (R : ℝ≥0) (Real.exp p.2.2).toNNReal
    (D p.1)))) ?_ (fun p => hΓ1 _)
  have h1 : Measurable[(condSigma Ξ X' r).prod inferInstance] fun p : Ω₁ × (F × ℝ) =>
      D p.1 := hDm.comp (@measurable_fst Ω₁ (F × ℝ) (condSigma Ξ X' r) _)
  have h2 : Measurable[(condSigma Ξ X' r).prod inferInstance] fun p : Ω₁ × (F × ℝ) =>
      p.2 := @measurable_snd Ω₁ (F × ℝ) (condSigma Ξ X' r) _
  exact hΓ.comp ((measurable_fst.comp h2).prodMk ((measurable_drvWin κ R).comp
    ((measurable_rescaleLim _).comp
      ((Real.measurable_exp.comp (measurable_snd.comp h2)).real_toNNReal.prodMk h1))))

/-- Step E (D3⁺(i)): the germ-free integrand against the target. -/
theorem tvNear_germ_target (hI : D3IG fr) {g : Ω₁ → ℂ → ℝ}
    (hS : D3Plus.Setup γ α r ρ₀ Q X' Ξ g) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → FieldSample} (hY : IsQuantumWedge γ α Y P') (R : ℕ)
    {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W] :
    TVNear (fun C Γ => ∫⁻ ω, germInt fr κ γ α r ρ₀ R W X' g C Γ ω ∂Q) (targetF fr κ R W P' Y) := by
  intro η hη
  have h := hI γ α r ρ₀ Q X' Ξ g P' Y hS hY R η hη
  filter_upwards [h] with C hC Γ hΓ hΓ1
  have hF : Measurable fun y : F =>
      ∫⁻ b, Γ (y, drvWin κ R (pathRestr (R : ℝ≥0) b)) ∂W :=
    (hΓ.comp (measurable_fst.prodMk ((measurable_drvWin κ R).comp
      ((measurable_pathRestr _).comp measurable_snd)))).lintegral_prod_right'
  have h1 := hC (fun p => ∫⁻ b, Γ (p.2, drvWin κ R (pathRestr (R : ℝ≥0) b)) ∂W)
    (hF.comp (@measurable_snd Ω₁ F (condSigma Ξ X' r) _)) (fun p => by
      calc ∫⁻ b, Γ (p.2, drvWin κ R (pathRestr (R : ℝ≥0) b)) ∂W ≤ ∫⁻ _, 1 ∂W :=
            lintegral_mono fun b => hΓ1 _
        _ = 1 := by simp)
  simp only [lintegral_const, measure_univ, mul_one] at h1
  exact h1

end E5
end QuantumZipper
