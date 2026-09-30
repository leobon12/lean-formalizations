import QuantumZipper.Proofs.Thm18.ASepPathDefs
import QuantumZipper.Proofs.Thm18.G1PkgPath
import QuantumZipper.Proofs.RS.BMModulus
import QuantumZipper.Proofs.RS.RealAlive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-T: from the per-path / iterated A-sep statement to `G4SepRep0Stmt`

* `g4SepConcl0_congr_dataFull`: the `τ' = 0` conclusion depends on the field only through its
  circle coordinates (copy of `G4Core.g4SepConcl_congr_dataFull`).
* `codeP`: the Polish code of a path (its values at the nonnegative rationals); two continuous
  paths with the same code agree (`eq_of_codeP_eq`).
* `GoodC γ ⊆ (ℕ → ℝ) × (ℕ → ℝ)`: the good (path code, circle coordinates) pairs.
  `GoodCMeasStmt`: this set is null-measurable for every finite measure (deterministic
  descriptive-set node; expected coanalytic, `G4Core.nullMeasurableSet_forall`).
* `g4SepRep0Stmt_of_iter`: `G4SepRep0Stmt` from `GoodCMeasStmt` and the iterated statement
  `G4SepIter0Stmt` (a.s. in the Brownian sample, a.s. in the wedge sample, the conclusion holds).
  Fubini for the completed product measure (mathlib `measure_prod_null_of_ae_null`,
  `ae_ae_of_ae_prod`), measurable hull of a null-measurable set.
* `ae_drvGood_drive`: a Brownian driver `√κ B`, `κ = γ² < 4`, is a.s. `DrvGood` (continuity,
  `W 0 = 0`; Hölder-1/4 from `RS.bm_holder` (Lévy modulus); real points alive `RS.ae_real_alive`,
  Rohde–Schramm Lemma 6.2).
* `g4SepRep0Stmt_of_path`: `G4SepPath0Stmt → GoodCMeasStmt → G4SepRep0Stmt`.

Own elementary bookkeeping (measurability the paper leaves implicit; Sheffield arXiv:1012.4797
works with the product law of the independent pair (driver, wedge) throughout §1.6).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-! ## Congruence -/

theorem g4SepConcl0_congr_avgReg_tr {γ : ℝ} {y y' : FieldSample} (h : avgReg y = avgReg y')
    (W : ℝ → ℝ) : G4SepConcl0 γ (y, W) ↔ G4SepConcl0 γ (y', W) := by
  have e : ∀ τ, unzippedField γ (y, W) τ = unzippedField γ (y', W) τ := fun τ =>
    Factorization.coordChange_congr h _ _
  simp only [G4SepConcl0, BackSupportI, BackSepI, e]

theorem g4SepConcl0_congr_coordsFull {γ : ℝ} {y y' : FieldSample}
    (h : CoordsFull.coordsFull y = CoordsFull.coordsFull y') (W : ℝ → ℝ) :
    G4SepConcl0 γ (y, W) ↔ G4SepConcl0 γ (y', W) :=
  g4SepConcl0_congr_avgReg_tr (CoordsFull.avgReg_congr_full h) W

/-! ## The code of a path -/

/-- An enumeration of the rationals. -/
def enumRat : ℕ → ℚ := (exists_surjective_nat ℚ).choose

/-- The `n`-th code time (a nonnegative rational). -/
def qs (n : ℕ) : ℝ≥0 := ((enumRat n : ℚ) : ℝ).toNNReal

/-- The Polish code of a path: its values at the code times. -/
def codeP (x : ℝ≥0 → ℝ) : ℕ → ℝ := fun n => x (qs n)

theorem measurable_codeP : Measurable codeP :=
  measurable_pi_iff.2 fun n => measurable_pi_apply (qs n)

theorem eq_of_codeP_eq {x x' : ℝ≥0 → ℝ} (hx : Continuous x) (hx' : Continuous x')
    (h : codeP x = codeP x') : x = x' := by
  have hd : DenseRange fun n => ((enumRat n : ℚ) : ℝ) :=
    Rat.denseRange_cast.comp (exists_surjective_nat ℚ).choose_spec.denseRange
      Rat.continuous_coe_real
  have e := hd.equalizer (hx.comp continuous_real_toNNReal) (hx'.comp continuous_real_toNNReal)
    (funext fun n => congrFun h n)
  funext t
  have := congrFun e (t : ℝ)
  simpa using this

/-! ## The good code set and the transfer -/

/-- The good pairs (path code, circle coordinates). -/
def GoodC (γ : ℝ) : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | ∀ x : ℝ≥0 → ℝ, Continuous x → codeP x = q.1 → ∀ y : FieldSample,
    CoordsFull.coordsFull y = q.2 → G4SepConcl0 γ (y, pathDrive (γ ^ 2) x)}

/-- **Remaining measurability node**: the good code set is null-measurable for every finite
measure on the (Polish) code space. -/
def GoodCMeasStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsFiniteMeasure ρ →
    NullMeasurableSet (GoodC γ) ρ

/-- The iterated form of A-sep at `τ' = 0`: a.s. in the Brownian sample, a.s. in the wedge
sample, the conclusion holds. -/
def G4SepIter0Stmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P', G4SepConcl0 γ (wedgeRep γ X A ω', drive (γ ^ 2) B ω)

/-- **Transfer**: the iterated statement and the measurability node give `G4SepRep0Stmt`. -/
theorem g4SepRep0Stmt_of_iter (hM : GoodCMeasStmt) (hI : G4SepIter0Stmt) : G4SepRep0Stmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA
  have hgm : AEMeasurable (pathOf B) P := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hαQ, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, rfl⟩
  have hdm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  set cw : Ω' → ℕ → ℝ := fun ω' => CoordsFull.coordsFull (wedgeRep γ X A ω') with hcw
  have hwm : AEMeasurable cw P' := measurable_fst.comp_aemeasurable hdm
  set cd : (ℝ≥0 → ℝ) → ℕ → ℝ := fun e => codeP (G1Pkg.pathReg e) with hcd_def
  have hcd : Measurable cd := measurable_codeP.comp G1Pkg.pathReg_spec.1
  set μ : Measure (ℕ → ℝ) := (P.map (pathOf B)).map cd with hμ
  set ν : Measure (ℕ → ℝ) := P'.map cw with hν
  have hG : NullMeasurableSet (GoodC γ) (μ.prod ν) := hM γ hγ hγ2 _ inferInstance
  obtain ⟨F, hFG, hFm, hFae⟩ := hG.exists_measurable_subset_ae_eq
  obtain ⟨T, hTG, hTm, hTae⟩ := hG.compl.exists_measurable_subset_ae_eq
  -- a.e. section of `T` is null
  have h1 : ∀ᵐ k ∂μ, ν (Prod.mk k ⁻¹' T) = 0 := by
    have hS : MeasurableSet {k : ℕ → ℝ | ν (Prod.mk k ⁻¹' T) = 0} :=
      measurable_measure_prodMk_left hTm (measurableSet_singleton 0)
    rw [hμ, ae_map_iff hcd.aemeasurable hS]
    refine (ae_map_iff hgm (hcd hS)).2 ?_
    filter_upwards [hI γ hγ hγ2 P B hB P' X A hX hA hXA, hB.cont] with ω hω hc
    have hc' : Continuous (pathOf B ω) := hc
    have hreg : G1Pkg.pathReg (pathOf B ω) = pathOf B ω := G1Pkg.pathReg_spec.2.2 _ hc'
    show ν (Prod.mk (cd (pathOf B ω)) ⁻¹' T) = 0
    rw [hν, Measure.map_apply_of_aemeasurable hwm (measurable_prodMk_left hTm)]
    refine measure_mono_null ?_ (ae_iff.1 hω)
    intro ω' hω' hC
    refine hTG hω' ?_
    intro x hx hxk y hy
    have hxe : x = pathOf B ω := by
      refine eq_of_codeP_eq hx hc' ?_
      rw [hxk]; simp only [hcd_def, hreg]
    subst hxe
    exact (g4SepConcl0_congr_coordsFull hy _).2 hC
  have h2 : μ.prod ν T = 0 := Measure.measure_prod_null_of_ae_null hTm h1
  have h3 : ∀ᵐ q ∂μ.prod ν, q ∈ F := by
    rw [ae_iff]
    exact (measure_congr (hFae.compl.trans hTae.symm)).trans h2
  have h4 := Measure.ae_ae_of_ae_prod h3
  refine ⟨{p : G1PathData | (cd p.1, p.2.1) ∈ F},
    hFm.preimage ((hcd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)), ?_, ?_⟩
  · rintro p hp hc y hy
    have hreg : G1Pkg.pathReg p.1 = p.1 := G1Pkg.pathReg_spec.2.2 _ hc
    have hmem := hFG hp
    refine hmem p.1 hc (by simp only [hcd_def, hreg]) y ?_
    rw [← hy]; rfl
  · have h5 := ae_of_ae_map hcd.aemeasurable h4
    filter_upwards [h5] with e he
    exact ae_of_ae_map hwm he

/-! ## Part (a): the Brownian driver is good -/

/-- **A Brownian driver is a.s. good** (`κ = γ² < 4`). -/
theorem ae_drvGood_drive {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, DrvGood (drive (γ ^ 2) B ω) := by
  have hκ4 : γ ^ 2 ≤ 4 := by nlinarith
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    RS.bm_holder hB (a := 1 / 4) (by norm_num),
    RS.ae_real_alive hB (κ := γ ^ 2) (by positivity) hκ4] with ω hc h0 hH hA
  refine ⟨continuous_const.mul (hc.comp continuous_real_toNNReal), ?_, ?_, hA⟩
  · simp only [drive, Real.toNNReal_zero]
    rw [h0]; simp
  · intro T hT
    obtain ⟨C, hC⟩ := hH T.toNNReal
    refine ⟨1 / 4, √(γ ^ 2) * max C 0, by norm_num, by norm_num, by positivity, ?_⟩
    have key : ∀ t t' : ℝ, 0 ≤ t → t ≤ t' → t' ≤ T → t' - t ≤ 1 / 2 →
        |drive (γ ^ 2) B ω t - drive (γ ^ 2) B ω t'| ≤
          √(γ ^ 2) * max C 0 * |t - t'| ^ (1 / 4 : ℝ) := by
      intro t t' ht0 htt' ht'T hd
      rcases eq_or_lt_of_le htt' with he | hlt
      · subst he; simp
      set s : ℝ≥0 := (t' - t).toNNReal with hs
      have hs' : (s : ℝ) = t' - t := Real.coe_toNNReal _ (by linarith)
      have hs0 : 0 < s := by rw [← NNReal.coe_pos, hs']; linarith
      have hs1 : s ≤ 1 / 2 := by
        rw [← NNReal.coe_le_coe, hs']; push_cast; linarith
      have htT : t.toNNReal ≤ T.toNNReal := Real.toNNReal_le_toNNReal (by linarith)
      have hb := hC t.toNNReal htT s hs0 hs1
      have hsum : t.toNNReal + s = t'.toNNReal := by
        apply NNReal.eq
        push_cast
        rw [hs', Real.coe_toNNReal _ ht0, Real.coe_toNNReal _ (by linarith)]
        ring
      rw [hsum] at hb
      have habs : |t - t'| = (s : ℝ) := by rw [hs', abs_sub_comm, abs_of_nonneg (by linarith)]
      simp only [drive]
      rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), habs, abs_sub_comm, mul_assoc]
      refine mul_le_mul_of_nonneg_left (hb.trans ?_) (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    intro t ht t' ht' hd
    rcases le_total t t' with h | h
    · exact key t t' ht.1 h ht'.2 (by rw [abs_le] at hd; linarith [hd.1])
    · have := key t' t ht'.1 h ht.2 (by rw [abs_le] at hd; linarith [hd.2])
      rw [abs_sub_comm t' t, abs_sub_comm (drive (γ ^ 2) B ω t')] at this
      exact this

/-! ## The per-path form -/

theorem g4SepIter0Stmt_of_path (h : G4SepPath0Stmt) : G4SepIter0Stmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA
  filter_upwards [ae_drvGood_drive hγ hγ2 hB] with ω hω
  exact h γ hγ hγ2 P' X A hX hA hXA _ hω

end ASep
end QuantumZipper
