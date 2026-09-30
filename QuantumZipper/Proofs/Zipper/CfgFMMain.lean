import QuantumZipper.Proofs.Zipper.CfgFMMeas
import QuantumZipper.Proofs.Zipper.CfgBatchDens
import QuantumZipper.Proofs.Thm18.G1FMAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FIRSTMODE (5): `CfgFirstModeStmt` from the fixed-driver variance node

Assembly (`CfgFM.cfgFirstMode_of_var`):

* the explicit regular witness `ZE(path, X) ∘ pr4 + Ddet` of the unzipped field for all
  `t ∈ [0, T']` (`CfgFM.ae_regWith_ZE`, `T' = max T 1`);
* for a fixed good path `f`, `CfgFMVarStmt` and the Hölder block chain give summable block
  probabilities of the first modes of `ZE(f, X)` (`CfgFM.fmH_block_summable`, Borel–Cantelli);
  the block events are measurable on path × field space (`CfgFM.measurableSet_fmHBlockEvent`), so
  independence of the driver and the field transfers the statement to the Brownian driver
  (`CharFun.ae_indep`); then `CfgFM.fmH_bound_of_eventually` gives `C/√τ`;
* the deterministic part is bounded (`CfgFM.abs_ddet_le`), so its first mode is `≤ 2π M`.

Then `cfgDensStmt_of_var : … → CfgDensStmt` by `cfgDensStmt_of_firstMode`. Bookkeeping; sources
as in the component files (Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; Duplantier–Sheffield,
Invent. Math. 185 (2011), Prop. 3.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal Real

namespace QuantumZipper.E6
namespace CfgFM

open RegUnif RegCont RegSample CharFun B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem measurableSet_eventually_notMem {α : Type*} [MeasurableSpace α] {A : ℕ → Set α}
    (hA : ∀ n, MeasurableSet (A n)) : MeasurableSet {x | ∀ᶠ n in atTop, x ∉ A n} := by
  have e : {x | ∀ᶠ n in atTop, x ∉ A n} = ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), (A n)ᶜ := by
    ext x; simp [Filter.eventually_atTop]
  rw [e]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => (hA n).compl

/-- **CFG-FIRSTMODE from the fixed-driver variance node.** -/
theorem cfgFirstMode_of_var (κ T : ℝ) (hV : ∀ T' : ℝ, ∀ hT' : 0 < T', CfgFMVarStmt κ T' hT')
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    CfgFirstModeStmt κ T P B X := by
  set T' := max T 1 with hT'def
  have hT' : 0 < T' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨B', hB'm, hB'c, hind', hgood, hreg⟩ := ae_regWith_ZE κ (Real.sqrt κ) hB hX hind hT'
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  set E : Set (C(Icc (0 : ℝ) T', ℝ) × FieldSample) :=
    ((GoodP hT'.le (1 / 3))ᶜ ×ˢ univ) ∪
      {px | ∀ m : ℕ, ∀ᶠ n in atTop, px ∉ fmHBlockEvent (fZE hT'.le κ) T' m n} with hEdef
  have hE : MeasurableSet E :=
    ((measurableSet_GoodP hT'.le _).compl.prod MeasurableSet.univ).union
      (by
        have := MeasurableSet.iInter fun m =>
          measurableSet_eventually_notMem fun n => measurableSet_fmHBlockEvent hT'.le κ m n
        convert this using 1
        ext px; simp)
  have hfib : ∀ f, ∀ᵐ ω ∂P, (f, X ω) ∈ E := by
    intro f
    by_cases hf : f ∈ GoodP hT'.le (1 / 3)
    · have hvar := hV T' hT' P X hX f hf
      filter_upwards [ae_all_iff.2 fun m => ae_eventually_notMem (fmH_block_summable hvar m)]
        with ω hω
      exact Or.inr fun m => hω m
    · exact ae_of_all _ fun ω => Or.inl ⟨hf, trivial⟩
  have hE' := ae_indep (measurable_pathC T' hB'm hB'c) hXm hind' hE hfib
  filter_upwards [hE', hgood, hreg] with ω hEω hg hr t ht htT K hK hKH
  rcases hEω with h | h
  · exact absurd hg h.1
  have htT' : t ∈ Icc (0 : ℝ) T' := ⟨ht, htT.trans (le_max_left _ _)⟩
  obtain ⟨C₁, τ₁, hτ₁, hb₁⟩ := fmH_bound_of_eventually h K hK hKH
  obtain ⟨M, τ₂, hM, hτ₂, hτ₂K, hbM⟩ := abs_ddet_le hr.1 hr.2.1 κ (Real.sqrt κ) T' hK hKH
  have hdet := detContStmt_holds κ (Real.sqrt κ) T' (drive κ B ω) hr.1 hr.2.1
  set px := (pathC T' B' hB'c ω, X ω) with hpx
  refine ⟨C₁ + M * (2 * π), min (min τ₁ τ₂) 1, lt_min (lt_min hτ₁ hτ₂) one_pos,
    fun w hw τ hτ s hs => ?_⟩
  have hτ0 : 0 < τ := hτ.1
  have hτ1 : τ < τ₁ := hτ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hτ2 : τ < τ₂ := hτ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hτ3 : τ < 1 := hτ.2.trans_le (min_le_right _ _)
  have hs0 : 0 < s := hs.1
  have hwτ : τ < w.im := hτ2.trans (hτ₂K w hw)
  set v : ℝ → ℂ := fun θ => w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvH : ∀ θ, v θ ∈ Hbar := fun θ => Thm18Asm.G1FM.circ_mem_Hbar hτ0.le hwτ θ
  have hvc : Continuous v := by rw [hv]; fun_prop
  have hsplit : ∀ θ, evalReg (zipCapDown (Real.sqrt κ) t (cfg κ B X ω)).1
      (foldedCircle (v θ) s) = fZE hT'.le κ px t (v θ, s) +
        Ddet κ (Real.sqrt κ) (drive κ B ω) (t, (v θ, s)) := by
    intro θ
    exact (hr.2.2 t htT').evalReg_fc_of_mem (hvH θ) hs0
  have hc1 : Continuous fun θ : ℝ => fZE hT'.le κ px t (v θ, s) :=
    (continuous_ZE hT'.le κ px).comp ((continuous_pr_fst s t).comp hvc)
  have hc2 : Continuous fun θ : ℝ => Ddet κ (Real.sqrt κ) (drive κ B ω) (t, (v θ, s)) :=
    hdet.comp_continuous (by fun_prop) fun θ => ⟨htT', hvH θ, show (0 : ℝ) < s from hs0⟩
  have hint : (∫ θ in (0 : ℝ)..(2 * π),
      ((evalReg (zipCapDown (Real.sqrt κ) t (cfg κ B X ω)).1
          (foldedCircle (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) s) : ℝ) : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I)) =
      D3Plus.fmInt (fZE hT'.le κ px t) w τ s +
        ∫ θ in (0 : ℝ)..(2 * π), ((Ddet κ (Real.sqrt κ) (drive κ B ω) (t, (v θ, s)) : ℝ) : ℂ) *
          Complex.exp ((θ : ℂ) * Complex.I) := by
    unfold D3Plus.fmInt
    rw [← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [show w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = v θ from rfl, hsplit θ]
      push_cast
      ring
    · exact ((Complex.continuous_ofReal.comp hc1).mul (by fun_prop)).intervalIntegrable _ _
    · exact ((Complex.continuous_ofReal.comp hc2).mul (by fun_prop)).intervalIntegrable _ _
  have hD : ‖∫ θ in (0 : ℝ)..(2 * π),
      ((Ddet κ (Real.sqrt κ) (drive κ B ω) (t, (v θ, s)) : ℝ) : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ M * (2 * π) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π) (C := M)
      (f := fun θ : ℝ => ((Ddet κ (Real.sqrt κ) (drive κ B ω) (t, (v θ, s)) : ℝ) : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I)) fun θ _ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact hbM t htT' w hw (v θ) ((Thm18Asm.G1FM.dist_circ hτ0.le θ).le.trans hτ2.le) s hs0
        (hs.2.trans hτ2).le
    rwa [sub_zero, abs_of_pos (by positivity)] at this
  have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  have hsq1 : Real.sqrt τ ≤ 1 := Real.sqrt_le_one.mpr hτ3.le
  have hle : M * (2 * π) ≤ M * (2 * π) / Real.sqrt τ :=
    le_div_self (by positivity) hsq hsq1
  rw [hint, add_div]
  calc _ ≤ ‖D3Plus.fmInt (fZE hT'.le κ px t) w τ s‖ + M * (2 * π) :=
        (norm_add_le _ _).trans (add_le_add le_rfl hD)
    _ ≤ _ := add_le_add (hb₁ w hw τ ⟨hτ0, hτ1⟩ s hs t htT') hle

/-- **`CfgDensStmt` from the fixed-driver variance node.** -/
theorem cfgDensStmt_of_var (κ T : ℝ) (hV : ∀ T' : ℝ, ∀ hT' : 0 < T', CfgFMVarStmt κ T' hT')
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    CfgDensStmt κ T P B X :=
  cfgDensStmt_of_firstMode hB hX hind (cfgFirstMode_of_var κ T hV hB hX hind)

end CfgFM
end QuantumZipper.E6
