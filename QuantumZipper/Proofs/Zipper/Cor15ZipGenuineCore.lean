import QuantumZipper.Proofs.Zipper.Cor15GrpHalves
import QuantumZipper.Proofs.Zipper.Cor15LastZc
import QuantumZipper.Proofs.Zipper.Cor15LastMain
import QuantumZipper.Proofs.Zipper.Cor15TdensMain
import QuantumZipper.Proofs.Zipper.Cor15MarkovField

/-!
# D35 core piece 2: `Cor15ZipGenuineStmt`, the driver half

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18),
clause (a): the zipped configuration `U_a c` is again a genuine configuration. Decision D35
(`DECISIONS.md`): the second half of the core `Cor15GenuineStmt`.

For a genuine configuration `c = (𝔥₀ + X, √κ B)` (`IsGrpSetup`), the driver of `U_a c` is
(`Zipper/Maps.lean`)

  `s ↦ W'(a − s) − W'(a)` for `s ≤ a`,  `s ↦ W(s − a) − W'(a)` for `s ≥ a`,

where `W = √κ B` and `W' = weldDriver γ (c.1) a`. This file constructs the candidate Brownian
motion on the *same* probability space,

  `B' u = (√κ)⁻¹ · (U_a c).2 u`  (`u ≥ 0`),

i.e. the reverse of the read welding driver on `[0,a]`, concatenated with `B(· − a)` shifted, and
proves `IsBrownianReal B' P`:

* **`continuous_zipDrvGlue`** / **`zipDrv_eq_glue`**: on the good set of the measurable driver
  reading `exists_readVp` (Corollary 1.5's use of Theorem 1.4: `weldDriver` is choice-based, so
  one reads it measurably), `B'` is the gluing of the continuous reverse driver `V(a − ·) − V a`
  with the continuous shifted Brownian driver, matched at `u = a` because `V 0 = 0` and
  `B 0 = 0` a.s. Hence `B'` has a.s. continuous paths (own elementary argument).
* **`map_zipDrv_eq_pathOf`** (Corollary 1.5(a) at `t = a > 0`,
  `theorem1_5a_pos_of_theorem1_3_of_tdensReg`, marginal of `configLawMod0` to the driver): the
  law of `B'` is the law of `B` on `[0,∞)`.
* **`isPreBrownianReal_of_map_pathOf_eq`** (`IsPreBrownianReal` is a finite-dimensional-law
  property, mathlib `BrownianMotion.Basic`) and **`isBrownianReal_zipDrv`**: with the a.s.
  continuity above, `IsBrownianReal B' P`.

Input: `h13 : theorem1_3` (through Theorem 1.4's a.s. uniqueness of the welding driver, used by
the reading); the regularity input of Corollary 1.5(a) at `t > 0` is the proved
`cor15TdensRegStmt` (`Cor15TdensMain`).
The field half and the assembly into `Cor15ZipGenuineStmt` are in `Cor15ZipGenuine.lean`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- The field of the zipped configuration `U_a c`. -/
def zipFld (κ a : ℝ) (c : FieldSample × (ℝ → ℝ)) : FieldSample :=
  (zipCapUp (Real.sqrt κ) a c).1

/-- The normalized driver of the zipped configuration on `[0,∞)`: the candidate `B'`. -/
def zipDrv (κ a : ℝ) (c : FieldSample × (ℝ → ℝ)) : ℝ≥0 → ℝ :=
  fun u => (Real.sqrt κ)⁻¹ * (zipCapUp (Real.sqrt κ) a c).2 (u : ℝ)

/-- The second component of `grpCfg` is `√κ B`. -/
theorem grpCfg_snd (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) (s : ℝ) :
    (grpCfg κ B X ω).2 s = Real.sqrt κ * B s.toNNReal ω := rfl

/-! ## Continuity of the glued driver on the good set of the driver reading -/

/-- The glued driver of the zipped configuration: the reverse of the read welding driver `V` on
`[0,a]`, then the shifted configuration driver. It is the pointwise value of `zipDrv` on the
event where the reading `V` agrees with `weldDriver` on `[0,a]`. -/
def zipDrvGlue (κ a : ℝ) (V : ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ :=
  fun u => (Real.sqrt κ)⁻¹ *
    (if (u : ℝ) ≤ a then V (a - (u : ℝ)) - V a else drive κ B ω ((u : ℝ) - a) - V a)

/-- **The glued driver is continuous** when the reverse reading `V` is continuous, `V 0 = 0`, the
Brownian path is continuous and `B 0 = 0`: the two branches match at `u = a`. -/
theorem continuous_zipDrvGlue {κ a : ℝ} {V : ℝ → ℝ} {ω : Ω}
    (hVc : Continuous V) (hV0 : V 0 = 0) (hBc : Continuous fun u : ℝ≥0 => B u ω)
    (hB0 : B 0 ω = 0) : Continuous (zipDrvGlue κ a V B ω) := by
  have h1 : Continuous fun u : ℝ≥0 => V (a - (u : ℝ)) - V a :=
    (hVc.comp (continuous_const.sub continuous_subtype_val)).sub continuous_const
  have h2 : Continuous fun u : ℝ≥0 => drive κ B ω ((u : ℝ) - a) - V a := by
    simp only [drive]
    exact (continuous_const.mul (hBc.comp
      (continuous_real_toNNReal.comp (continuous_subtype_val.sub continuous_const)))).sub
        continuous_const
  have h : Continuous (fun u : ℝ≥0 => if (u : ℝ) ≤ a then V (a - (u : ℝ)) - V a
      else drive κ B ω ((u : ℝ) - a) - V a) :=
    Continuous.if_le (f := fun u : ℝ≥0 => (u : ℝ)) (g := fun _ : ℝ≥0 => a)
      h1 h2 continuous_subtype_val continuous_const fun u hu => by
        have hu' : (u : ℝ) = a := hu
        rw [hu', sub_self, hV0, drive, Real.toNNReal_zero, hB0, mul_zero]
  exact continuous_const.mul h

/-- **On the good set of the reading, `B'` is the glued driver.** If `V` agrees with the
welding driver of the zipped field on `[0,a]`, then `zipDrv` is `zipDrvGlue V`: on `[0,a]`
`zipCapUp`'s driver is the time-reversal of `W'`, beyond `a` it uses `W' a` only. -/
theorem zipDrv_eq_glue {κ a : ℝ} {x : FieldSample} {ω : Ω} {V : ℝ → ℝ} (ha : 0 ≤ a)
    (hV : EqOn (weldDriver (Real.sqrt κ) x a) V (Icc 0 a)) :
    zipDrv κ a (x, drive κ B ω) = zipDrvGlue κ a V B ω := by
  funext u
  have hu : (0 : ℝ) ≤ (u : ℝ) := u.2
  have hmax : max (u : ℝ) 0 = (u : ℝ) := max_eq_left hu
  rw [zipDrv, zipDrvGlue]
  simp only [zipCapUp, hmax]
  by_cases hle : (u : ℝ) ≤ a
  · simp only [hle, ↓reduceIte]
    rw [hV (show a - (u : ℝ) ∈ Icc 0 a from ⟨by linarith, by linarith⟩),
      hV (show a ∈ Icc 0 a from ⟨ha, le_rfl⟩)]
  · simp only [hle, ↓reduceIte]
    rw [hV (show a ∈ Icc 0 a from ⟨ha, le_rfl⟩)]

/-! ## Measurability and law of the zipped driver -/

/-- **The zipped driver is a.e.-measurable**: it is the second component of `mod0Data ∘ U_a c`,
whose a.e.-measurability is `aemeasurable_mod0Data_zipCapUp_c` (`hZc`, from B1-FULL). -/
theorem aemeasurable_zipDrv (h13 : theorem1_3) {κ a : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (ha : 0 < a) :
    AEMeasurable (fun ω => zipDrv κ a (grpCfg κ B X ω)) P := by
  have h := aemeasurable_mod0Data_zipCapUp_c h13 RS.rohdeSchrammSimple hκ hκ4 hB hX hind ha
  have h2 : AEMeasurable
      (fun ω => fun s : ℝ≥0 => (zipCapUp (Real.sqrt κ) a (grpCfg κ B X ω)).2 (s : ℝ)) P := h.snd
  have hsm : Measurable fun p : ℝ≥0 → ℝ => fun u : ℝ≥0 => (Real.sqrt κ)⁻¹ * p u :=
    measurable_pi_iff.2 fun u => measurable_const.mul (measurable_pi_apply u)
  exact hsm.comp_aemeasurable h2

/-- **The genuine side of the driver law**: the driver of the genuine configuration is a
measurable function of the Brownian path. -/
theorem aemeasurable_drv_grpCfg (hB : IsBrownianReal B P) (κ : ℝ) (X : Ω → FieldSample) :
    AEMeasurable (fun ω => fun s : ℝ≥0 => (grpCfg κ B X ω).2 (s : ℝ)) P := by
  have hsm : Measurable fun p : ℝ≥0 → ℝ => fun s : ℝ≥0 => Real.sqrt κ * p s :=
    measurable_pi_iff.2 fun s => measurable_const.mul (measurable_pi_apply s)
  have h := hsm.comp_aemeasurable (IsBrownianReal.aemeasurable_pathOf hB)
  refine h.congr ?_
  filter_upwards with ω
  funext s
  show Real.sqrt κ * B s ω = (grpCfg κ B X ω).2 (s : ℝ)
  rw [grpCfg_snd, Real.toNNReal_coe]

/-- **The law of the zipped driver** (Corollary 1.5(a) at `t = a > 0`, marginal of
`configLawMod0` to the driving function): `(√κ)⁻¹ · (U_a c).2` has the law of the Brownian
motion on `[0,∞)`, i.e. of the original driver `B`. -/
theorem map_zipDrv_eq_pathOf (h13 : theorem1_3) {κ a : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ha : 0 < a) :
    P.map (fun ω => zipDrv κ a (grpCfg κ B X ω)) = P.map (pathOf B) := by
  have h := theorem1_5a_pos_of_theorem1_3_of_tdensReg h13 cor15TdensRegStmt κ hκ hκ4 P B X hB hX hind a
    ha
  rw [configLawMod0_eq_map, configLawMod0_eq_map] at h
  have hZm : AEMeasurable
      (fun ω => mod0Data (zipCap (Real.sqrt κ) a (grpCfg κ B X ω))) P := by
    rw [zipCap_of_nonneg ha.le]
    exact aemeasurable_mod0Data_zipCapUp_c h13 RS.rohdeSchrammSimple hκ hκ4 hB hX hind ha
  have hpair : Measurable (fun ω => fun ρ : TestFun0 H =>
      pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1) := by
    refine measurable_pi_iff.2 fun ρ => ?_
    have hc : ∀ μ : Measure ℂ, Measurable fun ω => (ofFun (h0rev κ) + X ω) μ :=
      fun μ => measurable_const.add (hX.measurable_coord μ)
    unfold pairRaw
    exact (hc _).sub (hc _)
  have hCm : AEMeasurable (fun ω => mod0Data (grpCfg κ B X ω)) P :=
    hpair.aemeasurable.prodMk (aemeasurable_drv_grpCfg hB κ X)
  have hdrv : P.map (fun ω => (mod0Data (zipCap (Real.sqrt κ) a (grpCfg κ B X ω))).2) =
      P.map (fun ω => (mod0Data (grpCfg κ B X ω)).2) := by
    have h' := congrArg (fun μ : Measure ((TestFun0 H → ℝ) × (ℝ≥0 → ℝ)) => μ.map Prod.snd) h
    rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hZm,
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hCm] at h'
    rw [show (Prod.snd ∘ fun ω => mod0Data (zipCap (Real.sqrt κ) a (grpCfg κ B X ω))) =
        fun ω => (mod0Data (zipCap (Real.sqrt κ) a (grpCfg κ B X ω))).2 from rfl,
      show (Prod.snd ∘ fun ω => mod0Data (grpCfg κ B X ω)) =
        fun ω => (mod0Data (grpCfg κ B X ω)).2 from rfl] at h'
    exact h'
  have hgm : Measurable fun p : ℝ≥0 → ℝ => fun u : ℝ≥0 => (Real.sqrt κ)⁻¹ * p u :=
    measurable_pi_iff.2 fun u => measurable_const.mul (measurable_pi_apply u)
  have hscale := congrArg
    (fun μ : Measure (ℝ≥0 → ℝ) => μ.map fun p : ℝ≥0 → ℝ => fun u : ℝ≥0 =>
      (Real.sqrt κ)⁻¹ * p u) hdrv
  rw [AEMeasurable.map_map_of_aemeasurable hgm.aemeasurable hZm.snd,
    AEMeasurable.map_map_of_aemeasurable hgm.aemeasurable hCm.snd] at hscale
  have eL : (fun ω => zipDrv κ a (grpCfg κ B X ω)) = fun (ω : Ω) (u : ℝ≥0) =>
      (Real.sqrt κ)⁻¹ * (mod0Data (zipCap (Real.sqrt κ) a (grpCfg κ B X ω))).2 u := by
    funext ω u
    simp only [zipDrv, mod0Data]
    rw [zipCap_of_nonneg ha.le]
  have eR : pathOf B = fun (ω : Ω) (u : ℝ≥0) =>
      (Real.sqrt κ)⁻¹ * (mod0Data (grpCfg κ B X ω)).2 u := by
    funext ω u
    show B u ω = (Real.sqrt κ)⁻¹ * (grpCfg κ B X ω).2 (u : ℝ)
    rw [grpCfg_snd, Real.toNNReal_coe, inv_mul_cancel_left₀ (Real.sqrt_pos.2 hκ).ne']
  rw [eL, eR]
  simpa only [Function.comp_def] using hscale

/-! ## `IsPreBrownianReal` transfers along an identity of laws of the process -/

/-- **`IsPreBrownianReal` is a property of the finite-dimensional laws** (`mathlib` defines it
through `HasLaw _ (projectiveFamily I)`), so a process with a.e.-measurable paths and the law of
a pre-Brownian motion is itself pre-Brownian. -/
theorem isPreBrownianReal_of_map_pathOf_eq {B' : ℝ≥0 → Ω → ℝ} (hm : AEMeasurable (pathOf B') P)
    (hmB : AEMeasurable (pathOf B) P) (hlaw : P.map (pathOf B') = P.map (pathOf B))
    (hB : IsPreBrownianReal B P) : IsPreBrownianReal B' P := by
  refine ⟨fun I => ?_⟩
  have hIm : Measurable fun p : ℝ≥0 → ℝ => (I.restrict p : I → ℝ) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℝ≥0)
  refine ⟨hIm.comp_aemeasurable hm, ?_⟩
  · have hg : AEMeasurable (fun p : ℝ≥0 → ℝ => (I.restrict p : I → ℝ))
        (Measure.map (pathOf B') P) := hIm.aemeasurable
    have hgB : AEMeasurable (fun p : ℝ≥0 → ℝ => (I.restrict p : I → ℝ))
        (Measure.map (pathOf B) P) := hIm.aemeasurable
    rw [show (fun ω => I.restrict (B' · ω)) =
        (fun p : ℝ≥0 → ℝ => (I.restrict p : I → ℝ)) ∘ pathOf B' from rfl,
      ← AEMeasurable.map_map_of_aemeasurable hg hm, hlaw,
      AEMeasurable.map_map_of_aemeasurable hgB hmB]
    exact (hB.hasLaw I).map_eq

/-! ## `IsBrownianReal` of the zipped driver -/

/-- **`Cor15ZipGenuineStmt`'s Brownian half.** The normalized zipped driver
`(u, ω) ↦ (√κ)⁻¹ (U_a c).2 u` is a Brownian motion on the same probability space: its
finite-dimensional laws are those of `B` (`map_zipDrv_eq_pathOf`) and, on the good set of the
driver reading, its paths are the continuous glued driver (`exists_readVp`,
`continuous_zipDrvGlue`). -/
theorem isBrownianReal_zipDrv (h13 : theorem1_3) {κ a : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hS : IsGrpSetup P B X) (ha : 0 < a) :
    IsBrownianReal (fun u ω => zipDrv κ a (grpCfg κ B X ω) u) P := by
  have hlaw := map_zipDrv_eq_pathOf h13 hκ hκ4 hS.1 hS.2.1 hS.2.2 ha
  have hm : AEMeasurable (pathOf fun u ω => zipDrv κ a (grpCfg κ B X ω) u) P :=
    aemeasurable_zipDrv h13 hκ hκ4 hS.1 hS.2.1 hS.2.2 ha
  refine ⟨isPreBrownianReal_of_map_pathOf_eq hm (IsBrownianReal.aemeasurable_pathOf hS.1) hlaw
    hS.1.toIsPreBrownianReal, ?_⟩
  obtain ⟨Vp, hVc, hV0, -, A, -, hdet, -, hcA⟩ :=
    exists_readVp h13 RS.rohdeSchrammSimple hκ hκ4 hS.1 hS.2.1 hS.2.2 ha
  filter_upwards [hcA, hS.1.cont, hS.1.eval_zero_ae_eq_zero] with ω hA hBc hB0
  show Continuous (fun u : ℝ≥0 => zipDrv κ a (grpCfg κ B X ω) u)
  rw [zipDrv_eq_glue (x := ofFun (h0rev κ) + X ω) (B := B) ha.le
    (V := Vp (b1Data (grpCfg κ B X ω))) (hdet _ hA).1]
  exact continuous_zipDrvGlue (hVc _) (hV0 _) hBc hB0

end Cor15Group
end QuantumZipper
