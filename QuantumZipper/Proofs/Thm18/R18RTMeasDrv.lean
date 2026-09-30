import QuantumZipper.Proofs.Thm18.R18RTMeasTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT3, part 2: the driver and the mask of the unzipped configuration

Continuation of `R18RTMeasTime.lean`. The unzipping of the pieces at time `t` followed by the
rescaling (1.8) with parameter `A` has driver `s ↦ (W(t + A² s) − W(t))/A` (Sheffield,
arXiv:1012.4797, (1.8), p. 26). For a continuous driver `W` this is read jointly Borel in the data,
`t` and `A` through the Borel regularization `G1Pkg.pathReg` (continuous in the time, so jointly
measurable by Carathéodory, mathlib `measurable_uncurry_of_continuous_of_measurable`). The masked
circle coordinates are the Borel mask `D74.maskSel` of the full coordinates (`D74.maskSel_cfgData`).
So the fixed-time reading `Ψ` of `DownLenCapReadStmt` reduces to Borel readings of the scale
`areaScale` and of the full circle coordinates of the output field (`DownLenScaleFieldReadStmt`).

Own elementary bookkeeping (measurability the paper leaves implicit).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G1Pkg

/-- The driver of the rescaled unzipping, read through the Borel regularization of the driver. -/
def drvOutR (x : (ℕ → ℝ) × (ℝ≥0 → ℝ)) (t A : ℝ) : ℝ≥0 → ℝ := fun s =>
  (pathReg x.2 (Real.toNNReal (t + max (A ^ 2 * max (s : ℝ) 0) 0)) -
    pathReg x.2 (Real.toNNReal t)) / A

theorem measurable_pathReg_joint :
    Measurable fun p : (ℝ≥0 → ℝ) × ℝ => pathReg p.1 p.2.toNNReal := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (r : ℝ) (a : ℝ≥0 → ℝ) => pathReg a r.toNNReal)
    (fun a => (pathReg_spec.2.1 a).comp continuous_real_toNNReal)
    (fun r => measurable_pi_iff.1 measurable_pathReg r.toNNReal)
  exact h.comp measurable_swap

theorem measurable_pathReg_comp {α : Type*} [MeasurableSpace α] {a : α → ℝ≥0 → ℝ} {r : α → ℝ}
    (ha : Measurable a) (hr : Measurable r) :
    Measurable fun x => pathReg (a x) (r x).toNNReal :=
  Measurable.comp (g := fun p : (ℝ≥0 → ℝ) × ℝ => pathReg p.1 p.2.toNNReal)
    (f := fun x => (a x, r x)) measurable_pathReg_joint (ha.prodMk hr)

theorem measurable_drvOutR :
    Measurable fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ × ℝ => drvOutR p.1 p.2.1 p.2.2 := by
  refine measurable_pi_iff.2 fun s => ?_
  have ha : Measurable fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ × ℝ => p.1.2 :=
    measurable_snd.comp measurable_fst
  have ht : Measurable fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ × ℝ => p.2.1 :=
    measurable_fst.comp measurable_snd
  have hA : Measurable fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ × ℝ => p.2.2 :=
    measurable_snd.comp measurable_snd
  have hin : Measurable fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ × ℝ =>
      p.2.1 + max (p.2.2 ^ 2 * max (s : ℝ) 0) 0 :=
    ht.add (((hA.pow_const 2).mul_const _).max measurable_const)
  have h1 := measurable_pathReg_comp ha hin
  have h2 := measurable_pathReg_comp ha ht
  exact (h1.sub h2).div hA

/-- The driver of the rescaled unzipping of the pieces, for a continuous driver. -/
theorem canonA_zipCapDownA_drv_eq {γ t : ℝ} {d : E6.FullData} (hc : Continuous d.2) :
    (fun s : ℝ≥0 => (canonAConfig γ (zipCapDownA γ t (configOfData γ d))).drv s) =
      drvOutR (πd d) t (areaScale (zipCapDownA γ t (configOfData γ d)).area) := by
  funext s
  simp only [canonAConfig, zipCapDownA, zipCapDown, configOfData, drvOfData, drvOutR, πd,
    AreaConfig.toPair, pathReg_spec.2.2 _ hc]
  rfl

theorem canonA_zipCapDownA_drv_cont {γ t : ℝ} {d : E6.FullData} (hc : Continuous d.2) :
    Continuous (canonAConfig γ (zipCapDownA γ t (configOfData γ d))).drv := by
  simp only [canonAConfig, zipCapDownA, zipCapDown, configOfData, drvOfData, AreaConfig.toPair]
  refine Continuous.div_const (Continuous.sub ?_ continuous_const) _
  refine hc.comp (Continuous.subtype_mk ?_ _)
  fun_prop

theorem canonA_zipCapDownA_drv_zero {γ t : ℝ} {d : E6.FullData} :
    (canonAConfig γ (zipCapDownA γ t (configOfData γ d))).drv 0 = 0 := by
  simp [canonAConfig, zipCapDownA, zipCapDown, configOfData, drvOfData, AreaConfig.toPair]

/-- `πd ∘ maskSel` reads only the circle coordinates and the driver. -/
theorem πd_maskSel_congr {c : ℕ → ℝ} {p p' : TestFun H → ℝ} {w : ℝ≥0 → ℝ} :
    πd (D74.maskSel ((c, p), w)) = πd (D74.maskSel ((c, p'), w)) := rfl

/-- The fixed-time reading built from Borel readings `Sc` of the scale and `Cf` of the full
circle coordinates. -/
def psiRead (Sc : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ → ℝ) (Cf : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ → ℕ → ℝ)
    (p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ) : (ℕ → ℝ) × (ℝ≥0 → ℝ) :=
  πd (D74.maskSel ((Cf p, fun _ => 0), drvOutR p.1 p.2 (Sc p)))

theorem measurable_psiRead {Sc : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ → ℝ}
    {Cf : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ → ℕ → ℝ} (hSc : Measurable Sc) (hCf : Measurable Cf) :
    Measurable (psiRead Sc Cf) := by
  have hd : Measurable fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ => drvOutR p.1 p.2 (Sc p) :=
    Measurable.comp (g := fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ × ℝ => drvOutR p.1 p.2.1 p.2.2)
      (f := fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ => (p.1, p.2, Sc p)) measurable_drvOutR
      (measurable_fst.prodMk (measurable_snd.prodMk hSc))
  have hc : Measurable fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ =>
      ((Cf p, fun _ : TestFun H => (0 : ℝ)), drvOutR p.1 p.2 (Sc p)) :=
    (hCf.prodMk measurable_const).prodMk hd
  have hm : Measurable fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ =>
      D74.maskSel ((Cf p, fun _ : TestFun H => (0 : ℝ)), drvOutR p.1 p.2 (Sc p)) :=
    Measurable.comp (g := D74.maskSel)
      (f := fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ =>
        (((Cf p, fun _ : TestFun H => (0 : ℝ)), drvOutR p.1 p.2 (Sc p)) : E6.FullData))
      D74.measurable_maskSel hc
  exact Measurable.comp (g := πd) (f := fun p : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ =>
    D74.maskSel ((Cf p, fun _ : TestFun H => (0 : ℝ)), drvOutR p.1 p.2 (Sc p))) measurable_πd hm

theorem psiRead_eq {γ t : ℝ} {d : E6.FullData} (hc : Continuous d.2)
    {Sc : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ → ℝ} {Cf : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ → ℕ → ℝ}
    (hS : Sc (πd d, t) = areaScale (zipCapDownA γ t (configOfData γ d)).area)
    (hC : Cf (πd d, t) =
      CoordsFull.coordsFull (canonAConfig γ (zipCapDownA γ t (configOfData γ d))).fld) :
    psiRead Sc Cf (πd d, t) =
      πd (offData (canonAConfig γ (zipCapDownA γ t (configOfData γ d))).toPair) := by
  set y := (canonAConfig γ (zipCapDownA γ t (configOfData γ d))).toPair with hy
  have hmask := D74.maskSel_cfgData (x := y) (canonA_zipCapDownA_drv_cont hc)
    canonA_zipCapDownA_drv_zero
  have hoff : offData y = D74.maskSel (cfgData y) := by
    rw [hmask]; rfl
  rw [hoff]
  unfold psiRead cfgData
  rw [hS, hC]
  show πd (D74.maskSel ((CoordsFull.coordsFull y.1, fun _ => 0), _)) =
    πd (D74.maskSel ((CoordsFull.coordsFull y.1, fun ρ : TestFun H => pairRaw y.1 ρ.1),
      fun s : ℝ≥0 => y.2 s))
  rw [πd_maskSel_congr (p' := fun ρ : TestFun H => pairRaw y.1 ρ.1)]
  congr 3
  exact (canonA_zipCapDownA_drv_eq hc).symm

/-- **RT3 remainder, after the driver and the mask**: `DownLenCapReadStmt` with the fixed-time
reading replaced by Borel readings `Sc` of the scale `areaScale` of the transported area and `Cf`
of the full circle coordinates of the rescaled unzipped field. -/
def DownLenScaleFieldReadStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ →
      ∃ (G : Set ((ℕ → ℝ) × (ℝ≥0 → ℝ))) (L : ℚ → (ℕ → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
        (G₂ : Set (((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ))
        (Sc : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ → ℝ) (Cf : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℝ → ℕ → ℝ),
        MeasurableSet G ∧ (∀ q, Measurable (L q)) ∧ MeasurableSet G₂ ∧ Measurable Sc ∧
        Measurable Cf ∧
        (∀ d : E6.FullData, πd d ∈ G → Continuous d.2 →
          (∀ q : ℚ, 0 ≤ q → (unzipLengthsOpen γ (configOfData γ d).toPair q).1 = L q (πd d)) ∧
          ∀ s t : ℝ, 0 ≤ s → s ≤ t → (unzipLengthsOpen γ (configOfData γ d).toPair s).1 ≤
            (unzipLengthsOpen γ (configOfData γ d).toPair t).1) ∧
        (∀ (d : E6.FullData) (t : ℝ), (πd d, t) ∈ G₂ → Continuous d.2 →
          Sc (πd d, t) = areaScale (zipCapDownA γ t (configOfData γ d)).area ∧
          Cf (πd d, t) =
            CoordsFull.coordsFull (canonAConfig γ (zipCapDownA γ t (configOfData γ d))).fld) ∧
        ∀ᵐ ω ∂P, πd (offData (wedgeAConfig γ B Y ω).toPair) ∈ G ∧
          (πd (offData (wedgeAConfig γ B Y ω).toPair),
            lenTimeOpen γ ℓ (configOfData γ (offData (wedgeAConfig γ B Y ω).toPair)).toPair) ∈ G₂

theorem downLenCapReadStmt_of_scaleField (h : DownLenScaleFieldReadStmt) :
    DownLenCapReadStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  obtain ⟨G, L, G₂, Sc, Cf, hG, hL, hG₂, hSc, hCf, hlen, hread, hae⟩ := h γ P B Y hS hIn ℓ hℓ
  exact ⟨G, L, G₂, psiRead Sc Cf, hG, hL, hG₂, measurable_psiRead hSc hCf, hlen,
    fun d t hd hc => psiRead_eq hc (hread d t hd hc).1 (hread d t hd hc).2, hae⟩

/-- **RT3 (continuous drivers) from the scale and field readings.** -/
theorem downDataMeasCStmt_of_scaleField (h : DownLenScaleFieldReadStmt) : DownDataMeasCStmt :=
  downDataMeasCStmt_of_read (downLenCapReadStmt_of_scaleField h)

end R18
end QuantumZipper
