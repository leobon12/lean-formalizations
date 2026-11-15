/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQKillWord
import InteractingSLE.Spec.Sec5.CrossCondWord

/-!
# Lemma 4.7 in the chart `Q`: the killed image word of the counterflow on the glued space

Packet PROVE-CFRESTART4, item D1 (glued-space layer; the Lemma 4.7 mirror of GLUECOND5's `CrossCondWord`). On the
glued space `Ω × HistorySpace 0 0` of `Prop411Q.CfGlueAE`, with the flow line prefix `η([0, q])` revealed (`q ≥ 0`
fixed), the counterflow `α = histLine p.2` (chart `R`, parameter `16/κ`, not simple) is mapped by the flow line's chart
`Ψ = revChart Wf q` (`Wf = fDrv W p`, the flow driver). Before its first contact with `G = R(K_q)` (read from the
flow history, `qObs`, which is hitting-measurable) the image is a killed curve (`isKilledCurve_qgCurve`), so the
non-simple killed chain of `CrossRestartKernelQKill` gives its **killed image word** in capacity time:

* `fDrv`, `qObs`, `IsGood47` (a good glued sample: the flow driver is continuous from `0` with a generating trace in
  `ℍ` at positive times and the flow history reads its hull; the counterflow history is a good hitting history whose
  trace does not return to `0`);
* `qgCurve`, `qgPre`, `qgXL`, `qgXR` and the killed image word `qW`, `qVL`, `qVR`, `qT`, `qTr`;
* **`isKilledCurve_qgCurve`**, **`isKilledWord_q`**: the image is a killed curve and its word a killed word
  (`ImgDrv.IsKilledWord`) at every glued sample, for marks `x_L ≤ 0` antitone and `x_R ≥ 0` monotone;
* `isGeneratingTrace_qTr`, `qTr_capClock`: the trace generates the killed chain and passes through `Ψ(α(u))` at the
  capacity time of `u`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord (vRay)
open LawUnique GlueCond MartChar.RealFlow Cond44Ref CfRegQ Prop411Q
open CrossCond.Word49 (psiL psiR junL junR psiL_nonpos junL_le_psiL psiL_mono psiR_nonneg psiR_le_junR psiR_mono
  antitone_snoc monotone_snoc snoc_le le_snoc)

namespace Kill47

variable {Ω : Type*} {nL nR : ℕ}

/-- **The flow driver of a glued sample**, on real times. -/
def fDrv (W : ℝ≥0 → Ω → ℝ) (p : Ω × HistorySpace 0 0) (r : ℝ) : ℝ := W r.toNNReal p.1

/-- **The obstacle** `G = R(K_q)` read from the flow history (hitting-measurable). -/
def qObs (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0)
    (p : Ω × HistorySpace 0 0) : Set ℂ :=
  negInv '' hullAt q (killedHistory W VL VR ζ p.1)

/-- **A good glued sample**: the flow path is good (`Aux50Hit.IsGoodPath`: infinite lifetime,
continuous driver and force points, driver from `0`) with a generating trace on `[0, ∞)` lying in `ℍ` at positive times
(the flow line); the counterflow history is a good hitting history whose trace does not return to `0`. -/
def IsGood47 (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (p : Ω × HistorySpace 0 0) : Prop :=
  Aux50Hit.IsGoodPath W VL VR ζ p.1 ∧
    (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t p.1) ⊤ η ∧ (∀ t : ℝ≥0, 0 < t → η t ∈ H) ∧
      seedLine ζ W p.1 = fun s : ℝ => η s.toNNReal) ∧
    p.2 ∈ goodHitSet ∧ ∀ u : ℝ, 0 < u → histLine p.2 u ≠ 0

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {q : ℝ≥0}
  {p : Ω × HistorySpace 0 0}

theorem continuous_flow (hg : IsGood47 W VL VR ζ p) : Continuous fun t => W t p.1 := by
  have h := hg.1.2.2.1
  rw [hg.1.1] at h
  exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)

theorem continuous_fDrv (hg : IsGood47 W VL VR ζ p) : Continuous (fDrv W p) :=
  (continuous_flow hg).comp continuous_real_toNNReal

theorem fDrv_zero (hg : IsGood47 W VL VR ζ p) : fDrv W p 0 = 0 := by
  simp only [fDrv, Real.toNNReal_zero]
  exact hg.1.2.1

/-- On a good sample the counterflow trace (chart `R`) lies in `ℍ` at positive times. -/
theorem histLine_mem_H (hg : IsGood47 W VL VR ζ p) {u : ℝ} (hu : 0 < u) : histLine p.2 u ∈ H := by
  obtain ⟨-, -, hy, hnr⟩ := hg
  have hbar : 0 ≤ (histLine p.2 u).im := by
    have hgen := GlueCond.isGeneratingTrace_of_mem_goodCfSet hy.1
    obtain ⟨⟨-, hcd⟩, -⟩ := hy.1
    have := Sec7.IsGeneratingTrace.mem_Hbar hgen hcd.continuous.continuousOn hcd.zero
      (le_top : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ⊤)
    rw [CfRegQ.histLine_eq_traceAt]
    exact this
  refine lt_of_le_of_ne hbar fun h0 => ?_
  have hre : ((histLine p.2 u).re : ℂ) = histLine p.2 u := Complex.ext rfl (by rw [Complex.ofReal_im, ← h0])
  by_cases hx : (histLine p.2 u).re = 0
  · exact hnr u hu (by rw [← hre, hx, Complex.ofReal_zero])
  · exact GlueCond.histLine_ne_real_of_mem_goodHitSet hy hu hx hre.symm

/-- On a good sample the flow driver has a Loewner trace (the flow line) lying in `ℍ` at positive times. -/
theorem exists_flowTrace (hg : IsGood47 W VL VR ζ p) :
    IsLoewnerTrace (fDrv W p) (seedLine ζ W p.1) ∧ ∀ r : ℝ, 0 < r → seedLine ζ W p.1 r ∈ H := by
  obtain ⟨-, ⟨η, hη, hηH, he⟩, -⟩ := hg
  rw [he]
  exact ⟨isLoewnerTrace_of_isGeneratingTrace hη, fun r hr => hηH _ (Real.toNNReal_pos.2 hr)⟩

/-- **The junction gaps of the flow chart** are strict at a positive flow time. -/
theorem junction_gaps (hg : IsGood47 W VL VR ζ p) (hq : 0 < q) :
    0 < rightImg (fDrv W p) 0 q - fDrv W p q ∧ -rightImg (fun r => -fDrv W p r) 0 q - fDrv W p q < 0 := by
  obtain ⟨hL, hH⟩ := exists_flowTrace hg
  have hH' : ∀ r ∈ Ioc (0 : ℝ) q, seedLine ζ W p.1 r ∈ H := fun r hr => hH r hr.1
  exact ⟨CrossRestart.chartAR_pos_of_mem_H hL hH' (continuous_fDrv hg) (fDrv_zero hg) (by exact_mod_cast hq),
    CrossRestart.chartAL_neg_of_mem_H hL hH' (continuous_fDrv hg) (fDrv_zero hg) (by exact_mod_cast hq)⟩

open scoped Classical in
/-- **The image curve** `Ψ ∘ α` of the counterflow on `E`, the vertical ray elsewhere. -/
def qgCurve (W : ℝ≥0 → Ω → ℝ) (q : ℝ≥0) (E : Set (Ω × HistorySpace 0 0)) (p : Ω × HistorySpace 0 0) : ℝ → ℂ :=
  if p ∈ E then imgCurve (fDrv W p) q (histLine p.2) else vRay

open scoped Classical in
/-- **The pre-contact times** of the counterflow with `G = R(K_q)` on `E`, `[0, ∞)` elsewhere. -/
def qgPre (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0)
    (E : Set (Ω × HistorySpace 0 0)) (p : Ω × HistorySpace 0 0) : Set ℝ :=
  if p ∈ E then preContact (histLine p.2) (qObs W VL VR ζ q p) else Ici 0

open scoped Classical in
/-- **The left marks of the image word**: the images `Ψ(x_i)` of the counterflow word's left marks and the left
junction `Ψ(∞⁻)` (`0` off `E`). -/
def qgXL {m : ℕ} (x : Fin m → ℝ) (W : ℝ≥0 → Ω → ℝ) (q : ℝ≥0) (E : Set (Ω × HistorySpace 0 0))
    (p : Ω × HistorySpace 0 0) : Fin (m + 1) → ℝ :=
  if p ∈ E then Fin.snoc (fun i => psiL (fDrv W p) q (x i)) (junL (fDrv W p) q) else fun _ => 0

open scoped Classical in
/-- **The right marks of the image word**: the images `Ψ(x_j)` and the right junction `Ψ(∞⁺)`. -/
def qgXR {m : ℕ} (x : Fin m → ℝ) (W : ℝ≥0 → Ω → ℝ) (q : ℝ≥0) (E : Set (Ω × HistorySpace 0 0))
    (p : Ω × HistorySpace 0 0) : Fin (m + 1) → ℝ :=
  if p ∈ E then Fin.snoc (fun j => psiR (fDrv W p) q (x j)) (junR (fDrv W p) q) else fun _ => 0

/-- **The killed image driver.** -/
def qW (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0)
    (E : Set (Ω × HistorySpace 0 0)) : ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun t p => kcW (qgCurve W q E p) (qgPre W VL VR ζ q E p) t

/-- **The images of the left marks.** -/
def qVL {m : ℕ} (x : Fin m → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (q : ℝ≥0) (E : Set (Ω × HistorySpace 0 0)) : Fin (m + 1) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun i t p => kcVL (qgCurve W q E p) (qgPre W VL VR ζ q E p) (qgXL x W q E p) i t

/-- **The images of the right marks.** -/
def qVR {m : ℕ} (x : Fin m → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (q : ℝ≥0) (E : Set (Ω × HistorySpace 0 0)) : Fin (m + 1) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun j t p => kcVR (qgCurve W q E p) (qgPre W VL VR ζ q E p) (qgXR x W q E p) j t

/-- **The killing time of the image word** (the capacity of the first contact). -/
def qT (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0)
    (E : Set (Ω × HistorySpace 0 0)) : Ω × HistorySpace 0 0 → WithTop ℝ≥0 :=
  fun p => kcLife (qgCurve W q E p) (qgPre W VL VR ζ q E p)

/-- **The image trace in capacity time.** -/
def qTr (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0)
    (E : Set (Ω × HistorySpace 0 0)) (p : Ω × HistorySpace 0 0) : ℝ≥0 → ℂ :=
  kcTr (qgCurve W q E p) (qgPre W VL VR ζ q E p)

variable {E : Set (Ω × HistorySpace 0 0)}

theorem qgCurve_of_mem (hp : p ∈ E) : qgCurve W q E p = imgCurve (fDrv W p) q (histLine p.2) := by
  simp only [qgCurve, hp, ↓reduceIte]

theorem qgPre_of_mem (hp : p ∈ E) : qgPre W VL VR ζ q E p = preContact (histLine p.2) (qObs W VL VR ζ q p) := by
  simp only [qgPre, hp, ↓reduceIte]

theorem qObs_of_good (hg : IsGood47 W VL VR ζ p) : qObs W VL VR ζ q p = negInv '' fwdHull (fDrv W p) q := by
  rw [qObs, hullAt, Aux50Hit.regHull_stopHistory_cstop hg.1 q]
  rfl

/-- **On good samples the image of the counterflow is a killed curve**; elsewhere the vertical ray. -/
theorem isKilledCurve_qgCurve (hE : ∀ p ∈ E, IsGood47 W VL VR ζ p) (p : Ω × HistorySpace 0 0) :
    IsKilledCurve (qgCurve W q E p) (qgPre W VL VR ζ q E p) := by
  by_cases hp : p ∈ E
  · have hg := hE p hp
    rw [qgCurve_of_mem hp, qgPre_of_mem hp, qObs_of_good hg]
    obtain ⟨hgp, ⟨η, hη, hηH, -⟩, hy, -⟩ := id hg
    obtain ⟨⟨-, hcd⟩, -⟩ := id hy.1
    have h := isKilledCurve_imgCurve_of_traces (continuous_flow hg) hgp.2.1 hη hηH hcd.continuous hcd.zero
      (GlueCond.isGeneratingTrace_of_mem_goodCfSet hy.1) (fun t ht => by
        have := histLine_mem_H hg (u := t) ht
        rw [CfRegQ.histLine_eq_traceAt] at this
        simpa only [Real.toNNReal_coe] using this) q
    rw [← CfRegQ.histLine_eq_traceAt] at h
    exact h
  · simp only [qgCurve, qgPre, hp, ↓reduceIte]
    exact isKilledCurve_vRay

theorem qgXL_nonpos {m : ℕ} {x : Fin m → ℝ} (hx : ∀ i, x i ≤ 0) (hE : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hq : 0 < q) (p : Ω × HistorySpace 0 0) (i : Fin (m + 1)) : qgXL x W q E p i ≤ 0 := by
  by_cases hp : p ∈ E
  · have hg := hE p hp
    have hj := (junction_gaps hg hq).1
    have hw := continuous_fDrv hg
    simp only [qgXL, hp, ↓reduceIte]
    exact snoc_le (fun i => psiL_nonpos hw q.coe_nonneg hj (hx i))
      ((junL_le_psiL hw q.coe_nonneg hj le_rfl).trans (psiL_nonpos hw q.coe_nonneg hj le_rfl)) i
  · simp [qgXL, hp]

theorem qgXR_nonneg {m : ℕ} {x : Fin m → ℝ} (hx : ∀ j, 0 ≤ x j) (hE : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hq : 0 < q) (p : Ω × HistorySpace 0 0) (j : Fin (m + 1)) : 0 ≤ qgXR x W q E p j := by
  by_cases hp : p ∈ E
  · have hg := hE p hp
    have hj := (junction_gaps hg hq).2
    have hw := continuous_fDrv hg
    simp only [qgXR, hp, ↓reduceIte]
    exact le_snoc (fun j => psiR_nonneg hw q.coe_nonneg hj (hx j))
      ((psiR_nonneg hw q.coe_nonneg hj le_rfl).trans (psiR_le_junR hw q.coe_nonneg hj le_rfl)) j
  · simp [qgXR, hp]

theorem antitone_qgXL {m : ℕ} {x : Fin m → ℝ} (hx : ∀ i, x i ≤ 0) (hxa : Antitone x)
    (hE : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hq : 0 < q) (p : Ω × HistorySpace 0 0) : Antitone (qgXL x W q E p) := by
  by_cases hp : p ∈ E
  · have hg := hE p hp
    have hj := (junction_gaps hg hq).1
    have hw := continuous_fDrv hg
    simp only [qgXL, hp, ↓reduceIte]
    exact antitone_snoc (fun i i' hii => psiL_mono hw q.coe_nonneg hj (hx i) (hxa hii))
      (fun i => junL_le_psiL hw q.coe_nonneg hj (hx i))
  · simp only [qgXL, hp, ↓reduceIte]
    exact antitone_const

theorem monotone_qgXR {m : ℕ} {x : Fin m → ℝ} (hx : ∀ j, 0 ≤ x j) (hxm : Monotone x)
    (hE : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hq : 0 < q) (p : Ω × HistorySpace 0 0) : Monotone (qgXR x W q E p) := by
  by_cases hp : p ∈ E
  · have hg := hE p hp
    have hj := (junction_gaps hg hq).2
    have hw := continuous_fDrv hg
    simp only [qgXR, hp, ↓reduceIte]
    exact monotone_snoc (fun j j' hjj => psiR_mono hw q.coe_nonneg hj (hx j) (hxm hjj))
      (fun j => psiR_le_junR hw q.coe_nonneg hj (hx j))
  · simp only [qgXR, hp, ↓reduceIte]
    exact monotone_const

/-- **The image word of the counterflow is a killed word** at every glued sample (for marks `x_L ≤ 0` antitone,
`x_R ≥ 0` monotone, at a positive flow time). -/
theorem isKilledWord_q {mL mR : ℕ} {xL : Fin mL → ℝ} {xR : Fin mR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxLa : Antitone xL)
    (hxR : ∀ j, 0 ≤ xR j) (hxRm : Monotone xR) (hE : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hq : 0 < q) :
    WangWu.ImgDrv.IsKilledWord (qW W VL VR ζ q E) (qVL xL W VL VR ζ q E) (qVR xR W VL VR ζ q E)
      (qT W VL VR ζ q E) :=
  isKilledWord_kc (isKilledCurve_qgCurve hE) (qgXL_nonpos hxL hE hq) (qgXR_nonneg hxR hE hq)
    (antitone_qgXL hxL hxLa hE hq) (monotone_qgXR hxR hxRm hE hq)

/-- **The image trace generates the killed image chain** before the killing time. -/
theorem isGeneratingTrace_qTr (hE : ∀ p ∈ E, IsGood47 W VL VR ζ p) (p : Ω × HistorySpace 0 0) {T : ℝ≥0∞}
    (hT : T < qT W VL VR ζ q E p) : IsGeneratingTrace (qW W VL VR ζ q E · p) T (qTr W VL VR ζ q E p) :=
  (isKilledCurve_qgCurve hE p).isGeneratingTrace_kcTr hT

/-- **The image trace passes through `Ψ(α(u))`** at the capacity time of every pre-contact time `u` (good samples). -/
theorem qTr_capClock (hE : ∀ p ∈ E, IsGood47 W VL VR ζ p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E) {u : ℝ}
    (hu : u ∈ qgPre W VL VR ζ q E p) :
    qTr W VL VR ζ q E p (capClock (qgCurve W q E p) u).toNNReal = imgCurve (fDrv W p) q (histLine p.2) u := by
  rw [qTr, (isKilledCurve_qgCurve hE p).kcTr_capClock hu, qgCurve_of_mem hp]

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
