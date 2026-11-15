/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualIdent
import InteractingSLE.Spec.Sec2.Assembly3Cont
import InteractingSLE.Spec.Sec2.Assembly3Entr
import InteractingSLE.Spec.Sec2.Assembly2Stage
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# Zhan's A.1.3: the law-level identification of the image path

Packet PROVE-ZHAN-GT4-A12. Astra, *Follow-up proofs*, §A.1.3 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L353–L355, R38): "The time change `du = A²_{j,1} dt_j`, Lévy's characterization, and uniqueness in law of the integrated
force system identify the claimed conditional image law inside this rectangle."

PROVE-ZHAN-GT4-A11 proved that under `Q = (M̃_S/M̃_0)·P`, in the capacity-time filtration `𝓗_u = 𝓕_{C'⁻¹(u)}` with the
`Q`-Brownian motion `B̂`, the image driver and image marks form a **local** force-point evolution before `a(S)`
(`FrzD10Hyp.isSLEEvolutionUpTo_img`). Here the image path is identified **in law**:

* `FrzD10Hyp.a_min_invClockT`, `FrzD10Hyp.measurable_img_min`: the image processes stopped at `a(S)` are adapted to
  `𝓗` at every time; `FrzD10Hyp.isStoppingTime_imgHor`: `a(S)` is an `𝓗`-stopping time;
* `FrzD10Hyp.goodWord_imgHor`: at `a(S)` the word seen from the image driver is good (separated by (D9), ordered,
  no threshold);
* **`FrzD10Hyp.isIntegratedSLEEvolution_img`**: the image path stopped at `a(S)`, continued after `a(S)` by the maximal
  solution driven by the increments of `B̂` (`Sec2.Assembly3.isIntegratedSLEEvolution_contClosed`), is an
  **integrated `SLE_κ(ρ)` evolution** of the image word under `Q` (usual augmentation of `𝓗`), and it agrees with the
  image path before `a(S)` (`FrzD10Hyp.contState_img_of_lt`);
* **`FrzD10Hyp.exists_isIntegratedSLEEvolution_img_law`**: hence (Theorem 2.2's uniqueness in law,
  `IsIntegratedSLEEvolution.measure_killedState_eq_assembled`) **the image path before `a(S)` is the initial segment of
  an evolution whose killed finite-dimensional laws are those of every integrated `SLE_κ(ρ)` evolution of the image word**
  on any probability space: "the claimed conditional image law inside this rectangle". No stopping functional of the
  image path is needed: the continuation lives on the same space as the image path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3

section Law

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The horizon `a(S)` of the image path, as a time. -/
def imgHor (a : Ω → ℝ → ℝ) (S : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 := (a ω (S ω)).toNNReal

/-- The image driver stopped at `a(S)`, recentred: `W'(u ∧ a(S)) − w₀`. -/
def imgStopW (W' a : Ω → ℝ → ℝ) (S : Ω → ℝ≥0) (w₀ : ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  W' ω (min (u : ℝ) (a ω (S ω))) - w₀

/-- An image mark stopped at `a(S)`, recentred: `Ṽ_x(u ∧ a(S)) − w₀`. -/
def imgStopV (W' a : Ω → ℝ → ℝ) (S : Ω → ℝ≥0) (x w₀ : ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  imgV (W' ω) x (min (u : ℝ) (a ω (S ω))) - w₀

namespace FrzD10Hyp

variable {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ}
  {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

theorem a_S_nonneg (ω : Ω) : 0 ≤ a ω (S ω) := (hH.a_mem_Icc_aT ω ⟨(S ω).coe_nonneg, le_rfl⟩).1

theorem coe_imgHor (ω : Ω) : (imgHor a S ω : ℝ) = a ω (S ω) := Real.coe_toNNReal _ (hH.a_S_nonneg ω)

/-- `a(S) > 0` for `S > 0`. -/
theorem a_S_pos {ω : Ω} (hS0 : 0 < S ω) : 0 < a ω (S ω) := by
  have h := (hH.own ω).mono ⟨le_rfl, (hH.own ω).pos.le⟩ ⟨(S ω).coe_nonneg, hH.le ω⟩
    (show (0 : ℝ) < S ω from hS0)
  rwa [(hH.own ω).a0] at h

/-- After `a(S)` the clock inverse is after `S`. -/
theorem S_lt_invClockT {u : ℝ≥0} {ω : Ω} (hu : a ω (S ω) < u) : S ω < invClockT (bmClk a S) u ω := by
  have ha₀ := (hH.d9 ω).a0
  have hc : 0 < min (a₀ ^ 2) 1 := lt_min (pow_pos ha₀ 2) one_pos
  obtain ⟨-, hC, -⟩ := invClock_eq_coe hH.continuous_bmClk hH.bmClk_zero hc hH.le_bmClk u ω
  by_contra h
  push Not at h
  have hm := (hH.strictMono_bmClk ω).monotone h
  rw [hC, bmClk_S] at hm
  exact absurd hu (not_lt.2 hm)

/-- `a(θ_u ∧ S) = u ∧ a(S)`, `θ_u = C'⁻¹(u)`. -/
theorem a_min_invClockT (u : ℝ≥0) (ω : Ω) :
    a ω ((min (invClockT (bmClk a S) u ω) (S ω) : ℝ≥0) : ℝ) = min (u : ℝ) (a ω (S ω)) := by
  rcases le_or_gt (u : ℝ) (a ω (S ω)) with hu | hu
  · obtain ⟨hθS, haθ⟩ := hH.invClockT_le_and_a_eq hu
    rw [min_eq_left hθS, haθ, min_eq_left hu]
  · rw [min_eq_right (hH.S_lt_invClockT hu).le, min_eq_right hu.le]

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The stopped image processes are adapted to the capacity-time filtration** `𝓗_u = 𝓕_{C'⁻¹(u)}` at every time:
if `r ↦ X_ω(a_ω(r ∧ S))` is continuous and `𝓕`-adapted, then `X_ω(u ∧ a(S))` is `𝓗_u`-measurable. -/
theorem measurable_img_min (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {X : Ω → ℝ → ℝ}
    (hY : ∀ t : ℝ≥0, Measurable[𝓕 t] fun ω => X ω (a ω ((min t (S ω) : ℝ≥0) : ℝ)))
    (hYc : ∀ ω, Continuous fun t : ℝ≥0 => X ω (a ω ((min t (S ω) : ℝ≥0) : ℝ))) (u : ℝ≥0) :
    Measurable[Zhan.Retarget.timeChangeFilt 𝓕
        (isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
          (hH.measurable_bmClk hBm hBc hS))
        (invClock_mono hH.continuous_bmClk fun ω => (hH.strictMono_bmClk ω).monotone) u]
      fun ω => X ω (min (u : ℝ) (a ω (S ω))) := by
  have hθ := isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
    (hH.measurable_bmClk hBm hBc hS) u
  have h := measurable_comp_invClockT hθ hY hYc
  have e : (fun ω => X ω (a ω ((min (invClockT (bmClk a S) u ω) (S ω) : ℝ≥0) : ℝ))) =
      fun ω => X ω (min (u : ℝ) (a ω (S ω))) := funext fun ω => by rw [hH.a_min_invClockT u ω]
  rw [e] at h
  exact h

/-- **`a(S)` is a stopping time of the capacity-time filtration.** -/
theorem isStoppingTime_imgHor (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    IsStoppingTime (Zhan.Retarget.timeChangeFilt 𝓕
        (isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
          (hH.measurable_bmClk hBm hBc hS))
        (invClock_mono hH.continuous_bmClk fun ω => (hH.strictMono_bmClk ω).monotone))
      fun ω => (imgHor a S ω : WithTop ℝ≥0) := by
  intro u
  have hθ := isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
    (hH.measurable_bmClk hBm hBc hS) u
  have e : {ω | (imgHor a S ω : WithTop ℝ≥0) ≤ u} = {ω | (S ω : WithTop ℝ≥0) ≤ invClock (bmClk a S) u ω} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    rw [← not_lt, ← not_lt, ← hH.lt_a_S_iff u ω, ← NNReal.coe_lt_coe, hH.coe_imgHor ω]
  rw [e]
  exact hS.measurableSet_stopping_time_le hθ

/-- The stopped image driver is continuous. -/
theorem continuous_imgStopW (ω : Ω) (w₀ : ℝ) : Continuous fun u : ℝ≥0 => imgStopW W' a S w₀ u ω :=
  ((hH.own ω).contW'.comp (NNReal.continuous_coe.min continuous_const)).sub continuous_const

/-- The stopped image marks are continuous. -/
theorem continuous_imgStopV (ω : Ω) (o : Option (Fin n)) (w₀ : ℝ) :
    Continuous fun u : ℝ≥0 => imgStopV W' a S (markPos ζ₀ ζ o) w₀ u ω := by
  refine ContinuousOn.comp_continuous (hH.toFrzMartHyp.continuousOn_imgV_mark ω o)
    (NNReal.continuous_coe.min continuous_const) (fun u => ?_) |>.sub continuous_const
  exact ⟨le_min u.coe_nonneg (hH.a_S_nonneg ω), (min_le_right _ _).trans (hH.a_S_le ω)⟩

/-- Order of the image marks, non-strict form (the positions are injective). -/
theorem imgV_le_imgV_of_le (ω : Ω) {o o' : Option (Fin n)} (h0 : markPos ζ₀ ζ o ≤ markPos ζ₀ ζ o') {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (a ω (T ω))) :
    imgV (W' ω) (markPos ζ₀ ζ o) u ≤ imgV (W' ω) (markPos ζ₀ ζ o') u := by
  rcases eq_or_lt_of_le h0 with h | h
  · rw [markPos_injective hH.ne hH.inj h]
  · exact (hH.toFrzMartHyp.imgV_lt_imgV_of_lt ω h hu).le

/-- **The word at `a(S)` seen from the image driver is good**: the left image marks are strictly left of the driver
and the right ones strictly right ((D9) and the order of the marks), the families are ordered, and no mark is at the
driver (so the threshold condition fails). -/
theorem goodWord_imgHor {nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)) {w₀ : ℝ} (hw₀ : ∀ ω, W' ω 0 = w₀)
    (hL : ∀ i, markPos ζ₀ ζ (e (Sum.inl i)) < w₀) (hR : ∀ i, w₀ < markPos ζ₀ ζ (e (Sum.inr i)))
    (hLa : Antitone fun i => markPos ζ₀ ζ (e (Sum.inl i))) (hRm : Monotone fun i => markPos ζ₀ ζ (e (Sum.inr i)))
    (ω : Ω) :
    GoodWord (fun i => markWt κ rr (e (Sum.inl i))) (fun i => markWt κ rr (e (Sum.inr i)))
      (contWord (imgStopW W' a S w₀) (fun i => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inl i))) w₀)
        (fun j => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inr j))) w₀) (imgHor a S) ω) := by
  have hu : a ω (S ω) ∈ Icc (0 : ℝ) (a ω (T ω)) := ⟨hH.a_S_nonneg ω, hH.a_S_le ω⟩
  have hmin : min ((imgHor a S ω : ℝ≥0) : ℝ) (a ω (S ω)) = a ω (S ω) := by rw [hH.coe_imgHor, min_self]
  have hw : contWord (imgStopW W' a S w₀) (fun i => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inl i))) w₀)
      (fun j => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inr j))) w₀) (imgHor a S) ω =
      (fun i => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inl i))) (a ω (S ω)) - W' ω (a ω (S ω)),
        fun j => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inr j))) (a ω (S ω)) - W' ω (a ω (S ω))) := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_) <;>
    · simp only [contWord, imgStopW, imgStopV, hmin]
      ring
  have hneg : ∀ i, imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inl i))) (a ω (S ω)) - W' ω (a ω (S ω)) < 0 := fun i =>
    sub_neg.2 (hH.toFrzMartHyp.imgV_lt_of_lt ω _ (by rw [hw₀ ω]; exact hL i) hu)
  have hpos : ∀ j, 0 < imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inr j))) (a ω (S ω)) - W' ω (a ω (S ω)) := fun j =>
    sub_pos.2 (hH.toFrzMartHyp.lt_imgV_of_lt ω _ (by rw [hw₀ ω]; exact hR j) hu)
  rw [hw]
  refine ⟨fun i j => (hneg i).trans (hpos j), ⟨fun i j hij => ?_, fun i => (hneg i).le, fun i j hij => ?_,
    fun j => (hpos j).le⟩, ?_⟩
  · exact sub_le_sub_right (hH.imgV_le_imgV_of_le ω (hLa hij) hu) _
  · exact sub_le_sub_right (hH.imgV_le_imgV_of_le ω (hRm hij) hu) _
  · unfold ForceWord.ThresholdCondition
    push Not
    constructor
    · rw [Finset.filter_false_of_mem fun i _ => (hneg i).ne, Finset.sum_empty]
      norm_num
    · rw [Finset.filter_false_of_mem fun j _ => (hpos j).ne', Finset.sum_empty]
      norm_num

/-- **The stopped image path is a local integrated path up to `a(S)`** (A11's `isSLEPathUpTo_img`, stopped). -/
theorem isSLEPathUpTo_imgStop (hκ : 0 < κ) {nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)) {w₀ : ℝ}
    (hw₀ : ∀ ω, W' ω 0 = w₀) (hL : ∀ i, markPos ζ₀ ζ (e (Sum.inl i)) < w₀)
    (hR : ∀ i, w₀ < markPos ζ₀ ζ (e (Sum.inr i))) (hLa : Antitone fun i => markPos ζ₀ ζ (e (Sum.inl i)))
    (hRm : Monotone fun i => markPos ζ₀ ζ (e (Sum.inr i))) (ω : Ω) :
    IsSLEPathUpTo κ (fun i => markPos ζ₀ ζ (e (Sum.inl i)) - w₀) (fun i => markPos ζ₀ ζ (e (Sum.inr i)) - w₀)
      (fun i => markWt κ rr (e (Sum.inl i))) (fun i => markWt κ rr (e (Sum.inr i)))
      (fun u => imgStopW W' a S w₀ u ω) (fun i u => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inl i))) w₀ u ω)
      (fun j u => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inr j))) w₀ u ω)
      (fun u => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω) ((imgHor a S ω : ℝ≥0) : ℝ≥0∞) := by
  have h := hH.isSLEPathUpTo_img hκ e hw₀ hL hR hLa hRm ω
  have h0 : min (0 : ℝ) (a ω (S ω)) = 0 := min_eq_left (hH.a_S_nonneg ω)
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ENNReal.ofReal (a ω (S ω)) → min (t : ℝ) (a ω (S ω)) = t := fun t ht =>
    min_eq_left ((coe_lt_ofReal_iff t _).1 ht).le
  exact Assembly2.isSLEPathUpTo_congr h (by simp only [imgStopW, NNReal.coe_zero, h0])
    (fun i => by simp only [imgStopV, NNReal.coe_zero, h0]) (fun j => by simp only [imgStopV, NNReal.coe_zero, h0])
    (fun t ht => by simp only [imgStopW, hlt t ht]) (fun t ht i => by simp only [imgStopV, hlt t ht])
    (fun t ht j => by simp only [imgStopV, hlt t ht]) fun _ _ => rfl

/-- **The identification in law (§A.1.3).** Under `Q = (M̃_S/M̃_0)·P`, in the usual augmentation of the capacity-time
filtration `𝓗_u = 𝓕_{C'⁻¹(u)}`, with the `Q`-Brownian motion `B̂_u = Y_{C'⁻¹(u)}`: the image driver and image marks
stopped at `a(S)` (recentred at `w₀ = W'(0)`, sorted by `e`), continued after `a(S)` by the maximal solution driven by
the increments of `B̂`, form an **integrated `SLE_κ(ρ)` evolution** (`IsIntegratedSLEEvolution`, Definition 2.1) of the
image word: the other tip with weight `−κ/2` and the force marks with weights `κ r_m`. -/
theorem isIntegratedSLEEvolution_img (hκ : 0 < κ) {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hS0 : ∀ ω, 0 < S ω)
    {NB : ℝ} (hBb : ∀ ω (r : ℝ≥0), r ≤ S ω → |B r ω| ≤ NB) {nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n))
    {w₀ : ℝ} (hw₀ : ∀ ω, W' ω 0 = w₀) (hL : ∀ i, markPos ζ₀ ζ (e (Sum.inl i)) < w₀)
    (hR : ∀ i, w₀ < markPos ζ₀ ζ (e (Sum.inr i))) (hLa : Antitone fun i => markPos ζ₀ ζ (e (Sum.inl i)))
    (hRm : Monotone fun i => markPos ζ₀ ζ (e (Sum.inr i))) :
    IsIntegratedSLEEvolution κ (fun i => markPos ζ₀ ζ (e (Sum.inl i)) - w₀)
      (fun i => markPos ζ₀ ζ (e (Sum.inr i)) - w₀) (fun i => markWt κ rr (e (Sum.inl i)))
      (fun i => markWt κ rr (e (Sum.inr i)))
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell)
      (usualAugmentation (Zhan.Retarget.timeChangeFilt 𝓕
        (isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
          (hH.measurable_bmClk (fun u => hB.2.1 u) hBc hS))
        (invClock_mono hH.continuous_bmClk fun ω => (hH.strictMono_bmClk ω).monotone))
        (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell))
      (fun t ω => (contState κ (fun i => markWt κ rr (e (Sum.inl i))) (fun i => markWt κ rr (e (Sum.inr i)))
        (imgStopW W' a S w₀) (fun i => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inl i))) w₀)
        (fun j => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inr j))) w₀)
        (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω) (imgHor a S) t ω).1)
      (fun i t ω => (contState κ (fun i => markWt κ rr (e (Sum.inl i))) (fun i => markWt κ rr (e (Sum.inr i)))
        (imgStopW W' a S w₀) (fun i => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inl i))) w₀)
        (fun j => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inr j))) w₀)
        (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω) (imgHor a S) t ω).2.1 i)
      (fun j t ω => (contState κ (fun i => markWt κ rr (e (Sum.inl i))) (fun i => markWt κ rr (e (Sum.inr i)))
        (imgStopW W' a S w₀) (fun i => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inl i))) w₀)
        (fun j => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inr j))) w₀)
        (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω) (imgHor a S) t ω).2.2 j)
      (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω)
      (fun ω => (imgHor a S ω : ℝ≥0∞) + contLife κ (fun i => markWt κ rr (e (Sum.inl i)))
        (fun i => markWt κ rr (e (Sum.inr i))) (imgStopW W' a S w₀)
        (fun i => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inl i))) w₀)
        (fun j => imgStopV W' a S (markPos ζ₀ ζ (e (Sum.inr j))) w₀)
        (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω) (imgHor a S) ω) := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hBQ := hH.isFilteredBrownianReal_bm hκ hB hBc hS hBb
  have := hBQ.isProbabilityMeasure'
  have h𝓗 := Ito.le_usualAugmentation (Zhan.Retarget.timeChangeFilt 𝓕
    (isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
      (hH.measurable_bmClk hBm hBc hS))
    (invClock_mono hH.continuous_bmClk fun ω => (hH.strictMono_bmClk ω).monotone))
    (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell)
  have hBhc : ∀ ω, Continuous fun u => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω := fun ω => by
    have hc : 0 < min (a₀ ^ 2) 1 := lt_min (pow_pos (hH.d9 ω).a0 2) one_pos
    exact (hH.continuous_bmY hBc ω).comp
      (continuous_invClockT hH.continuous_bmClk hH.strictMono_bmClk hH.bmClk_zero hc hH.le_bmClk ω)
  have hVa : ∀ (o : Option (Fin n)) (t : ℝ≥0), Measurable[usualAugmentation _ _ t]
      (imgStopV W' a S (markPos ζ₀ ζ o) w₀ t) := fun o t =>
    ((hH.measurable_img_min hBm hBc hS (X := fun ω => imgV (W' ω) (markPos ζ₀ ζ o))
      (hH.measurable_imgV_min hBm hBc hS o) (fun ω => continuous_comp_min (hH.continuousOn_imgV_a ω o)) t).sub_const
      w₀).mono (h𝓗 t) le_rfl
  refine isIntegratedSLEEvolution_contClosed hκ (Ito.isFilteredBrownianReal_usualAugmentation hBQ) hBhc
    (fun t => ((hH.measurable_img_min hBm hBc hS (X := W') (hH.measurable_W'_min hBm hBc hS)
      (fun ω => continuous_comp_min (hH.continuousOn_W'_a ω)) t).sub_const w₀).mono (h𝓗 t) le_rfl)
    (fun i t => hVa _ t) (fun j t => hVa _ t) (fun ω => hH.continuous_imgStopW ω w₀)
    (fun i ω => hH.continuous_imgStopV ω _ w₀) (fun j ω => hH.continuous_imgStopV ω _ w₀)
    (Eventually.of_forall fun ω => hH.isSLEPathUpTo_imgStop hκ e hw₀ hL hR hLa hRm ω)
    (fun u => h𝓗 u _ (hH.isStoppingTime_imgHor hBm hBc hS u))
    (fun ω => Real.toNNReal_pos.2 (hH.a_S_pos (hS0 ω)))
    (Eventually.of_forall fun ω => hH.goodWord_imgHor e hw₀ hL hR hLa hRm ω)

omit hH in
/-- **The continued evolution is the image path before `a(S)`.** -/
theorem contState_img_of_lt {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    {w₀ : ℝ} (Bh : ℝ≥0 → Ω → ℝ) {ω : Ω} {t : ℝ≥0} (ht : (t : ℝ) < a ω (S ω)) :
    (contState κ ρL ρR (imgStopW W' a S w₀) (fun i => imgStopV W' a S (xL i) w₀)
        (fun j => imgStopV W' a S (xR j) w₀) Bh (imgHor a S) t ω).1 = W' ω t - w₀ ∧
      (∀ i, (contState κ ρL ρR (imgStopW W' a S w₀) (fun i => imgStopV W' a S (xL i) w₀)
        (fun j => imgStopV W' a S (xR j) w₀) Bh (imgHor a S) t ω).2.1 i = imgV (W' ω) (xL i) t - w₀) ∧
      ∀ j, (contState κ ρL ρR (imgStopW W' a S w₀) (fun i => imgStopV W' a S (xL i) w₀)
        (fun j => imgStopV W' a S (xR j) w₀) Bh (imgHor a S) t ω).2.2 j = imgV (W' ω) (xR j) t - w₀ := by
  have hlt : t < imgHor a S ω := by
    rw [← NNReal.coe_lt_coe, imgHor, Real.coe_toNNReal _ ((t.coe_nonneg).trans ht.le)]
    exact ht
  have hmin : min (t : ℝ) (a ω (S ω)) = t := min_eq_left ht.le
  refine ⟨?_, fun i => ?_, fun j => ?_⟩ <;>
  · simp only [contState]
    rw [concatAt_of_lt hlt]
    simp only [imgStopW, imgStopV, hmin]

/-- **The law-level identification (§A.1.3): the image path inside the rectangle has the force-point law.** Under
`Q = (M̃_S/M̃_0)·P` there is an integrated `SLE_κ(ρ)` evolution `(gW, gL, gR, B̂, ζG)` of the image word on the same space
(usual augmentation of the capacity-time filtration), living at least until `a(S)` and equal to the image driver and
image marks before `a(S)`; its killed finite-dimensional laws are those of **every** integrated `SLE_κ(ρ)` evolution of
the image word, on any probability space (Theorem 2.2's uniqueness in law). -/
theorem exists_isIntegratedSLEEvolution_img_law (hκ : 0 < κ) {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hS0 : ∀ ω, 0 < S ω)
    {NB : ℝ} (hBb : ∀ ω (r : ℝ≥0), r ≤ S ω → |B r ω| ≤ NB) {nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n))
    {w₀ : ℝ} (hw₀ : ∀ ω, W' ω 0 = w₀) (hL : ∀ i, markPos ζ₀ ζ (e (Sum.inl i)) < w₀)
    (hR : ∀ i, w₀ < markPos ζ₀ ζ (e (Sum.inr i))) (hLa : Antitone fun i => markPos ζ₀ ζ (e (Sum.inl i)))
    (hRm : Monotone fun i => markPos ζ₀ ζ (e (Sum.inr i))) :
    ∃ (gW : ℝ≥0 → Ω → ℝ) (gL : Fin nL → ℝ≥0 → Ω → ℝ) (gR : Fin nR → ℝ≥0 → Ω → ℝ) (ζG : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ (fun i => markPos ζ₀ ζ (e (Sum.inl i)) - w₀)
        (fun i => markPos ζ₀ ζ (e (Sum.inr i)) - w₀) (fun i => markWt κ rr (e (Sum.inl i)))
        (fun i => markWt κ rr (e (Sum.inr i)))
        (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell)
        (usualAugmentation (Zhan.Retarget.timeChangeFilt 𝓕
          (isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
            (hH.measurable_bmClk (fun u => hB.2.1 u) hBc hS))
          (invClock_mono hH.continuous_bmClk fun ω => (hH.strictMono_bmClk ω).monotone))
          (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell))
        gW gL gR (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω) ζG ∧
      (∀ ω, ENNReal.ofReal (a ω (S ω)) ≤ ζG ω ∧ ∀ t : ℝ≥0, (t : ℝ) < a ω (S ω) →
        gW t ω = W' ω t - w₀ ∧ (∀ i, gL i t ω = imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inl i))) t - w₀) ∧
          ∀ j, gR j t ω = imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inr j))) t - w₀) ∧
      ∀ {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
        {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
        {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞},
        IsIntegratedSLEEvolution κ (fun i => markPos ζ₀ ζ (e (Sum.inl i)) - w₀)
          (fun i => markPos ζ₀ ζ (e (Sum.inr i)) - w₀) (fun i => markWt κ rr (e (Sum.inl i)))
          (fun i => markWt κ rr (e (Sum.inr i))) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
        ∀ (m : ℕ) (ts : Fin m → ℝ≥0) (Asets : Fin m → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
          (∀ j, MeasurableSet (Asets j)) →
          girsMeasure P (Real.sqrt κ) B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell)
              {ω | ∀ j, (ts j : ℝ≥0∞) < ζG ω ∧ (gW (ts j) ω, (fun i => gL i (ts j) ω), (fun i => gR i (ts j) ω),
                bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) (ts j) ω) ω) ∈ Asets j} =
            P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
              (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ Asets j} := by
  have hE := hH.isIntegratedSLEEvolution_img hκ hB hBc hS hS0 hBb e hw₀ hL hR hLa hRm
  have := (hH.isFilteredBrownianReal_bm hκ hB hBc hS hBb).isProbabilityMeasure'
  have hF : IsOrderedForceWord (fun i => markPos ζ₀ ζ (e (Sum.inl i)) - w₀)
      (fun i => markPos ζ₀ ζ (e (Sum.inr i)) - w₀) :=
    ⟨fun i j hij => sub_le_sub_right (hLa hij) _, fun i => (sub_neg.2 (hL i)).le,
      fun i j hij => sub_le_sub_right (hRm hij) _, fun i => (sub_pos.2 (hR i)).le⟩
  refine ⟨_, _, _, _, hE, fun ω => ⟨le_self_add, fun t ht => contState_img_of_lt _ _ _ _ _ ht⟩, ?_⟩
  intro Ω₂ m₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ m ts Asets hA
  exact IsIntegratedSLEEvolution.measure_killedState_eq_assembled hκ hF hE h₂ hA

end FrzD10Hyp

end Law

end InteractingSLE.ZhanGT4
