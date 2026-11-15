/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightFinRow

/-!
# Zhan's A.1 (Eight): the row martingales of the concrete Eight records

Packet PROVE-A1-EIGHTFIN. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (`ig1_followup_proofs.txt` L300–L425) and
follow-up 4 §2.5 (L739–L788).

A1-EIGHTSEED's `seedFieldInputM_of_eight` reduces the rectangle-wise Eight input `SeedFieldInputM` to named inputs,
among them the **row martingales** `hrow`, `hrowc` of the concrete records `eightRec` (A22's open "concrete two-view
identification"). Here they are proved (`eight_rows`) from the fused-density martingale (`row_martingale`), given
the stochastic half of the large curve's rows (`IsRowStoch`) and positive large exits; and
`seedFieldInputM_of_eight_rows` is `seedFieldInputM_of_eight` with `hrow`, `hrowc` replaced by these inputs.

* `eightRR_fused`: the Eight seed charges have vanishing fused exponent;
* `sixteen_div_kh`: `16/κ̂ = κ`;
* `eightRec_eq_srcRec`: a record at height `t ≤ T` reads the large path stopped at `T`;
* `eightView`: the enclosure data of one rectangle (`ViewSetup`) from A1-EIGHTSEED's pathwise hypotheses;
* **`eight_rows`**, **`seedFieldInputM_of_eight_rows`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1EightFin

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A1SeedField A1EightSeed A2X A1Patch A1Law

/-- **The Eight seed charges have vanishing fused exponent**: `−1/2 + Σ −(κ̂/4) r_m = 0` for `r = eightRR κ`
(`(ρ_L + ρ_R)/κ̂ = −2/κ̂`). -/
theorem eightRR_fused {κ : ℝ} (hκ : 0 < κ) : -1 / 2 + ∑ m, -(kh κ / 4) * eightRR κ m = 0 := by
  have hk : kh κ ≠ 0 := by unfold kh; positivity
  simp only [eightRR, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smallEightRhoL,
    smallEightRhoR]
  field_simp
  ring

/-- `16 / κ̂ = κ`. -/
theorem sixteen_div_kh {κ : ℝ} (hκ : κ ≠ 0) : 16 / kh κ = κ := by
  unfold kh
  field_simp

section Records

variable {X Y : Type*}

/-- **A record at height `t ≤ T` reads the large path stopped at `T`** (A1-EIGHTSEED's frozen paths are stopped at the
height itself). -/
theorem eightRec_eq_srcRec {κ p : ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {x : X} {y : Y} {t T : ℝ}
    (hc₂ : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 T)) (ht : 0 ≤ t) (htT : t ≤ T) :
    eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y) = srcRec (eightDrv W₁ S₁ m x) (S₁ m x) (frzPath W₂ p T y) t (kh κ)
      (eightRR κ) p ![Strip.extPath (VL₁ 0 · x), Strip.extPath (VR₁ 0 · x)] := by
  rcases htT.eq_or_lt with rfl | hlt
  · rfl
  · refine srcRec_congr_frozen (continuous_frzPath (hc₂.mono (Icc_subset_Icc_right hlt.le)) ht).continuousOn
      (continuous_frzPath hc₂ (ht.trans hlt.le)).continuousOn ht hlt fun s hs => ?_
    simp only [frzPath, A1Ref.stopDrv_eqOn _ t hs, A1Ref.stopDrv_eqOn _ T ⟨hs.1, hs.2.trans hlt.le⟩]

/-- **The enclosure data of one Eight rectangle** from a source record at the rectangle's positive large exit. -/
theorem viewSetup_of_isSourceRecord {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin 2 → ℝ} {W₂ : ℝ → ℝ} {t₂ : ℝ}
    {s : SeedData 2} {Vlo Vhi : ℝ → ℝ} {T : ℝ} (hpp : IsProtectedPair H₁ H₂ δ p q dd)
    (hrec : IsSourceRecord H₁ H₂ p Tm κ rr W₂ t₂ s Vlo Vhi T) (hV : s.V = ![Vlo, Vhi]) :
    ViewSetup H₁ H₂ δ p q dd Tm s.W W₂ T t₂ Vlo Vhi where
  pp := hpp
  cont₁ := hrec.own.cont
  zero₁ := hrec.own.zero
  pos₁ := hrec.own.pos
  le₁ := hrec.le₁
  K₁ := hrec.sub₁
  cont₂ := hrec.contW₂
  zero₂ := hrec.zeroW₂
  pos₂ := hrec.pos₂
  le₂ := hrec.le₂
  K₂ := hrec.sub₂
  lo := hrec.lo
  hi := hrec.hi
  drv := hrec.drv
  inj := fun u hu he => by
    have := hrec.inj u hu (a₁ := 0) (a₂ := 1)
    rw [hV] at this
    exact absurd (this he) (by decide)

end Records

/-- **The canonical protected point**: the small curve's source, `−p` in the large curve's frame, is protected from the
translated large enclosure by the separation `δ`, as soon as `0` lies in the closure of the small enclosure. -/
theorem disjoint_ball_neg_src {H₁ H₂ : Set ℂ} {δ p q dd : ℝ} (hpp : IsProtectedPair H₁ H₂ δ p q dd)
    (h0 : ((0 : ℝ) : ℂ) ∈ closure H₁) : Disjoint (ball ((-p : ℝ) : ℂ) δ) (transl (-p) H₂) := by
  refine Set.disjoint_left.2 fun z hz hzG => ?_
  obtain ⟨w, hw, rfl⟩ := hzG
  have h1 := le_norm_of_mem_closure (fun a ha z hz => by rw [norm_sub_rev]; exact hpp.sep z hz a ha) h0 hw
  rw [mem_ball, dist_eq_norm] at hz
  have e : w + ((-p : ℝ) : ℂ) - ((-p : ℝ) : ℂ) = w - ((0 : ℝ) : ℂ) := by push_cast; ring
  rw [e, norm_sub_rev] at hz
  linarith [hpp.sep_pos]

/-! ### The Eight rows -/

section Rows

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

omit mX in
/-- **The row martingales of the concrete Eight records** (`hrow`, `hrowc` of `seedFieldInputM_of_eight`): from
A1-EIGHTSEED's rectangle and pathwise hypotheses, positive large exits, and the stochastic half of the large curve's
rows (`IsRowStoch`, for one protected real point `x₀` left of every large enclosure), the rows of every rectangle's
seeded height field are martingales with continuous paths. -/
theorem eight_rows {P₂ : Measure Y} [IsProbabilityMeasure P₂] {κ p a : ℝ} (hκ : 0 < κ) {xL : Fin 1 → ℝ}
    {xR : Fin 2 → ℝ} {ρL : Fin 1 → ℝ} {ρR : Fin 2 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0)
    (H₁ H₂ : ℕ → Set ℂ) (δ q dd Tm : ℕ → ℝ)
    (h₂ : ∀ m, IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0))
    (hpp : ∀ m, IsProtectedPair (H₁ m) (H₂ m) (δ m) p (q m) (dd m))
    (hP : ∀ x, IsIntegratedSLEPath a xL xR ρL ρR (W₁ · x) (fun i s => VL₁ i s x) (fun i s => VR₁ i s x) (B₁ · x)
      (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0)
    (hgood₁ : ∀ m x, (S₁ m x : ℝ≥0∞) < ζ₁ x ∧ 0 < (S₁ m x : ℝ) ∧ (S₁ m x : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁ m)
    (hsep₁ : ∀ x (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ x → VL₁ 0 s x ≠ W₁ s x ∧ VR₁ 0 s x ≠ W₁ s x)
    (hc₂ : ∀ m y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (S₂ m y))) (h0₂ : ∀ y, W₂ 0 y = 0)
    (hgood₂ : ∀ m y, (S₂ m y : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ p (S₂ m y) y) (S₂ m y) ⊆ H₂ m)
    (hS₂pos : ∀ m y, 0 < (S₂ m y : ℝ))
    {x₀ ρ : ℕ → ℝ} (hρ : ∀ m, 0 < ρ m) (hx₀ : ∀ m, x₀ m < 0)
    (hx₀G : ∀ m, Disjoint (ball (x₀ m : ℂ) (ρ m)) (transl (-p) (H₂ m)))
    (hrowst : ∀ m, ∃ (B D : ℝ≥0 → Y → ℝ) (V : Y → ℝ → ℝ), IsRowStoch 𝓕₂ P₂ κ
      (fun y u => frzPath W₂ p (S₂ m y) y u - frzPath W₂ p (S₂ m y) y 0) (S₂ m) (x₀ m) B D V) :
    (∀ m x (s : ℝ), 0 ≤ s → s ≤ S₁ m x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s
        (min (t : ℝ) (S₂ m y))) 𝓕₂ P₂) ∧
    (∀ m x y (s : ℝ), 0 ≤ s → s ≤ S₁ m x →
      Continuous fun t : ℝ≥0 => seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s
        (min (t : ℝ) (S₂ m y))) := by
  -- the source record at the positive large exit
  have hrec : ∀ m x y, IsSourceRecord (H₁ m) (H₂ m) p (Tm m) (kh κ) (eightRR κ) (frzPath W₂ p (S₂ m y) y) (S₂ m y)
      (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m (S₂ m y) (x, y)) (Strip.extPath (VL₁ 0 · x))
      (Strip.extPath (VR₁ 0 · x)) (S₁ m x) := fun m x y => by
    have hne : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VL₁ 0 s x ≠ W₁ s x ∧ VR₁ 0 s x ≠ W₁ s x := fun s hs hsS =>
      hsep₁ x s hs (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsS) (hgood₁ m x).1)
    exact isSourceRecord_eightRec (hP x) hxL hxR (hgood₁ m x).1 (hgood₁ m x).2.1 (fun s hs hsS => (hne s hs hsS).1)
      (fun s hs hsS => (hne s hs hsS).2) (hc₂ m y) (h0₂ y) (hS₂pos m y) (hgood₂ m y).1 (hgood₁ m x).2.2.1
      (hpp m).sep_pos (hpp m).sep (hgood₁ m x).2.2.2 (hgood₂ m y).2
  have hset : ∀ m x y, ViewSetup (H₁ m) (H₂ m) (δ m) p (q m) (dd m) (Tm m) (eightDrv W₁ S₁ m x)
      (frzPath W₂ p (S₂ m y) y) (S₁ m x) (S₂ m y) (Strip.extPath (VL₁ 0 · x)) (Strip.extPath (VR₁ 0 · x)) :=
    fun m x y => viewSetup_of_isSourceRecord (hpp m) (hrec m x y) rfl
  -- the row process is the row of `srcRec` along the stopped large path
  have hproc : ∀ m x (s : ℝ) (t : ℝ≥0) y,
      seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s (min (t : ℝ) (S₂ m y)) =
        Real.exp ((srcRec (eightDrv W₁ S₁ m x) (S₁ m x) (frzPath W₂ p (S₂ m y) y) (min (t : ℝ) (S₂ m y)) (kh κ)
          (eightRR κ) p ![Strip.extPath (VL₁ 0 · x), Strip.extPath (VR₁ 0 · x)]).normEll s -
          (srcRec (eightDrv W₁ S₁ m x) (S₁ m x) (frzPath W₂ p (S₂ m y) y) (min (t : ℝ) (S₂ m y)) (kh κ)
            (eightRR κ) p ![Strip.extPath (VL₁ 0 · x), Strip.extPath (VR₁ 0 · x)]).normEll 0) := by
    intro m x s t y
    rw [seedHeightField, eightRec_eq_srcRec (hc₂ m y) (le_min t.coe_nonneg (S₂ m y).coe_nonneg) (min_le_right _ _)]
  have hk : 0 < kh κ := by unfold kh; positivity
  have hmain : ∀ m x (s : ℝ), 0 < s → s ≤ S₁ m x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s
        (min (t : ℝ) (S₂ m y))) 𝓕₂ P₂ ∧
      ∀ y, Continuous fun t : ℝ≥0 => seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s
        (min (t : ℝ) (S₂ m y)) := by
    intro m x s hs hsS
    obtain ⟨B, D, V, hst⟩ := hrowst m
    rw [← sixteen_div_kh hκ.ne'] at hst
    obtain ⟨hmart, hcont⟩ := row_martingale (hpp m) hk (eightRR_fused hκ) (hset m x) (h₂ m) (hρ m) (hx₀ m) (hx₀G m) hst
      (a := s) ⟨hs, hsS⟩
    refine ⟨?_, fun y => ?_⟩
    · have e : (fun (t : ℝ≥0) y => seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s
          (min (t : ℝ) (S₂ m y))) = _ := funext₂ (hproc m x s)
      rw [e]
      exact hmart
    · have e : (fun t : ℝ≥0 => seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s
          (min (t : ℝ) (S₂ m y))) = _ := funext fun t => hproc m x s t y
      rw [e]
      exact hcont y
  refine ⟨fun m x s hs hsS => ?_, fun m x y s hs hsS => ?_⟩
  · rcases hs.eq_or_lt with rfl | hpos
    · simp only [seedHeightField_zero_left]
      exact martingale_const _ _ _
    · exact (hmain m x s hpos hsS).1
  · rcases hs.eq_or_lt with rfl | hpos
    · simp only [seedHeightField_zero_left]
      exact continuous_const
    · exact (hmain m x s hpos hsS).2 y

/-- **A1-EIGHTSEED's rectangle-wise Eight input with the rows discharged**: `seedFieldInputM_of_eight` with its row
hypotheses `hrow`, `hrowc` replaced by positive large exits and the stochastic half of the large curve's rows
(`IsRowStoch` at a protected real point `x₀`), through `eight_rows`. -/
theorem seedFieldInputM_of_eight_rows {P₁ : Measure X} {P₂ : Measure Y} [IsProbabilityMeasure P₂] {κ p a : ℝ}
    (hκ : 0 < κ) {xL : Fin 1 → ℝ} {xR : Fin 2 → ℝ} {ρL : Fin 1 → ℝ} {ρR : Fin 2 → ℝ} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {Law : Measure (X × Y) → Prop}
    (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0)
    (H₁ H₂ : ℕ → Set ℂ) (δ q dd Tm : ℕ → ℝ)
    (h₁ : ∀ m, IsStoppingTime 𝓕₁ fun x => (S₁ m x : WithTop ℝ≥0))
    (h₂ : ∀ m, IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0))
    (hpp : ∀ m, IsProtectedPair (H₁ m) (H₂ m) (δ m) p (q m) (dd m))
    (hU : ∀ m, ∃ U : ℝ≥0, (∀ x, S₁ m x ≤ U) ∧ ∀ y, S₂ m y ≤ U)
    (hP : ∀ x, IsIntegratedSLEPath a xL xR ρL ρR (W₁ · x) (fun i s => VL₁ i s x) (fun i s => VR₁ i s x) (B₁ · x)
      (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0)
    (hgood₁ : ∀ m x, (S₁ m x : ℝ≥0∞) < ζ₁ x ∧ 0 < (S₁ m x : ℝ) ∧ (S₁ m x : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁ m)
    (hsep₁ : ∀ x (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ x → VL₁ 0 s x ≠ W₁ s x ∧ VR₁ 0 s x ≠ W₁ s x)
    (hc₂ : ∀ m y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (S₂ m y))) (h0₂ : ∀ y, W₂ 0 y = 0)
    (hgood₂ : ∀ m y, (S₂ m y : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ p (S₂ m y) y) (S₂ m y) ⊆ H₂ m)
    (hS₂pos : ∀ m y, 0 < (S₂ m y : ℝ))
    (hstoch : ∀ m y, 0 < (S₂ m y : ℝ) → ∃ B D : ℝ≥0 → X → ℝ,
      IsColumnStoch 𝓕₁ P₁ (kh κ) (fun x => eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m (S₂ m y) (x, y)) (S₁ m) B D)
    {x₀ ρ : ℕ → ℝ} (hρ : ∀ m, 0 < ρ m) (hx₀ : ∀ m, x₀ m < 0)
    (hx₀G : ∀ m, Disjoint (ball (x₀ m : ℂ) (ρ m)) (transl (-p) (H₂ m)))
    (hrowst : ∀ m, ∃ (B D : ℝ≥0 → Y → ℝ) (V : Y → ℝ → ℝ), IsRowStoch 𝓕₂ P₂ κ
      (fun y u => frzPath W₂ p (S₂ m y) y u - frzPath W₂ p (S₂ m y) y 0) (S₂ m) (x₀ m) B D V)
    (hmeas : ∀ m, IsFieldMeas (seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m)) (fun _ : Unit => S₁ m)
      (fun _ : Unit => S₂ m))
    (hlaw : ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (h₁ m).measurableSpace (h₂ m).measurableSpace P₁ P₂ μ
        fun ω => ENNReal.ofReal (seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) ω (S₁ m ω.1) (S₂ m ω.2))) →
      Law μ) :
    SeedFieldInputM P₁ P₂ (kh κ) Law := by
  obtain ⟨hrow, hrowc⟩ := eight_rows hκ 𝓕₂ S₁ S₂ H₁ H₂ δ q dd Tm h₂ hpp hP hxL hxR hgood₁ hsep₁ hc₂ h0₂ hgood₂
    hS₂pos hρ hx₀ hx₀G hrowst
  exact seedFieldInputM_of_eight 𝓕₁ 𝓕₂ S₁ S₂ H₁ H₂ δ q dd Tm h₁ h₂ hpp hU hP hxL hxR hgood₁ hsep₁ hc₂ h0₂ hgood₂
    hstoch hrow hrowc hmeas hlaw

end Rows

end InteractingSLE.ZhanGT4.A1EightFin
