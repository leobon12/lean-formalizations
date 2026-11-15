/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualTwoDirCont

/-!
# The height-`0` marginal factors of the dual coupling density

Packet PROVE-ZHAN-GT4-A16. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L300–L407, R38): "The positive density `M(S₁, S₂)`, with respect to the product of the two
marginal laws, has expectation one, by optional sampling successively in the two coordinates. Its marginals are
unchanged."

The product density of A15 is `D = M*_s(T, T) · m₁ · m₂` with the marginal factors at height `0`:
`m₁ = Ñ_s(max S₁, 0)/Ñ_s(0, 0)` (curve `2`'s hull empty) and `m₂ = Ñ_t(0, max S₂)/Ñ_t(0, 0)`.

* **Marks of a frozen curve** (A15's `hne`, `hinj`): a real point alive for a frozen curve keeps a mark different from
  the frozen tip, and alive marks stay distinct (`frzMarks_ne_of_isForwardSol`, `frzMarks_injective_of_isForwardSol`);
  hence, for protected enclosures, the `s`-view normalised density is continuous in the frozen height
  (`TwoEncl.continuousOn_normLog_sEll_height`) with no further hypothesis.
* **Intrinsic dependence at height `0`**: at height `0` the frozen hull is empty, the chart is the identity and every
  mark is itself, for every continuous frozen path (`frzChart_zero_eq_id`, `frzMarks_zero_eq_self`), so the canonical
  image data and the `s`-view `ℓ` at height `0` depend on the frozen curve only through its starting point
  (`imgSelD_zero_congr`, `sEll_zero_congr`), and symmetrically the `t`-view `ℓ` at height `0` depends on curve `1` only
  through `W₁ 0` (`tEll_zero_congr`).
-/

set_option autoImplicit false

noncomputable section

open Finset Set Complex MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-! ### Marks of a frozen curve -/

section Marks

variable {n : ℕ}

/-- Translating a driver and a real starting point by the same constant does not change the forward solution. -/
theorem isForwardSol_sub_const_iff {W : ℝ → ℝ} {c z T : ℝ} {u : ℝ → ℂ} :
    IsForwardSol (fun s => W s - c) (((z - c : ℝ)) : ℂ) T u ↔ IsForwardSol W (z : ℂ) T u := by
  have e : ∀ t, (((z - c : ℝ)) : ℂ) - (((W t - c : ℝ)) : ℂ) = (z : ℂ) - (W t : ℂ) := fun t => by
    push_cast; ring
  simp only [IsForwardSol, e]

/-- **A mark alive for the frozen curve differs from the frozen tip**: the forward solution from a real point is real and
never vanishes. -/
theorem frzMarks_ne_of_isForwardSol {V : ℝ → ℝ} (hV : Continuous V) {p : Fin n → ℝ} {m : Fin n} {T u : ℝ}
    {x : ℝ → ℂ} (hx : IsForwardSol V ((p m : ℝ) : ℂ) T x) (hu : u ∈ Icc (0 : ℝ) T) : frzMarks V p u m ≠ V u := by
  have he := InteractingSLE.fwdMap_eq_of_isForwardSol hV hx hu
  have him := fwdMap_real_im hV hx hu
  have hne := (hx.2 u hu).1
  intro h
  unfold frzMarks at h
  have hre : (fwdMap V u (p m)).re = 0 := by linarith
  apply hne
  rw [← he]
  exact Complex.ext hre him

/-- **Alive marks of the frozen curve stay distinct** (the linear identity `f_u(w) − f_u(z) = (w − z) e^{…}`). -/
theorem frzMarks_injective_of_isForwardSol {V : ℝ → ℝ} (hV : Continuous V) {p : Fin n → ℝ}
    (hp : Function.Injective p) {T u : ℝ} (hx : ∀ m, ∃ x, IsForwardSol V ((p m : ℝ) : ℂ) T x)
    (hu : u ∈ Icc (0 : ℝ) T) : Function.Injective (frzMarks V p u) := by
  intro m k hmk
  obtain ⟨x, hxm⟩ := hx m
  obtain ⟨y, hyk⟩ := hx k
  have h1 := InteractingSLE.fwdMap_eq_of_isForwardSol hV hxm hu
  have h2 := InteractingSLE.fwdMap_eq_of_isForwardSol hV hyk hu
  have hre : (fwdMap V u (p m)).re = (fwdMap V u (p k)).re := by unfold frzMarks at hmk; linarith
  have heq : fwdMap V u (p m) = fwdMap V u (p k) :=
    Complex.ext hre (by rw [fwdMap_real_im hV hxm hu, fwdMap_real_im hV hyk hu])
  have e := QuantumZipper.FwdHolo.sol_sub_eq hxm hyk u hu
  rw [← h1, ← h2, heq, sub_self] at e
  rcases mul_eq_zero.1 e.symm with h | h
  · exact hp (by exact_mod_cast (sub_eq_zero.1 h).symm)
  · exact absurd h (Complex.exp_ne_zero _)

end Marks

namespace TwoEncl

variable {ι : Type*} [Fintype ι] {n : ℕ} {W₁ W₂ : ℝ → ℝ} {S₁ S₂ : ι → ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ}
  {p : Fin n → ℝ} {Tm : ℝ} (h : TwoEncl W₁ W₂ S₁ S₂ H₁ H₂ δ q d p Tm)
include h

/-- In the `t`-view (translated by `−W₂ 0`), the frozen marks of curve `1` differ from its tip (A15's `hne`). -/
theorem tMarks_ne (i : ι) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (S₁ i)) (m : Fin n) :
    frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u m ≠ W₁ u - W₂ 0 := by
  obtain ⟨x, hx⟩ := (h.twoViewMarks i).alive₁ m
  exact frzMarks_ne_of_isForwardSol (h.cont₁.sub continuous_const) (p := fun m => p m - W₂ 0) (m := m)
    (isForwardSol_sub_const_iff.2 hx) hu

/-- In the `t`-view, the frozen marks of curve `1` are distinct (A15's `hinj`). -/
theorem tMarks_injective (i : ι) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (S₁ i)) :
    Function.Injective (frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u) := by
  refine frzMarks_injective_of_isForwardSol (h.cont₁.sub continuous_const)
    (fun m k hmk => h.pinj (by simpa using hmk)) (fun m => ?_) hu
  obtain ⟨x, hx⟩ := (h.twoViewMarks i).alive₁ m
  exact ⟨x, isForwardSol_sub_const_iff.2 hx⟩

/-- **The `s`-view normalised density is continuous in the frozen height**, on every rectangle of protected
enclosures (A15's `TwoViewRect.continuousOn_normLog_sEll_height` with `hne`, `hinj` discharged). -/
theorem continuousOn_normLog_sEll_height {κ : ℝ} (hκ : κ ≠ 0) (r : Fin n → ℝ) (i : ι) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (S₁ i)) :
    ContinuousOn (fun y => normLog (sEll κ r W₁ W₂ (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) p) x y)
      (Icc 0 (S₂ i)) :=
  (h.twoViewRect i).continuousOn_normLog_sEll_height hκ r p h.cont₁ h.cont₂ (h.S₂pos i) (h.twoViewMarks i)
    (fun _ hu m => h.tMarks_ne i hu m) (fun _ hu => h.tMarks_injective i hu) hx

end TwoEncl

/-! ### Height `0`: the frozen curve is seen only through its starting point -/

section Zero

variable {n : ℕ}

/-- **At height `0` the chart of a frozen curve is the identity**, everywhere (also at the start, where the forward map
takes its junk value `0`). -/
theorem frzChart_zero_eq_id (V : ℝ → ℝ) : frzChart V 0 = id := by
  funext z
  simp only [frzChart, id]
  by_cases hz : z = (V 0 : ℂ)
  · have hno : ¬ ∃ u, IsForwardSol V z 0 u := by
      rintro ⟨u, hu⟩
      have h0 := hu.2 0 ⟨le_rfl, le_rfl⟩
      apply h0.1
      rw [h0.2, hz, intervalIntegral.integral_same, sub_self, add_zero]
    simp only [QuantumZipper.fwdMap, hno, ↓reduceDIte, zero_add]
    exact hz.symm
  · have hex : ∃ u, IsForwardSol V z 0 u := ⟨fun _ => z - V 0, continuousOn_const, fun t ht => by
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst ht0
      refine ⟨sub_ne_zero.2 hz, ?_⟩
      rw [intervalIntegral.integral_same, add_zero]⟩
    have h0 := hex.choose_spec.2 0 ⟨le_rfl, le_rfl⟩
    simp only [QuantumZipper.fwdMap, hex, ↓reduceDIte]
    rw [h0.2, intervalIntegral.integral_same, add_zero, sub_add_cancel]

/-- **At height `0` every mark of a frozen curve is itself.** -/
theorem frzMarks_zero_eq_self (V : ℝ → ℝ) (p : Fin n → ℝ) : frzMarks V p 0 = p := by
  funext m
  have h := congrArg Complex.re (congrFun (frzChart_zero_eq_id V) (p m : ℂ))
  simp only [frzChart, id, Complex.add_re, Complex.ofReal_re] at h
  exact h

open scoped Classical in
/-- `imgSelD` as a function of the frozen hull and chart. -/
def imgSelAux (W : ℝ → ℝ) (A : Set ℂ) (φ : ℂ → ℂ) (w : ℝ) : (ℝ → ℝ) × (ℝ → ℝ) :=
  if h : ∃ a W', OwnData W A φ w a W' then (h.choose, h.choose_spec.choose) else (0, 0)

theorem imgSelD_eq_imgSelAux (W V : ℝ → ℝ) (w y : ℝ) :
    imgSelD W V w y = imgSelAux W (fwdHull V y) (frzChart V y) w := rfl

/-- **The canonical image data at height `0` do not see the frozen curve** (continuous frozen paths). -/
theorem imgSelD_zero_congr (W : ℝ → ℝ) {V V' : ℝ → ℝ} (hV : Continuous V) (hV' : Continuous V') (w : ℝ) :
    imgSelD W V w 0 = imgSelD W V' w 0 := by
  rw [imgSelD_eq_imgSelAux, imgSelD_eq_imgSelAux, QuantumZipper.RS.fwdHull_zero_eq_empty hV,
    QuantumZipper.RS.fwdHull_zero_eq_empty hV', frzChart_zero_eq_id, frzChart_zero_eq_id]

variable {ι : Type*} [Fintype ι]

/-- The staircase width at height `0` is the largest column end. -/
theorem stairH_zero_eq_maxIn {S₁ S₂ : ι → ℝ} (hS₂ : ∀ i, 0 ≤ S₂ i) : stairH S₂ S₁ 0 = maxIn (stairCols S₁) := by
  unfold stairH maxIn stairCols
  congr 3
  exact filter_true_of_mem fun i _ => hS₂ i

/-- **The `s`-view `ℓ` at height `0` sees the frozen curve `2` only through its starting point** (and the staircase
only through its column ends). -/
theorem sEll_zero_congr (κ : ℝ) (r p : Fin n → ℝ) (W₁ : ℝ → ℝ) {W₂ W₂' : ℝ → ℝ} (hW₂ : Continuous W₂)
    (hW₂' : Continuous W₂') (h0 : W₂ 0 = W₂' 0) (S₁ : ι → ℝ) {S₂ S₂' : ι → ℝ} (hS₂ : ∀ i, 0 ≤ S₂ i)
    (hS₂' : ∀ i, 0 ≤ S₂' i) (x : ℝ) :
    sEll κ r W₁ W₂ (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) p x 0 =
      sEll κ r W₁ W₂' (sSelA W₁ W₂' S₁ S₂') (sSelW W₁ W₂' S₁ S₂') p x 0 := by
  have hw : stairH S₂ S₁ 0 = stairH S₂' S₁ 0 := by rw [stairH_zero_eq_maxIn hS₂, stairH_zero_eq_maxIn hS₂']
  have hsel : imgSelD W₁ W₂ (stairH S₂ S₁ 0) 0 = imgSelD W₁ W₂' (stairH S₂' S₁ 0) 0 := by
    rw [hw]; exact imgSelD_zero_congr W₁ hW₂ hW₂' _
  simp only [sEll, sView, sSelA, sSelW, hsel, frzChart_zero_eq_id, frzMarks_zero_eq_self, h0]

/-- **The `t`-view `ℓ` at curve-`1` height `0` sees curve `1` only through its starting point** (and the staircase
only through the column ends of curve `2`). -/
theorem tEll_zero_congr (κ : ℝ) (r p : Fin n → ℝ) {W₁ W₁' : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₁' : Continuous W₁')
    (h0 : W₁ 0 = W₁' 0) (W₂ : ℝ → ℝ) {S₁ S₁' : ι → ℝ} (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₁' : ∀ i, 0 ≤ S₁' i) (S₂ : ι → ℝ)
    (y : ℝ) :
    tEll κ r W₁ W₂ (tSelA W₁ W₂ S₁ S₂) (tSelW W₁ W₂ S₁ S₂) p 0 y =
      tEll κ r W₁' W₂ (tSelA W₁' W₂ S₁' S₂) (tSelW W₁' W₂ S₁' S₂) p 0 y := by
  have hw : stairH S₁ S₂ 0 = stairH S₁' S₂ 0 := by rw [stairH_zero_eq_maxIn hS₁, stairH_zero_eq_maxIn hS₁']
  have hsel : imgSelD (fun s => W₂ s - W₂ 0) (fun s => W₁ s - W₂ 0) (stairH S₁ S₂ 0) 0 =
      imgSelD (fun s => W₂ s - W₂ 0) (fun s => W₁' s - W₂ 0) (stairH S₁' S₂ 0) 0 := by
    rw [hw]; exact imgSelD_zero_congr _ (hW₁.sub continuous_const) (hW₁'.sub continuous_const) _
  simp only [tEll, tView, tSelA, tSelW, hsel, frzChart_zero_eq_id, frzMarks_zero_eq_self, h0]

end Zero

/-! ### A14's column product with a low height cap -/

section Low

variable {Ω : Type*} {ι : Type*} [Fintype ι] {n : ℕ}

/-- Below the height cap, A14's staircase width is the canonical one. -/
theorem coe_frzWidth_eq_stairH_of_le {S₁ : ι → Ω → ℝ≥0} {S₂ : ι → ℝ} {tb y : ℝ} (hy : y ≤ tb) (ω : Ω) :
    ((frzWidth S₁ S₂ tb y ω : ℝ≥0) : ℝ) = stairH S₂ (fun i => (S₁ i ω : ℝ)) y := by
  have hfilt : (univ.filter fun i => y ≤ min (S₂ i) tb) = univ.filter fun i => y ≤ S₂ i :=
    filter_congr fun i _ => by rw [le_min_iff]; exact and_iff_left hy
  unfold frzWidth stairH
  rw [hfilt]
  apply le_antisymm
  · have h0 : 0 ≤ (insert 0 ((univ.filter fun i => y ≤ S₂ i).image fun i => (S₁ i ω : ℝ))).max'
        (insert_nonempty _ _) := le_max' _ _ (mem_insert_self _ _)
    rw [← NNReal.coe_mk _ h0, NNReal.coe_le_coe]
    refine Finset.sup_le fun i hi => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_mk]
    exact le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun i => (S₁ i ω : ℝ)) hi))
  · refine max'_le _ _ _ fun x hx => ?_
    rcases mem_insert.1 hx with rfl | hx
    · exact NNReal.coe_nonneg _
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun i => S₁ i ω) hi)

/-- **Below the height cap, A14's density is `exp` of the canonical `s`-view `ℓ`.** -/
theorem frzDens_eq_exp_sEll_of_le {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W₂ : ℝ → ℝ} {S₁ : ι → Ω → ℝ≥0} {S₂ : ι → ℝ}
    {tb y : ℝ} (hy : y ≤ tb) (rr p : Fin n → ℝ) (ω : Ω) (x : ℝ) :
    frzDens κ B W₂ S₁ S₂ tb rr p ω x y =
      Real.exp (sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
        (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p x y) := by
  have hsel : frzImgSel κ B W₂ S₁ S₂ tb y ω =
      imgSelD (drive κ B ω) W₂ (stairH S₂ (fun i => (S₁ i ω : ℝ)) y) y := by
    have e1 : frzImgSel κ B W₂ S₁ S₂ tb y ω = imgSelD (drive κ B ω) W₂ (frzWidth S₁ S₂ tb y ω : ℝ) y := rfl
    rw [e1, coe_frzWidth_eq_stairH_of_le hy ω]
  unfold frzDens
  rw [frzN_eq_sView]
  simp only [sEll, sView, sSelA, sSelW, hsel]

/-- **A14's column product with a height cap below every rectangle height** is the `s`-view normalised density at
(largest column end, cap) times the curve-`1` marginal factor at height `0`. -/
theorem colProd_frzDens_low {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W₂ : ℝ → ℝ} {S₁ : ι → Ω → ℝ≥0} {S₂ : ι → ℝ} {tb : ℝ}
    (htb : ∀ i, tb ≤ S₂ i) (rr p : Fin n → ℝ) {s : ℝ≥0} {ω : Ω} (hs : ∀ i, S₁ i ω ≤ s) :
    colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb s ω =
      Real.exp (normLog (sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
          (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p) (maxIn (stairCols fun i => (S₁ i ω : ℝ))) tb) *
        Real.exp (sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
            (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p (maxIn (stairCols fun i => (S₁ i ω : ℝ))) 0 -
          sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
            (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p 0 0) := by
  rw [colProd_eq_colProdT _ _ _ hs]
  unfold colProdT
  set L := sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
    (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p with hL
  have hmin : ∀ c ∈ colEnds S₁ ω, min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) tb = tb := fun c hc => by
    obtain ⟨i, rfl⟩ := mem_colEnds.1 hc
    exact min_eq_right ((htb i).trans (le_stairH le_rfl))
  have hprod : ∏ c ∈ colEnds S₁ ω, (frzDens κ B W₂ S₁ S₂ tb rr p ω c
      (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) tb) / frzDens κ B W₂ S₁ S₂ tb rr p ω (prevIn (colEnds S₁ ω) c)
      (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) tb)) = Real.exp (∑ c ∈ colEnds S₁ ω, (L c tb -
        L (prevIn (colEnds S₁ ω) c) tb)) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [hmin c hc, frzDens_eq_exp_sEll_of_le le_rfl, frzDens_eq_exp_sEll_of_le le_rfl, ← Real.exp_sub]
  rw [hprod, sum_sub_prevIn (colEnds S₁ ω) (fun c hc => nonneg_of_mem_colEnds hc) fun c => L c tb,
    ← Real.exp_add]
  congr 1
  show L (maxIn (colEnds S₁ ω)) tb - L 0 tb = _
  unfold normLog colEnds
  ring

end Low

/-! ### The curve-`1` marginal factor has mean one -/

section MeanOne

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {n : ℕ} {ι : Type*}
  [Fintype ι]

/-- **The height-`0` marginal factor of curve `1` has mean one** (§A.1.3, "by optional sampling successively in the
two coordinates"): for ordinary `SLE_κ` (driver `√κ B`) with exit times `S₁ i` from protected enclosures and any frozen
second curve `W₂` with the enclosure data of A14's `martingale_colProd_frozen`,
`E[Ñ_s(max S₁, 0)/Ñ_s(0, 0)] = 1`, with `Ñ_s = exp ℓ` the canonical `s`-view density. Proof: A14's bounded column
martingale with height cap `t̄ ≤ min S₂` has mean one and equals `exp(normLog ℓ (max S₁, t̄)) · Ñ_s(max S₁, 0)/Ñ_s(0, 0)`
(`colProd_frzDens_low`); as `t̄ ↓ 0` the first factor tends to `1` by continuity in the frozen height
(`TwoEncl.continuousOn_normLog_sEll_height`), and dominated convergence (A14's uniform bound) gives the claim. -/
theorem integral_exp_sMarg_eq_one {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {H₁ H₂ : ι → Set ℂ} (hH₁ : ∀ i, IsHPHull (H₁ i)) (hH₂ : ∀ i, IsHPHull (H₂ i)) {δ : ι → ℝ}
    (hδ : ∀ i, 0 < δ i) (hsep : ∀ i, ∀ a ∈ H₂ i, ∀ z ∈ H₁ i, 2 * δ i ≤ ‖a - z‖) {q d : ι → ℝ}
    (hd : ∀ i, 0 < d i) (hq : ∀ i, 0 < q i) (hqH : ∀ i, Disjoint (Metric.ball (q i : ℂ) (2 * d i)) (H₁ i ∪ H₂ i))
    {p : Fin n → ℝ} (hpH : ∀ i m, Disjoint (Metric.ball (p m : ℂ) (2 * d i)) (H₁ i ∪ H₂ i))
    (hpinj : Function.Injective p) {Tm : ℝ} (rr : Fin n → ℝ)
    {S₁ : ι → Ω → ℝ≥0} (hS₁ : ∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0)) (hS₁0 : ∀ i ω, 0 < S₁ i ω)
    (hS₁m : ∀ i ω, (S₁ i ω : ℝ) ≤ Tm) (hK₁ : ∀ i ω, fwdHull (drive κ B ω) (S₁ i ω) ⊆ H₁ i)
    {W₂ : ℝ → ℝ} (hW₂ : Continuous W₂) (hW₂H : ∀ i, ((W₂ 0 : ℝ) : ℂ) ∈ closure (H₂ i)) (hqW : ∀ i, q i < W₂ 0)
    {S₂ : ι → ℝ} (hS₂0 : ∀ i, 0 < S₂ i) (hS₂m : ∀ i, S₂ i ≤ Tm) (hK₂ : ∀ i, fwdHull W₂ (S₂ i) ⊆ H₂ i) :
    ∫ ω, Real.exp (sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
        (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p (maxIn (stairCols fun i => (S₁ i ω : ℝ))) 0 -
      sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
        (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p 0 0) ∂P = 1 := by
  obtain ⟨K, hK⟩ := martingale_colProd_frozen (𝓕 := 𝓕) (P := P) hκ hB hBc hB0 hH₁ hH₂ hδ hsep hd hq hqH hpH
    hpinj Tm rr
  have hP : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  obtain ⟨c, hc, hcS⟩ := exists_pos_le_of_fintype S₂ hS₂0
  -- the height caps `t̄_k = c/(k + 1) ↓ 0`
  set tb : ℕ → ℝ := fun k => c * (1 / ((k : ℝ) + 1)) with htbdef
  have htb0 : ∀ k, 0 < tb k := fun k => by positivity
  have htbS : ∀ k i, tb k ≤ S₂ i := fun k i => by
    refine le_trans ?_ (hcS i)
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    calc tb k = c * (1 / ((k : ℝ) + 1)) := rfl
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left h1 hc.le
      _ = c := mul_one c
  have htbT : Tendsto tb atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
    rwa [mul_zero] at this
  -- a time after every exit
  set s₀ : ℝ≥0 := Tm.toNNReal with hs₀
  have hS₁s : ∀ i ω, S₁ i ω ≤ s₀ := fun i ω => by
    rw [← NNReal.coe_le_coe, hs₀, Real.coe_toNNReal']; exact (hS₁m i ω).trans (le_max_left _ _)
  set F : ℕ → Ω → ℝ := fun k ω => colProd (frzDens κ B W₂ S₁ S₂ (tb k) rr p) S₁ S₂ (tb k) s₀ ω with hFdef
  have hMk := fun k => hK hS₁ hS₁0 hS₁m hK₁ hW₂ hW₂H hqW hS₂0 hS₂m hK₂ (htb0 k)
  have hint : ∀ k, ∫ ω, F k ω ∂P = 1 := fun k =>
    (integral_colProd_eq_one (fun ω x y => Real.exp_pos _) (hMk k).1).1 s₀
  have hmeas : ∀ k, AEStronglyMeasurable (F k) P := fun k =>
    (((hMk k).1.1 s₀).mono (𝓕.le s₀)).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ ω ∂P, ‖F k ω‖ ≤ K := fun k => Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact (hMk k).2.2 s₀ ω
  -- the pointwise limit
  have hlim : ∀ ω, Tendsto (fun k => F k ω) atTop (𝓝 (Real.exp (sEll κ rr (drive κ B ω) W₂
      (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p
      (maxIn (stairCols fun i => (S₁ i ω : ℝ))) 0 - sEll κ rr (drive κ B ω) W₂
      (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p
      0 0))) := by
    intro ω
    set L := sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
      (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p with hL
    set X := maxIn (stairCols fun i => (S₁ i ω : ℝ)) with hX
    have hF : (fun k => F k ω) = fun k => Real.exp (normLog L X (tb k)) * Real.exp (L X 0 - L 0 0) := by
      funext k
      exact colProd_frzDens_low (htbS k) rr p (hS₁s · ω)
    rw [hF]
    have hcont : Tendsto (fun k => normLog L X (tb k)) atTop (𝓝 0) := by
      by_cases hX0 : X = 0
      · simp only [hX0, normLog_zero_left]
        exact tendsto_const_nhds
      · have hmem : X ∈ insert 0 (stairCols fun i => (S₁ i ω : ℝ)) := max'_mem _ _
        rcases Finset.mem_insert.1 hmem with h0 | hmem
        · exact absurd h0 hX0
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hmem
        have hE : TwoEncl (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂ H₁ H₂ δ q d p Tm :=
          { cont₁ := QuantumZipper.drive_continuous (hBc ω), cont₂ := hW₂,
            zero₁ := QuantumZipper.drive_zero (hB0 ω), hull₁ := hH₁, hull₂ := hH₂, δpos := hδ, sep := hsep,
            dpos := hd, qpos := hq, qH := hqH, pH := hpH, pinj := hpinj, start₂ := hW₂H, qW := hqW,
            S₁pos := fun i => NNReal.coe_pos.2 (hS₁0 i ω), S₂pos := hS₂0, S₁le := fun i => hS₁m i ω,
            S₂le := hS₂m, K₁ := fun i => hK₁ i ω, K₂ := hK₂ }
        have hXi : X ∈ Icc (0 : ℝ) (S₁ i ω) := ⟨maxIn_nonneg _, hi.ge⟩
        have hc := hE.continuousOn_normLog_sEll_height hκ.ne' rr i hXi
        have hw : Tendsto tb atTop (𝓝[Icc 0 (S₂ i)] 0) :=
          tendsto_nhdsWithin_iff.2 ⟨htbT, Eventually.of_forall fun k => ⟨(htb0 k).le, htbS k i⟩⟩
        have h := (hc 0 ⟨le_rfl, (hS₂0 i).le⟩).tendsto.comp hw
        rwa [normLog_zero_right] at h
    have h := ((Real.continuous_exp.tendsto 0).comp hcont).mul_const (Real.exp (L X 0 - L 0 0))
    rwa [Real.exp_zero, one_mul] at h
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => K) hmeas (integrable_const K) hbound
    (Eventually.of_forall hlim)
  have h1 : Tendsto (fun k => ∫ ω, F k ω ∂P) atTop (𝓝 1) := by
    simp only [hint]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hDCT h1

/-- **The `s`-direction mean (D12)–(D11), curve `2` frozen** (Fubini's inner integral in the other order): for every
frozen continuous path `W₂` of curve `2` (from `closure (H₂ i)`, in `H₂ i` up to the heights `S₂ i`) and curve `1` =
`√κ B` with exit times `S₁ i`, `E[M*_s(T, T) · Ñ_s(max S₁, 0)/Ñ_s(0, 0)] = 1`, with `M*_s` the (D11) patch of the
canonical `s`-view normalised density. -/
theorem integral_patch_mul_sMarg_eq_one {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {H₁ H₂ : ι → Set ℂ} (hH₁ : ∀ i, IsHPHull (H₁ i)) (hH₂ : ∀ i, IsHPHull (H₂ i)) {δ : ι → ℝ}
    (hδ : ∀ i, 0 < δ i) (hsep : ∀ i, ∀ a ∈ H₂ i, ∀ z ∈ H₁ i, 2 * δ i ≤ ‖a - z‖) {q d : ι → ℝ}
    (hd : ∀ i, 0 < d i) (hq : ∀ i, 0 < q i) (hqH : ∀ i, Disjoint (Metric.ball (q i : ℂ) (2 * d i)) (H₁ i ∪ H₂ i))
    {p : Fin n → ℝ} (hpH : ∀ i m, Disjoint (Metric.ball (p m : ℂ) (2 * d i)) (H₁ i ∪ H₂ i))
    (hpinj : Function.Injective p) {Tm : ℝ} (hTm : 0 < Tm) (rr : Fin n → ℝ)
    {S₁ : ι → Ω → ℝ≥0} (hS₁ : ∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0)) (hS₁0 : ∀ i ω, 0 < S₁ i ω)
    (hS₁m : ∀ i ω, (S₁ i ω : ℝ) ≤ Tm) (hK₁ : ∀ i ω, fwdHull (drive κ B ω) (S₁ i ω) ⊆ H₁ i)
    {W₂ : ℝ → ℝ} (hW₂ : Continuous W₂) (hW₂H : ∀ i, ((W₂ 0 : ℝ) : ℂ) ∈ closure (H₂ i)) (hqW : ∀ i, q i < W₂ 0)
    {S₂ : ι → ℝ} (hS₂0 : ∀ i, 0 < S₂ i) (hS₂m : ∀ i, S₂ i ≤ Tm) (hK₂ : ∀ i, fwdHull W₂ (S₂ i) ⊆ H₂ i) :
    ∫ ω, patch (fun i => (S₁ i ω : ℝ)) S₂
        (fun x y => Real.exp (normLog (sEll κ rr (drive κ B ω) W₂
          (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
          (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p) x y)) Tm Tm *
      Real.exp (sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
          (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p
          (min (maxIn (stairCols fun i => (S₁ i ω : ℝ))) Tm) 0 -
        sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
          (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p 0 0) ∂P = 1 := by
  obtain ⟨K, hK⟩ := martingale_colProd_frozen (𝓕 := 𝓕) (P := P) hκ hB hBc hB0 hH₁ hH₂ hδ hsep hd hq hqH hpH
    hpinj Tm rr
  obtain ⟨hM, -, -⟩ := hK hS₁ hS₁0 hS₁m hK₁ hW₂ hW₂H hqW hS₂0 hS₂m hK₂ hTm
  have hP : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  set N := frzDens κ B W₂ S₁ S₂ Tm rr p with hNdef
  have hN : ∀ ω x y, 0 < N ω x y := fun ω x y => Real.exp_pos _
  set s₀ : ℝ≥0 := Tm.toNNReal with hs₀
  have hs₀R : (s₀ : ℝ) = Tm := Real.coe_toNNReal _ hTm.le
  have hS₁s : ∀ i ω, S₁ i ω ≤ s₀ := fun i ω => by
    rw [← NNReal.coe_le_coe, hs₀R]; exact hS₁m i ω
  have h1 := (integral_colProd_eq_one hN hM).2 s₀ hS₁s
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [← colProd_eq_colProdT N S₂ Tm (hS₁s · ω)]
  have hpm := patch_mul_marginal (S₁ := fun i => (S₁ i ω : ℝ)) (S₂ := S₂) (fun i => (S₁ i ω).coe_nonneg)
    (N := N ω) (hN ω) s₀.coe_nonneg Tm
  have hcolP : colProd N S₁ S₂ Tm s₀ ω = ∏ c ∈ stairCols (fun i => (S₁ i ω : ℝ)),
      (N ω (min c s₀) (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) Tm) /
        N ω (min (prevIn (stairCols fun i => (S₁ i ω : ℝ)) c) s₀)
          (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) Tm)) := rfl
  rw [hcolP, ← hpm]
  have hNe : ∀ x y, N ω x y = Real.exp (sEll κ rr (drive κ B ω) W₂
      (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p
      x y) := fun x y => frzDens_eq_exp_sEll hS₂m rr p ω x y
  simp only [hNe, normFactor_exp]
  rw [hs₀R, ← Real.exp_sub]

end MeanOne

end InteractingSLE.ZhanGT4
