/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop49QExitMainMerge
import InteractingSLE.Spec.Sec5.GlueCondUnionImgAssemblyMean

/-!
# Proposition 4.9's exit on the glued space: the image word leaves at a real point left of the junction

Packet PROVE-GLUECOND11 (G6 of Proposition 4.9's direction; specification §4.2, proof of Proposition 4.9 and Remark
4.10, pp. 119–121). On the glued space of `Prop411Q.CfGlueAE` (counterflow time `s > 0`), the killed image word of
the flow line in the counterflow chart `Ψ` (PROVE-GLUECOND5) is, by PROVE-GLUECOND10's `imageWord49FiltCStatement`
and PROVE-GLUECOND7's `exists_isWordEntrance_of_filtW`, an integrated `SLE_κ(ρ′)` word before its killing time
`imgT`, with R57's junction weights. Aux. lemma 22 for its left span (`ae_leftExit_of_killed_ord`, marks only
ordered) gives: **almost surely `imgT < ∞` and the image trace converges at `imgT`, either to a point of `ℍ` or to a
real point `x₀` strictly left of the left junction `Ψ(∞⁻)`** (`ae_imgExit`).

* `exists_extendFrom_eq_lt`: for a continuous driver whose inverse map has boundary limits, a real coordinate left of
  the left image of a mark `a ≤ 0` is the coordinate of an alive real point `x₀ < a`;
* `imgVL_zero`, `imgVR_zero`, `not_threshold_img`: the image word at time `0` is below the threshold on good samples;
* `imgGeo`: the geometric hypothesis of the exit theorem, at every sample;
* **`ae_imgExit`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop49Exit

open CrossCond CrossCond.Word49 WangWu.ImgWord MartChar.RealFlow LawUnique Cond44Ref Prop411Q
open WangWu hiding ratPt exists_ratPt_dist_lt
open Sec7.Lemma71C (capClock)

/-! ### Real exit points -/

section Real

/-- **A real coordinate left of the left image of a mark `a ≤ 0` is an alive real point left of `a`**: for a
continuous driver `w` from `0` whose inverse map at `t` has boundary limits, `F̄_t(y) = x₀` real with `x₀ < a`
whenever `y < −rightImg(−w)(−a)(t) − w(t)`. -/
theorem exists_extendFrom_eq_lt {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hB : HasBdryLimits (fwdMapInv w t)) {a y : ℝ} (ha : a ≤ 0)
    (hy : y < -rightImg (fun s => -w s) (-a) t - w t) :
    ∃ x₀ : ℝ, x₀ < a ∧ extendFrom H (fwdMapInv w t) y = x₀ := by
  set w' : ℝ → ℝ := fun s => -w s with hw'def
  have hw' : Continuous w' := hw.neg
  have hM : rightImg w' 0 t < -y - w t :=
    lt_of_le_of_lt (rightImg_mono_index hw' ht (neg_nonneg.2 ha)) (by linarith)
  obtain ⟨x', -, hx'a, hx'g⟩ := Restart.RetAux79.exists_alive_gImg_eq hw' ht hM
  have hsol := WangWu.isForwardSol_neg_of_alive hw hx'a
  have hHb : -((x' : ℝ) : ℂ) ∈ Hbar := by
    show 0 ≤ (-((x' : ℝ) : ℂ)).im
    simp
  have hE := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hw hw0 ht hHb hsol
  have hc : cflow w' x' t = -y := by
    have h1 : gImg w' x' t = w' t + cflow w' x' t := rfl
    rw [hx'g] at h1
    simp only [hw'def] at h1
    linarith
  have hyC : -((cflow w' x' t : ℝ) : ℂ) = (y : ℂ) := by rw [hc]; push_cast; ring
  rw [hyC] at hE
  refine ⟨-x', ?_, by rw [hE]; push_cast; ring⟩
  have h1 : rightImg w' (-a) t ≤ gImg w' x' t := by rw [hx'g]; linarith
  by_cases hxa : -a = x'
  · exfalso
    rw [hxa, rightImg_eq_gImg hw' ht hx'a, hx'g] at hy
    linarith
  · have := (Restart.RetAux79.rightImg_le_gImg_iff hw' ht hx'a hxa).1 h1
    linarith

variable {γ : ℝ → ℂ} {P : Set ℝ}

/-- **The killed version**: before the terminal capacity, a real coordinate left of the left image of a mark
`a ≤ 0` under the killed driver is an alive real point left of `a`. -/
theorem exists_extendFrom_eq_lt_of_killed (hγ : IsKilledArc γ P) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < kLife γ P) {a y : ℝ} (ha : a ≤ 0)
    (hy : y < -kImg (fun r => -kPath γ P r) (-a) t - kW γ P t) :
    ∃ x₀ : ℝ, x₀ < a ∧ extendFrom H (fwdMapInv (kPath γ P) t) y = x₀ := by
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, -, -⟩ := hγ.exists_kPath_trace ht
  have hEq' : EqOn (fun r => -kPath γ P r) (fun r => -w r) (Icc 0 (capClock γ S)) := fun r hr => by
    simp only [hEq hr]
  rw [kImg_eq hw.neg hEq' htS.le, ← kPath_coe, hEq ⟨t.coe_nonneg, htS.le⟩] at hy
  rw [fwdMapInv_eq_of_eqOn (W := kPath γ P) (W' := w) t.coe_nonneg htS fun r hr => hEq hr]
  exact exists_extendFrom_eq_lt hw hw0 t.coe_nonneg (hηL.hasBdryLimits hw hw0 t.coe_nonneg) ha hy

/-- The killed left image of a mark `x ≤ 0` at time `0` is the mark. -/
theorem kVLr_zero_of_killed (hγ : IsKilledArc γ P) {n : ℕ} (xL : Fin n → ℝ) (hxL : ∀ i, xL i ≤ 0) (i : Fin n) :
    kVLr γ P xL i 0 = xL i := by
  obtain ⟨S, -, -, hS, w, hw, hw0, hEq, -⟩ := hγ.exists_kPath_trace hγ.zero_lt_kLife
  have hEq' : EqOn (fun r => -kPath γ P r) (fun r => -w r) (Icc 0 (capClock γ S)) := fun r hr => by
    simp only [hEq hr]
  simp only [kVLr]
  rw [kImg_eq hw.neg hEq' hS.le, NNReal.coe_zero, rightImg_zero hw.neg (by simp [hw0]) (neg_nonneg.2 (hxL i))]
  ring

/-- The killed right image of a mark `x ≥ 0` at time `0` is the mark. -/
theorem kVRr_zero_of_killed (hγ : IsKilledArc γ P) {n : ℕ} (xR : Fin n → ℝ) (hxR : ∀ j, 0 ≤ xR j) (j : Fin n) :
    kVRr γ P xR j 0 = xR j := by
  obtain ⟨S, -, -, hS, w, hw, hw0, hEq, -⟩ := hγ.exists_kPath_trace hγ.zero_lt_kLife
  simp only [kVRr]
  rw [kImg_eq hw hEq hS.le, NNReal.coe_zero, rightImg_zero hw hw0 (hxR j)]

end Real

/-! ### The image word at time `0` and its geometry -/

section Img

variable {Ω : Type*} {nL nR : ℕ} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}

theorem imgW_zero (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (p : Ω × HistorySpace 0 0) : imgW s ζ W E 0 p = 0 :=
  (isKilledArc_gCurve hEg p).kW_zero

theorem imgVL_zero {xL : Fin nL → ℝ} (hxL : ∀ i, xL i ≤ 0) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    (p : Ω × HistorySpace 0 0) (i : Fin (nL + 1)) : imgVL xL s ζ W E i 0 p = gXL xL s E p i := by
  have hγ := isKilledArc_gCurve hEg p
  simp only [Word49.imgVL]
  rw [kVL_of_lt _ _ (by simpa using hγ.zero_lt_kLife)]
  exact kVLr_zero_of_killed hγ _ (gXL_nonpos hxL hEg p) i

theorem imgVR_zero {xR : Fin nR → ℝ} (hxR : ∀ j, 0 ≤ xR j) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    (p : Ω × HistorySpace 0 0) (j : Fin (nR + 1)) : imgVR xR s ζ W E j 0 p = gXR xR s E p j := by
  have hγ := isKilledArc_gCurve hEg p
  simp only [Word49.imgVR]
  rw [kVR_of_lt _ _ (by simpa using hγ.zero_lt_kLife)]
  exact kVRr_zero_of_killed hγ _ (gXR_nonneg hxR hEg p) j

theorem psiL_ne_zero {w : ℝ → ℝ} {t : ℝ} (hw : Continuous w) (ht : 0 ≤ t) (hj : 0 < rightImg w 0 t - w t)
    {x : ℝ} (hx : x ≤ 0) (hx0 : x ≠ 0) : psiL w t x ≠ 0 := by
  have hy : 0 ≤ -1 / x := div_nonneg_of_nonpos (by norm_num) hx
  have hc := rightImg_sub_ge hw ht hy
  simp only [psiL, hx0, ↓reduceIte]
  exact div_ne_zero (by norm_num) (hj.trans_le hc).ne'

theorem psiR_ne_zero {w : ℝ → ℝ} {t : ℝ} (hw : Continuous w) (ht : 0 ≤ t)
    (hj : -rightImg (fun r => -w r) 0 t - w t < 0) {x : ℝ} (hx : 0 ≤ x) (hx0 : x ≠ 0) : psiR w t x ≠ 0 := by
  have hy : 0 ≤ 1 / x := div_nonneg zero_le_one hx
  have hc := neg_rightImg_neg_sub_le hw ht hy
  simp only [psiR, hx0, ↓reduceIte]
  exact div_ne_zero (by norm_num) (hc.trans_lt hj).ne

theorem sum_filter_snoc_eq_zero {n : ℕ} (f g : Fin n → ℝ) (c d : ℝ) (hc : c ≠ 0) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (Fin.snoc f c : Fin (n + 1) → ℝ) i = 0),
        (Fin.snoc g d : Fin (n + 1) → ℝ) i =
      ∑ i ∈ Finset.univ.filter (fun i => f i = 0), g i := by
  rw [Finset.sum_filter, Fin.sum_univ_castSucc, Finset.sum_filter]
  simp [Fin.snoc_castSucc, Fin.snoc_last, hc]

/-- A sum over the marks at `0` of an ordered (4.4) side exceeds `−2`. -/
theorem neg_two_lt_sum_filter_zero {n : ℕ} {x ρ : Fin n → ℝ} {c : ℝ} (hc : -2 < c)
    (hdown : ∀ i i' : Fin n, i' ≤ i → x i = 0 → x i' = 0)
    (hpre : ∀ m : ℕ, 1 ≤ m → m ≤ n → c ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), ρ i) :
    -2 < ∑ i ∈ Finset.univ.filter (fun i => x i = 0), ρ i := by
  rw [Sec4.filter_eq_filter_val_lt_card (p := fun i => x i = 0) hdown]
  by_cases h0 : (Finset.univ.filter fun i => x i = 0).card = 0
  · rw [h0]
    have : (Finset.univ.filter fun i : Fin n => i.val < 0) = ∅ := by
      ext i; simp
    rw [this, Finset.sum_empty]
    norm_num
  · refine lt_of_lt_of_le hc (hpre _ (Nat.one_le_iff_ne_zero.2 h0) ?_)
    exact (Finset.card_filter_le _ _).trans (by simp)

/-- **The image word is below the threshold at time `0`** on good samples (an ordered (4.4) word, `0 < κ`): the
marks at `0` are the images of the flow word's seed marks, a prefix of each side, whose weights sum to more than
`−2`; the junctions are not at `0`. -/
theorem not_threshold_img {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E) :
    ¬ ForceWord.ThresholdCondition (jwL cL6 κ ρL) (jwR cR6 κ ρR) (imgW s ζ W E 0 p)
      (fun i => imgVL xL s ζ W E i 0 p) (fun j => imgVR xR s ζ W E j 0 p) := by
  obtain ⟨-, -, hjL, hjR, -⟩ := hEg p hp
  have hw := continuous_cfDrv0 s p.2
  simp only [imgW_zero hEg, imgVL_zero hF.2.1 hEg, imgVR_zero hF.2.2.2 hEg, gXL_of_mem hp, gXR_of_mem hp,
    ForceWord.ThresholdCondition, jwL, jwR, not_or, not_le]
  have hjL0 : junL (cfDrv0 s p.2) s ≠ 0 := div_ne_zero (by norm_num) hjL.ne'
  have hjR0 : junR (cfDrv0 s p.2) s ≠ 0 := div_ne_zero (by norm_num) hjR.ne
  rw [sum_filter_snoc_eq_zero _ _ _ _ hjL0, sum_filter_snoc_eq_zero _ _ _ _ hjR0]
  have eL : (Finset.univ.filter fun i => psiL (cfDrv0 s p.2) s (xL i) = 0) =
      Finset.univ.filter fun i => xL i = 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => psiL_ne_zero hw s.coe_nonneg hjL (hF.2.1 i) h0 h, fun h => ?_⟩
    simp [psiL, h]
  have eR : (Finset.univ.filter fun j => psiR (cfDrv0 s p.2) s (xR j) = 0) =
      Finset.univ.filter fun j => xR j = 0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => psiR_ne_zero hw s.coe_nonneg hjR (hF.2.2.2 j) h0 h, fun h => ?_⟩
    simp [psiR, h]
  rw [eL, eR]
  refine ⟨neg_two_lt_sum_filter_zero (c := κ / 2 - 2) (by linarith) (fun i i' hii h => ?_) h44.1,
    neg_two_lt_sum_filter_zero (c := 0) (by norm_num) (fun j j' hjj h => ?_) h44.2⟩
  · exact le_antisymm (hF.2.1 i') (h ▸ hF.1 hii)
  · exact le_antisymm (h ▸ hF.2.2.1 hjj) (hF.2.2.2 j')

/-- **The geometric hypothesis of the exit theorem for the image word**, at every sample: before the killing time,
a real coordinate left of the image of the last left mark is the coordinate of an alive real point left of that
mark (in particular `F̄_t` sends it off `ℍ`). -/
theorem imgGeo {xL : Fin nL → ℝ} (hxL : ∀ i, xL i ≤ 0) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    (p : Ω × HistorySpace 0 0) {t : ℝ≥0} (htT : (t : WithTop ℝ≥0) < imgT s ζ W E p) {y : ℝ}
    (hy : y < imgVL xL s ζ W E (Fin.last nL) t p - imgW s ζ W E t p) :
    ∃ x₀ : ℝ, x₀ < gXL xL s E p (Fin.last nL) ∧
      extendFrom H (fwdMapInv (fun r : ℝ => imgW s ζ W E r.toNNReal p) t) y = x₀ := by
  have hγ := isKilledArc_gCurve hEg p
  simp only [Word49.imgVL, Word49.imgW] at hy
  rw [kVL_of_lt _ _ htT] at hy
  exact exists_extendFrom_eq_lt_of_killed hγ htT (gXL_nonpos hxL hEg p _) hy

end Img

/-! ### The exit of the image word on the glued space -/

section Exit

/-- **Proposition 4.9's image exit (G6, the probabilistic part).** In the setting of `Prop411Q.CfGlueAE`, for every
counterflow time `s > 0`, almost surely on the glued space the killing time `imgT` of the image word is finite and the
image trace converges at `imgT`, either to a point of `ℍ` or to a real point `x₀` strictly left of the image's last
left mark, the left junction `Ψ(∞⁻)` (Aux. lemma 22 for the image word's left span, Remark 4.10). -/
theorem ae_imgExit {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W) p : ℝ≥0∞) ≠ ⊤ ∧
      ∃ z : ℂ, Tendsto (imgTr s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) p)
        (𝓝[<] ENNReal.toNNReal (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) p)) (𝓝 z) ∧
        (z ∈ H ∨ ∃ x₀ : ℝ, x₀ < gXL xL s (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) p (Fin.last nL) ∧ z = x₀) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
      hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  obtain ⟨-, hK, hWa, hVLa, hVRa, -, -, -, -, hζq⟩ := filtClauses (μ := μ) (xL := xL) (xR := xR) hWad hF hae
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, Bi, hB, hBc, hEnt⟩ :=
    exists_isWordEntrance_of_filtW imageWord49FiltCStatement hκ hκ4 hF h44 hC hcf hlaw k hk hs
  set 𝓖 := imgFilt μ xL xR s ζ W E with h𝓖
  have hTq' : ∀ q : ℝ≥0, MeasurableSet[WholeField.prodFiltration 𝓖 𝓦 q]
      {p : (Ω × HistorySpace 0 0) × Ω₀ | (q : ℝ≥0∞) < (imgT s ζ W E p.1 : ℝ≥0∞)} := fun q =>
    WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hζq q, rfl⟩
  have hthr : ∀ᵐ p ∂(μ.prod P₀), ¬ ForceWord.ThresholdCondition (jwL cL6 κ ρL) (jwR cR6 κ ρR)
      (imgW s ζ W E 0 p.1) (fun i => imgVL xL s ζ W E i 0 p.1) (fun j => imgVR xR s ζ W E j 0 p.1) := by
    have h1 : ∀ᵐ p ∂μ, ¬ ForceWord.ThresholdCondition (jwL cL6 κ ρL) (jwR cR6 κ ρR)
        (imgW s ζ W E 0 p) (fun i => imgVL xL s ζ W E i 0 p) (fun j => imgVR xR s ζ W E j 0 p) := by
      filter_upwards [ae_mem_glueGood hae] with p hp
      exact not_threshold_img hκ hF h44 hEg hp
    exact Measure.quasiMeasurePreserving_fst.ae h1
  have hgeo : ∀ (p : (Ω × HistorySpace 0 0) × Ω₀) (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < (imgT s ζ W E p.1 : ℝ≥0∞) →
      ∀ y : ℝ, y < imgVL xL s ζ W E (Fin.last nL) t p.1 - imgW s ζ W E t p.1 →
        extendFrom H (fwdMapInv (fun r : ℝ => imgW s ζ W E r.toNNReal p.1) t) y ∉ H := by
    intro p t _ htT y hy
    obtain ⟨x₀, -, hx₀⟩ := imgGeo hF.2.1 hEg p.1 htT hy
    rw [hx₀]
    intro hH
    have h0 : (0 : ℝ) < ((x₀ : ℝ) : ℂ).im := hH
    simp at h0
  have hX := ae_leftExit_of_killed_ord (P := μ.prod P₀) (𝓘 := WholeField.prodFiltration 𝓖 𝓦) hκ hκ4.le
    (hasStripPrefixSums_jw hκ4 h44) (abs_charge_jw_lt hκ hκ4 ρL ρR) hB hBc
    (W := fun t p => imgW s ζ W E t p.1) (VL := fun i t p => imgVL xL s ζ W E i t p.1)
    (VR := fun j t p => imgVR xR s ζ W E j t p.1)
    (Sec7.PhaseSelFull.stronglyAdapted_fst hWa) (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
    (fun j => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa j)) (T := fun p => (imgT s ζ W E p.1 : ℝ≥0∞)) hTq'
    (fun p => (isKilledArc_gCurve hEg p.1).zero_lt_kLife) hEnt
    (fun p t ht htT i => hK.sepL p.1 t ht htT i) (fun p t ht htT j => hK.sepR p.1 t ht htT j) hthr hgeo
  have h2 := Measure.ae_ae_of_ae_prod hX
  filter_upwards [h2] with p hp
  obtain ⟨_, hpω⟩ := hp.exists
  obtain ⟨hTne, z, hz, hzalt⟩ := hpω (imgTr s ζ W E p) (fun r hr => isGeneratingTraceIcc_imgTr hEg p hr)
    (fun t ht0 ht => imgTr_mem_H hEg p ht0 ht)
  refine ⟨hTne, z, hz, ?_⟩
  rcases hzalt with hzH | ⟨q, y, -, hqT, hy, rfl⟩
  · exact Or.inl hzH
  · obtain ⟨x₀, hx₀, hx₀e⟩ := imgGeo hF.2.1 hEg p hqT hy
    exact Or.inr ⟨x₀, hx₀, hx₀e⟩

end Exit

end InteractingSLE.Sec5.Prop49Exit
