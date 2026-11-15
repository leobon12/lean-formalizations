/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.WordsStrip
import InteractingSLE.Spec.Zhan.StripTimeGap
import InteractingSLE.Spec.Zhan.StripNoncollision
import InteractingSLE.Spec.Sec7.CounterflowProbDilation

/-!
# Reduction of the left energy to strip evolutions (R36)

Packet PROVE-ZHAN-B4. For a word whose marks are strictly ordered on both sides, dilate so that the outermost left
mark sits at `−1`; the evolution is then the R36 strip evolution (`Strip.IsStripSLEEvolution`) whose end mark is the
outermost left mark, with lower left marks `pᴸᵢ = log(1 + xᴸᵢ)` and lower right marks `pᴿⱼ = log(1 + xᴿⱼ)`. The left
side energy is invariant under dilation (`HasBoundedSideEnergy.of_dilate`) and equals the strip-time energy of the left
coth error (`integral_sq_sideErr_eq`). Hence `StrictLeftEnergyStatement` follows from the strip statement
`StripLeftEnergyStatement` (`strictLeftEnergyStatement_of_strip`): finite strip-time energy of the coth errors of the
lower left marks — the linear escape of lower strip gaps (Astra (3.24)) with exponentially decaying errors.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Zhan

open Strip Sec7.Dilation

variable {n : ℕ}

/-! ### Dilation of side energies -/

theorem sideErr_smul (ρ : Fin n → ℝ) {s : ℝ} (_hs : s ≠ 0) (w : ℝ) (v : Fin n → ℝ) :
    sideErr ρ (s⁻¹ * w) (fun i => s⁻¹ * v i) = s * sideErr ρ w v := by
  simp only [sideErr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_sub, ← mul_sub, mul_inv, mul_inv, inv_inv, ← mul_sub]
  ring

/-- **Side energies are invariant under dilation.** -/
theorem HasBoundedSideEnergy.of_dilate {c : ℝ≥0} (hc : c ≠ 0) {ρ : Fin n → ℝ} {w : ℝ≥0 → ℝ}
    {v : Fin n → ℝ≥0 → ℝ} (h : HasBoundedSideEnergy ρ (dilPath c w) (fun i => dilPath c (v i))) :
    HasBoundedSideEnergy ρ w v := by
  obtain ⟨m, hm⟩ := h
  have hc0 : (0 : ℝ) < c := by positivity
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0.le
  set g : ℝ → ℝ := fun u => sideErrAt ρ w v u.toNNReal ^ 2 with hg
  have hdil : ∀ s : ℝ, sideErrAt ρ (dilPath c w) (fun i => dilPath c (v i)) s.toNNReal ^ 2 =
      c * g (c * s) := fun s => by
    simp only [sideErrAt, hg]
    rw [dilPath_toNNReal]
    simp only [dilPath_toNNReal]
    rw [sideErr_smul ρ (sqrt_ne_zero_of_ne hc), mul_pow, hsq]
  refine ⟨m, fun T => ?_⟩
  set T' : ℝ≥0 := T / c with hT'
  have hT'c : (c : ℝ) * T' = T := by rw [hT', NNReal.coe_div]; field_simp
  obtain ⟨hint, hle⟩ := hm T'
  have hint' : IntervalIntegrable (fun s => g (c * s)) volume 0 T' :=
    (hint.const_mul (c : ℝ)⁻¹).congr fun s _ => by
      simp only [hdil]; field_simp
  have hgint : IntervalIntegrable g volume 0 T := by
    refine (IntervalIntegrable.comp_mul_left_iff (f := g) (c := (c : ℝ)) (a := 0) (b := T) hc0.ne').1 ?_
    rw [zero_div, show (T : ℝ) / c = T' by rw [hT', NNReal.coe_div]]
    exact hint'
  refine ⟨hgint, ?_⟩
  have e : ∫ s in (0 : ℝ)..T', sideErrAt ρ (dilPath c w) (fun i => dilPath c (v i)) s.toNNReal ^ 2 =
      ∫ s in (0 : ℝ)..T, g s := by
    simp only [hdil, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left g hc0.ne',
      mul_zero, hT'c, smul_eq_mul]
    field_simp
  rw [← e]
  exact hle

/-! ### The R36 identification -/

theorem wordXL_log {x : Fin (n + 1) → ℝ} (hlast : x (Fin.last n) = -1) (hx : ∀ i : Fin n, -1 < x i.castSucc) :
    wordXL (fun i => Real.log (1 + x i.castSucc)) = x := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [wordXL_last, hlast]
  | cast i =>
    rw [wordXL_castSucc, Real.exp_log (by linarith [hx i])]
    ring

theorem wordXR_log {nR : ℕ} {x : Fin nR → ℝ} (hx : ∀ j, -1 < x j) :
    wordXR (fun j => Real.log (1 + x j)) = x := by
  funext j
  rw [wordXR, Real.exp_log (by linarith [hx j])]
  ring

theorem wordRhoL_castSucc_last (ρ : Fin (n + 1) → ℝ) :
    wordRhoL (fun i => ρ i.castSucc) (ρ (Fin.last n)) = ρ := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [wordRhoL_last]
  | cast i => rw [wordRhoL_castSucc]

/-- **Strip prefix sums from admissibility** of a strictly ordered word. -/
theorem hasStripPrefixSums_of_admissible {κ : ℝ} {nR : ℕ} {xL ρL : Fin (n + 1) → ℝ} {xR ρR : Fin nR → ℝ}
    (hsL : StrictAnti xL) (hsR : StrictMono xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) :
    HasStripPrefixSums κ (fun i => ρL i.castSucc) ρR := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · set x := (xL j.castSucc + xL j.succ) / 2 with hx
    have h1 : xL j.succ < xL j.castSucc := hsL (Fin.castSucc_lt_succ (i := j))
    have hfilt : (Finset.univ.filter fun i : Fin (n + 1) => x < xL i) =
        (Finset.Iic j).map Fin.castSuccEmb := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Iic,
        Fin.castSuccEmb_apply]
      constructor
      · intro hi
        have hle : i ≤ j.castSucc := by
          by_contra hlt
          push Not at hlt
          have : j.succ ≤ i := by rw [Fin.le_def]; rw [Fin.lt_def] at hlt; simp at hlt ⊢; omega
          have := hsL.antitone this
          linarith
        refine ⟨⟨i, by have := Fin.le_def.1 hle; simp at this; omega⟩, ?_, by ext; simp⟩
        rw [Fin.le_def] at hle ⊢; simpa using hle
      · rintro ⟨k, hk, rfl⟩
        have : xL j.castSucc ≤ xL k.castSucc := hsL.antitone (Fin.castSucc_le_castSucc_iff.2 hk)
        linarith
    have h := hadm.1 x (by linarith [hxL j.castSucc, hxL j.succ]) ⟨j.castSucc, by linarith⟩
    rwa [hfilt, Finset.sum_map] at h
  · have hfilt : (Finset.univ.filter fun i => xR i ≤ xR j) = Finset.Iic j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
      exact hsR.le_iff_le
    have h := hadm.2 (xR j) (hxR j).le ⟨j, le_rfl⟩
    rwa [hfilt] at h

/-! ### The strip statement and the reduction -/

/-- **Finite strip-time energy of the lower left coth errors** (Astra §3, linear escape of lower strip gaps (3.24),
L1520–L1556, with `q₋ = chargeMinus ≥ κ/2 − 2 > κ/2 − 4` and lower left total `≥ κ/2 − 2 ≥ −2`; then the coth errors
decay exponentially, L1567–L1571): for every R36 strip evolution of a separated strip word with the prefix sums
of (3.3), almost surely the strip-time integrals of the squared left coth error are bounded. -/
def StripLeftEnergyStatement (κ : ℝ) : Prop :=
  ∀ {n nR : ℕ} (pL : Fin n → ℝ) (pR : Fin nR → ℝ) (ρL : Fin n → ℝ) (ρR : Fin nR → ℝ) (τm : ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (n + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsSeparatedStripWord pL pR → HasStripPrefixSums κ ρL ρR → κ / 2 - 2 ≤ chargeMinus ρL τm →
      IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ m : ℝ, ∀ t : ℝ, 0 ≤ t →
          ∫ u in (0 : ℝ)..t, (leftStripErr ρL (extPath (W · ω)) (extPath (VL (Fin.last n) · ω))
            (fun i => extPath (VL i.castSucc · ω)) u) ^ 2 ≤ m

theorem hasBoundedSideEnergy_zero {ρ : Fin 0 → ℝ} {w : ℝ≥0 → ℝ} {v : Fin 0 → ℝ≥0 → ℝ} :
    HasBoundedSideEnergy ρ w v :=
  ⟨0, fun T => by simp [sideErrAt, sideErr]⟩

/-- **Reduction of `StrictLeftEnergyStatement` to strip evolutions** (dilation, R36 identification, change of
variables). -/
theorem strictLeftEnergyStatement_of_strip {κ : ℝ} (hκ : 0 < κ) (h : StripLeftEnergyStatement.{u} κ) :
    StrictLeftEnergyStatement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hsL hsR hF hadm hxL hxR hE
  rcases nL with _ | n
  · exact ae_of_all _ fun ω => hasBoundedSideEnergy_zero
  set l : Fin (n + 1) := Fin.last n with hldef
  have hl0 : xL l < 0 := hxL l
  set c : ℝ≥0 := ⟨xL l ^ 2, sq_nonneg _⟩ with hcdef
  have hcR : (c : ℝ) = xL l ^ 2 := rfl
  have hc : c ≠ 0 := by
    intro h0
    have : (c : ℝ) = 0 := by rw [h0]; rfl
    rw [hcR] at this
    nlinarith
  have hsc : Real.sqrt c = -xL l := by rw [hcR, Real.sqrt_sq_eq_abs, abs_of_neg hl0]
  have hspos : 0 < (Real.sqrt c)⁻¹ := by rw [hsc]; exact inv_pos.2 (by linarith)
  set x' : Fin (n + 1) → ℝ := fun i => (Real.sqrt c)⁻¹ * xL i with hx'def
  set y' : Fin nR → ℝ := fun j => (Real.sqrt c)⁻¹ * xR j with hy'def
  have hx'last : x' l = -1 := by
    simp only [x', hsc]
    field_simp [hl0.ne]
  have hx'gt : ∀ i : Fin n, -1 < x' i.castSucc := fun i => by
    have h1 : xL l < xL i.castSucc := hsL (Fin.castSucc_lt_last i)
    rw [← hx'last]
    exact mul_lt_mul_of_pos_left h1 hspos
  have hx'neg : ∀ i, x' i < 0 := fun i => mul_neg_of_pos_of_neg hspos (hxL i)
  have hy'pos : ∀ j, 0 < y' j := fun j => mul_pos hspos (hxR j)
  set pL : Fin n → ℝ := fun i => Real.log (1 + x' i.castSucc) with hpLdef
  set pR : Fin nR → ℝ := fun j => Real.log (1 + y' j) with hpRdef
  have hXL : wordXL pL = x' := wordXL_log hx'last hx'gt
  have hXR : wordXR pR = y' := wordXR_log fun j => by linarith [hy'pos j]
  have hEd := InteractingSLE.IsIntegratedSLEEvolution.dilate hc hE
  have hstrip : IsStripSLEEvolution κ pL pR (fun i => ρL i.castSucc) ρR (ρL l) P (dilFiltration c 𝓕)
      (dilProc c W) (fun i => dilProc c (VL i)) (fun i => dilProc c (VR i)) (dilProc c B)
      (fun ω => ζ ω / c) := by
    unfold IsStripSLEEvolution
    rw [hXL, hXR, wordRhoL_castSucc_last]
    exact hEd
  have hsep : IsSeparatedStripWord pL pR := by
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun j => ?_⟩
    · have h1 : x' j.castSucc < x' i.castSucc :=
        mul_lt_mul_of_pos_left (hsL (Fin.castSucc_lt_castSucc_iff.2 hij)) hspos
      exact Real.log_lt_log (by linarith [hx'gt j]) (by linarith)
    · exact Real.log_neg (by linarith [hx'gt i]) (by linarith [hx'neg i.castSucc])
    · have h1 : y' i < y' j := mul_lt_mul_of_pos_left (hsR hij) hspos
      exact Real.log_lt_log (by linarith [hy'pos i]) (by linarith)
    · exact Real.log_pos (by linarith [hy'pos j])
  have hpre := hasStripPrefixSums_of_admissible hsL hsR hxL hxR hadm
  have hq : κ / 2 - 2 ≤ chargeMinus (fun i => ρL i.castSucc) (ρL l) := by
    rw [chargeMinus, ← Fin.sum_univ_castSucc]
    exact le_sum_left hF hadm hxL l
  have H := h pL pR _ ρR (ρL l) P _ _ _ _ _ _ hsep hpre hq hstrip
  have h6 := Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE
  filter_upwards [H, h6, hE.2.2.2.2] with ω hH h6ω hp
  obtain ⟨m, hm⟩ := hH
  obtain ⟨hζ, hnc⟩ := h6ω
  refine HasBoundedSideEnergy.of_dilate hc ⟨m, fun T => ?_⟩
  have hpd : IsIntegratedSLEPath κ (wordXL pL) (wordXR pR) (wordRhoL (fun i => ρL i.castSucc) (ρL l)) ρR
      (dilPath c (fun t => W t ω)) (fun i => dilPath c (fun t => VL i t ω))
      (fun j => dilPath c (fun t => VR j t ω)) (dilPath c (fun t => B t ω)) (ζ ω / c) := by
    rw [hXL, hXR, wordRhoL_castSucc_last]
    exact hp.dilate hc
  have hζd : ζ ω / c = ⊤ := by rw [hζ]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top
  have hlt : ∀ (r : ℝ≥0) (i : Fin (n + 1)),
      dilPath c (fun t => VL i t ω) r < dilPath c (fun t => W t ω) r := by
    intro r i
    simp only [dilPath]
    refine mul_lt_mul_of_pos_left ?_ hspos
    rcases eq_zero_or_pos (c * r) with h0 | hpos
    · have h1 : VL i 0 ω = xL i := hp.2.1 i
      have h2 : W 0 ω = 0 := hp.1
      rw [h0, h1, h2]
      exact hxL i
    · exact (hnc _ hpos).1 i
  have hlife : ∀ r : ℝ≥0, IsStripLife (dilPath c (fun t => W t ω)) (dilPath c (fun t => VL l t ω)) (ζ ω / c) r :=
    fun r => ⟨by rw [hζd]; exact ENNReal.coe_lt_top, fun r' _ => hlt r' l⟩
  have hsm := isSepMark_of_isIntegratedSLEPath hpd (hlife T)
  have hin : ∀ (r : ℝ≥0) (i : Fin n),
      dilPath c (fun t => VL l t ω) r < dilPath c (fun t => VL i.castSucc t ω) r := fun r i =>
    vL_last_lt_vL_castSucc hpd (hlife r) i
  have hcont : ∀ i, ContinuousOn (extPath (dilPath c (fun t => VL i t ω))) (Icc 0 (T : ℝ)) := fun i =>
    continuousOn_extPath (hpd.2.2.2.2.1 i) (hlife T).1
  have heq := integral_sq_sideErr_eq hsm (ρ := ρL) (vL := fun i => extPath (dilPath c (fun t => VL i t ω)))
    rfl (fun i => hcont _) (fun r _ i => ⟨hin _ i, hlt _ _⟩)
  have hcW : ContinuousOn (extPath (dilPath c (fun t => W t ω))) (Icc 0 (T : ℝ)) :=
    continuousOn_extPath hpd.2.2.2.1 (hlife T).1
  refine ⟨?_, ?_⟩
  · have hfun : (fun s : ℝ => sideErrAt ρL (dilPath c (fun t => W t ω))
        (fun i => dilPath c (fun t => VL i t ω)) s.toNNReal ^ 2) = fun s : ℝ =>
        (∑ i, ρL i * ((extPath (dilPath c (fun t => W t ω)) s -
          extPath (dilPath c (fun t => VL (lastOf i) t ω)) s)⁻¹ -
          (extPath (dilPath c (fun t => W t ω)) s - extPath (dilPath c (fun t => VL i t ω)) s)⁻¹)) ^ 2 := rfl
    rw [hfun]
    refine ContinuousOn.intervalIntegrable_of_Icc (NNReal.coe_nonneg T) ?_
    refine ContinuousOn.pow ?_ 2
    refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
    refine ((hcW.sub (hcont _)).inv₀ fun r _ => ?_).sub ((hcW.sub (hcont i)).inv₀ fun r _ => ?_)
    · exact (sub_pos.2 (hlt _ _)).ne'
    · exact (sub_pos.2 (hlt _ _)).ne'
  · exact (le_of_eq heq).trans (hm _ (hsm.stripClock_nonneg ⟨NNReal.coe_nonneg T, le_rfl⟩))

/-! ### Consequences -/

/-- `SeparatedTransienceStatement κ` (`0 < κ ≤ 4`) from the strip-time left energy. -/
theorem separatedTransienceStatement_of_stripLeftEnergy {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (h : StripLeftEnergyStatement.{u} κ) : SeparatedTransienceStatement.{u} κ :=
  separatedTransienceStatement_of_strictLeftEnergy hκ hκ4 (strictLeftEnergyStatement_of_strip hκ h)

/-- **Aux. lemma 7** (`0 < κ ≤ 4`) from the strip-time left energy. -/
theorem aux7Statement_of_stripLeftEnergy {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (h : StripLeftEnergyStatement.{u} κ) : Sec4.Aux7Statement.{u} κ :=
  aux7Statement_of_strictLeftEnergy hκ hκ4 (strictLeftEnergyStatement_of_strip hκ h)

/-- **Wang–Wu's input 8.3** from the strip-time left energy at `κ = 4`. -/
theorem zhanNonboundaryTransience_of_stripLeftEnergy (h : StripLeftEnergyStatement.{u} 4) :
    WangWu.ZhanNonboundaryTransience.{u} :=
  zhanNonboundaryTransience_of_strictLeftEnergy (strictLeftEnergyStatement_of_strip (by norm_num) h)

end InteractingSLE.Zhan
