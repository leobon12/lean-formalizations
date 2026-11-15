/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb7BandMart
import InteractingSLE.WangWu.CouplingFrozenTwo

/-!
# Aux. lemma 102: finitely many band switches

Packet PROVE-SEC7-C7. Specification p. 354 (Aux. lemma 106): on a finite angular clock the alternating bands
`U ≤ 2/3`, `U ≥ 1/3` have only finitely many switches.

The band process `N = h(U) − ∫ itoGen h(U)` (`ContinuityProb7BandMart`) is, before the lifetime, independent of the
localization (`bandN_eq_Nhat`). Doob's maximal inequality for the martingale `N_t − N_{t∧s}` and the `L²` identity give
`ε P(sup_{[s, n]} |N − N_s| ≥ ε) ≤ δ/2 + κ K'² E[∫_{s∧σ_n}^{σ_n} D^{-2}]/(2δ)` (`measureReal_osc_le`). The localizing
times increase with `n` (`angLoc_mono`), so the tail clocks `∫_{s∧σ_n}^{σ_n} D^{-2}` are dominated by the total clock,
which is integrable, and tend to `0` as `s → ∞`; hence `N` is almost surely Cauchy at infinity on `{ζ = ∞}`. The drift
part is absolutely integrable on `[0, ∞)` (the finite clock and (P4)), so `h(U_t)` converges, and `U` eventually stays
in one band.

## Main results

* `angLoc_mono`, `Nhat`, `bandN_eq_Nhat`, `measureReal_osc_le`;
* **`ae_eventually_band`**, **`aux102BandStatement`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Clock

open Zhan

variable {nL nR : ℕ}

section Conv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

/-! ### The localizing times increase -/

theorem hitBelow_mono_fun {f g : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {ε : ℝ} (h : ∀ s, f s ≤ g s) :
    Coupling.hitBelow f ζ' ε ≤ Coupling.hitBelow g ζ' ε := by
  by_cases hg : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ' ∧ g s < ε}.Nonempty
  · have hf : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ' ∧ f s < ε}.Nonempty := by
      obtain ⟨s, hs⟩ := hg
      exact ⟨s, hs.1, (h s).trans_lt hs.2⟩
    rw [Coupling.hitBelow_of_nonempty hf, Coupling.hitBelow_of_nonempty hg]
    exact WithTop.coe_le_coe.2 (csInf_le_csInf (OrderBot.bddBelow _) hg fun s hs =>
      ⟨hs.1, (h s).trans_lt hs.2⟩)
  · rw [Coupling.hitBelow_of_not_nonempty hg]; exact le_top

theorem hitBox_mono {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    hitBox G W VL VR ζ m ω ≤ hitBox G W VL VR ζ n ω := by
  by_cases hω : ω ∈ G
  · simp only [hitBox, hω, ↓reduceIte]
    refine hitBelow_mono_fun fun s => ?_
    simp only [boxLev]
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  · simp [hitBox, hω]

/-- **The localizing times increase with `n`.** -/
theorem angLoc_mono (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
    (hTm : ∀ ω, Monotone (T · ω)) (ω : Ω) : Monotone fun n => angLoc G T W VL VR B ζ n ω := by
  intro m n hmn
  have h := coe_angLoc (G := G) (T := T) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) m ω
  have h' := coe_angLoc (G := G) (T := T) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n ω
  show angLoc G T W VL VR B ζ m ω ≤ angLoc G T W VL VR B ζ n ω
  rw [← WithTop.coe_le_coe, h, h']
  refine min_le_min ?_ (min_le_min (hitBox_mono hmn ω)
    (MathFin.exitTime_mono (continuous_brownG_ang hgood) hmn ω))
  exact WithTop.coe_le_coe.2 (min_le_min (by exact_mod_cast hmn) (hTm ω hmn))

/-! ### The band process before the lifetime -/

/-- The drift part `∫₀ʳ itoGen h(U)` along the path. -/
def Ihat (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..r, genExpr κ ρL ρR hB' hB'' (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) u

/-- The band process `h(U_r) − ∫₀ʳ itoGen h(U)` along the path. -/
def Nhat (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  hB (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r) - Ihat κ ρL ρR W VL VR r ω

theorem bandN_eq_Nhat (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω) {n : ℕ} {ω : Ω}
    (hω : ω ∈ G) {r : ℝ≥0} (hr : r ≤ angLoc G T W VL VR B ζ n ω) :
    bandN κ xL xR ρL ρR G T W VL VR B ζ n r ω = Nhat κ ρL ρR W VL VR r ω := by
  have hp := (hgood ω hω).1
  have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr) (angLoc_lt_lifetime (hgood ω hω))
  have hI : bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) r ω = Ihat κ ρL ρR W VL VR r ω := by
    unfold bandI Ihat
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le r.coe_nonneg] at hu
    exact bandC_eq n hω ⟨hu.1, hu.2.trans (by exact_mod_cast hr)⟩
  have e : coordA xL xR G VL VR (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) r ω =
      (fun i => VL i r ω, fun j => VR j r ω, bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) r ω) := by
    simp only [coordA, hω, ↓reduceIte]
  have hU := angU_pathCoord hp (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) r ω) hrζ
  simp only [bandN, min_eq_left hr, bandΦ, e, Nhat]
  rw [← hI]
  congr 2
  simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte]
  exact hU

/-! ### Doob's inequality for the oscillation -/

/-- The angular clock up to `s ∧ σ_n` (good event; `0` off it). -/
def clockYs (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (n : ℕ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  (coordA xL xR G VL VR (clockI xL xR G VL VR (angLoc G T W VL VR B ζ n))
    (min s (angLoc G T W VL VR B ζ n ω)) ω).2.2

/-- The tail clock `∫_{s∧σ_n}^{σ_n} D^{-2}`. -/
def clockR (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (n : ℕ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  clockY xL xR G T W VL VR B ζ n ω - clockYs xL xR G T W VL VR B ζ n s ω

section Tail

variable (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω) (hx : 0 < xR 0 - xL 0)
include hgood hx

theorem clockR_eq {n : ℕ} {s : ℝ≥0} {ω : Ω} (hω : ω ∈ G) :
    clockR xL xR G T W VL VR B ζ n s ω = ∫ u in (min s (angLoc G T W VL VR B ζ n ω) : ℝ)..
      (angLoc G T W VL VR B ζ n ω : ℝ), (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 := by
  have hσζ := angLoc_lt_lifetime (n := n) (G := G) (hgood ω hω)
  have hci := intervalIntegrable_clockRate (hgood ω hω).1 hx hσζ
  unfold clockR
  rw [clockY_eq hω]
  simp only [clockYs, coordA, hω, ↓reduceIte]
  rw [clockI_eq n hω (min_le_right _ _), NNReal.coe_min]
  refine intervalIntegral.integral_interval_sub_left hci (hci.mono_set ?_)
  rw [uIcc_of_le (le_min s.coe_nonneg (angLoc G T W VL VR B ζ n ω).coe_nonneg),
    uIcc_of_le (angLoc G T W VL VR B ζ n ω).coe_nonneg]
  exact Icc_subset_Icc_right (min_le_right _ _)

theorem clockR_nonneg (n : ℕ) (s : ℝ≥0) (ω : Ω) : 0 ≤ clockR xL xR G T W VL VR B ζ n s ω := by
  by_cases hω : ω ∈ G
  · rw [clockR_eq hgood hx hω]
    exact intervalIntegral.integral_nonneg (by exact_mod_cast min_le_right _ _) fun _ _ => by positivity
  · simp [clockR, clockY, clockYs, coordA, hω]

omit hgood hx in
theorem clockR_le (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    clockR xL xR G T W VL VR B ζ n s ω ≤ clockY xL xR G T W VL VR B ζ n ω := by
  unfold clockR
  have : 0 ≤ clockYs xL xR G T W VL VR B ζ n s ω := by
    by_cases hω : ω ∈ G
    · simp only [clockYs, coordA, hω, ↓reduceIte, clockI]
      exact intervalIntegral.integral_nonneg (by positivity) fun _ _ => by unfold clockC; positivity
    · simp [clockYs, coordA, hω]
  linarith

end Tail

section Osc

variable (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)
  {K' K'' : ℝ} (hK' : ∀ u, |hB' u| ≤ K') (hK'' : ∀ u, |hB'' u| ≤ K'')

include hE hGm hGc hgood hT hx in
theorem measurable_clockR (n : ℕ) (s : ℝ≥0) : Measurable (clockR xL xR G T W VL VR B ζ n s) := by
  have h := measurable_coordA_angLoc hE hGm hGc hgood hT n (I := clockI xL xR G VL VR
    (angLoc G T W VL VR B ζ n)) ⟨_, measurable_clockI hE hGm hGc hgood hT n, fun _ _ _ _ => rfl⟩
    (fun ω _ => continuousOn_clockI hgood hx n ω) s
  have hs := (measurable_snd.comp (measurable_snd.comp h)).mono ((usualAugmentation 𝓕 P).le _) le_rfl
  exact (measurable_clockY hE hGm hGc hgood hT hx n).sub hs

include hgood hx in
theorem continuous_bandN (n : ℕ) (ω : Ω) :
    Continuous fun t => bandN κ xL xR ρL ρR G T W VL VR B ζ n t ω := by
  by_cases hω : ω ∈ G
  · have hω' := hgood ω hω
    have hF := hω'.1.isForcePath
    set σ := angLoc G T W VL VR B ζ n ω
    have hsub : Iic σ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast hs) (angLoc_lt_lifetime hω')
    have hIc := continuousOn_bandI hgood n hx hω (κ := κ) (ρL := ρL) (ρR := ρR)
    have hpath : ContinuousOn (fun r => ((fun i => VL i r ω, fun j => VR j r ω,
        bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) r ω), B r ω) :
          ℝ≥0 → SCoord nL (nR + 1) × ℝ) (Iic σ) :=
      ((continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
        ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk hIc)).prodMk
        hω'.2.1.continuousOn
    have hmaps : MapsTo (fun r => ((fun i => VL i r ω, fun j => VR j r ω,
        bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) r ω), B r ω) :
          ℝ≥0 → SCoord nL (nR + 1) × ℝ) (Iic σ) angRegion := fun r hr => by
      show 0 < gapD _
      exact hx.trans_le (le_gap_of_lt hω' (hsub hr))
    have hΦ := ((contDiffOn_bandΦ κ xL xR ρL ρR).continuousOn.comp hpath hmaps).comp_continuous
      (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right r σ)
    refine hΦ.congr fun t => ?_
    simp only [bandN, coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte, Function.comp_apply, id_eq, σ]
  · simp only [bandN, coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    exact continuous_const

include hκ hE hGm hGc hgood hT hx hK' hK'' in
/-- **Doob's inequality for the oscillation after `s`**, with the `L²` identity: for every `δ > 0`,
`ε P(sup_{r ≤ n} |N_r − N_{r∧s}| ≥ ε) ≤ δ/2 + κ K'² E[∫_{s∧σ_n}^{σ_n} D^{-2}]/(2δ)`. -/
theorem measureReal_osc_le (n : ℕ) (s : ℝ≥0) {ε δ : ℝ} (hδ : 0 < δ) :
    ε * P.real {ω | ε ≤ ⨆ i : Set.Iic (n : ℝ≥0), ‖1 * (bandN κ xL xR ρL ρR G T W VL VR B ζ n i ω -
        bandN κ xL xR ρL ρR G T W VL VR B ζ n (min (i : ℝ≥0) s) ω)‖} ≤
      δ / 2 + κ * K' ^ 2 * (∫ ω, clockR xL xR G T W VL VR B ζ n s ω ∂P) / (2 * δ) := by
  have hP := hE.1.isProbabilityMeasure'
  set N := bandN κ xL xR ρL ρR G T W VL VR B ζ n with hNdef
  have hM := martingale_bandN hκ hE hGm hGc hgood hT hx hK' hK'' n
  have hb := abs_bandN_le hκ hE hGc hgood hx hK' hK'' n
  have hX := WangWu.martingale_mul_sub_stopped hM (fun ω t => (continuous_bandN hgood hx n ω).continuousWithinAt)
    hb (isStoppingTime_const (usualAugmentation 𝓕 P) s) (Z := fun _ => 1)
    stronglyMeasurable_const (K' := 1) fun _ => by norm_num
  have hXc : ∀ ω, Continuous fun t => 1 * (N t ω - N (min t s) ω) := fun ω =>
    continuous_const.mul ((continuous_bandN hgood hx n ω).sub
      ((continuous_bandN hgood hx n ω).comp (continuous_id.min continuous_const)))
  have hdoob := ProbabilityTheory.maximal_ineq_norm hX ε (n : ℝ≥0) fun ω => (hXc ω).isRightContinuous
  set A := {ω | ε ≤ ⨆ i : Set.Iic (n : ℝ≥0), ‖1 * (N i ω - N (min (i : ℝ≥0) s) ω)‖} with hA
  set Xn : Ω → ℝ := fun ω => 1 * (N n ω - N (min (n : ℝ≥0) s) ω) with hXn
  have hXi : Integrable Xn P := hX.integrable n
  have hXm : StronglyMeasurable Xn := (hX.1 n).mono ((usualAugmentation 𝓕 P).le _)
  have hX2 : Integrable (fun ω => Xn ω ^ 2) P := by
    refine Integrable.of_bound (hXm.aestronglyMeasurable.pow 2) ((2 * (1 + bandKc κ xL xR ρL ρR K' K'' n)) ^ 2)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    simp only [hXn, one_mul]
    have h1 := hb n ω
    have h2 := hb (min (n : ℝ≥0) s) ω
    calc |N n ω - N (min (n : ℝ≥0) s) ω| ≤ |N n ω| + |N (min (n : ℝ≥0) s) ω| := abs_sub _ _
      _ ≤ _ := by linarith
  -- the Doob bound
  have h1 : ε * P.real A ≤ ∫ ω, |Xn ω| ∂P := by
    refine hdoob.trans ?_
    rw [smul_eq_mul] at *
    refine setIntegral_le_integral hXi.norm (ae_of_all _ fun ω => norm_nonneg _) |>.trans (le_of_eq ?_)
    simp only [Real.norm_eq_abs]
  -- `|x| ≤ δ/2 + x²/(2δ)`
  have h2 : ∫ ω, |Xn ω| ∂P ≤ ∫ ω, (δ / 2 + Xn ω ^ 2 / (2 * δ)) ∂P := by
    refine integral_mono hXi.abs ((integrable_const _).add (hX2.div_const _)) fun ω => ?_
    rw [show δ / 2 + Xn ω ^ 2 / (2 * δ) = (δ ^ 2 + Xn ω ^ 2) / (2 * δ) by field_simp,
      le_div_iff₀ (by positivity)]
    nlinarith [sq_abs (Xn ω), sq_nonneg (|Xn ω| - δ)]
  -- the `L²` identity and the tail clock
  have hL2 : ∫ ω, Xn ω ^ 2 ∂P ≤ κ * K' ^ 2 * ∫ ω, clockR xL xR G T W VL VR B ζ n s ω ∂P := by
    have hid := integral_sq_sub_bandN hκ hE hGm hGc hgood hT hx hK' hK'' n
      (min_le_left (n : ℝ≥0) s)
    have e : (fun ω => Xn ω ^ 2) = fun ω => (N n ω - N (min (n : ℝ≥0) s) ω) ^ 2 := by
      funext ω; simp only [hXn, one_mul]
    rw [e, hid, ← integral_const_mul]
    have hM2 := martingale_bandN_sq hκ hE hGm hGc hgood hT hx hK' hK'' n
    have hN2 : ∀ r, Integrable (fun ω => N r ω ^ 2) P := fun r => by
      refine Integrable.of_bound ((((hM.1 r).mono ((usualAugmentation 𝓕 P).le r)).aestronglyMeasurable).pow 2)
        ((1 + bandKc κ xL xR ρL ρR K' K'' n) ^ 2) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb r ω) 2
    set s' : ℝ≥0 := min (n : ℝ≥0) s
    have hJi : Integrable (fun ω => bandJ κ xL xR ρL ρR G T W VL VR B ζ n n ω -
        bandJ κ xL xR ρL ρR G T W VL VR B ζ n s' ω) P := by
      refine (((hN2 n).sub (hN2 s')).sub ((hM2.integrable n).sub (hM2.integrable s'))).congr
        (ae_of_all _ fun ω => ?_)
      simp only [Pi.sub_apply]; ring
    have hRi : Integrable (clockR xL xR G T W VL VR B ζ n s) P := by
      refine Integrable.of_bound (measurable_clockR hE hGm hGc hgood hT hx n s).aestronglyMeasurable
        (n * ((xR 0 - xL 0) ^ 2)⁻¹) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (clockR_nonneg hgood hx n s ω)]
      refine (clockR_le n s ω).trans ?_
      by_cases hω : ω ∈ G
      · have h := clockI_le hgood n hx (t := angLoc G T W VL VR B ζ n ω) (angLoc_le_n n ω) ω
        simp only [clockY, coordA, hω, ↓reduceIte, min_eq_right (angLoc_le_n n ω)]
        exact (le_abs_self _).trans h
      · simp only [clockY, coordA, hω, ↓reduceIte]; positivity
    refine integral_mono hJi (hRi.const_mul _) fun ω => ?_
    by_cases hω : ω ∈ G
    · have h := bandJ_sub_le hgood n hκ.le hx hK' hω (min_le_left (n : ℝ≥0) s)
      have hmin : min ((s' : ℝ≥0) : ℝ) (angLoc G T W VL VR B ζ n ω : ℝ) =
          min (s : ℝ) (angLoc G T W VL VR B ζ n ω : ℝ) := by
        rw [← NNReal.coe_min, ← NNReal.coe_min]
        congr 1
        simp only [s']
        rw [min_assoc]
        exact min_eq_right ((min_le_right _ _).trans (angLoc_le_n n ω))
      rw [hmin] at h
      rw [clockR_eq hgood hx hω]
      exact h
    · have h0 : ∀ r, bandJ κ xL xR ρL ρR G T W VL VR B ζ n r ω = 0 := fun r => by
        simp [bandJ, angLoc_of_not_mem hω]
      have hR0 : clockR xL xR G T W VL VR B ζ n s ω = 0 := by simp [clockR, clockY, clockYs, coordA, hω]
      rw [h0, h0, hR0]; simp
  have h3 : ∫ ω, (δ / 2 + Xn ω ^ 2 / (2 * δ)) ∂P = δ / 2 + (∫ ω, Xn ω ^ 2 ∂P) / (2 * δ) := by
    rw [integral_add (integrable_const _) (hX2.div_const _), integral_const, integral_div]
    simp
  calc ε * P.real A ≤ δ / 2 + (∫ ω, Xn ω ^ 2 ∂P) / (2 * δ) := h1.trans (h2.trans h3.le)
    _ ≤ _ := by
        gcongr

end Osc

/-! ### The tail clocks tend to zero -/

section Tails

/-- The total angular clock `sup_n ∫₀^{σ_n} D^{-2}`. -/
def clockTot (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (clockY xL xR G T W VL VR B ζ n ω)

/-- The tail clock `sup_n ∫_{s∧σ_n}^{σ_n} D^{-2}`. -/
def clockTail (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (s : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (clockR xL xR G T W VL VR B ζ n (s : ℝ≥0) ω)

variable (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω) (hx : 0 < xR 0 - xL 0)
  (hTm : ∀ ω, Monotone (T · ω))
include hgood hx hTm

theorem integral_clockRate_mono {ω : Ω} (hω : ω ∈ G) {m n : ℕ} (hmn : m ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ angLoc G T W VL VR B ζ m ω) :
    ∫ u in (0 : ℝ)..a, (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 ≤
      ∫ u in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ), (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 := by
  have hσζ := angLoc_lt_lifetime (n := n) (G := G) (hgood ω hω)
  have hmono : (angLoc G T W VL VR B ζ m ω : ℝ) ≤ angLoc G T W VL VR B ζ n ω := by
    exact_mod_cast angLoc_mono hgood hTm ω hmn
  exact intervalIntegral.integral_mono_interval le_rfl ha (hab.trans hmono)
    (ae_of_all _ fun _ => by positivity) (intervalIntegrable_clockRate (hgood ω hω).1 hx hσζ)

theorem clockY_mono (ω : Ω) : Monotone fun n => clockY xL xR G T W VL VR B ζ n ω := by
  intro m n hmn
  by_cases hω : ω ∈ G
  · simp only
    rw [clockY_eq hω, clockY_eq hω]
    exact integral_clockRate_mono hgood hx hTm hω hmn (angLoc G T W VL VR B ζ m ω).coe_nonneg le_rfl
  · simp [clockY, coordA, hω]

omit hgood hx hTm in
theorem clockTail_le (s : ℕ) (ω : Ω) :
    clockTail xL xR G T W VL VR B ζ s ω ≤ clockTot xL xR G T W VL VR B ζ ω :=
  iSup_mono fun n => ENNReal.ofReal_le_ofReal (clockR_le n s ω)

/-- **The tail clocks tend to zero** where the total clock is finite. -/
theorem tendsto_clockTail {ω : Ω} (hfin : clockTot xL xR G T W VL VR B ζ ω < ⊤) :
    Tendsto (fun s : ℕ => clockTail xL xR G T W VL VR B ζ s ω) atTop (𝓝 0) := by
  by_cases hω : ω ∈ G
  swap
  · have h0 : ∀ s : ℕ, clockTail xL xR G T W VL VR B ζ s ω = 0 := fun s => by
      simp [clockTail, clockR, clockY, clockYs, coordA, hω]
    simp only [h0]; exact tendsto_const_nhds
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  set Y := clockTot xL xR G T W VL VR B ζ ω with hY
  by_cases hY0 : Y = 0
  · exact ⟨0, fun s _ => (clockTail_le s ω).trans (by rw [← hY, hY0]; exact bot_le)⟩
  have hlt : Y - ε < Y := ENNReal.sub_lt_self hfin.ne hY0 hε.ne'
  have hlt' : Y - ε < ⨆ m : ℕ, ENNReal.ofReal (clockY xL xR G T W VL VR B ζ m ω) := hlt
  obtain ⟨n₀, hn₀⟩ := lt_iSup_iff.1 hlt'
  refine ⟨n₀, fun s hs => iSup_le fun n => ?_⟩
  set σ := fun m : ℕ => angLoc G T W VL VR B ζ m ω
  by_cases hn : n ≤ n₀
  · have hσs : σ n ≤ (s : ℝ≥0) := (angLoc_le_n n ω).trans (by exact_mod_cast hn.trans hs)
    have hσs' : ((σ n : ℝ≥0) : ℝ) ≤ ((s : ℝ≥0) : ℝ) := by exact_mod_cast hσs
    rw [clockR_eq hgood hx hω, min_eq_right hσs', intervalIntegral.integral_same, ENNReal.ofReal_zero]
    exact bot_le
  · push Not at hn
    have hYn : clockY xL xR G T W VL VR B ζ n ω = ∫ u in (0 : ℝ)..(σ n : ℝ),
        (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 := clockY_eq hω
    have hYn₀ : clockY xL xR G T W VL VR B ζ n₀ ω = ∫ u in (0 : ℝ)..(σ n₀ : ℝ),
        (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 := clockY_eq hω
    have hσζ := angLoc_lt_lifetime (n := n) (G := G) (hgood ω hω)
    have hci := intervalIntegrable_clockRate (hgood ω hω).1 hx hσζ
    have hms : (min ((s : ℝ≥0) : ℝ) (σ n) : ℝ) ≤ σ n := min_le_right _ _
    have hm0 : (0 : ℝ) ≤ min ((s : ℝ≥0) : ℝ) (σ n) := le_min (s : ℝ≥0).coe_nonneg (σ n).coe_nonneg
    have hR : clockR xL xR G T W VL VR B ζ n s ω = clockY xL xR G T W VL VR B ζ n ω -
        ∫ u in (0 : ℝ)..(min ((s : ℝ≥0) : ℝ) (σ n) : ℝ), (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 := by
      rw [clockR_eq hgood hx hω, hYn]
      refine (intervalIntegral.integral_interval_sub_left hci (hci.mono_set ?_)).symm
      rw [uIcc_of_le hm0, uIcc_of_le (σ n).coe_nonneg]
      exact Icc_subset_Icc_right hms
    have hge : clockY xL xR G T W VL VR B ζ n₀ ω ≤
        ∫ u in (0 : ℝ)..(min ((s : ℝ≥0) : ℝ) (σ n) : ℝ), (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 := by
      rw [hYn₀]
      refine intervalIntegral.integral_mono_interval le_rfl (σ n₀).coe_nonneg ?_
        (ae_of_all _ fun _ => by positivity) (hci.mono_set ?_)
      · refine le_min ?_ (by exact_mod_cast angLoc_mono hgood hTm ω hn.le)
        exact ((by exact_mod_cast angLoc_le_n n₀ ω : (σ n₀ : ℝ) ≤ n₀)).trans (by exact_mod_cast hs)
      · rw [uIcc_of_le hm0, uIcc_of_le (σ n).coe_nonneg]
        exact Icc_subset_Icc_right hms
    have hY₀n : 0 ≤ clockY xL xR G T W VL VR B ζ n₀ ω := clockY_nonneg n₀ ω
    calc ENNReal.ofReal (clockR xL xR G T W VL VR B ζ n s ω)
        ≤ ENNReal.ofReal (clockY xL xR G T W VL VR B ζ n ω - clockY xL xR G T W VL VR B ζ n₀ ω) := by
          rw [hR]; exact ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (clockY xL xR G T W VL VR B ζ n ω) -
            ENNReal.ofReal (clockY xL xR G T W VL VR B ζ n₀ ω) := ENNReal.ofReal_sub _ hY₀n
      _ ≤ Y - ENNReal.ofReal (clockY xL xR G T W VL VR B ζ n₀ ω) :=
          tsub_le_tsub_right (le_iSup (fun m => ENNReal.ofReal (clockY xL xR G T W VL VR B ζ m ω)) n) _
      _ ≤ ε := by
          rw [tsub_le_iff_right, add_comm]
          exact tsub_le_iff_right.1 hn₀.le

end Tails

end Conv

end Clock

end Sec7

end InteractingSLE
