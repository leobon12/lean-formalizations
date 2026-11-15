import InteractingSLE.Spec.Coupling.Lemma311
import InteractingSLE.Spec.Sec2.GirsanovCut

/-!
# Safe stops: protection without a bound on the driving coordinates

Packet PROVE-T11-L311 (Specification §3.3, L559–L565, graph node `SPEC.thm-1.1#safe-stops`; L546: "localize so that
… the relevant continuous driving quantities are bounded"). The safe stops of the source,
`s_{U,n} = T_n ∧ inf{t : inf_{z ∈ Ū} Im g_t(z) ≤ 1/n}`, are bounded, strictly before `T_*`, and keep `Ū` at height
`≥ 1/n`; they do not bound `|W|, |B|, |V|`. This file removes the bound `R` of `IsTestProtected` from the
characteristic-function martingale and from Lemma 3.11 by localizing at the exit times of the stopped coordinate size
`|W| + |B| + Σ|V|` from `[0, R)` and letting `R → ∞` (dominated convergence: the integrands are bounded by
`exp(θ² |E₀ − c t| / 2)`, `c = ((2/δ) ∫ |φ|)²`).

## Main results

* `IsTestSafe`: the protection of `supp φ` by `σ` (`σ < ζ`, `σ ≤ N`, `supp φ` unswallowed at `σ` with
  `Im f_σ ≥ δ`);
* `setIntegral_cexp_testMean_eq_of_safe`: the characteristic-function martingale identity at safe stops;
* `map_eq_gaussianReal_of_condExp_testMean_of_safe`: Lemma 3.11 at safe stops.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {φ : ℂ → ℝ} {σ : Ω → ℝ≥0} {δ R N : ℝ}

/-- **Safe protection of `supp φ` by `σ`** (the safe stops `s_{U,n}` of Specification L559–L565): `σ < ζ`,
`σ ≤ N`, and every `z ∈ supp φ` has a forward solution on `[0, σ]` with `δ ≤ Im f_σ(z)`. -/
def IsTestSafe (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (φ : ℂ → ℝ) (σ : Ω → ℝ≥0) (δ N : ℝ) (ω : Ω) :
    Prop :=
  (σ ω : ℝ≥0∞) < ζ ω ∧ (σ ω : ℝ) ≤ N ∧
    ∀ z ∈ tsupport φ, (∃ u, IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (fwdMap (rpath (W · ω)) (σ ω) z).im

/-- The size `|W| + |B| + Σ |V^L| + Σ |V^R|` of the driving coordinates. -/
def coordSize (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  |W t ω| + |B t ω| + ∑ i, |VL i t ω| + ∑ i, |VR i t ω|

theorem coordSize_bounds {t : ℝ≥0} {ω : Ω} (h : coordSize W VL VR B t ω ≤ R) :
    |W t ω| ≤ R ∧ |B t ω| ≤ R ∧ (∀ i, |VL i t ω| ≤ R) ∧ ∀ i, |VR i t ω| ≤ R := by
  have h1 : 0 ≤ ∑ i, |VL i t ω| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : 0 ≤ ∑ i, |VR i t ω| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hW := abs_nonneg (W t ω)
  have hB := abs_nonneg (B t ω)
  unfold coordSize at h
  refine ⟨by linarith, by linarith, fun i => ?_, fun i => ?_⟩
  · have := Finset.single_le_sum (f := fun i => |VL i t ω|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith
  · have := Finset.single_le_sum (f := fun i => |VR i t ω|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith

/-- A good path at a safe stop is a good path at any earlier time `σ' ≤ σ`, for any bound `R` on the coordinates
up to `σ'`. -/
theorem isGoodTest_of_le {σ' : Ω → ℝ≥0} {ω : Ω}
    (hP : IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)) (hB : Continuous (B · ω))
    (hs : IsTestSafe W ζ φ σ δ N ω) (hφH : tsupport φ ⊆ H) (hle : σ' ω ≤ σ ω)
    (hR : ∀ s ≤ σ' ω, coordSize W VL VR B s ω ≤ R) :
    IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ' δ R N ω := by
  obtain ⟨hσζ, hN, hK⟩ := hs
  have hle' : (σ' ω : ℝ) ≤ σ ω := by exact_mod_cast hle
  refine ⟨hP, hB, lt_of_le_of_lt (by exact_mod_cast hle) hσζ, hle'.trans hN,
    fun s hs => coordSize_bounds (hR s hs), fun z hz => ⟨?_, ?_⟩⟩
  · obtain ⟨u, hu⟩ := (hK z hz).1
    exact ⟨u, isForwardSol_of_le hu (σ' ω).coe_nonneg hle'⟩
  · have hanti := antitoneOn_im_fwdMap_of_continuousOn (σ ω).coe_nonneg
      (Ito.continuousOn_rpath hP.2.2.2.1 hσζ) (hφH hz) (hK z hz).1
    exact (hK z hz).2.trans (hanti ⟨(σ' ω).coe_nonneg, hle'⟩ ⟨(σ ω).coe_nonneg, le_rfl⟩ hle')

/-! ### The exit times of the stopped coordinate size -/

section Exit

/-- The good event of a safe stop: path properties, a continuous Brownian path, safe protection. -/
def IsGoodSafe (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (φ : ℂ → ℝ) (σ : Ω → ℝ≥0) (δ N : ℝ) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
    (fun t => B t ω) (ζ ω) ∧ Continuous (B · ω) ∧ IsTestSafe W ζ φ σ δ N ω

/-- The coordinate size stopped at `σ` on `G` (and `0` off `G`). -/
def sizeProc (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (G : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then coordSize W VL VR B (min t (σ ω)) ω else 0

variable {G : Set Ω}
  (hGs : ∀ ω ∈ G, IsGoodSafe κ xL xR ρL ρR W VL VR B ζ φ σ δ N ω)
include hGs

theorem continuous_sizeProc (ω : Ω) : Continuous fun t => sizeProc W VL VR B σ G t ω := by
  by_cases hω : ω ∈ G
  · obtain ⟨hP, hB, hσζ, -, -⟩ := hGs ω hω
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t ht =>
      lt_of_le_of_lt (by exact_mod_cast ht) hσζ
    have hst : Continuous fun t : ℝ≥0 => min t (σ ω) := continuous_id.min continuous_const
    have hmem : ∀ t : ℝ≥0, min t (σ ω) ∈ Iic (σ ω) := fun t => mem_Iic.2 (min_le_right _ _)
    have cW : Continuous fun t => W (min t (σ ω)) ω :=
      (hP.2.2.2.1.mono hsub).comp_continuous hst hmem
    have cVL : ∀ i, Continuous fun t => VL i (min t (σ ω)) ω := fun i =>
      ((hP.2.2.2.2.1 i).mono hsub).comp_continuous hst hmem
    have cVR : ∀ i, Continuous fun t => VR i (min t (σ ω)) ω := fun i =>
      ((hP.2.2.2.2.2.1 i).mono hsub).comp_continuous hst hmem
    simp only [sizeProc, hω, ↓reduceIte, coordSize]
    exact ((cW.abs.add (hB.comp hst).abs).add (continuous_finsetSum _ fun i _ => (cVL i).abs)).add
      (continuous_finsetSum _ fun i _ => (cVR i).abs)
  · simp only [sizeProc, hω, ↓reduceIte]; exact continuous_const

omit hGs in
theorem measurable_sizeProc (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G)
    (hGs : ∀ ω ∈ G, IsGoodSafe κ xL xR ρL ρR W VL VR B ζ φ σ δ N ω) (t : ℝ≥0) :
    Measurable[nullAugmented 𝓕 P t] (sizeProc W VL VR B σ G t) := by
  obtain ⟨hB, hWa, hVLa, hVRa, -⟩ := hE
  set 𝓖 := nullAugmented 𝓕 P
  have hsub : ∀ ω ∈ G, Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun ω hω t ht =>
    lt_of_le_of_lt (by exact_mod_cast ht) (hGs ω hω).2.2.1
  have hstop : ∀ X : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓕 ζ X →
      (∀ ω ∈ G, ContinuousOn (X · ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω}) →
      Measurable[𝓖 t] fun ω => if ω ∈ G then X (min t (σ ω)) ω else 0 := fun X hX hXc =>
    measurable_stopped_of_agree (K := Girsanov.killed ζ X) (X := X) hσ
      (fun s => Girsanov.measurable_killed (adaptedBefore_mono (le_nullAugmented 𝓕 P) hX) s) hG0 0
      (fun ω hω s hs => Girsanov.killed_of_lt (hsub ω hω hs)) (fun ω hω => (hXc ω hω).mono (hsub ω hω)) t
  have hW' := hstop W hWa fun ω hω => (hGs ω hω).1.2.2.2.1
  have hVL' := fun i => hstop (VL i) (hVLa i) fun ω hω => (hGs ω hω).1.2.2.2.2.1 i
  have hVR' := fun i => hstop (VR i) (hVRa i) fun ω hω => (hGs ω hω).1.2.2.2.2.2.1 i
  have hB' : Measurable[𝓖 t] fun ω => if ω ∈ G then B (min t (σ ω)) ω else 0 :=
    measurable_stopped_of_agree (K := B) (X := B) hσ
      (fun s => (hB.2.1 s).mono (le_nullAugmented 𝓕 P s) le_rfl) hG0 0 (fun _ _ _ _ => rfl)
      (fun ω hω => (hGs ω hω).2.1.continuousOn) t
  have hGt : MeasurableSet[𝓖 t] G := 𝓖.mono (zero_le (a := t)) G hG0
  have e : sizeProc W VL VR B σ G t = G.piecewise (fun ω =>
      |if ω ∈ G then W (min t (σ ω)) ω else 0| + |if ω ∈ G then B (min t (σ ω)) ω else 0| +
        ∑ i, |if ω ∈ G then VL i (min t (σ ω)) ω else 0| +
        ∑ i, |if ω ∈ G then VR i (min t (σ ω)) ω else 0|) fun _ => 0 := by
    funext ω; by_cases hω : ω ∈ G <;> simp [sizeProc, coordSize, hω, Set.piecewise]
  rw [e]
  have ha := continuous_abs.measurable (α := ℝ)
  exact Measurable.piecewise hGt ((((ha.comp hW').add (ha.comp hB')).add
    (Finset.measurable_sum (m := 𝓖 t) _ fun i _ => ha.comp (hVL' i))).add
    (Finset.measurable_sum (m := 𝓖 t) _ fun i _ => ha.comp (hVR' i))) measurable_const

omit hGs in
/-- The safe stop `σ` cut at the exit time of the stopped coordinate size from `[0, R)` (before time `T`). -/
def exitStop (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (G : Set Ω) (R : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  min (σ ω) (hittingBtwn (sizeProc W VL VR B σ G) (Ici R) 0 T ω)

omit hGs in
theorem isStoppingTime_exitStop (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G)
    (hGs : ∀ ω ∈ G, IsGoodSafe κ xL xR ρL ρR W VL VR B ζ φ σ δ N ω) (R : ℝ) (T : ℝ≥0) :
    IsStoppingTime (nullAugmented 𝓕 P)
      fun ω => ((exitStop W VL VR B σ G R T ω : ℝ≥0) : WithTop ℝ≥0) := by
  have hτ := ItoLite.isStoppingTime_hittingBtwn_of_isClosed (𝓕 := nullAugmented 𝓕 P)
    (U := sizeProc W VL VR B σ G) (fun t => measurable_sizeProc hE hσ hG0 hGs t)
    (continuous_sizeProc hGs) (isClosed_Ici (a := R)) T
  have h := hσ.min hτ
  convert h using 2 with ω
  simp [exitStop]

omit hGs in
theorem exitStop_le (R : ℝ) (T : ℝ≥0) (ω : Ω) : exitStop W VL VR B σ G R T ω ≤ σ ω :=
  min_le_left _ _

/-- Before the exit stop the coordinate size is at most `R` (if it starts below `R`). -/
theorem coordSize_le_of_le_exitStop {ω : Ω} (hω : ω ∈ G)
    (hR0 : coordSize W VL VR B 0 ω < R) {T : ℝ≥0} {s : ℝ≥0}
    (hs : s ≤ exitStop W VL VR B σ G R T ω) : coordSize W VL VR B s ω ≤ R := by
  set D := sizeProc W VL VR B σ G
  have hsσ : s ≤ σ ω := hs.trans (min_le_left _ _)
  have hsτ : s ≤ hittingBtwn D (Ici R) 0 T ω := hs.trans (min_le_right _ _)
  have hD : ∀ r ≤ σ ω, D r ω = coordSize W VL VR B r ω := fun r hr => by
    simp [D, sizeProc, hω, min_eq_left hr]
  have hlt : ∀ r < hittingBtwn D (Ici R) 0 T ω, D r ω < R := fun r hr =>
    not_le.1 fun h => notMem_of_lt_hittingBtwn hr (zero_le (a := r)) (mem_Ici.2 h)
  rcases hsτ.lt_or_eq with h | h
  · rw [← hD s hsσ]; exact (hlt s h).le
  · rcases eq_or_ne s 0 with h0 | h0
    · rw [h0]; exact hR0.le
    · have hcl : IsClosed {r : ℝ≥0 | D r ω ≤ R} :=
        isClosed_le (continuous_sizeProc hGs ω) continuous_const
      have hsub : Ico 0 s ⊆ {r : ℝ≥0 | D r ω ≤ R} := fun r hr => (hlt r (h ▸ hr.2)).le
      have hmem : s ∈ closure (Ico 0 s) := by
        rw [closure_Ico (Ne.symm h0)]; exact ⟨zero_le, le_rfl⟩
      rw [← hD s hsσ]
      exact hcl.closure_subset_iff.2 hsub hmem

/-- For a fixed good path, the exit stops at levels `n → ∞` are eventually `σ` itself. -/
theorem eventually_exitStop_eq {ω : Ω} {T : ℝ≥0} (hσT : σ ω ≤ T) :
    ∀ᶠ n : ℕ in atTop, exitStop W VL VR B σ G (n : ℝ) T ω = σ ω := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    (continuous_sizeProc hGs ω).continuousOn
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop C] with n hn
  have hno : ¬ ∃ j ∈ Icc (0 : ℝ≥0) T, sizeProc W VL VR B σ G j ω ∈ Ici (n : ℝ) := by
    rintro ⟨j, hj, hjn⟩
    have := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hC j hj))
    exact absurd (hjn.trans this) (not_le.2 hn)
  simp only [exitStop, hittingBtwn, hno, ↓reduceIte]
  exact min_eq_left hσT

end Exit

/-! ### The characteristic-function identity at safe stops -/

section Safe

/-- `exp(iθ (𝔥_{t∧σ}, φ) − θ² E_{t∧σ}(φ)/2)`. -/
def cfTest (κ : ℝ) (W : ℝ≥0 → Ω → ℝ) (u : Ω → ℝ≥0 → ℂ → ℝ) (φ : ℂ → ℝ) (σ : Ω → ℝ≥0) (θ : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * θ *
    ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (min t (σ ω) : ℝ≥0)
      (u ω (min t (σ ω))) z * φ z : ℝ) : ℂ) -
    θ ^ 2 * ((loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (min t (σ ω) : ℝ≥0) φ : ℝ) : ℂ) / 2)

theorem exists_goodSafeSet (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hσs : ∀ᵐ ω ∂P, IsTestSafe W ζ φ σ δ N ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ MeasurableSet[nullAugmented 𝓕 P 0] G ∧
      ∀ ω ∈ G, IsGoodSafe κ xL xR ρL ρR W VL VR B ζ φ σ δ N ω := by
  obtain ⟨hB, -, -, -, hpath⟩ := hE
  have hae : ∀ᵐ ω ∂P, IsGoodSafe κ xL xR ρL ρR W VL VR B ζ φ σ δ N ω := by
    filter_upwards [hpath, hB.1.cont, hσs] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  have h0 : P (toMeasurable P {ω | ¬ IsGoodSafe κ xL xR ρL ρR W VL VR B ζ φ σ δ N ω}) = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.1 hae
  refine ⟨(toMeasurable P {ω | ¬ IsGoodSafe κ xL xR ρL ρR W VL VR B ζ φ σ δ N ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, by rw [compl_compl]; exact h0,
    (measurableSet_nullAugmented_of_null (𝓕 := 𝓕) (measurableSet_toMeasurable _ _) h0 0).compl,
    fun ω hω => ?_⟩
  by_contra h; exact hω (subset_toMeasurable _ _ h)

theorem IsGoodSafe.coordSize_zero (hκ : 0 < κ) {ω : Ω}
    (hg : IsGoodSafe κ xL xR ρL ρR W VL VR B ζ φ σ δ N ω) :
    coordSize W VL VR B 0 ω = ∑ i, |xL i| + ∑ i, |xR i| := by
  obtain ⟨hP, -, hσζ, -, -⟩ := hg
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by simp) hσζ
  have hw := hP.2.2.2.2.2.2.2.2.2.2.2.2.1 0 hζ0
  simp only [NNReal.coe_zero, intervalIntegral.integral_same, Finset.sum_const_zero, add_zero]
    at hw
  have hW0 : W 0 ω = 0 := hP.1
  have hB0 : B 0 ω = 0 := by
    rw [hW0] at hw
    rcases mul_eq_zero.1 hw.symm with h | h
    · exact absurd h (Real.sqrt_pos.2 hκ).ne'
    · exact h
  simp only [coordSize, hW0, hB0, abs_zero, zero_add, fun i => hP.2.1 i, fun i => hP.2.2.1 i]

variable {G : Set Ω} (hGs : ∀ ω ∈ G, IsGoodSafe κ xL xR ρL ρR W VL VR B ζ φ σ δ N ω)
  (hφH : tsupport φ ⊆ H)
include hGs hφH

/-- A good path at a safe stop is good (`IsGoodTest`) for some bound `R` of its coordinates on `[0, σ]`. -/
theorem exists_isGoodTest_of_safe {ω : Ω} (hω : ω ∈ G) :
    ∃ R, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := σ ω)).exists_bound_of_continuousOn
    (continuous_sizeProc hGs ω).continuousOn
  refine ⟨C, isGoodTest_of_le (hGs ω hω).1 (hGs ω hω).2.1 (hGs ω hω).2.2 hφH le_rfl
    fun s hs => ?_⟩
  have h := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hC s ⟨zero_le, hs⟩))
  simpa [sizeProc, hω, min_eq_left hs] using h

end Safe

theorem re_cexp_arg (θ X E : ℝ) :
    (Complex.I * θ * (X : ℂ) - θ ^ 2 * (E : ℂ) / 2).re = -(θ ^ 2 * E / 2) := by
  have : Complex.I * θ * (X : ℂ) - θ ^ 2 * (E : ℂ) / 2 =
      ((-(θ ^ 2 * E / 2) : ℝ) : ℂ) + ((θ * X : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
    add_zero]

section SafeMain

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
  (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
  (hσs : ∀ᵐ ω ∂P, IsTestSafe W ζ φ σ δ N ω) (hφH : tsupport φ ⊆ H)
  (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hδ : 0 < δ) (u : Ω → ℝ≥0 → ℂ → ℝ)
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
include hE hκ hσ hσs hφH hφc hφs hδ hu

/-- **The characteristic-function martingale at a safe stop** (Specification L550–L565): for a stopping time
`σ` of the null-augmented filtration with `σ < ζ`, `σ ≤ N` and `supp φ` unswallowed at height `≥ δ` up to `σ`
(no bound on the driving coordinates), `∫_S exp(iθ (𝔥_{t∧σ}, φ) − θ² E_{t∧σ}(φ)/2)` does not depend on `t ≥ s`
for `S ∈ 𝓖_s`. -/
theorem setIntegral_cexp_testMean_eq_of_safe {s t : ℝ≥0} (hst : s ≤ t) {S : Set Ω}
    (hS : MeasurableSet[nullAugmented 𝓕 P s] S) (θ : ℝ) :
    ∫ ω in S, cfTest κ W u φ σ θ t ω ∂P = ∫ ω in S, cfTest κ W u φ σ θ s ω ∂P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨G, -, hGc, hG0, hGs⟩ := exists_goodSafeSet hE hσs
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set D₀ : ℝ := ∑ i, |xL i| + ∑ i, |xR i|
  set Nn : ℝ≥0 := N.toNNReal
  set σn : ℕ → Ω → ℝ≥0 := fun n => exitStop W VL VR B σ G n Nn with hσn_def
  have hσn : ∀ n : ℕ, IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σn n ω : WithTop ℝ≥0) :=
    fun n => isStoppingTime_exitStop hE hσ hG0 hGs n Nn
  have hgood : ∀ n : ℕ, D₀ < n → ∀ ω ∈ G,
      IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ (σn n) δ n N ω := fun n hn ω hω =>
    isGoodTest_of_le (hGs ω hω).1 (hGs ω hω).2.1 (hGs ω hω).2.2 hφH (exitStop_le _ _ ω)
      fun s hs => coordSize_le_of_le_exitStop hGs hω
        (by rw [(hGs ω hω).coordSize_zero hκ]; exact hn) hs
  have hprot : ∀ n : ℕ, D₀ < n → ∀ᵐ ω ∂P, IsTestProtected W VL VR B ζ φ (σn n) δ n N ω :=
    fun n hn => by filter_upwards [hGae] with ω hω; exact (hgood n hn ω hω).2.2
  have hevn : ∀ᶠ n : ℕ in atTop, D₀ < n := tendsto_natCast_atTop_atTop.eventually_gt_atTop D₀
  have hid : ∀ᶠ n : ℕ in atTop, ∫ ω in S, cfTest κ W u φ (σn n) θ t ω ∂P =
      ∫ ω in S, cfTest κ W u φ (σn n) θ s ω ∂P := by
    filter_upwards [hevn] with n hn
    exact setIntegral_cexp_testMean_eq hE hκ (hσn n) (hprot n hn) hφH hφc hφs hδ u hu hst hS θ
  have hlim : ∀ r : ℝ≥0, Tendsto (fun n : ℕ => ∫ ω in S, cfTest κ W u φ (σn n) θ r ω ∂P) atTop
      (𝓝 (∫ ω in S, cfTest κ W u φ σ θ r ω ∂P)) := by
    intro r
    set c : ℝ := (2 / δ * ∫ z, |φ z|) ^ 2
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => Real.exp (θ ^ 2 * |c * r - greenEnergy0 φ| / 2)) ?_ ?_ (integrable_const _) ?_
    · filter_upwards [hevn] with n hn
      obtain ⟨hX, hEn⟩ := aemeasurable_testMean_energy hE hκ (hσn n) (hprot n hn) hφH hφc hφs hδ u hu r
      have hg : Measurable fun p : ℝ × ℝ =>
          Complex.exp (Complex.I * θ * (p.1 : ℂ) - θ ^ 2 * (p.2 : ℂ) / 2) := by fun_prop
      exact (hg.comp_aemeasurable (hX.prodMk hEn)).aestronglyMeasurable.restrict
    · filter_upwards [hevn] with n hn
      refine ae_restrict_of_ae ?_
      filter_upwards [hGae] with ω hω
      have hg := hgood n hn ω hω
      have he := (hg.energy_sub_mem hφH hφc hφs hδ (zero_le (a := r))).2
      rw [min_eq_left (zero_le (a := σn n ω)), NNReal.coe_zero, hg.loewnerGreenEnergy_zero hφH]
        at he
      rw [cfTest, Complex.norm_exp, re_cexp_arg]
      refine Real.exp_le_exp.2 ?_
      have h3 := le_abs_self (c * r - greenEnergy0 φ)
      have hθ := sq_nonneg θ
      simp only [sub_zero] at he
      nlinarith [mul_le_mul_of_nonneg_left (show greenEnergy0 φ - c * r ≤
        loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (min r (σn n ω) : ℝ≥0) φ + 0 by linarith) hθ]
    · refine ae_restrict_of_ae ?_
      filter_upwards [hGae] with ω hω
      have hσN : σ ω ≤ Nn := by
        have h1 := Real.toNNReal_le_toNNReal (hGs ω hω).2.2.2.1
        rwa [Real.toNNReal_coe] at h1
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_exitStop_eq hGs (G := G) hσN] with n hn
      simp only [cfTest, σn, hn]
  exact tendsto_nhds_unique ((hlim t).congr' hid) (hlim s)

/-- **Optional stopping at a safe stop**: `E[exp(iθ (𝔥_σ, φ) − θ² E_σ(φ)/2)] = exp(iθ (𝔥₀, φ) − θ² E₀(φ)/2)`. -/
theorem integral_cexp_testMean_stopped_of_safe {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (θ : ℝ) :
    ∫ ω, Complex.exp (Complex.I * θ *
        ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (σ ω) (u ω (σ ω)) z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (σ ω) φ : ℝ) : ℂ) / 2) ∂P =
      Complex.exp (Complex.I * θ * ((∫ z, u₀ z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((greenEnergy0 φ : ℝ) : ℂ) / 2) := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨G, -, hGc, -, hGs⟩ := exists_goodSafeSet hE hσs
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have h := setIntegral_cexp_testMean_eq_of_safe hE hκ hσ hσs hφH hφc hφs hδ u hu
    (zero_le (a := N.toNNReal)) (S := univ) MeasurableSet.univ θ
  rw [setIntegral_univ, setIntegral_univ] at h
  have hl : ∀ᵐ ω ∂P, min N.toNNReal (σ ω) = σ ω := by
    filter_upwards [hGae] with ω hω
    have h1 := Real.toNNReal_le_toNNReal (hGs ω hω).2.2.2.1
    rw [Real.toNNReal_coe] at h1
    exact min_eq_right h1
  refine (integral_congr_ae (hl.mono fun ω hω => by simp only [cfTest, hω])).trans (h.trans ?_)
  have hr : ∀ᵐ ω ∂P, cfTest κ W u φ σ θ 0 ω = Complex.exp (Complex.I * θ *
      ((∫ z, u₀ z * φ z : ℝ) : ℂ) - θ ^ 2 * ((greenEnergy0 φ : ℝ) : ℂ) / 2) := by
    filter_upwards [hGae] with ω hω
    obtain ⟨R', hg⟩ := exists_isGoodTest_of_safe hGs hφH hω
    rw [cfTest, min_eq_left (zero_le (a := σ ω)), hg.testMean_zero hφH u hu hu₀, NNReal.coe_zero,
      hg.loewnerGreenEnergy_zero hφH]
  rw [integral_congr_ae hr, integral_const, probReal_univ, one_smul]

/-- **Lemma 3.11 at a safe stop** (Specification L569–L586): if, conditionally on `𝓕_σ`, `Y` is Gaussian with
mean `(𝔥_σ, φ)` and variance `E_σ(φ)`, then `Y ∼ N((𝔥₀, φ), ‖φ‖²_{H⁻¹(ℍ)})`, the law of `(h̃ + 𝔥₀, φ)`. -/
theorem map_eq_gaussianReal_of_condExp_testMean_of_safe {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {Y : Ω → ℝ} (hY : Measurable Y)
    (hcond : ∀ θ : ℝ, P[fun ω => Complex.exp (Complex.I * θ * Y ω) | hσ.measurableSpace] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * θ *
        ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (σ ω) (u ω (σ ω)) z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (σ ω) φ : ℝ) : ℂ) / 2))
    {ψ : LQGMetric.TestOn upperHalfPlaneOpens} (hψ : ⇑ψ = φ) :
    P.map Y = gaussianReal (∫ z, u₀ z * φ z) (zeroGFFTestCov upperHalfPlaneOpens φ φ).toNNReal := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hnn : 0 ≤ zeroGFFTestCov upperHalfPlaneOpens φ φ := by
    rw [← hψ]
    exact LQGMetric.zeroGFFTestCov_self_nonneg (LQGMetric.zbAdmissible_of_subset_H subset_rfl) ψ
  refine map_eq_gaussianReal_of_condExp hσ.measurableSpace_le hY hcond fun θ => ?_
  rw [integral_cexp_testMean_stopped_of_safe hE hκ hσ hσs hφH hφc hφs hδ u hu hu₀ θ, ← hψ,
    greenEnergy0_eq_zeroGFFTestCov, Real.coe_toNNReal _ (hψ ▸ hnn)]

end SafeMain

end Coupling

end InteractingSLE
