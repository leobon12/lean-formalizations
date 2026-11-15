import InteractingSLE.WangWu.CouplingTested
import InteractingSLE.Spec.Ito.Measurability
import InteractingSLE.Spec.Ito.FiltrationBasic
import QuantumZipper.Proofs.Thm11.ExtMeasTamed
import QuantumZipper.Proofs.Thm11.ExtMeasLimit

/-!
# Wang–Wu at `κ = 4`: a jointly measurable version of the frozen mean (Lemma 3.5)

Packet PROVE-WW-A2. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, Lemma 3.5 ("A jointly
measurable version has continuous time paths for Lebesgue-almost every `z`, almost surely"), ruling R31. This is the
missing input M of `planning/handoffs/PROVE-WW-A.md`: the integrated Lemma 3.6
(`martingale_integral_frozenMean_of_version`) needs a version of `(z, ω) ↦ η̄_{t∧σ₀}(z)` measurable for
`Borel(ℂ) ⊗ 𝓖_t`.

The frozen mean uses `limUnder` along the point-dependent filter `𝓝[<] s(z)`. Following QuantumZipper's
`Thm11/ExtMeas*` (ρ = 0), the filter is replaced by countable devices:

* **path space** (`measurableSet_fwdHull_pathProd`, `measurable_fwdMap_alivePath`): the hull and the forward map at
  a fixed time are jointly measurable in the point and the driver path in `C([0, s])`, through QuantumZipper's
  tamed flow;
* **alive pairs** (`aliveProd`, `measurable_meanAtInd`): composing with the driver path map of the landed
  `Ito.drvPathMap`, the mean `η_d(z)` on the pairs alive at time `d` is `Borel(ℂ) ⊗ 𝓖_d`-measurable;
* **the grid** (`gridIdx`, `meanGrid`, `tendsto_meanGrid`): the last dyadic time of level `n` before `t ∧ σ₀` at which
  `z` is alive (`Nat.findGreatest`) tends to `t ∧ σ₀ ∧ s(z)`, strictly below `s(z)` when `z` is swallowed; the means
  there converge to the frozen mean whenever the left limit at `s(z)` exists;
* **the guard** (`guardG`, `guardG_iff`): a countable oscillation condition over rational windows, measurable, which
  holds exactly when the left limit exists (QuantumZipper's `MeasLimit.tendsto_iff_ratOsc`);
* **the version** (`frozenMeanVersion`): the grid limit clamped to `[−M, M]`; it equals the frozen mean at every time
  on the measurable set of good pairs (`frozenMeanVersion_eq`), which has full measure in `ω` for each `z` by the
  landed left-limit theorem `exists_martingale_frozenMean`, hence (Fubini) for almost every `z` almost surely.

Main result: **`exists_frozenMean_version`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace WangWu

section PathSpace

/-- Restriction of a path on `[0, s]` to `[0, r]`, `r ≤ s`. -/
def restrictIcc {r s : ℝ} (hrs : r ≤ s) (g : C(Icc (0 : ℝ) s, ℝ)) : C(Icc (0 : ℝ) r, ℝ) :=
  g.comp ⟨Set.inclusion (Icc_subset_Icc_right hrs), continuous_inclusion _⟩

theorem continuous_restrictIcc {r s : ℝ} (hrs : r ≤ s) : Continuous (restrictIcc hrs) :=
  ContinuousMap.continuous_precomp _

theorem extIccPath_restrictIcc {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (g : C(Icc (0 : ℝ) s, ℝ)) :
    ∀ x ∈ Icc (0 : ℝ) r, extIccPath (hr.trans hrs) g x = extIccPath hr (restrictIcc hrs g) x := by
  intro x hx
  rw [extIccPath_of_mem _ _ ⟨hx.1, hx.2.trans hrs⟩, extIccPath_of_mem _ _ hx]
  rfl

/-- Joint continuity of the tamed flow at an intermediate time `r ≤ s`, in the start point and the path. -/
theorem continuous_tamedZ_pathProd {s r c : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (hrs : r ≤ s) (hc : 0 < c) :
    Continuous fun p : ℂ × C(Icc (0 : ℝ) s, ℝ) => tamedZ (extIccPath hs p.2) c p.1 r := by
  have h := (continuous_tamed_path hc hr).1.comp
    (continuous_fst.prodMk ((continuous_restrictIcc hrs).comp continuous_snd))
  refine h.congr fun p => ?_
  exact (tamedZ_congr_drive (continuous_extIccPath hs _) (continuous_extIccPath hr _) hc hr p.1
    (extIccPath_restrictIcc hr hrs p.2)).symm

variable {s : ℝ} [MeasurableSpace C(Icc (0 : ℝ) s, ℝ)] [BorelSpace C(Icc (0 : ℝ) s, ℝ)]

/-- The hull at time `s` is jointly measurable in the point and the path. -/
theorem measurableSet_fwdHull_pathProd (hs : 0 ≤ s) :
    MeasurableSet {p : ℂ × C(Icc (0 : ℝ) s, ℝ) | p.1 ∈ fwdHull (extIccPath hs p.2) s} := by
  have e : {p : ℂ × C(Icc (0 : ℝ) s, ℝ) | p.1 ∈ fwdHull (extIccPath hs p.2) s} = {p | 0 < p.1.im} ∩
      ⋂ k : ℕ, ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ s),
        {p | (tamedZ (extIccPath hs p.2) (1 / ((k : ℝ) + 1)) p.1 q).im < 2 * (1 / ((k : ℝ) + 1))} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, exists_prop,
      NonSwallow.mem_fwdHull_iff_tamed (continuous_extIccPath hs p.2) hs, and_assoc]
  rw [e]
  refine (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
      measurableSet_lt (Complex.measurable_im.comp
        (continuous_tamedZ_pathProd hs hq.1 hq.2 (by positivity)).measurable) measurable_const)

/-- The points of `ℍ` not swallowed by time `s` under the path. -/
def alivePath (hs : 0 ≤ s) : Set (ℂ × C(Icc (0 : ℝ) s, ℝ)) :=
  {p | p.1 ∈ H \ fwdHull (extIccPath hs p.2) s}

theorem measurableSet_alivePath (hs : 0 ≤ s) : MeasurableSet (alivePath hs) := by
  have e : alivePath hs = {p : ℂ × C(Icc (0 : ℝ) s, ℝ) | 0 < p.1.im} \
      {p | p.1 ∈ fwdHull (extIccPath hs p.2) s} := by
    ext p; exact Iff.rfl
  rw [e]
  exact (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).diff
    (measurableSet_fwdHull_pathProd hs)

/-- The forward map at time `s`, on the alive set, is jointly measurable in the point and the path. -/
theorem measurable_fwdMap_alivePath (hs : 0 ≤ s) :
    Measurable ((alivePath hs).indicator fun p => fwdMap (extIccPath hs p.2) s p.1) := by
  refine measurable_of_tendsto_metrizable (f := fun k : ℕ => (alivePath hs).indicator
    fun p => tamedZ (extIccPath hs p.2) (1 / ((k : ℝ) + 1)) p.1 s) (fun k => ?_) ?_
  · exact (continuous_tamedZ_pathProd hs hs le_rfl (by positivity)).measurable.indicator
      (measurableSet_alivePath hs)
  · rw [tendsto_pi_nhds]
    intro p
    by_cases hp : p ∈ alivePath hs
    · simp only [indicator_of_mem hp]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Thm11Asm.MeasTamed.eventually_tamed_eq_at (continuous_extIccPath hs p.2)
        hp.1 hs hp.2] with k hk
      rw [hk.1]
    · simp only [indicator_of_notMem hp]
      exact tendsto_const_nhds

end PathSpace

/-! ### Alive pairs of a process -/

section Omega

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- The pairs `(z, ω)` with `z ∈ ℍ`, `ω ∈ G`, `d < ζ(ω)` and `z` not swallowed by time `d`. -/
def aliveProd (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (d : ℝ≥0) : Set (ℂ × Ω) :=
  {p | p.1 ∈ H ∧ p.2 ∈ Ito.aliveSet W ζ G p.1 d}

theorem aliveProd_eq (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (d : ℝ≥0) :
    aliveProd W ζ G d = {p : ℂ × Ω | p.2 ∈ G ∧ (d : ℝ≥0∞) < ζ p.2} ∩
      (fun p : ℂ × Ω => (p.1, Ito.drvPathMap W ζ G hGc d p.2)) ⁻¹' alivePath d.coe_nonneg := by
  ext ⟨z, ω⟩
  simp only [aliveProd, Ito.aliveSet, mem_ofPred_eq, mem_inter_iff, mem_preimage, alivePath]
  constructor
  · rintro ⟨hz, hG, hd, u, hu⟩
    have hu' := (Ito.isForwardSol_iff_of_eqOn (Ito.extIccPath_drvPathMap_eqOn hGc ⟨hG, hd⟩) u).2 hu
    exact ⟨⟨hG, hd⟩, hz, Ito.notMem_fwdHull_of_isForwardSol (continuous_extIccPath _ _) hz
      d.coe_nonneg hu'⟩
  · rintro ⟨⟨hG, hd⟩, hz, hK⟩
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull d.coe_nonneg hz hK
    exact ⟨hz, hG, hd, u,
      (Ito.isForwardSol_iff_of_eqOn (Ito.extIccPath_drvPathMap_eqOn hGc ⟨hG, hd⟩) u).1 hu⟩

theorem measurable_pair_drvPathMap (hW : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) (d : ℝ≥0) :
    @Measurable (ℂ × Ω) (ℂ × C(Icc (0 : ℝ) d, ℝ)) ((borel ℂ).prod (𝓖 d))
      (@Prod.instMeasurableSpace ℂ _ _ (borel _))
      (fun p : ℂ × Ω => (p.1, Ito.drvPathMap W ζ G hGc d p.2)) := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) d, ℝ) := borel _
  exact (@measurable_fst ℂ Ω (borel ℂ) (𝓖 d)).prodMk
    ((Ito.measurable_drvPathMap hW hGc hG d).comp (@measurable_snd ℂ Ω (borel ℂ) (𝓖 d)))

theorem measurableSet_aliveProd (hW : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) (d : ℝ≥0) :
    MeasurableSet[(borel ℂ).prod (𝓖 d)] (aliveProd W ζ G d) := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) d, ℝ) := borel _
  have _ : BorelSpace C(Icc (0 : ℝ) d, ℝ) := ⟨rfl⟩
  have hev : MeasurableSet[𝓖 d] {ω | ω ∈ G ∧ (d : ℝ≥0∞) < ζ ω} := by
    have h1 := hW d univ MeasurableSet.univ
    simp only [mem_univ, and_true] at h1
    exact (𝓖.mono (bot_le : (0 : ℝ≥0) ≤ d) _ hG).inter h1
  rw [aliveProd_eq hGc d]
  exact (hev.preimage (@measurable_snd ℂ Ω (borel ℂ) (𝓖 d))).inter
    (measurable_pair_drvPathMap hW hGc hG d (measurableSet_alivePath d.coe_nonneg))


/-! ### The mean on the alive pairs -/

variable {nL nR : ℕ}

theorem measurable_condMean (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Measurable fun q : (Fin nL → ℝ) × (Fin nR → ℝ) × ℂ => condMean ρL ρR q.1 q.2.1 q.2.2 := by
  unfold condMean
  refine (measurable_const.sub (Complex.measurable_arg.comp
    (measurable_snd.comp measurable_snd))).sub (measurable_const.mul ?_)
  refine (Finset.measurable_sum _ fun i _ => measurable_const.mul (Complex.measurable_arg.comp
    ((measurable_snd.comp measurable_snd).sub (Complex.measurable_ofReal.comp
      ((measurable_pi_apply i).comp measurable_fst))))).add
    (Finset.measurable_sum _ fun i _ => measurable_const.mul (Complex.measurable_arg.comp
      ((measurable_snd.comp measurable_snd).sub (Complex.measurable_ofReal.comp
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))))))

/-- The mean `η_d(z)` on the alive pairs at the time `d`, `0` elsewhere. -/
def meanAtInd (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (d : ℝ≥0) (p : ℂ × Ω) : ℝ :=
  if p ∈ aliveProd W ζ G d then
    meanAt ρL ρR (W · p.2) (fun i => (VL i · p.2)) (fun i => (VR i · p.2)) d p.1
  else 0

theorem measurable_meanAtInd (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) (d : ℝ≥0) :
    Measurable[(borel ℂ).prod (𝓖 d)] (meanAtInd ρL ρR W VL VR ζ G d) := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) d, ℝ) := borel _
  have _ : BorelSpace C(Icc (0 : ℝ) d, ℝ) := ⟨rfl⟩
  set m : MeasurableSpace (ℂ × Ω) := (borel ℂ).prod (𝓖 d) with hm
  have hk : ∀ X : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓖 ζ X →
      Measurable[m] fun p : ℂ × Ω => Girsanov.killed ζ X d p.2 := fun X hX =>
    (Girsanov.measurable_killed hX d).comp (@measurable_snd ℂ Ω (borel ℂ) (𝓖 d))
  have hf : Measurable[m] fun p : ℂ × Ω => (alivePath d.coe_nonneg).indicator
      (fun q => fwdMap (extIccPath d.coe_nonneg q.2) d q.1) (p.1, Ito.drvPathMap W ζ G hGc d p.2) :=
    (measurable_fwdMap_alivePath d.coe_nonneg).comp (measurable_pair_drvPathMap hW hGc hG d)
  have hF : Measurable[m] fun p : ℂ × Ω => condMean ρL ρR
      (fun i => Girsanov.killed ζ (VL i) d p.2 - Girsanov.killed ζ W d p.2)
      (fun i => Girsanov.killed ζ (VR i) d p.2 - Girsanov.killed ζ W d p.2)
      ((alivePath d.coe_nonneg).indicator (fun q => fwdMap (extIccPath d.coe_nonneg q.2) d q.1)
        (p.1, Ito.drvPathMap W ζ G hGc d p.2)) := by
    have h1 : Measurable[m] fun p : ℂ × Ω =>
        fun i => Girsanov.killed ζ (VL i) d p.2 - Girsanov.killed ζ W d p.2 :=
      measurable_pi_iff.mpr fun i => (hk _ (hVL i)).sub (hk _ hW)
    have h2 : Measurable[m] fun p : ℂ × Ω =>
        fun i => Girsanov.killed ζ (VR i) d p.2 - Girsanov.killed ζ W d p.2 :=
      measurable_pi_iff.mpr fun i => (hk _ (hVR i)).sub (hk _ hW)
    exact (measurable_condMean ρL ρR).comp (h1.prodMk (h2.prodMk hf))
  have e : meanAtInd ρL ρR W VL VR ζ G d = fun p => if p ∈ aliveProd W ζ G d then condMean ρL ρR
      (fun i => Girsanov.killed ζ (VL i) d p.2 - Girsanov.killed ζ W d p.2)
      (fun i => Girsanov.killed ζ (VR i) d p.2 - Girsanov.killed ζ W d p.2)
      ((alivePath d.coe_nonneg).indicator (fun q => fwdMap (extIccPath d.coe_nonneg q.2) d q.1)
        (p.1, Ito.drvPathMap W ζ G hGc d p.2)) else 0 := by
    funext ⟨z, ω⟩
    by_cases hp : (z, ω) ∈ aliveProd W ζ G d
    · simp only [meanAtInd, hp, ↓reduceIte]
      have hmem : (z, Ito.drvPathMap W ζ G hGc d ω) ∈ alivePath d.coe_nonneg := by
        rw [aliveProd_eq hGc d] at hp
        exact hp.2
      obtain ⟨hz, hG', hd, -⟩ := hp
      rw [indicator_of_mem hmem]
      simp only [Girsanov.killed_of_lt hd, meanAt]
      rw [Ito.fwdMap_congr_of_eqOn (Ito.extIccPath_drvPathMap_eqOn hGc ⟨hG', hd⟩)]
    · simp only [meanAtInd, hp, ↓reduceIte]
  rw [e]
  exact Measurable.ite (measurableSet_aliveProd hW hGc hG d) hF measurable_const


theorem prod_le_prod_filtration {a b : ℝ≥0} (hab : a ≤ b) :
    (borel ℂ).prod (𝓖 a) ≤ (borel ℂ).prod (𝓖 b) :=
  sup_le_sup_left (MeasurableSpace.comap_mono (𝓖.mono hab)) _

end Omega

/-! ### The dyadic grid -/

/-- The level-`n` dyadic grid time `k / 2^n`. -/
def gridT (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

theorem gridT_le {n k : ℕ} {t : ℝ≥0} (hk : k ≤ ⌊(2 : ℝ≥0) ^ n * t⌋₊) : gridT n k ≤ t := by
  unfold gridT
  rw [div_le_iff₀ (pow_pos (by norm_num) n), mul_comm]
  exact (Nat.cast_le.2 hk).trans (Nat.floor_le (by positivity))

theorem gridT_floor_le (n : ℕ) (r : ℝ≥0) : gridT n ⌊(2 : ℝ≥0) ^ n * r⌋₊ ≤ r :=
  gridT_le le_rfl

theorem sub_lt_gridT_floor (n : ℕ) (r : ℝ≥0) :
    (r : ℝ) - 1 / 2 ^ n < (gridT n ⌊(2 : ℝ≥0) ^ n * r⌋₊ : ℝ) := by
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hlt := Nat.lt_floor_add_one ((2 : ℝ≥0) ^ n * r)
  have hlt' : (2 : ℝ) ^ n * r < (⌊(2 : ℝ≥0) ^ n * r⌋₊ : ℝ) + 1 := by exact_mod_cast hlt
  unfold gridT
  push_cast
  rw [lt_div_iff₀ h2, sub_mul, div_mul_cancel₀ _ h2.ne']
  linarith [mul_comm ((2 : ℝ) ^ n) r]

section Grid

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {nL nR : ℕ}

/-- The last level-`n` grid time `≤ t ∧ σ₀` at which `z` is alive (index). -/
def gridIdx (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (σ₀ : Ω → ℝ≥0) (t : ℝ≥0) (n : ℕ)
    (p : ℂ × Ω) : ℕ :=
  Nat.findGreatest (fun k => p ∈ aliveProd W ζ G (gridT n k) ∧ gridT n k ≤ σ₀ p.2)
    ⌊(2 : ℝ≥0) ^ n * t⌋₊

/-- The mean at the last alive level-`n` grid time `≤ t ∧ σ₀`. -/
def meanGrid (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (σ₀ : Ω → ℝ≥0) (t : ℝ≥0) (n : ℕ)
    (p : ℂ × Ω) : ℝ :=
  meanAtInd ρL ρR W VL VR ζ G (gridT n (gridIdx W ζ G σ₀ t n p)) p

theorem measurableSet_gridPred (hW : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime 𝓖 fun ω => (σ₀ ω : WithTop ℝ≥0)) {t : ℝ≥0} {n k : ℕ}
    (hk : k ≤ ⌊(2 : ℝ≥0) ^ n * t⌋₊) :
    MeasurableSet[(borel ℂ).prod (𝓖 t)]
      {p : ℂ × Ω | p ∈ aliveProd W ζ G (gridT n k) ∧ gridT n k ≤ σ₀ p.2} := by
  have hle := prod_le_prod_filtration (𝓖 := 𝓖) (gridT_le hk)
  have h1 : MeasurableSet[𝓖 (gridT n k)] {ω | (σ₀ ω : WithTop ℝ≥0) < (gridT n k : WithTop ℝ≥0)} :=
    hσ₀.measurableSet_lt _
  have e : {p : ℂ × Ω | p ∈ aliveProd W ζ G (gridT n k) ∧ gridT n k ≤ σ₀ p.2} =
      aliveProd W ζ G (gridT n k) ∩
        Prod.snd ⁻¹' {ω | (σ₀ ω : WithTop ℝ≥0) < (gridT n k : WithTop ℝ≥0)}ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, WithTop.coe_lt_coe,
      not_lt]
  rw [e]
  exact (hle _ (measurableSet_aliveProd hW hGc hG _)).inter
    (hle _ (h1.compl.preimage (@measurable_snd ℂ Ω (borel ℂ) (𝓖 _))))

theorem measurable_gridIdx (hW : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime 𝓖 fun ω => (σ₀ ω : WithTop ℝ≥0)) (t : ℝ≥0) (n : ℕ) :
    Measurable[(borel ℂ).prod (𝓖 t)] (gridIdx W ζ G σ₀ t n) :=
  @measurable_findGreatest (ℂ × Ω) ((borel ℂ).prod (𝓖 t)) _ _ _ fun _ hk =>
    measurableSet_gridPred hW hGc hG hσ₀ hk

theorem gridIdx_le (σ₀ : Ω → ℝ≥0) (t : ℝ≥0) (n : ℕ) (p : ℂ × Ω) :
    gridIdx W ζ G σ₀ t n p ≤ ⌊(2 : ℝ≥0) ^ n * t⌋₊ :=
  Nat.findGreatest_le _

theorem measurable_meanGrid (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime 𝓖 fun ω => (σ₀ ω : WithTop ℝ≥0)) (t : ℝ≥0) (n : ℕ) :
    Measurable[(borel ℂ).prod (𝓖 t)] (meanGrid ρL ρR W VL VR ζ G σ₀ t n) := by
  set N := ⌊(2 : ℝ≥0) ^ n * t⌋₊
  set F : ℂ × Ω → ℕ → ℝ := fun p k => if k ≤ N then meanAtInd ρL ρR W VL VR ζ G (gridT n k) p
    else 0 with hF
  have hFm : ∀ k, Measurable[(borel ℂ).prod (𝓖 t)] fun p => F p k := fun k => by
    by_cases hk : k ≤ N
    · simp only [hF, hk, ↓reduceIte]
      exact (measurable_meanAtInd ρL ρR hW hVL hVR hGc hG _).mono
        (prod_le_prod_filtration (gridT_le hk)) le_rfl
    · simp only [hF, hk, ↓reduceIte]
      exact measurable_const
  have e : meanGrid ρL ρR W VL VR ζ G σ₀ t n = fun p => F p (gridIdx W ζ G σ₀ t n p) := by
    funext p
    simp only [hF, meanGrid]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (gridIdx_le σ₀ t n p))]
  rw [e]
  exact @Ito.measurable_comp_index (ℂ × Ω) ℝ ((borel ℂ).prod (𝓖 t)) _ F hFm _
    (measurable_gridIdx hW hGc hG hσ₀ t n)


end Grid

/-! ### Convergence along the grid -/

theorem gridT_mono (n : ℕ) {k k' : ℕ} (h : k ≤ k') : gridT n k ≤ gridT n k' := by
  unfold gridT
  exact div_le_div_of_nonneg_right (Nat.cast_le.2 h) (by positivity)

/-- A point of `ℍ` has a forward solution on `[0, 0]`. -/
theorem exists_isForwardSol_zero (w : ℝ → ℝ) {z : ℂ} (hz : 0 < z.im) :
    ∃ u, IsForwardSol w z 0 u := by
  refine ⟨fun _ => z - (w 0 : ℂ), continuousOn_const, fun t ht => ?_⟩
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  subst ht0
  refine ⟨fun h => ?_, by simp⟩
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at this
  linarith

section Converge

variable {nL nR : ℕ} {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {ω : Ω}

theorem mem_aliveProd_iff
    (hP : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω)) (hω : ω ∈ G) {z : ℂ} (hz : z ∈ H) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ ω) :
    (z, ω) ∈ aliveProd W ζ G r ↔ (r : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) z := by
  constructor
  · rintro ⟨-, -, -, hsol⟩
    exact lt_swallowTime_of_path hP hr hz hsol
  · intro h
    refine ⟨hz, hω, hr, exists_isForwardSol_of_not_mem_fwdHull r.coe_nonneg hz fun hK => ?_⟩
    have h2 := hK.2
    rw [ENNReal.ofReal_coe_nnreal] at h2
    exact (not_le.2 h) h2

theorem tendsto_one_half_pow_sub (x : ℝ) :
    Tendsto (fun n : ℕ => x - 1 / 2 ^ n) atTop (𝓝 x) := by
  have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have := (tendsto_const_nhds (x := x)).sub h
  rw [sub_zero] at this
  refine this.congr fun n => ?_
  rw [one_div_pow]

/-- **Convergence along the grid.** On a good path, the means at the last alive grid times `≤ t ∧ σ₀` converge to
the frozen mean at `t ∧ σ₀`, provided the left limit at the swallowing time exists when `z` is swallowed by `σ₀`. -/
theorem tendsto_meanGrid
    (hP : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω)) (hω : ω ∈ G) {σ₀ : Ω → ℝ≥0} (hσζ : (σ₀ ω : ℝ≥0∞) < ζ ω) {z : ℂ} (hz : z ∈ H)
    (hlim : swallowTime (Ito.rpath (W · ω)) z ≤ σ₀ ω →
      Tendsto (fun r => meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z)
        (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal)
        (𝓝 (frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z)))
    (t : ℝ≥0) :
    Tendsto (fun n => meanGrid ρL ρR W VL VR ζ G σ₀ t n (z, ω)) atTop
      (𝓝 (frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z)) := by
  set s := swallowTime (Ito.rpath (W · ω)) z with hsdef
  set u := min t (σ₀ ω) with hudef
  set η : ℝ≥0 → ℝ := fun r =>
    meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z with hηdef
  set d : ℕ → ℝ≥0 := fun n => gridT n (gridIdx W ζ G σ₀ t n (z, ω)) with hddef
  have hu : u ≤ σ₀ ω := min_le_right _ _
  have huζ : (u : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hu) hσζ
  have hP0 : ∀ n, (z, ω) ∈ aliveProd W ζ G (gridT n 0) ∧ gridT n 0 ≤ σ₀ ω := fun n => by
    have hg0 : gridT n 0 = 0 := by simp [gridT]
    rw [hg0]
    refine ⟨⟨hz, hω, lt_of_le_of_lt (zero_le) hσζ, ?_⟩, zero_le⟩
    simpa using exists_isForwardSol_zero (Ito.rpath (W · ω)) hz
  have hspec : ∀ n, (z, ω) ∈ aliveProd W ζ G (d n) ∧ d n ≤ σ₀ ω := fun n =>
    Nat.findGreatest_spec (P := fun k => (z, ω) ∈ aliveProd W ζ G (gridT n k) ∧ gridT n k ≤ σ₀ ω)
      (Nat.zero_le _) (hP0 n)
  have hd_le : ∀ n, d n ≤ u := fun n => le_min (gridT_le (gridIdx_le σ₀ t n _)) (hspec n).2
  have hgrid : ∀ n, meanGrid ρL ρR W VL VR ζ G σ₀ t n (z, ω) = η (d n) := fun n => by
    simp only [meanGrid, meanAtInd, hηdef]
    rw [ite_eq_left (hspec n).1]
  -- the lower bound
  have hlow : ∀ r : ℝ≥0, r ≤ u → (z, ω) ∈ aliveProd W ζ G r → ∀ n, (r : ℝ) - 1 / 2 ^ n < d n := by
    intro r hr hra n
    have hk : ⌊(2 : ℝ≥0) ^ n * r⌋₊ ≤ ⌊(2 : ℝ≥0) ^ n * t⌋₊ :=
      Nat.floor_mono (mul_le_mul_right (hr.trans (min_le_left _ _)) _)
    have hPk : (z, ω) ∈ aliveProd W ζ G (gridT n ⌊(2 : ℝ≥0) ^ n * r⌋₊) ∧
        gridT n ⌊(2 : ℝ≥0) ^ n * r⌋₊ ≤ σ₀ ω := by
      have hle : gridT n ⌊(2 : ℝ≥0) ^ n * r⌋₊ ≤ r := gridT_floor_le n r
      exact ⟨⟨hra.1, Ito.aliveSet_mono hle hra.2⟩, (hle.trans hr).trans hu⟩
    have hle := Nat.le_findGreatest
      (P := fun k => (z, ω) ∈ aliveProd W ζ G (gridT n k) ∧ gridT n k ≤ σ₀ ω) hk hPk
    calc (r : ℝ) - 1 / 2 ^ n < gridT n ⌊(2 : ℝ≥0) ^ n * r⌋₊ := sub_lt_gridT_floor n r
      _ ≤ d n := NNReal.coe_le_coe.2 (gridT_mono n hle)
  simp_rw [hgrid]
  by_cases hA : (u : ℝ≥0∞) < s
  · -- `z` is alive at `u`: continuity of the mean
    have hua : (z, ω) ∈ aliveProd W ζ G u := (mem_aliveProd_iff hP hω hz huζ).2 hA
    have hdu : Tendsto (fun n => (d n : ℝ)) atTop (𝓝 (u : ℝ)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_one_half_pow_sub (u : ℝ))
        tendsto_const_nhds (fun n => (hlow u le_rfl hua n).le) fun n => by exact_mod_cast hd_le n
    have hdu' : Tendsto d atTop (𝓝[Icc 0 u] u) :=
      tendsto_nhdsWithin_iff.2 ⟨NNReal.tendsto_coe.1 hdu,
        Eventually.of_forall fun n => ⟨zero_le, hd_le n⟩⟩
    have hcont := continuousOn_meanAt (ρL := ρL) (ρR := ρR) hP huζ hz hua.2.2.2 u ⟨zero_le, le_rfl⟩
    have hfr : frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) u z = η u := by
      simp only [frozenMean, hηdef]
      rw [ite_eq_left hA]
    rw [hfr]
    exact hcont.tendsto.comp hdu'
  · -- `z` is swallowed by `u`: the left limit
    have hsu : s ≤ u := not_lt.1 hA
    have hsσ : s ≤ σ₀ ω := hsu.trans (by exact_mod_cast hu)
    have hsT : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hsu
    set S := s.toNNReal with hSdef
    have hSs : (S : ℝ≥0∞) = s := ENNReal.coe_toNNReal hsT
    have hdS : ∀ n, d n < S := fun n => by
      have hdζ : (d n : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hd_le n) huζ
      have h1 := (mem_aliveProd_iff hP hω hz hdζ).1 (hspec n).1
      have h2 : (d n : ℝ≥0∞) < (S : ℝ≥0∞) := by rw [hSs]; exact h1
      exact_mod_cast h2
    have hconv : Tendsto d atTop (𝓝 S) := by
      refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => Eventually.of_forall fun n => (hdS n).trans hb⟩
      obtain ⟨r, har, hrS⟩ := exists_between ha
      have hrs : (r : ℝ≥0∞) < s := by rw [← hSs]; exact_mod_cast hrS
      have hru : r ≤ u := by
        have : (r : ℝ≥0∞) ≤ u := hrs.le.trans hsu
        exact_mod_cast this
      have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hru) huζ
      have hra : (z, ω) ∈ aliveProd W ζ G r := (mem_aliveProd_iff hP hω hz hrζ).2 hrs
      have hev : ∀ᶠ n in atTop, (a : ℝ) < (r : ℝ) - 1 / 2 ^ n :=
        (tendsto_one_half_pow_sub (r : ℝ)).eventually (lt_mem_nhds (by exact_mod_cast har))
      filter_upwards [hev] with n hn
      have := hn.trans (hlow r hru hra n)
      exact_mod_cast this
    have hdS' : Tendsto d atTop (𝓝[<] S) :=
      tendsto_nhdsWithin_iff.2 ⟨hconv, Eventually.of_forall hdS⟩
    have hfr : frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) u z =
        frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z := by
      simp only [frozenMean]
      rw [ite_eq_right_iff.2 fun h => absurd h (not_lt.2 hsu),
        ite_eq_right_iff.2 fun h => absurd h (not_lt.2 hsσ)]
    rw [hfr]
    exact (hlim hsσ).comp hdS'


end Converge

/-! ### The guard: a countable criterion for the left limit -/

section Guard

variable {nL nR : ℕ} {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The window `[s − 1/(m+1), s)` before the swallowing time `s`, read through aliveness at `r` and `r + 1/(m+1)`. -/
def winG (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (m : ℕ) (r : ℝ≥0) (p : ℂ × Ω) : Prop :=
  p ∈ aliveProd W ζ G r ∧ p ∉ aliveProd W ζ G (r + (1 / ((m : ℝ) + 1)).toNNReal)

/-- The oscillation of the mean over the rational times of the window is at most `1/(n+1)`. -/
def oscG (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (m n : ℕ) (p : ℂ × Ω) : Prop :=
  ∀ q q' : ℚ, (0 : ℝ) ≤ q → winG W ζ G m (q : ℝ).toNNReal p → (0 : ℝ) ≤ q' →
    winG W ζ G m (q' : ℝ).toNNReal p →
      |meanAtInd ρL ρR W VL VR ζ G (q : ℝ).toNNReal p -
        meanAtInd ρL ρR W VL VR ζ G (q' : ℝ).toNNReal p| ≤ 1 / ((n : ℝ) + 1)

/-- **The guard**: for every `n` some window has oscillation at most `1/(n+1)`. -/
def guardG (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (p : ℂ × Ω) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, oscG ρL ρR W VL VR ζ G m n p

theorem measurableSet_guardG {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) :
    MeasurableSet[(borel ℂ).prod mΩ] {p : ℂ × Ω | guardG ρL ρR W VL VR ζ G p} := by
  have hle : ∀ d : ℝ≥0, (borel ℂ).prod (𝓖 d) ≤ (borel ℂ).prod mΩ := fun d =>
    sup_le_sup_left (MeasurableSpace.comap_mono (𝓖.le d)) _
  have hA : ∀ d : ℝ≥0, MeasurableSet[(borel ℂ).prod mΩ] (aliveProd W ζ G d) := fun d =>
    hle d _ (measurableSet_aliveProd hW hGc hG d)
  have hM : ∀ d : ℝ≥0, Measurable[(borel ℂ).prod mΩ] (meanAtInd ρL ρR W VL VR ζ G d) := fun d =>
    (measurable_meanAtInd ρL ρR hW hVL hVR hGc hG d).mono (hle d) le_rfl
  have hwin : ∀ m (r : ℝ≥0), MeasurableSet[(borel ℂ).prod mΩ] {p : ℂ × Ω | winG W ζ G m r p} :=
    fun m r => (hA r).inter (hA _).compl
  have hosc : ∀ m n, MeasurableSet[(borel ℂ).prod mΩ] {p : ℂ × Ω | oscG ρL ρR W VL VR ζ G m n p} := by
    intro m n
    have e : {p : ℂ × Ω | oscG ρL ρR W VL VR ζ G m n p} = ⋂ q : ℚ, ⋂ q' : ℚ,
        {p : ℂ × Ω | (0 : ℝ) ≤ q → winG W ζ G m (q : ℝ).toNNReal p → (0 : ℝ) ≤ q' →
          winG W ζ G m (q' : ℝ).toNNReal p →
            |meanAtInd ρL ρR W VL VR ζ G (q : ℝ).toNNReal p -
              meanAtInd ρL ρR W VL VR ζ G (q' : ℝ).toNNReal p| ≤ 1 / ((n : ℝ) + 1)} := by
      ext p; simp only [oscG, mem_iInter, mem_ofPred_eq]
    rw [e]
    refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun q' => ?_
    have h3 : MeasurableSet[(borel ℂ).prod mΩ] {p : ℂ × Ω |
        |meanAtInd ρL ρR W VL VR ζ G (q : ℝ).toNNReal p -
          meanAtInd ρL ρR W VL VR ζ G (q' : ℝ).toNNReal p| ≤ 1 / ((n : ℝ) + 1)} :=
      measurableSet_le (((hM _).sub (hM _)).abs) measurable_const
    by_cases hq : (0 : ℝ) ≤ q
    · by_cases hq' : (0 : ℝ) ≤ q'
      · have e2 : {p : ℂ × Ω | (0 : ℝ) ≤ q → winG W ζ G m (q : ℝ).toNNReal p → (0 : ℝ) ≤ q' →
            winG W ζ G m (q' : ℝ).toNNReal p →
              |meanAtInd ρL ρR W VL VR ζ G (q : ℝ).toNNReal p -
                meanAtInd ρL ρR W VL VR ζ G (q' : ℝ).toNNReal p| ≤ 1 / ((n : ℝ) + 1)} =
            {p | winG W ζ G m (q : ℝ).toNNReal p}ᶜ ∪ ({p | winG W ζ G m (q' : ℝ).toNNReal p}ᶜ ∪
              {p : ℂ × Ω | |meanAtInd ρL ρR W VL VR ζ G (q : ℝ).toNNReal p -
                meanAtInd ρL ρR W VL VR ζ G (q' : ℝ).toNNReal p| ≤ 1 / ((n : ℝ) + 1)}) := by
          ext p
          simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
          tauto
        rw [e2]
        exact (hwin m _).compl.union ((hwin m _).compl.union h3)
      · have e2 : {p : ℂ × Ω | (0 : ℝ) ≤ q → winG W ζ G m (q : ℝ).toNNReal p → (0 : ℝ) ≤ q' →
            winG W ζ G m (q' : ℝ).toNNReal p →
              |meanAtInd ρL ρR W VL VR ζ G (q : ℝ).toNNReal p -
                meanAtInd ρL ρR W VL VR ζ G (q' : ℝ).toNNReal p| ≤ 1 / ((n : ℝ) + 1)} = univ := by
          ext p; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact fun _ _ h => absurd h hq'
        rw [e2]; exact MeasurableSet.univ
    · have e2 : {p : ℂ × Ω | (0 : ℝ) ≤ q → winG W ζ G m (q : ℝ).toNNReal p → (0 : ℝ) ≤ q' →
          winG W ζ G m (q' : ℝ).toNNReal p →
            |meanAtInd ρL ρR W VL VR ζ G (q : ℝ).toNNReal p -
              meanAtInd ρL ρR W VL VR ζ G (q' : ℝ).toNNReal p| ≤ 1 / ((n : ℝ) + 1)} = univ := by
        ext p; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact fun h => absurd h hq
      rw [e2]; exact MeasurableSet.univ
  have e : {p : ℂ × Ω | guardG ρL ρR W VL VR ζ G p} =
      ⋂ n : ℕ, ⋃ m : ℕ, {p : ℂ × Ω | oscG ρL ρR W VL VR ζ G m n p} := by
    ext p; simp only [guardG, mem_iInter, mem_iUnion, mem_ofPred_eq]
  rw [e]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m => hosc m n

variable {ω : Ω}

/-- Aliveness on a good path, through the swallowing time. -/
theorem mem_aliveProd_iff_lt
    (hP : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω)) (hω : ω ∈ G) {z : ℂ} (hz : z ∈ H)
    (hsζ : swallowTime (Ito.rpath (W · ω)) z < ζ ω) (r : ℝ≥0) :
    (z, ω) ∈ aliveProd W ζ G r ↔ r < (swallowTime (Ito.rpath (W · ω)) z).toNNReal := by
  have hsT : swallowTime (Ito.rpath (W · ω)) z ≠ ⊤ := ne_top_of_lt hsζ
  have hSs := ENNReal.coe_toNNReal hsT
  by_cases hr : (r : ℝ≥0∞) < ζ ω
  · rw [mem_aliveProd_iff hP hω hz hr, ← ENNReal.coe_lt_coe, hSs]
  · constructor
    · rintro ⟨-, -, h, -⟩; exact absurd h hr
    · intro h
      have h1 : (r : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) z := by
        rw [← hSs]; exact_mod_cast h
      exact absurd (h1.trans hsζ) hr

/-- **The guard detects the left limit** at the swallowing time `s < ζ`. -/
theorem guardG_iff
    (hP : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω)) (hω : ω ∈ G) {z : ℂ} (hz : z ∈ H)
    (hsζ : swallowTime (Ito.rpath (W · ω)) z < ζ ω) :
    guardG ρL ρR W VL VR ζ G (z, ω) ↔ ∃ L, Tendsto
      (fun r => meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z)
      (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal) (𝓝 L) := by
  set S := (swallowTime (Ito.rpath (W · ω)) z).toNNReal with hSdef
  set η : ℝ≥0 → ℝ := fun r =>
    meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z with hηdef
  have halive := mem_aliveProd_iff_lt hP hω hz hsζ (B := B)
  have hζ0 : (0 : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (zero_le) hsζ
  have hS0 : 0 < S := by
    refine (halive 0).1 ⟨hz, hω, by simpa using hζ0, ?_⟩
    simpa using exists_isForwardSol_zero (Ito.rpath (W · ω)) hz
  set τ : ℝ := (S : ℝ) with hτdef
  set f : ℝ → ℝ := fun x => η x.toNNReal with hfdef
  have hτ0 : 0 < τ := by exact_mod_cast hS0
  -- the windows
  have hwin : ∀ (m : ℕ) (q : ℚ), (0 : ℝ) ≤ q → (winG W ζ G m (q : ℝ).toNNReal (z, ω) ↔
      (q : ℝ) < τ ∧ τ - 1 / ((m : ℝ) + 1) ≤ q) := by
    intro m q hq
    have hc : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    unfold winG
    rw [halive, halive, Real.toNNReal_lt_iff_lt_coe hq, not_lt, ← NNReal.coe_le_coe,
      NNReal.coe_add, Real.coe_toNNReal _ hq, Real.coe_toNNReal _ hc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  have hval : ∀ r : ℝ≥0, r < S → meanAtInd ρL ρR W VL VR ζ G r (z, ω) = η r := fun r hr => by
    simp only [meanAtInd, hηdef]
    rw [ite_eq_left ((halive r).2 hr)]
  have hosc : ∀ m n, oscG ρL ρR W VL VR ζ G m n (z, ω) ↔ Thm11Asm.MeasLimit.RatOsc f τ m n := by
    intro m n
    unfold oscG Thm11Asm.MeasLimit.RatOsc
    refine forall₂_congr fun q q' => ?_
    constructor
    · intro h hq hqτ hqw hq' hqτ' hqw'
      have h1 := h hq ((hwin m q hq).2 ⟨hqτ, hqw⟩) hq' ((hwin m q' hq').2 ⟨hqτ', hqw'⟩)
      rwa [hval _ ((Real.toNNReal_lt_iff_lt_coe hq).2 hqτ),
        hval _ ((Real.toNNReal_lt_iff_lt_coe hq').2 hqτ')] at h1
    · intro h hq hw hq' hw'
      obtain ⟨hqτ, hqw⟩ := (hwin m q hq).1 hw
      obtain ⟨hqτ', hqw'⟩ := (hwin m q' hq').1 hw'
      rw [hval _ ((Real.toNNReal_lt_iff_lt_coe hq).2 hqτ),
        hval _ ((Real.toNNReal_lt_iff_lt_coe hq').2 hqτ')]
      exact h hq hqτ hqw hq' hqτ' hqw'
  have hcont : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < τ → ContinuousOn f (Icc a b) := by
    intro a b ha hab hbτ
    have hbS : b.toNNReal < S := (Real.toNNReal_lt_iff_lt_coe (ha.trans hab)).2 hbτ
    have hbζ : (b.toNNReal : ℝ≥0∞) < ζ ω := by
      have h1 : (b.toNNReal : ℝ≥0∞) < (S : ℝ≥0∞) := by exact_mod_cast hbS
      rw [hSdef, ENNReal.coe_toNNReal (ne_top_of_lt hsζ)] at h1
      exact h1.trans hsζ
    have hη := continuousOn_meanAt (ρL := ρL) (ρR := ρR) hP hbζ hz ((halive _).2 hbS).2.2.2
    exact hη.comp continuous_real_toNNReal.continuousOn fun x hx =>
      ⟨zero_le, Real.toNNReal_le_toNNReal hx.2⟩
  have hiff := Thm11Asm.MeasLimit.tendsto_iff_ratOsc hτ0 hcont
  -- filter translation
  have htr : (∃ L, Tendsto f (𝓝[<] τ) (𝓝 L)) ↔ ∃ L, Tendsto η (𝓝[<] S) (𝓝 L) := by
    constructor
    · rintro ⟨L, hL⟩
      refine ⟨L, ?_⟩
      have hc : Tendsto (fun r : ℝ≥0 => (r : ℝ)) (𝓝[<] S) (𝓝[<] τ) :=
        tendsto_nhdsWithin_iff.2 ⟨(NNReal.continuous_coe.tendsto S).mono_left
          nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun r hr => by
            simp only [mem_Iio] at hr ⊢; exact_mod_cast hr⟩
      refine (hL.comp hc).congr fun r => ?_
      simp only [hfdef, Function.comp, Real.toNNReal_coe]
    · rintro ⟨L, hL⟩
      refine ⟨L, hL.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)⟩
      · have h := (continuous_real_toNNReal.tendsto τ).mono_left (nhdsWithin_le_nhds (s := Iio τ))
        rwa [hτdef, Real.toNNReal_coe] at h
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_Iio] at hx ⊢
        rw [← Real.toNNReal_coe (r := S)]
        exact (Real.toNNReal_lt_toNNReal_iff hτ0).2 hx
  rw [← htr, hiff]
  unfold guardG
  exact forall_congr' fun n => exists_congr fun m => hosc m n

end Guard

/-! ### The version -/

/-- Clamping to `[−C, C]`. -/
def clampAbs (C x : ℝ) : ℝ := max (-C) (min C x)

theorem abs_clampAbs_le {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clampAbs C x| ≤ C := by
  unfold clampAbs
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampAbs_of_abs_le {C x : ℝ} (h : |x| ≤ C) : clampAbs C x = x := by
  unfold clampAbs
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem continuous_clampAbs (C : ℝ) : Continuous (clampAbs C) :=
  continuous_const.max (continuous_const.min continuous_id)

section Version

variable {nL nR : ℕ} {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The version of the frozen mean**: the limit of the grid means, clamped to `[−M, M]`. -/
def frozenMeanVersion (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω)
    (σ₀ : Ω → ℝ≥0) (t : ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  clampAbs (meanBound ρL ρR) (limUnder atTop fun n => meanGrid ρL ρR W VL VR ζ G σ₀ t n (z, ω))

theorem abs_frozenMeanVersion_le (σ₀ : Ω → ℝ≥0) (t : ℝ≥0) (z : ℂ) (ω : Ω) :
    |frozenMeanVersion ρL ρR W VL VR ζ G σ₀ t z ω| ≤ meanBound ρL ρR :=
  abs_clampAbs_le (meanBound_nonneg ρL ρR) _

theorem measurable_frozenMeanVersion {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime 𝓖 fun ω => (σ₀ ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[(borel ℂ).prod (𝓖 t)]
      (fun p : ℂ × Ω => frozenMeanVersion ρL ρR W VL VR ζ G σ₀ t p.1 p.2) := by
  have hs := @StronglyMeasurable.limUnder ℕ (ℂ × Ω) ℝ ((borel ℂ).prod (𝓖 t)) _ _ atTop _
    (fun n p => meanGrid ρL ρR W VL VR ζ G σ₀ t n p) _ _
    fun n => (measurable_meanGrid ρL ρR hW hVL hVR hGc hG hσ₀ t n).stronglyMeasurable
  exact (continuous_clampAbs _).measurable.comp hs.measurable

theorem abs_meanAtInd_le (d : ℝ≥0) (p : ℂ × Ω) :
    |meanAtInd ρL ρR W VL VR ζ G d p| ≤ meanBound ρL ρR := by
  unfold meanAtInd
  split_ifs
  · exact abs_condMean_le _ _ _ _ _
  · rw [abs_zero]; exact meanBound_nonneg ρL ρR

/-- The good pairs: a good path, `z ∈ ℍ`, and either `z` alive at a rational time after `σ₀`, or the guard. -/
def goodPair (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (σ₀ : Ω → ℝ≥0) : Set (ℂ × Ω) :=
  {p | p.2 ∈ G ∧ p.1 ∈ H} ∩ ((⋃ q : ℚ, {p | σ₀ p.2 < (q : ℝ).toNNReal} ∩
    aliveProd W ζ G (q : ℝ).toNNReal) ∪ {p | guardG ρL ρR W VL VR ζ G p})

theorem measurableSet_goodPair {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime 𝓖 fun ω => (σ₀ ω : WithTop ℝ≥0)) :
    MeasurableSet[(borel ℂ).prod mΩ] (goodPair ρL ρR W VL VR ζ G σ₀) := by
  have hle : ∀ d : ℝ≥0, (borel ℂ).prod (𝓖 d) ≤ (borel ℂ).prod mΩ := fun d =>
    sup_le_sup_left (MeasurableSpace.comap_mono (𝓖.le d)) _
  have hG' : MeasurableSet[mΩ] G := 𝓖.le 0 _ hG
  have h1 : MeasurableSet[(borel ℂ).prod mΩ] {p : ℂ × Ω | p.2 ∈ G ∧ p.1 ∈ H} :=
    (hG'.preimage (@measurable_snd ℂ Ω (borel ℂ) mΩ)).inter
      (isOpen_H.measurableSet.preimage (@measurable_fst ℂ Ω (borel ℂ) mΩ))
  have h2 : ∀ r : ℝ≥0, MeasurableSet[(borel ℂ).prod mΩ] {p : ℂ × Ω | σ₀ p.2 < r} := fun r => by
    have h := 𝓖.le r _ (hσ₀.measurableSet_lt r)
    have e : {p : ℂ × Ω | σ₀ p.2 < r} =
        Prod.snd ⁻¹' {ω | (σ₀ ω : WithTop ℝ≥0) < (r : WithTop ℝ≥0)} := by
      ext p; simp only [mem_ofPred_eq, mem_preimage, WithTop.coe_lt_coe]
    rw [e]
    exact h.preimage (@measurable_snd ℂ Ω (borel ℂ) mΩ)
  exact h1.inter ((MeasurableSet.iUnion fun q => (h2 _).inter
    (hle _ _ (measurableSet_aliveProd hW hGc hG _))).union (measurableSet_guardG hW hVL hVR hGc hG))

variable {ω : Ω}

/-- On a good pair the version is the frozen mean, at every time. -/
theorem frozenMeanVersion_eq
    (hP : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω)) {σ₀ : Ω → ℝ≥0} (hσζ : (σ₀ ω : ℝ≥0∞) < ζ ω) {z : ℂ}
    (hgood : (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀) (t : ℝ≥0) :
    frozenMeanVersion ρL ρR W VL VR ζ G σ₀ t z ω =
      frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z := by
  obtain ⟨⟨hω, hz⟩, hor⟩ := hgood
  have hlim : swallowTime (Ito.rpath (W · ω)) z ≤ σ₀ ω →
      Tendsto (fun r => meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z)
        (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal)
        (𝓝 (frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z)) := by
    intro hsσ
    have hsζ : swallowTime (Ito.rpath (W · ω)) z < ζ ω := lt_of_le_of_lt hsσ hσζ
    rcases hor with hq | hg
    · exfalso
      obtain ⟨q, hq1, -, -, hqζ, hsol⟩ := mem_iUnion.1 hq
      have h1 := lt_swallowTime_of_path hP hqζ hz hsol
      have h2 : (σ₀ ω : ℝ≥0∞) < ((q : ℝ).toNNReal : ℝ≥0∞) := by exact_mod_cast hq1
      exact absurd (hsσ.trans_lt (h2.trans h1)) (lt_irrefl _)
    · obtain ⟨L, hL⟩ := (guardG_iff hP hω hz hsζ).1 hg
      have he := tendsto_nhds_limUnder ⟨L, hL⟩
      have hfr : frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z =
          limUnder (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal)
            (fun r => meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z) := by
        simp only [frozenMean]
        rw [ite_eq_right_iff.2 fun h => absurd h (not_lt.2 hsσ)]
      rw [hfr]
      exact he
  have ht := tendsto_meanGrid hP hω hσζ hz hlim t
  have hb : |frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z|
      ≤ meanBound ρL ρR :=
    le_of_tendsto ht.abs (Eventually.of_forall fun n => abs_meanAtInd_le _ _)
  unfold frozenMeanVersion
  rw [ht.limUnder_eq, clampAbs_of_abs_le hb]

end Version

/-! ### Lemma 3.5: the jointly measurable version -/

section Main

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Lemma 3.5, a jointly measurable version of the frozen mean** (input M of PROVE-WW-A). For a marked chain
and a bounded stopping time `σ₀ < T` of the usual augmentation, there is `Yv` with `(z, ω) ↦ Yv_t(z, ω)`
measurable for `Borel(ℂ) ⊗ 𝓖_t`, `|Yv| ≤ M`, equal for each `z ∈ ℍ` almost surely (for all `t`) to the frozen mean
`η̄_{t ∧ σ₀}(z)`, and almost surely equal to it for Lebesgue-almost every `z ∈ ℍ` (for all `t`). -/
theorem exists_frozenMean_version [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N) :
    ∃ Yv : ℝ≥0 → ℂ → Ω → ℝ,
      (∀ t, Measurable[(borel ℂ).prod (usualAugmentation 𝓕 P t)]
        (fun p : ℂ × Ω => Yv t p.1 p.2)) ∧
      (∀ t z ω, |Yv t z ω| ≤ meanBound ρL ρR) ∧
      (∀ z ∈ H, ∀ᵐ ω ∂P, ∀ t, Yv t z ω =
        frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z) ∧
      (∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ H → ∀ t, Yv t z ω =
        frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z) := by
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hE' := hE
  obtain ⟨hB, hWa, hVLa, hVRa, hpath⟩ := hE'
  set Gp : Set Ω := {ω | IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω))
    (fun i => (VR i · ω)) (B · ω) (ζ ω) ∧ (σ₀ ω : ℝ≥0∞) < ζ ω} with hGpdef
  have hGp : ∀ᵐ ω ∂P, ω ∈ Gp := by
    filter_upwards [hpath, hσ₀ζ] with ω h1 h2 using ⟨h1, h2⟩
  set G : Set Ω := (toMeasurable P Gpᶜ)ᶜ with hGdef
  have hnull : P (toMeasurable P Gpᶜ) = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.1 hGp
  have hG0 : MeasurableSet[𝓖 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable _ _) hnull 0).compl
  have hGsub : ∀ ω ∈ G, ω ∈ Gp := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    simpa [hGdef] using hω
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGsub ω hω).1.2.2.2.1
  have hW𝓖 : AdaptedBefore 𝓖 ζ W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) hWa
  have hVL𝓖 : ∀ i, AdaptedBefore 𝓖 ζ (VL i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hVLa i)
  have hVR𝓖 : ∀ i, AdaptedBefore 𝓖 ζ (VR i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hVRa i)
  -- for each `z ∈ ℍ`, almost every `(z, ω)` is good
  have hgood : ∀ z ∈ H, ∀ᵐ ω ∂P, (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀ := by
    intro z hz
    obtain ⟨hlim, -⟩ := exists_martingale_frozenMean (ρL := ρL) (ρR := ρR) hE hz hσ₀ hσ₀ζ hσ₀N
    filter_upwards [hlim, hGae] with ω hl hω
    obtain ⟨hP, hσζ⟩ := hGsub ω hω
    refine ⟨⟨hω, hz⟩, ?_⟩
    by_cases hs : (σ₀ ω : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) z
    · left
      obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hs hσζ)
      have hc1' : (σ₀ ω : ℝ) < c := by exact_mod_cast hc1
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hc1'
      have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg _).trans hq1.le
      have hqc : ((q : ℝ).toNNReal : ℝ≥0∞) < c := by
        exact_mod_cast (Real.toNNReal_lt_iff_lt_coe hq0).2 hq2
      have hqm := hqc.trans hc2
      refine mem_iUnion.2 ⟨q, ?_, ?_⟩
      · show σ₀ ω < (q : ℝ).toNNReal
        exact Real.lt_toNNReal_iff_coe_lt.2 hq1
      · exact (mem_aliveProd_iff hP hω hz (hqm.trans_le (min_le_right _ _))).2
          (hqm.trans_le (min_le_left _ _))
    · right
      have hsσ := not_lt.1 hs
      exact (guardG_iff hP hω hz (lt_of_le_of_lt hsσ hσζ)).2 ⟨_, hl hsσ⟩
  refine ⟨frozenMeanVersion ρL ρR W VL VR ζ G σ₀,
    fun t => measurable_frozenMeanVersion hW𝓖 hVL𝓖 hVR𝓖 hGc hG0 hσ₀ t,
    fun t z ω => abs_frozenMeanVersion_le σ₀ t z ω, fun z hz => ?_, ?_⟩
  · filter_upwards [hgood z hz] with ω hω t
    exact frozenMeanVersion_eq (hGsub ω hω.1.1).1 (hGsub ω hω.1.1).2 hω t
  · have hgm := measurableSet_goodPair (ρL := ρL) (ρR := ρR) hW𝓖 hVL𝓖 hVR𝓖 hGc hG0 hσ₀
    have e : {x : ℂ × Ω | x.1 ∈ H → x ∈ goodPair ρL ρR W VL VR ζ G σ₀} =
        (Prod.fst ⁻¹' H)ᶜ ∪ goodPair ρL ρR W VL VR ζ G σ₀ := by
      ext x
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]
      tauto
    have hmeas : MeasurableSet {x : ℂ × Ω | x.1 ∈ H → x ∈ goodPair ρL ρR W VL VR ζ G σ₀} := by
      rw [e]
      exact (isOpen_H.measurableSet.preimage measurable_fst).compl.union hgm
    have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂P, z ∈ H →
        (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀ := Eventually.of_forall fun z => by
      by_cases hz : z ∈ H
      · filter_upwards [hgood z hz] with ω hω _ using hω
      · exact Eventually.of_forall fun ω h => absurd h hz
    have h2 := (Measure.ae_ae_comm (μ := (volume : Measure ℂ)) (ν := P)
      (p := fun z ω => z ∈ H → (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀) hmeas).1 h1
    filter_upwards [h2] with ω hω
    filter_upwards [hω] with z hz hzH t
    have hg := hz hzH
    exact frozenMeanVersion_eq (hGsub ω hg.1.1).1 (hGsub ω hg.1.1).2 hg t

end Main

end WangWu

end InteractingSLE
