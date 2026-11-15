import InteractingSLE.WangWu.CouplingVersion
import QuantumZipper.Proofs.GFF.K3.C5KernelMeas

/-!
# Wang–Wu at `κ = 4`: the integrated covariance identity (Lemma 3.6), unconditionally

Packet PROVE-WW-A3. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, Lemma 3.6 ("`M_t(p) =
∫ p(z)(η_t(z) − η_0(z)) dz` … Conditional Fubini applied to the stopped pointwise martingales gives the martingale
property … Fubini implies that `M_t(p)² + E_t(p)` is a martingale"), ruling R31.

PROVE-WW-A proved the integrated identities conditional on jointly measurable versions
(`martingale_integral_frozenMean_of_version`, `martingale_integral_frozenMean_two_of_version`), and PROVE-WW-A2 the
version of the frozen mean (`exists_frozenMean_version`). This file supplies the version of the retained Green kernel
`G_{U_{t∧σ₀}}(y, z)` and removes the conditions:

* `fwdAtInd`, `measurable_fwdAtInd`: the forward map `f_d(z)` on the pairs alive at time `d`, measurable for
  `Borel(ℂ) ⊗ 𝓖_d`;
* `greenAtInd`, `greenVersionE`: the kernel `G_ℍ(f_r y, f_r z)` at the rational times `r ≤ t ∧ σ₀` at which both
  points are alive, and its infimum, measurable for `Borel(ℂ × ℂ) ⊗ 𝓖_t` (`measurable_greenVersionE`);
* `greenVersionE_eq`: on a good path the infimum is the retained kernel (QuantumZipper's `VTe` is an infimum over
  `ℚ ∪ {t}`, `K3.VTe_eq_iInf_countable`; the time `t` itself is reached by rationals from the left, by continuity
  of `s ↦ G_ℍ(f_s y, f_s z)`);
* **`exists_martingale_testedMean`** and **`exists_martingale_testedMean_sq_add_energy`**: for a bounded stopping
  time `σ₀ < T`, `t ↦ ∫ φ η̄_{t∧σ₀}` and `t ↦ (∫ φ η̄_{t∧σ₀})² + Q_{U_{t∧σ₀}}(φ, φ)` agree almost surely with
  martingales of the usual augmentation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace WangWu

/-! ### The forward map and the Green kernel on alive pairs -/

section GreenVersion

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- The forward map `f_d(z)` read through the driver path map (junk off the alive pairs). -/
def fwdAtInd (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (d : ℝ≥0) (p : ℂ × Ω) : ℂ :=
  (alivePath d.coe_nonneg).indicator (fun q => fwdMap (extIccPath d.coe_nonneg q.2) d q.1)
    (p.1, Ito.drvPathMap W ζ G hGc d p.2)

theorem measurable_fwdAtInd (hW : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) (d : ℝ≥0) :
    Measurable[(borel ℂ).prod (𝓖 d)] (fwdAtInd W ζ G hGc d) := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) d, ℝ) := borel _
  have _ : BorelSpace C(Icc (0 : ℝ) d, ℝ) := ⟨rfl⟩
  exact (measurable_fwdMap_alivePath d.coe_nonneg).comp (measurable_pair_drvPathMap hW hGc hG d)

theorem fwdAtInd_eq (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    {d : ℝ≥0} {p : ℂ × Ω} (hp : p ∈ aliveProd W ζ G d) :
    fwdAtInd W ζ G hGc d p = fwdMap (Ito.rpath (W · p.2)) d p.1 := by
  have hmem : (p.1, Ito.drvPathMap W ζ G hGc d p.2) ∈ alivePath d.coe_nonneg := by
    rw [aliveProd_eq hGc d] at hp
    exact hp.2
  obtain ⟨-, hG', hd, -⟩ := hp
  unfold fwdAtInd
  rw [indicator_of_mem hmem]
  exact Ito.fwdMap_congr_of_eqOn (Ito.extIccPath_drvPathMap_eqOn hGc ⟨hG', hd⟩)

/-- `G_ℍ(f_d y, f_d z)` on the pairs `(y, z)` both alive at time `d`, `⊤` elsewhere. -/
def greenAtInd (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (d : ℝ≥0) (q : (ℂ × ℂ) × Ω) :
    ℝ≥0∞ :=
  if (q.1.1, q.2) ∈ aliveProd W ζ G d ∧ (q.1.2, q.2) ∈ aliveProd W ζ G d then
    ENNReal.ofReal (greenH (fwdMap (Ito.rpath (W · q.2)) d q.1.1)
      (fwdMap (Ito.rpath (W · q.2)) d q.1.2))
  else ⊤

theorem measurable_greenAtInd (hW : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) (d : ℝ≥0) :
    Measurable[MeasurableSpace.prod inferInstance (𝓖 d)] (greenAtInd W ζ G d) := by
  set m : MeasurableSpace ((ℂ × ℂ) × Ω) := MeasurableSpace.prod inferInstance (𝓖 d) with hm
  have h1 : @Measurable ((ℂ × ℂ) × Ω) (ℂ × Ω) m ((borel ℂ).prod (𝓖 d)) fun q => (q.1.1, q.2) :=
    (measurable_fst.comp (@measurable_fst (ℂ × ℂ) Ω inferInstance (𝓖 d))).prodMk
      (@measurable_snd (ℂ × ℂ) Ω inferInstance (𝓖 d))
  have h2 : @Measurable ((ℂ × ℂ) × Ω) (ℂ × Ω) m ((borel ℂ).prod (𝓖 d)) fun q => (q.1.2, q.2) :=
    (measurable_snd.comp (@measurable_fst (ℂ × ℂ) Ω inferInstance (𝓖 d))).prodMk
      (@measurable_snd (ℂ × ℂ) Ω inferInstance (𝓖 d))
  have hA := measurableSet_aliveProd hW hGc hG d
  have hS : MeasurableSet[m] {q : (ℂ × ℂ) × Ω |
      (q.1.1, q.2) ∈ aliveProd W ζ G d ∧ (q.1.2, q.2) ∈ aliveProd W ζ G d} :=
    (h1 hA).inter (h2 hA)
  have hF : Measurable[m] fun q : (ℂ × ℂ) × Ω => ENNReal.ofReal
      (greenH (fwdAtInd W ζ G hGc d (q.1.1, q.2)) (fwdAtInd W ζ G hGc d (q.1.2, q.2))) :=
    ENNReal.measurable_ofReal.comp (measurable_greenH.comp
      (((measurable_fwdAtInd hW hGc hG d).comp h1).prodMk ((measurable_fwdAtInd hW hGc hG d).comp h2)))
  have e : greenAtInd W ζ G d = fun q => if (q.1.1, q.2) ∈ aliveProd W ζ G d ∧
      (q.1.2, q.2) ∈ aliveProd W ζ G d then ENNReal.ofReal
        (greenH (fwdAtInd W ζ G hGc d (q.1.1, q.2)) (fwdAtInd W ζ G hGc d (q.1.2, q.2))) else ⊤ := by
    funext q
    unfold greenAtInd
    split_ifs with h
    · rw [fwdAtInd_eq hGc h.1, fwdAtInd_eq hGc h.2]
    · rfl
  rw [e]
  exact Measurable.ite hS hF measurable_const

/-- The infimum of `G_ℍ(f_r y, f_r z)` over the rational times `r ≤ t ∧ σ₀` at which both points are alive. -/
def greenVersionE (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (σ₀ : Ω → ℝ≥0) (t : ℝ≥0)
    (q : (ℂ × ℂ) × Ω) : ℝ≥0∞ :=
  ⨅ r : ℚ, if (r : ℝ).toNNReal ≤ t then
    (if (r : ℝ).toNNReal ≤ σ₀ q.2 then greenAtInd W ζ G (r : ℝ).toNNReal q else ⊤) else ⊤

/-- **The version of the retained Green kernel** `G_{U_{t∧σ₀}}(y, z)`. -/
def greenVersion (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (σ₀ : Ω → ℝ≥0) (t : ℝ≥0)
    (p : ℂ × ℂ) (ω : Ω) : ℝ :=
  (greenVersionE W ζ G σ₀ t (p, ω)).toReal

theorem measurable_greenVersionE (hW : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime 𝓖 fun ω => (σ₀ ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[MeasurableSpace.prod inferInstance (𝓖 t)] (greenVersionE W ζ G σ₀ t) := by
  set m : MeasurableSpace ((ℂ × ℂ) × Ω) := MeasurableSpace.prod inferInstance (𝓖 t) with hm
  refine Measurable.iInf fun r => ?_
  by_cases hr : (r : ℝ).toNNReal ≤ t
  · simp only [hr, ↓reduceIte]
    set r' := (r : ℝ).toNNReal
    have hle : MeasurableSpace.prod inferInstance (𝓖 r') ≤ m :=
      sup_le_sup_left (MeasurableSpace.comap_mono (𝓖.mono hr)) _
    have hS : MeasurableSet[m] {q : (ℂ × ℂ) × Ω | r' ≤ σ₀ q.2} := by
      have h := hσ₀.measurableSet_lt r'
      have e : {q : (ℂ × ℂ) × Ω | r' ≤ σ₀ q.2} =
          Prod.snd ⁻¹' {ω | (σ₀ ω : WithTop ℝ≥0) < (r' : WithTop ℝ≥0)}ᶜ := by
        ext q; simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, WithTop.coe_lt_coe, not_lt]
      rw [e]
      exact (𝓖.mono hr _ h).compl.preimage (@measurable_snd (ℂ × ℂ) Ω inferInstance (𝓖 t))
    exact Measurable.ite hS ((measurable_greenAtInd hW hGc hG r').mono hle le_rfl) measurable_const
  · simp only [hr, ↓reduceIte]
    exact measurable_const

end GreenVersion

/-! ### The version on a good path -/

section Path

variable {nL nR : ℕ} {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {ω : Ω}

/-- Rationals approximating a nonnegative real from below, within `1/(n+1)`. -/
theorem exists_rat_approx_left {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ∃ r : ℚ, max 0 (q - 1 / ((n : ℝ) + 1)) ≤ (r : ℝ) ∧ (r : ℝ) ≤ q := by
  by_cases h : max 0 (q - 1 / ((n : ℝ) + 1)) < q
  · obtain ⟨r, h1, h2⟩ := exists_rat_btwn h
    exact ⟨r, h1.le, h2.le⟩
  · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hq0 : q = 0 := by
      rcases le_max_iff.1 (not_lt.1 h) with h' | h'
      · exact le_antisymm h' hq
      · linarith
    exact ⟨0, by simp only [hq0, Rat.cast_zero, zero_sub]; exact max_le le_rfl (by linarith), by simp [hq0]⟩

/-- **On a good path the version is the retained kernel** at the time `t ∧ σ₀`. -/
theorem greenVersionE_eq
    (hP : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω)) (hω : ω ∈ G) {σ₀ : Ω → ℝ≥0} (hσζ : (σ₀ ω : ℝ≥0∞) < ζ ω) {y z : ℂ}
    (hy : y ∈ H) (hz : z ∈ H) (t : ℝ≥0) :
    greenVersionE W ζ G σ₀ t ((y, z), ω) =
      K3.VTe (Ito.rpath (W · ω)) ((min t (σ₀ ω) : ℝ≥0) : ℝ) y z := by
  set T : ℝ≥0 := min t (σ₀ ω) with hTdef
  have hTζ : (T : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (by exact_mod_cast min_le_right t (σ₀ ω)) hσζ
  obtain ⟨T', hTT', hT'ζ⟩ : ∃ T' : ℝ≥0, T < T' ∧ (T' : ℝ≥0∞) < ζ ω := by
    obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTζ
    exact ⟨c, by exact_mod_cast hc1, hc2⟩
  set w := Ito.rpath (W · ω) with hw
  have hwc : ContinuousOn w (Icc 0 (T' : ℝ)) := Ito.continuousOn_rpath hP.2.2.2.1 hT'ζ
  set W' := Ito.clampDrv w (T' : ℝ) with hW'
  have hW'c : Continuous W' := Ito.continuous_clampDrv T'.coe_nonneg hwc
  have heq : EqOn w W' (Icc 0 (T' : ℝ)) := fun s hs => (Ito.clampDrv_eqOn hs).symm
  have hTT'r : (T : ℝ) < T' := by exact_mod_cast hTT'
  have halive : ∀ x : ℂ, x ∈ H → ∀ r : ℝ≥0, r ≤ T →
      ((x, ω) ∈ aliveProd W ζ G r ↔ ENNReal.ofReal (r : ℝ) < swallowTime W' x) := by
    intro x hx r hr
    have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr) hTζ
    have hrT : (r : ℝ) ≤ T := by exact_mod_cast hr
    rw [mem_aliveProd_iff hP hω hx hrζ, ← ENNReal.ofReal_coe_nnreal]
    exact ⟨fun h => lt_swallowTime_of_eqOn hTT'r hW'c.continuousOn heq hx r.coe_nonneg hrT h,
      fun h => lt_swallowTime_of_eqOn hTT'r hwc heq.symm hx r.coe_nonneg hrT h⟩
  have hfwd : ∀ x : ℂ, ∀ r : ℝ≥0, r ≤ T → fwdMap w r x = fwdMap W' r x := fun x r hr =>
    Ito.fwdMap_congr_of_eqOn_of_le heq ((show (r : ℝ) ≤ T by exact_mod_cast hr).trans hTT'r.le)
  -- the term at a rational time `r' ≤ T` at which both points are alive
  have hterm : ∀ r : ℚ, (r : ℝ).toNNReal ≤ T →
      (r : ℝ).toNNReal ≤ t ∧ (r : ℝ).toNNReal ≤ σ₀ ω := fun r hr =>
    ⟨hr.trans (min_le_left _ _), hr.trans (min_le_right _ _)⟩
  rw [VTe_eq_of_eqOn hTT'r hwc hW'c.continuousOn heq hy hz]
  refine le_antisymm ?_ ?_
  · -- every admissible time is approached from the left by admissible rationals
    refine le_iInf₂ fun q hq => ?_
    obtain ⟨hq0, hqT, hqy, hqz⟩ := hq
    choose r hr1 hr2 using exists_rat_approx_left hq0
    have hr0 : ∀ n, (0 : ℝ) ≤ r n := fun n => (le_max_left _ _).trans (hr1 n)
    have hrq : ∀ n, ((r n : ℝ).toNNReal : ℝ) = r n := fun n => Real.coe_toNNReal _ (hr0 n)
    have hrT : ∀ n, (r n : ℝ).toNNReal ≤ T := fun n => by
      rw [← NNReal.coe_le_coe, hrq]; exact (hr2 n).trans hqT
    have hle : ∀ n, greenVersionE W ζ G σ₀ t ((y, z), ω) ≤ K3.vtKer W' (r n) y z := fun n => by
      refine (iInf_le _ (r n)).trans (le_of_eq ?_)
      obtain ⟨h1, h2⟩ := hterm (r n) (hrT n)
      have hay : (y, ω) ∈ aliveProd W ζ G (r n : ℝ).toNNReal := by
        rw [halive y hy _ (hrT n), hrq]
        exact (ENNReal.ofReal_le_ofReal (hr2 n)).trans_lt hqy
      have haz : (z, ω) ∈ aliveProd W ζ G (r n : ℝ).toNNReal := by
        rw [halive z hz _ (hrT n), hrq]
        exact (ENNReal.ofReal_le_ofReal (hr2 n)).trans_lt hqz
      simp only [h1, h2, ↓reduceIte, greenAtInd, hay, haz, and_self, K3.vtKer]
      rw [hfwd y _ (hrT n), hfwd z _ (hrT n), hrq]
    have hcont := K3.continuousOn_greenH_fwdMap hW'c hy hz hq0 hqy hqz
    have hlim : Tendsto (fun n => (r n : ℝ)) atTop (𝓝[Icc 0 q] q) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ⟨hr0 n, hr2 n⟩⟩
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
        (fun n => (le_max_right _ _).trans (hr1 n)) hr2
      have := (tendsto_const_nhds (x := q)).sub tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [sub_zero] at this
    have hK : Tendsto (fun n => K3.vtKer W' (r n) y z) atTop (𝓝 (K3.vtKer W' q y z)) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((hcont q ⟨hq0, le_rfl⟩).tendsto.comp hlim)
    exact ge_of_tendsto' hK hle
  · refine le_iInf fun r => ?_
    by_cases h1 : (r : ℝ).toNNReal ≤ t
    · by_cases h2 : (r : ℝ).toNNReal ≤ σ₀ ω
      · simp only [h1, h2, ↓reduceIte, greenAtInd]
        split_ifs with h3
        · have hrT : (r : ℝ).toNNReal ≤ T := le_min h1 h2
          have hmem : (((r : ℝ).toNNReal : ℝ≥0) : ℝ) ∈ K3.vtIdx W' T y z :=
            ⟨NNReal.coe_nonneg _, by exact_mod_cast hrT, (halive y hy _ hrT).1 h3.1,
              (halive z hz _ hrT).1 h3.2⟩
          refine (iInf₂_le _ hmem).trans (le_of_eq ?_)
          simp only [K3.vtKer]
          rw [hfwd y _ hrT, hfwd z _ hrT]
        · exact le_top
      · simp only [h1, h2, ↓reduceIte, le_top]
    · simp only [h1, ↓reduceIte, le_top]

/-- The version lies in `[0, G_ℍ(y, z)]` for distinct points of `ℍ`, everywhere. -/
theorem greenVersion_mem_Icc
    (hGP : ∀ ω ∈ G, IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω))
      (fun i => (VR i · ω)) (B · ω) (ζ ω))
    (σ₀ : Ω → ℝ≥0) (t : ℝ≥0) {y z : ℂ} (hy : y ∈ H) (hz : z ∈ H) (hyz : y ≠ z) (ω : Ω) :
    0 ≤ greenVersion W ζ G σ₀ t (y, z) ω ∧ greenVersion W ζ G σ₀ t (y, z) ω ≤ greenH y z := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hyb : y ∈ Hbar := le_of_lt (show (0 : ℝ) < y.im from hy)
  have hzb : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hz)
  have hG0 : 0 ≤ greenH y z := greenH_nonneg hyb hzb hyz
  by_cases h0 : (y, ω) ∈ aliveProd W ζ G 0 ∧ (z, ω) ∈ aliveProd W ζ G 0
  · obtain ⟨-, hωG, hζ0, hsy⟩ := h0.1
    obtain ⟨-, -, -, hsz⟩ := h0.2
    have hb := (greenH_fwdMap_mem_Icc_of_path (hGP ω hωG) hζ0 hy hz hyz hsy hsz).2
    unfold greenVersion
    refine ENNReal.toReal_le_of_le_ofReal hG0 ((iInf_le _ (0 : ℚ)).trans ?_)
    have e : ((0 : ℚ) : ℝ).toNNReal = 0 := by simp
    simp only [e, zero_le, ↓reduceIte, greenAtInd, h0, and_self]
    exact ENNReal.ofReal_le_ofReal hb
  · have htop : greenVersionE W ζ G σ₀ t ((y, z), ω) = ⊤ := by
      refine iInf_eq_top.2 fun r => ?_
      split_ifs with h1 h2
      · simp only [greenAtInd, ite_eq_right_iff]
        rintro ⟨⟨-, hωG, hrζ, -⟩, ⟨-, -, -, -⟩⟩
        have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by simpa using lt_of_le_of_lt zero_le hrζ
        refine absurd (show (y, ω) ∈ aliveProd W ζ G 0 ∧ (z, ω) ∈ aliveProd W ζ G 0 from
          ⟨⟨hy, hωG, hζ0, ?_⟩, ⟨hz, hωG, hζ0, ?_⟩⟩) h0
        · simpa using Ito.exists_isForwardSol_zero (Ito.rpath (W · ω)) hy
        · simpa using Ito.exists_isForwardSol_zero (Ito.rpath (W · ω)) hz
      · rfl
      · rfl
    unfold greenVersion
    rw [htop, ENNReal.toReal_top]
    exact hG0

end Path

/-! ### Lemma 3.6, integrated, unconditionally -/

section Main

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- A good event of `𝓖_0` (the usual augmentation): good paths with `σ₀ < ζ`, of full measure. -/
theorem exists_goodSet [IsProbabilityMeasure P] (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {σ₀ : Ω → ℝ≥0} (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) :
    ∃ G : Set Ω, MeasurableSet[usualAugmentation 𝓕 P 0] G ∧ (∀ᵐ ω ∂P, ω ∈ G) ∧
      ∀ ω ∈ G, IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω))
        (fun i => (VR i · ω)) (B · ω) (ζ ω) ∧ (σ₀ ω : ℝ≥0∞) < ζ ω := by
  obtain ⟨-, -, -, -, hpath⟩ := hE
  set Gp : Set Ω := {ω | IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω))
    (fun i => (VR i · ω)) (B · ω) (ζ ω) ∧ (σ₀ ω : ℝ≥0∞) < ζ ω} with hGpdef
  have hGp : ∀ᵐ ω ∂P, ω ∈ Gp := by
    filter_upwards [hpath, hσ₀ζ] with ω h1 h2 using ⟨h1, h2⟩
  have hnull : P (toMeasurable P Gpᶜ) = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.1 hGp
  refine ⟨(toMeasurable P Gpᶜ)ᶜ,
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable _ _) hnull 0).compl, ?_,
    fun ω hω => ?_⟩
  · rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    simpa using hω
  · by_contra h; exact hω (subset_toMeasurable _ _ h)

/-- **Lemma 3.6, the tested frozen mean.** For an integrable `φ` vanishing off `ℍ` and a bounded stopping time
`σ₀ < T` of the usual augmentation, `t ↦ ∫ φ(z) η̄_{t∧σ₀}(z) dz` agrees almost surely with a martingale. -/
theorem exists_martingale_testedMean [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N)
    {φ : ℂ → ℝ} (hφm : Measurable φ) (hφi : Integrable φ) (hφH : ∀ z, z ∉ H → φ z = 0) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧
      ∀ᵐ ω ∂P, ∀ t, M t ω = ∫ z, φ z * frozenMean ρL ρR (W · ω) (fun i => (VL i · ω))
        (fun i => (VR i · ω)) (min t (σ₀ ω)) z := by
  obtain ⟨Yv, hYm, hYb, hYz, hYae⟩ := exists_frozenMean_version (ρL := ρL) (ρR := ρR) hE hσ₀ hσ₀ζ hσ₀N
  refine ⟨_, martingale_integral_frozenMean_of_version hE hσ₀ hσ₀ζ hσ₀N hφm hφi hφH hYm hYb hYz, ?_⟩
  filter_upwards [hYae] with ω hω t
  refine integral_congr_ae ?_
  filter_upwards [hω] with z hz
  by_cases hzH : z ∈ H
  · rw [hz hzH t]
  · simp [hφH z hzH]

/-- **Lemma 3.6, the square of the tested mean plus the retained energy.** For a continuous `φ` with compact
support at height `≥ δ > 0` and a bounded stopping time `σ₀ < T` of the usual augmentation,
`t ↦ (∫ φ η̄_{t∧σ₀})² + Q_{U_{t∧σ₀}}(φ, φ)` agrees almost surely with a martingale. -/
theorem exists_martingale_testedMean_sq_add_energy [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N)
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ)
    (hφδ : ∀ a : ℂ, a.im < δ → φ a = 0) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧
      ∀ᵐ ω ∂P, ∀ t, M t ω = (∫ z, φ z * frozenMean ρL ρR (W · ω) (fun i => (VL i · ω))
        (fun i => (VR i · ω)) (min t (σ₀ ω)) z) ^ 2 +
          retainedGreenEnergy (W · ω) (min t (σ₀ ω)) φ := by
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  obtain ⟨Yv, hYm, hYb, hYz, hYae⟩ := exists_frozenMean_version (ρL := ρL) (ρR := ρR) hE hσ₀ hσ₀ζ hσ₀N
  obtain ⟨G, hG0, hGae, hGsub⟩ := exists_goodSet hE hσ₀ζ
  have hWa := hE.2.1
  have hW𝓖 : AdaptedBefore 𝓖 ζ W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) hWa
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGsub ω hω).1.2.2.2.1
  have hφH : ∀ a : ℂ, φ a ≠ 0 → a ∈ H := fun a ha => by
    by_contra h
    exact ha (hφδ a (lt_of_le_of_lt (not_lt.1 h) hδ))
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
  set C := meanBound ρL ρR
  set Y2 : ℝ≥0 → ℂ × ℂ → Ω → ℝ := fun t p ω =>
    Yv t p.1 ω * Yv t p.2 ω + greenVersion W ζ G σ₀ t p ω with hY2def
  have hY2m : ∀ t, Measurable[MeasurableSpace.prod inferInstance (𝓖 t)]
      (fun q : (ℂ × ℂ) × Ω => Y2 t q.1 q.2) := fun t => by
    have h1 : @Measurable ((ℂ × ℂ) × Ω) (ℂ × Ω) (MeasurableSpace.prod inferInstance (𝓖 t))
        ((borel ℂ).prod (𝓖 t)) fun q => (q.1.1, q.2) :=
      (measurable_fst.comp (@measurable_fst (ℂ × ℂ) Ω inferInstance (𝓖 t))).prodMk
        (@measurable_snd (ℂ × ℂ) Ω inferInstance (𝓖 t))
    have h2 : @Measurable ((ℂ × ℂ) × Ω) (ℂ × Ω) (MeasurableSpace.prod inferInstance (𝓖 t))
        ((borel ℂ).prod (𝓖 t)) fun q => (q.1.2, q.2) :=
      (measurable_snd.comp (@measurable_fst (ℂ × ℂ) Ω inferInstance (𝓖 t))).prodMk
        (@measurable_snd (ℂ × ℂ) Ω inferInstance (𝓖 t))
    exact (((hYm t).comp h1).mul ((hYm t).comp h2)).add
      (measurable_greenVersionE hW𝓖 hGc hG0 hσ₀ t).ennreal_toReal
  have hY2b : ∀ t (p : ℂ × ℂ) ω, p.1 ∈ H → p.2 ∈ H → p.1 ≠ p.2 →
      |Y2 t p ω| ≤ C ^ 2 + greenH p.1 p.2 := fun t p ω h1 h2 h12 => by
    obtain ⟨g0, gG⟩ := greenVersion_mem_Icc (σ₀ := σ₀) (t := t) (fun ω hω => (hGsub ω hω).1) h1 h2 h12 ω
    have hab : |Yv t p.1 ω * Yv t p.2 ω| ≤ C ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul (hYb t _ _) (hYb t _ _) (abs_nonneg _) (meanBound_nonneg ρL ρR)
    calc |Y2 t p ω| ≤ |Yv t p.1 ω * Yv t p.2 ω| + |greenVersion W ζ G σ₀ t p ω| := abs_add_le _ _
      _ ≤ C ^ 2 + greenH p.1 p.2 := by rw [abs_of_nonneg g0]; exact add_le_add hab gG
  have hgreen : ∀ ω ∈ G, ∀ t, ∀ a ∈ H, ∀ b ∈ H,
      greenVersion W ζ G σ₀ t (a, b) ω = retainedGreen (W · ω) (min t (σ₀ ω)) a b :=
    fun ω hω t a ha b hb => by
      unfold greenVersion retainedGreen K3.VT
      rw [greenVersionE_eq (hGsub ω hω).1 hω (hGsub ω hω).2 ha hb t]
  have hY2 : ∀ y ∈ H, ∀ z ∈ H, y ≠ z → ∀ᵐ ω ∂P, ∀ t, Y2 t (y, z) ω =
      frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) y *
        frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z +
      retainedGreen (W · ω) (min t (σ₀ ω)) y z := fun y hy z hz _ => by
    filter_upwards [hYz y hy, hYz z hz, hGae] with ω h1 h2 hω t
    simp only [hY2def]
    rw [h1 t, h2 t, hgreen ω hω t y hy z hz]
  have hmart := martingale_integral_frozenMean_two_of_version (ρL := ρL) (ρR := ρR) hE hσ₀ hσ₀ζ hσ₀N
    hφc hφs hδ hφδ hY2m hY2b hY2
  refine ⟨_, hmart, ?_⟩
  filter_upwards [hYae, hGae] with ω hω hωG t
  set fm : ℂ → ℝ := fun z => frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
    (min t (σ₀ ω)) z with hfm
  have hYvm : Measurable fun z => Yv t z ω := (hYm t).comp measurable_prodMk_right
  have hgm : Measurable fun p : ℂ × ℂ => greenVersion W ζ G σ₀ t p ω :=
    (measurable_greenVersionE hW𝓖 hGc hG0 hσ₀ t).ennreal_toReal.comp measurable_prodMk_right
  have hφY : Integrable fun z => φ z * Yv t z ω :=
    hφi.mul_bdd hYvm.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hYb t z ω)
  have hint1 : Integrable (fun p : ℂ × ℂ => (φ p.1 * Yv t p.1 ω) * (φ p.2 * Yv t p.2 ω))
      ((volume : Measure ℂ).prod volume) := hφY.mul_prod hφY
  have hint2 : Integrable (fun p : ℂ × ℂ => φ p.1 * φ p.2 * greenVersion W ζ G σ₀ t p ω)
      ((volume : Measure ℂ).prod volume) := by
    refine (FieldMart.integrable_rho_rho_greenH hφc hφs hδ hφδ).mono'
      (((hφc.measurable.comp measurable_fst).mul (hφc.measurable.comp measurable_snd)).mul
        hgm).aestronglyMeasurable ?_
    filter_upwards [FieldMart.ae_ne_diag] with p hp
    by_cases h0 : φ p.1 = 0 ∨ φ p.2 = 0
    · rcases h0 with h0 | h0 <;> simp [h0]
    · push Not at h0
      obtain ⟨g0, gG⟩ := greenVersion_mem_Icc (σ₀ := σ₀) (t := t) (fun ω hω => (hGsub ω hω).1)
        (hφH _ h0.1) (hφH _ h0.2) hp ω
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg g0]
      exact mul_le_mul_of_nonneg_left gG (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hmean : ∫ z, φ z * Yv t z ω = ∫ z, φ z * fm z := by
    refine integral_congr_ae ?_
    filter_upwards [hω] with z hz
    by_cases h0 : φ z = 0
    · simp [h0]
    · rw [hz (hφH z h0) t]
  calc ∫ p, φ p.1 * φ p.2 * Y2 t p ω ∂((volume : Measure ℂ).prod volume)
      = ∫ p, ((φ p.1 * Yv t p.1 ω) * (φ p.2 * Yv t p.2 ω) +
          φ p.1 * φ p.2 * greenVersion W ζ G σ₀ t p ω) ∂((volume : Measure ℂ).prod volume) :=
        integral_congr_ae (ae_of_all _ fun p => by simp only [hY2def]; ring)
    _ = (∫ p, (φ p.1 * Yv t p.1 ω) * (φ p.2 * Yv t p.2 ω) ∂((volume : Measure ℂ).prod volume)) +
          ∫ p, φ p.1 * φ p.2 * greenVersion W ζ G σ₀ t p ω ∂((volume : Measure ℂ).prod volume) :=
        integral_add hint1 hint2
    _ = (∫ z, φ z * fm z) ^ 2 + retainedGreenEnergy (W · ω) (min t (σ₀ ω)) φ := by
        congr 1
        · rw [integral_prod_mul (fun z => φ z * Yv t z ω) (fun z => φ z * Yv t z ω), hmean, sq]
        · rw [integral_prod _ hint2]
          unfold retainedGreenEnergy
          refine integral_congr_ae (ae_of_all _ fun a => integral_congr_ae (ae_of_all _ fun b => ?_))
          show φ a * φ b * greenVersion W ζ G σ₀ t (a, b) ω =
            φ a * retainedGreen (W · ω) (min t (σ₀ ω)) a b * φ b
          by_cases h0 : φ a = 0 ∨ φ b = 0
          · rcases h0 with h0 | h0 <;> simp [h0]
          · push Not at h0
            rw [hgreen ω hωG t a (hφH a h0.1) b (hφH b h0.2)]
            ring

end Main

end WangWu

end InteractingSLE
