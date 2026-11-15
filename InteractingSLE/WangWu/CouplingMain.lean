import InteractingSLE.WangWu.CouplingVersionTwo
import InteractingSLE.WangWu.CouplingExp
import InteractingSLE.WangWu.CouplingRetained
import QuantumZipper.Proofs.Loewner.ForwardODE

/-!
# Wang–Wu at `κ = 4`: pathwise regularity of the retained Green form (towards Proposition 3.7)

Packet PROVE-WW-A3. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, Lemma 3.4.3–3.4.4
("Its time paths are continuous for pairs of points retained through the time in question", "`Q_{U_t}(p, p)` is
nonincreasing in `t`") and Lemma 3.6 ("dominated convergence makes it continuous"), ruling R31.

Pathwise statements on a path of the marked chain:

* `continuous_VTe`, `continuous_VT`: for a continuous driver, `T ↦ V_T(a, b)` (QuantumZipper's frozen kernel, the
  retained Green kernel) is continuous: `G_ℍ(f_T a, f_T b)` before the first swallowing, constant afterwards, with
  the monotone left limit at the swallowing time;
* `continuous_retainedGreen_min`, `retainedGreen_le_greenH`: the same for `t ↦ G_{U_{t∧σ}}(a, b)` on a path of the
  chain (driver clamped after a time in `(σ, T)`), and `0 ≤ G_{U_t} ≤ G_ℍ`;
* `retainedGreenForm` (the bilinear form `Q_{U_t}(φ, ψ)`), `retainedGreenForm_eq_integral_prod` (Fubini),
  `continuous_retainedGreenForm_min` (dominated convergence), `antitone_retainedGreenForm_min` (for `φ, ψ ≥ 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace WangWu

/-! ### Continuity of the frozen kernel in time -/

section KernelTime

variable {W : ℝ → ℝ} {a b : ℂ}

theorem VTe_antitone (W : ℝ → ℝ) (a b : ℂ) : Antitone fun T : ℝ≥0 => K3.VTe W (T : ℝ) a b :=
  fun _ _ hst => iInf₂_mono' fun r hr =>
    ⟨r, ⟨hr.1, hr.2.1.trans (by exact_mod_cast hst), hr.2.2⟩, le_rfl⟩

/-- After the first swallowing the frozen kernel no longer changes. -/
theorem VTe_eq_of_swallow {T T' : ℝ}
    (hT : min (swallowTime W a) (swallowTime W b) ≤ ENNReal.ofReal T)
    (hT' : min (swallowTime W a) (swallowTime W b) ≤ ENNReal.ofReal T') :
    K3.VTe W T a b = K3.VTe W T' a b := by
  have hidx : K3.vtIdx W T a b = K3.vtIdx W T' a b := by
    have key : ∀ {S S' : ℝ}, min (swallowTime W a) (swallowTime W b) ≤ ENNReal.ofReal S' →
        ∀ t, t ∈ K3.vtIdx W S a b → t ≤ S' := fun {S S'} hS' t ht => by
      have h1 : ENNReal.ofReal t < ENNReal.ofReal S' := (lt_min ht.2.2.1 ht.2.2.2).trans_le hS'
      exact ((ENNReal.ofReal_lt_ofReal_iff'.1 h1).1).le
    ext t
    exact ⟨fun ht => ⟨ht.1, key hT' t ht, ht.2.2⟩, fun ht => ⟨ht.1, key hT t ht, ht.2.2⟩⟩
  simp only [K3.VTe, hidx]

/-- **The frozen kernel is continuous in time** (continuous driver, points of `ℍ`). -/
theorem continuous_VTe (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) :
    Continuous fun T : ℝ≥0 => K3.VTe W (T : ℝ) a b := by
  set h : ℝ≥0 → ℝ≥0∞ := fun T => K3.VTe W (T : ℝ) a b with hh
  set τ := min (swallowTime W a) (swallowTime W b) with hτ
  have hanti : Antitone h := VTe_antitone W a b
  -- before the first swallowing the kernel is `G(f_T a, f_T b)`, continuous on `[0, T₁]`
  have hbefore : ∀ T₁ : ℝ≥0, ENNReal.ofReal T₁ < τ → ContinuousOn h (Icc 0 T₁) := by
    intro T₁ hT₁
    have hsa : ENNReal.ofReal T₁ < swallowTime W a := hT₁.trans_le (min_le_left _ _)
    have hsb : ENNReal.ofReal T₁ < swallowTime W b := hT₁.trans_le (min_le_right _ _)
    have hc := K3.continuousOn_greenH_fwdMap hW ha hb T₁.coe_nonneg hsa hsb
    have hc' : ContinuousOn (fun T : ℝ≥0 => K3.vtKer W (T : ℝ) a b) (Icc 0 T₁) := by
      have hmaps : MapsTo (fun T : ℝ≥0 => (T : ℝ)) (Icc 0 T₁) (Icc 0 (T₁ : ℝ)) :=
        fun T (hT : T ∈ Icc (0 : ℝ≥0) T₁) => ⟨T.coe_nonneg, by exact_mod_cast hT.2⟩
      exact ENNReal.continuous_ofReal.comp_continuousOn
        (hc.comp NNReal.continuous_coe.continuousOn hmaps)
    refine hc'.congr fun T hT => ?_
    have hle : ENNReal.ofReal (T : ℝ) ≤ ENNReal.ofReal T₁ :=
      ENNReal.ofReal_le_ofReal (by exact_mod_cast hT.2)
    exact K3.VTe_eq_vtKer_of_lt hW ha hb T.coe_nonneg (hle.trans_lt hsa) (hle.trans_lt hsb)
  refine continuous_iff_continuousAt.2 fun T₀ => continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · -- left continuity
    rcases lt_or_ge (ENNReal.ofReal T₀) τ with hlt | hge
    · exact ((hbefore T₀ hlt) T₀ ⟨zero_le, le_rfl⟩).mono fun T hT => ⟨zero_le, hT⟩
    · -- the first swallowing time `s ≤ T₀`
      have hτfin : τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hge
      set s : ℝ≥0 := τ.toNNReal with hs
      have hsτ : (s : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hτfin
      have hsT₀ : s ≤ T₀ := by
        rw [← ENNReal.coe_le_coe, hsτ]; rwa [ENNReal.ofReal_coe_nnreal] at hge
      have hconst : ∀ T : ℝ≥0, s ≤ T → h T = h s := fun T hT => by
        refine VTe_eq_of_swallow ?_ ?_
        · rw [ENNReal.ofReal_coe_nnreal, ← hτ, ← hsτ]; exact_mod_cast hT
        · rw [ENNReal.ofReal_coe_nnreal, ← hτ, ← hsτ]
      rcases lt_or_eq_of_le hsT₀ with hsT | hsT
      · refine (continuousWithinAt_const (b := h s)).congr_of_eventuallyEq ?_ (hconst T₀ hsT₀)
        filter_upwards [Ioc_mem_nhdsLE hsT] with T hT using hconst T hT.1.le
      · rw [← hsT]
        refine continuousWithinAt_Iio_iff_Iic.1 ?_
        have hlim := hanti.tendsto_nhdsLT s
        have heq : sInf (h '' Iio s) = h s := by
          refine le_antisymm ?_ (le_sInf ?_)
          · show sInf (h '' Iio s) ≤ ⨅ t ∈ K3.vtIdx W s a b, K3.vtKer W t a b
            refine le_iInf₂ fun t ht => ?_
            have ht' : ENNReal.ofReal t < τ := lt_min ht.2.2.1 ht.2.2.2
            have hts : t.toNNReal < s := by
              have h1 : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < s := by rw [hsτ]; exact ht'
              exact_mod_cast h1
            have hmem : h t.toNNReal ∈ h '' Iio s := ⟨t.toNNReal, hts, rfl⟩
            refine (sInf_le hmem).trans (le_of_eq ?_)
            show K3.VTe W ((t.toNNReal : ℝ≥0) : ℝ) a b = K3.vtKer W t a b
            rw [Real.coe_toNNReal _ ht.1]
            exact K3.VTe_eq_vtKer_of_lt hW ha hb ht.1 (ht'.trans_le (min_le_left _ _))
              (ht'.trans_le (min_le_right _ _))
          · rintro _ ⟨T, hT, rfl⟩
            exact hanti hT.le
        rw [heq] at hlim
        exact hlim
  · -- right continuity
    rcases lt_or_ge (ENNReal.ofReal T₀) τ with hlt | hge
    · obtain ⟨T₁, hT₀₁, hT₁τ⟩ : ∃ T₁ : ℝ≥0, T₀ < T₁ ∧ ENNReal.ofReal T₁ < τ := by
        rw [ENNReal.ofReal_coe_nnreal] at hlt
        obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
        exact ⟨c, by exact_mod_cast hc1, by rwa [ENNReal.ofReal_coe_nnreal]⟩
      exact ((hbefore T₁ hT₁τ) T₀ ⟨zero_le, hT₀₁.le⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Ico_mem_nhdsGE hT₀₁) fun T hT => ⟨zero_le, hT.2.le⟩)
    · refine (continuousWithinAt_const (b := h T₀)).congr_of_eventuallyEq ?_ rfl
      filter_upwards [self_mem_nhdsWithin] with T hT
      exact VTe_eq_of_swallow (hge.trans (ENNReal.ofReal_le_ofReal (by exact_mod_cast hT))) hge

theorem VTe_le_vtKer_zero (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) (T : ℝ≥0) :
    K3.VTe W T a b ≤ K3.vtKer W 0 a b :=
  iInf₂_le 0 ⟨le_rfl, T.coe_nonneg, by rw [ENNReal.ofReal_zero]; exact swallowTime_pos hW ha,
    by rw [ENNReal.ofReal_zero]; exact swallowTime_pos hW hb⟩

theorem continuous_VT (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) :
    Continuous fun T : ℝ≥0 => K3.VT W T a b :=
  ENNReal.continuousOn_toReal.comp_continuous (continuous_VTe hW ha hb) fun T =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (VTe_le_vtKer_zero hW ha hb T)

end KernelTime

/-! ### The retained kernel on a path of the chain -/

section Path

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {bm : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- A continuous driver agreeing with the path on `[0, T']`, for some `T' > σ`. -/
theorem exists_clamp (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ) {σ : ℝ≥0}
    (hσ : (σ : ℝ≥0∞) < ζ) :
    ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T' : ℝ, (σ : ℝ) < T' ∧
      EqOn (Ito.rpath w) W' (Icc 0 T') ∧ ContinuousOn (Ito.rpath w) (Icc 0 T') := by
  obtain ⟨T', hσT', hT'ζ⟩ : ∃ T' : ℝ≥0, σ < T' ∧ (T' : ℝ≥0∞) < ζ := by
    obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hσ
    exact ⟨c, by exact_mod_cast hc1, hc2⟩
  have hwc : ContinuousOn (Ito.rpath w) (Icc 0 (T' : ℝ)) := Ito.continuousOn_rpath hP.2.2.2.1 hT'ζ
  refine ⟨Ito.clampDrv (Ito.rpath w) T', Ito.continuous_clampDrv T'.coe_nonneg hwc, ?_, T',
    by exact_mod_cast hσT', fun s hs => (Ito.clampDrv_eqOn hs).symm, hwc⟩
  rw [(Ito.clampDrv_eqOn (W := Ito.rpath w) ⟨le_rfl, T'.coe_nonneg⟩), Ito.rpath]
  simpa using hP.1

/-- On a path, the retained kernel up to time `σ < T` is the frozen kernel of a continuous driver. -/
theorem retainedGreen_eq_VT_of_clamp {W' : ℝ → ℝ} (hW' : Continuous W') {σ : ℝ≥0} {T' : ℝ}
    (hσT' : (σ : ℝ) < T') (heq : EqOn (Ito.rpath w) W' (Icc 0 T'))
    (hwc : ContinuousOn (Ito.rpath w) (Icc 0 T')) {T : ℝ≥0} (hT : T ≤ σ) {a b : ℂ} (ha : a ∈ H)
    (hb : b ∈ H) : retainedGreen w T a b = K3.VT W' T a b := by
  unfold retainedGreen K3.VT
  rw [VTe_eq_of_eqOn ((show (T : ℝ) ≤ σ by exact_mod_cast hT).trans_lt hσT') hwc
    hW'.continuousOn heq ha hb]

/-- **The retained kernel is continuous in time** along `t ↦ t ∧ σ` on a path of the chain. -/
theorem continuous_retainedGreen_min (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) :
    Continuous fun t : ℝ≥0 => retainedGreen w (min t σ) a b := by
  obtain ⟨W', hW'c, -, T', hσT', heq, hwc⟩ := exists_clamp hP hσ
  have e : (fun t : ℝ≥0 => retainedGreen w (min t σ) a b) =
      fun t => K3.VT W' (min t σ : ℝ≥0) a b := funext fun t =>
    retainedGreen_eq_VT_of_clamp hW'c hσT' heq hwc (min_le_right _ _) ha hb
  rw [e]
  exact (continuous_VT hW'c ha hb).comp (continuous_id.min continuous_const)

/-- On a path, the frozen kernel at time `0` bounds it at every time, and it is finite. -/
theorem VTe_le_ofReal_greenH (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ) (hζ : 0 < ζ)
    {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) (T : ℝ≥0) :
    K3.VTe (Ito.rpath w) T a b ≤ ENNReal.ofReal (greenH a b) := by
  have hpa := swallowTime_pos_of_path hP hζ (show 0 < a.im from ha)
  have hpb := swallowTime_pos_of_path hP hζ (show 0 < b.im from hb)
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := by rwa [ENNReal.coe_zero]
  have hsa : ∃ v, IsForwardSol (Ito.rpath w) a ((0 : ℝ≥0) : ℝ) v := by
    simpa using Ito.exists_isForwardSol_zero (Ito.rpath w) ha
  have hsb : ∃ v, IsForwardSol (Ito.rpath w) b ((0 : ℝ≥0) : ℝ) v := by
    simpa using Ito.exists_isForwardSol_zero (Ito.rpath w) hb
  have hg := (greenH_fwdMap_mem_Icc_of_path hP h0 ha hb hab hsa hsb).2
  refine (iInf₂_le 0 ⟨le_rfl, T.coe_nonneg, by rwa [ENNReal.ofReal_zero],
    by rwa [ENNReal.ofReal_zero]⟩).trans ?_
  simp only [K3.vtKer]
  exact ENNReal.ofReal_le_ofReal (by simpa using hg)

theorem retainedGreen_le_greenH (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ) (hζ : 0 < ζ)
    {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) (T : ℝ≥0) :
    retainedGreen w T a b ≤ greenH a b :=
  ENNReal.toReal_le_of_le_ofReal
    (greenH_nonneg (le_of_lt (show (0 : ℝ) < a.im from ha) : a ∈ Hbar)
      (le_of_lt (show (0 : ℝ) < b.im from hb) : b ∈ Hbar) hab)
    (VTe_le_ofReal_greenH hP hζ ha hb hab T)

/-- **The retained kernel is nonincreasing in time**, on a path. -/
theorem retainedGreen_antitone_of_path (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ)
    (hζ : 0 < ζ) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) {s t : ℝ≥0} (hst : s ≤ t) :
    retainedGreen w t a b ≤ retainedGreen w s a b :=
  retainedGreen_antitone w hst a b
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (VTe_le_ofReal_greenH hP hζ ha hb hab s))

/-- On a path, the retained kernel at a time `T < ζ` agrees on `ℍ × ℍ` with a Borel function. -/
theorem exists_measurable_retainedGreen (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) :
    ∃ g : ℂ × ℂ → ℝ, Measurable g ∧ ∀ p : ℂ × ℂ, p.1 ∈ H → p.2 ∈ H →
      g p = retainedGreen w T p.1 p.2 := by
  obtain ⟨W', hW'c, hW'0, T', hσT', heq, hwc⟩ := exists_clamp hP hT
  refine ⟨fun p => ((H ×ˢ H).indicator (fun p : ℂ × ℂ => K3.VTe W' T p.1 p.2) p).toReal,
    (K3.measurable_indicator_VTe hW'c hW'0 T).ennreal_toReal, fun p h1 h2 => ?_⟩
  simp only [indicator_of_mem (show p ∈ H ×ˢ H from ⟨h1, h2⟩)]
  rw [retainedGreen_eq_VT_of_clamp hW'c hσT' heq hwc le_rfl h1 h2]
  rfl

end Path

/-! ### Test functions and the retained Green form -/

/-- The test functions of the integrated identities: continuous, compactly supported, vanishing below a positive
height (every test function on `ℍ` is one). -/
def IsTestFn (φ : ℂ → ℝ) : Prop :=
  Continuous φ ∧ HasCompactSupport φ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℂ, a.im < δ → φ a = 0

/-- **The retained Green form** `Q_{U_t}(φ, ψ) = ∬ φ(a) G_{U_t}(a, b) ψ(b) da db`. -/
def retainedGreenForm (w : ℝ≥0 → ℝ) (t : ℝ≥0) (φ ψ : ℂ → ℝ) : ℝ :=
  ∫ a, ∫ b, φ a * retainedGreen w t a b * ψ b

theorem retainedGreenEnergy_eq_form (w : ℝ≥0 → ℝ) (t : ℝ≥0) (φ : ℂ → ℝ) :
    retainedGreenEnergy w t φ = retainedGreenForm w t φ φ := rfl

section TestFn

variable {φ ψ : ℂ → ℝ}

theorem IsTestFn.mem_H (hφ : IsTestFn φ) {a : ℂ} (ha : φ a ≠ 0) : a ∈ H := by
  obtain ⟨-, -, δ, hδ, hφδ⟩ := hφ
  by_contra h
  exact ha (hφδ a (lt_of_le_of_lt (not_lt.1 h) hδ))

theorem IsTestFn.integrable (hφ : IsTestFn φ) : Integrable φ :=
  hφ.1.integrable_of_hasCompactSupport hφ.2.1

theorem IsTestFn.lin (hφ : IsTestFn φ) (hψ : IsTestFn ψ) (c d : ℝ) :
    IsTestFn fun a => c * φ a + d * ψ a := by
  obtain ⟨hφc, hφs, δ, hδ, hφδ⟩ := hφ
  obtain ⟨hψc, hψs, δ', hδ', hψδ⟩ := hψ
  refine ⟨(continuous_const.mul hφc).add (continuous_const.mul hψc),
    (hφs.mul_left).add hψs.mul_left, min δ δ', lt_min hδ hδ', fun a ha => ?_⟩
  show c * φ a + d * ψ a = 0
  rw [hφδ a (ha.trans_le (min_le_left _ _)), hψδ a (ha.trans_le (min_le_right _ _))]
  ring

/-- `|φ| + |ψ|`, the dominating test function. -/
def testAbs (φ ψ : ℂ → ℝ) (a : ℂ) : ℝ := |φ a| + |ψ a|

theorem IsTestFn.testAbs (hφ : IsTestFn φ) (hψ : IsTestFn ψ) : IsTestFn (testAbs φ ψ) := by
  obtain ⟨hφc, hφs, δ, hδ, hφδ⟩ := hφ
  obtain ⟨hψc, hψs, δ', hδ', hψδ⟩ := hψ
  refine ⟨hφc.abs.add hψc.abs, (hφs.comp_left abs_zero).add (hψs.comp_left abs_zero),
    min δ δ', lt_min hδ hδ', fun a ha => ?_⟩
  simp only [WangWu.testAbs, hφδ a (ha.trans_le (min_le_left _ _)),
    hψδ a (ha.trans_le (min_le_right _ _)), abs_zero, add_zero]

theorem testAbs_nonneg (φ ψ : ℂ → ℝ) (a : ℂ) : 0 ≤ testAbs φ ψ a :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem integrable_testAbs_greenH (hφ : IsTestFn φ) (hψ : IsTestFn ψ) :
    Integrable (fun p : ℂ × ℂ => |testAbs φ ψ p.1| * |testAbs φ ψ p.2| * greenH p.1 p.2)
      ((volume : Measure ℂ).prod volume) := by
  obtain ⟨hc, hs, δ, hδ, hρδ⟩ := hφ.testAbs hψ
  exact FieldMart.integrable_rho_rho_greenH hc hs hδ hρδ

end TestFn

section Form

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {bm : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  {φ ψ : ℂ → ℝ}

theorem norm_formIntegrand_le (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ) (hζ : 0 < ζ)
    (hφ : IsTestFn φ) (hψ : IsTestFn ψ) (T : ℝ≥0) {p : ℂ × ℂ} (hp : p.1 ≠ p.2) :
    ‖φ p.1 * retainedGreen w T p.1 p.2 * ψ p.2‖ ≤
      |testAbs φ ψ p.1| * |testAbs φ ψ p.2| * greenH p.1 p.2 := by
  by_cases h0 : φ p.1 = 0 ∨ ψ p.2 = 0
  · have hrhs : 0 ≤ |testAbs φ ψ p.1| * |testAbs φ ψ p.2| * greenH p.1 p.2 := by
      by_cases h1 : testAbs φ ψ p.1 = 0 ∨ testAbs φ ψ p.2 = 0
      · rcases h1 with h1 | h1 <;> simp [h1]
      · push Not at h1
        have ha := (hφ.testAbs hψ).mem_H h1.1
        have hb := (hφ.testAbs hψ).mem_H h1.2
        exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (greenH_nonneg (le_of_lt (show (0 : ℝ) < p.1.im from ha) : p.1 ∈ Hbar)
            (le_of_lt (show (0 : ℝ) < p.2.im from hb) : p.2 ∈ Hbar) hp)
    rcases h0 with h0 | h0 <;> simpa [h0] using hrhs
  · push Not at h0
    have ha := hφ.mem_H h0.1
    have hb := hψ.mem_H h0.2
    have g0 := retainedGreen_nonneg w T p.1 p.2
    have gG := retainedGreen_le_greenH hP hζ ha hb hp T
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg g0,
      abs_of_nonneg (testAbs_nonneg φ ψ _), abs_of_nonneg (testAbs_nonneg φ ψ _)]
    have h1 : |φ p.1| ≤ testAbs φ ψ p.1 := le_add_of_nonneg_right (abs_nonneg _)
    have h2 : |ψ p.2| ≤ testAbs φ ψ p.2 := le_add_of_nonneg_left (abs_nonneg _)
    calc |φ p.1| * retainedGreen w T p.1 p.2 * |ψ p.2|
        ≤ testAbs φ ψ p.1 * greenH p.1 p.2 * testAbs φ ψ p.2 :=
          mul_le_mul (mul_le_mul h1 gG g0 (testAbs_nonneg φ ψ _)) h2 (abs_nonneg _)
            (mul_nonneg (testAbs_nonneg φ ψ _) (g0.trans gG))
      _ = testAbs φ ψ p.1 * testAbs φ ψ p.2 * greenH p.1 p.2 := by ring

theorem aestronglyMeasurable_formIntegrand (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ)
    (hφ : IsTestFn φ) (hψ : IsTestFn ψ) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) :
    AEStronglyMeasurable (fun p : ℂ × ℂ => φ p.1 * retainedGreen w T p.1 p.2 * ψ p.2)
      ((volume : Measure ℂ).prod volume) := by
  obtain ⟨g, hgm, hg⟩ := exists_measurable_retainedGreen hP hT
  refine (((hφ.1.measurable.comp measurable_fst).mul hgm).mul
    (hψ.1.measurable.comp measurable_snd)).aestronglyMeasurable.congr (ae_of_all _ fun p => ?_)
  show φ p.1 * g p * ψ p.2 = φ p.1 * retainedGreen w T p.1 p.2 * ψ p.2
  by_cases h0 : φ p.1 = 0 ∨ ψ p.2 = 0
  · rcases h0 with h0 | h0 <;> simp [h0]
  · push Not at h0
    rw [hg p (hφ.mem_H h0.1) (hψ.mem_H h0.2)]

theorem integrable_formIntegrand (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ)
    (hφ : IsTestFn φ) (hψ : IsTestFn ψ) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) :
    Integrable (fun p : ℂ × ℂ => φ p.1 * retainedGreen w T p.1 p.2 * ψ p.2)
      ((volume : Measure ℂ).prod volume) :=
  (integrable_testAbs_greenH hφ hψ).mono' (aestronglyMeasurable_formIntegrand hP hφ hψ hT)
    (by filter_upwards [FieldMart.ae_ne_diag] with p hp
        exact norm_formIntegrand_le hP (lt_of_le_of_lt zero_le hT) hφ hψ T hp)

theorem retainedGreenForm_eq_integral_prod (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ)
    (hφ : IsTestFn φ) (hψ : IsTestFn ψ) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) :
    retainedGreenForm w T φ ψ =
      ∫ p, φ p.1 * retainedGreen w T p.1 p.2 * ψ p.2 ∂((volume : Measure ℂ).prod volume) :=
  (integral_prod _ (integrable_formIntegrand hP hφ hψ hT)).symm

/-- **The retained form is continuous in time** along `t ↦ t ∧ σ` (dominated convergence). -/
theorem continuous_retainedGreenForm_min (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) (hφ : IsTestFn φ) (hψ : IsTestFn ψ) :
    Continuous fun t : ℝ≥0 => retainedGreenForm w (min t σ) φ ψ := by
  have hT : ∀ t : ℝ≥0, ((min t σ : ℝ≥0) : ℝ≥0∞) < ζ := fun t =>
    lt_of_le_of_lt (by exact_mod_cast min_le_right t σ) hσ
  have hζ : 0 < ζ := lt_of_le_of_lt zero_le hσ
  have e : (fun t : ℝ≥0 => retainedGreenForm w (min t σ) φ ψ) = fun t =>
      ∫ p, φ p.1 * retainedGreen w (min t σ) p.1 p.2 * ψ p.2 ∂((volume : Measure ℂ).prod volume) :=
    funext fun t => retainedGreenForm_eq_integral_prod hP hφ hψ (hT t)
  rw [e]
  refine continuous_of_dominated (fun t => aestronglyMeasurable_formIntegrand hP hφ hψ (hT t))
    (fun t => ?_) (integrable_testAbs_greenH hφ hψ) ?_
  · filter_upwards [FieldMart.ae_ne_diag] with p hp
    exact norm_formIntegrand_le hP hζ hφ hψ _ hp
  · refine ae_of_all _ fun p => ?_
    by_cases h0 : φ p.1 = 0 ∨ ψ p.2 = 0
    · rcases h0 with h0 | h0 <;> simp only [h0, zero_mul, mul_zero] <;> exact continuous_const
    · push Not at h0
      exact (continuous_const.mul (continuous_retainedGreen_min hP hσ (hφ.mem_H h0.1)
        (hψ.mem_H h0.2))).mul continuous_const

/-- **The retained form of nonnegative test functions is nonincreasing in time** (Lemma 3.4.4 for `φ, ψ ≥ 0`;
pointwise monotonicity of the kernel). -/
theorem antitone_retainedGreenForm_min (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) (hφ : IsTestFn φ) (hψ : IsTestFn ψ) (hφ0 : ∀ a, 0 ≤ φ a)
    (hψ0 : ∀ a, 0 ≤ ψ a) :
    Antitone fun t : ℝ≥0 => retainedGreenForm w (min t σ) φ ψ := by
  have hT : ∀ t : ℝ≥0, ((min t σ : ℝ≥0) : ℝ≥0∞) < ζ := fun t =>
    lt_of_le_of_lt (by exact_mod_cast min_le_right t σ) hσ
  have hζ : 0 < ζ := lt_of_le_of_lt zero_le hσ
  intro s t hst
  show retainedGreenForm w (min t σ) φ ψ ≤ retainedGreenForm w (min s σ) φ ψ
  rw [retainedGreenForm_eq_integral_prod hP hφ hψ (hT s),
    retainedGreenForm_eq_integral_prod hP hφ hψ (hT t)]
  refine integral_mono_ae (integrable_formIntegrand hP hφ hψ (hT t))
    (integrable_formIntegrand hP hφ hψ (hT s)) ?_
  filter_upwards [FieldMart.ae_ne_diag] with p hp
  by_cases h0 : φ p.1 = 0 ∨ ψ p.2 = 0
  · rcases h0 with h0 | h0 <;> simp [h0]
  · push Not at h0
    have hmono := retainedGreen_antitone_of_path hP hζ (hφ.mem_H h0.1) (hψ.mem_H h0.2) hp
      (min_le_min_right σ hst)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (hφ0 _)) (hψ0 _)

/-- **Bilinear expansion** `Q(c φ + d ψ) = c² Q(φ) + 2 c d Q(φ, ψ) + d² Q(ψ)`. -/
theorem retainedGreenEnergy_lin (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ)
    (hφ : IsTestFn φ) (hψ : IsTestFn ψ) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (c d : ℝ) :
    retainedGreenEnergy w T (fun a => c * φ a + d * ψ a) =
      c ^ 2 * retainedGreenEnergy w T φ + 2 * c * d * retainedGreenForm w T φ ψ +
        d ^ 2 * retainedGreenEnergy w T ψ := by
  simp only [retainedGreenEnergy_eq_form]
  rw [retainedGreenForm_eq_integral_prod hP (hφ.lin hψ c d) (hφ.lin hψ c d) hT,
    retainedGreenForm_eq_integral_prod hP hφ hφ hT, retainedGreenForm_eq_integral_prod hP hφ hψ hT,
    retainedGreenForm_eq_integral_prod hP hψ hψ hT]
  set μ := (volume : Measure ℂ).prod (volume : Measure ℂ)
  set I₁₁ := fun p : ℂ × ℂ => φ p.1 * retainedGreen w T p.1 p.2 * φ p.2
  set I₁₂ := fun p : ℂ × ℂ => φ p.1 * retainedGreen w T p.1 p.2 * ψ p.2
  set I₂₁ := fun p : ℂ × ℂ => ψ p.1 * retainedGreen w T p.1 p.2 * φ p.2
  set I₂₂ := fun p : ℂ × ℂ => ψ p.1 * retainedGreen w T p.1 p.2 * ψ p.2
  have h11 := integrable_formIntegrand hP hφ hφ hT
  have h12 := integrable_formIntegrand hP hφ hψ hT
  have h21 := integrable_formIntegrand hP hψ hφ hT
  have h22 := integrable_formIntegrand hP hψ hψ hT
  have hswap : ∫ p, I₂₁ p ∂μ = ∫ p, I₁₂ p ∂μ := by
    rw [← integral_prod_swap I₁₂]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [I₁₂, I₂₁, Prod.fst_swap, Prod.snd_swap, retainedGreen_comm w T p.2 p.1]
    ring
  have e : (fun p : ℂ × ℂ => (c * φ p.1 + d * ψ p.1) * retainedGreen w T p.1 p.2 *
      (c * φ p.2 + d * ψ p.2)) = fun p => c ^ 2 * I₁₁ p + c * d * I₁₂ p + c * d * I₂₁ p +
        d ^ 2 * I₂₂ p := funext fun p => by simp only [I₁₁, I₁₂, I₂₁, I₂₂]; ring
  have hA : Integrable (fun p => c ^ 2 * I₁₁ p + c * d * I₁₂ p) μ :=
    (h11.const_mul _).add (h12.const_mul _)
  have hB : Integrable (fun p => c ^ 2 * I₁₁ p + c * d * I₁₂ p + c * d * I₂₁ p) μ :=
    hA.add (h21.const_mul _)
  rw [e, integral_add hB (h22.const_mul _), integral_add hA (h21.const_mul _),
    integral_add (h11.const_mul _) (h12.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hswap]
  ring

end Form

end WangWu

end InteractingSLE
