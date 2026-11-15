/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNCompWire
import InteractingSLE.Spec.Sec5.StagedS7Rep

/-!
# Proposition 5.9 after the last switch, for arbitrary angle flags: the pathwise facts of the flag word

Packet PROVE-STAGED-NODEPATHS. PROVE-STAGED-S7 proved, for PIECES' alternating root flags, that the restarted word
of the candidate after its last switch starts strictly ordered, is killed at its far (junction) marks with left
limits, and has a generating trace up to its lifetime. Here the same argument is run for the flag candidate of
arbitrary angle flags `fl` (PROVE-STAGED-NODECOMP's `candWF`, `candEgF`, `candTsF`, `candFiltF`):

* `strictMono_candTsF`: the flag candidate's switch times are positive and strictly increasing;
* `ae_of_ae_prod_cond`: an almost-sure statement about the first factor of `μ[|A] ⊗ ν` holds `μ`-almost surely on
  `A` (descent from the conditioned product);
* `FlagExitWord`: the restarted flag word `consAlt (bornL κ fl) (nodeρL0 κ c θ₀) ℓ` satisfies Zhan's strip
  hypotheses for its left span, or (reflected) for its right span — the word-level input of the far exit;
* **`flagPaths_of_exitWord`**: `FlagPaths` (strict start, far kill with left limits, trace up to the lifetime,
  almost surely on the alive event) for every flag list, depth `ℓ ≥ 1` and counterflow time `s > 0` whose restarted
  word is a `FlagExitWord`. The proof is PROVE-STAGED-S7's (`exists_isKilledStageRep_cand`): the word entrance
  `exists_isWordEntrance_candF` on the conditioned glued space, the staged far exit `ae_restartExitL` /
  `ae_restartExitR`, then S7's deterministic `strictAnti_s6Start`, `isKilledAtFarLim_s6`,
  `exists_isGeneratingTrace_s3W`, and descent to the glued space.

Conditional helpers with distinct names; they replace no source theorem. R48: the only named input is
`h44 : Theorem12ParamCond44Statement` (R74, through PROVE-STAGED-S4/S5/S6 and NODECOMP); nothing here uses Theorem
1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNPath

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q Word49 Theta StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged MartChar.RealFlow
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target StagedGlue StagedDepth Prop59Pieces StagedRepLater
open Prop59Stage Prop59System Prop59NodeTree StagedNComp StagedS7
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open StagedFinal (imgStageRhoL imgStageRhoR)

/-! ### The flag candidate's switch times -/

section Times

variable {fl : ℕ → Bool} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}

/-- **The flag candidate's switch times are positive and strictly increasing.** -/
theorem strictMono_candTsF (hv : IsValid ℓ t) :
    (∀ j : Fin ℓ, 0 < candTsF fl ℓ t (j + 1) ∧ candTsF fl ℓ t (j + 1) ≤ (lastO ℓ t : ℝ)) ∧
      StrictMono fun j : Fin ℓ => candTsF fl ℓ t (j + 1) := by
  refine ⟨fun j => ⟨?_, (candTsF_bounds hv j).2⟩, fun j j' hjj => ?_⟩
  · rw [candTsF_succ hv j]
    exact_mod_cast oTime_pos hv j
  · simp only [candTsF_succ hv]
    rw [oTime_eq (hv.2 j).2.2, oTime_eq (hv.2 j').2.2]
    exact decode_strictMono (hv.2 j').2.1 (hv.1 hjj)

end Times

/-! ### Descent from the conditioned product -/

section Descent

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} [IsFiniteMeasure μ]
  {ν : Measure β} [IsProbabilityMeasure ν] {A : Set α}

/-- **Descent from `μ[|A] ⊗ ν`**: a statement about the first factor that holds almost surely under the conditioned
product holds `μ`-almost surely on `A`. -/
theorem ae_of_ae_prod_cond (hA : MeasurableSet A) {Q : α → Prop}
    (h : ∀ᵐ p ∂((μ[|A]).prod ν), p.1 ∈ A → Q p.1) : ∀ᵐ x ∂μ, x ∈ A → Q x := by
  have h1 : ∀ᵐ x ∂μ[|A], x ∈ A → Q x :=
    (Measure.ae_ae_of_ae_prod h).mono fun x hx => Filter.eventually_const.1 hx
  have h2 : ∀ᵐ x ∂μ.restrict A, x ∈ A → Q x :=
    (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2 (measure_ne_top μ A))).1 h1
  exact ((ae_restrict_iff' hA).1 h2).mono fun x hx hxA => hx hxA hxA

end Descent

/-! ### The word-level input of the far exit -/

/-- **The restarted flag word satisfies Zhan's strip hypotheses on one side**: the word
`consAlt (bornL κ fl) (nodeρL0 κ c θ₀) ℓ`, `consAlt (bornR κ fl) (nodeρR0 κ c θ₀) ℓ` (first angle
`θ₀ = flagAngle (fl 0)`) is a stage word for its left span, or its reflection is a stage word (right span). -/
def FlagExitWord (κ : ℝ) (c : BoundaryWord) (fl : ℕ → Bool) (ℓ : ℕ) : Prop :=
  IsStageWordN κ (consAlt (bornL κ fl) (nodeρL0 κ c (flagAngle (fl 0))) ℓ)
      (consAlt (bornR κ fl) (nodeρR0 κ c (flagAngle (fl 0))) ℓ) ∨
    IsStageWordN κ (consAlt (bornR κ fl) (nodeρR0 κ c (flagAngle (fl 0))) ℓ)
      (consAlt (bornL κ fl) (nodeρL0 κ c (flagAngle (fl 0))) ℓ)

/-! ### The pathwise facts of a flag word -/

section Paths

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

/-- **The pathwise facts of the flag candidate's restarted word** (PROVE-STAGED-S7's items 1 and 3 for arbitrary
flags): almost surely on the alive event of the last switch, the restarted start is strictly ordered, the restarted
word is killed at its far (junction) marks with left limits, and its driver has a generating trace up to the
restarted lifetime — for every flag list whose restarted word satisfies Zhan's strip hypotheses on one side. -/
theorem flagPaths_of_exitWord (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) (hℓ : 0 < ℓ) {s : ℝ≥0} (hs : 0 < s)
    (hw : FlagExitWord κ (sourceWord (x₀ := x₀) hκ hb) fl ℓ) :
    FlagPaths x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s := by
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  unfold FlagPaths
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  obtain ⟨us, hus, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  set Wc := candWF x₀ h44 hκ hκ4 hb h fl (ℓ + 1) t with hWc
  set Eg := candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 (ℓ + 1) t s with hEgdef
  set τ : ℝ := (lastO (ℓ + 1) t : ℝ) with hτ
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set A := s3Alive s Wc Eg τ with hAdef
  set 𝓐 := candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs with h𝓐
  have hAmeas : MeasurableSet A :=
    𝓐.le 0 _ (measurableSet_s3Alive_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0)
  by_cases hA0 : μ A = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hA0] with p hp hpA
    exact absurd hpA hp
  set μA := μ[|A] with hμA
  have hμA1 : IsProbabilityMeasure μA := cond_isProbabilityMeasure hA0
  obtain ⟨P₀, hP₀, 𝓦, B, hB, hBc, hEnt⟩ :=
    exists_isWordEntrance_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hus hv hs hA0
  have := hP₀
  refine ae_of_ae_prod_cond (ν := P₀) hAmeas ?_
  set xLc := flowLineXL c.fn c.jumps 0 with hxLc
  set xRc := flowLineXR c.fn c.jumps 0 with hxRc
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 (ℓ + 1) t s
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hxLs : StrictAnti xLc := fun i i' hii => Theorem14.GW0.flowLineXL_lt c.fn c.jumps 0 hii
  have hxRs : StrictMono xRc := fun i i' hii => Theorem14.GW0.flowLineXR_lt c.fn c.jumps 0 hii
  obtain ⟨hτs, hτm⟩ := strictMono_candTsF (fl := fl) hv
  have hτs' : ∀ k : Fin (ℓ + 1), 0 ≤ candTsF fl (ℓ + 1) t (k + 1) ∧ candTsF fl (ℓ + 1) t (k + 1) ≤ τ := fun k =>
    ⟨(hτs k).1.le, (hτs k).2⟩
  have hK := isKilledWord_s6 (xL := xLc) (xR := xRc) hEg hF.2.1 hF.1 hF.2.2.2 hF.2.2.1 hτs' hτm.monotone
  have hρL : (fun i => imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ c.fn c.jumps 0 (flagAngle (fl 0)))
      (fun j => candAngF fl (ℓ + 1) t j - candAngF fl (ℓ + 1) t 0) (ℓ + 1) (treeIdx (ℓ + 1) _ i)) =
      consAlt (bornL κ fl) (nodeρL0 κ c (flagAngle (fl 0))) (ℓ + 1) :=
    funext fun i => imgStageRhoL_treeIdxF hκ c hv i
  have hρR : (fun j => imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ c.fn c.jumps 0 (flagAngle (fl 0)))
      (fun j => candAngF fl (ℓ + 1) t j - candAngF fl (ℓ + 1) t 0) (ℓ + 1) (treeIdx (ℓ + 1) _ j)) =
      consAlt (bornR κ fl) (nodeρR0 κ c (flagAngle (fl 0))) (ℓ + 1) :=
    funext fun j => imgStageRhoR_treeIdxF hκ c hv j
  rw [hρL, hρR] at hEnt
  -- the filtration
  set 𝓖 := usualAugmentation 𝓐 μA with h𝓖
  have hle : 𝓐 ≤ 𝓖 := Ito.le_usualAugmentation 𝓐 μA
  have hWa : StronglyAdapted 𝓖 (s3W s Wc Eg τ) := fun r =>
    (stronglyAdapted_s3W_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r).mono (hle r)
  have hVLa : ∀ i, StronglyAdapted 𝓖 (s6VL xLc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ i) := fun i r =>
    (stronglyAdapted_s6VL_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs xLc i r).mono (hle r)
  have hVRa : ∀ k, StronglyAdapted 𝓖 (s6VR xRc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ k) := fun k r =>
    (stronglyAdapted_s6VR_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs xRc k r).mono (hle r)
  have hζq : ∀ r : ℝ≥0, MeasurableSet[𝓖 r] {p | (r : ℝ≥0∞) < s3ζ s Wc Eg τ p} := fun r =>
    hle r _ (measurableSet_lt_s3ζ_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r)
  have hTq : ∀ q : ℝ≥0, MeasurableSet[WholeField.prodFiltration 𝓖 𝓦 q]
      {p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) | (q : ℝ≥0∞) < s3ζ s Wc Eg τ p.1} := fun q =>
    WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hζq q, rfl⟩
  have hT0 : ∀ p : (Ω × HistorySpace 0 0) × (ℕ → ℝ), 0 < s3ζ s Wc Eg τ p.1 := fun p =>
    StagedS6.zero_lt_arcζ (fun p => StagedS5.s3Start_lt_kLife' hEg τ p) p.1
  -- almost sure facts on the first factor
  have hgood : ∀ᵐ p ∂μA, p ∈ A ∧ p ∈ Eg ∧ p.2 ∈ goodSet49 s := by
    filter_upwards [ae_cond_mem hAmeas,
      cond_absolutelyContinuous.ae_le (ae_goodSet49_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf hs),
      cond_absolutelyContinuous.ae_le (ae_good_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf (ℓ + 1) t hv hs)]
      with p hpA hy hgc
    exact ⟨hpA, hgc.1, hy⟩
  have hgood' : ∀ᵐ p ∂(μA.prod P₀), p.1 ∈ A ∧ p.1 ∈ Eg ∧ p.1.2 ∈ goodSet49 s :=
    Measure.quasiMeasurePreserving_fst.ae hgood
  -- strict start and threshold at time `0`
  have hstr : ∀ p : Ω × HistorySpace 0 0, p ∈ A → p.2 ∈ goodSet49 s →
      StrictAnti (fun i => s6VL xLc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ i 0 p) ∧
        StrictMono (fun k => s6VR xRc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ k 0 p) := fun p hp hy =>
    ⟨strictAnti_s6Start hEg hp hy hF.2.1 hxLs hτs hτm, strictMono_s6Start hEg hp hy hF.2.2.2 hxRs hτs hτm⟩
  have hO : ∀ p : Ω × HistorySpace 0 0, IsOrderedForceWord
      (fun i => s6VL xLc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ i 0 p)
      (fun k => s6VR xRc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ k 0 p) :=
    isOrderedForceWord_s6Start hEg hF.2.1 hF.1 hF.2.2.2 hF.2.2.1 hτs' hτm.monotone
  have hthr0 : ∀ p : Ω × HistorySpace 0 0, p ∈ A → p.2 ∈ goodSet49 s →
      ¬ ForceWord.ThresholdCondition (consAlt (bornL κ fl) (nodeρL0 κ c (flagAngle (fl 0))) (ℓ + 1))
        (consAlt (bornR κ fl) (nodeρR0 κ c (flagAngle (fl 0))) (ℓ + 1))
        (s3W s Wc Eg τ 0 p) (fun i => s6VL xLc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ i 0 p)
        (fun k => s6VR xRc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ k 0 p) := by
    intro p hp hy
    obtain ⟨hsA, hsM⟩ := hstr p hp hy
    have hW0 : s3W s Wc Eg τ 0 p = 0 := StagedS6.arcW_zero p
    rw [hW0]
    exact not_threshold_consAlt hκ hκ4 fl (Nat.succ_pos ℓ) _ _ hsA hsM ((hO p).2.1 _) ((hO p).2.2.2 _)
  have hthr : ∀ᵐ p ∂(μA.prod P₀),
      ¬ ForceWord.ThresholdCondition (consAlt (bornL κ fl) (nodeρL0 κ c (flagAngle (fl 0))) (ℓ + 1))
        (consAlt (bornR κ fl) (nodeρR0 κ c (flagAngle (fl 0))) (ℓ + 1))
        (s3W s Wc Eg τ 0 p.1) (fun i => s6VL xLc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ i 0 p.1)
        (fun k => s6VR xRc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ k 0 p.1) := by
    filter_upwards [hgood'] with p hp
    exact hthr0 p.1 hp.1 hp.2.2
  -- the exit of the full staged arc through a far span
  have hγf : ∀ p : (Ω × HistorySpace 0 0) × (ℕ → ℝ),
      IsKilledArc (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) := fun p =>
    isKilledArc_gCurve hEg p.1
  have hζ' : ∀ (p : (Ω × HistorySpace 0 0) × (ℕ → ℝ)) (r : ℝ≥0), (r : ℝ≥0∞) < s3ζ s Wc Eg τ p.1 ↔
      ((s3Start s Wc Eg τ p.1 + r : ℝ≥0) : WithTop ℝ≥0) <
        kLife (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) := fun p r =>
    lt_arcζ_iff.trans ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  have hWk : ∀ (p : (Ω × HistorySpace 0 0) × (ℕ → ℝ)) (r : ℝ≥0), (r : ℝ≥0∞) < s3ζ s Wc Eg τ p.1 →
      s3W s Wc Eg τ r p.1 = kW (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1)
        (s3Start s Wc Eg τ p.1 + r) -
        kW (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) (s3Start s Wc Eg τ p.1) :=
    fun p r hr => arcW_of_lt hr
  have hnH : ∀ᵐ p ∂(μA.prod P₀), ∀ (T : ℝ≥0) (z : ℂ),
      (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) →
      Tendsto (kTrace (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1)) (𝓝[<] T) (𝓝 z) →
        z ∉ H := by
    filter_upwards [hgood'] with p hp T z hT hz
    exact notMem_H_of_tendsto_gCurve hp.2.1 (hEg p.1 hp.2.1) hT hz
  have hexit : ∀ᵐ p ∂(μA.prod P₀), ∃ T : ℝ≥0,
      (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) ∧
      ∃ x₁ : ℝ, Tendsto (kTrace (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1)) (𝓝[<] T)
          (𝓝 (x₁ : ℂ)) ∧
        (x₁ < GlueImg.imgMarkL xLc (cfDrv0 s p.1.2) s (Fin.last _) ∨
          GlueImg.imgMarkR xRc (cfDrv0 s p.1.2) s (Fin.last _) < x₁) := by
    rcases hw with hwN | hwN
    · have hw := isStageWord_of_N (m := rootNL c + ℓ) hwN
      have hfar : ∀ᵐ p ∂(μA.prod P₀), ∀ r : ℝ≥0, (r : ℝ≥0∞) < s3ζ s Wc Eg τ p.1 →
          s6VL xLc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ (Fin.last (rootNL c + ℓ)) r p.1 -
              s3W s Wc Eg τ r p.1 =
            -kImg (fun r => -kPath (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) r)
                (-GlueImg.imgMarkL xLc (cfDrv0 s p.1.2) s (Fin.last _)) (s3Start s Wc Eg τ p.1 + r) -
              kW (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) (s3Start s Wc Eg τ p.1 + r) := by
        filter_upwards [hgood'] with p hp r hr
        exact s6VL_far_sub hEg hp.1 hτs' (by simp only [Fin.val_last, rootNL]; omega) hr
      have ha : ∀ᵐ p ∂(μA.prod P₀), GlueImg.imgMarkL xLc (cfDrv0 s p.1.2) s (Fin.last _) ≤ 0 := by
        filter_upwards [hgood'] with p hp
        obtain ⟨-, -, hjL, -, -⟩ := hEg p.1 hp.2.1
        exact imgMarkL_nonpos hF.2.1 hjL _
      have hX := ae_restartExitL (m := rootNL c + ℓ) hκ hκ4.le hw.2.1
        (Prop59Tips.abs_charge_lt_of_sum hκ hκ4 _ hw.1)
        hB hBc (Sec7.PhaseSelFull.stronglyAdapted_fst hWa)
        (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
        (fun k => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa k)) hTq hT0 hEnt
        (fun p r hr0 hr i => hK.sepL p.1 r hr0 hr i) (fun p r hr0 hr k => hK.sepR p.1 r hr0 hr k) hthr hγf hζ' hWk
        hfar ha hnH
      filter_upwards [hX] with p hp
      obtain ⟨T, hT, x₁, hx₁, hlim⟩ := hp
      exact ⟨T, hT, x₁, hlim, Or.inl hx₁⟩
    · have hw := isStageWord_of_N (m := rootNR c + ℓ) hwN
      have hfar : ∀ᵐ p ∂(μA.prod P₀), ∀ r : ℝ≥0, (r : ℝ≥0∞) < s3ζ s Wc Eg τ p.1 →
          s6VR xRc (candTsF fl (ℓ + 1) t) (ℓ + 1) s Wc Eg τ (Fin.last (rootNR c + ℓ)) r p.1 -
              s3W s Wc Eg τ r p.1 =
            kImg (kPath (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1))
                (GlueImg.imgMarkR xRc (cfDrv0 s p.1.2) s (Fin.last _)) (s3Start s Wc Eg τ p.1 + r) -
              kW (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) (s3Start s Wc Eg τ p.1 + r) := by
        filter_upwards [hgood'] with p hp r hr
        exact s6VR_far_sub hEg hp.1 hτs' (by simp only [Fin.val_last, rootNR]; omega) hr
      have hb' : ∀ᵐ p ∂(μA.prod P₀), 0 ≤ GlueImg.imgMarkR xRc (cfDrv0 s p.1.2) s (Fin.last _) := by
        filter_upwards [hgood'] with p hp
        obtain ⟨-, -, -, hjR, -⟩ := hEg p.1 hp.2.1
        exact imgMarkR_nonneg hF.2.2.2 hjR _
      have hX := ae_restartExitR (n := rootNR c + ℓ) hκ hκ4.le hw.2.1
        (Prop59Tips.abs_charge_lt_of_sum hκ hκ4 _ hw.1)
        hB hBc (Sec7.PhaseSelFull.stronglyAdapted_fst hWa)
        (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
        (fun k => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa k)) hTq hT0 hEnt
        (fun p r hr0 hr i => hK.sepL p.1 r hr0 hr i) (fun p r hr0 hr k => hK.sepR p.1 r hr0 hr k) hthr hγf hζ' hWk
        hfar hb' hnH
      filter_upwards [hX] with p hp
      obtain ⟨T, hT, x₁, hx₁, hlim⟩ := hp
      exact ⟨T, hT, x₁, hlim, Or.inr hx₁⟩
  -- the pathwise facts
  filter_upwards [hgood', hexit] with p hp hX _
  obtain ⟨hpA, hpE, hy⟩ := hp
  obtain ⟨hsA, hsM⟩ := hstr p.1 hpA hy
  obtain ⟨-, -, hjL, hjR, -⟩ := hEg p.1 hpE
  obtain ⟨T, hT, x₁, hlim, hside⟩ := hX
  have hexit' : ∀ T' : ℝ≥0,
      (T' : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) →
      ∃ x₂ : ℝ, Tendsto (kTrace (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1)) (𝓝[<] T')
          (𝓝 (x₂ : ℂ)) ∧
        (x₂ < GlueImg.imgMarkL xLc (cfDrv0 s p.1.2) s (Fin.last _) ∨
          GlueImg.imgMarkR xRc (cfDrv0 s p.1.2) s (Fin.last _) < x₂) := by
    intro T' hT'
    have hTT : T' = T := WithTop.coe_injective (hT'.trans hT.symm)
    subst hTT
    exact ⟨x₁, hlim, hside⟩
  have hx₁ : x₁ ≠ 0 := by
    rcases hside with h' | h'
    · linarith [imgMarkL_nonpos hF.2.1 hjL (Fin.last _)]
    · linarith [imgMarkR_nonneg hF.2.2.2 hjR (Fin.last _)]
  refine ⟨⟨hsA, hsM⟩, ?_, exists_isGeneratingTrace_s3W hEg p.1 hT hx₁ hlim⟩
  exact isKilledAtFarLim_s6 hEg hpA hF.2.1 hF.1 hF.2.2.2 hF.2.2.1 hτs' hτm.monotone (Nat.succ_pos ℓ) hsA hsM
    (by simp only [farL, rootNL, hc]; omega) (by simp only [farR, rootNR, hc]; omega) hexit'

end Paths

end InteractingSLE.Sec5.CrossCond.StagedNPath
