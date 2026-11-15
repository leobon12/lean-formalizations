/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdxSlow

/-!
# The successor pair with version-indexed slow variables (ruling R119, decisions D1 and D3)

Packet PROVE-GW2-SDE (round 10). Decision D3: the slow stage variable is indexed by the member `n` of RELDET's
exhausting version family (`GW2Rd.exists_schedVersionsA`), the slow word and the slow stopped SDE hold eventually
in `n`, and the slow buffer fact is lossy with a loss tending to `0` in `n`. The near variables keep their index `m`.
Decision D1: the safe laws are asked only on time-ordered histories.

* `VPkgX` (`VPkg` with `slowVar l a n`), `VPkgXFamily`, `VPkgXFamily.at n` (the package of version `n`);
* `VPkgXSafe` (guarded safe laws, every version), `VWordsX` (near words; slow words eventually in `n`),
  **`retainedStoppedSDEStatementN_vpkgX`**;
* BUF's slow inputs in the indexed form: `VDriverIdN` (S1 for `u < min(gain, stop n)`), `VStopCoversN`
  (`∀ᵐ ξ ∈ gate, ∀ᶠ n, gain ξ ≤ stop n ξ`), with the round-6 shell choice;
* **`ae_slowBufferFactLossy_vpkgX`**: for every `j`, eventually in `n`, the lossy slow fact with loss `(j + 1)⁻¹`
  (loss set `{4^k · stop n < lifetime}` = `{stop n < gain}`; its kernel measure tends to `0` by
  `tendsto_measure_of_ae_eventually_notMem`);
* **`VPairInputsX`**, **`retainedComparisonsLossyX_vpkg`**: the lossy near binder and the lossy slow binder for J32.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdx

open ZhanGT4.UpMark GW2JDetR11 GW2Sde GW2Sdf GW2Sdg GW2Sdh GW2Sdi GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootL6 GW2TipSystem.RootN4

/-- **A stage-variable package with version-indexed slow variables** (`slowVar l a n`). -/
structure VPkgX {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) where
  nearFamily : List (EntryIdx c.Θ c.Q) → Ω → NearCrossingFamily.{u} c.κ
  nearCandidate : List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ
  nearVar : List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ → StageVar Ω
  slowShell : List (EntryIdx c.Θ c.Q) → ℕ → Ω → SlowShell
  slowVar : List (EntryIdx c.Θ c.Q) → ℕ → ℕ → StageVar Ω

/-- Version-indexed packages for every source setup and root. -/
abbrev VPkgXFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q), VPkgX c r

/-- **The package of version `n`.** -/
abbrev VPkgXFamily.at (V : VPkgXFamily.{u}) (n : ℕ) : VPkgFamily.{u} :=
  fun Ω _ _ c r =>
    { nearFamily := (V Ω c r).nearFamily
      nearCandidate := (V Ω c r).nearCandidate
      nearVar := (V Ω c r).nearVar
      slowShell := (V Ω c r).slowShell
      slowVar := fun l a => (V Ω c r).slowVar l a n }

/-- A package without version index, constant in `n`. -/
def _root_.InteractingSLE.Theorem14.GW2Sdi.VPkgFamily.toX (V : VPkgFamily.{u}) : VPkgXFamily.{u} :=
  fun Ω _ _ c r =>
    { nearFamily := (V Ω c r).nearFamily
      nearCandidate := (V Ω c r).nearCandidate
      nearVar := (V Ω c r).nearVar
      slowShell := (V Ω c r).slowShell
      slowVar := fun l a _ => (V Ω c r).slowVar l a }

theorem toX_at (V : VPkgFamily.{u}) (n : ℕ) : V.toX.at n = V := rfl

/-- **The guarded safe laws of a version-indexed package** (decisions D1, D3): every version is safe on
time-ordered histories. -/
structure VPkgXSafe (V : VPkgXFamily.{u}) : Prop where
  nearSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ∀ a : ℕ, ((V Ω c r).nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((V Ω c r).nearVar l n m a).IsSafe c.κ c.P ((V Ω c r).nearVar l n m a).record
  slowSafe : ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 →
      HistOrdered c r l → ∀ a : ℕ, ((V Ω c r).slowVar l a n).Generates (𝒢 := c.sigma r l) c.P ∧
        ((V Ω c r).slowVar l a n).IsSafe c.κ c.P ((V Ω c r).slowVar l a n).record

theorem VPkgXSafe.at {V : VPkgXFamily.{u}} (h : VPkgXSafe V) (n : ℕ) : VPkgSafeT (V.at n) :=
  ⟨h.nearSafe, h.slowSafe n⟩

theorem vpkgXSafe_toX {V : VPkgFamily.{u}} (h : VPkgSafeT V) : VPkgXSafe V.toX :=
  ⟨h.nearSafe, fun _ => h.slowSafe⟩

/-- **The words of a version-indexed package** (decision D3): the near words, and the slow words eventually in
`n`. -/
structure VWordsX (D : ConstructionFamily.{u}) (V : VPkgXFamily.{u}) (lam : NearDil.{u}) : Prop where
  nearWord : FrameNNearWord D ((V.at 0).frameN lam)
  slowWord : FrameNSlowWordN D fun n => (V.at n).frameN lam

/-- **The SDE half for a version-indexed package** (decisions D1, D3; Theorems 1.2–1.3, R48): the near half for
version `0` (the near data do not depend on the version) and the slow half eventually in `n`. -/
theorem retainedStoppedSDEStatementN_vpkgX (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) {D : ConstructionFamily.{u}}
    (V : VPkgXFamily.{u}) (lam : NearDil.{u})
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hord : AliveOrdered D) (hV : VPkgXSafe V) (hW : VWordsX D V lam) :
    RetainedStoppedSDEStatementN D (comparisonFamilyN ((V.at 0).frameN lam))
      fun n => comparisonFamilyN ((V.at n).frameN lam) :=
  ⟨retainedStoppedNearSDE_of_safeT h12p₀ h13₀ h13 D _ hord
      (fun Ω _ _ c r l ω => nearRootScale_ne_zero r.2 (hlam Ω c r l ω)) hV.nearSafe hW.nearWord,
    retainedStoppedSlowSDEN_of_safeT h12p₀ h13₀ h13 D _ hord (fun _ _ _ _ _ r => rootScale_ne_zero r.2)
      (fun n => hV.slowSafe n) hW.slowWord⟩

/-! ### BUF's slow inputs in the indexed form -/

section Inputs

variable (V : VPkgXFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **S1 for version `n`** (decision D3): on the retained gate, J32's centred reads are the version's relative
driver for `u < min(gain, stop n)`. -/
def VDriverIdN (n : ℕ) : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ u : ℝ≥0, u < rootGain c r l a ξ →
    (u : ℝ≥0∞) < ((V Ω c r).slowVar l a n).stop ξ →
    GW2Bf.j32Read c r l a (rootHistCap c r l a ξ + u) ξ - GW2Bf.j32Read c r l a (rootHistCap c r l a ξ) ξ =
      ((V Ω c r).slowVar l a n).R u ξ

/-- **S3 in the indexed form** (decision D3): on the retained gate, eventually in `n`, the version's stop dominates
the gain up to the buffer. -/
def VStopCoversN : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ᶠ n in atTop, (rootGain c r l a ξ : ℝ≥0∞) ≤ ((V Ω c r).slowVar l a n).stop ξ

end Inputs

/-- Round 6's S1 gives the indexed one. -/
theorem vDriverIdN_of_vDriverId {V : VPkgXFamily.{u}} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {a n : ℕ}
    (h : VDriverId (V.at n) Ω c r l a) : VDriverIdN V Ω c r l a n :=
  h.mono fun _ hξ hG u hu _ => hξ hG u hu

/-- Round 6's S3 for every version gives the indexed one. -/
theorem vStopCoversN_of_vStopCovers {V : VPkgXFamily.{u}} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {a : ℕ}
    (h : ∀ n, VStopCovers (V.at n) Ω c r l a) : VStopCoversN V Ω c r l a :=
  (ae_all_iff.2 h).mono fun _ hξ hG => Eventually.of_forall fun n => hξ n hG

/-- **The lossy slow buffer facts for J32, eventually in the version index** (decision D3; PROVE-GW2-BUF's slow
proof with the version's driver and stop): at P-a.e. alive history, for every `j`, for all large `n`, the slow fact
of version `n` holds off the loss set `{4^{r.2} · stop n < lifetime}`, whose kernel measure is below `(j + 1)⁻¹`. -/
theorem ae_slowBufferFactLossy_vpkgX (h13 : Exist.Theorem13Statement.{u}) (V : VPkgXFamily.{u}) (lam : NearDil.{u})
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hmeas : HistOrdered c r l → ∀ n, Measurable ((V Ω c r).slowVar l a n).stop)
    (hdrv : ∀ n, VDriverIdN V Ω c r l a n) (hstop : VStopCoversN V Ω c r l a)
    (hshell : VShellChoice (V.at 0) Ω c r l a) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
      ∀ j : ℕ, ∀ᶠ n in atTop,
        SlowBufferFactLossy ((comparisonFamilyN ((V.at n).frameN lam) Ω c r).slow l a ω)
          (condExpKernel c.P (c.sigma r l) ω) (RootJ31.sourceDriftBound c r) (RootJ32.sourceSample c r l a)
          ((j : ℝ≥0∞) + 1)⁻¹ := by
  by_cases hord : HistOrdered c r l
  swap
  · exact Eventually.of_forall fun ω halive => absurd (RootJ32.alive_spec c r l ω halive).2.2 hord
  have hv₀ := GW2Bf.v0_le_historyTime c r l hord
  have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hG : MeasurableSet[c.sigma r l] (rootGate c r l) := RootK32.measurableSet_sourceBuffer_gate c r l
  have hSm : Measurable (RootJ32.sourceSample c r l a) := RootJ32.measurable_sourceSample c r l a
  set B : ℕ → Set Ω := fun n =>
    {ξ | (4 : ℝ≥0∞) ^ r.2 * ((V Ω c r).slowVar l a n).stop ξ < (RootJ32.sourceSample c r l a ξ).1} with hBdef
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    measurableSet_lt ((hmeas hord n).const_mul _) (measurable_fst.comp hSm)
  have hgood : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ n, ξ ∉ B n →
      (RootJ32.sourceSample c r l a ξ).1 ≤
        ((V.at n).frameN lam Ω c r).base.stop (((V.at n).frameN lam Ω c r).base.slowVar l a) ξ ∧
      ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
        (RootJ32.sourceSample c r l a ξ).2 q = GW2Bf.histStart c r l ξ +
          ((V.at n).frameN lam Ω c r).base.drv l (((V.at n).frameN lam Ω c r).base.slowVar l a) q ξ := by
    filter_upwards [GW2Bf.ae_j32Start_eq_histStart h13 c r l hv₀, ae_all_iff.2 hdrv] with ξ hst hd hξG n hξB
    have hlife : (RootJ32.sourceSample c r l a ξ).1 ≤ (4 : ℝ≥0∞) ^ r.2 * ((V Ω c r).slowVar l a n).stop ξ :=
      not_lt.1 hξB
    refine ⟨(hlife.trans_eq (vpkg_slow_stop' (V.at n) lam Ω c r l a ξ).symm), fun q hq => ?_⟩
    have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 :=
      lt_of_le_of_lt zero_le (hq.trans_eq (RootJ32.sourceSample_fst c r l a ξ))
    have hu : (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 < rootGain c r l a ξ :=
      div_four_pow_lt r.2 (by rw [← GW2Bf.j32Sample_fst]; exact hq)
    have hgs : (rootGain c r l a ξ : ℝ≥0∞) ≤ ((V Ω c r).slowVar l a n).stop ξ := by
      rw [GW2Bf.j32Sample_fst] at hlife
      exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ (by norm_num)) (ENNReal.pow_ne_top (by norm_num))).1 hlife
    have hus : ((((q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 : ℝ≥0)) : ℝ≥0∞) < ((V Ω c r).slowVar l a n).stop ξ :=
      (ENNReal.coe_lt_coe.2 hu).trans_le hgs
    rw [GW2Bf.j32Sample_snd c r l a ξ hq, hst a hlive, hd n hξG _ hu hus, vpkg_slow_drv (V.at n) lam Ω c r l a q ξ]
  have hev : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ᶠ n in atTop, ξ ∉ B n := by
    filter_upwards [hstop] with ξ h hξG
    filter_upwards [h hξG] with n hn hB
    have hle : (RootJ32.sourceSample c r l a ξ).1 ≤ (4 : ℝ≥0∞) ^ r.2 * ((V Ω c r).slowVar l a n).stop ξ := by
      rw [GW2Bf.j32Sample_fst]
      gcongr
    exact absurd hB (not_lt.2 hle)
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hgood, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hev,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq h𝒢 (GW2Bf.measurable_histStart c r l),
    KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hG, hshell] with ω hgd hevk hfz hGc hsh halive j
  obtain ⟨hcov, hold, -⟩ := RootJ32.alive_spec c r l ω halive
  have hωG : ω ∈ rootGate c r l := ⟨hcov, hold⟩
  have hGξ : ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ξ ∈ rootGate c r l := ae_iff.2 (hGc.1 hωG)
  have hlim := tendsto_measure_of_ae_eventually_notMem (μ := condExpKernel c.P (c.sigma r l) ω) hBm
    (by filter_upwards [hevk, hGξ] with ξ h hξ using h hξ)
  have hpos : (0 : ℝ≥0∞) < ((j : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
  filter_upwards [(tendsto_order.1 hlim).2 _ hpos] with n hn
  obtain ⟨hshf, hst⟩ := hsh halive
  refine ⟨hshf.1, hshf.2.1, hshf.2.2, B n, hn.le, ?_, ?_⟩
  · filter_upwards [hgd, hGξ] with ξ h hξG hξN
    show _ ≤ (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.stop ξ
    rw [slowData_stop]
    exact (h hξG n hξN).1
  · filter_upwards [hgd, hfz, hGξ] with ξ h hξ hξG hξN q hq
    show _ = (((V.at n).frameN lam Ω c r).base.slowData l a ω).start +
      (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.W q ξ
    rw [(h hξG n hξN).2 q hq, hξ, slowData_W]
    exact congrArg (· + _) hst.symm

/-! ### The successor pair for J32 -/

/-- **The named inputs of the successor pair for J32** (decisions D1, D3): version-indexed packages `V k` (near
candidates with loss `(k + 1)⁻¹`; the slow inputs for `V 0` in the indexed form). -/
structure VPairInputsX (V : ℕ → VPkgXFamily.{u}) (lam : NearDil.{u}) : Prop where
  lam_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0
  safe : ∀ k : ℕ, VPkgXSafe (V k)
  words : ∀ k : ℕ, VWordsX RootJ32.constructionFamily (V k) lam
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), VNearImgL ((V k).at 0) lam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a n : ℕ,
      VDriverIdN (V 0) Ω c r l a n
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      VStopCoversN (V 0) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      VShellChoice ((V 0).at 0) Ω c r l a

/-- **The successor pair for J32: the lossy near binder and the lossy slow binder** (decisions D1, D3; R113, R114;
Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossyX_vpkg (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (V : ℕ → VPkgXFamily.{u})
    (lam : NearDil.{u}) (hV : VPairInputsX V lam) :
    RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsLossyStatement RootJ32.constructionFamily.{u} := by
  have hsde : ∀ k, RetainedStoppedSDEStatementN RootJ32.constructionFamily
      (comparisonFamilyN (((V k).at 0).frameN lam)) fun n => comparisonFamilyN (((V k).at n).frameN lam) :=
    fun k => retainedStoppedSDEStatementN_vpkgX h12p₀ h13₀ h13 (V k) lam hV.lam_ne aliveOrdered_rootJ32 (hV.safe k)
      (hV.words k)
  refine retainedComparisonsLossyN_of_stoppedSDE_buffer RootJ32.constructionFamily
    (fun k => comparisonFamilyN (((V k).at 0).frameN lam)) (fun n => comparisonFamilyN (((V 0).at n).frameN lam))
    (fun k => (hsde k).near) ?_ (hsde 0).slow ?_
  · intro Ω _ _ c r l k
    filter_upwards [(hsde k).near Ω c r l,
      nearImgPathLossy_vpkg ((V k).at 0) lam Ω c r l (hV.lam_ne Ω c r l) (hV.nearImg k Ω c r l)]
      with ω hs hi halive n
    filter_upwards [hs halive n, hi halive n] with m h1 h2
    exact nearBufferFactLossy_of_imgPath h1 (RootJ32.experiment_reach_measurable c r l _) h2
  · intro Ω _ _ c r k l hl a
    exact ae_slowBufferFactLossy_vpkgX h13 (V 0) lam Ω c r l a
      (fun hTO n => ((hV.safe 0).slowSafe n Ω c r k l hl hTO a).2.measurable_stop) (hV.driverId Ω c r k l hl a)
      (hV.stopCovers Ω c r k l hl a) (hV.shell Ω c r k l hl a)

end InteractingSLE.Theorem14.GW2Sdx
