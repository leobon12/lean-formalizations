/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdyTop

/-!
# The successor pair with its inputs on the scaled cover (review defect N1)

Packet PROVE-GW2-SDE (round 12; DECISIONS-FABLE-3: N1 is SDE's). The pair's near words and near facts must be asked on
the alive events of COVER's scaled family `withScaledCover J32 gap` (ruling R118: on the unscaled cover the near words
are false), and the conclusion is for the scaled family. Every proof is pointwise in the alive sample, and the scaled
family's experiment is J32's, so this is a re-typing:

* `J32S gap`, `alive_scaled_subset` (scaled-alive ⊆ J32-alive), **`aliveOrdered_scaled`**;
* `VNearImgOn` (`GW2Sdi.VNearImgL` on any alive set), `nearImgPathLossy_on`;
* **`ae_slowBufferCut_on`**: D3a's cut slow facts (`GW2Sdy.ae_slowBufferCut_vpkgX`) on any alive set inside J32's,
  with the shells asked only there (F1's `≤` drift clause);
* **`VPairInputsXCS`** (`words`, `nearImg`, `shell` on the scaled family), **`retainedComparisonsLossyXCS_vpkg`**
  (both lossy binders for the scaled family);
* **`theorem14Statement_J32_scaled_vpkgXCS`**: Theorem 1.4 from the successor top
  (`GW2Sdy.theorem14Statement_J32_scaled_lossyS`) and this pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdz

open ZhanGT4.UpMark GW2JDetR11 GW2Sde GW2Sdf GW2Sdg GW2Sdh GW2Sdi GW2Sdx GW2Sdy GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4 GW2TipSystem.RootV7 Sec5

/-- COVER's scaled family over J32. -/
abbrev J32S (gap : RootCv.GapFamily.{u}) : ConstructionFamily.{u} :=
  RootCv.withScaledCover RootJ32.constructionFamily gap

/-- **Scaled-alive histories are J32-alive.** -/
theorem alive_scaled_subset (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) {ω : Ω}
    (h : ω ∈ ((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l) :
    ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l :=
  aliveTests_mono (scaledCoverEvent_subset_rootJ32 gap Ω c r) _ _ l h

/-- **Alive histories of the scaled family are time-ordered** (decision D1). -/
theorem aliveOrdered_scaled (gap : RootCv.GapFamily.{u}) : AliveOrdered (J32S gap) :=
  fun Ω _ _ c r l => Eventually.of_forall fun ω h =>
    (RootJ32.alive_spec c r l ω (alive_scaled_subset gap Ω c r l h)).2.2

/-! ### The near facts on any alive set -/

section Near

variable (V : VPkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))

/-- **`GW2Sdi.VNearImgL` on an alive set `A`** (the lossy near facts for J32 in terms of the near stage variables). -/
def VNearImgOn (ε : ℝ≥0∞) (A : Set Ω) : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ A →
    ∀ n : ℕ, ∀ᶠ m in atTop, ∃ N : Set Ω, condExpKernel c.P (c.sigma r l) ω N ≤ ε ∧
      ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ξ ∉ N →
      0 < (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
        ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).stop ξ ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) = (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
          ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).stop ξ →
        v < (n : ℝ≥0) →
        imgState ((V Ω c r).nearFamily l ω).xL ((V Ω c r).nearFamily l ω).xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * lam Ω c r l ω * ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).R
            (s / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ))
          v ∉ nearBuffer ((V Ω c r).nearFamily l ω) n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) →
        (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
          ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).stop ξ →
        imgState ((V Ω c r).nearFamily l ω).xL ((V Ω c r).nearFamily l ω).xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * lam Ω c r l ω * ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).R
            (s / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ))
          t ∈ nearTarget ((V Ω c r).nearFamily l ω) →
        RootJ32.sourceSample c r l ((V Ω c r).nearCandidate l ω n m) ξ ∈ RootD25.reachSet

end Near

/-- The near facts on an alive set give the near path facts there (`GW2Sdi.nearImgPathLossy_vpkg` on `A`). -/
theorem nearImgPathLossy_on (V : VPkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    {ε : ℝ≥0∞} {A : Set Ω} (hlam : ∀ ω, lam Ω c r l ω ≠ 0) (h : VNearImgOn V lam Ω c r l ε A) :
    ∀ᵐ ω ∂c.P, ω ∈ A →
      ∀ n, ∀ᶠ m in atTop, NearImgPathLossy ((comparisonFamilyN (V.frameN lam) Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((RootJ32.constructionFamily Ω c).experiment r).data.sample l)
        (((RootJ32.constructionFamily Ω c).experiment r).data.reach l) n m ε := by
  filter_upwards [h] with ω hω halive n
  filter_upwards [hω halive n] with m hm
  obtain ⟨N, hN, hae⟩ := hm
  refine ⟨N, hN, ?_⟩
  filter_upwards [hae] with ξ hξ hξN
  obtain ⟨h0, hex, htg⟩ := hξ hξN
  have hW : (fun s => (((comparisonFamilyN (V.frameN lam) Ω c r).near l ω).dynamics n m).W s ξ) =
      fun s => (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * lam Ω c r l ω *
        ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).R
          (s / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ) :=
    funext fun s => vpkg_near_W V lam Ω c r l ω n m s ξ
  have hS := vpkg_near_stop V lam Ω c r l ω n m ξ (hlam ω)
  refine ⟨hS ▸ h0, fun v hv hvn => ?_, fun t htn ht htar => ?_⟩
  · rw [hW]
    exact hex v (hv.trans hS) hvn
  · rw [hW] at htar
    exact htg t htn (ht.trans_eq hS) htar

/-! ### D3a's cut slow facts on any alive set inside J32's -/

/-- **The cut slow facts on an alive set `A ⊆ alive_J32`** (`GW2Sdy.ae_slowBufferCut_vpkgX` with the shells asked
only on `A`). -/
theorem ae_slowBufferCut_on (h13 : Exist.Theorem13Statement.{u}) (V : VPkgXFamily.{u}) (lam : NearDil.{u})
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {A : Set Ω}
    (hA : ∀ ω ∈ A, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive
      ((RootJ32.constructionFamily Ω c).G r) l)
    (hmeas : HistOrdered c r l → ∀ n, Measurable ((V Ω c r).slowVar l a n).stop)
    (hdrv : ∀ n, VDriverIdN V Ω c r l a n) (hex : VStopExhaustsN V Ω c r l a) (C : ℝ)
    (hshell : ∀ᵐ ω ∂c.P, ω ∈ A →
      ShellFactLe c.κ C ((V Ω c r).slowShell l a ω) ∧ ((V Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω) :
    ∀ᵐ ω ∂c.P, ω ∈ A →
      (∀ n, SlowBufferFactCut ((comparisonFamilyN ((V.at n).frameN lam) Ω c r).slow l a ω)
        (condExpKernel c.P (c.sigma r l) ω) C (RootJ32.sourceSample c r l a)) ∧
      ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ∀ q : ℚ≥0,
        ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
        ∀ᶠ n in atTop,
          ((q : ℝ≥0) : ℝ≥0∞) < ((comparisonFamilyN ((V.at n).frameN lam) Ω c r).slow l a ω).dynamics.stop ξ := by
  by_cases hord : HistOrdered c r l
  swap
  · exact Eventually.of_forall fun ω halive => absurd (RootJ32.alive_spec c r l ω (hA ω halive)).2.2 hord
  have hv₀ := GW2Bf.v0_le_historyTime c r l hord
  have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hG : MeasurableSet[c.sigma r l] (rootGate c r l) := RootK32.measurableSet_sourceBuffer_gate c r l
  have h4 : (4 : ℝ≥0∞) ^ r.2 ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4' : (4 : ℝ≥0∞) ^ r.2 ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hcoe : ∀ q : ℚ≥0, ((((q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 : ℝ≥0)) : ℝ≥0∞) =
      ((q : ℝ≥0) : ℝ≥0∞) / (4 : ℝ≥0∞) ^ r.2 := fun q => by
    rw [ENNReal.coe_div (pow_ne_zero _ (by norm_num)), ENNReal.coe_pow]
    rfl
  have hgood : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ n, ∀ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
      ((q : ℝ≥0) : ℝ≥0∞) < ((V.at n).frameN lam Ω c r).base.stop (((V.at n).frameN lam Ω c r).base.slowVar l a) ξ →
        (RootJ32.sourceSample c r l a ξ).2 q = GW2Bf.histStart c r l ξ +
          ((V.at n).frameN lam Ω c r).base.drv l (((V.at n).frameN lam Ω c r).base.slowVar l a) q ξ := by
    filter_upwards [GW2Bf.ae_j32Start_eq_histStart h13 c r l hv₀, ae_all_iff.2 hdrv] with ξ hst hd hξG n q hq hqs
    have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 :=
      lt_of_le_of_lt zero_le (hq.trans_eq (RootJ32.sourceSample_fst c r l a ξ))
    have hu : (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 < rootGain c r l a ξ :=
      div_four_pow_lt r.2 (by rw [← GW2Bf.j32Sample_fst]; exact hq)
    have hus : ((((q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 : ℝ≥0)) : ℝ≥0∞) < ((V Ω c r).slowVar l a n).stop ξ := by
      rw [vpkg_slow_stop' (V.at n) lam Ω c r l a ξ] at hqs
      rw [hcoe, ENNReal.div_lt_iff (Or.inl h4) (Or.inl h4'), mul_comm]
      exact hqs
    rw [GW2Bf.j32Sample_snd c r l a ξ hq, hst a hlive, hd n hξG _ hu hus, vpkg_slow_drv (V.at n) lam Ω c r l a q ξ]
  have hexP : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
      ∀ᶠ n in atTop, ((q : ℝ≥0) : ℝ≥0∞) <
        ((V.at n).frameN lam Ω c r).base.stop (((V.at n).frameN lam Ω c r).base.slowVar l a) ξ := by
    filter_upwards [hex] with ξ h hξG q hq
    have hu : (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 < rootGain c r l a ξ :=
      div_four_pow_lt r.2 (by rw [← GW2Bf.j32Sample_fst]; exact hq)
    filter_upwards [h hξG _ hu] with n hn
    rw [vpkg_slow_stop' (V.at n) lam Ω c r l a ξ]
    rw [hcoe, ENNReal.div_lt_iff (Or.inl h4) (Or.inl h4'), mul_comm] at hn
    exact hn
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hgood, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hexP,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq h𝒢 (GW2Bf.measurable_histStart c r l),
    KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hG, hshell] with ω hgd hexk hfz hGc hsh halive
  obtain ⟨hcov, hold, -⟩ := RootJ32.alive_spec c r l ω (hA ω halive)
  have hωG : ω ∈ rootGate c r l := ⟨hcov, hold⟩
  have hGξ : ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ξ ∈ rootGate c r l := ae_iff.2 (hGc.1 hωG)
  obtain ⟨hshf, hst⟩ := hsh halive
  refine ⟨fun n => ⟨hshf.1, hshf.2.1, hshf.2.2, ?_, ?_⟩, ?_⟩
  · show Measurable (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.stop
    rw [slowData_stop]
    exact fun t ht => (hmeas hord n).div_const ((rootScale r.2 : ℝ≥0) : ℝ≥0∞) ht
  · filter_upwards [hgd, hfz, hGξ] with ξ h hξ hξG q hq hqs
    show _ = (((V.at n).frameN lam Ω c r).base.slowData l a ω).start +
      (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.W q ξ
    change ((q : ℝ≥0) : ℝ≥0∞) < (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.stop ξ at hqs
    rw [slowData_stop] at hqs
    rw [h hξG n q hq hqs, hξ, slowData_W]
    exact congrArg (· + _) hst.symm
  · filter_upwards [hexk, hGξ] with ξ h hξG q hq
    filter_upwards [h hξG q hq] with n hn
    show ((q : ℝ≥0) : ℝ≥0∞) < (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.stop ξ
    rw [slowData_stop]
    exact hn

/-! ### The pair on the scaled cover -/

/-- **The named inputs of the successor pair on the scaled cover** (review defect N1): as `GW2Sdy.VPairInputsXC`, with
the near words, the near facts and the shells asked on the alive events of `withScaledCover J32 gap` (and the shells'
drift clause in F1's `≤` form). -/
structure VPairInputsXCS (V : ℕ → VPkgXFamily.{u}) (lam : NearDil.{u}) (gap : RootCv.GapFamily.{u}) : Prop where
  lam_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0
  safe : ∀ k : ℕ, VPkgXSafe (V k)
  words : ∀ k : ℕ, VWordsX (J32S gap) (V k) lam
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    VNearImgOn ((V k).at 0) lam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
      (((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l)
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a n : ℕ,
      VDriverIdN (V 0) Ω c r l a n
  stopExhausts : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      VStopExhaustsN (V 0) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ∀ᵐ ω ∂c.P, ω ∈ ((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l →
        ShellFactLe c.κ (RootJ31.sourceDriftBound c r) ((V 0 Ω c r).slowShell l a ω) ∧
          ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω

/-- **The successor pair on the scaled cover: both lossy binders for `withScaledCover J32 gap`** (review defect N1;
decisions D1, D3, D3a; R113, R114, R118; Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossyXCS_vpkg (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (V : ℕ → VPkgXFamily.{u})
    (lam : NearDil.{u}) (gap : RootCv.GapFamily.{u}) (hV : VPairInputsXCS V lam gap) :
    RetainedNearModelsLossyStatement (J32S gap) ∧ RetainedSlowComparisonsLossyStatement (J32S gap) := by
  have hsde : ∀ k, RetainedStoppedSDEStatementN (J32S gap)
      (comparisonFamilyN (((V k).at 0).frameN lam)) fun n => comparisonFamilyN (((V k).at n).frameN lam) :=
    fun k => retainedStoppedSDEStatementN_vpkgX h12p₀ h13₀ h13 (V k) lam hV.lam_ne (aliveOrdered_scaled gap)
      (hV.safe k) (hV.words k)
  refine ⟨retainedNearModelsLossy_of_nearSDE (J32S gap)
    (fun k => comparisonFamilyN (((V k).at 0).frameN lam)) (fun k => (hsde k).near) ?_,
    retainedSlowComparisonsLossy_of_stoppedSDE_cut (J32S gap)
      (fun n => comparisonFamilyN (((V 0).at n).frameN lam)) (hsde 0).slow ?_⟩
  · intro Ω _ _ c r l k
    filter_upwards [(hsde k).near Ω c r l,
      nearImgPathLossy_on ((V k).at 0) lam Ω c r l (hV.lam_ne Ω c r l) (hV.nearImg k Ω c r l)]
      with ω hs hi halive n
    filter_upwards [hs halive n, hi halive n] with m h1 h2
    exact nearBufferFactLossy_of_imgPath h1 (RootJ32.experiment_reach_measurable c r l _) h2
  · intro Ω _ _ c r k l hl a
    filter_upwards [ae_slowBufferCut_on h13 (V 0) lam Ω c r l a (fun ω h => alive_scaled_subset gap Ω c r l h)
      (fun hTO n => ((hV.safe 0).slowSafe n Ω c r k l hl hTO a).2.measurable_stop) (hV.driverId Ω c r k l hl a)
      (hV.stopExhausts Ω c r k l hl a) _ (hV.shell Ω c r k l hl a)] with ω h halive
    exact ⟨Eventually.of_forall (h halive).1, (h halive).2⟩

/-- **Theorem 1.4 with J32 on the scaled cover from the successor pair with its inputs on the scaled cover** (review
defect N1; decisions D1, D2, D3, D3a; ruling R118): geometry discharged, both comparison binders from
`VPairInputsXCS`. -/
theorem theorem14Statement_J32_scaled_vpkgXCS (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (V : ℕ → VPkgXFamily.{u}) (lam : NearDil.{u}) (hV : VPairInputsXCS V lam gap)
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  have h := retainedComparisonsLossyXCS_vpkg
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0})
    Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} V lam gap hV
  theorem14Statement_J32_scaled_lossyS gap hgap hpos h.1 h.2 hN hgeo hcond

end InteractingSLE.Theorem14.GW2Sdz
