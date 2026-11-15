/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BiHull
import InteractingSLE.Spec.Supplement.GW2SxTimeVer
import InteractingSLE.Spec.Sec6.DrivingCriterion

/-!
# J32's capacity driver is every GB6 version below its cap (S1 in decision D3's indexed form)

Packet PROVE-GW2-BUF (S1, round 6). Decision D3 builds the slow stage instance on the member `n` of RELDET's exhausting
version family and asks `VDriverId` for each `n` below the `n`-th cap. This file proves it at the version level, at
root `0`, for ANY GB6 version `(R, V)` of the schedule instance (no monotonicity of the family is used):

* **`ae_version_eq`**: two GB6 versions of the same exploration agree below both caps (their hulls agree there, and
  hulls determine drivers, `Sec6.eqOn_of_fwdHull_eq`);
* **`ae_j32Read_eq_version`**: almost surely at every live sample, J32's capacity driver read is `R` at every relative
  time below J32's capacity at the buffer and below `V`. The proof uses one member of RELDET's exhausting family that
  covers the buffer (`GW2Rd.exists_schedVersionsA`, existence only), `GW2Bf.ae_j32Read_eq_of_hull` for it, and
  `ae_version_eq`;
* **`ae_j32DriverId_version`**: the centred form. For `u < rootGain` with `rootHistCap + u < V`,
  `j32Read (F_T + u) − j32Read F_T = R (F_T + u) − R F_T`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.RelDrv GW2TipSystem GW2TipSystem.RootC24 GW2Rd

/-- **Two GB6 versions of one exploration agree below both caps.** -/
theorem ae_version_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ}
    {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    {s : ℝ≥0} {R R' : ℝ≥0 → Ω → ℝ} {V V' : Ω → ℝ≥0∞}
    (hver : IsGB6RelVersion s P W Wα ζα γ α R V) (hver' : IsGB6RelVersion s P W Wα ζα γ α R' V') :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ c' : ℝ≥0, (c' : ℝ≥0∞) < V ω → (c' : ℝ≥0∞) < V' ω →
      R c' ω = R' c' ω := by
  have hS := ae_timeCap_sample hF hα hW hver
  obtain ⟨-, hRc, hR0, -, -, -, hae⟩ := hver
  obtain ⟨-, hRc', hR0', -, -, -, hae'⟩ := hver'
  filter_upwards [hS, hae, hae'] with ω hSω hω hω' hs hsH c' hcV hcV'
  obtain ⟨-, h0, -, hcont, -, -⟩ := hSω hs hsH
  obtain ⟨-, hcov, hhull⟩ := hω hs hsH
  obtain ⟨-, -, hhull'⟩ := hω' hs hsH
  obtain ⟨t₁, ht₁, hct₁⟩ := hcov c' hcV
  have hsub : Icc 0 t₁ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < gb6Tc s γ α ω} :=
    fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans_lt ht₁
  have hK : ∀ x ∈ Icc (0 : ℝ) c', QuantumZipper.fwdHull (fun r : ℝ => R r.toNNReal ω) x =
      QuantumZipper.fwdHull (fun r : ℝ => R' r.toNNReal ω) x := by
    intro x hx
    obtain ⟨t, ht, htx⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t₁) (hcont.mono hsub)
      (show x ∈ Icc (gb6Clock s W Wα ω 0) (gb6Clock s W Wα ω t₁) from ⟨by rw [h0]; exact hx.1, hx.2.trans hct₁.le⟩)
    have hle : ENNReal.ofReal (gb6Clock s W Wα ω t) ≤ (c' : ℝ≥0∞) := by
      rw [htx, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hx.2
    rw [← htx, hhull t (hsub ht) (hle.trans hcV.le), hhull' t (hsub ht) (hle.trans hcV'.le)]
  have he := Sec6.eqOn_of_fwdHull_eq ((hRc ω).comp continuous_real_toNNReal)
    ((hRc' ω).comp continuous_real_toNNReal) (by simp [hR0 ω]) (by simp [hR0' ω]) c'.coe_nonneg hK
  have h1 := he ⟨c'.coe_nonneg, le_rfl⟩
  simpa only [Function.comp_apply, Real.toNNReal_coe] using h1

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **J32's capacity driver read is every GB6 version below its cap** (root `0`). -/
theorem ae_j32Read_eq_version (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGB6RelVersion c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 → ∀ c' : ℝ≥0,
      (c' : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s
        (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) (GW2Bf.exactPair c r l a ξ) →
      (c' : ℝ≥0∞) < V ξ → GW2Bf.j32Read c r l a c' ξ = R c' ξ := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hW : ∀ᵐ ω ∂c.P, Continuous (schedW c r l a · ω) ∧ schedW c r l a 0 ω = 0 ∧
      IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) :=
    (ae_schedW_regular h13 c r l a).mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  obtain ⟨Rn, Vn, hverN, -, hcovN⟩ := exists_schedVersionsA h13 c r l a
  have hhullN := ae_all_iff.2 fun n => ae_hull_version_root0 h13 c r l a hroot (hverN n).1.1
  have huniq := ae_all_iff.2 fun n => ae_version_eq hfl hα hW (hverN n).1.1 hver
  filter_upwards [hcovN, hhullN, huniq, ae_exactPair_root0 h13 c r l a hroot, GW2Bf.ae_j32Read_eq_of_hull h13 c r,
    ae_timeCap_sample hfl hα hW hver] with ξ hcovξ hhullξ huniqξ hpair hread hS hlive c' hcA hcV
  obtain ⟨hsζ, hsH, hTc, -, hK⟩ := hpair hlive
  obtain ⟨-, -, hm, -, -, -⟩ := hS hsζ hsH
  set v := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ with hvdef
  obtain ⟨N, hN⟩ := hcovξ hsζ hsH v hTc
  have hR : ∀ t ∈ Icc 0 v, QuantumZipper.fwdHull (fun q : ℝ => Rn N q.toNNReal ξ)
      (RootH29.forwardCapacity (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ)) =
        (fun z : ℂ => z + ((-GW2Bf.relBase (rootPt r.1) c.s (GW2Bf.exactPair c r l a ξ) : ℝ) : ℂ)) ''
          RootH29.forwardHull (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ) := by
    intro t ht
    refine hhullξ N hlive t ht.2 ((ENNReal.ofReal_le_ofReal ?_).trans hN.le)
    exact hm.monotoneOn ((ENNReal.coe_le_coe.2 ht.2).trans_lt hTc) hTc ht.2
  have h1 := hread l a hlive (fun u => Rn N u ξ) ((hverN N).1.1.2.1 ξ) ((hverN N).1.1.2.2.1 ξ) hR c' hcA
  have hcVN : (c' : ℝ≥0∞) < Vn N ξ := by
    refine lt_of_lt_of_le ?_ hN.le
    rw [← (hK v le_rfl).2, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg c'.2).2 hcA
  rw [h1]
  exact huniqξ N hsζ hsH c' hcVN hcV

/-- **`VDriverId` below a version's cap** (decision D3's indexed form, root `0`): J32's centred capacity driver is
the version's increment after the history's capacity, for every `u < rootGain` with `rootHistCap + u < V`. -/
theorem ae_j32DriverId_version (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGB6RelVersion c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) :
    ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
      ((GW2Sdg.rootHistCap c r l a ξ + u : ℝ≥0) : ℝ≥0∞) < V ξ →
      GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ + u) ξ -
          GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ) ξ =
        R (GW2Sdg.rootHistCap c r l a ξ + u) ξ - R (GW2Sdg.rootHistCap c r l a ξ) ξ := by
  filter_upwards [ae_j32Read_eq_version h13 c r l a hroot hver] with ξ hread u hu hV
  set T := RootJ31.historyTime c r l
  set v := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ
  have hgain : 0 < GW2Sdg.rootGain c r l a ξ := lt_of_le_of_lt zero_le hu
  have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 := by
    rw [GW2Sdg.sourceSample_fst]
    exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) (ENNReal.coe_ne_zero.2 hgain.ne')
  have hT0 : 0 ≤ RootH29.forwardCapacity (rootPt r.1) c.s T (RootJ31.futurePair c r l a ξ) :=
    RootJ32.forwardCapacity_nonneg _ _ _ _
  have hgain' : (0 : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s v (RootJ31.futurePair c r l a ξ) -
      RootH29.forwardCapacity (rootPt r.1) c.s T (RootJ31.futurePair c r l a ξ) := by
    have h := hgain
    unfold GW2Sdg.rootGain GW2Sdg.rootCapAt at h
    exact Real.toNNReal_pos.1 h
  have hlev : ∀ w : ℝ≥0, w ≤ u → ((GW2Sdg.rootHistCap c r l a ξ + w : ℝ≥0) : ℝ) <
      RootH29.forwardCapacity (rootPt r.1) c.s v (GW2Bf.exactPair c r l a ξ) := by
    intro w hw
    rw [← GW2Bf.forwardCapacity_future_eq_exact c r l a ξ le_rfl]
    have hu' : ((u : ℝ≥0) : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s v (RootJ31.futurePair c r l a ξ) -
        RootH29.forwardCapacity (rootPt r.1) c.s T (RootJ31.futurePair c r l a ξ) := by
      have h := NNReal.coe_lt_coe.2 hu
      unfold GW2Sdg.rootGain GW2Sdg.rootCapAt at h
      rwa [Real.coe_toNNReal _ hgain'.le] at h
    have hw' : (w : ℝ) ≤ u := NNReal.coe_le_coe.2 hw
    unfold GW2Sdg.rootHistCap GW2Sdg.rootCapAt
    push_cast
    rw [Real.coe_toNNReal _ hT0]
    linarith
  have hV0 : ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V ξ :=
    (ENNReal.coe_le_coe.2 le_self_add).trans_lt hV
  rw [hread hlive _ (hlev u le_rfl) hV, hread hlive _ (by simpa using hlev 0 zero_le) hV0]
