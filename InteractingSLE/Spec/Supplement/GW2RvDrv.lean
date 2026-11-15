/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzPair
import InteractingSLE.Spec.Supplement.GW2RzSched
import InteractingSLE.Spec.Supplement.GW2BiDrv


/-!
# GW2 at a root `x`: J32's reads are every root-`x` version below its cap (S1 at a root)

Packet PROVE-GW2-ROOTX, round 4. BUF's `GW2BiDrv` (S1 in decision D3's indexed form) at the root point
`x = rootPt r.1 ≥ 0`, with the root-`x` versions `GW2Rz.IsRelVersionX`:

* `pos_of_physGoodX` (a good sample has `0 < s`);
* **`ae_version_eqX`**: two root-`x` versions agree below both caps (their hulls agree at every root-`x` clock value
  below both caps, `Sec6.eqOn_of_fwdHull_eq`);
* **`ae_j32Read_eq_versionX`**: almost surely at every live sample, J32's capacity driver read is the version's driver
  below J32's capacity at the buffer and below the cap (one member of the root-`x` exhausting family covers the
  buffer, `GW2Rz.ae_hull_version_rootX`, BUF's `GW2Bf.ae_j32Read_eq_of_hull`);
* **`ae_j32DriverId_versionX`**: the centred form after the history's capacity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Rv

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.ReadD GW2TipSystem
  GW2TipSystem.RootC24 GW2Rd GW2Rz

/-- A good sample at a root has a positive retained time (the record's trace is at `0` at time `0`). -/
theorem pos_of_physGoodX {Ω : Type*} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {w : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ} {ω : Ω} (hω : PhysGoodX x s W' ζ' w γ α ω) : 0 < s := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h | h
  · exfalso
    have hH := hω.2.2.2.2.1.2.1
    have hrt : recordTrace s (cfRec s W' ζ' ω) = α ω s := hω.2.2.2.1 s le_rfl
    have hα0 := hω.2.1.1.1
    change recordTrace s (cfRec s W' ζ' ω) ∈ H at hH
    rw [hrt, ← h, hα0] at hH
    exact (lt_irrefl (0 : ℝ)) hH
  · exact h

/-! ### Two root-`x` versions agree below both caps -/

section Uniq

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {w : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}

/-- **Two root-`x` versions of one exploration agree below both caps** (BUF's `GW2Bh.ae_version_eq` at a root `x`:
their hulls agree at every root-`x` clock value below both caps, and hulls determine drivers). -/
theorem ae_version_eqX (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) (hx : 0 ≤ x)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s W' ζ' ω ∈ goodX x s) {R R' : ℝ≥0 → Ω → ℝ} {V V' : Ω → ℝ≥0∞}
    (hver : IsRelVersionX x s P W' ζ' w γ α R V) (hver' : IsRelVersionX x s P W' ζ' w γ α R' V') :
    ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ c' : ℝ≥0, (c' : ℝ≥0∞) < V ω → (c' : ℝ≥0∞) < V' ω →
      R c' ω = R' c' ω := by
  obtain ⟨-, hRc, hR0, -, -, -, hae⟩ := hver
  obtain ⟨-, hRc', hR0', -, -, -, hae'⟩ := hver'
  filter_upwards [hae, hae', hGTae] with ω hω hω' hG hm c' hcV hcV'
  have hωG : ω ∈ GT := hG.2 hm
  have hs := pos_of_physGoodX (hGT ω hωG)
  obtain ⟨hfc, hfm, hf0⟩ := clockX_props hGT hs hx hωG
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hωG
  obtain ⟨h0, -, hcont⟩ := clock_props W' ζ' ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  obtain ⟨-, hcov, hhull⟩ := hω hm
  obtain ⟨-, -, hhull'⟩ := hω' hm
  obtain ⟨t₁, ht₁, hct₁⟩ := hcov c' hcV
  have hsub : Icc 0 t₁ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < contactX x s γ α ω} :=
    fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans_lt ht₁
  have hK : ∀ y ∈ Icc (0 : ℝ) c', fwdHull (fun r : ℝ => R r.toNNReal ω) y =
      fwdHull (fun r : ℝ => R' r.toNNReal ω) y := by
    intro y hy
    obtain ⟨t, ht, hty0⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t₁) (hcont.mono hsub)
      (show y ∈ Icc (clockX x s W' ζ' w 0 ω) (clockX x s W' ζ' w t₁ ω) from
        ⟨by rw [show clockX x s W' ζ' w 0 ω = 0 from h0]; exact hy.1, hy.2.trans hct₁.le⟩)
    have hty : clockX x s W' ζ' w t ω = y := hty0
    have hle : ENNReal.ofReal (clockX x s W' ζ' w t ω) ≤ (c' : ℝ≥0∞) := by
      rw [hty, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hy.2
    rw [← hty, hhull t (hsub ht) (hle.trans hcV.le), hhull' t (hsub ht) (hle.trans hcV'.le)]
  have he := Sec6.eqOn_of_fwdHull_eq ((hRc ω).comp continuous_real_toNNReal)
    ((hRc' ω).comp continuous_real_toNNReal) (by simp [hR0 ω]) (by simp [hR0' ω]) c'.coe_nonneg hK
  have h1 := he ⟨c'.coe_nonneg, le_rfl⟩
  simpa only [Function.comp_apply, Real.toNNReal_coe] using h1

end Uniq

/-! ### J32's reads are every root-`x` version below its cap -/

section J32

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **J32's capacity driver read is every root-`x` version below its cap** (BUF's `GW2Bh.ae_j32Read_eq_version` at
the root `rootPt r.1 ≥ 0`: one member of the root-`x` exhausting family covers the buffer, its hulls are J32's
re-centred hulls there (`GW2Rz.ae_hull_version_rootX`), and two root-`x` versions agree below both caps). -/
theorem ae_j32Read_eq_versionX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 → ∀ c' : ℝ≥0,
      (c' : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s
        (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) (GW2Bf.exactPair c r l a ξ) →
      (c' : ℝ≥0∞) < V ξ → GW2Bf.j32Read c r l a c' ξ = R c' ξ := by
  obtain ⟨Rn, Vn, hverN, -, -, hcovN⟩ := exists_schedVersionsXA_mono h13 c r l a hx
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  have hhullN := ae_all_iff.2 fun n => ae_hull_version_rootX h13 c r l a (hverN n).1.1
  have huniq := ae_all_iff.2 fun n => ae_version_eqX hGT hx hGTae (hverN n).1.1 hver
  filter_upwards [hcovN, hhullN, huniq, ae_exactPair_rootX h13 c r l a, GW2Bf.ae_j32Read_eq_of_hull h13 c r,
    hGTae] with ξ hcovξ hhullξ huniqξ hpair hread hGξ hlive c' hcA hcV
  obtain ⟨hgx, hTc, hK⟩ := hpair hlive
  have hξG : ξ ∈ schedGTX h13 c r l a := hGξ.2 hgx
  have hs := pos_of_physGoodX (hGT ξ hξG)
  obtain ⟨-, hm, -⟩ := clockX_props hGT hs hx hξG
  set v := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ with hvdef
  obtain ⟨N, hN⟩ := (hcovξ hgx v hTc).exists
  have hR : ∀ t ∈ Icc 0 v, fwdHull (fun q : ℝ => Rn N q.toNNReal ξ)
      (RootH29.forwardCapacity (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ)) =
        (fun z : ℂ => z + ((-GW2Bf.relBase (rootPt r.1) c.s (GW2Bf.exactPair c r l a ξ) : ℝ) : ℂ)) ''
          RootH29.forwardHull (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ) := by
    intro t ht
    exact hhullξ N hlive t ht.2 ((hm ((ENNReal.coe_le_coe.2 ht.2).trans_lt hTc) hTc ht.2).trans hN.le)
  have h1 := hread l a hlive (fun u => Rn N u ξ) ((hverN N).1.1.2.1 ξ) ((hverN N).1.1.2.2.1 ξ) hR c' hcA
  have hcVN : (c' : ℝ≥0∞) < Vn N ξ := by
    refine lt_of_lt_of_le ?_ hN.le
    rw [(hK v le_rfl).1, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg c'.2).2 hcA
  rw [h1]
  exact huniqξ N hgx c' hcVN hcV

/-- **`VDriverId` below a version's cap** (BUF's `GW2Bh.ae_j32DriverId_version` at a root `x`): J32's centred
capacity driver is the version's increment after the history's capacity, for every `u < rootGain` with
`rootHistCap + u < V`. -/
theorem ae_j32DriverId_versionX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} (hver : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V):
    ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
      ((GW2Sdg.rootHistCap c r l a ξ + u : ℝ≥0) : ℝ≥0∞) < V ξ →
      GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ + u) ξ -
          GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ) ξ =
        R (GW2Sdg.rootHistCap c r l a ξ + u) ξ - R (GW2Sdg.rootHistCap c r l a ξ) ξ := by
  filter_upwards [ae_j32Read_eq_versionX h13 c r l a hx hver] with ξ hread u hu hV
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

end J32

end InteractingSLE.Theorem14.GW2Rv
