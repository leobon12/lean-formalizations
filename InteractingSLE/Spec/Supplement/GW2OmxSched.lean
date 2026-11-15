/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxUnion2
import InteractingSLE.Spec.Supplement.GW2OmxGeo
import InteractingSLE.Spec.Supplement.GW2SgkStop

/-!
# GW2's open lines: the localization hypotheses at the actual schedule, per sample

Packet PROVE-GW2-STAGEMEAN, R120 round (per-sample assembly, root `0`). At one sample where the history succeeded, the
current piece is launched in `cL`, the traces exist and the launch datum's clock `ℓ` has range the times before the
first tip of the counterflow in the explored trace image (the retained prefix), the two localization hypotheses of
`GW2Omx.kernel_launch_mean` hold with `I = noContact`:

* **`launch_sub_of_noContact`** (`hsub`): on no contact the clock reaches `s` at some `t₀`, and the kernel unions at
  `v ≤ t₀`, `u ≤ t` (`u` before the piece's death) lie in the launch image of the instance's union at `t`;
* **`launch_eq_of_clock`** (`heq`): where the clock reaches `s` at `t₀` and the piece is alive at `t`, there is no
  contact and the launch image of the instance's union at `t` IS the kernel union at `t₀`, `t`.

Monotonicity: `invHull_mono`, `launchUnion_mono`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule

theorem invHull_mono {U : ℝ → ℝ} {σ σ' : ℝ} (h : σ ≤ σ') : Supp8.Q3Rel.invHull U σ ⊆ Supp8.Q3Rel.invHull U σ' :=
  image_mono (QuantumZipper.fwdHull_mono.1 h)

theorem launchUnion_mono {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (cL : Chart) {u t : ℝ≥0} (hut : u ≤ t) (ω : Ω) :
    GW2Olm.launchUnion c r l a cL u ω ⊆ GW2Olm.launchUnion c r l a cL t ω := by
  refine image_mono (inter_subset_inter_left _ ?_)
  unfold GW2Sdi.schedUnionS GW2Sdh.schedPhysUnion
  split_ifs
  · refine union_subset_union_right _ (QuantumZipper.fwdHull_mono.1 ?_)
    exact_mod_cast add_le_add_right hut _
  · exact le_rfl

variable {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **`hsub` at the actual schedule, per sample.** -/
theorem launch_sub_of_noContact (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (t : ℝ≥0) (ω : Ω) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hconf : cL.IsConformal) (hext : GW1P.HasProperBdryExt cL) (htcap : t < candidateCap c r a)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    {γ' : ℝ≥0 → ℂ} (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0)
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ') (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) {ηe : ℝ≥0 → ℂ}
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => GW2Rd.schedW c r l a u ω) (h0e : GW2Rd.schedW c r l a 0 ω = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      (ηe '' Icc 0 (historyTime c r l))})
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z)
    (hnc : ω ∈ noContact c r l a) :
    ∃ t₀ : ℝ≥0, ℓ t₀ = c.s ∧ ∀ v ≤ t₀, ∀ u ≤ t,
      (u : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 →
      Supp8.Q3Rel.invHull (fun q : ℝ => Wk q.toNNReal) (v : ℝ) ∪
        fwdHull (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal) (u : ℝ) ⊆
          GW2Olm.launchUnion c r l a cL t ω := by
  have hlt := (mem_noContact_iff_lt_firstTipTime c r l a hγ' hW' hW'0 hsζ hηe hce h0e).1 hnc
  have hmem : c.s ∈ range ℓ := by
    rw [hℓr]
    exact hlt
  obtain ⟨t₀, ht₀⟩ := hmem
  have hd := disjoint_closure_of_mem_noContact c r l a hγ' hW' hW'0 hsζ hηe hce h0e hnc
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  refine ⟨t₀, ht₀, fun v hv u hu huζ => ?_⟩
  have hU := launchUnion_eq_of_launch c r l a hr0 hord u ω hold hgood hl hc hconf hext (lt_of_le_of_lt hu htcap)
    huζ hWk hWk0 hγk hW' hW'0 hγ' hsζ hℓc hℓm.monotone hℓ0 hiff ht₀ hd
  refine Subset.trans ?_ (launchUnion_mono c r l a cL hu ω)
  rw [hU]
  exact union_subset_union_left _ (invHull_mono (by exact_mod_cast hv))

/-- **`heq` at the actual schedule, per sample.** -/
theorem launch_eq_of_clock (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (t : ℝ≥0) (ω : Ω) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hconf : cL.IsConformal) (hext : GW1P.HasProperBdryExt cL) (htcap : t < candidateCap c r a)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    {γ' : ℝ≥0 → ℂ} (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0)
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ') (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) {ηe : ℝ≥0 → ℂ}
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => GW2Rd.schedW c r l a u ω) (h0e : GW2Rd.schedW c r l a 0 ω = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      (ηe '' Icc 0 (historyTime c r l))})
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z)
    {t₀ : ℝ≥0} (ht₀ : ℓ t₀ = c.s) (htζ : (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2) :
    ω ∈ noContact c r l a ∧ GW2Olm.launchUnion c r l a cL t ω =
      Supp8.Q3Rel.invHull (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) ∪
        fwdHull (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal) (t : ℝ) := by
  have hmem : c.s ∈ range ℓ := ⟨t₀, ht₀⟩
  rw [hℓr] at hmem
  have hnc := (mem_noContact_iff_lt_firstTipTime c r l a hγ' hW' hW'0 hsζ hηe hce h0e).2 hmem
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  exact ⟨hnc, launchUnion_eq_of_launch c r l a hr0 hord t ω hold hgood hl hc hconf hext htcap htζ hWk hWk0 hγk
    hW' hW'0 hγ' hsζ hℓc hℓm.monotone hℓ0 hiff ht₀
    (disjoint_closure_of_mem_noContact c r l a hγ' hW' hW'0 hsζ hηe hce h0e hnc)⟩

end InteractingSLE.Theorem14.GW2Omx
