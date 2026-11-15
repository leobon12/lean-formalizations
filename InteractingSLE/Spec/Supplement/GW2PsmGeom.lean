/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxDil8
import InteractingSLE.Spec.Supplement.GW2OmxDrv
import InteractingSLE.WangWu.CouplingRetained

/-!
# GW2's open lines: the stage-start geometry at one sample (root `0`)

Packet PROVE-GW2-STAGEMEAN, R121 round. At one sample of the actual schedule (root `0`, strictly time-ordered
history, success, launch in `cL`, the launch datum's clock reaching `s` at `t₀`, the stage shape at every stage time
`u ≤ t` with stage capacities `A`), together with the current piece's relative chain `Rk` (`HullsUpTo`) and its
hulls off the conditional counterflow's retained hull:

* **`sample_stage_geom`**: the stage chart `cs = stgChart (relChart rec) R a₀` has domain `ℍ ∖ B 0`, lies in the
  launch chart's domain, is sent by `cL` off the retained hull, `relMap (Uk, t₀) ∘ cL.1 = λ · cs.1` on it
  (`GW2Omx.sample_kernel_dilation`), and the stage driver is the Brownian rescaling of `Rk` with relative clock `λ² Q`
  (`GW2Omx.sample_driver_scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Psm

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean
open Supp8.GB6 (relMap gb6Rec relClock)
open Supp8.Q3Rel (invHull)

/-- **The stage-start geometry at one sample** (root `0`). -/
theorem sample_stage_geom {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (t : ℝ≥0) (htpos : 0 < t) (ω : Ω)
    (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hconf : cL.IsConformal) (hext : GW1P.HasProperBdryExt cL) (htcap : t < candidateCap c r a)
    (htζ : (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    {γ' : ℝ≥0 → ℂ} (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0)
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ') (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) {ηe : ℝ≥0 → ℂ}
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => GW2Rd.schedW c r l a u ω) (h0e : GW2Rd.schedW c r l a 0 ω = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      (ηe '' Icc 0 (historyTime c r l))})
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) {t₀ : ℝ≥0} (ht₀ : ℓ t₀ = c.s)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {A : ℝ≥0 → ℝ≥0} {a₀ : ℝ≥0} (hA0 : A 0 = a₀)
    (hAa : ∀ u, a₀ ≤ A u) (hAc : Continuous A)
    (hshape : ∀ u ≤ t, H \ GW2Sdi.schedUnionS c r l a u ω =
      (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u)))
    {Rk : ℝ → ℝ} (hRk : Continuous Rk) (hRk0 : Rk 0 = 0)
    (hhull : HullsUpTo (fun q : ℝ => Wk q.toNNReal) t₀
      (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal) Rk t)
    (hdisj : ∀ u : ℝ≥0, u ≤ t → fwdHull (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal)
      u ⊆ H \ invHull (fun q : ℝ => Wk q.toNNReal) t₀) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ x ∈ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
        relMap (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) (cL.1 x) =
          (lam : ℂ) * (GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).1 x) ∧
      ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ) =
        H \ GW2Sdi.schedUnionS c r l a 0 ω ∧
      ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ) ⊆ cL.dom ∧
      (∀ y ∈ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
        cL.1 y ∈ H \ invHull (fun q : ℝ => Wk q.toNNReal) t₀) ∧
      EqOn (Ito.rpath (GW2Rd.stgDrv R a₀)) (fun s => Rk (lam ^ 2 * s) / lam) (Icc 0 ((A t : ℝ) - a₀)) ∧
      relClock (fun q : ℝ => Wk q.toNNReal) t₀
        (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal) t = lam ^ 2 * ((A t : ℝ) - a₀) := by
  classical
  set rec := gb6Rec c.s c.W c.ζ ω with hrec
  set c₀ := Supp8.RelSafeS.relChart rec with hc₀def
  set cs := GW2Rd.stgChart c₀ R a₀ with hcsdef
  set k := GW2Olm.curIdx c r l with hk
  set Δ := specDelta (GW2Olm.futSpec c r l a) with hΔ
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω with hD
  set Uk : ℝ → ℝ := fun q : ℝ => Wk q.toNNReal with hUk
  have hc₀ : c₀.IsConformal := Supp8.RelSafeS.isConformal_relChart rec
  have hcs : cs.IsConformal := GW2Rd.isConformal_stgChart hc₀ hR hR0 a₀
  have hUkc : Continuous Uk := hWk.comp continuous_real_toNNReal
  have hUk0 : Uk 0 = 0 := by simp [hUk, hWk0]
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  -- the dilation
  obtain ⟨lam, hlam, hdil⟩ := sample_kernel_dilation c r l a hr0 hord t htpos ω hold hgood hl hc hconf hext htcap htζ
    hWk hWk0 hγk hW' hW'0 hγ' hsζ hηe hce h0e hℓc hℓm hℓr hiff ht₀ hR hR0 hA0 hAa
    ((hAc.tendsto 0).trans (by rw [hA0])) hshape
  -- the union identity at every stage time `u ≤ t`
  have hΔk : Δ k = (candidateCap c r a : ℝ≥0∞) := futureProgram_delta c r l a
  have hmin_ne : min (Δ k) (D k).2 ≠ ⊤ := ne_top_of_le_ne_top (specDelta_ne_top _ k) (min_le_left _ _)
  have hU : ∀ u ≤ t, cL.1 '' (GW2Sdi.schedUnionS c r l a u ω ∩ (cL.dom : Set ℂ)) =
      invHull Uk (t₀ : ℝ) ∪ fwdHull (fun q : ℝ => (D k).1 q.toNNReal) (u : ℝ) := by
    intro u hu
    exact (launch_eq_of_clock c r l a hr0 hord u ω hold hgood hl hc hconf hext (hu.trans_lt htcap)
      hWk hWk0 hγk hW' hW'0 hγ' hsζ hηe hce h0e hℓc hℓm hℓr hiff ht₀
      ((ENNReal.coe_le_coe.2 hu).trans_lt htζ)).2
  -- the launch domain and the retained hull through `cL`
  obtain ⟨hdomL, hcont⟩ := launch_dom_cont c r l a hr0 hord ω hold hgood hl hc hconf hext hWk hWk0 hγk hW' hW'0
    hγ' hℓc hℓm.monotone hℓ0 hiff
  have hdisjL : ∀ q : ℝ≥0, Disjoint (closure (fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω)
      (historyTime c r l : ℝ))) (closure (invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ))) := by
    intro q
    have hq : ℓ q ∈ range ℓ := ⟨q, rfl⟩
    rw [hℓr] at hq
    exact disjoint_closure_of_lt_firstTipTime c r l a hγ' hW' hW'0 hηe hce h0e hq
  have hc0 : cL.2.1 '' invHull Uk (t₀ : ℝ) = invHull (fun u : ℝ => c.W u.toNNReal ω) c.s := by
    have h := hcont t₀ (hdisjL t₀)
    rw [ht₀] at h
    exact h
  have hRp : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath R 0 = 0 := by simp [Ito.rpath, hR0]
  have hB0 : GW2Sdi.schedUnionS c r l a 0 ω =
      invHull (fun u : ℝ => c.W u.toNNReal ω) c.s ∪ fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω)
        (historyTime c r l : ℝ) := by
    rw [GW2Sdi.schedUnionS_eq, Supp8.RelSafeS.invHull_record_eq hW'0 hW'.continuousOn hsζ]
    simp only [hold, ↓reduceIte, add_zero]
    rfl
  have hcsdom : (cs.dom : Set ℂ) = H \ GW2Sdi.schedUnionS c r l a 0 ω := by
    rw [hcs.coe_dom, hshape 0 zero_le, hA0]
    change (fun w => c₀.2.1 (fwdMapInv (Ito.rpath R) (a₀ : ℝ) w)) '' H = _
    rw [← Set.image_image, QuantumZipper.RS.image_fwdMapInv_H hRp hRp0 a₀.coe_nonneg]
  have hsubL : (cs.dom : Set ℂ) ⊆ cL.dom := by
    rw [hcsdom, hB0, hdomL]
    exact fun z hz => ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  have hmaps : ∀ y ∈ (cs.dom : Set ℂ), cL.1 y ∈ H \ invHull Uk t₀ := by
    intro y hy
    have hyL := hsubL hy
    refine ⟨hconf.fwd_mem hyL, fun hmem => ?_⟩
    rw [hcsdom, hB0] at hy
    apply hy.2
    left
    rw [← hc0]
    exact ⟨cL.1 y, hmem, hconf.inv_fwd hyL⟩
  -- the driver relation
  have hKB : ∀ u ≤ t, fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ) ⊆
      GW2Sdi.schedUnionS c r l a u ω := by
    intro u _ z hz
    rw [GW2Sdi.schedUnionS_eq]
    simp only [hold, ↓reduceIte]
    refine Or.inr ?_
    exact WangWu.fwdHull_mono (by
      have : (historyTime c r l : ℝ) ≤ ((historyTime c r l + u : ℝ≥0) : ℝ) := by
        simp only [NNReal.coe_add]; linarith [u.coe_nonneg]
      exact this) hz
  obtain ⟨hS, hq⟩ := sample_driver_scale hconf hc₀ hR hR0 hUkc hUk0 hlam hdil hA0 hAa hAc.continuousOn hshape hdomL
    hKB hRk hRk0 (fun u hu => hhull u hu) hdisj (fun u hu => hU u hu)
  exact ⟨lam, hlam, hdil, hcsdom, hsubL, hmaps, hS, hq⟩

end InteractingSLE.Theorem14.GW2Psm
