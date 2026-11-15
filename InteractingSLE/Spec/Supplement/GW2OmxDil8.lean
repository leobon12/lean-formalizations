/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxDil7
import InteractingSLE.Spec.Supplement.GW2OmxSched
import InteractingSLE.Spec.Supplement.GW2OmxDil2
import InteractingSLE.Spec.Supplement.RelSafeS7

/-!
# GW2's open lines: the stage-start dilation at the actual schedule, per sample

Packet PROVE-GW2-STAGEMEAN, R120 round. Per sample (root `0`, strict history, success, launch `cL`, the datum's clock
with `ℓ t₀ = s`, the piece alive at `t > 0` below the cap) and for a stage chart `stgChart (relChart (gb6Rec …)) R a₀`
whose shape reads the instance's union at every stage time `u ≤ t` off the relative hull at the clock `A u → a₀`:

* **`sample_kernel_dilation`**: `relMap (Wk, t₀) ∘ cL.1 = λ · cs.1` on the stage chart's domain
  (`GW2Omx.kernel_dilation` with `stage_near_zero`, `stage_far`, `launch_eq_of_clock`, `launch_dom_cont`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule
open Supp8.GB6 (relMap gb6Rec)
open Supp8.Q3Rel (invHull)

theorem sample_kernel_dilation {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
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
    (hAa : ∀ u, a₀ ≤ A u) (hAc : Tendsto A (𝓝 0) (𝓝 a₀))
    (hshape : ∀ u ≤ t, H \ GW2Sdi.schedUnionS c r l a u ω =
      (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u))) :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ x ∈ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
        relMap (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) (cL.1 x) =
          (lam : ℂ) * (GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).1 x := by
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
  obtain ⟨hVc, hV0⟩ := hc k (Nat.lt_succ_self k)
  set V := stopDrv (Δ k) (D k) with hV
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  -- the piece's hulls are the stopped driver's hulls before `t`
  have hΔk : Δ k = (candidateCap c r a : ℝ≥0∞) := futureProgram_delta c r l a
  have hmin_ne : min (Δ k) (D k).2 ≠ ⊤ := ne_top_of_le_ne_top (specDelta_ne_top _ k) (min_le_left _ _)
  have hK : ∀ u ≤ t, fwdHull V (u : ℝ) = fwdHull (fun q : ℝ => (D k).1 q.toNNReal) (u : ℝ) := by
    intro u hu
    have htst : (u : ℝ) < stopTime (Δ k) (D k) := by
      have h1 : (u : ℝ≥0∞) < min (Δ k) (D k).2 :=
        lt_min (by rw [hΔk]; exact_mod_cast hu.trans_lt htcap) ((ENNReal.coe_le_coe.2 hu).trans_lt htζ)
      have h2 : u < (min (Δ k) (D k).2).toNNReal := by
        rwa [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hmin_ne]
      exact_mod_cast h2
    refine fwdHull_eq_of_eqOn u.coe_nonneg htst fun q hq => ?_
    refine Gm.stopDrv_eq_of_le ?_
    have h1 : q.toNNReal ≤ (min (Δ k) (D k).2).toNNReal := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hq.2
    calc ((q.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ((min (Δ k) (D k).2).toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.2 h1
      _ = min (Δ k) (D k).2 := ENNReal.coe_toNNReal hmin_ne
  -- the union identity at every stage time `u ≤ t`
  have hU : ∀ u ≤ t, GW2Olm.launchUnion c r l a cL u ω = invHull Uk (t₀ : ℝ) ∪ fwdHull V (u : ℝ) := by
    intro u hu
    rw [hK u hu]
    exact (launch_eq_of_clock c r l a hr0 hord u ω hold hgood hl hc hconf hext (hu.trans_lt htcap)
      hWk hWk0 hγk hW' hW'0 hγ' hsζ hηe hce h0e hℓc hℓm hℓr hiff ht₀
      ((ENNReal.coe_le_coe.2 hu).trans_lt htζ)).2
  -- the domain and the continuation through `cL`
  obtain ⟨hdomL, hcont⟩ := launch_dom_cont c r l a hr0 hord ω hold hgood hl hc hconf hext hWk hWk0 hγk hW' hW'0
    hγ' hℓc hℓm.monotone hℓ0 hiff
  have hdisj : ∀ q : ℝ≥0, Disjoint (closure (fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω)
      (historyTime c r l : ℝ))) (closure (invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ))) := by
    intro q
    have hq : ℓ q ∈ range ℓ := ⟨q, rfl⟩
    rw [hℓr] at hq
    exact disjoint_closure_of_lt_firstTipTime c r l a hγ' hW' hW'0 hηe hce h0e hq
  have hcont' : ∀ q : ℝ≥0, cL.2.1 '' invHull Uk (q : ℝ) = invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ) :=
    fun q => hcont q (hdisj q)
  -- the domains
  have hRp : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath R 0 = 0 := by simp [Ito.rpath, hR0]
  have hB0 : GW2Sdi.schedUnionS c r l a 0 ω =
      invHull (fun u : ℝ => c.W u.toNNReal ω) c.s ∪ fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω)
        (historyTime c r l : ℝ) := by
    rw [GW2Sdi.schedUnionS_eq, Supp8.RelSafeS.invHull_record_eq hW'0 hW'.continuousOn hsζ]
    simp only [hold, ↓reduceIte, add_zero]
    rfl
  have hj := Supp8.Q3Rel.isDomainChart_rel hUkc hUk0 t₀.coe_nonneg
  have hjc : (GW2JointKernel.jointChart Uk t₀).IsConformal := hj.isConformal
  have hjdom : ((GW2JointKernel.jointChart Uk t₀).dom : Set ℂ) = H \ invHull Uk t₀ := by
    rw [hjc.coe_dom, hj.image_eq]
  have hcsdom : (cs.dom : Set ℂ) = H \ GW2Sdi.schedUnionS c r l a 0 ω := by
    rw [hcs.coe_dom, hshape 0 zero_le, hA0]
    change (fun w => c₀.2.1 (fwdMapInv (Ito.rpath R) (a₀ : ℝ) w)) '' H = _
    rw [← Set.image_image, QuantumZipper.RS.image_fwdMapInv_H hRp hRp0 a₀.coe_nonneg]
  have hdom : (cs.dom : Set ℂ) = (cL.trans (GW2JointKernel.jointChart Uk t₀)).dom := by
    rw [hcsdom, hB0]
    ext z
    rw [SetLike.mem_coe, WalkInf.mem_dom_trans_iff hconf hjc, ← SetLike.mem_coe, hdomL, ← SetLike.mem_coe, hjdom]
    have hc0 := hcont' t₀
    rw [ht₀] at hc0
    constructor
    · rintro ⟨hzH, hzU⟩
      have hzL : z ∈ H \ fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ) :=
        ⟨hzH, fun h => hzU (Or.inr h)⟩
      refine ⟨hzL, ?_, ?_⟩
      · rw [← hdomL] at hzL
        exact hconf.fwd_mem hzL
      · intro hmem
        rw [← hdomL] at hzL
        apply hzU
        left
        rw [← hc0]
        exact ⟨cL.1 z, hmem, hconf.inv_fwd hzL⟩
    · rintro ⟨hzL, -, hzI⟩
      refine ⟨hzL.1, ?_⟩
      rintro (h | h)
      · rw [← hc0] at h
        obtain ⟨w, hw, rfl⟩ := h
        have hwH : w ∈ H := GW2Shr.invHull_subset_H hUkc t₀.coe_nonneg hw
        exact hzI (by rw [hconf.2.2 w hwH]; exact hw)
      · exact hzL.2 h
  -- the two families
  set uN : ℕ → ℝ≥0 := fun n => t / ((n : ℝ≥0) + 2) with huN
  have hden : ∀ n : ℕ, (0 : ℝ≥0) < (n : ℝ≥0) + 2 := fun n => by positivity
  have huNpos : ∀ n, 0 < uN n := fun n => div_pos htpos (hden n)
  have huNle : ∀ n, uN n ≤ t := fun n => div_le_self zero_le (by
    have h0 : (0 : ℝ≥0) ≤ n := zero_le
    calc (1 : ℝ≥0) ≤ 2 := by norm_num
      _ ≤ (n : ℝ≥0) + 2 := le_add_of_nonneg_left h0)
  have huN0 : Tendsto uN atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    have h1 := (tendsto_const_div_atTop_nhds_zero_nat (t : ℝ)).comp (tendsto_add_atTop_nat 2)
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply, huN, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat,
      Nat.cast_add, Nat.cast_ofNat]
  set vN : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1) with hvN
  have hvNpos : ∀ n, 0 < vN n := fun n => by positivity
  have hvN0 : Tendsto vN atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => ?_
    simp only [hvN, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
  have hc₀ := stage_near_zero hconf hc₀ (R := Ito.rpath R) hRp hRp0 a₀.coe_nonneg (u := fun n => (uN n : ℝ))
    (A := fun n => (A (uN n) : ℝ)) (fun n => NNReal.coe_le_coe.2 (hAa (uN n)))
    ((NNReal.continuous_coe.tendsto a₀).comp (hAc.comp huN0)) (B := fun n => GW2Sdi.schedUnionS c r l a (uN n) ω)
    (fun n => hshape (uN n) (huNle n)) (V := V) (fun n => by
      have h := hU (uN n) (huNle n)
      intro w hw
      change w ∈ GW2Olm.launchUnion c r l a cL (uN n) ω
      rw [h]
      exact Or.inr hw)
  set w : ℕ → ℝ := fun n => (ℓ (t₀ + vN n) : ℝ) - c.s with hw
  have hwpos : ∀ n, 0 < w n := fun n => by
    have h := hℓm (lt_add_of_pos_right t₀ (hvNpos n))
    rw [ht₀] at h
    simp only [hw]
    exact sub_pos.2 (by exact_mod_cast h)
  have hw0 : Tendsto w atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ℓ (t₀ + vN n)) atTop (𝓝 (ℓ t₀)) := by
      have h2 : Tendsto (fun n => t₀ + vN n) atTop (𝓝 t₀) := by simpa using tendsto_const_nhds.add hvN0
      exact (hℓc.tendsto t₀).comp h2
    have h3 := (NNReal.continuous_coe.tendsto _).comp h1
    rw [ht₀] at h3
    simpa [hw] using h3.sub_const (c.s : ℝ)
  have hc₁ := stage_far hW'0 hW' hsζ hR hR0 a₀ (S₁ := fun n => cL.2.1 '' (invHull Uk (t₀ + (vN n : ℝ)) \
    invHull Uk t₀)) hwpos hw0 (fun n => by
      rintro z ⟨w', hw', rfl⟩
      have hq := hcont' (t₀ + vN n)
      have hc0 := hcont' t₀
      rw [ht₀] at hc0
      have hw'H : w' ∈ H := GW2Shr.invHull_subset_H hUkc (by positivity) hw'.1
      have hsw : (c.s : ℝ) + w n = (ℓ (t₀ + vN n) : ℝ) := by simp only [hw]; ring
      refine ⟨?_, ?_⟩
      · rw [hsw, ← hq]
        exact ⟨w', by simpa using hw'.1, rfl⟩
      · intro hmem
        rw [← hc0] at hmem
        obtain ⟨w'', hw'', he⟩ := hmem
        have hw''H : w'' ∈ H := GW2Shr.invHull_subset_H hUkc t₀.coe_nonneg hw''
        have : w'' = w' := hconf.injOn hw''H hw'H he
        exact hw'.2 (this ▸ hw''))
  obtain ⟨lam, hlam, hdil⟩ := kernel_dilation hconf hcs hUkc hUk0 t₀.coe_nonneg hVc hV0 hdom
    (u := fun n => (uN n : ℝ)) (fun n => NNReal.coe_pos.2 (huNpos n))
    ((NNReal.continuous_coe.tendsto 0).comp huN0) (v := fun n => (vN n : ℝ))
    (fun n => NNReal.coe_pos.2 (hvNpos n)) ((NNReal.continuous_coe.tendsto 0).comp hvN0) hc₀ hc₁
  exact ⟨lam, hlam, hdil⟩

end InteractingSLE.Theorem14.GW2Omx
