/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Geo

/-!
# The root piece's stage-start dilation and driver relation at a root `x` (launch chart `recenter x`)

Packet PROVE-GW2-GEOM2, round 14 (D49). **`sample_stage_geom0X`**: at one sample of the history `l = []` (success),
with BR4a's datum at index `0` and the root piece's relative chain, the stage chart `cs = stgChart (relChartX x s rec)
R a₀` read from the root's start satisfies `relMap (Wk, t₀) ∘ cL.1 = λ · cs.1` on `cs.dom = ℍ ∖ B 0`, `cL.1` maps
`cs.dom` off the retained hull, and the stage driver is the Brownian rescaling of the chain's driver
(`GW2Omx.kernel_dilation` with `GW2Omx.stage_near_zero`, `GW2Xk.stage_farX`; `GW2Omx.sample_driver_scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Kx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean GW2Xk GW2Kb
open Supp8.GB6 (relMap gb6Rec relClock)
open Supp8.Q3Rel (invHull)

/-- **The root piece's stage-start geometry from the root's start** (root `x ≥ 0`, one sample). -/
theorem sample_stage_geom0X {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ)
    (hx0 : 0 ≤ rootPt r.1) (t : ℝ≥0) (htpos : 0 < t) (ω : Ω) (hold : oldSuccess c r [] ω)
    (hce : Continuous fun u => GW2Rd.schedW c r [] a u ω) (h0e : GW2Rd.schedW c r [] a 0 ω = 0)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    {γ' : ℝ≥0 → ℂ} (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0)
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ') (hsζ : (c.s : ℝ≥0∞) < c.ζ ω)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      {((rootPt r.1 : ℝ) : ℂ)}})
    (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * γ' τ + 1 = 0)
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), ((Chart.id.recenter (rootPt r.1)).trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) {t₀ : ℝ≥0} (ht₀ : ℓ t₀ = c.s)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {A : ℝ≥0 → ℝ≥0} {a₀ : ℝ≥0} (hA0 : A 0 = a₀)
    (hAa : ∀ u, a₀ ≤ A u) (hAc : Continuous A)
    (hshape : ∀ u ≤ t, H \ GW2Rd.schedUnionX c r [] a 0 u ω =
      (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u)))
    {Wc : ℝ → ℝ} (hWcK : ∀ u : ℝ≥0, u ≤ t →
      fwdHull Wc u = fwdHull (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) u)
    {Rk : ℝ → ℝ} (hRk : Continuous Rk) (hRk0 : Rk 0 = 0)
    (hhull : ∀ u : ℝ≥0, u ≤ t →
      relMap (fun q : ℝ => Wk q.toNNReal) t₀ '' fwdHull Wc u =
        fwdHull Rk (relClock (fun q : ℝ => Wk q.toNNReal) t₀ Wc u))
    (hdisj : ∀ u : ℝ≥0, u ≤ t → fwdHull Wc u ⊆ H \ invHull (fun q : ℝ => Wk q.toNNReal) t₀) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ y ∈ ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
        relMap (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) ((Chart.id.recenter (rootPt r.1)).1 y) =
          (lam : ℂ) * (GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).1 y) ∧
      ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ) =
        H \ GW2Rd.schedUnionX c r [] a 0 0 ω ∧
      (∀ y ∈ ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
        (Chart.id.recenter (rootPt r.1)).1 y ∈ H \ invHull (fun q : ℝ => Wk q.toNNReal) t₀) ∧
      EqOn (Ito.rpath (GW2Rd.stgDrv R a₀)) (fun s => Rk (lam ^ 2 * s) / lam) (Icc 0 ((A t : ℝ) - a₀)) ∧
      relClock (fun q : ℝ => Wk q.toNNReal) t₀ Wc t = lam ^ 2 * ((A t : ℝ) - a₀) := by
  classical
  set x := rootPt r.1 with hx
  set rec := cfRec c.s c.W c.ζ ω with hrec
  set c₀ := GW2Rz.relChartX x c.s rec with hc₀def
  set cs := GW2Rd.stgChart c₀ R a₀ with hcsdef
  set cL := Chart.id.recenter x with hcLdef
  set Uk : ℝ → ℝ := fun q : ℝ => Wk q.toNNReal with hUk
  have hconf : cL.IsConformal := Chart.isConformal_id.recenter x
  have hc₀ : c₀.IsConformal := GW2Rz.isConformal_relChartX _ _ rec
  have hcs : cs.IsConformal := GW2Rd.isConformal_stgChart hc₀ hR hR0 a₀
  have hUkc : Continuous Uk := hWk.comp continuous_real_toNNReal
  have hUk0 : Uk 0 = 0 := by simp [hUk, hWk0]
  have hcont : ∀ q : ℝ≥0, cL.2.1 '' invHull Uk (q : ℝ) = invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ) :=
    cont_root0X hx0 hWk hWk0 hγk hW' hW'0 hγ' hℓc hℓm hℓr hvis hiff
  have hc0 : cL.2.1 '' invHull Uk (t₀ : ℝ) = invHull (fun u : ℝ => c.W u.toNNReal ω) c.s := by
    rw [hcont t₀, ht₀]
  have hU : ∀ u : ℝ≥0, cL.1 '' (GW2Rd.schedUnionX c r [] a 0 u ω ∩ (cL.dom : Set ℂ)) =
      invHull Uk t₀ ∪ fwdHull (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) u :=
    union_root0X c r a hold hW'0 hW' hsζ hWk hc0
  set V : ℝ → ℝ := fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω with hVdef
  have hVc : Continuous V := hce.comp continuous_real_toNNReal
  have hV0 : V 0 = 0 := by simp [hVdef, h0e]
  have hRp : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath R 0 = 0 := by simp [Ito.rpath, hR0]
  have hdomL : (cL.dom : Set ℂ) = H := coe_dom_recenter_id x
  have hB0 : GW2Rd.schedUnionX c r [] a 0 0 ω = invHull (fun u : ℝ => c.W u.toNNReal ω) c.s := by
    rw [← Supp8.RelSafeS.invHull_record_eq hW'0 hW'.continuousOn hsζ]
    have hK0 : fwdHull (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) 0 = ∅ := fwdHull_zero_eq_empty hVc hV0
    simp only [GW2Rd.schedUnionX, GW2Rd.schedHullX, hold, ↓reduceIte, GW2Rd.schedHull, add_zero,
      NNReal.coe_zero]
    rw [hK0, image_empty, union_empty]
  have hj := Supp8.Q3Rel.isDomainChart_rel hUkc hUk0 t₀.coe_nonneg
  have hjc : (GW2JointKernel.jointChart Uk t₀).IsConformal := hj.isConformal
  have hjdom : ((GW2JointKernel.jointChart Uk t₀).dom : Set ℂ) = H \ invHull Uk t₀ := by
    rw [hjc.coe_dom, hj.image_eq]
  have hcsdom : (cs.dom : Set ℂ) = H \ GW2Rd.schedUnionX c r [] a 0 0 ω := by
    rw [hcs.coe_dom, hshape 0 zero_le, hA0]
    change (fun w => c₀.2.1 (fwdMapInv (Ito.rpath R) (a₀ : ℝ) w)) '' H = _
    rw [← Set.image_image, QuantumZipper.RS.image_fwdMapInv_H hRp hRp0 a₀.coe_nonneg]
  have hmaps : ∀ y ∈ (cs.dom : Set ℂ), cL.1 y ∈ H \ invHull Uk t₀ := by
    intro y hy
    rw [hcsdom, hB0] at hy
    have hyL : y ∈ (cL.dom : Set ℂ) := by rw [hdomL]; exact hy.1
    refine ⟨hconf.fwd_mem hyL, fun hmem => hy.2 ?_⟩
    rw [← hc0]
    exact ⟨cL.1 y, hmem, hconf.inv_fwd hyL⟩
  have hdom : (cs.dom : Set ℂ) = (cL.trans (GW2JointKernel.jointChart Uk t₀)).dom := by
    ext z
    have e1 : z ∈ ((cL.trans (GW2JointKernel.jointChart Uk t₀)).dom : Set ℂ) ↔
        z ∈ (cL.dom : Set ℂ) ∧ cL.1 z ∈ ((GW2JointKernel.jointChart Uk t₀).dom : Set ℂ) :=
      WalkInf.mem_dom_trans_iff hconf hjc
    rw [e1, hjdom, hdomL]
    constructor
    · intro hz
      have hzH : z ∈ H := by rw [hcsdom] at hz; exact hz.1
      exact ⟨hzH, hmaps z hz⟩
    · rintro ⟨hzL, hzI⟩
      rw [hcsdom, hB0]
      refine ⟨hzL, fun hzW => ?_⟩
      rw [← hc0] at hzW
      obtain ⟨w, hw, hwz⟩ := hzW
      have hwH : w ∈ H := GW2Shr.invHull_subset_H hUkc t₀.coe_nonneg hw
      apply hzI.2
      rw [← hwz, hconf.2.2 w hwH]
      exact hw
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
  have hcn := stage_near_zero hconf hc₀ (R := Ito.rpath R) hRp hRp0 a₀.coe_nonneg (u := fun n => (uN n : ℝ))
    (A := fun n => (A (uN n) : ℝ)) (fun n => NNReal.coe_le_coe.2 (hAa (uN n)))
    ((NNReal.continuous_coe.tendsto a₀).comp ((hA0 ▸ hAc.tendsto 0).comp huN0))
    (B := fun n => GW2Rd.schedUnionX c r [] a 0 (uN n) ω)
    (fun n => hshape (uN n) (huNle n)) (V := V) (fun n => by
      intro w hw
      rw [hU (uN n)]
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
  have hc₁ := stage_farX hW'0 hW' hsζ hR hR0 x a₀ (S₁ := fun n => cL.2.1 '' (invHull Uk (t₀ + (vN n : ℝ)) \
    invHull Uk t₀)) hwpos hw0 (fun n => by
      rintro z ⟨w', hw', rfl⟩
      have hq := hcont (t₀ + vN n)
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
    (fun n => NNReal.coe_pos.2 (hvNpos n)) ((NNReal.continuous_coe.tendsto 0).comp hvN0) hcn hc₁
  -- the driver relation
  have hdomL' : (cL.dom : Set ℂ) = H \ (∅ : Set ℂ) := by rw [hdomL, sdiff_empty]
  obtain ⟨hS, hq⟩ := sample_driver_scale hconf hc₀ hR hR0 hUkc hUk0 hlam hdil hA0 hAa hAc.continuousOn hshape hdomL'
    (fun _ _ => empty_subset _) hRk hRk0 hhull hdisj (fun u hu => by rw [hU u, hWcK u hu])
  exact ⟨lam, hlam, hdil, hcsdom, hmaps, hS, hq⟩

end InteractingSLE.Theorem14.GW2Kx
