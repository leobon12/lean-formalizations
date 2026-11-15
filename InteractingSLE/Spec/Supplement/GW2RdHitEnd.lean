/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdHitSet
import InteractingSLE.Spec.Supplement.GW2RdExt
import InteractingSLE.Spec.Supplement.GW2RdVer
import InteractingSLE.Spec.Supplement.GB7aCmpPath
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Sec4.Aux25Term
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal

/-!
# GW2's lifetime as a hitting time, part 3: the terminal landing; `FlowLifetimeHitStatement`

Packet PROVE-GW2-RELDET. At a finite positive lifetime `T` the flow-line state converges to a threshold state (Aux.
lemma 3), say on the right, with colliding group `S` of weight `≤ −2`; let `k = max S`. Then (deterministically,
`exists_landing_right`):

* `x^R_k` is alive before `T` and its centred flow tends to `0` (`Sec2.IsForcePath.exists_gapR_of_tendsto`,
  `isForwardSol_gapR`), so the trace at `T` is a real point `y ≥ x^R_k` (Aux. lemma 25's ray lemma,
  `Aux25.exists_eq_ray_of_tendsto_fwdMap`);
* every later mark `x^R_j` (`j > k`) lies beyond `y`: otherwise its centred flow, bounded below on `[0, T)` (its gap
  is positive there and tends to `V^j_T − W_T > 0` since `j ∉ S`), continues to `[0, T]`
  (`exists_isForwardSol_of_forall_lt`), so `y ≥ x^R_j` is alive at `T` and is not on the trace up to `T`
  (`IsLoewnerTraceLT.ofReal_not_mem_image_of_isForwardSol`, on the trace of the regularized driver beyond `T`,
  `GW2Rd.ae_extTr_spec`) — but `y` is the trace at `T`;
* hence the marks `≤ y` are exactly `S` and `y` is a right bad point.

The left side is the right side of the reflected path (`Sec2.IsForcePath.reflect`, `LP.isGeneratingTrace_reflect`).
With part 2 (`GW2RdHitSet`) this proves **`FlowLifetimeHitStatement`** (`flowLifetimeHitStatement`), hence
GW2's version statement from Theorem 1.3 alone (`gw2RdVersionStatement_of_thm13`) and GW2's root determination from
Theorems 1.2–1.3 and the relative safe law (`gw2JointDetC2Statement_of_thm12_thm13_safe`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap IsForwardSol)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open GW2TipSystem

/-! ### The deterministic landing -/

section Landing

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The landing at a right threshold.** Let a force path reach at the finite positive lifetime `T` a threshold
state whose right colliding group has weight `≤ −2`, and let `η` generate on `[0, ∞)` the chain of a continuous driver
agreeing with `w` before `T`. Then `η(T)` is a real point `y > 0` whose marks `x^R_i ≤ y` carry total weight
`≤ −2`. -/
theorem exists_landing_right (hf : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hxR : StrictMono xR)
    {T : ℝ≥0} (hT0 : 0 < T) (hT : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hconv : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hR : ∑ i ∈ univ.filter (fun i => vR₀ i = w₀), ρR i ≤ -2)
    {w' : ℝ≥0 → ℝ} (hw'c : Continuous w') (hw'0 : w' 0 = 0) (hw'w : ∀ t : ℝ≥0, t < T → w' t = w t)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w' ⊤ η) :
    ∃ y : ℝ, η T = y ∧ 0 < y ∧ ∑ i ∈ univ.filter (fun i => xR i ≤ y), ρR i ≤ -2 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  have hlt : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ := fun t ht => hT ▸ (by exact_mod_cast ht)
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hconv
  have hv : ∀ j, Tendsto (vR j) (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    ((continuous_apply j).tendsto _).comp ((continuous_snd.comp continuous_snd).tendsto _ |>.comp hconv)
  have : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
  have hev : ∀ᶠ t in 𝓝[<] T, t < T := self_mem_nhdsWithin
  have hle : ∀ j, w₀ ≤ vR₀ j := fun j =>
    le_of_tendsto_of_tendsto hw (hv j) (hev.mono fun t ht => hf.w_le_vR (hlt t ht) j)
  have hmono : ∀ i j : Fin nR, i ≤ j → vR₀ i ≤ vR₀ j := fun i j hij =>
    le_of_tendsto_of_tendsto (hv i) (hv j) (hev.mono fun t ht => hf.monotone_vR (hlt t ht) hij)
  -- the last member `k` of the colliding group
  obtain ⟨k₁, hk₁sep, hk₁⟩ := hf.exists_gapR_of_tendsto hT0 hT hconv hR
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin nR), S = univ.filter (fun i => vR₀ i = w₀) := ⟨_, rfl⟩
  have hmemS : ∀ i, i ∈ S ↔ vR₀ i = w₀ := fun i => by
    rw [hSdef, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  have hk₁S : k₁ ∈ S := (hmemS k₁).2 hk₁
  obtain ⟨k, hkdef⟩ : ∃ k, k = S.max' ⟨k₁, hk₁S⟩ := ⟨_, rfl⟩
  have hkS : k ∈ S := hkdef ▸ S.max'_mem _
  have hmaxS : ∀ i ∈ S, i ≤ k := fun i hi => hkdef ▸ S.le_max' i hi
  have hk0 : vR₀ k = w₀ := (hmemS k).1 hkS
  have hsep : ∀ j, k ≤ j → ∀ t : ℝ≥0, t < T → w t < vR j t := fun j hkj t ht =>
    (hk₁sep t ht).trans_le (hf.monotone_vR (hlt t ht) ((hmaxS k₁ hk₁S).trans hkj))
  -- the driver and the trace on the real line
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ → ℝ, U = fun r => w' r.toNNReal := ⟨_, rfl⟩
  have hU : Continuous U := hUdef ▸ hw'c.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by rw [hUdef]; simp [hw'0]
  have hUeq : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal := fun r hr hrT => by
    rw [hUdef]
    exact hw'w _ (by rw [Real.toNNReal_lt_iff_lt_coe hr]; exact hrT)
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ → ℂ, γ = fun s => η s.toNNReal := ⟨_, rfl⟩
  have hLT : IsLoewnerTraceLT U ((T + 1 : ℝ≥0) : ℝ) γ := by
    rw [hγdef]
    exact GB7a.isLoewnerTraceLT_of_agree hη le_top fun s _ _ => by rw [hUdef]
  have hTT1 : (T : ℝ) < ((T + 1 : ℝ≥0) : ℝ) := by push_cast; linarith
  have hγT : γ T = η T := by rw [hγdef]; simp
  -- the centred flows of the separated marks
  have hsol : ∀ j, k ≤ j → ∀ r : ℝ, r < T →
      IsForwardSol U (xR j : ℂ) r (Sec2.IsForcePath.gapR vR w j) := fun j hkj r hr =>
    hf.isForwardSol_gapR hT (hsep j hkj) hUeq hr
  -- Step 1: the trace at `T` is a real point `y ≥ x^R_k`
  have hy₀ : 0 < xR k := by
    have := hsep k le_rfl 0 hT0
    rwa [hf.w_zero, hf.vR_zero] at this
  have hm : Tendsto Real.toNNReal (𝓝[<] (T : ℝ)) (𝓝[<] T) := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hT']
    exact Sec2.IsForcePath.tendsto_toNNReal_nhdsLT T
  have hlim0 : Tendsto (fun r => fwdMap U r (xR k)) (𝓝[<] (T : ℝ)) (𝓝 0) := by
    have hgap : Tendsto (fun t => vR k t - w t) (𝓝[<] T) (𝓝 0) := by
      simpa [hk0] using (hv k).sub hw
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp (hgap.comp hm)
    rw [Complex.ofReal_zero] at h2
    refine h2.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hT'] with r hr
    exact (fwdMap_eq_of_isForwardSol hU (hsol k le_rfl r hr.2) ⟨hr.1.le, le_rfl⟩).symm
  have hfill : ∀ t ∈ Ico (0 : ℝ) T, IsFilling (QuantumZipper.fwdHull U t) (γ '' Icc 0 t) := by
    intro t ht
    have hf' := hη.2.2 t.toNNReal ENNReal.coe_lt_top
    rw [Real.coe_toNNReal _ ht.1] at hf'
    rw [hγdef, image_toNNReal_Icc η ht.1, hUdef]
    exact hf'
  have hγc : ContinuousOn γ (Icc 0 T) := hLT.2.1.mono fun s hs => ⟨hs.1, hs.2.trans_lt hTT1⟩
  obtain ⟨y, hky, hγy⟩ := Aux25.exists_eq_ray_of_tendsto_fwdMap hU hU0 hT' hy₀ hLT.1 hγc hfill
    (fun r hr => ⟨_, hsol k le_rfl r hr.2⟩) hlim0
  -- Step 2: every later mark lies beyond `y`
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} = Iio T := by rw [← hT]; exact Sec2.setOf_lt_coe_eq_Iio T
  have hwc : ContinuousOn w (Iio T) := hset ▸ hf.continuousOn_w
  have hbeyond : ∀ j, k < j → y < xR j := by
    intro j hkj
    by_contra hjy
    have hjy' : xR j ≤ y := not_lt.1 hjy
    have hjne : vR₀ j ≠ w₀ := fun he => absurd (hmaxS j ((hmemS j).2 he)) (not_le.2 hkj)
    have hLpos : 0 < vR₀ j - w₀ := sub_pos.2 (lt_of_le_of_ne (hle j) (Ne.symm hjne))
    have hvc : ContinuousOn (vR j) (Iio T) := hset ▸ hf.continuousOn_vR j
    obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = fun s =>
        FiniteEndpoint.extDriver (vR j) T (vR₀ j) s - FiniteEndpoint.extDriver w T w₀ s := ⟨_, rfl⟩
    have hGc : Continuous G := hGdef ▸
      (FiniteEndpoint.continuous_extDriver hvc (hv j)).sub (FiniteEndpoint.continuous_extDriver hwc hw)
    have hGlt : ∀ s : ℝ, 0 ≤ s → s < T → G s = vR j s.toNNReal - w s.toNNReal := fun s hs hsT => by
      rw [hGdef]
      simp only
      rw [FiniteEndpoint.extDriver_of_lt hs hsT, FiniteEndpoint.extDriver_of_lt hs hsT]
    have hGT : G T = vR₀ j - w₀ := by
      rw [hGdef]
      simp [FiniteEndpoint.extDriver]
    have hGpos : ∀ s ∈ Icc (0 : ℝ) T, 0 < G s := by
      intro s hs
      rcases hs.2.lt_or_eq with hsT | hsT
      · rw [hGlt s hs.1 hsT]
        exact sub_pos.2 (hsep j hkj.le _ (by rw [Real.toNNReal_lt_iff_lt_coe hs.1]; exact hsT))
      · rw [hsT, hGT]
        exact hLpos
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT'.le) hGc.continuousOn
    have hc := hGpos s₀ hs₀
    have hge : ∀ s ∈ Ico (0 : ℝ) T, G s₀ ≤ (fwdMap U s (xR j)).re := by
      intro s hs
      rw [fwdMap_eq_of_isForwardSol hU (hsol j hkj.le s hs.2) ⟨hs.1, le_rfl⟩]
      have h1 := isMinOn_iff.1 hmin s ⟨hs.1, hs.2.le⟩
      rw [hGlt s hs.1 hs.2] at h1
      simpa [Sec2.IsForcePath.gapR] using h1
    obtain ⟨vj, hvj⟩ := exists_isForwardSol_of_forall_lt hU hU0 hT'
      (fun s hs => ⟨_, hsol j hkj.le s hs.2⟩) hc hge
    have hxj : 0 < xR j := hy₀.trans (hxR hkj)
    obtain ⟨vy, hvy⟩ : ∃ v, IsForwardSol U (y : ℂ) T v := by
      rcases hjy'.lt_or_eq with hlt' | heq
      · exact QuantumZipper.RS.exists_isForwardSol_of_lt hU hT'.le (by rw [hU0]; exact hxj) hlt' hvj
      · exact ⟨vj, heq ▸ hvj⟩
    exact hLT.ofReal_not_mem_image_of_isForwardSol hU hU0 hT'.le hTT1 hvy
      ⟨T, ⟨NNReal.coe_nonneg T, le_rfl⟩, hγy⟩
  -- Step 3: the marks `≤ y` are the colliding group
  have hfilter : univ.filter (fun i => xR i ≤ y) = S := by
    ext i
    rw [hmemS i, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_contra hne
      have hik : ¬ i ≤ k := fun hik =>
        hne (le_antisymm ((hmono i k hik).trans hk0.le) (hle i))
      exact absurd hi (not_le.2 (hbeyond i (not_le.1 hik)))
    · intro hi
      exact (hxR.monotone (hmaxS i ((hmemS i).2 hi))).trans hky
  refine ⟨y, by rw [← hγT, hγy], hy₀.trans_le hky, ?_⟩
  rw [hfilter, hSdef]
  exact hR

end Landing

/-! ### Clause 2 and the statement -/

section Hit

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}

/-- **Clause 2 of `FlowLifetimeHitStatement`**: almost surely, at a finite positive lifetime the flow line is in the
hitting set. -/
theorem ae_trace_mem_hitSet_at_lifetime [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζα ω → 0 < T → α ω T ∈ hitSet κ b J θ := by
  have hext := ae_extTr_spec hκ hfl hα 0
  obtain ⟨h', 𝓕, VL, VR, B, -, hcpl⟩ := hfl
  have hE := hcpl.1
  filter_upwards [hE.ae_tendsto_threshold hκ, hE.ae_isIntegratedSLEPath, hext] with ω hthr hp hx T hT hT0
  have hpos : 0 < ζα ω := by rw [← hT]; exact_mod_cast hT0
  obtain ⟨hUc, hU0, hUeq, hgen, hagree⟩ := hx hpos
  obtain ⟨w₀, vL₀, vR₀, hconv, hth⟩ := hthr T hT0 hT
  have hf := hp.isForcePath
  have hUeq' : ∀ t : ℝ≥0, t < T → regW 0 Wα ζα t ω = Wα t ω := fun t ht =>
    hUeq t (by rw [← hT]; exact_mod_cast ht)
  rw [← hagree T (le_of_eq hT)]
  rcases hth with hL | hR
  · -- left threshold: the right landing of the reflected path
    have hLr : ∑ i ∈ univ.filter (fun i => (fun i => -vL₀ i) i = -w₀), flowLineRhoL κ b J 0 θ i ≤ -2 := by
      simpa only [neg_inj] using hL
    have hconv' : Tendsto (fun t => ((-(fun t => Wα t ω)) t, fun i => (fun i t => -VR i t ω) i t,
        fun i => (fun i t => -VL i t ω) i t)) (𝓝[<] T) (𝓝 (-w₀, fun i => -vR₀ i, fun i => -vL₀ i)) := by
      have hc : Continuous fun p : ℝ × (Fin (flowLineNL b J 0) → ℝ) × (Fin (flowLineNR b J 0) → ℝ) =>
          (-p.1, fun i => -p.2.2 i, fun i => -p.2.1 i) := by fun_prop
      exact (hc.tendsto _).comp hconv
    have hanti : StrictMono (-flowLineXL b J 0) := fun i j hij => by
      simp only [Pi.neg_apply]
      exact neg_lt_neg (Theorem14.GW0.flowLineXL_lt b J 0 hij)
    obtain ⟨y, hy, hy0, hs⟩ := exists_landing_right hf.reflect hanti hT0 hT hconv' hLr hUc.neg
      (by simp [hU0]) (fun t ht => congrArg Neg.neg (hUeq' t ht)) (LP.isGeneratingTrace_reflect hgen)
    have hyT : extTr 0 Wα ζα α ω T = ((-y : ℝ) : ℂ) := by
      have e := congrArg LP.reflectC hy
      simp only [LP.reflectC_reflectC] at e
      rw [e]
      simp [LP.reflectC]
    rw [hyT]
    refine ofReal_mem_hitSet (Or.inr ⟨by linarith, ?_⟩)
    have hF : univ.filter (fun i => -y ≤ flowLineXL b J 0 i) =
        univ.filter (fun i => (-flowLineXL b J 0) i ≤ y) := by
      refine Finset.filter_congr fun i _ => ?_
      simp only [Pi.neg_apply]
      constructor <;> intro h₁ <;> linarith
    rw [hF]
    exact hs
  · have hxR : StrictMono (flowLineXR b J 0) := fun i j hij => Theorem14.GW0.flowLineXR_lt b J 0 hij
    obtain ⟨y, hy, hy0, hs⟩ := exists_landing_right hf hxR hT0 hT hconv hR hUc hU0 hUeq' hgen
    rw [hy]
    exact ofReal_mem_hitSet (Or.inl ⟨hy0, hs⟩)

end Hit

/-- **`FlowLifetimeHitStatement`, proved**: the closed set `hitSet κ b J θ` is avoided strictly before the lifetime
and hit at a finite positive lifetime. -/
theorem flowLifetimeHitStatement : FlowLifetimeHitStatement.{u} := by
  intro κ θ hκ hκ4 _ _ Ω _ P hP h b J Wα ζα α hb hh hfl hα
  have := hP
  refine ⟨hitSet κ b J θ, isClosed_hitSet, ?_⟩
  filter_upwards [ae_trace_notMem_hitSet hκ hκ4 hb hh hfl hα, ae_trace_mem_hitSet_at_lifetime hκ hfl hα]
    with ω h1 h2
  exact ⟨h1, fun T hT hT0 => h2 T hT hT0⟩

/-- **GW2's version statement from Theorem 1.3 alone.** -/
theorem gw2RdVersionStatement_of_thm13 (h13 : Exist.Theorem13Statement.{u}) : GW2RdVersionStatement.{u} :=
  gw2RdVersionStatement_of_thm13_hit h13 flowLifetimeHitStatement

/-- **GW2's root determination from Theorems 1.2–1.3 and the relative safe law.** -/
theorem gw2JointDetC2Statement_of_thm12_thm13_safe (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (hS : GW2RdSafeStatement.{u}) :
    GW2JointKernel.GW2JointDetC2Statement.{u} :=
  gw2JointDetC2Statement_of_thm12_thm13_hit h12p₀ h13₀ h13 flowLifetimeHitStatement hS

end InteractingSLE.Theorem14.GW2Rd
