/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LifeEnd
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Supplement.LPProbReflect

/-!
# Proposition GB6, step (e): the incident images of the flow range lie in the filled base

Packet PROVE-GB6D. Proof of **`GB6BaseStatement`** (GB6's proof, p. 519: "Outside `[a, b]`, the inverse chart maps the
two real rays monotonically onto untouched original-real rays disjoint from the flow range").

* `not_isForwardSol_of_tip`: a real point with a forward solution up to time `t` (not yet swallowed) is not the tip
  `α(t)`: along `w → 0` in `ℍ`, `f_t⁻¹(w) → α(t)` and `f_t` is continuous at a point with a forward solution, so
  `w = f_t(f_t⁻¹(w))` would tend to the nonzero `u_t`;
* `exists_extendFrom_eq_alive_of_lt`: beyond the right end `V̂^{0,R}_s` of the base, the boundary extension `F̄_s` of
  `f_s⁻¹` takes a real value `x₀` with `x₀` alive at `s` (`F̄_s` at images of alive points, `exists_alive_gImg_mem`,
  limits of alive points above a fixed alive point are alive);
* `exists_extendFrom_eq_of_lt_baseL`: the mirror image beyond the left end (reflection of forward solutions,
  `LP.isForwardSol_neg`);
* **`gb6BaseStatement`**: if `f_s(z_n) → y` outside the base, then `z_n = F̄_s(f_s(z_n)) → F̄_s(y) = x₀`, a real point
  with a forward solution up to `s`, which is no point of `α([0, s])`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp8

namespace GB6

open MartChar.RealFlow

/-! ### The real flow only reads the driver up to the current time -/

theorem isPosSol_congr {w w' : ℝ → ℝ} {y t : ℝ} {X : ℝ → ℝ} (h : ∀ r ∈ Icc (0 : ℝ) t, w r = w' r)
    (hX : IsPosSol w y t X) : IsPosSol w' y t X :=
  ⟨hX.1, fun r hr => by rw [← h r hr]; exact hX.2 r hr⟩

theorem alive_congr {w w' : ℝ → ℝ} {y t : ℝ} (h : ∀ r ∈ Icc (0 : ℝ) t, w r = w' r) :
    Alive w y t ↔ Alive w' y t :=
  ⟨fun ⟨X, hX⟩ => ⟨X, isPosSol_congr h hX⟩, fun ⟨X, hX⟩ => ⟨X, isPosSol_congr (fun r hr => (h r hr).symm) hX⟩⟩

theorem gImg_congr {w w' : ℝ → ℝ} (hw' : Continuous w') {y t : ℝ} (ht : 0 ≤ t)
    (h : ∀ r ∈ Icc (0 : ℝ) t, w r = w' r) (hy : Alive w y t) : gImg w y t = gImg w' y t := by
  have hc : cflow w y t = cflow w' y t := by
    have hX := hy.choose_spec
    have e1 : cflow w y t = hy.choose t := by simp only [cflow, hy, ↓reduceDIte]
    rw [e1, cflow_eq_of_isPosSol hw' (isPosSol_congr h hX) ⟨ht, le_rfl⟩]
  rw [gImg, gImg, hc, h t ⟨ht, le_rfl⟩]

theorem rightImg_congr {w w' : ℝ → ℝ} (hw' : Continuous w') {x t : ℝ} (ht : 0 ≤ t)
    (h : ∀ r ∈ Icc (0 : ℝ) t, w r = w' r) : rightImg w x t = rightImg w' x t := by
  have e : imgSet w x t = imgSet w' x t := by
    ext g
    simp only [imgSet, mem_ofPred_eq]
    constructor
    · rintro ⟨y, hxy, hy, rfl⟩
      exact ⟨y, hxy, (alive_congr h).1 hy, (gImg_congr hw' ht h hy).symm⟩
    · rintro ⟨y, hxy, hy, rfl⟩
      have hy' := (alive_congr h).2 hy
      exact ⟨y, hxy, hy', gImg_congr hw' ht h hy'⟩
  rw [rightImg, rightImg, e]

theorem baseR_congr {w w' : ℝ → ℝ} (hw' : Continuous w') {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ r ∈ Icc (0 : ℝ) t, w r = w' r) : baseR w t = baseR w' t := by
  rw [baseR, baseR, rightImg_congr hw' ht h, h t ⟨ht, le_rfl⟩]

theorem baseL_congr {w w' : ℝ → ℝ} (hw' : Continuous w') {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ r ∈ Icc (0 : ℝ) t, w r = w' r) : baseL w t = baseL w' t := by
  have h' : ∀ r ∈ Icc (0 : ℝ) t, (fun r => -w r) r = (fun r => -w' r) r := fun r hr => by
    simp only [h r hr]
  rw [baseL, baseL, rightImg_congr hw'.neg ht h', h t ⟨ht, le_rfl⟩]
  rfl

/-! ### Points with a forward solution are not the tip -/

/-- **A real point with a forward solution up to time `t` is not the tip `α(t)`.** -/
theorem not_isForwardSol_of_tip {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {t : ℝ} (ht : 0 ≤ t) {p : ℂ}
    (htip : Tendsto (QuantumZipper.fwdMapInv U t) (𝓝[H] 0) (𝓝 p)) {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol U p t u) : False := by
  have hF : Tendsto (QuantumZipper.fwdMapInv U t) (𝓝[H] 0) (𝓝[H] p) :=
    tendsto_nhdsWithin_iff.2 ⟨htip, eventually_nhdsWithin_of_forall fun w hw =>
      (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 ht hw).1⟩
  have h1 : Tendsto (fun w => QuantumZipper.fwdMap U t (QuantumZipper.fwdMapInv U t w)) (𝓝[H] 0) (𝓝 (u t)) :=
    (tendsto_fwdMap_of_isForwardSol hU ht hu).comp hF
  have h2 : Tendsto (fun w => QuantumZipper.fwdMap U t (QuantumZipper.fwdMapInv U t w)) (𝓝[H] 0) (𝓝 0) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
      (eventually_nhdsWithin_of_forall fun w hw => (QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 ht hw).symm)
  have hNe : (𝓝[H] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [closure_H]; show (0 : ℝ) ≤ (0 : ℂ).im; simp)
  exact (hu.2 t ⟨ht, le_rfl⟩).1 (tendsto_nhds_unique h1 h2)

/-! ### Beyond the base, the boundary extension lands on points with a forward solution -/

/-- The boundary extension at a real limit of real points where it is known. -/
theorem tendsto_extendFrom_of_real {U : ℝ → ℝ} {s : ℝ} (hB : HasBdryLimits (QuantumZipper.fwdMapInv U s))
    {c : ℕ → ℝ} {y : ℝ} (hc : Tendsto c atTop (𝓝 y)) :
    Tendsto (fun n => extendFrom H (QuantumZipper.fwdMapInv U s) (c n : ℂ)) atTop
      (𝓝 (extendFrom H (QuantumZipper.fwdMapInv U s) (y : ℂ))) := by
  have hyH : (y : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hcH : Tendsto (fun n => (c n : ℂ)) atTop (𝓝[Hbar] (y : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto y).comp hc,
      Eventually.of_forall fun n => show (0 : ℝ) ≤ ((c n : ℝ) : ℂ).im by simp⟩
  exact (hB.continuousOn _ hyH).tendsto.comp hcH

/-- **Beyond the right end of the base**, `F̄_s(y)` is a real point alive at `s`. -/
theorem exists_extendFrom_eq_alive_of_gt {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hB : HasBdryLimits (QuantumZipper.fwdMapInv U s)) {y : ℝ} (hy : baseR U s < y) :
    ∃ x₀ : ℝ, extendFrom H (QuantumZipper.fwdMapInv U s) (y : ℂ) = (x₀ : ℂ) ∧ Alive U x₀ s := by
  have hM : rightImg U 0 s ≤ y + U s := by unfold baseR at hy; linarith
  have hseq : ∀ n : ℕ, ∃ p, 0 < p ∧ Alive U p s ∧ y + U s < gImg U p s ∧
      gImg U p s < y + U s + 1 / ((n : ℝ) + 1) := fun n => exists_alive_gImg_mem hU hs (by positivity) hM
  choose p hp0 hpa hpl hpu using hseq
  have hδ : 0 < y - baseR U s := by linarith
  obtain ⟨q, -, hqa, -, hqu⟩ := exists_alive_gImg_mem hU hs (half_pos hδ) (le_refl (rightImg U 0 s))
  have hqy : gImg U q s < y + U s := by have := hqu; unfold baseR at this; linarith
  have hpq : ∀ n, q < p n := by
    intro n
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · have h1 := (cflow_lt_and_sub_le hU (hpa n) hlt hs ⟨hs, le_rfl⟩).1
      have h2 : gImg U (p n) s < gImg U q s := by simp only [gImg]; linarith
      linarith [hpl n]
    · have := hpl n; rw [heq] at this; linarith
  set c : ℕ → ℝ := fun n => gImg U (p n) s - U s with hcdef
  have hc : Tendsto c atTop (𝓝 y) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => y) (h := fun n : ℕ => y + 1 / ((n : ℝ) + 1))
      tendsto_const_nhds ?_ (fun n => ?_) (fun n => ?_)
    · simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · have := hpl n; simp only [hcdef]; linarith
    · have := hpu n; simp only [hcdef]; linarith
  have hF : ∀ n, extendFrom H (QuantumZipper.fwdMapInv U s) (c n : ℂ) = (p n : ℂ) := fun n => by
    have h := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hU hU0 hs
      (show ((p n : ℝ) : ℂ) ∈ Hbar from show (0 : ℝ) ≤ ((p n : ℝ) : ℂ).im by simp)
      (WangWu.isForwardSol_of_alive hU (hpa n))
    have e : ((cflow U (p n) s : ℝ) : ℂ) = ((c n : ℝ) : ℂ) := by simp only [hcdef, gImg]; push_cast; ring
    rwa [e] at h
  have hlim := tendsto_extendFrom_of_real hB hc
  simp_rw [hF] at hlim
  set L := extendFrom H (QuantumZipper.fwdMapInv U s) (y : ℂ) with hLdef
  have hre : Tendsto p atTop (𝓝 L.re) :=
    ((Complex.continuous_re.tendsto L).comp hlim).congr fun n => by simp
  have him : L.im = 0 := by
    have h : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 L.im) :=
      ((Complex.continuous_im.tendsto L).comp hlim).congr fun n => by simp
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hqL : q ≤ L.re := ge_of_tendsto hre (Eventually.of_forall fun n => (hpq n).le)
  exact ⟨L.re, Complex.ext (by simp) (by simp [him]), hqa.of_le hU hqL hs⟩

/-- **Beyond the left end of the base**, `F̄_s(y)` is a real point with a forward solution up to `s` (the mirror image
of `exists_extendFrom_eq_alive_of_gt`, through the reflected driver). -/
theorem exists_extendFrom_eq_of_lt_baseL {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hB : HasBdryLimits (QuantumZipper.fwdMapInv U s)) {y : ℝ} (hy : y < baseL U s) :
    ∃ x₀ : ℝ, extendFrom H (QuantumZipper.fwdMapInv U s) (y : ℂ) = (x₀ : ℂ) ∧
      ∃ u, QuantumZipper.IsForwardSol U (x₀ : ℂ) s u := by
  set V : ℝ → ℝ := fun r => -U r with hVdef
  have hV : Continuous V := hU.neg
  have hVV : (-V) = U := by funext r; simp [hVdef]
  -- forward solutions of `U` from reflected alive points of `V`
  have hrefl : ∀ {p : ℝ}, Alive V p s →
      QuantumZipper.IsForwardSol U ((-p : ℝ) : ℂ) s (fun r => LP.reflectC ((cflow V p r : ℝ) : ℂ)) := by
    intro p hp
    have h := LP.isForwardSol_neg (WangWu.isForwardSol_of_alive hV hp)
    rw [hVV] at h
    have e : LP.reflectC ((p : ℝ) : ℂ) = ((-p : ℝ) : ℂ) := by simp [LP.reflectC]
    rwa [e] at h
  have hM : rightImg V 0 s ≤ -y + V s := by
    have : baseL U s = -rightImg V 0 s - U s := rfl
    simp only [hVdef]; linarith
  have hseq : ∀ n : ℕ, ∃ p, 0 < p ∧ Alive V p s ∧ -y + V s < gImg V p s ∧
      gImg V p s < -y + V s + 1 / ((n : ℝ) + 1) := fun n => exists_alive_gImg_mem hV hs (by positivity) hM
  choose p hp0 hpa hpl hpu using hseq
  have hδ : 0 < -y + V s - rightImg V 0 s := by
    have : baseL U s = -rightImg V 0 s - U s := rfl
    simp only [hVdef]; linarith
  obtain ⟨q, -, hqa, -, hqu⟩ := exists_alive_gImg_mem hV hs (half_pos hδ) (le_refl (rightImg V 0 s))
  have hpq : ∀ n, q < p n := by
    intro n
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · have h1 := (cflow_lt_and_sub_le hV (hpa n) hlt hs ⟨hs, le_rfl⟩).1
      have h2 : gImg V (p n) s < gImg V q s := by simp only [gImg]; linarith
      linarith [hpl n]
    · have := hpl n; rw [heq] at this; linarith
  set c : ℕ → ℝ := fun n => -(gImg V (p n) s - V s) with hcdef
  have hc : Tendsto c atTop (𝓝 y) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => y - 1 / ((n : ℝ) + 1)) (h := fun _ => y)
      ?_ tendsto_const_nhds (fun n => ?_) (fun n => ?_)
    · simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · have := hpu n; simp only [hcdef]; linarith
    · have := hpl n; simp only [hcdef]; linarith
  have hF : ∀ n, extendFrom H (QuantumZipper.fwdMapInv U s) (c n : ℂ) = ((-p n : ℝ) : ℂ) := fun n => by
    have h := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hU hU0 hs
      (show ((-p n : ℝ) : ℂ) ∈ Hbar from show (0 : ℝ) ≤ ((-p n : ℝ) : ℂ).im by simp) (hrefl (hpa n))
    have e : LP.reflectC ((cflow V (p n) s : ℝ) : ℂ) = ((c n : ℝ) : ℂ) := by
      simp only [hcdef, gImg, LP.reflectC, Complex.conj_ofReal]; push_cast; ring
    rwa [e] at h
  have hlim := tendsto_extendFrom_of_real hB hc
  simp_rw [hF] at hlim
  set L := extendFrom H (QuantumZipper.fwdMapInv U s) (y : ℂ) with hLdef
  have hre : Tendsto (fun n => -p n) atTop (𝓝 L.re) :=
    ((Complex.continuous_re.tendsto L).comp hlim).congr fun n => by simp
  have him : L.im = 0 := by
    have h : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 L.im) :=
      ((Complex.continuous_im.tendsto L).comp hlim).congr fun n => by simp
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hqL : q ≤ -L.re := by
    have := hre.neg
    simp only [neg_neg] at this
    exact ge_of_tendsto this (Eventually.of_forall fun n => (hpq n).le)
  have hal : Alive V (-L.re) s := hqa.of_le hV hqL hs
  have h := hrefl hal
  rw [neg_neg] at h
  exact ⟨L.re, Complex.ext (by simp) (by simp [him]), _, h⟩

/-! ### The base statement -/

/-- **`GB6BaseStatement` holds**: the finite incident images of the flow range lie in the filled base. -/
theorem gb6BaseStatement : GB6BaseStatement := by
  intro wα Tα α s hα hwα hwα0 hs z zs y hzK hz hzs hfz
  obtain ⟨t₂, hst₂, ht₂⟩ := exists_real_btwn_of_lt hs
  set U' : ℝ → ℝ := frozenDrive wα t₂ with hU'def
  have hU' : Continuous U' := continuous_frozenDrive_of_lt hwα ht₂
  have ht₂0 : (0 : ℝ) ≤ t₂ := le_trans (NNReal.coe_nonneg s) hst₂.le
  have hU'0 : U' 0 = 0 := by rw [hU'def, frozenDrive_zero ht₂0, hwα0]
  have hagree : ∀ r ∈ Icc (0 : ℝ) t₂, wα r.toNNReal = U' r := fun r hr => (frozenDrive_eq hr).symm
  have hagree_s : ∀ r ∈ Icc (0 : ℝ) s, wα r.toNNReal = U' r := fun r hr => hagree r ⟨hr.1, hr.2.trans hst₂.le⟩
  have hB : HasBdryLimits (QuantumZipper.fwdMapInv U' s) :=
    (hα.isLoewnerTraceLT ht₂).hasBdryLimits hU' hU'0 (NNReal.coe_nonneg s) hst₂
  have hhull : QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) s = QuantumZipper.fwdHull U' s :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
  have hfz' : Tendsto (fun n => QuantumZipper.fwdMap U' s (z n)) atTop (𝓝 (y : ℂ)) := by
    have e : ∀ n, QuantumZipper.fwdMap U' s (z n) = QuantumZipper.fwdMap (fun r : ℝ => wα r.toNNReal) s (z n) :=
      fun n => (fwdMap_eq_of_eqOn (NNReal.coe_nonneg s) hagree_s).symm
    simp_rw [e]; exact hfz
  have hzK' : ∀ n, z n ∈ H \ QuantumZipper.fwdHull U' s := fun n => by rw [← hhull]; exact hzK n
  -- `z_n = F̄_s(f_s(z_n)) → F̄_s(y)`
  have hzF : ∀ n, z n = extendFrom H (QuantumZipper.fwdMapInv U' s) (QuantumZipper.fwdMap U' s (z n)) := fun n =>
    (WangWu.extendFrom_fwdMap hU' hU'0 (NNReal.coe_nonneg s) (hzK' n)).symm
  have hyH : (y : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hfzH : Tendsto (fun n => QuantumZipper.fwdMap U' s (z n)) atTop (𝓝[Hbar] (y : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hfz', Eventually.of_forall fun n =>
      show (0 : ℝ) ≤ (QuantumZipper.fwdMap U' s (z n)).im from
        le_of_lt (QuantumZipper.FwdHolo.mapsTo_fwdMap hU' (NNReal.coe_nonneg s) (hzK' n))⟩
  have hzlim : Tendsto z atTop (𝓝 (extendFrom H (QuantumZipper.fwdMapInv U' s) (y : ℂ))) := by
    have := (hB.continuousOn _ hyH).tendsto.comp hfzH
    refine this.congr fun n => ?_
    exact (hzF n).symm
  have hzs_eq : zs = extendFrom H (QuantumZipper.fwdMapInv U' s) (y : ℂ) := tendsto_nhds_unique hz hzlim
  -- a real point with a forward solution up to `s` is not on `α([0, s])`
  have hnot : ∀ (x₀ : ℝ) (u : ℝ → ℂ), QuantumZipper.IsForwardSol U' (x₀ : ℂ) s u → (x₀ : ℂ) ∉ α '' Icc 0 s := by
    rintro x₀ u hu ⟨t, ht, hαt⟩
    have hts : (t : ℝ) ≤ s := by exact_mod_cast ht.2
    have hut : QuantumZipper.IsForwardSol U' (x₀ : ℂ) t u :=
      ⟨hu.1.mono (Icc_subset_Icc_right hts), fun r hr => hu.2 r ⟨hr.1, hr.2.trans hts⟩⟩
    have htTα : (t : ℝ≥0∞) < Tα := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hs
    have htip : Tendsto (QuantumZipper.fwdMapInv U' t) (𝓝[H] 0) (𝓝 (α t)) := by
      have h1 := IsGeneratingTrace.tendsto_fwdMapInv_tip hα hwα hwα0 htTα
      have h2 : QuantumZipper.fwdMapInv (fun r : ℝ => wα r.toNNReal) t = QuantumZipper.fwdMapInv U' t :=
        fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg t) (lt_of_le_of_lt hts hst₂) hagree
      rw [← h2]; exact h1
    rw [hαt] at htip
    exact not_isForwardSol_of_tip hU' hU'0 (NNReal.coe_nonneg t) htip hut
  constructor
  · by_contra hlt
    push Not at hlt
    rw [baseL_congr hU' (NNReal.coe_nonneg s) hagree_s] at hlt
    obtain ⟨x₀, hx₀, u, hu⟩ := exists_extendFrom_eq_of_lt_baseL hU' hU'0 (NNReal.coe_nonneg s) hB hlt
    rw [hzs_eq, hx₀] at hzs
    exact hnot x₀ u hu hzs
  · by_contra hlt
    push Not at hlt
    rw [baseR_congr hU' (NNReal.coe_nonneg s) hagree_s] at hlt
    obtain ⟨x₀, hx₀, hal⟩ := exists_extendFrom_eq_alive_of_gt hU' hU'0 (NNReal.coe_nonneg s) hB hlt
    rw [hzs_eq, hx₀] at hzs
    exact hnot x₀ _ (WangWu.isForwardSol_of_alive hU' hal) hzs

end GB6

end Supp8

end InteractingSLE
