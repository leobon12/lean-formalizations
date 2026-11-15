import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Dimension.Future

/-!
# The first-visit cover of Aux. lemma 15 for a frozen generating trace

Packet PROVE-T11-DU2. Specification, proof of Aux. lemma 15 (`source/spec/p049-096.md`, L870–L872, p. 89):
"Fix `z ∈ γ([0, T_*)) ∩ ℍ` and let `t_z` be its first visit time … `t_z > 0` because the seed is real … one of
the preceding localizations lasts beyond `t_z`. The point `z` is not on the old trace at `a` … It follows that
`z ∈ D_a` and `g_a(z) ∈ ℍ`. Thus the countably many localized mapped futures cover every interior physical
trace point after pulling back by `g_a⁻¹` … The dimension of a countable union is the supremum."

This is the deterministic core, for the frozen `IsGeneratingTrace` (finite horizon, driver continuous only
before the horizon). It replaces PROVE-T11-DU's `dimH_trace_inter_H_le_of_cover`, whose hypotheses (uniform
radial convergence of `F_t(iy)` on compact time intervals and a globally continuous driver) are not available
for a frozen trace; the generation property of the frozen trace (`IsLoewnerTraceLT.frontier_…`) is used in
their place.

## Main results

* `IsLoewnerTraceLT.mem_image_or_mem_prefix`: a trace point after `s` is the image under `F_s` of the
  future trace, or an old point (finite-horizon form of `trace_add_mem_image_or_mem_prefix`);
* `dimH_image_inter_H_le_of_cover`: the first-visit cover and the dimension bound.
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Dimension

open QuantumZipper QuantumZipper.RS

/-- **A trace point after time `s` is the image of the future trace or an old point** (finite horizon). -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.mem_image_or_mem_prefix {W : ℝ → ℝ} {T : ℝ}
    {η : ℝ → ℂ} (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {s u : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hsuT : s + u < T)
    (hlimS : Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W s) u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace (shiftDrive W s) u)))
    (hq : η (s + u) ∈ H) :
    (trace (shiftDrive W s) u ∈ H ∧ η (s + u) = fwdMapInv W s (trace (shiftDrive W s) u)) ∨
      η (s + u) ∈ η '' Icc 0 s := by
  have hsu : 0 ≤ s + u := add_nonneg hs hu
  have hlim := hη.tendsto_fwdMapInv_mul_I hW hW0 hsu hsuT
  set p := trace (shiftDrive W s) u with hp
  set q := η (s + u) with hqdef
  by_cases hpH : p ∈ H
  · refine Or.inl ⟨hpH, ?_⟩
    rw [hqdef, ← hη.trace_eq hW hW0 hsu hsuT]
    exact (trace_add_of_tendsto_shift hW hW0 hs hu hpH hlimS).2.2
  right
  have hmem : ∀ y : ℝ, 0 < y → fwdMapInv W (s + u) (y * Complex.I) ∈ H \ fwdHull W s := by
    intro y hy
    have h1 : fwdMapInv W (s + u) (y * Complex.I) ∈ H \ fwdHull W (s + u) := by
      rw [← image_fwdMapInv_H hW hW0 hsu]
      exact mem_image_of_mem _ (mul_I_mem_H hy)
    exact ⟨h1.1, fun h => h1.2 (fwdHull_mono.1 (le_add_of_nonneg_right hu) h)⟩
  have hcl : q ∈ closure (H \ fwdHull W s) :=
    mem_closure_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun y hy => hmem y hy)
  have hnot : q ∉ H \ fwdHull W s := by
    intro hqU
    have hopen : IsOpen (H \ fwdHull W s) := FwdHolo.isOpen_compl_fwdHull hW hs
    have hcontg : ContinuousAt (fwdMap W s) q :=
      ((FwdHolo.differentiableOn_fwdMap hW hs).differentiableAt
        (hopen.mem_nhds hqU)).continuousAt
    have h1 : Tendsto (fun y : ℝ => fwdMap W s (fwdMapInv W (s + u) (y * Complex.I))) (𝓝[>] 0)
        (𝓝 (fwdMap W s q)) := hcontg.tendsto.comp hlim
    have h2 : Tendsto (fun y : ℝ => fwdMap W s (fwdMapInv W (s + u) (y * Complex.I))) (𝓝[>] 0)
        (𝓝 p) := by
      refine hlimS.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
      exact fwdMapInv_shift_eq hW hW0 hs hu (mul_I_mem_H hy)
    have hpq : p = fwdMap W s q := tendsto_nhds_unique h2 h1
    exact hpH (hpq ▸ FwdHolo.mapsTo_fwdMap hW hs hqU)
  have hfr : q ∈ frontier (H \ fwdHull W s) ∩ H := by
    refine ⟨?_, hq⟩
    rw [(FwdHolo.isOpen_compl_fwdHull hW hs).frontier_eq]
    exact ⟨hcl, hnot⟩
  exact hη.frontier_compl_fwdHull_inter_H_subset hs
    (lt_of_le_of_lt (le_add_of_nonneg_right hu) hsuT) hfr

/-- `(↑a + r)⁺ = a + r⁺` for `r ≥ 0`. -/
theorem toNNReal_coe_add {a : ℝ≥0} {r : ℝ} (hr : 0 ≤ r) :
    ((a : ℝ) + r).toNNReal = a + r.toNNReal := by
  rw [Real.toNNReal_add (NNReal.coe_nonneg a) hr, Real.toNNReal_coe]

/-- **The first-visit cover** (proof of Aux. lemma 15, pathwise). Let `η` be a frozen generating trace of
`w` before `ζ` (`w` continuous before `ζ`, `w 0 = 0`). Let `(a_i, X_i)` be countably many localizations:
`X_i` are continuous paths whose traces (driven by `√κ X_i`) have radial limits and interior dimension at
most `d`. Suppose every first-visit time `t₁` of an interior point is covered: some `a_i < t₁` has
`w(a_i + t) − w(a_i) = √κ X_i(t)` for `a_i + t ≤ t₁`. Then `dim_H(η([0, ζ)) ∩ ℍ) ≤ d`. -/
theorem dimH_image_inter_H_le_of_cover {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ζ η) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {κ : ℝ} {d : ℝ≥0∞} {ι : Type*} [Countable ι] (a : ι → ℝ≥0) (X : ι → CPath)
    (hXlim : ∀ i, ∀ u : ℝ, 0 ≤ u → Tendsto
      (fun y : ℝ => fwdMapInv (drive κ canonBM (X i)) u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace (drive κ canonBM (X i)) u)))
    (hXdim : ∀ i, dimH (trace (drive κ canonBM (X i)) '' Ici 0 ∩ H) ≤ d)
    (hcover : ∀ t₁ : ℝ≥0, 0 < t₁ → (t₁ : ℝ≥0∞) < ζ → η t₁ ∈ H → ∃ i, a i < t₁ ∧
      ∀ t : ℝ≥0, a i + t ≤ t₁ → w (a i + t) - w (a i) = Real.sqrt κ * (X i).1 t) :
    dimH (η '' {t | (t : ℝ≥0∞) < ζ} ∩ H) ≤ d := by
  classical
  set S : ι → Set ℂ := fun i => if ((a i : ℝ≥0) : ℝ≥0∞) < ζ then
    fwdMapInv (fun s : ℝ => w s.toNNReal) (a i) '' (trace (drive κ canonBM (X i)) '' Ici 0 ∩ H)
    else ∅ with hS
  have hdim : ∀ i, dimH (S i) ≤ d := by
    intro i
    by_cases hai : ((a i : ℝ≥0) : ℝ≥0∞) < ζ
    · simp only [hS, hai, ↓reduceIte]
      obtain ⟨t₂, hat₂, ht₂ζ⟩ := exists_real_btwn_of_lt hai
      have hW' := continuous_frozenDrive_of_lt hw ht₂ζ
      have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg _).trans hat₂.le
      have hW'0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
      rw [fwdMapInv_eq_of_eqOn (W := fun s : ℝ => w s.toNNReal) (W' := frozenDrive w t₂)
        (NNReal.coe_nonneg _) hat₂ (fun r hr => (frozenDrive_eq hr).symm)]
      exact (dimH_image_le_of_differentiableOn (U := H) QuantumZipper.isOpen_H
        (differentiableOn_fwdMapInv hW' hW'0 (NNReal.coe_nonneg _)) inter_subset_right).trans
        (hXdim i)
    · simp only [hS, hai, ↓reduceIte, dimH_empty, zero_le]
  have hsub : η '' {t | (t : ℝ≥0∞) < ζ} ∩ H ⊆ ⋃ i, S i := by
    rintro z ⟨⟨t₀, ht₀ζ, rfl⟩, hzH⟩
    -- the first visit time `t₁` of `z = η t₀`
    have hηc : ContinuousOn η (Icc 0 t₀) :=
      hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans (le_of_lt ht₀ζ)
    set K : Set ℝ≥0 := Icc 0 t₀ ∩ η ⁻¹' {η t₀} with hK
    have hKc : IsCompact K :=
      isCompact_Icc.of_isClosed_subset (hηc.preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton) inter_subset_left
    obtain ⟨t₁, ⟨ht₁I, ht₁η⟩, ht₁min⟩ := hKc.exists_isLeast ⟨t₀, ⟨⟨zero_le, le_rfl⟩, rfl⟩⟩
    have ht₁η' : η t₁ = η t₀ := ht₁η
    have ht₁ζ : (t₁ : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₁I.2) ht₀ζ
    have hzH1 : η t₁ ∈ H := ht₁η' ▸ hzH
    have ht₁pos : 0 < t₁ := by
      refine pos_iff_ne_zero.2 fun h0 => ?_
      rw [h0, hη.1] at hzH1
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH1)
    obtain ⟨i, hai, hid⟩ := hcover t₁ ht₁pos ht₁ζ hzH1
    have haiζ : ((a i : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hai.le) ht₁ζ
    refine mem_iUnion.2 ⟨i, ?_⟩
    simp only [hS, haiζ, ↓reduceIte]
    -- the frozen driver and the finite-horizon trace
    obtain ⟨t₂, ht₁t₂, ht₂ζ⟩ := exists_real_btwn_of_lt ht₁ζ
    have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg _).trans ht₁t₂.le
    set W' := frozenDrive w t₂ with hW'def
    have hW' : Continuous W' := continuous_frozenDrive_of_lt hw ht₂ζ
    have hW'0 : W' 0 = 0 := by rw [hW'def, frozenDrive_zero ht₂, hw0]
    have hL := hη.isLoewnerTraceLT ht₂ζ
    set A : ℝ := (a i : ℝ) with hA
    set u : ℝ := (t₁ : ℝ) - A with hu
    have hA0 : 0 ≤ A := NNReal.coe_nonneg _
    have hu0 : 0 ≤ u := by rw [hu, hA]; exact sub_nonneg.2 (by exact_mod_cast hai.le)
    have hAu : A + u = t₁ := by rw [hu]; ring
    have hAut₂ : A + u < t₂ := by rw [hAu]; exact ht₁t₂
    -- the shifted frozen driver is the localized Brownian driver on `[0, u]`
    have hEq : EqOn (shiftDrive W' A) (drive κ canonBM (X i)) (Icc 0 u) := by
      intro r hr
      have hr0 : 0 ≤ r := hr.1
      have h1 : A + r ∈ Icc (0 : ℝ) t₂ := ⟨add_nonneg hA0 hr0, by linarith [hr.2]⟩
      have h2 : A ∈ Icc (0 : ℝ) t₂ := ⟨hA0, by linarith [hr.2]⟩
      have hle : a i + r.toNNReal ≤ t₁ := by
        rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hr0]
        linarith [hr.2]
      simp only [shiftDrive, drive, canonBM]
      rw [hW'def, frozenDrive_eq h1, frozenDrive_eq h2, hA, toNNReal_coe_add hr0,
        Real.toNNReal_coe]
      exact hid _ hle
    have hD : Continuous (drive κ canonBM (X i)) := continuous_drive_path (X i).2
    have hS' : Continuous (shiftDrive W' A) := continuous_shiftDrive hW' A
    have hD0 : drive κ canonBM (X i) 0 = 0 := by
      rw [← hEq ⟨le_rfl, hu0⟩, shiftDrive_zero]
    have htr : trace (shiftDrive W' A) u = trace (drive κ canonBM (X i)) u :=
      trace_congr_drive hS' (shiftDrive_zero _ _) hD hD0 hu0 hEq
    have hInv : EqOn (fwdMapInv (shiftDrive W' A) u) (fwdMapInv (drive κ canonBM (X i)) u) H :=
      RegCont.fwdMapInv_congr hS' (shiftDrive_zero _ _) hD hD0 hEq ⟨hu0, le_rfl⟩
    have hlimS : Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W' A) u (y * Complex.I)) (𝓝[>] 0)
        (𝓝 (trace (shiftDrive W' A) u)) := by
      rw [htr]
      refine (hXlim i u hu0).congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
      exact (hInv (mul_I_mem_H hy)).symm
    have hq : (fun s : ℝ => η s.toNNReal) (A + u) ∈ H := by
      simp only [hAu, Real.toNNReal_coe]
      exact hzH1
    rcases hL.mem_image_or_mem_prefix hW' hW'0 hA0 hu0 hAut₂ hlimS hq with ⟨hpH, heq⟩ | hold
    · refine ⟨trace (drive κ canonBM (X i)) u, ⟨⟨u, mem_Ici.2 hu0, rfl⟩, htr ▸ hpH⟩, ?_⟩
      rw [fwdMapInv_eq_of_eqOn (W := fun s : ℝ => w s.toNNReal) (W' := W')
        (NNReal.coe_nonneg _) (lt_of_le_of_lt (by exact_mod_cast hai.le) ht₁t₂)
        (fun r hr => (frozenDrive_eq hr).symm), ← htr, ← ht₁η']
      simp only [hAu, Real.toNNReal_coe] at heq
      exact heq.symm
    · exfalso
      obtain ⟨r, hr, hrη⟩ := hold
      simp only [hAu, Real.toNNReal_coe] at hrη
      have hr' : r.toNNReal ≤ a i := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2
      have hmem : r.toNNReal ∈ K :=
        ⟨⟨zero_le, hr'.trans (hai.le.trans ht₁I.2)⟩, by
          show η r.toNNReal = η t₀
          rw [hrη, ht₁η']⟩
      exact absurd (ht₁min hmem) (not_le.2 (lt_of_le_of_lt hr' hai))
  calc dimH (η '' {t | (t : ℝ≥0∞) < ζ} ∩ H) ≤ dimH (⋃ i, S i) := dimH_mono hsub
    _ = ⨆ i, dimH (S i) := dimH_iUnion S
    _ ≤ d := iSup_le hdim

end InteractingSLE.Dimension
