import QuantumZipper.Proofs.Zipper.T13Hard4Path
import QuantumZipper.Proofs.Probability.GermZeroOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD4: tools for the translation smoothness of first passage laws

* continuous-path coding `T13Trans.pathC` (subtype of continuous paths), its law is that of any
  Brownian motion with continuous paths (`map_pathC_eq`, from
  `GermZeroOne.map_path_eq_of_isPreBrownianReal`), and the first passage time as a measurable
  function on it (`measurable_PhiC`, `measurable_PhiC2` jointly in the level);
* the mixture bound `tv_map_prod_le_gen` (general form of `D3Plus.tv_map_prod_le_path`);
* `Tc_split'`: first passage splitting at a deterministic time before which `Xc > 0`.
Own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace T13Trans

/-- Continuous paths. -/
abbrev CPathT : Type := {w : ℝ≥0 → ℝ // Continuous w}

/-- The coordinate family on continuous paths. -/
def coordC : ℝ≥0 → CPathT → ℝ := fun t w => w.1 t

theorem measurable_coordC (t : ℝ≥0) : Measurable (coordC t) :=
  (measurable_pi_apply t).comp measurable_subtype_coe

/-- The first passage time as a function on continuous paths. -/
def PhiC (α Q c : ℝ) : CPathT → ℝ := fun w => ZoomRadial.Tc α Q c coordC w

theorem measurable_PhiC (α Q c : ℝ) : Measurable (PhiC α Q c) :=
  D3Plus.measurable_Tc_of_cont (b := coordC) (fun w => w.2) (fun t => measurable_coordC _) α Q c

/-- The first passage time, jointly in the level shift and the path. -/
def PhiC2 (α Q L : ℝ) : ℝ × CPathT → ℝ := fun p => ZoomRadial.Tc α Q (L + p.1) coordC p.2

theorem measurable_PhiC2 (α Q L : ℝ) : Measurable (PhiC2 α Q L) := by
  set bh : ℝ≥0 → ℝ × CPathT → ℝ := fun t p => p.2.1 t + p.1 / Real.sqrt 2 with hbh
  have hc : ∀ p : ℝ × CPathT, Continuous fun t => bh t p := fun p =>
    p.2.2.add continuous_const
  have hm : ∀ t : ℝ, Measurable fun p : ℝ × CPathT => bh t.toNNReal p := fun t =>
    ((measurable_coordC _).comp measurable_snd).add (measurable_fst.div_const _)
  have h := D3Plus.measurable_Tc_of_cont hc hm α Q L
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have key : PhiC2 α Q L = fun p => ZoomRadial.Tc α Q L bh p := by
    funext p
    simp only [PhiC2, ZoomRadial.Tc, ZoomRadial.Xc, hbh, coordC]
    congr 1
    ext t
    simp only [mem_setOf_eq]
    have e : Real.sqrt 2 * (p.2.1 t.toNNReal + p.1 / Real.sqrt 2) =
        Real.sqrt 2 * p.2.1 t.toNNReal + p.1 := by field_simp
    rw [e]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  rw [key]; exact h

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The continuous path of a family with continuous sections. -/
def pathC (W : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous fun t => W t ω) : Ω → CPathT :=
  fun ω => ⟨fun t => W t ω, hc ω⟩

theorem measurable_pathC {W : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t => W t ω)
    (hm : ∀ t, Measurable (W t)) : Measurable (pathC W hc) :=
  (measurable_pi_iff.2 hm).subtype_mk

/-- Two Brownian motions with continuous paths have the same continuous-path law. -/
theorem map_pathC_eq {P : Measure Ω} {W W' : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W P)
    (hW' : IsPreBrownianReal W' P) (hm : ∀ t, Measurable (W t)) (hm' : ∀ t, Measurable (W' t))
    (hc : ∀ ω, Continuous fun t => W t ω) (hc' : ∀ ω, Continuous fun t => W' t ω) :
    P.map (pathC W hc) = P.map (pathC W' hc') := by
  have hpath := GermZeroOne.map_path_eq_of_isPreBrownianReal hW hW' hm hm'
  ext s hs
  obtain ⟨B, hB, rfl⟩ := hs
  rw [Measure.map_apply (measurable_pathC hc hm) (measurable_subtype_coe hB),
    Measure.map_apply (measurable_pathC hc' hm') (measurable_subtype_coe hB)]
  have e1 : pathC W hc ⁻¹' (Subtype.val ⁻¹' B) = (fun ω t => W t ω) ⁻¹' B := rfl
  have e2 : pathC W' hc' ⁻¹' (Subtype.val ⁻¹' B) = (fun ω t => W' t ω) ⁻¹' B := rfl
  rw [e1, e2, ← Measure.map_apply (measurable_pi_iff.2 hm) hB,
    ← Measure.map_apply (measurable_pi_iff.2 hm') hB, hpath]

/-- TV of two images of a product measure is at most the average TV of the sections. -/
theorem tv_map_prod_le_gen {α E β : Type*} [MeasurableSpace α] [MeasurableSpace E]
    [MeasurableSpace β] (μ0 : Measure α) [IsProbabilityMeasure μ0] (μs : Measure E)
    [IsProbabilityMeasure μs] {f1 f2 : α × E → β} (h1 : Measurable f1) (h2 : Measurable f2) :
    TV.tvDist ((μ0.prod μs).map f1) ((μ0.prod μs).map f2) ≤
      ∫⁻ a, TV.tvDist (μs.map fun x => f1 (a, x)) (μs.map fun x => f2 (a, x)) ∂μ0 := by
  have key : ∀ f : α × E → β, Measurable f → (μ0.prod μs).map f =
      μ0.bind (Kernel.map (Kernel.id ×ₖ Kernel.const α μs) f) := by
    intro f hf
    rw [← Measure.compProd_const, Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hf]
  have kap : ∀ f : α × E → β, Measurable f → ∀ a,
      Kernel.map (Kernel.id ×ₖ Kernel.const α μs) f a = μs.map fun x => f (a, x) := by
    intro f hf a
    rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
      Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
    rfl
  haveI : IsMarkovKernel (Kernel.map (Kernel.id ×ₖ Kernel.const α μs) f1) :=
    Kernel.IsMarkovKernel.map _ h1
  haveI : IsMarkovKernel (Kernel.map (Kernel.id ×ₖ Kernel.const α μs) f2) :=
    Kernel.IsMarkovKernel.map _ h2
  rw [key f1 h1, key f2 h2]
  refine (TV.tvDist_bind_le _ _).trans (le_of_eq ?_)
  simp only [kap f1 h1, kap f2 h2]

/-- **First passage splitting at a time `τ` before which `Xc_L > 0`.** -/
theorem Tc_split' {α Q L : ℝ} {W W' : ℝ≥0 → Ω → ℝ} {ω : Ω} {τ : ℝ≥0}
    (hW' : ∀ s, W' s ω = W (τ + s) ω - W τ ω) (hW'c : Continuous fun s => W' s ω)
    (hpos : ∀ t : ℝ, 0 ≤ t → t < τ → 0 < ZoomRadial.Xc α Q L W ω t)
    (hhit : ∃ v, 0 ≤ v ∧ ZoomRadial.Xc α Q (L + (Real.sqrt 2 * W τ ω + (α - Q) * (τ : ℝ)))
      W' ω v ≤ 0) :
    ZoomRadial.Tc α Q L W ω =
      τ + ZoomRadial.Tc α Q (L + (Real.sqrt 2 * W τ ω + (α - Q) * (τ : ℝ))) W' ω := by
  set M := L + (Real.sqrt 2 * W τ ω + (α - Q) * (τ : ℝ)) with hM
  set SL : Set ℝ := {t | 0 ≤ t ∧ ZoomRadial.Xc α Q L W ω t ≤ 0} with hSL
  set SM : Set ℝ := {v | 0 ≤ v ∧ ZoomRadial.Xc α Q M W' ω v ≤ 0} with hSM
  have hcM : Continuous fun v : ℝ => ZoomRadial.Xc α Q M W' ω v := by
    have h1 : Continuous fun v : ℝ => W' v.toNNReal ω := hW'c.comp continuous_real_toNNReal
    simp only [ZoomRadial.Xc]
    fun_prop
  have hSMc : IsClosed SM := isClosed_Ici.inter (isClosed_le hcM continuous_const)
  have hmem := hSMc.csInf_mem hhit ⟨0, fun s hs => hs.1⟩
  have hin : (τ : ℝ) + sInf SM ∈ SL :=
    ⟨add_nonneg τ.2 hmem.1, by rw [T13Path.Xc_split hW' hM hmem.1]; exact hmem.2⟩
  refine le_antisymm (csInf_le ⟨0, fun s hs => hs.1⟩ hin) ?_
  refine le_csInf ⟨_, hin⟩ fun t ht => ?_
  have htτ : (τ : ℝ) ≤ t := by
    by_contra h
    push Not at h
    exact absurd ht.2 (not_le.2 (hpos t ht.1 h))
  have hv : 0 ≤ t - τ := by linarith
  have hmemv : t - τ ∈ SM := by
    refine ⟨hv, ?_⟩
    have h := T13Path.Xc_split (α := α) (Q := Q) hW' hM hv
    rw [add_sub_cancel] at h
    rw [← h]; exact ht.2
  have := csInf_le ⟨0, fun s hs => hs.1⟩ hmemv
  change (τ : ℝ) + sInf SM ≤ t
  linarith

end T13Trans
end QuantumZipper
