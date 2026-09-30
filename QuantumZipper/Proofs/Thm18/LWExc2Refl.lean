import QuantumZipper.Proofs.Thm18.LWExc2Lower
import QuantumZipper.Proofs.Thm18.LWExc2Poisson

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route: the reflection principle for harmonic functions (local form)

`harmReflectStmt_holds : HarmReflectStmt`, following Ahlfors' proof (L. Ahlfors, *Complex
Analysis*, 3rd ed. 1979, Ch. 4 §6.5, Theorem 24, pp. 172–173,
`literature/Ahlfors_ComplexAnalysis_1979.pdf`, PDF pp. 187–188): extend `v` oddly across `ℝ`
(`V(z) = −v(z̄)`), take the Poisson integral `P_V` over a circle centred on `ℝ`; `P_V` is harmonic,
has the boundary values `V` (Ahlfors Thm 23, `lwExc2_poisson_tendsto`) and vanishes on the
diameter by symmetry (`lwExc2_poisson_odd`), so `v − P_V` tends to `0` at the whole boundary of
the upper half-disk and vanishes there by the maximum principle (`lwExc_harm_le_zero`).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The odd reflection of `v` across `ℝ`. -/
def lwOddExt (v : ℂ → ℝ) (z : ℂ) : ℝ := if 0 ≤ z.im then v z else - v (conj z)

lemma lwOddExt_cont {v : ℂ → ℝ} {x r : ℝ} (hc : ContinuousOn v (Hbar ∩ ball (x : ℂ) r))
    (hz : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → v z = 0) :
    ContinuousOn (lwOddExt v) (ball (x : ℂ) r) := by
  have hcl : closure {a : ℂ | ¬ 0 ≤ a.im} ⊆ {a : ℂ | a.im ≤ 0} :=
    closure_minimal (fun (z : ℂ) (hz : ¬ 0 ≤ z.im) => (not_le.1 hz).le)
      (isClosed_le continuous_im continuous_const)
  refine ContinuousOn.if ?_ ?_ ?_
  · intro a ⟨haB, hfr⟩
    have h1 : 0 ≤ a.im := closure_minimal (fun _ h => h) isClosed_Hbar
      (frontier_subset_closure hfr)
    have h2 : a.im ≤ 0 := by
      have hfr' := hfr
      rw [← frontier_compl] at hfr'
      exact hcl (frontier_subset_closure hfr')
    have ha : a.im = 0 := le_antisymm h2 h1
    rw [conj_eq_iff_im.2 ha, hz a haB ha, neg_zero]
  · exact hc.mono fun a ⟨haB, ha⟩ => ⟨closure_minimal (fun _ h => h) isClosed_Hbar ha, haB⟩
  · have hsub : ball (x : ℂ) r ∩ closure {a : ℂ | ¬ 0 ≤ a.im} ⊆
        {a : ℂ | a.im ≤ 0} ∩ ball (x : ℂ) r := fun a ⟨haB, ha⟩ => ⟨hcl ha, haB⟩
    refine ContinuousOn.mono ?_ hsub
    refine (hc.comp continuous_conj.continuousOn ?_).neg
    intro a ⟨ha, haB⟩
    exact ⟨show 0 ≤ (conj a).im by simpa using ha, CA.conj_mem_ball_ofReal haB⟩

lemma lwOddExt_conj {v : ℂ → ℝ} {x r : ℝ} (hz : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → v z = 0)
    {z : ℂ} (hzB : z ∈ ball (x : ℂ) r) : lwOddExt v (conj z) = - lwOddExt v z := by
  unfold lwOddExt
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · rw [if_pos (by simp; linarith), if_neg (by linarith)]; simp
  · rw [conj_eq_iff_im.2 hzero, if_pos hzero.ge, hz z hzB hzero]; simp
  · rw [if_neg (by simp; linarith), if_pos hpos.le, conj_conj]

/-- **Reflection principle for harmonic functions** (Ahlfors Thm 24), local form. -/
theorem harmReflectStmt_holds : HarmReflectStmt := by
  intro v x r hr hharm hcont hzero
  set ρ := r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρr : ρ < r := by linarith
  set g : ℂ → ℝ := fun ζ => lwOddExt v (ζ + x) with hgdef
  have hVc := lwOddExt_cont hcont hzero
  have hsubB : ∀ ζ ∈ sphere (0 : ℂ) ρ, ζ + x ∈ ball (x : ℂ) r := by
    intro ζ hζ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
    rw [mem_sphere, dist_zero_right] at hζ; linarith
  have hgc : ContinuousOn g (sphere (0 : ℂ) ρ) :=
    hVc.comp (continuous_id.add continuous_const).continuousOn (fun ζ hζ => hsubB ζ hζ)
  have hgodd : ∀ ζ ∈ sphere (0 : ℂ) ρ, g (conj ζ) = - g ζ := by
    intro ζ hζ
    simp only [hgdef]
    have : conj ζ + (x : ℂ) = conj (ζ + x) := by simp
    rw [this, lwOddExt_conj hzero (hsubB ζ hζ)]
  set P : ℂ → ℝ := fun z => lwPoisson g ρ (z - x) with hPdef
  have hPh : InnerProductSpace.HarmonicOnNhd P (ball (x : ℂ) ρ) :=
    lwExc2_poisson_harm hρ hgc (x : ℂ)
  have hP0 : ∀ z ∈ ball (x : ℂ) ρ, z.im = 0 → P z = 0 := fun z _ hz =>
    lwExc2_poisson_odd hρ hgodd (by simp [hz])
  set U := H ∩ ball (x : ℂ) ρ with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_im).inter isOpen_ball
  have hUsub : U ⊆ Hbar ∩ ball (x : ℂ) r := fun z hz =>
    ⟨H_subset_Hbar hz.1, ball_subset_ball hρr.le hz.2⟩
  have hvh : InnerProductSpace.HarmonicOnNhd v U := hharm.mono fun z hz =>
    ⟨hz.1, ball_subset_ball hρr.le hz.2⟩
  -- boundary behaviour of `v − P`
  have hbdry : ∀ x₀ ∈ frontier U, Tendsto (fun z => v z - P z) (𝓝[U] x₀) (𝓝 0) := by
    intro x₀ hx₀
    have hcl : x₀ ∈ closure U := frontier_subset_closure hx₀
    have hnU : x₀ ∉ U := fun h => by
      rw [hUo.frontier_eq] at hx₀; exact hx₀.2 h
    have hHb : 0 ≤ x₀.im := closure_minimal (H_subset_Hbar) isClosed_Hbar
      (closure_mono inter_subset_left hcl)
    have hBb : x₀ ∈ closedBall (x : ℂ) ρ :=
      closure_ball_subset_closedBall (closure_mono inter_subset_right hcl)
    have hx₀r : x₀ ∈ ball (x : ℂ) r := closedBall_subset_ball hρr hBb
    have hvlim : Tendsto v (𝓝[U] x₀) (𝓝 (v x₀)) :=
      ((hcont x₀ ⟨hHb, hx₀r⟩).mono hUsub).tendsto
    by_cases hin : x₀ ∈ ball (x : ℂ) ρ
    · -- `x₀` on the diameter
      have him : x₀.im = 0 := by
        by_contra hne
        exact hnU ⟨lt_of_le_of_ne hHb (Ne.symm hne), hin⟩
      have hPlim : Tendsto P (𝓝[U] x₀) (𝓝 (P x₀)) :=
        ((hPh x₀ hin).1.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      have := hvlim.sub hPlim
      rwa [hzero x₀ hx₀r him, hP0 x₀ hin him, sub_zero] at this
    · -- `x₀` on the circle
      have hsph : x₀ - x ∈ sphere (0 : ℂ) ρ := by
        rw [mem_sphere, dist_zero_right, ← dist_eq_norm]
        exact le_antisymm (mem_closedBall.1 hBb) (not_lt.1 fun h => hin h)
      have ht := lwExc2_poisson_tendsto hρ hgc hsph
      have hmap : Tendsto (fun z : ℂ => z - x) (𝓝[U] x₀) (𝓝[ball (0 : ℂ) ρ] (x₀ - x)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · exact ((continuous_id.sub continuous_const).tendsto x₀).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with z hz
          rw [mem_ball, dist_zero_right, ← dist_eq_norm]; exact hz.2
      have hPlim : Tendsto P (𝓝[U] x₀) (𝓝 (g (x₀ - x))) := ht.comp hmap
      have hgx : g (x₀ - x) = v x₀ := by
        simp only [hgdef, sub_add_cancel, lwOddExt, if_pos hHb]
      rw [hgx] at hPlim
      have := hvlim.sub hPlim
      rwa [sub_self] at this
  have hbd : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ x₀ ∈ frontier U, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ U, dist y x₀ < δ → s * (v y - P y) ≤ ε := by
    intro s hs x₀ hx₀ ε hε
    have ht := ((hbdry x₀ hx₀).const_mul s)
    rw [mul_zero, Metric.tendsto_nhdsWithin_nhds] at ht
    obtain ⟨δ, hδ, hδs⟩ := ht ε hε
    refine ⟨δ, hδ, fun y hy hdy => ?_⟩
    have := hδs hy hdy
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  have hinf : ∀ (s : ℝ), ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ y ∈ U, R ≤ ‖y‖ → s * (v y - P y) ≤ ε := by
    intro s ε hε
    refine ⟨‖(x : ℂ)‖ + ρ + 1, fun y hy hR => ?_⟩
    exfalso
    have h1 : ‖y‖ ≤ ‖y - x‖ + ‖(x : ℂ)‖ := by
      calc ‖y‖ = ‖(y - x) + (x : ℂ)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖y - x‖ < ρ := by rw [← dist_eq_norm]; exact hy.2
    linarith
  have hPU : InnerProductSpace.HarmonicOnNhd P U := hPh.mono fun z hz => hz.2
  have hle1 := lwExc_harm_le_zero (f := fun y => v y - P y) hUo (hvh.sub hPU)
    (fun x₀ hx ε hε => by
      obtain ⟨δ, hδ, h⟩ := hbd 1 (Or.inl rfl) x₀ hx ε hε
      exact ⟨δ, hδ, fun y hy hd => by have := h y hy hd; linarith⟩)
    (fun ε hε => by
      obtain ⟨R, h⟩ := hinf 1 ε hε
      exact ⟨R, fun y hy hR => by have := h y hy hR; linarith⟩)
  have hle2 := lwExc_harm_le_zero (f := fun y => P y - v y) hUo (hPU.sub hvh)
    (fun x₀ hx ε hε => by
      obtain ⟨δ, hδ, h⟩ := hbd (-1) (Or.inr rfl) x₀ hx ε hε
      exact ⟨δ, hδ, fun y hy hd => by have := h y hy hd; linarith⟩)
    (fun ε hε => by
      obtain ⟨R, h⟩ := hinf (-1) ε hε
      exact ⟨R, fun y hy hR => by have := h y hy hR; linarith⟩)
  refine ⟨ρ, hρ, hρr.le, P, hPh, fun z hz => ?_⟩
  rcases (show (0 : ℝ) ≤ z.im from hz.1).lt_or_eq with hpos | hz0
  · have h1 := hle1 z ⟨hpos, hz.2⟩
    have h2 := hle2 z ⟨hpos, hz.2⟩
    linarith
  · rw [hP0 z hz.2 hz0.symm, hzero z (ball_subset_ball hρr.le hz.2) hz0.symm]

end LWFar
end Thm18Asm
end QuantumZipper
