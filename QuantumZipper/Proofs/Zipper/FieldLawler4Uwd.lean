import QuantumZipper.Proofs.Zipper.FieldLawler4WdReal
import QuantumZipper.Proofs.Zipper.FieldLawler4Wd
import QuantumZipper.Proofs.Zipper.FieldLawler4E
import QuantumZipper.Proofs.Zipper.FieldLawler4ArcEnd
import QuantumZipper.Proofs.Zipper.FieldLawler3WdMob

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-UWD: the uniformization input of `fl3Wd_excR_symm` for `Wd = fl4Wd …`

Task FL4-UWD (Track A round 4). For the concrete domain `Wd` beyond the arc `ηD = C_ε(α, β)`
(FieldLawler4WdBasic.lean), `fl4_uwd` produces a boundary point `p` of `Wd` off `closure ηD` and
off `C_R`, and a uniformization `FL3Unif (T_p '' Wd) F` of the Möbius image `T_p z = (z - p)⁻¹`,
via `fl3Wd_FL3Unif_of_car` (Carathéodory's theorem, Pommerenke 1992, Thm 2.6, p. 24) with the
frame `E = fl4eE (trace W) t R ε α β = K ∪ closure ηD ∪ (C_R ∩ ℍ̄) ∪ [-R, R]`.

Used by: Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), proof of
Prop. 3.4, p. 9 (symmetry of the excursion measure between two boundary arcs of the domain).
The point-set facts `∂Wd ⊆ E ⊆ Wdᶜ` are own elementary arguments (FL leave them implicit).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- `fl4WdDom` with the closed trace `trace W '' [0, t]` in place of `fwdHull W t`. -/
lemma fl4uwd_dom_eq (hc : SideCtx W t F) (R ε α β : ℝ) :
    fl4WdDom W t R ε α β =
      (H ∩ ball 0 R) \ (trace W '' Icc 0 t ∪ closure (flCircArc ε α β)) := by
  ext z
  constructor
  · rintro ⟨⟨hH, hb⟩, hn⟩
    refine ⟨⟨hH, hb⟩, ?_⟩
    rintro (⟨s, hs, rfl⟩ | h)
    · rcases hs.1.lt_or_eq with h | h
      · exact hn (Or.inl (by rw [hc.hull]; exact ⟨s, ⟨h, hs.2⟩, rfl⟩))
      · have h2 : (0 : ℝ) < (trace W s).im := hH
        rw [← h, hc.tr0] at h2
        simp at h2
    · exact hn (Or.inr h)
  · rintro ⟨h1, hn⟩
    refine ⟨h1, ?_⟩
    rintro (h | h)
    · rw [hc.hull] at h
      obtain ⟨s, hs, e⟩ := h
      exact hn (Or.inl ⟨s, Ioc_subset_Icc_self hs, e⟩)
    · exact hn (Or.inr h)

/-- The frame `E` contains `∂Wd`. -/
lemma fl4uwd_frontier_sub (hc : SideCtx W t F) {R ε α β : ℝ} {p₀ : ℂ} :
    frontier (fl4Wd W t R ε α β p₀) ⊆ fl4eE (trace W) t R ε α β := by
  intro x hx
  have hnot := fl4_frontier_cc_not_mem (fl4WdDom_isOpen hc R ε α β) p₀ hx
  have hcl : closure (fl4Wd W t R ε α β p₀) ⊆ {z : ℂ | 0 ≤ z.im} ∩ closedBall 0 R :=
    closure_minimal (fun z hz => ⟨show (0 : ℝ) ≤ z.im from le_of_lt (fl4wd_subset_D hz).1,
      ball_subset_closedBall (fl4wd_subset_ball hz)⟩)
      ((isClosed_le continuous_const Complex.continuous_im).inter isClosed_closedBall)
  obtain ⟨him, hball⟩ := hcl hx.1
  rw [mem_closedBall_zero_iff] at hball
  rcases (show (0 : ℝ) ≤ x.im from him).lt_or_eq with h | h
  · by_cases hxR : ‖x‖ = R
    · exact Or.inl (Or.inr ⟨mem_sphere_zero_iff_norm.2 hxR, him⟩)
    have hxb : x ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 (lt_of_le_of_ne hball hxR)
    by_contra hK
    refine hnot ⟨⟨h, hxb⟩, ?_⟩
    rintro (h' | h')
    · rw [hc.hull] at h'
      obtain ⟨s, hs, e⟩ := h'
      exact hK (Or.inl (Or.inl (Or.inl ⟨s, Ioc_subset_Icc_self hs, e⟩)))
    · exact hK (Or.inl (Or.inl (Or.inr h')))
  · have hre := abs_le.1 ((Complex.abs_re_le_norm x).trans hball)
    exact Or.inr ⟨x.re, ⟨hre.1, hre.2⟩, Complex.ext (by simp) (by simp [h])⟩

/-- The frame `E` misses `Wd`. -/
lemma fl4uwd_E_sub_compl (hc : SideCtx W t F) {R ε α β : ℝ} {p₀ : ℂ} :
    fl4eE (trace W) t R ε α β ⊆ (fl4Wd W t R ε α β p₀)ᶜ := by
  intro z hzE hzW
  have hU : z ∈ (H ∩ ball 0 R) \ (trace W '' Icc 0 t ∪ closure (flCircArc ε α β)) := by
    rw [← fl4uwd_dom_eq hc]; exact fl4wd_subset_dom hzW
  obtain ⟨⟨hzH, hzb⟩, hzn⟩ := hU
  rcases hzE with ((h | h) | h) | ⟨x, -, rfl⟩
  · exact hzn (Or.inl h)
  · exact hzn (Or.inr h)
  · exact (ne_of_lt (mem_ball_zero_iff.1 hzb)) (mem_sphere_zero_iff_norm.1 h.1)
  · have h2 : (0 : ℝ) < ((x : ℂ)).im := hzH
    simp at h2

/-- An end point of `ηD` off `D = ℍ \ K_t` lies in `K ∪ ℝ` (`K = trace W '' [0, t]`). -/
lemma fl4uwd_end (hc : SideCtx W t F) {ε θ : ℝ} (hε : 0 < ε) (hθ : θ ∈ Icc 0 π)
    (hnot : flCirc ε θ ∉ H \ fwdHull W t) :
    (ε : ℂ) * exp (θ * I) ∈ trace W '' Icc 0 t ∪ range ((↑) : ℝ → ℂ) := by
  rcases fl4_end_mem hc hε hθ hnot with ⟨s, hs, e⟩ | h
  · exact Or.inl ⟨s, Ioc_subset_Icc_self hs, e⟩
  · have h' : (flCirc ε θ).im = 0 := h
    refine Or.inr ⟨(flCirc ε θ).re, ?_⟩
    show ((flCirc ε θ).re : ℂ) = flCirc ε θ
    exact Complex.ext (by simp) (by rw [ofReal_im]; exact h'.symm)

end FieldLawler
end QuantumZipper
