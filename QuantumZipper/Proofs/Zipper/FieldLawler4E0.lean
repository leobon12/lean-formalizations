import QuantumZipper.Proofs.Zipper.FieldLawler4Uwd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-E0: the frame `E` and FL4-UWD for arcs ending on the real axis

Task FL4-E0 (Track A round 4). `fl4eE_diff_preconnected` (FieldLawler4E.lean) and `fl4_uwd`
(FieldLawler4Uwd.lean) assumed strict angle bounds `0 < α`, `β < π`. Here they are relaxed to
`0 ≤ α < β ≤ π`, so the arc `C_ε(α, β)` may end on the real axis at `ε` (`α = 0`) or `-ε`
(`β = π`). A real end point `ε e^{iθ} = x` has `|x| = ε < R`, so it lies on the segment
`[-R, R] ⊆ E`; the closed arc is then still attached to the connected rest of `E` at both ends,
and `fl4e_arc_diff` applies unchanged. The Wd lemmas used by `fl4_uwd`
(`fl4wd_bdry_point`, `fl4e_hcomp`, `fl4eE_ulc`, ...) need no angle bounds.
Own elementary point-set argument (as in FieldLawler4E.lean); no published source states it.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar
open QuantumZipper.CA

section E0

variable {γ : ℝ → ℂ} {t R ε α β : ℝ}

/-- `E \ {q}` is preconnected, for `0 ≤ α < β ≤ π` (end points of the arc in `K ∪ ℝ`).
Own elementary proof. -/
theorem fl4eE_diff_preconnected' (ht : 0 < t) (hγc : ContinuousOn γ (Icc 0 t))
    (hγi : InjOn γ (Icc 0 t)) (hγ0 : γ 0 = 0) (hγH : ∀ s ∈ Ioc 0 t, γ s ∈ H)
    (hγt : ‖γ t‖ = R) (hε : 0 < ε) (hεR : ε < R) (hα : 0 ≤ α) (hαβ : α < β) (hβ : β ≤ π)
    (hend : (ε : ℂ) * exp (α * I) ∈ γ '' Icc 0 t ∪ range ((↑) : ℝ → ℂ) ∧
      (ε : ℂ) * exp (β * I) ∈ γ '' Icc 0 t ∪ range ((↑) : ℝ → ℂ)) (q : ℂ) :
    IsPreconnected (fl4eE γ t R ε α β \ {q}) := by
  have hR : 0 < R := hε.trans hεR
  set K := γ '' Icc 0 t with hKd
  set A := flClArc ε α β with hAd
  set S := flClArc R 0 π with hSd
  set seg := (fun x : ℝ => (x : ℂ)) '' Icc (-R) R with hsegd
  have hJ := fl4e_J_diff hR q
  have h0seg : γ 0 ∈ seg := ⟨0, ⟨by linarith, hR.le⟩, by simp [hγ0]⟩
  have htS : γ t ∈ S := by
    show γ t ∈ flClArc R 0 π
    rw [← fl4e_semi_eq hR]
    exact ⟨by rw [mem_sphere, dist_zero_right, hγt],
      le_of_lt (show (0 : ℝ) < (γ t).im from hγH t ⟨ht, le_rfl⟩)⟩
  have hK := fl4e_arc_diff (f := γ) ht.le hγc hγi hJ q (fun h => ⟨Or.inr h0seg, h⟩)
    (fun h => ⟨Or.inl htS, h⟩)
  have hendM : ∀ θ : ℝ, (ε : ℂ) * exp (θ * I) ∈ K ∪ range ((↑) : ℝ → ℂ) →
      (ε : ℂ) * exp (θ * I) ≠ q →
        (ε : ℂ) * exp (θ * I) ∈ (S ∪ seg) \ {q} ∪ (K \ {q}) := by
    rintro θ (h | ⟨x, hx⟩) hq
    · exact Or.inr ⟨h, hq⟩
    · have hx1 : |x| = ε := by
        have := congrArg norm hx
        simpa [abs_of_pos hε] using this
      exact Or.inl ⟨Or.inr ⟨x, abs_le.1 (hx1.le.trans hεR.le), hx⟩, hq⟩
  have hsub : Icc α β ⊆ Icc 0 π := Icc_subset_Icc hα hβ
  have hA := fl4e_arc_diff (f := fun θ : ℝ => (ε : ℂ) * exp (θ * I)) hαβ.le
    (flClArc_cont ε).continuousOn ((fl4e_injOn hε).mono hsub) hK q
    (hendM α hend.1) (hendM β hend.2)
  have e : fl4eE γ t R ε α β \ {q} = (S ∪ seg) \ {q} ∪ (K \ {q}) ∪ (A \ {q}) := by
    rw [fl4eE, fl4e_closure_arc hαβ, fl4e_semi_eq hR]
    ext z
    simp only [Set.mem_union, Set.mem_sdiff, hKd, hAd, hSd, hsegd]
    tauto
  rw [e]
  exact hA

end E0

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **FL4-UWD, non-strict angles.** `fl4_uwd` under `0 ≤ α < β ≤ π` (the arc may end on the
real axis), with the same end point hypotheses `hαD`, `hβD` as returned by `fl4_arc_chart`. -/
theorem fl4_uwd' (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hα : 0 ≤ α) (hαβ : α < β) (hβ : β ≤ π) (hinj : InjOn (trace W) (Icc 0 t))
    (hH : trace W t ∈ H) (hnorm : ‖trace W t‖ = R) (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') {a b : ℝ}
    (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a < b) (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β)
    (hαD : flCirc ε α ∉ H \ fwdHull W t) (hβD : flCirc ε β ∉ H \ fwdHull W t)
    {p₀ : ℂ} (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η') :
    ∃ (p : ℂ) (F Φ : ℂ → ℂ), p ∈ frontier (fl4Wd W t R ε α β p₀) ∧
      p ∉ closure (flCircArc ε α β) ∧ p ∉ sphere 0 R ∧ ε < ‖p‖ ∧ ‖p‖ < R ∧
      FL3Unif (fl3WdT p '' fl4Wd W t R ε α β p₀) F ∧
      BijOn F (fl3WdT p '' fl4Wd W t R ε α β p₀) H ∧
      (∀ q ∈ closure (fl3WdT p '' fl4Wd W t R ε α β p₀), F q ∈ Hbar ∧ Φ (F q) = q) ∧
      (∀ z ∈ Hbar, F (Φ z) = z) ∧ ContinuousOn Φ Hbar ∧
      range (fun x : ℝ => Φ x) = frontier (fl3WdT p '' fl4Wd W t R ε α β p₀) := by
  obtain ⟨p, hpfr, hεp, hpR, -⟩ :=
    fl4wd_bdry_point hc hε hεR hlt hnorm hH hη ha hb hab hηD hp hpU
  have hγH : ∀ s ∈ Ioc 0 t, trace W s ∈ H := fun s hs =>
    (show trace W s ∈ fwdHull W t by rw [hc.hull]; exact ⟨s, hs, rfl⟩).1
  have hend : (ε : ℂ) * exp (α * I) ∈ trace W '' Icc 0 t ∪ range ((↑) : ℝ → ℂ) ∧
      (ε : ℂ) * exp (β * I) ∈ trace W '' Icc 0 t ∪ range ((↑) : ℝ → ℂ) :=
    ⟨fl4uwd_end hc hε ⟨hα, (hαβ.le.trans hβ)⟩ hαD,
      fl4uwd_end hc hε ⟨(hα.trans hαβ.le), hβ⟩ hβD⟩
  have hEsub := fl4uwd_E_sub_compl (p₀ := p₀) hc (R := R) (ε := ε) (α := α) (β := β)
  have hDU : ∀ z ∈ fl4Wd W t R ε α β p₀, connectedComponentIn
      ((H ∩ ball 0 R) \ (trace W '' Icc 0 t ∪ closure (flCircArc ε α β))) z ⊆
        fl4Wd W t R ε α β p₀ := by
    intro z hz
    rw [← fl4uwd_dom_eq hc]
    have e : connectedComponentIn (fl4WdDom W t R ε α β) p₀ =
        connectedComponentIn (fl4WdDom W t R ε α β) z := connectedComponentIn_eq hz
    show _ ⊆ connectedComponentIn _ p₀
    rw [e]
  have hcomp := fl4e_hcomp hc.tpos.le hc.trCont hc.tr0 hαβ hend.1 (fl4wd_open hc)
    (Set.disjoint_left.2 fun z hzW hzE => hEsub hzE hzW)
    (fun z hz => (fl4wd_subset_dom hz).1) hDU
  obtain ⟨F, Φ, h⟩ := fl3Wd_FL3Unif_of_car (fl4wd_open hc) (fl4wd_conn hp).isPreconnected
    (fl4wd_conn hp).nonempty hcomp fl4wd_subset_ball (fl4eE_isClosed hc.trCont)
    (fl4uwd_frontier_sub hc) hEsub (fl4eE_sub_closedBall hlt hnorm hε hεR)
    (fl4eE_ulc hc.tpos.le hc.trCont (hε.trans hεR) hαβ)
    (fl4eE_diff_preconnected' hc.tpos hc.trCont hinj hc.tr0 hγH hnorm hε hεR hα hαβ hβ hend)
    hpfr
  refine ⟨p, F, Φ, hpfr, fun h' => ?_, fun h' => ?_, hεp, hpR, h⟩
  · have := fl4_closure_arc_subset h'
    rw [mem_sphere_zero_iff_norm, abs_of_pos hε] at this
    linarith
  · rw [mem_sphere_zero_iff_norm] at h'
    linarith

end FieldLawler
end QuantumZipper
