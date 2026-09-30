import QuantumZipper.Proofs.Zipper.FieldLawler3Cmp
import QuantumZipper.Proofs.Zipper.FieldLawler3UnifF
import QuantumZipper.Proofs.Zipper.FieldLawler4WdPolar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-WD (basic): the domain `Wd` between `ηⱼ` and `C_R`

Task FL4-WD (Track A round 4). In FL's proof of Prop. 3.4 (Field–Lawler, *Escape probability
and transience for SLE*, EJP 20 (2015), p. 9) the comparison `ℰ(ηⱼ, γ̃) ≤ ℰ(ηⱼ, C_R)` is made in
the part of `H_t ∩ B(0, R)` beyond `ηⱼ`. Here it is
`Wd = connectedComponentIn ((ℍ ∩ B(0,R)) \ (K_t ∪ closure ηD)) p₀`, `ηD = F(η') = flCircArc ε α β`,
with `p₀` just beyond the arc on the `hullComp η'` side. This file: the base point
(`fl4wd_base_exists`) and generic facts on components of open sets. Own elementary argument
(FL leave the domain implicit).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- The open set whose component is `Wd`. -/
def fl4WdDom (W : ℝ → ℝ) (t R ε α β : ℝ) : Set ℂ :=
  (H ∩ ball 0 R) \ (fwdHull W t ∪ closure (flCircArc ε α β))

/-- **The domain `Wd`** between the arc `ηD = flCircArc ε α β` and `C_R`. -/
def fl4Wd (W : ℝ → ℝ) (t R ε α β : ℝ) (p₀ : ℂ) : Set ℂ :=
  connectedComponentIn (fl4WdDom W t R ε α β) p₀

lemma fl4WdDom_isOpen (hc : SideCtx W t F) (R ε α β : ℝ) : IsOpen (fl4WdDom W t R ε α β) := by
  have : fl4WdDom W t R ε α β = ((H \ fwdHull W t) ∩ ball 0 R) ∩ (closure (flCircArc ε α β))ᶜ := by
    ext z; simp only [fl4WdDom, Set.mem_sdiff, mem_inter_iff, mem_union, mem_compl_iff]; tauto
  rw [this]
  exact (hc.isOpen_dom.inter isOpen_ball).inter isClosed_closure.isOpen_compl

/-- Frontier points of a component of an open set lie outside the open set. -/
lemma fl4_frontier_cc_not_mem {O : Set ℂ} (hO : IsOpen O) (p : ℂ) {x : ℂ}
    (hx : x ∈ frontier (connectedComponentIn O p)) : x ∉ O := by
  intro hxO
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO x hxO
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hx.1 _ (ball_mem_nhds x hr)
  have hsub : ball x r ⊆ connectedComponentIn O y :=
    (convex_ball x r).isPreconnected.subset_connectedComponentIn hy1 hrO
  rw [← connectedComponentIn_eq hy2] at hsub
  apply hx.2
  rw [(hO.connectedComponentIn).interior_eq]
  exact hsub (mem_ball_self hr)

lemma fl4_fwdMap_inv (hc : SideCtx W t F) {q : ℂ} (hq : q ∈ H) :
    fwdMap W t (fwdMapInv W t q) = q := by
  rw [← hc.Feq hq]; exact hc.fwdMap_F hq

lemma fl4_inv_mem (hc : SideCtx W t F) {q : ℂ} (hq : q ∈ H) :
    fwdMapInv W t q ∈ H \ fwdHull W t := by
  rw [← hc.Feq hq]; exact hc.F_mem_dom hq

lemma fl4_arc_subset (hc : SideCtx W t F) {R ε α β : ℝ} (hεR : ε < R) (hε : 0 < ε)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) :
    flCircArc ε α β ⊆ (H \ fwdHull W t) ∩ ball 0 R := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rw [← hηD] at hz
    obtain ⟨q, ⟨s, hs, rfl⟩, rfl⟩ := hz
    exact fl4_inv_mem hc (hη.2.2.1 hs)
  · obtain ⟨φ, -, rfl⟩ := hz
    rw [mem_ball_zero_iff]
    have := fl4Pol_norm ε φ
    rw [abs_of_pos hε] at this
    change ‖fl4Pol ε φ‖ < R
    rw [this]; exact hεR

/-- Points of `D ∩ B(0,R)` off the circle `|z| = ε` lie in `fl4WdDom`. -/
lemma fl4_mem_dom {R ε α β : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z ∈ (H \ fwdHull W t) ∩ ball 0 R) (hne : ‖z‖ ≠ ε) : z ∈ fl4WdDom W t R ε α β := by
  refine ⟨⟨hz.1.1, hz.2⟩, ?_⟩
  rintro (h | h)
  · exact hz.1.2 h
  · have := fl4_closure_arc_subset h
    rw [mem_sphere_zero_iff_norm, abs_of_pos hε] at this
    exact hne this

end FieldLawler
end QuantumZipper
