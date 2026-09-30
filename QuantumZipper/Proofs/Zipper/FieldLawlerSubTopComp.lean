import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopArc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-IMAGETOP (partial): the arcs of `D ∩ C_ε` as components of an open set of angles

Task FL-IMAGETOP (helper of FL-THM, D75). Field–Lawler, EJP 20 (2015), proof of Prop. 3.4 (p. 9):
`D ∩ C_ε = ⋃ⱼ ηⱼ`. For an open `D ⊆ ℍ`, the set of angles `flO D ε = {θ ∈ (0, π) | ε e^{iθ} ∈ D}`
is open; each of its connected components is an open interval `(α, β)` with `0 ≤ α < β ≤ π` whose
end points are not in `D` (`flComp_props`); conversely a maximal arc is a component
(`flComp_of_maximal`). Own elementary argument (components of open subsets of `ℝ`).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

/-- The angles of `D ∩ C_ε`. -/
def flO (D : Set ℂ) (ε : ℝ) : Set ℝ := {θ | θ ∈ Ioo 0 π ∧ flCirc ε θ ∈ D}

variable {D : Set ℂ} {ε : ℝ}

lemma flO_isOpen (hD : IsOpen D) : IsOpen (flO D ε) :=
  isOpen_Ioo.inter (hD.preimage (flCirc_continuous ε))

lemma flCirc_im (ε θ : ℝ) : (flCirc ε θ).im = ε * Real.sin θ := by
  simp [flCirc, Complex.exp_ofReal_mul_I_im]

lemma flCirc_mem_Ioo_of_H {θ : ℝ} (h : θ ∈ Icc 0 π) (hH : flCirc ε θ ∈ H) : θ ∈ Ioo 0 π := by
  have him : 0 < ε * Real.sin θ := by rw [← flCirc_im]; exact hH
  refine ⟨lt_of_le_of_ne h.1 fun h0 => ?_, lt_of_le_of_ne h.2 fun hπ => ?_⟩
  · rw [← h0, Real.sin_zero, mul_zero] at him; exact lt_irrefl _ him
  · rw [hπ, Real.sin_pi, mul_zero] at him; exact lt_irrefl _ him

/-- A component of `flO D ε` is `Ioo α β` with end points outside `D`. -/
theorem flComp_props (hD : IsOpen D) (hDH : D ⊆ H) {θ : ℝ} (hθ : θ ∈ flO D ε) :
    connectedComponentIn (flO D ε) θ =
        Ioo (sInf (connectedComponentIn (flO D ε) θ)) (sSup (connectedComponentIn (flO D ε) θ)) ∧
      0 ≤ sInf (connectedComponentIn (flO D ε) θ) ∧
      sInf (connectedComponentIn (flO D ε) θ) < sSup (connectedComponentIn (flO D ε) θ) ∧
      sSup (connectedComponentIn (flO D ε) θ) ≤ π ∧
      flCirc ε (sInf (connectedComponentIn (flO D ε) θ)) ∉ D ∧
      flCirc ε (sSup (connectedComponentIn (flO D ε) θ)) ∉ D ∧
      ∀ θ' ∈ connectedComponentIn (flO D ε) θ, flCirc ε θ' ∈ D := by
  set O := flO D ε with hOdef
  set I := connectedComponentIn O θ with hIdef
  have hO : IsOpen O := flO_isOpen hD
  have hIo : IsOpen I := hO.connectedComponentIn
  have hIc : IsConnected I := isConnected_connectedComponentIn_iff.2 hθ
  have hIO : I ⊆ O := connectedComponentIn_subset _ _
  have hθI : θ ∈ I := mem_connectedComponentIn hθ
  have hb : BddBelow I := ⟨0, fun y hy => (hIO hy).1.1.le⟩
  have ha : BddAbove I := ⟨π, fun y hy => (hIO hy).1.2.le⟩
  set α := sInf I with hα
  set β := sSup I with hβ
  have hαI : α ∉ I := fun h => by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hIo α h
    have hm : α - δ / 2 ∈ I := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    have := csInf_le hb hm
    linarith
  have hβI : β ∉ I := fun h => by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hIo β h
    have hm : β + δ / 2 ∈ I := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    have := le_csSup ha hm
    linarith
  have hIeq : I = Ioo α β := by
    refine Subset.antisymm (fun y hy => ?_) (hIc.Ioo_csInf_csSup_subset hb ha)
    exact ⟨lt_of_le_of_ne (csInf_le hb hy) fun h => hαI (h ▸ hy),
      lt_of_le_of_ne (le_csSup ha hy) fun h => hβI (h.symm ▸ hy)⟩
  have hαθ : α < θ := (hIeq ▸ hθI).1
  have hθβ : θ < β := (hIeq ▸ hθI).2
  have h0α : 0 ≤ α := le_csInf ⟨θ, hθI⟩ fun y hy => (hIO hy).1.1.le
  have hβπ : β ≤ π := csSup_le ⟨θ, hθI⟩ fun y hy => (hIO hy).1.2.le
  -- an end point in `O` would belong to `I`
  have hend : ∀ e : ℝ, e ∈ O → (∀ δ > 0, ∃ y ∈ I, |y - e| < δ) → e ∈ I := by
    intro e he hnear
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO e he
    obtain ⟨y, hyI, hye⟩ := hnear δ hδ
    have hsub : ball e δ ⊆ connectedComponentIn O y :=
      (convex_ball e δ).isPreconnected.subset_connectedComponentIn
        (by rw [Metric.mem_ball, Real.dist_eq]; exact hye) hball
    rw [← connectedComponentIn_eq hyI] at hsub
    exact hsub (mem_ball_self hδ)
  have hαO : α ∉ O := fun h => hαI (hend α h fun δ hδ => ⟨min (α + δ / 2) θ,
    hIeq ▸ ⟨lt_min (by linarith) hαθ, (min_le_right _ _).trans_lt hθβ⟩, by
      rw [abs_lt]; constructor
      · have : α < min (α + δ / 2) θ := lt_min (by linarith) hαθ
        linarith
      · have := min_le_left (α + δ / 2) θ
        linarith⟩)
  have hβO : β ∉ O := fun h => hβI (hend β h fun δ hδ => ⟨max (β - δ / 2) θ,
    hIeq ▸ ⟨hαθ.trans_le (le_max_right _ _), max_lt (by linarith) hθβ⟩, by
      rw [abs_lt]; constructor
      · have := le_max_left (β - δ / 2) θ
        linarith
      · have : max (β - δ / 2) θ < β := max_lt (by linarith) hθβ
        linarith⟩)
  refine ⟨hIeq, h0α, hαθ.trans hθβ, hβπ, fun h => hαO ⟨?_, h⟩, fun h => hβO ⟨?_, h⟩,
    fun y hy => (hIO hy).2⟩
  · exact flCirc_mem_Ioo_of_H ⟨h0α, (hαθ.trans hθβ).le.trans hβπ⟩ (hDH h)
  · exact flCirc_mem_Ioo_of_H ⟨h0α.trans (hαθ.trans hθβ).le, hβπ⟩ (hDH h)

/-- A maximal arc of `D ∩ C_ε` is a component of `flO D ε`. -/
theorem flComp_of_maximal (hD : IsOpen D) (hDH : D ⊆ H) {α β : ℝ} (hab : α < β) (h0α : 0 ≤ α)
    (hβπ : β ≤ π) (hin : ∀ θ ∈ Ioo α β, flCirc ε θ ∈ D) (hα : flCirc ε α ∉ D)
    (hβ : flCirc ε β ∉ D) : connectedComponentIn (flO D ε) ((α + β) / 2) = Ioo α β := by
  have hsubO : Ioo α β ⊆ flO D ε := fun θ hθ =>
    ⟨flCirc_mem_Ioo_of_H ⟨h0α.trans hθ.1.le, hθ.2.le.trans hβπ⟩ (hDH (hin θ hθ)), hin θ hθ⟩
  have hm : (α + β) / 2 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  obtain ⟨hIeq, -, -, -, hα', hβ', -⟩ := flComp_props hD hDH (hsubO hm)
  set I := connectedComponentIn (flO D ε) ((α + β) / 2) with hI
  have hsub : Ioo α β ⊆ I :=
    (isPreconnected_Ioo).subset_connectedComponentIn hm hsubO
  have hIO : I ⊆ flO D ε := connectedComponentIn_subset _ _
  have hsub' := hsub
  rw [hIeq, Ioo_subset_Ioo_iff hab] at hsub'
  have e1 : sInf I = α := by
    refine le_antisymm hsub'.1 (not_lt.1 fun hlt => hα (hIO ?_).2)
    rw [hIeq]; exact ⟨hlt, hab.trans_le hsub'.2⟩
  have e2 : sSup I = β := by
    refine le_antisymm (not_lt.1 fun hlt => hβ (hIO ?_).2) hsub'.2
    rw [hIeq]; exact ⟨hsub'.1.trans_lt hab, hlt⟩
  rw [hIeq, e1, e2]

end FieldLawler
end QuantumZipper
