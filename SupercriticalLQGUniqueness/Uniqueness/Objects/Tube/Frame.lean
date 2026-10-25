import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Polar




 
















set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 

 
def o1 (sp ψv : ℝ) : Path (pol (1 + 3 * sp / 4) ψv) (pol (3 / 2) ψv) :=
  polarPath (1 + 3 * sp / 4) (3 / 2) ψv ψv
 
def o2 (ψv : ℝ) : Path (pol (3 / 2) ψv) (pol (3 / 2) 0) := polarPath (3 / 2) (3 / 2) ψv 0
 
def o3 : Path (pol (3 / 2) 0) (pol (5 / 2) 0) := polarPath (3 / 2) (5 / 2) 0 0
 
def t1 (Δ : ℝ) : Path (pol (5 / 2) 0) (pol (5 / 2) (Δ / 2)) := polarPath (5 / 2) (5 / 2) 0 (Δ / 2)
 
def t2 (Δ : ℝ) : Path (pol (5 / 2) (Δ / 2)) (pol (7 / 2) (Δ / 2)) :=
  polarPath (5 / 2) (7 / 2) (Δ / 2) (Δ / 2)
 
def t3 (Δ : ℝ) : Path (pol (7 / 2) (Δ / 2)) (pol (7 / 2) Δ) := polarPath (7 / 2) (7 / 2) (Δ / 2) Δ
 
def t4 (Δ : ℝ) : Path (pol (7 / 2) Δ) (pol 4 Δ) := polarPath (7 / 2) 4 Δ Δ

 
def outPath (sp ψv Δ : ℝ) : Path (pol (1 + 3 * sp / 4) ψv) (pol 4 Δ) :=
  (o1 sp ψv).trans ((o2 ψv).trans (o3.trans ((t1 Δ).trans ((t2 Δ).trans ((t3 Δ).trans (t4 Δ))))))

 

 
def nt4 (Δ : ℝ) : Path (pol 4 (Δ + π)) (pol (7 / 2) (Δ + π)) := polarPath 4 (7 / 2) (Δ + π) (Δ + π)
 
def nt3 (Δ : ℝ) : Path (pol (7 / 2) (Δ + π)) (pol (7 / 2) (Δ / 2 + π)) :=
  polarPath (7 / 2) (7 / 2) (Δ + π) (Δ / 2 + π)
 
def nt2 (Δ : ℝ) : Path (pol (7 / 2) (Δ / 2 + π)) (pol (5 / 2) (Δ / 2 + π)) :=
  polarPath (7 / 2) (5 / 2) (Δ / 2 + π) (Δ / 2 + π)
 
def nt1 (Δ : ℝ) : Path (pol (5 / 2) (Δ / 2 + π)) (pol (5 / 2) π) :=
  polarPath (5 / 2) (5 / 2) (Δ / 2 + π) π
 
def i2 : Path (pol (5 / 2) π) (pol 0 π) := polarPath (5 / 2) 0 π π

theorem pol_zero_eq (a b : ℝ) : pol 0 a = pol 0 b := by rw [pol_zero_left, pol_zero_left]

 
def i1 (α sp ψu : ℝ) : Path (pol 0 π) (pol (α - 3 * sp / 4) ψu) :=
  (polarPath 0 (α - 3 * sp / 4) ψu ψu).cast (pol_zero_eq π ψu) rfl

 
def inPath (α sp ψu Δ : ℝ) : Path (pol 4 (Δ + π)) (pol (α - 3 * sp / 4) ψu) :=
  (nt4 Δ).trans ((nt3 Δ).trans ((nt2 Δ).trans ((nt1 Δ).trans (i2.trans (i1 α sp ψu)))))

 

 
def clampAng (sp ψ : ℝ) : ℝ := max (-(π / 2) + sp / 4) (min ψ (π / 2 - sp / 4))

 

def blockSpine (α sp ψu ψv : ℝ) : Path (pol (α - 3 * sp / 4) ψu) (pol (1 + 3 * sp / 4) ψv) :=
  (polarPath (α - 3 * sp / 4) (α + sp / 2) ψu ψu).trans
    ((polarPath (α + sp / 2) (α + sp / 2) ψu (clampAng sp ψu)).trans
      ((polarPath (α + sp / 2) (1 - sp / 2) (clampAng sp ψu) (clampAng sp ψv)).trans
        ((polarPath (1 - sp / 2) (1 - sp / 2) (clampAng sp ψv) ψv).trans
          (polarPath (1 - sp / 2) (1 + 3 * sp / 4) ψv ψv))))

 

 
def blockNorm (α : ℝ) : Set ℂ := {ζ | α < ‖ζ‖ ∧ ‖ζ‖ < 1 ∧ 0 < ζ.re}

 
def corrOutH (Δ : ℝ) : Set ℂ := {x | 4 ≤ (ex (-Δ) * x).re}

 
def corrInH (Δ : ℝ) : Set ℂ := {x | 4 ≤ -(ex (-Δ) * x).re}

 
def outRest (ψv Δ : ℝ) : Set ℂ :=
  range (o2 ψv) ∪ range o3 ∪ range (t1 Δ) ∪ range (t2 Δ) ∪ range (t3 Δ) ∪ range (t4 Δ)

 
def inRest (Δ : ℝ) : Set ℂ :=
  range (nt4 Δ) ∪ range (nt3 Δ) ∪ range (nt2 Δ) ∪ range (nt1 Δ) ∪ range i2

theorem range_outPath (sp ψv Δ : ℝ) :
    range (outPath sp ψv Δ) = range (o1 sp ψv) ∪ outRest ψv Δ := by
  simp only [outPath, Path.trans_range, outRest]
  ext x; simp only [mem_union]; tauto

theorem range_i1 (α sp ψu : ℝ) :
    range (i1 α sp ψu) = range (polarPath 0 (α - 3 * sp / 4) ψu ψu) := by
  simp [i1]

theorem range_inPath (α sp ψu Δ : ℝ) :
    range (inPath α sp ψu Δ) = inRest Δ ∪ range (i1 α sp ψu) := by
  simp only [inPath, Path.trans_range, inRest]
  ext x; simp only [mem_union]; tauto

 

section Describe

variable {α sp ψu ψv Δ : ℝ} {x : ℂ}

theorem mem_o1 (hsp : sp ≤ 2 / 3) (hx : x ∈ range (o1 sp ψv)) :
    ∃ R ∈ Icc (1 + 3 * sp / 4) (3 / 2), x = pol R ψv := by
  obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
  rw [uIcc_of_le (by linarith)] at hR
  exact ⟨R, hR, rfl⟩

theorem mem_o2 (hx : x ∈ range (o2 ψv)) : ∃ φ ∈ uIcc ψv 0, x = pol (3 / 2) φ :=
  mem_range_polarPath_arc hx

theorem mem_o3 (hx : x ∈ range o3) : ∃ R ∈ Icc (3 / 2 : ℝ) (5 / 2), x = pol R 0 := by
  obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
  rw [uIcc_of_le (by norm_num)] at hR
  exact ⟨R, hR, rfl⟩

theorem mem_t1 (hx : x ∈ range (t1 Δ)) : ∃ φ ∈ uIcc 0 (Δ / 2), x = pol (5 / 2) φ :=
  mem_range_polarPath_arc hx

theorem mem_t2 (hx : x ∈ range (t2 Δ)) : ∃ R ∈ Icc (5 / 2 : ℝ) (7 / 2), x = pol R (Δ / 2) := by
  obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
  rw [uIcc_of_le (by norm_num)] at hR
  exact ⟨R, hR, rfl⟩

theorem mem_t3 (hx : x ∈ range (t3 Δ)) : ∃ φ ∈ uIcc (Δ / 2) Δ, x = pol (7 / 2) φ :=
  mem_range_polarPath_arc hx

theorem mem_t4 (hx : x ∈ range (t4 Δ)) : ∃ R ∈ Icc (7 / 2 : ℝ) 4, x = pol R Δ := by
  obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
  rw [uIcc_of_le (by norm_num)] at hR
  exact ⟨R, hR, rfl⟩

theorem mem_nt4 (hx : x ∈ range (nt4 Δ)) : ∃ R ∈ Icc (7 / 2 : ℝ) 4, x = pol R (Δ + π) := by
  obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
  rw [uIcc_of_ge (by norm_num)] at hR
  exact ⟨R, hR, rfl⟩

theorem mem_nt3 (hx : x ∈ range (nt3 Δ)) :
    ∃ φ ∈ uIcc (Δ / 2) Δ, x = pol (7 / 2) (φ + π) := by
  obtain ⟨φ, hφ, rfl⟩ := mem_range_polarPath_arc hx
  refine ⟨φ - π, ?_, by rw [sub_add_cancel]⟩
  have h := hφ
  rw [mem_uIcc] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; constructor <;> linarith
  · left; constructor <;> linarith

theorem mem_nt2 (hx : x ∈ range (nt2 Δ)) : ∃ R ∈ Icc (5 / 2 : ℝ) (7 / 2), x = pol R (Δ / 2 + π) := by
  obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
  rw [uIcc_of_ge (by norm_num)] at hR
  exact ⟨R, hR, rfl⟩

theorem mem_nt1 (hx : x ∈ range (nt1 Δ)) : ∃ φ ∈ uIcc 0 (Δ / 2), x = pol (5 / 2) (φ + π) := by
  obtain ⟨φ, hφ, rfl⟩ := mem_range_polarPath_arc hx
  refine ⟨φ - π, ?_, by rw [sub_add_cancel]⟩
  have h := hφ
  rw [mem_uIcc] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; constructor <;> linarith
  · left; constructor <;> linarith

theorem mem_i2 (hx : x ∈ range i2) : ∃ R ∈ Icc (0 : ℝ) (5 / 2), x = pol R π := by
  obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
  rw [uIcc_of_ge (by norm_num)] at hR
  exact ⟨R, hR, rfl⟩

theorem mem_i1 (hpos : 0 ≤ α - 3 * sp / 4) (hx : x ∈ range (i1 α sp ψu)) :
    ∃ R ∈ Icc (0 : ℝ) (α - 3 * sp / 4), x = pol R ψu := by
  rw [range_i1] at hx
  obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
  rw [uIcc_of_le hpos] at hR
  exact ⟨R, hR, rfl⟩

end Describe

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
