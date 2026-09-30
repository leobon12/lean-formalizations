import QuantumZipper.Proofs.Zipper.FieldLawler4L33Curve
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 4: Lemma 3.3 + (2.4) for arcs ending on the left (mirror image)

`fl4_lemma33_neg`: `fl4_lemma33_loewner` for arcs whose end points lie on `K` or on the closed
third quadrant (the arcs of the negative crosscuts, which may end at `−ε`). Proof: reflect by
`ρ z = −conj z` (`fl4_lemma33_curve` for the curve `ρ ∘ trace W`), and `fl2FluxR` is
`ρ`-invariant (`fl4_fluxR_refl`, the change of variables `θ ↦ π − θ`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Complex Metric
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- The reflection `z ↦ −conj z`. -/
def fl4ρ (z : ℂ) : ℂ := -(starRingEnd ℂ) z

theorem fl4ρ_fl2Pt (R θ s : ℝ) : fl4ρ (fl2Pt R θ s) = fl2Pt R (π - θ) s := by
  simp only [fl4ρ, fl2Pt, map_mul, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show ((π - θ : ℝ) : ℂ) * I = (π : ℂ) * I + ((θ : ℂ) * -I) by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem fl4_rDer_refl (R : ℝ) (h : ℂ → ℝ) (θ : ℝ) :
    fl2rDer R (h ∘ fl4ρ) θ = fl2rDer R h (π - θ) := by
  have e : (fun s : ℝ => (h ∘ fl4ρ) (fl2Pt R θ s) / s) = fun s => h (fl2Pt R (π - θ) s) / s := by
    funext s; simp only [Function.comp, fl4ρ_fl2Pt]
  unfold fl2rDer
  rw [e]

theorem fl4_fluxR_refl (R : ℝ) (h : ℂ → ℝ) : fl2FluxR R (h ∘ fl4ρ) = fl2FluxR R h := by
  unfold fl2FluxR
  simp only [fl4_rDer_refl]
  have hmp : MeasurePreserving (fun θ : ℝ => π - θ) volume volume :=
    Measure.measurePreserving_sub_left volume π
  have hemb : MeasurableEmbedding (fun θ : ℝ => π - θ) :=
    (Homeomorph.subLeft π).measurableEmbedding
  have hpre : (fun θ : ℝ => π - θ) ⁻¹' Ioo 0 π = Ioo 0 π := by
    ext θ; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;>
      linarith [h.1, h.2]
  have := hmp.setLIntegral_comp_preimage_emb hemb
    (fun θ => ENNReal.ofReal (fl2rDer R h θ * R)) (Ioo 0 π)
  rw [hpre] at this
  exact this

theorem fl4ρ_involutive (z : ℂ) : fl4ρ (fl4ρ z) = z := by simp [fl4ρ]

theorem fl4ρ_injective : Function.Injective fl4ρ := fun a b h => by
  rw [← fl4ρ_involutive a, h, fl4ρ_involutive]

theorem fl4ρ_im (z : ℂ) : (fl4ρ z).im = z.im := by simp [fl4ρ]

theorem fl4ρ_norm (z : ℂ) : ‖fl4ρ z‖ = ‖z‖ := by simp [fl4ρ]

theorem fl4ρ_eq_flSim (z : ℂ) : fl4ρ z = flSim (-1) 1 z :=
  Complex.ext (by simp [fl4ρ, flSim]) (by simp [fl4ρ, flSim])

theorem fl4ρ_circ (ε θ : ℝ) : fl4ρ ((ε : ℂ) * exp (θ * I)) = (ε : ℂ) * exp (((π - θ : ℝ) : ℂ) * I) := by
  have := fl4ρ_fl2Pt ε θ 0
  simpa [fl2Pt] using this

theorem fl4ρ_image_arc (ε α β : ℝ) :
    fl4ρ '' flCircArc ε α β = flCircArc ε (π - β) (π - α) := by
  ext z; constructor
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    exact ⟨π - θ, ⟨by linarith [hθ.2], by linarith [hθ.1]⟩, (fl4ρ_circ ε θ).symm⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨(ε : ℂ) * exp (((π - θ : ℝ) : ℂ) * I), ⟨π - θ, ⟨by linarith [hθ.2], by linarith [hθ.1]⟩,
      rfl⟩, ?_⟩
    rw [fl4ρ_circ]; congr 3; push_cast; ring

/-- **Lemma 3.3 + (2.4) for arcs ending on the left.** -/
theorem fl4_lemma33_neg {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t R ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (hR : 4 * ε ≤ R)
    (htr0 : trace W 0 = 0) (hcont : ContinuousOn (trace W) (Icc 0 t))
    (hH : ∀ s ∈ Ioc 0 t, trace W s ∈ H) (hhull : fwdHull W t = trace W '' Ioc 0 t)
    (hγR : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (hγt : ‖trace W t‖ = R)
    {n : ℕ} {α β : Fin n → ℝ} (hαβ : ∀ k, 0 < α k ∧ α k < β k ∧ β k ≤ π)
    (hend : ∀ k, (ε : ℂ) * exp (α k * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} ∧
      (ε : ℂ) * exp (β k * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0})
    (harc : ∀ k, flCircArc ε (α k) (β k) ⊆ H \ trace W '' Ioc 0 t)
    (hdisj : Pairwise fun i j => Disjoint (flCircArc ε (α i) (β i)) (flCircArc ε (α j) (β j)))
    {h : Fin n → ℂ → ℝ}
    (hh : ∀ k, IsHarmMeas (fl4D₁ W t R \ flCircArc ε (α k) (β k)) (flCircArc ε (α k) (β k))
      (h k)) :
    ∑ k, fl2FluxR R (h k) ≤ ENNReal.ofReal (128 * π * ε / R) * ENNReal.ofReal π := by
  classical
  set γ : ℝ → ℂ := fun s => fl4ρ (trace W s) with hγ
  have hρc : Continuous fl4ρ := by unfold fl4ρ; fun_prop
  have himg : ∀ S : Set ℝ, γ '' S = fl4ρ '' (trace W '' S) := fun S => by
    rw [image_image]
  have hρH : fl4ρ '' H = H := by
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩; show 0 < (fl4ρ w).im; rw [fl4ρ_im]; exact hw
    · intro hz; exact ⟨fl4ρ z, show 0 < (fl4ρ z).im by rw [fl4ρ_im]; exact hz, fl4ρ_involutive z⟩
  have hρB : fl4ρ '' ball (0 : ℂ) R = ball 0 R := by
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩; rw [mem_ball_zero_iff, fl4ρ_norm]; exact mem_ball_zero_iff.1 hw
    · intro hz
      exact ⟨fl4ρ z, by rw [mem_ball_zero_iff, fl4ρ_norm]; exact mem_ball_zero_iff.1 hz,
        fl4ρ_involutive z⟩
  have hpc : IsPreconnected (H \ γ '' Ioc 0 t) := by
    have h0 := RS.isPreconnected_compl_fwdHull hW hW0 ht
    rw [hhull] at h0
    have h1 := h0.image fl4ρ hρc.continuousOn
    rwa [image_diff fl4ρ_injective, hρH, ← himg] at h1
  have hD : ∀ k, fl4ρ '' (fl4D₁ W t R \ flCircArc ε (α k) (β k)) =
      ((H \ γ '' Ioc 0 t) ∩ ball 0 R) \ flCircArc ε (π - β k) (π - α k) := by
    intro k
    rw [fl4D₁, image_diff fl4ρ_injective, image_inter fl4ρ_injective, image_diff fl4ρ_injective,
      hρH, hρB, ← himg, fl4ρ_image_arc]
  have hh' : ∀ k, IsHarmMeas (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \
      flCircArc ε (π - β k) (π - α k)) (flCircArc ε (π - β k) (π - α k)) (h k ∘ fl4ρ) := by
    intro k
    have := flSim_isHarmMeas (σ := -1) (m := 1) (Or.inr rfl) one_pos (hh k)
    have he : ∀ S : Set ℂ, flSimHomeo (-1) 1 (fl_sigma_sq (Or.inr rfl)) one_pos.ne' '' S =
        fl4ρ '' S := fun S => by
      ext z; simp only [mem_image]
      exact ⟨fun ⟨w, hw, e⟩ => ⟨w, hw, (fl4ρ_eq_flSim w).trans e⟩,
        fun ⟨w, hw, e⟩ => ⟨w, hw, (fl4ρ_eq_flSim w).symm.trans e⟩⟩
    rw [he, he, hD k, fl4ρ_image_arc] at this
    convert this using 1
    funext w
    simp only [Function.comp]
    congr 1
    rw [fl4ρ_eq_flSim]
    apply Complex.ext <;> simp [flSim]
  have hsum := fl4_lemma33_curve (γ := γ) ht hε hR (by simp [hγ, htr0, fl4ρ])
    ((hρc.comp_continuousOn hcont))
    (fun s hs => by show 0 < (γ s).im; simp only [hγ]; rw [fl4ρ_im]; exact hH s hs) hpc
    (fun s hs => by simp only [hγ]; rw [fl4ρ_norm]; exact hγR s hs)
    (by simp only [hγ]; rw [fl4ρ_norm]; exact hγt)
    (α := fun k => π - β k) (β := fun k => π - α k)
    (fun k => ⟨by linarith [(hαβ k).2.2], by linarith [(hαβ k).2.1], by linarith [(hαβ k).1]⟩)
    (fun k => by
      have e1 : (ε : ℂ) * exp (((π - β k : ℝ) : ℂ) * I) = fl4ρ ((ε : ℂ) * exp (β k * I)) :=
        (fl4ρ_circ ε (β k)).symm
      have e2 : (ε : ℂ) * exp (((π - α k : ℝ) : ℂ) * I) = fl4ρ ((ε : ℂ) * exp (α k * I)) :=
        (fl4ρ_circ ε (α k)).symm
      have tr : ∀ z, z ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} →
          fl4ρ z ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} := by
        rintro z (⟨s, hs, rfl⟩ | hz)
        · exact Or.inl ⟨s, hs, rfl⟩
        · refine Or.inr ⟨by rw [fl4ρ_im]; exact hz.1, ?_⟩
          simp only [fl4ρ, neg_re, conj_re]; linarith [hz.2]
      exact ⟨e1 ▸ tr _ (hend k).2, e2 ▸ tr _ (hend k).1⟩)
    (fun k => by
      rw [← fl4ρ_image_arc]
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨hzH, hzK⟩ := harc k hz
      refine ⟨show 0 < (fl4ρ z).im by rw [fl4ρ_im]; exact hzH, ?_⟩
      rintro ⟨s, hs, e⟩
      exact hzK ⟨s, hs, fl4ρ_injective e⟩)
    (fun i j hij => by
      show Disjoint (flCircArc ε (π - β i) (π - α i)) (flCircArc ε (π - β j) (π - α j))
      rw [← fl4ρ_image_arc, ← fl4ρ_image_arc]
      exact (disjoint_image_iff fl4ρ_injective).2 (hdisj hij))
    hh'
  calc ∑ k, fl2FluxR R (h k) = ∑ k, fl2FluxR R (h k ∘ fl4ρ) :=
        Finset.sum_congr rfl fun k _ => (fl4_fluxR_refl R (h k)).symm
    _ ≤ _ := hsum

end FieldLawler
end QuantumZipper
