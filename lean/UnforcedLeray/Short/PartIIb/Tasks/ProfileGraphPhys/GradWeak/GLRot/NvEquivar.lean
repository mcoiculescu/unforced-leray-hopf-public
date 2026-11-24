import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2

/-!
# `PartII-b:T10/7/1/1/2/1`: `gl_nvEquivar` (the lift `N_v` is `𝒪`-equivariant)

Source of record: `the November 2 reference manuscript` lines 1912-1921 (chart 1639-1668).
For `g` fixing `e₃` (`FixesAxis g`), `mer ∘ g = mer` (`Axi.mer_map`), so the chart and the age are
unchanged, `frameL (g y) v = g (frameL y v)` (`Axi.eR_map`, `g e₃ = e₃`), hence `Axi.Nv` is
equivariant. Splitting into real and imaginary parts (`reS`, `imS` of `realC A + I • realC B`) gives
the complex statement `NvC R b (τ, T y) = cApp T (NvC R b (τ, y))`, which holds for every `y`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Off the axis-independent part: the real ring lift `Axi.Nv` commutes with `g` when `g` fixes `e₃`. -/
theorem nv_fix_equivar {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (R τ : ℝ)
    (b : ℝ × (ℝ × ℝ) → Axi.Merid) (y : Space) :
    Axi.Nv R b τ (g y) = g (Axi.Nv R b τ y) := by
  have he3 : g Axi.e3 = Axi.e3 := hg
  have hage : Axi.age R (g y) = Axi.age R y := by
    simp only [Axi.age, Axi.ϱ_map hg]
  have hchart : Axi.chart R τ (g y) = Axi.chart R τ y := by
    simp only [Axi.chart, Axi.phase, Axi.trans, hage, Axi.ϱ_map hg, Axi.apply_two_map hg]
  have hframe : ∀ v : Axi.Merid, Axi.frameL (g y) v = g (Axi.frameL y v) := by
    intro v
    rw [Axi.frameL_apply, Axi.frameL_apply, Axi.eR_map hg y, map_add, map_smul, map_smul, he3]
  simp only [Axi.Nv, hage, hchart]
  rw [hframe, map_smul]

theorem reS_add_I (A B : Space) :
    reS (B0412.realC A + Complex.I • B0412.realC B) = A := by
  ext i
  simp [reS, B0412.realC_apply]

theorem imS_add_I (A B : Space) :
    imS (B0412.realC A + Complex.I • B0412.realC B) = B := by
  ext i
  simp [imS, B0412.realC_apply]

theorem cApp_add_I (T : Space ≃ₗᵢ[ℝ] Space) (A B : Space) :
    cApp T (B0412.realC A + Complex.I • B0412.realC B) =
      B0412.realC (T A) + Complex.I • B0412.realC (T B) := by
  unfold cApp
  rw [reS_add_I, imS_add_I]

/-- Complex ring lift equivariance for every `T` fixing `e₃`, at every point. -/
theorem NvC_equivar_fix {T : Space ≃ₗᵢ[ℝ] Space} (hT : FixesAxis T) (R : ℝ) (b : CProf)
    (τ : ℝ) (y : Space) :
    NvC R b (τ, T y) = cApp T (NvC R b (τ, y)) := by
  have h1 := nv_fix_equivar hT R τ (fun z => reM (b z)) y
  have h2 := nv_fix_equivar hT R τ (fun z => imM (b z)) y
  calc NvC R b (τ, T y)
      = B0412.realC (Axi.Nv R (fun z => reM (b z)) τ (T y)) +
          Complex.I • B0412.realC (Axi.Nv R (fun z => imM (b z)) τ (T y)) := rfl
    _ = B0412.realC (T (Axi.Nv R (fun z => reM (b z)) τ y)) +
          Complex.I • B0412.realC (T (Axi.Nv R (fun z => imM (b z)) τ y)) := by
        rw [h1, h2]
    _ = cApp T (B0412.realC (Axi.Nv R (fun z => reM (b z)) τ y) +
          Complex.I • B0412.realC (Axi.Nv R (fun z => imM (b z)) τ y)) :=
        (cApp_add_I T _ _).symm
    _ = cApp T (NvC R b (τ, y)) := rfl

theorem gl_nvEquivar : UnforcedLeray.Short.IIb.GLNvEquivar := by
  intro R b T hT
  have hfix : FixesAxis T := by
    rcases hT with h | ⟨θ, h⟩
    · rw [h]
      exact Axi.fixesAxis_reflY
    · rw [h]
      exact Axi.fixesAxis_rotZ θ
  exact ae_of_all _ (fun x => NvC_equivar_fix hfix R b x.1 x.2)

end UnforcedLeray.Short.IIb
