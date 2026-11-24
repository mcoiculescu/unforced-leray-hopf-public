import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6

/-!
# `PartIII-b:C/asrc/ra/6/1` : the lifts `ĥ_A`, `F_A+E_A`, `sΨ_A` are `g`-equivariant

Source of record: `the November 2 reference manuscript` 121-124, 4979-4981, 5024.

For a linear isometry `g` fixing `e₃`: `ϱ`, `age`, `trans`, `phase` (hence `chart`) are `g`-invariant,
`eR (g y) = g (eR y)`, so `Nv R b τ (g y) = g (Nv R b τ y)`; `sPsiPhys` depends on `y` only through
the chart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

theorem raEq_fixes_two {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) (y : Space) :
    (g y) 2 = y 2 := by
  have h := UnforcedLeray.Axi.symm_apply_two g hg (g y)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h.symm

theorem raEq_ϱ {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) (y : Space) :
    UnforcedLeray.Axi.ϱ (g y) = UnforcedLeray.Axi.ϱ y := by
  have h := UnforcedLeray.Axi.ϱ_symm_apply g hg (g y)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h.symm

theorem raEq_chart {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) (R τ : ℝ)
    (y : Space) : UnforcedLeray.Axi.chart R τ (g y) = UnforcedLeray.Axi.chart R τ y := by
  have h1 := raEq_ϱ hg y
  have h2 := raEq_fixes_two hg y
  simp only [UnforcedLeray.Axi.chart, UnforcedLeray.Axi.age, UnforcedLeray.Axi.phase,
    UnforcedLeray.Axi.trans, h1, h2]

theorem raEq_hor {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) (y : Space) :
    UnforcedLeray.Axi.hor (g y) = g (UnforcedLeray.Axi.hor y) := by
  have h2 := raEq_fixes_two hg y
  have hg3 : g UnforcedLeray.Axi.e3 = UnforcedLeray.Axi.e3 := hg
  rw [UnforcedLeray.Axi.hor_eq, UnforcedLeray.Axi.hor_eq, h2, map_sub, map_smul, hg3]

theorem raEq_eR {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) (y : Space) :
    UnforcedLeray.Axi.eR (g y) = g (UnforcedLeray.Axi.eR y) := by
  rw [UnforcedLeray.Axi.eR, UnforcedLeray.Axi.eR, raEq_ϱ hg y, map_smul, raEq_hor hg y]

theorem raEq_frameL {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) (y : Space)
    (v : UnforcedLeray.Axi.Merid) :
    UnforcedLeray.Axi.frameL (g y) v = g (UnforcedLeray.Axi.frameL y v) := by
  have hg3 : g UnforcedLeray.Axi.e3 = UnforcedLeray.Axi.e3 := hg
  rw [UnforcedLeray.Axi.frameL_apply, UnforcedLeray.Axi.frameL_apply, map_add, map_smul,
    map_smul, raEq_eR hg y, hg3]

theorem raEq_Nv {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) (R : ℝ)
    (b : ℝ × (ℝ × ℝ) → UnforcedLeray.Axi.Merid) (τ : ℝ) (y : Space) :
    UnforcedLeray.Axi.Nv R b τ (g y) = g (UnforcedLeray.Axi.Nv R b τ y) := by
  have hage : UnforcedLeray.Axi.age R (g y) = UnforcedLeray.Axi.age R y := by
    unfold UnforcedLeray.Axi.age
    rw [raEq_ϱ hg y]
  unfold UnforcedLeray.Axi.Nv
  rw [hage, raEq_chart hg R τ y, raEq_frameL hg y, map_smul]

theorem raEq_sPsi {g : Space ≃ₗᵢ[ℝ] Space} (hg : UnforcedLeray.FixesAxis g) (ν R : ℝ)
    (χ : ℝ → ℝ) (A : ℝ → Mat3) (τ : ℝ) (y : Space) :
    sPsiPhys ν R χ A (τ, g y) = sPsiPhys ν R χ A (τ, y) := by
  unfold sPsiPhys
  dsimp only
  rw [raEq_chart hg R τ y]

theorem raLiftsEquiv (as : ℝ) (χf : ℝ → ℝ) : RALiftsEquiv as χf := by
  intro _ ν μ ε _ _ A _ g hg
  refine ⟨fun τ y => raEq_Nv hg ε⁻¹ _ τ y, fun τ y => raEq_Nv hg ε⁻¹ _ τ y,
    fun τ y => raEq_sPsi hg ν ε⁻¹ χf A τ y⟩

end UnforcedLeray.Short.PartIIIb.Concrete
