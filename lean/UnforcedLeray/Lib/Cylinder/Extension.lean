import UnforcedLeray.Lib.Cylinder.Lebesgue
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Zero extension, restriction and the cell projection (INF13, target CY14)


§5 CY14.

`paper/main.tex` lines 6166-6188 (unit B0319): "`ℋ_m = L²(ℝ², ⟨y⟩^{2m} dy)`. `I_c` is zero
extension of cell functions, `R_c = I_c*` is restriction, and `Π_c = I_c R_c`."  Lines
6469-6492 (unit B0342) use the same objects on moving cells.

* `hμ m = ⟨y⟩^{2m} dy = (1 + q² + η²)^m dq dη` on the plane and `Hm m = L²(hμ m)`.
* `Ic c m : Xc c m →L[ℂ] Hm m` is the zero extension (`coeFn_Ic`); it is an isometry
  (`norm_Ic`), because the cell space `Xc c m` carries the centred weight, which is the
  restriction of `⟨y⟩^{2m}` (`hμ_restrict_cell`).
  The scoping note writes the domain as `X c m` (smooth periodic weight); with that domain the
  zero extension is not an isometry and `Rc ∘ Ic = id` fails, so the centred space of B0242
  and B0319 is used.
* `Rc c m = (Ic c m)†`, `Rc_comp_Ic : Rc ∘ Ic = id`; `Rc` is the restriction to the cell
  (`coeFn_Rc`).
* `PiC c m = Ic ∘ Rc` is the orthogonal projection onto functions supported in the cell
  (`PiC_idem`, `isSelfAdjoint_PiC`, `coeFn_PiC`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Cyl

/-- `⟨y⟩^{2m} dy = (1 + q² + η²)^m dq dη` on the plane (B0319). -/
def hμ (m : ℝ) : Measure Plane := volume.withDensity fun z => ENNReal.ofReal (ρc z ^ m)

/-- `ℋ_m = L²(ℝ², ⟨y⟩^{2m} dy; ℂ)` (B0319, tex 6166-6188). -/
abbrev Hm (m : ℝ) := Lp ℂ 2 (hμ m)

theorem hμ_restrict_cell (c m : ℝ) : (hμ m).restrict (cell c) = wμc c m := by
  rw [hμ, restrict_withDensity (measurableSet_cell c)]; rfl

theorem memLp_indicator_cell {c m : ℝ} (f : Xc c m) :
    MemLp ((cell c).indicator f) 2 (hμ m) := by
  rw [memLp_indicator_iff_restrict (measurableSet_cell c), hμ_restrict_cell]
  exact Lp.memLp f

theorem indicator_ae_eq {c m : ℝ} {f g : Plane → ℂ} (h : f =ᵐ[wμc c m] g) :
    (cell c).indicator f =ᵐ[hμ m] (cell c).indicator g := by
  rw [← hμ_restrict_cell, EventuallyEq, ae_restrict_iff' (measurableSet_cell c)] at h
  filter_upwards [h] with z hz
  by_cases hzc : z ∈ cell c
  · rw [indicator_of_mem hzc, indicator_of_mem hzc, hz hzc]
  · rw [indicator_of_notMem hzc, indicator_of_notMem hzc]

/-- The zero extension as a linear isometry. -/
def IcLI (c m : ℝ) : Xc c m →ₗᵢ[ℂ] Hm m where
  toFun f := (memLp_indicator_cell f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_indicator_cell (f + g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_indicator_cell f).toLp _) ((memLp_indicator_cell g).toLp _),
      (memLp_indicator_cell f).coeFn_toLp, (memLp_indicator_cell g).coeFn_toLp,
      indicator_ae_eq (Lp.coeFn_add f g)] with z h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    by_cases hzc : z ∈ cell c <;> simp [hzc]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [(memLp_indicator_cell (a • f)).coeFn_toLp,
      Lp.coeFn_smul a ((memLp_indicator_cell f).toLp _),
      (memLp_indicator_cell f).coeFn_toLp,
      indicator_ae_eq (Lp.coeFn_smul a f)] with z h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4]
    by_cases hzc : z ∈ cell c <;> simp [hzc]
  norm_map' f := by
    change ‖(memLp_indicator_cell f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_cell c),
      hμ_restrict_cell]

/-- `I_c`: zero extension of cell functions into `ℋ_m` (CY14; B0319, tex 6166-6188). -/
def Ic (c m : ℝ) : Xc c m →L[ℂ] Hm m := (IcLI c m).toContinuousLinearMap

theorem coeFn_Ic {c m : ℝ} (f : Xc c m) : (Ic c m f : Plane → ℂ) =ᵐ[hμ m] (cell c).indicator f :=
  (memLp_indicator_cell f).coeFn_toLp

theorem norm_Ic {c m : ℝ} (f : Xc c m) : ‖Ic c m f‖ = ‖f‖ := (IcLI c m).norm_map f

/-- `R_c = I_c*` (CY14; B0319). -/
def Rc (c m : ℝ) : Hm m →L[ℂ] Xc c m := ContinuousLinearMap.adjoint (Ic c m)

/-- `R_c I_c = id` (CY14 `Rc_comp_Ic`). -/
theorem Rc_comp_Ic (c m : ℝ) : Rc c m ∘L Ic c m = ContinuousLinearMap.id ℂ (Xc c m) :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (Ic c m)).1 (norm_Ic)

theorem Rc_Ic {c m : ℝ} (f : Xc c m) : Rc c m (Ic c m f) = f := by
  rw [← ContinuousLinearMap.comp_apply, Rc_comp_Ic, ContinuousLinearMap.id_apply]

/-- `Π_c = I_c R_c` (CY14; B0319). -/
def PiC (c m : ℝ) : Hm m →L[ℂ] Hm m := Ic c m ∘L Rc c m

theorem PiC_idem (c m : ℝ) : PiC c m ∘L PiC c m = PiC c m := by
  rw [PiC, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (Rc c m),
    Rc_comp_Ic, ContinuousLinearMap.id_comp]

theorem isSelfAdjoint_PiC (c m : ℝ) : IsSelfAdjoint (PiC c m) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, PiC, ContinuousLinearMap.adjoint_comp,
    Rc, ContinuousLinearMap.adjoint_adjoint]

/-! ### `R_c` is the restriction to the cell -/

theorem memLp_restrict_cell {c m : ℝ} (g : Hm m) : MemLp g 2 (wμc c m) := by
  rw [← hμ_restrict_cell]; exact (Lp.memLp g).restrict _

/-- `R_c g = g|_cell` (B0319: "`R_c = I_c*` is restriction"). -/
theorem coeFn_Rc {c m : ℝ} (g : Hm m) : (Rc c m g : Plane → ℂ) =ᵐ[wμc c m] g := by
  have key : Rc c m g = (memLp_restrict_cell (c := c) g).toLp _ := by
    refine ext_inner_right ℂ fun f => ?_
    rw [Rc, ContinuousLinearMap.adjoint_inner_left, MeasureTheory.L2.inner_def,
      MeasureTheory.L2.inner_def]
    have h1 : ∫ z, ⟪(g : Plane → ℂ) z, (Ic c m f : Plane → ℂ) z⟫_ℂ ∂hμ m =
        ∫ z in cell c, ⟪(g : Plane → ℂ) z, (f : Plane → ℂ) z⟫_ℂ ∂hμ m := by
      rw [← integral_indicator (measurableSet_cell c)]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_Ic f] with z hz
      rw [hz]
      by_cases hzc : z ∈ cell c
      · simp [indicator_of_mem hzc]
      · simp [indicator_of_notMem hzc]
    rw [h1, hμ_restrict_cell]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_restrict_cell (c := c) g).coeFn_toLp] with z hz
    rw [hz]
  rw [key]
  exact (memLp_restrict_cell g).coeFn_toLp

/-- `Π_c g = 1_cell g` (B0319). -/
theorem coeFn_PiC {c m : ℝ} (g : Hm m) :
    (PiC c m g : Plane → ℂ) =ᵐ[hμ m] (cell c).indicator g := by
  have h1 := coeFn_Ic (Rc c m g)
  have h2 := indicator_ae_eq (coeFn_Rc (c := c) g)
  exact h1.trans h2

end UnforcedLeray.Cyl
