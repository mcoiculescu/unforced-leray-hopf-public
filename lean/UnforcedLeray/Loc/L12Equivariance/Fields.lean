import UnforcedLeray.Loc.L12Equivariance.Rotation

/-!
# L12 helper: `𝒪` commutes with the heat flow, the tensors and the weak `-𝔓 div`

`paper/main.tex` lines 563–567 (step L12, blueprint unit B1025): "The action commutes with
`𝒜_h`, `𝔓` and the Navier–Stokes nonlinearity". For a linear isometry `g` of `ℝ³`:

* the Gaussian kernel is radial, so `e^{tΔ}(g·f) = g·(e^{tΔ}f)` pointwise
  (`average_rotateField`); hence the heat flow, the compiled free similarity evolution
  `AncientLocalization.freeEvolution` and the heat profile `H_h` commute with `g`;
* the columns of `g·𝕋 = g 𝕋(g⁻¹·) gᵀ` are `(g·𝕋)ₖ = ∑ⱼ gₖⱼ (g·𝕋ⱼ)` (`rotCols`), and
  `u ⊗ v`, `u ⊗ v + v ⊗ u` are equivariant (`tensorColumns_rot`, `symTensorColumns_rot`);
* the literal weak `-𝔓 div` of `Package.lean` is equivariant:
  `F = -𝔓 div 𝕋 ⇒ g·F = -𝔓 div (g·𝕋)` (`IsMinusLerayDiv.rot`), using that `𝔓` commutes
  with `rotL2 g` (`Rotation.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L12

open SobolevGraph
open UnforcedLeray.Blueprint.L10 (toL2_of_ae_eq_coeFn coeFn_finsetSum vectorTest_memLp
  testPartial_memLp)

variable (g : Space ≃ₗᵢ[ℝ] Space)

/-! ## The heat flow -/

theorem kernel_rot (t : ℝ) (z : Space) : Heat.kernel t (g z) = Heat.kernel t z := by
  simp only [Heat.kernel, Heat.Gaussian.kernel, LinearIsometryEquiv.norm_map]

/-- `e^{tΔ}(g·f)(x) = g (e^{tΔ}f)(g⁻¹x)`, at every point and every time. -/
theorem average_rotateField (t : ℝ) (f : SpatialField) (x : Space) :
    Heat.average t (rotateField g f) x = g (Heat.average t f (g.symm x)) := by
  simp only [Heat.average, rotateField]
  rw [← MeasureTheory.integral_comp g
    (fun y => Heat.kernel t y • g (f (g.symm (x - y))))]
  have h2 := LinearIsometry.integral_comp_comm (μ := volume) g.toLinearIsometry
    (fun y : Space => Heat.kernel t y • f (g.symm x - y))
  simp only [LinearIsometryEquiv.coe_toLinearIsometry] at h2
  rw [← h2]
  congr 1
  funext z
  simp only [kernel_rot, map_sub, LinearIsometryEquiv.symm_apply_apply, map_smul]

theorem flow_rotateField (f : SpatialField) (t : ℝ) :
    Heat.flow (rotateField g f) t = rotateField g (Heat.flow f t) := by
  by_cases ht : 0 < t
  · rw [Heat.flow_pos _ ht, Heat.flow_pos _ ht]
    funext x
    rw [average_rotateField]
    rfl
  · rw [Heat.flow_nonpos _ (not_lt.mp ht), Heat.flow_nonpos _ (not_lt.mp ht)]

theorem freeEvolution_rotateField (h s : ℝ) (f : SpatialField) :
    AncientLocalization.freeEvolution h s (rotateField g f) =
      rotateField g (AncientLocalization.freeEvolution h s f) := by
  unfold AncientLocalization.freeEvolution
  rw [flow_rotateField]
  funext x
  simp only [SpatialScaling.spatialScale, rotateField, map_smul]

theorem heatProfile_rotateField (h : ℝ) (u : SpatialField) (τ : ℝ) :
    heatProfile h (rotateField g u) τ = rotateField g (heatProfile h u τ) := by
  funext y
  simp only [heatProfile, average_rotateField, rotateField, map_smul]

theorem heatProfile_congr {h : ℝ} {u u' : SpatialField} (hu : u =ᵐ[volume] u') (τ : ℝ) :
    heatProfile h u τ = heatProfile h u' τ := by
  funext y
  simp only [heatProfile, Heat.average_congr_ae hu]

/-- An `𝒪`-invariant field has an `𝒪`-invariant heat profile, at every point. -/
theorem heatProfile_invariant {h : ℝ} {u : SpatialField} (hu : rotateField g u =ᵐ[volume] u)
    (τ : ℝ) : rotateField g (heatProfile h u τ) = heatProfile h u τ := by
  rw [← heatProfile_rotateField, heatProfile_congr hu]

/-! ## Tensors -/

/-- The columns of `g·𝕋 = g 𝕋(g⁻¹·) gᵀ`: `(g·𝕋)ₖ = ∑ⱼ gₖⱼ (g·𝕋ⱼ)`. -/
def rotCols (col : Fin 3 → SpatialField) (k : Fin 3) : SpatialField :=
  fun x => ∑ j : Fin 3, rc g k j • rotateField g (col j) x

theorem tensorColumns_rot (u v : SpatialField) :
    tensorColumns (rotateField g u) (rotateField g v) = rotCols g (tensorColumns u v) := by
  funext k x
  simp only [tensorColumns, rotCols, rotateField, map_smul]
  rw [apply_coord g, Finset.sum_smul]
  simp_rw [smul_smul]

theorem rotCols_add (c₁ c₂ : Fin 3 → SpatialField) :
    rotCols g (addColumns c₁ c₂) = addColumns (rotCols g c₁) (rotCols g c₂) := by
  funext k x
  simp only [rotCols, addColumns, rotateField, Pi.add_apply, map_add, smul_add,
    Finset.sum_add_distrib]

theorem symTensorColumns_eq (u v : SpatialField) :
    symTensorColumns u v = addColumns (tensorColumns u v) (tensorColumns v u) := by
  funext k x
  simp only [symTensorColumns, addColumns, tensorColumns, Pi.add_apply]

theorem symTensorColumns_rot (u v : SpatialField) :
    symTensorColumns (rotateField g u) (rotateField g v) =
      rotCols g (symTensorColumns u v) := by
  rw [symTensorColumns_eq, symTensorColumns_eq, tensorColumns_rot, tensorColumns_rot,
    rotCols_add]

theorem tensorColumns_congr {u u' v v' : SpatialField} (hu : u =ᵐ[volume] u')
    (hv : v =ᵐ[volume] v') (j : Fin 3) :
    tensorColumns u v j =ᵐ[volume] tensorColumns u' v' j := by
  filter_upwards [hu, hv] with x h1 h2
  simp only [tensorColumns, h1, h2]

theorem symTensorColumns_congr {u u' v v' : SpatialField} (hu : u =ᵐ[volume] u')
    (hv : v =ᵐ[volume] v') (j : Fin 3) :
    symTensorColumns u v j =ᵐ[volume] symTensorColumns u' v' j := by
  filter_upwards [hu, hv] with x h1 h2
  simp only [symTensorColumns, h1, h2]

/-! ## Tests and the literal pairing -/

theorem isVectorTest_rot {φ : Space → Space} (hφ : IsVectorTest φ) :
    IsVectorTest (rotateField g φ) :=
  ⟨g.contDiff.comp (hφ.smooth.comp g.symm.contDiff),
    (hφ.compact.comp_homeomorph g.symm.toHomeomorph).comp_left (map_zero g)⟩

/-- `∂ⱼ(g·φ) = ∑ₖ gⱼₖ (g·∂ₖφ)`. -/
theorem testPartial_rot (φ : Space → Space) (j : Fin 3) :
    testPartial (rotateField g φ) j =
      fun x => ∑ k : Fin 3, rc g j k • rotateField g (testPartial φ k) x := by
  funext x
  have h1 : fderiv ℝ (fun y => g (φ (g.symm y))) x =
      (g.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        (fderiv ℝ (fun y => φ (g.symm y)) x) :=
    g.toContinuousLinearEquiv.comp_fderiv (𝕜 := ℝ) (f := fun y => φ (g.symm y)) (x := x)
  simp only [testPartial]
  show fderiv ℝ (fun y => g (φ (g.symm y))) x (coordinateVector j) =
    ∑ k : Fin 3, rc g j k • g (fderiv ℝ φ (g.symm x) (coordinateVector k))
  rw [h1, fderiv_comp_rot g.symm φ x]
  simp only [ContinuousLinearMap.comp_apply]
  have e : (g.symm.toContinuousLinearEquiv : Space →L[ℝ] Space) (coordinateVector j) =
      ∑ k : Fin 3, rc g j k • coordinateVector k := (sum_rc_smul g j).symm
  rw [e, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, map_smul]
  rfl

theorem rc_symm (j k : Fin 3) : rc g.symm j k = rc g k j := by
  simp only [rc]
  rw [← inner_coord_left, ← inner_coord_left,
    real_inner_comm (g.symm (coordinateVector k)) (coordinateVector j), inner_symm_left]

theorem toL2_sum_rot (c : Fin 3 → ℝ) (f : Fin 3 → SpatialField)
    (hf : ∀ j, MemLp (f j) 2 volume) :
    toL2 (fun x => ∑ j : Fin 3, c j • rotateField g (f j) x) =
      ∑ j : Fin 3, c j • rotL2 g (toL2 (f j)) := by
  apply toL2_of_ae_eq_coeFn
  filter_upwards [coeFn_finsetSum Finset.univ (fun j : Fin 3 => c j • rotL2 g (toL2 (f j))),
    ae_all_iff.mpr (fun j : Fin 3 => Lp.coeFn_smul (c j) (rotL2 g (toL2 (f j)))),
    ae_all_iff.mpr (fun j : Fin 3 => rotL2_ae g (toL2 (f j))),
    ae_all_iff.mpr (fun j : Fin 3 => rotateField_congr g (coeFn_toL2 (hf j)))]
    with x h1 h2 h3 h4
  rw [h1]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [h2 j, Pi.smul_apply, h3 j, h4 j]

theorem columnsL2_rotCols {col : Fin 3 → SpatialField} (h : ColumnsL2 col) :
    ColumnsL2 (rotCols g col) := fun k =>
  memLp_finsetSum Finset.univ (fun j _ => (memLp_rotateField g (h j)).const_smul (rc g k j))

/-- `⟨𝔓 div 𝕋, g⁻¹·φ⟩ = ⟨𝔓 div (g·𝕋), φ⟩` for the literal pairing. -/
theorem lerayDivPairing_rot {col : Fin 3 → SpatialField} (hcol : ColumnsL2 col)
    {φ : Space → Space} (hφ : IsVectorTest φ) :
    lerayDivPairing col (rotateField g.symm φ) = lerayDivPairing (rotCols g col) φ := by
  unfold lerayDivPairing
  congr 1
  have e1 : ∀ j, toL2 (testPartial (rotateField g.symm φ) j) =
      ∑ k : Fin 3, rc g.symm j k • rotL2 g.symm (toL2 (testPartial φ k)) := by
    intro j
    rw [testPartial_rot]
    exact toL2_sum_rot g.symm (fun k => rc g.symm j k) (fun k => testPartial φ k)
      (fun k => testPartial_memLp hφ k 2)
  have e2 : ∀ k, toL2 (rotCols g col k) = ∑ j : Fin 3, rc g k j • rotL2 g (toL2 (col j)) :=
    fun k => toL2_sum_rot g (fun j => rc g k j) col hcol
  simp_rw [e1, e2, map_sum, map_smul, projection_rotL2, inner_sum, sum_inner,
    real_inner_smul_right, real_inner_smul_left, inner_rotL2_right,
    LinearIsometryEquiv.symm_symm, rc_symm]
  rw [Finset.sum_comm]

/-- The weak `-𝔓 div` is `𝒪`-equivariant: `F = -𝔓 div 𝕋 ⇒ g·F = -𝔓 div (g·𝕋)`. -/
theorem IsMinusLerayDiv.rot {col : Fin 3 → SpatialField} {F : L2Space}
    (h : IsMinusLerayDiv col F) : IsMinusLerayDiv (rotCols g col) (rotL2 g F) := by
  refine ⟨columnsL2_rotCols g h.1, fun φ hφ => ?_⟩
  rw [inner_rotL2_left, rotL2_toL2 g.symm (vectorTest_memLp hφ 2),
    h.2 _ (isVectorTest_rot g.symm hφ), lerayDivPairing_rot g h.1 hφ]

end UnforcedLeray.Blueprint.L12
