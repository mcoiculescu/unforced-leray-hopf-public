import UnforcedLeray.Units.B0656.Weight
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# B0656, part 2: the weighted spaces `X_m` and the unweighted duality `X_m^* = X_{-m}`

Blueprint unit **B0656** (`unlabeled:13869`), `paper/main.tex` lines 13879–13887.

The cylinder `(ℝ/ℓℤ) × ℝ` is represented by the open centered cell
`(-ℓ/2, ℓ/2) × ℝ` with Lebesgue measure `dq dη`; the omitted seam is a null set. The space
`X_m = L²(ρ_ℓ^m dq dη)` is the real `L²` space of the measure with density `ρ_ℓ^m` on this cell.

The unweighted pairing `⟨f, g⟩ = ∫ f g dq dη` of `f ∈ X_m` and `g ∈ X_{-m}` is a genuine
Lebesgue integral (`integrable_mul_X`). The main result `dualX` is the linear isometric
equivalence `X_{-m} ≃ (X_m)^*`, `g ↦ (f ↦ ∫ f g dq dη)`: the Hilbert dual of `X_m` under the
unweighted pairing is `X_{-m}` (lines 13886–13887).

The proof first identifies `L²(w dμ)` with `L²(μ)` through multiplication by `√w`
(`mulL2Equiv`, for any measure and any positive measurable square root of the density), and
then applies the Riesz isomorphism `InnerProductSpace.toDual` on the unweighted cell `L²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.B0656

/-! ### Weighted `L²` through a square root of the density -/

section General

variable {α : Type*} [MeasurableSpace α]

/-- `σ` is a positive measurable square root of the density `w`. -/
structure IsSqrtDensity (w : α → ℝ≥0∞) (σ : α → ℝ) : Prop where
  measurable : Measurable σ
  pos : ∀ x, 0 < σ x
  eq : ∀ x, w x = ENNReal.ofReal (σ x ^ 2)

variable {w : α → ℝ≥0∞} {σ : α → ℝ}

theorem IsSqrtDensity.measurable_density (h : IsSqrtDensity w σ) : Measurable w := by
  have : w = fun x => ENNReal.ofReal (σ x ^ 2) := funext h.eq
  rw [this]
  exact ENNReal.measurable_ofReal.comp (h.measurable.pow_const 2)

theorem IsSqrtDensity.ne_zero (h : IsSqrtDensity w σ) (x : α) : w x ≠ 0 := by
  rw [h.eq x]
  exact (ENNReal.ofReal_pos.2 (pow_pos (h.pos x) 2)).ne'

theorem IsSqrtDensity.lt_top (h : IsSqrtDensity w σ) (x : α) : w x < ∞ := by
  rw [h.eq x]
  exact ENNReal.ofReal_lt_top

variable (μ : Measure α)

theorem IsSqrtDensity.absCont (h : IsSqrtDensity w σ) : μ ≪ μ.withDensity w :=
  withDensity_absolutelyContinuous' h.measurable_density.aemeasurable
    (ae_of_all _ h.ne_zero)

theorem IsSqrtDensity.absCont' : μ.withDensity w ≪ μ :=
  withDensity_absolutelyContinuous μ w

/-- The density measure and the base measure have the same null sets. -/
theorem IsSqrtDensity.ae_eq (h : IsSqrtDensity w σ) : ae (μ.withDensity w) = ae μ :=
  le_antisymm (IsSqrtDensity.absCont' μ).ae_le (h.absCont μ).ae_le

/-- `‖f‖_{L²(w μ)} = ‖√w f‖_{L²(μ)}` for every function, measurable or not. -/
theorem IsSqrtDensity.eLpNorm_eq (h : IsSqrtDensity w σ) (f : α → ℝ) :
    eLpNorm f 2 (μ.withDensity w) = eLpNorm (fun x => σ x * f x) 2 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable μ h.measurable_density
    (ae_of_all _ h.lt_top)]
  congr 1
  funext x
  simp only [Pi.mul_apply, ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_mul]
  rw [mul_pow, h.eq x]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem IsSqrtDensity.memLp_mul (h : IsSqrtDensity w σ) (f : Lp ℝ 2 (μ.withDensity w)) :
    MemLp (fun x => σ x * f x) 2 μ := by
  refine ⟨?_, ?_⟩
  · exact h.measurable.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).mono_ac (h.absCont μ))
  · rw [← h.eLpNorm_eq μ]
    exact Lp.eLpNorm_lt_top f

/-- Multiplication by `√w`, as a map of `L²` spaces. -/
def IsSqrtDensity.mulL2 (h : IsSqrtDensity w σ) :
    Lp ℝ 2 (μ.withDensity w) →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toFun f := (h.memLp_mul μ f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(h.memLp_mul μ (f + g)).coeFn_toLp,
      Lp.coeFn_add ((h.memLp_mul μ f).toLp _) ((h.memLp_mul μ g).toLp _),
      (h.memLp_mul μ f).coeFn_toLp, (h.memLp_mul μ g).coeFn_toLp,
      (h.absCont μ).ae_eq (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(h.memLp_mul μ (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((h.memLp_mul μ f).toLp _),
      (h.memLp_mul μ f).coeFn_toLp,
      (h.absCont μ).ae_eq (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  norm_map' f := by
    change ‖(h.memLp_mul μ f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def, h.eLpNorm_eq μ]

theorem IsSqrtDensity.coeFn_mulL2 (h : IsSqrtDensity w σ) (f : Lp ℝ 2 (μ.withDensity w)) :
    (h.mulL2 μ f : α → ℝ) =ᵐ[μ] fun x => σ x * f x :=
  (h.memLp_mul μ f).coeFn_toLp

theorem IsSqrtDensity.mulL2_surjective (h : IsSqrtDensity w σ) :
    Function.Surjective (h.mulL2 μ) := by
  intro g
  have hmem : MemLp (fun x => (σ x)⁻¹ * g x) 2 (μ.withDensity w) := by
    refine ⟨?_, ?_⟩
    · exact ((h.measurable.inv).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)).mono_ac
        (IsSqrtDensity.absCont' μ)
    · rw [h.eLpNorm_eq μ]
      have : (fun x => σ x * ((σ x)⁻¹ * g x)) = fun x => g x := by
        funext x
        rw [← mul_assoc, mul_inv_cancel₀ (h.pos x).ne', one_mul]
      rw [this]
      exact Lp.eLpNorm_lt_top g
  refine ⟨hmem.toLp _, ?_⟩
  apply Lp.ext
  filter_upwards [h.coeFn_mulL2 μ (hmem.toLp _), (h.absCont μ).ae_eq hmem.coeFn_toLp]
    with x h1 h2
  rw [h1, h2, ← mul_assoc, mul_inv_cancel₀ (h.pos x).ne', one_mul]

/-- The linear isometric equivalence `L²(w μ) ≃ L²(μ)`, `f ↦ √w f`. -/
def IsSqrtDensity.mulL2Equiv (h : IsSqrtDensity w σ) :
    Lp ℝ 2 (μ.withDensity w) ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (h.mulL2 μ) (h.mulL2_surjective μ)

theorem IsSqrtDensity.coeFn_mulL2Equiv (h : IsSqrtDensity w σ)
    (f : Lp ℝ 2 (μ.withDensity w)) :
    (h.mulL2Equiv μ f : α → ℝ) =ᵐ[μ] fun x => σ x * f x :=
  h.coeFn_mulL2 μ f

end General

/-! ### The cylinder cell and the spaces `X_m` -/

/-- The open centered cell `(-ℓ/2, ℓ/2) × ℝ`, a fundamental domain of the cylinder
`(ℝ/ℓℤ) × ℝ` up to the null seam `q = ±ℓ/2`. -/
def cell (ℓ : ℝ) : Set Plane := Ioo (-(ℓ / 2)) (ℓ / 2) ×ˢ univ

theorem measurableSet_cell (ℓ : ℝ) : MeasurableSet (cell ℓ) :=
  measurableSet_Ioo.prod MeasurableSet.univ

theorem isOpen_cell (ℓ : ℝ) : IsOpen (cell ℓ) :=
  isOpen_Ioo.prod isOpen_univ

/-- The unweighted measure `dq dη` on the cylinder, realized on one cell. -/
def cellMeasure (ℓ : ℝ) : Measure Plane := volume.restrict (cell ℓ)

/-- The density `ρ_ℓ^m`. -/
def weightDensity (ℓ m : ℝ) (z : Plane) : ℝ≥0∞ := ENNReal.ofReal (rho ℓ z ^ m)

/-- The weighted measure `ρ_ℓ^m dq dη` on the cylinder. -/
def weightMeasure (ℓ m : ℝ) : Measure Plane := (cellMeasure ℓ).withDensity (weightDensity ℓ m)

/-- `X_m = L²(ρ_ℓ^m dq dη)` (`paper/main.tex`, line 13882), real valued. Elements are
almost-everywhere classes of functions on the cylinder cell. -/
abbrev X (ℓ m : ℝ) := Lp ℝ 2 (weightMeasure ℓ m)

/-- The unweighted cylinder `L²` space, `X_0` up to the trivial density. -/
abbrev L2cell (ℓ : ℝ) := Lp ℝ 2 (cellMeasure ℓ)

/-- The square root `ρ_ℓ^{m/2}` of the density. -/
def sqrtWeight (ℓ m : ℝ) (z : Plane) : ℝ := rho ℓ z ^ (m / 2)

theorem continuous_rho (ℓ : ℝ) : Continuous (rho ℓ) := (contDiff_rho ℓ).continuous

theorem continuous_rho_rpow (ℓ s : ℝ) : Continuous fun z => rho ℓ z ^ s :=
  (continuous_rho ℓ).rpow_const fun z => Or.inl (rho_pos ℓ z).ne'

theorem sqrtWeight_pos (ℓ m : ℝ) (z : Plane) : 0 < sqrtWeight ℓ m z :=
  Real.rpow_pos_of_pos (rho_pos ℓ z) _

theorem sqrtWeight_mul_neg (ℓ m : ℝ) (z : Plane) :
    sqrtWeight ℓ m z * sqrtWeight ℓ (-m) z = 1 := by
  unfold sqrtWeight
  rw [← Real.rpow_add (rho_pos ℓ z), show m / 2 + -m / 2 = 0 by ring, Real.rpow_zero]

theorem isSqrtDensity_weight (ℓ m : ℝ) :
    IsSqrtDensity (weightDensity ℓ m) (sqrtWeight ℓ m) where
  measurable := (continuous_rho_rpow ℓ (m / 2)).measurable
  pos := sqrtWeight_pos ℓ m
  eq z := by
    unfold weightDensity sqrtWeight
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (rho_pos ℓ z).le]
    norm_num

/-- `ρ_ℓ^m dq dη` and `dq dη` have the same null sets on the cell: the weight is positive. -/
theorem ae_weightMeasure (ℓ m : ℝ) : ae (weightMeasure ℓ m) = ae (cellMeasure ℓ) :=
  (isSqrtDensity_weight ℓ m).ae_eq (cellMeasure ℓ)

/-- The isometry `X_m ≃ L²(dq dη)`, `f ↦ ρ_ℓ^{m/2} f`. -/
def toL2cell (ℓ m : ℝ) : X ℓ m ≃ₗᵢ[ℝ] L2cell ℓ :=
  (isSqrtDensity_weight ℓ m).mulL2Equiv (cellMeasure ℓ)

theorem coeFn_toL2cell (ℓ m : ℝ) (f : X ℓ m) :
    (toL2cell ℓ m f : Plane → ℝ) =ᵐ[cellMeasure ℓ] fun z => sqrtWeight ℓ m z * f z :=
  (isSqrtDensity_weight ℓ m).coeFn_mulL2Equiv (cellMeasure ℓ) f

/-! ### The unweighted pairing and the duality `X_m^* = X_{-m}` -/

/-- The unweighted pairing of `X_m` with `X_{-m}` is the inner product of the two
`L²(dq dη)` images. -/
theorem integral_mul_eq_inner (ℓ m : ℝ) (f : X ℓ m) (g : X ℓ (-m)) :
    ∫ z, f z * g z ∂(cellMeasure ℓ) = inner ℝ (toL2cell ℓ (-m) g) (toL2cell ℓ m f) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_toL2cell ℓ m f, coeFn_toL2cell ℓ (-m) g] with z h1 h2
  rw [Real.inner_apply, h1, h2]
  have := sqrtWeight_mul_neg ℓ m z
  calc f z * g z = (sqrtWeight ℓ m z * sqrtWeight ℓ (-m) z) * (f z * g z) := by
        rw [this, one_mul]
    _ = sqrtWeight ℓ (-m) z * g z * (sqrtWeight ℓ m z * f z) := by ring

/-- The unweighted pairing `∫ f g dq dη` of `f ∈ X_m` and `g ∈ X_{-m}` is a genuine
Lebesgue integral: the integrand is integrable (line 13886, "the distribution pairing is
unweighted"). -/
theorem integrable_mul_X (ℓ m : ℝ) (f : X ℓ m) (g : X ℓ (-m)) :
    Integrable (fun z => f z * g z) (cellMeasure ℓ) := by
  refine (MeasureTheory.L2.integrable_inner (toL2cell ℓ (-m) g) (toL2cell ℓ m f)).congr ?_
  filter_upwards [coeFn_toL2cell ℓ m f, coeFn_toL2cell ℓ (-m) g] with z h1 h2
  rw [Real.inner_apply, h1, h2]
  have := sqrtWeight_mul_neg ℓ m z
  calc sqrtWeight ℓ (-m) z * g z * (sqrtWeight ℓ m z * f z)
      = (sqrtWeight ℓ m z * sqrtWeight ℓ (-m) z) * (f z * g z) := by ring
    _ = f z * g z := by rw [this, one_mul]

/-- Cauchy–Schwarz for the unweighted pairing: `|∫ f g| ≤ ‖f‖_{X_m} ‖g‖_{X_{-m}}`. -/
theorem abs_integral_mul_le (ℓ m : ℝ) (f : X ℓ m) (g : X ℓ (-m)) :
    |∫ z, f z * g z ∂(cellMeasure ℓ)| ≤ ‖f‖ * ‖g‖ := by
  rw [integral_mul_eq_inner, ← Real.norm_eq_abs]
  refine (norm_inner_le_norm _ _).trans_eq ?_
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, mul_comm]

/-- The functional `f ↦ ∫ f g dq dη` on `X_m` defined by `g ∈ X_{-m}`. -/
def pairingCLM (ℓ m : ℝ) (g : X ℓ (-m)) : StrongDual ℝ (X ℓ m) :=
  (InnerProductSpace.toDual ℝ (L2cell ℓ) (toL2cell ℓ (-m) g)).comp
    (toL2cell ℓ m : X ℓ m →L[ℝ] L2cell ℓ)

theorem pairingCLM_apply (ℓ m : ℝ) (g : X ℓ (-m)) (f : X ℓ m) :
    pairingCLM ℓ m g f = ∫ z, f z * g z ∂(cellMeasure ℓ) := by
  rw [integral_mul_eq_inner]
  rfl

theorem norm_pairingCLM (ℓ m : ℝ) (g : X ℓ (-m)) : ‖pairingCLM ℓ m g‖ = ‖g‖ := by
  unfold pairingCLM
  rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]

/-- The pairing map `X_{-m} → (X_m)^*`, as a linear isometry. -/
def pairingIsometry (ℓ m : ℝ) : X ℓ (-m) →ₗᵢ[ℝ] StrongDual ℝ (X ℓ m) where
  toFun := pairingCLM ℓ m
  map_add' g h := by
    ext f
    simp [pairingCLM]
  map_smul' c g := by
    ext f
    simp [pairingCLM]
  norm_map' := norm_pairingCLM ℓ m

theorem pairingIsometry_surjective (ℓ m : ℝ) :
    Function.Surjective (pairingIsometry ℓ m) := by
  intro Λ
  set y : L2cell ℓ := (InnerProductSpace.toDual ℝ (L2cell ℓ)).symm
    (Λ.comp ((toL2cell ℓ m).symm : L2cell ℓ →L[ℝ] X ℓ m)) with hy
  refine ⟨(toL2cell ℓ (-m)).symm y, ?_⟩
  ext f
  change pairingCLM ℓ m ((toL2cell ℓ (-m)).symm y) f = Λ f
  simp only [pairingCLM, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.apply_symm_apply,
    InnerProductSpace.toDual_apply_apply]
  rw [hy, InnerProductSpace.toDual_symm_apply]
  simp

/-- **Duality** (`paper/main.tex`, lines 13886–13887: "The distribution pairing is unweighted.
Thus the literal full-space Hilbert dual of `X_m` is `X_{-m}`"). The map
`g ↦ (f ↦ ∫ f g dq dη)` is a linear isometric equivalence `X_{-m} ≃ (X_m)^*`. -/
def dualX (ℓ m : ℝ) : X ℓ (-m) ≃ₗᵢ[ℝ] StrongDual ℝ (X ℓ m) :=
  LinearIsometryEquiv.ofSurjective (pairingIsometry ℓ m) (pairingIsometry_surjective ℓ m)

/-- The duality is the literal unweighted integral pairing. -/
theorem dualX_apply (ℓ m : ℝ) (g : X ℓ (-m)) (f : X ℓ m) :
    dualX ℓ m g f = ∫ z, f z * g z ∂(cellMeasure ℓ) :=
  pairingCLM_apply ℓ m g f

end UnforcedLeray.B0656
