import UnforcedLeray.Lib.Cylinder.Weight
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Weighted cell spaces `X c m`, circulation and the zero-circulation subspace (INF13, CY03)


§5 CY03; decisions D1 and D12 of `scoping/README.md` §3.

* `X c m = L²(cell c, ρw^m dq dη)` (smooth periodic weight, B0271, tex 4569-4578) and
  `Xc c m = L²(cell c, ρc^m dq dη)` (the centred weight of
  `X_c = L²(C_c, (1+q²+η²)^m dq dη)`, B0242, tex 4171-4184).  Both are complex `L²` spaces
  (`Lp ℂ 2`) of a density measure on the cell.
* The circulation `circ c f = ∫_cell f dq dη` is a continuous functional on `X c m` for
  `m > 1`, with norm bounded uniformly in the period (`norm_circCLM_le`), and
  `X0 c m = ker circ` is the zero-circulation subspace (B0285, tex 4653-4677; B0655,
  tex 13840-13866: "The full zero-circulation space").
* The unweighted pairing `∫_cell f g` of `X c m` and `X c (-m)` is bounded by the product of
  the norms (`norm_pairing_le`).
* The smooth and centred norms are uniformly equivalent (`eLpNorm_wμ_le_wμc`,
  `eLpNorm_wμc_le_wμ`, D12).

The weighted Cauchy-Schwarz identity `eLpNorm_withDensity_sq` is adapted from

there for real functions.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace UnforcedLeray.Cyl

/-! ### Weighted `L²` through a square root of the density -/

section General

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- `‖f‖_{L²(σ² μ)} = ‖σ f‖_{L²(μ)}` for every function (adapted from
`Units/B0656/Spaces.lean`, `IsSqrtDensity.eLpNorm_eq`). -/
theorem eLpNorm_withDensity_sq {σ : α → ℝ} (hσ : Measurable σ) (f : α → ℂ) :
    eLpNorm f 2 (μ.withDensity fun x => ENNReal.ofReal (σ x ^ 2)) =
      eLpNorm (fun x => (σ x : ℂ) * f x) 2 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable μ
    (f := fun x => ENNReal.ofReal (σ x ^ 2))
    (ENNReal.measurable_ofReal.comp (hσ.pow_const 2))
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  simp only [Pi.mul_apply, ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_mul]
  rw [mul_pow]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

end General

/-! ### The spaces -/

/-- The density `ρw^m` on the cell. -/
def wμ (c m : ℝ) : Measure Plane := (cellμ c).withDensity fun z => ENNReal.ofReal (ρw c z ^ m)

/-- The density `ρc^m` on the cell. -/
def wμc (c m : ℝ) : Measure Plane := (cellμ c).withDensity fun z => ENNReal.ofReal (ρc z ^ m)

/-- `X c m = L²(cell c, ρw^m dq dη; ℂ)` (smooth periodic weight, B0271). -/
abbrev X (c m : ℝ) := Lp ℂ 2 (wμ c m)

/-- `Xc c m = L²(cell c, (1+q²+η²)^m dq dη; ℂ)` (the manuscript's `X_c`, B0242). -/
abbrev Xc (c m : ℝ) := Lp ℂ 2 (wμc c m)

theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) (m : ℝ) : (x ^ (m / 2)) ^ 2 = x ^ m := by
  rw [← Real.rpow_mul_natCast hx]; norm_num

theorem wμ_eq_sq (c m : ℝ) :
    wμ c m = (cellμ c).withDensity fun z => ENNReal.ofReal ((ρw c z ^ (m / 2)) ^ 2) := by
  simp only [wμ, rpow_half_sq (ρw_pos c _).le]

theorem wμc_eq_sq (c m : ℝ) :
    wμc c m = (cellμ c).withDensity fun z => ENNReal.ofReal ((ρc z ^ (m / 2)) ^ 2) := by
  simp only [wμc, rpow_half_sq (ρc_pos _).le]

theorem measurable_rpow_ρw (c m : ℝ) : Measurable fun z => ρw c z ^ m :=
  (continuous_rpow_ρw c m).measurable

theorem measurable_rpow_ρc (m : ℝ) : Measurable fun z => ρc z ^ m :=
  (continuous_rpow_ρc m).measurable

/-- `‖f‖_{X c m} = ‖ρw^{m/2} f‖_{L²(cell)}`. -/
theorem eLpNorm_wμ_eq (c m : ℝ) (f : Plane → ℂ) :
    eLpNorm f 2 (wμ c m) = eLpNorm (fun z => ((ρw c z ^ (m / 2) : ℝ) : ℂ) * f z) 2 (cellμ c) := by
  rw [wμ_eq_sq]; exact eLpNorm_withDensity_sq _ (measurable_rpow_ρw c _) f

theorem eLpNorm_wμc_eq (c m : ℝ) (f : Plane → ℂ) :
    eLpNorm f 2 (wμc c m) = eLpNorm (fun z => ((ρc z ^ (m / 2) : ℝ) : ℂ) * f z) 2 (cellμ c) := by
  rw [wμc_eq_sq]; exact eLpNorm_withDensity_sq _ (measurable_rpow_ρc _) f

theorem cellμ_ac_wμ (c m : ℝ) : cellμ c ≪ wμ c m :=
  withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp
    (measurable_rpow_ρw c m)).aemeasurable
    (ae_of_all _ fun z => (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (ρw_pos c z) m)).ne')

theorem wμ_ac_cellμ (c m : ℝ) : wμ c m ≪ cellμ c := withDensity_absolutelyContinuous _ _

/-- The weighted measure and the cell measure have the same null sets. -/
theorem ae_wμ (c m : ℝ) : ae (wμ c m) = ae (cellμ c) :=
  le_antisymm (wμ_ac_cellμ c m).ae_le (cellμ_ac_wμ c m).ae_le

theorem cellμ_ac_wμc (c m : ℝ) : cellμ c ≪ wμc c m :=
  withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp
    (measurable_rpow_ρc m)).aemeasurable
    (ae_of_all _ fun z => (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (ρc_pos z) m)).ne')

theorem ae_wμc (c m : ℝ) : ae (wμc c m) = ae (cellμ c) :=
  le_antisymm (withDensity_absolutelyContinuous _ _).ae_le (cellμ_ac_wμc c m).ae_le

theorem aestronglyMeasurable_cell {c m : ℝ} (f : X c m) : AEStronglyMeasurable f (cellμ c) :=
  (Lp.aestronglyMeasurable f).mono_ac (cellμ_ac_wμ c m)

/-! ### Uniform equivalence of the smooth and centred norms (D12) -/

theorem wμ_le_wμc {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) : wμ c m ≤ wμc c m := by
  refine withDensity_mono ((ae_restrict_iff' (measurableSet_cell c)).2
    (ae_of_all _ fun z hz => ?_))
  exact ENNReal.ofReal_le_ofReal (rpow_ρw_comparable hc hm hz).2

theorem wμc_le_smul_wμ {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) :
    wμc c m ≤ ENNReal.ofReal ((4 / π ^ 2) ^ (-m)) • wμ c m := by
  rw [wμ, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_mono ((ae_restrict_iff' (measurableSet_cell c)).2
    (ae_of_all _ fun z hz => ?_))
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg four_div_pi_sq_pos.le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := (rpow_ρw_comparable hc hm hz).1
  have hpos : 0 < (4 / π ^ 2) ^ m := Real.rpow_pos_of_pos four_div_pi_sq_pos m
  rw [Real.rpow_neg four_div_pi_sq_pos.le]
  rw [← div_eq_inv_mul, le_div_iff₀ hpos]
  linarith

/-- The smooth weighted norm is at most the centred one (`m ≥ 0`). -/
theorem eLpNorm_wμ_le_wμc {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (f : Plane → ℂ) :
    eLpNorm f 2 (wμ c m) ≤ eLpNorm f 2 (wμc c m) :=
  eLpNorm_mono_measure f (wμ_le_wμc hc hm)

/-- The centred weighted norm is at most `(π²/4)^{m/2}` times the smooth one, uniformly in
the period (`m ≥ 0`). -/
theorem eLpNorm_wμc_le_wμ {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (f : Plane → ℂ) :
    eLpNorm f 2 (wμc c m) ≤
      ENNReal.ofReal ((4 / π ^ 2) ^ (-m)) ^ (1 / 2 : ℝ) * eLpNorm f 2 (wμ c m) := by
  calc eLpNorm f 2 (wμc c m) ≤ eLpNorm f 2 (ENNReal.ofReal ((4 / π ^ 2) ^ (-m)) • wμ c m) :=
        eLpNorm_mono_measure f (wμc_le_smul_wμ hc hm)
    _ = _ := by
        rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofNat_ne_top]
        simp

theorem memLp_wμ_iff_wμc {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) {f : Plane → ℂ} :
    MemLp f 2 (wμ c m) ↔ MemLp f 2 (wμc c m) := by
  constructor
  · intro hf
    refine ⟨hf.1.mono_ac ((withDensity_absolutelyContinuous _ _).trans (cellμ_ac_wμ c m)), ?_⟩
    exact (eLpNorm_wμc_le_wμ hc hm f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hf.2)
  · intro hf
    exact ⟨hf.1.mono_ac ((withDensity_absolutelyContinuous _ _).trans (cellμ_ac_wμc c m)),
      (eLpNorm_wμ_le_wμc hc hm f).trans_lt hf.2⟩

/-! ### Cell integrability and the circulation -/

theorem eLpNorm_rpow_neg_half_ρw_le {m : ℝ} (hm : 1 < m) :
    ∃ C, 0 ≤ C ∧ ∀ c > 0,
      eLpNorm (fun z => ((ρw c z ^ (-m / 2) : ℝ) : ℂ)) 2 (cellμ c) ≤ ENNReal.ofReal C := by
  obtain ⟨K, hK⟩ := setIntegral_rpow_neg_ρw_le hm
  refine ⟨Real.sqrt (max K 0), Real.sqrt_nonneg _, fun c hc => ?_⟩
  have hmeas : AEStronglyMeasurable (fun z => ((ρw c z ^ (-m / 2) : ℝ) : ℂ)) (cellμ c) :=
    (Complex.continuous_ofReal.comp (continuous_rpow_ρw c _)).aestronglyMeasurable
  have hsq : ∀ z, ‖((ρw c z ^ (-m / 2) : ℝ) : ℂ)‖ ^ (2 : ℝ) = ρw c z ^ (-m) := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (ρw_pos c z).le _),
      Real.rpow_two, rpow_half_sq (ρw_pos c z).le]
  have hmem : MemLp (fun z => ((ρw c z ^ (-m / 2) : ℝ) : ℂ)) 2 (cellμ c) := by
    refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
    have := integrableOn_rpow_neg_ρw hc hm
    refine this.congr_fun (fun z _ => ?_) (measurableSet_cell c)
    show ρw c z ^ (-m) = _
    rw [← hsq z, Real.rpow_two]
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofNat, hsq]
  rw [Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  exact Real.rpow_le_rpow (integral_nonneg fun z => Real.rpow_nonneg (ρw_pos c z).le _)
    ((hK c hc).trans (le_max_left _ _)) (by norm_num)

/-- **Weighted Cauchy-Schwarz on the cell.**  For `m > 1`,
`∫_cell |f| ≤ C ‖f‖_{X c m}` with `C` independent of the period (CY03). -/
theorem eLpNorm_one_cell_le {m : ℝ} (hm : 1 < m) :
    ∃ C, 0 ≤ C ∧ ∀ c > 0, ∀ f : Plane → ℂ, AEStronglyMeasurable f (cellμ c) →
      eLpNorm f 1 (cellμ c) ≤ ENNReal.ofReal C * eLpNorm f 2 (wμ c m) := by
  obtain ⟨C, hC0, hC⟩ := eLpNorm_rpow_neg_half_ρw_le hm
  refine ⟨C, hC0, fun c hc f hf => ?_⟩
  set ψ : Plane → ℂ := fun z => ((ρw c z ^ (-m / 2) : ℝ) : ℂ)
  set g : Plane → ℂ := fun z => ((ρw c z ^ (m / 2) : ℝ) : ℂ) * f z
  have hψ : AEStronglyMeasurable ψ (cellμ c) :=
    (Complex.continuous_ofReal.comp (continuous_rpow_ρw c _)).aestronglyMeasurable
  have hg : AEStronglyMeasurable g (cellμ c) :=
    (Complex.continuous_ofReal.comp (continuous_rpow_ρw c _)).aestronglyMeasurable.mul hf
  have hfg : f = ψ • g := by
    funext z
    show f z = ψ z * g z
    simp only [ψ, g]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (ρw_pos c z), neg_div,
      neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
  calc eLpNorm f 1 (cellμ c) = eLpNorm (ψ • g) 1 (cellμ c) := by rw [← hfg]
    _ ≤ eLpNorm ψ 2 (cellμ c) * eLpNorm g 2 (cellμ c) := eLpNorm_smul_le_mul_eLpNorm hg hψ
    _ ≤ ENNReal.ofReal C * eLpNorm f 2 (wμ c m) := by
        rw [eLpNorm_wμ_eq]
        exact mul_le_mul_left (hC c hc) _

theorem integrableOn_cell {c m : ℝ} (hc : 0 < c) (hm : 1 < m) (f : X c m) :
    IntegrableOn (f : Plane → ℂ) (cell c) := by
  obtain ⟨C, _, hC⟩ := eLpNorm_one_cell_le hm
  refine ⟨aestronglyMeasurable_cell f, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, ← eLpNorm_one_eq_lintegral_enorm]
  exact (hC c hc f (aestronglyMeasurable_cell f)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f))

/-- `∫_cell |f| ≤ C ‖f‖_{X c m}`, uniformly in the period (CY03 `eLpNorm_one_cell_le`). -/
theorem integral_norm_cell_le {m : ℝ} (hm : 1 < m) :
    ∃ C, 0 ≤ C ∧ ∀ c > 0, ∀ f : X c m, ∫ z in cell c, ‖f z‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC0, hC⟩ := eLpNorm_one_cell_le hm
  refine ⟨C, hC0, fun c hc f => ?_⟩
  have h := hC c hc f (aestronglyMeasurable_cell f)
  show ∫ z, ‖f z‖ ∂(cellμ c) ≤ C * ‖f‖
  rw [integral_norm_eq_lintegral_enorm (aestronglyMeasurable_cell f),
    ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def]
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (Lp.eLpNorm_lt_top f).ne) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0] at this

/-- The circulation `∫_cell f dq dη`. -/
def circ (c : ℝ) (f : Plane → ℂ) : ℂ := ∫ z in cell c, f z

/-- The circulation as a linear map on `X c m`, `m > 1`. -/
def circLM (c m : ℝ) (hm : 1 < m) (hc : 0 < c) : X c m →ₗ[ℂ] ℂ where
  toFun f := circ c f
  map_add' f g := by
    simp only [circ]
    rw [← integral_add (integrableOn_cell hc hm f) (integrableOn_cell hc hm g)]
    refine integral_congr_ae ?_
    have := Lp.coeFn_add f g
    rw [EventuallyEq, ae_wμ] at this
    exact this
  map_smul' a f := by
    simp only [circ, RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have := Lp.coeFn_smul a f
    rw [EventuallyEq, ae_wμ] at this
    filter_upwards [this] with z hz
    rw [hz]; rfl

/-- The circulation functional on `X c m`, `m > 1` (CY03). -/
def circCLM (c m : ℝ) (hm : 1 < m) (hc : 0 < c) : X c m →L[ℂ] ℂ :=
  (circLM c m hm hc).mkContinuous (integral_norm_cell_le hm).choose fun f => by
    have h := (integral_norm_cell_le hm).choose_spec.2 c hc f
    exact (norm_integral_le_integral_norm _).trans h

theorem circCLM_apply {c m : ℝ} (hm : 1 < m) (hc : 0 < c) (f : X c m) :
    circCLM c m hm hc f = ∫ z in cell c, f z := rfl

/-- The circulation functionals are bounded uniformly in the period (CY03). -/
theorem norm_circCLM_le {m : ℝ} (hm : 1 < m) :
    ∃ C, ∀ c (hc : 0 < c), ‖circCLM c m hm hc‖ ≤ C :=
  ⟨(integral_norm_cell_le hm).choose, fun _ _ =>
    LinearMap.mkContinuous_norm_le _ (integral_norm_cell_le hm).choose_spec.1 _⟩

/-- The zero-circulation subspace `X⁰ c m = {f ∈ X c m : ∫_cell f = 0}`, `m > 1`
(CY03; B0285, B0655). -/
def X0 (c m : ℝ) (hm : 1 < m) (hc : 0 < c) : Submodule ℂ (X c m) :=
  LinearMap.ker (circCLM c m hm hc).toLinearMap

theorem mem_X0 {c m : ℝ} (hm : 1 < m) (hc : 0 < c) (f : X c m) :
    f ∈ X0 c m hm hc ↔ ∫ z in cell c, f z = 0 := by
  rw [X0, LinearMap.mem_ker]; rfl

theorem isClosed_X0 {c m : ℝ} (hm : 1 < m) (hc : 0 < c) :
    IsClosed (X0 c m hm hc : Set (X c m)) :=
  (circCLM c m hm hc).isClosed_ker

/-! ### The unweighted pairing of `X c m` and `X c (-m)` -/

/-- `|∫_cell f g| ≤ ‖f‖_{X c m} ‖g‖_{X c (-m)}` (CY03, the unweighted pairing of B0656,
tex 13879-13887). -/
theorem norm_pairing_le {c m : ℝ} (f : X c m) (g : X c (-m)) :
    ‖∫ z in cell c, f z * g z‖ ≤ ‖f‖ * ‖g‖ := by
  set F : Plane → ℂ := fun z => ((ρw c z ^ (m / 2) : ℝ) : ℂ) * f z
  set G : Plane → ℂ := fun z => ((ρw c z ^ (-m / 2) : ℝ) : ℂ) * g z
  have hF : AEStronglyMeasurable F (cellμ c) :=
    (Complex.continuous_ofReal.comp (continuous_rpow_ρw c _)).aestronglyMeasurable.mul
      (aestronglyMeasurable_cell f)
  have hG : AEStronglyMeasurable G (cellμ c) :=
    (Complex.continuous_ofReal.comp (continuous_rpow_ρw c _)).aestronglyMeasurable.mul
      (aestronglyMeasurable_cell g)
  have hfg : (fun z => f z * g z) = F • G := by
    funext z
    show f z * g z = F z * G z
    simp only [F, G]
    have : ((ρw c z ^ (m / 2) : ℝ) : ℂ) * ((ρw c z ^ (-m / 2) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add (ρw_pos c z), neg_div, add_neg_cancel,
        Real.rpow_zero, Complex.ofReal_one]
    linear_combination (-(f z * g z)) * this
  have h1 : eLpNorm (fun z => f z * g z) 1 (cellμ c) ≤
      eLpNorm f 2 (wμ c m) * eLpNorm g 2 (wμ c (-m)) := by
    rw [hfg, eLpNorm_wμ_eq, eLpNorm_wμ_eq]
    exact eLpNorm_smul_le_mul_eLpNorm hG hF
  calc ‖∫ z in cell c, f z * g z‖ ≤ ∫ z in cell c, ‖f z * g z‖ :=
        norm_integral_le_integral_norm _
    _ = (eLpNorm (fun z => f z * g z) 1 (cellμ c)).toReal := by
        rw [integral_norm_eq_lintegral_enorm (hfg ▸ hF.smul hG), eLpNorm_one_eq_lintegral_enorm]
        rfl
    _ ≤ (eLpNorm f 2 (wμ c m) * eLpNorm g 2 (wμ c (-m))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_lt_top f).ne
          (Lp.eLpNorm_lt_top g).ne) h1
    _ = ‖f‖ * ‖g‖ := by rw [ENNReal.toReal_mul, Lp.norm_def, Lp.norm_def]

end UnforcedLeray.Cyl
