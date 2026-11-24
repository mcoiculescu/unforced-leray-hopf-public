import UnforcedLeray.Lib.Axisymmetric.Cylindrical

/-!
# AX01 (second order): the vector Laplacian of a meridional lift


§5 Layer 3, target AX01, item `vecLaplacian_liftMer`. Blueprint units served: B0222
(`eq:st18-t00115`, tex 3327–3339: "the radial minus-ε-squared term is the vector-basis
contribution `−r⁻²` in the cylindrical vector Laplacian"), B0483 (`eq:free-stress-B2`,
tex 7951–7968), B0187 (`eq:st18-t00190`, tex 2867–2888).

Off the axis, for a meridional profile `b = (b_r, b_z)` of class `C²` on `{ρ > 0}`,
`Δ(b_r e_r + b_z e_z) = (Δ_mer b_r − b_r/ρ²) e_r + (Δ_mer b_z) e_z` with
`Δ_mer = ∂_ρ² + ρ⁻¹∂_ρ + ∂_z²` (`vecLap_liftMer`). The Laplacian is the Cartesian
`∑ᵢ ∂ᵢ∂ᵢ` with iterated Fréchet derivatives, the convention of `Statement.spatialLaplacian`.

The computation goes through scalar lemmas: the cylindrical Laplacian of an axisymmetric
function (`lap_comp_mer`), `Δ(x_j/ϱ) = −(x_j/ϱ)/ϱ²` (`lap_gv`), and the product rule
(`lap_mul`). To keep every algebraic step a polynomial identity, all formulas are written with
`ι = ϱ⁻¹` and the relation `ι² (y₀² + y₁²) = 1` (`ιr_rel`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Axi

/-- Scalar Laplacian `Δg = ∑ᵢ ∂ᵢ∂ᵢ g`. -/
def lap (g : Space → ℝ) (y : Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ g x (coordinateVector i)) y (coordinateVector i)

/-- Vector Laplacian `Δf = ∑ᵢ ∂ᵢ∂ᵢ f` (the convention of `Statement.spatialLaplacian`). -/
def vecLap (f : Space → Space) (y : Space) : Space :=
  ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ f x (coordinateVector i)) y (coordinateVector i)

/-- Meridional scalar Laplacian `Δ_mer h = ∂_ρ²h + ρ⁻¹ ∂_ρ h + ∂_z² h`. -/
def lapMer (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := dρ (dρ h) p + dρ h p / p.1 + dz (dz h) p

/-- Profile of the vector Laplacian of a lift: `(Δ_mer b_r − b_r/ρ², Δ_mer b_z)`. -/
def vecLapMer (b : ℝ × ℝ → Merid) (p : ℝ × ℝ) : Merid :=
  !₂[lapMer (fun q => b q 0) p - b p 0 / p.1 ^ 2, lapMer (fun q => b q 1) p]

theorem vecLapMer_apply_zero (b : ℝ × ℝ → Merid) (p : ℝ × ℝ) :
    vecLapMer b p 0 = lapMer (fun q => b q 0) p - b p 0 / p.1 ^ 2 := rfl

theorem vecLapMer_apply_one (b : ℝ × ℝ → Merid) (p : ℝ × ℝ) :
    vecLapMer b p 1 = lapMer (fun q => b q 1) p := rfl

/-! ### Tools -/

theorem isOpen_halfPlane : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ

theorem mem_nhds_compl_axis {y : Space} (hy : y ∉ axis) : axisᶜ ∈ 𝓝 y :=
  isOpen_compl_axis.mem_nhds hy

theorem differentiableAt_of_contDiffOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f axisᶜ) (hn : n ≠ 0) {x : Space}
    (hx : x ∉ axis) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (mem_nhds_compl_axis hx)).differentiableAt hn

theorem differentiableAt_fderiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiffOn ℝ 2 f axisᶜ) {x : Space} (hx : x ∉ axis) (v : Space) :
    DifferentiableAt ℝ (fun x => fderiv ℝ f x v) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    (hf.contDiffAt (mem_nhds_compl_axis hx)).fderiv_right one_add_one_eq_two.le
  exact (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const v)

theorem differentiableAt_profile {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ × ℝ → F} {n : WithTop ℕ∞} (hh : ContDiffOn ℝ n h (Ioi 0 ×ˢ univ)) (hn : n ≠ 0)
    {x : Space} (hx : x ∉ axis) : DifferentiableAt ℝ h (mer x) :=
  (hh.contDiffAt (isOpen_halfPlane.mem_nhds (mapsTo_mer hx))).differentiableAt hn

theorem contDiffOn_dρ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ × ℝ → F}
    (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ)) : ContDiffOn ℝ 1 (dρ h) (Ioi 0 ×ˢ univ) :=
  (hh.fderiv_of_isOpen isOpen_halfPlane one_add_one_eq_two.le).clm_apply contDiffOn_const

theorem contDiffOn_dz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ × ℝ → F}
    (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ)) : ContDiffOn ℝ 1 (dz h) (Ioi 0 ×ˢ univ) :=
  (hh.fderiv_of_isOpen isOpen_halfPlane one_add_one_eq_two.le).clm_apply contDiffOn_const

/-- `D(h ∘ mer)(x) v = ⟪e_r, v⟫ ∂_ρ h + v₃ ∂_z h`. -/
theorem fderiv_comp_mer_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ × ℝ → F} {x : Space} (hx : x ∉ axis) (hh : DifferentiableAt ℝ h (mer x))
    (v : Space) :
    fderiv ℝ (fun y => h (mer y)) x v = ϱD x v • dρ h (mer x) + v 2 • dz h (mer x) := by
  have hc : HasFDerivAt (fun y => h (mer y)) ((fderiv ℝ h (mer x)).comp (merD x)) x :=
    hh.hasFDerivAt.comp x (hasFDerivAt_mer hx)
  rw [hc.fderiv, ContinuousLinearMap.comp_apply, merD_apply, clm_pair]
  rfl

/-! ### `ι = ϱ⁻¹` and the horizontal inner product -/

/-- `ι = ϱ⁻¹`. -/
def ιr (x : Space) : ℝ := (ϱ x)⁻¹

/-- The horizontal inner product `x ↦ v₀x₀ + v₁x₁` as a continuous linear functional. -/
def linH (v : Space) : Space →L[ℝ] ℝ :=
  v 0 • (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) +
    v 1 • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)

theorem linH_apply (v x : Space) : linH v x = v 0 * x 0 + v 1 * x 1 := by
  simp only [linH, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    EuclideanSpace.coe_proj, smul_eq_mul]

theorem ϱD_eq (x v : Space) : ϱD x v = linH v x * ιr x := by
  rw [ϱD_apply, linH_apply, ιr, div_eq_mul_inv]
  ring

theorem ιr_rel {y : Space} (hy : y ∉ axis) : ιr y ^ 2 * (y 0 ^ 2 + y 1 ^ 2) = 1 := by
  rw [ιr, ← ϱ_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (ϱ_ne_zero hy))]

theorem hasFDerivAt_ιr {y : Space} (hy : y ∉ axis) :
    HasFDerivAt ιr ((-(ιr y ^ 3)) • linH y) y := by
  have h : HasFDerivAt (fun x => (ϱ x)⁻¹) ((-(ϱ y ^ 2)⁻¹) • ϱD y) y :=
    (hasDerivAt_inv (ϱ_ne_zero hy)).comp_hasFDerivAt y (hasFDerivAt_ϱ hy)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ϱD_eq, ιr, linH_apply]
  ring

theorem contDiffOn_gv (v : Space) {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (fun x => linH v x * ιr x) axisᶜ :=
  (linH v).contDiff.contDiffOn.mul (contDiffOn_ϱ.inv fun _ hx => ϱ_ne_zero hx)

/-! ### Product rule -/

/-- `Δ(fg) = fΔg + gΔf + 2∇f·∇g` for `C²` functions off the axis. -/
theorem lap_mul {f g : Space → ℝ} (hf : ContDiffOn ℝ 2 f axisᶜ) (hg : ContDiffOn ℝ 2 g axisᶜ)
    {y : Space} (hy : y ∉ axis) :
    lap (fun x => f x * g x) y = f y * lap g y + g y * lap f y +
      2 * ∑ i : Fin 3, fderiv ℝ f y (coordinateVector i) * fderiv ℝ g y (coordinateVector i) := by
  have key : ∀ v : Space, fderiv ℝ (fun x => fderiv ℝ (fun x => f x * g x) x v) y v =
      f y * fderiv ℝ (fun x => fderiv ℝ g x v) y v + g y * fderiv ℝ (fun x => fderiv ℝ f x v) y v +
        2 * (fderiv ℝ f y v * fderiv ℝ g y v) := by
    intro v
    have hev : (fun x => fderiv ℝ (fun x => f x * g x) x v) =ᶠ[𝓝 y]
        (fun x => f x * fderiv ℝ g x v + g x * fderiv ℝ f x v) := by
      filter_upwards [mem_nhds_compl_axis hy] with x hx
      have hfx := (differentiableAt_of_contDiffOn hf two_ne_zero hx).hasFDerivAt
      have hgx := (differentiableAt_of_contDiffOn hg two_ne_zero hx).hasFDerivAt
      rw [(hfx.fun_mul hgx).fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring
    have hfy := (differentiableAt_of_contDiffOn hf two_ne_zero hy).hasFDerivAt
    have hgy := (differentiableAt_of_contDiffOn hg two_ne_zero hy).hasFDerivAt
    have hDf := (differentiableAt_fderiv_apply hf hy v).hasFDerivAt
    have hDg := (differentiableAt_fderiv_apply hg hy v).hasFDerivAt
    rw [hev.fderiv_eq, ((hfy.fun_mul hDg).fun_add (hgy.fun_mul hDf)).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  simp only [lap, Fin.sum_univ_three, key]
  ring

/-! ### The cylindrical Laplacian of an axisymmetric function -/

theorem fderiv_comp_mer_eq {h : ℝ × ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ)) {x : Space}
    (hx : x ∉ axis) (v : Space) :
    fderiv ℝ (fun y => h (mer y)) x v = linH v x * ιr x * dρ h (mer x) + v 2 * dz h (mer x) := by
  rw [fderiv_comp_mer_apply hx (differentiableAt_profile hh two_ne_zero hx), ϱD_eq, smul_eq_mul,
    smul_eq_mul]

theorem second_comp_mer {h : ℝ × ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ)) {y : Space}
    (hy : y ∉ axis) (v u : Space) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => h (mer y)) x v) y u =
      linH v u * ιr y * dρ h (mer y) + linH v y * (-(ιr y ^ 3) * linH y u) * dρ h (mer y) +
        linH v y * ιr y * (linH u y * ιr y * dρ (dρ h) (mer y) + u 2 * dz (dρ h) (mer y)) +
        v 2 * (linH u y * ιr y * dρ (dz h) (mer y) + u 2 * dz (dz h) (mer y)) := by
  have hev : (fun x => fderiv ℝ (fun y => h (mer y)) x v) =ᶠ[𝓝 y]
      (fun x => linH v x * ιr x * dρ h (mer x) + v 2 * dz h (mer x)) := by
    filter_upwards [mem_nhds_compl_axis hy] with x hx
    exact fderiv_comp_mer_eq hh hx v
  have hdρ : HasFDerivAt (fun x => dρ h (mer x)) ((fderiv ℝ (dρ h) (mer y)).comp (merD y)) y :=
    (differentiableAt_profile (contDiffOn_dρ hh) one_ne_zero hy).hasFDerivAt.comp y
      (hasFDerivAt_mer hy)
  have hdz : HasFDerivAt (fun x => dz h (mer x)) ((fderiv ℝ (dz h) (mer y)).comp (merD y)) y :=
    (differentiableAt_profile (contDiffOn_dz hh) one_ne_zero hy).hasFDerivAt.comp y
      (hasFDerivAt_mer hy)
  have hΦ := (((linH v).hasFDerivAt.fun_mul (hasFDerivAt_ιr hy)).fun_mul hdρ).fun_add
    (hdz.const_mul (v 2))
  rw [hev.fderiv_eq, hΦ.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, merD_apply, smul_eq_mul]
  rw [clm_pair (fderiv ℝ (dρ h) (mer y)), clm_pair (fderiv ℝ (dz h) (mer y))]
  simp only [smul_eq_mul, ϱD_eq]
  simp only [dρ, dz]
  ring

/-- **Cylindrical Laplacian of an axisymmetric function.** Off the axis,
`Δ(h(ϱ, y₃)) = (∂_ρ² h + ρ⁻¹∂_ρ h + ∂_z² h)(ϱ, y₃)` for `h` of class `C²` on `{ρ > 0}`. -/
theorem lap_comp_mer {h : ℝ × ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ)) {y : Space}
    (hy : y ∉ axis) : lap (fun x => h (mer x)) y = lapMer h (mer y) := by
  have hrel : (ϱ y)⁻¹ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) = 1 := ιr_rel hy
  simp only [lap, Fin.sum_univ_three, second_comp_mer hh hy]
  simp only [lapMer, linH_apply, coordinateVector_apply, Fin.isValue, Fin.reduceEq, ite_true,
    ite_false, ↓reduceIte, ιr, mer, div_eq_mul_inv]
  linear_combination (dρ (dρ h) (ϱ y, y 2) - (ϱ y)⁻¹ * dρ h (ϱ y, y 2)) * hrel

/-! ### `Δ(x_j/ϱ) = −(x_j/ϱ)/ϱ²` -/

theorem fderiv_gv_eq {x : Space} (hx : x ∉ axis) (v w : Space) :
    fderiv ℝ (fun x => linH v x * ιr x) x w =
      linH v x * (-(ιr x ^ 3) * linH x w) + ιr x * linH v w := by
  rw [((linH v).hasFDerivAt.fun_mul (hasFDerivAt_ιr hx)).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring

theorem second_gv {y : Space} (hy : y ∉ axis) (v w u : Space) :
    fderiv ℝ (fun x => fderiv ℝ (fun x => linH v x * ιr x) x w) y u =
      linH v u * (-(ιr y ^ 3) * linH w y) +
        linH v y * (3 * ιr y ^ 5 * linH y u * linH w y + -(ιr y ^ 3) * linH w u) +
        -(ιr y ^ 3) * linH y u * linH v w := by
  have hev : (fun x => fderiv ℝ (fun x => linH v x * ιr x) x w) =ᶠ[𝓝 y]
      (fun x => linH v x * (-(ιr x * ιr x * ιr x) * linH w x) + ιr x * linH v w) := by
    filter_upwards [mem_nhds_compl_axis hy] with x hx
    rw [fderiv_gv_eq hx]
    simp only [linH_apply]
    ring
  have hι := hasFDerivAt_ιr hy
  have hι3 := (hι.fun_mul hι).fun_mul hι
  have hΨ := ((linH v).hasFDerivAt.fun_mul (hι3.fun_neg.fun_mul (linH w).hasFDerivAt)).fun_add
    (hι.fun_mul (hasFDerivAt_const (linH v w) y))
  rw [hev.fderiv_eq, hΨ.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply, smul_eq_mul]
  ring

theorem lap_gv {y : Space} (hy : y ∉ axis) (v : Space) :
    lap (fun x => linH v x * ιr x) y = -(linH v y) * ιr y ^ 3 := by
  have hrel := ιr_rel hy
  simp only [lap, Fin.sum_univ_three, second_gv hy v]
  simp only [linH_apply, coordinateVector_apply, Fin.isValue, Fin.reduceEq, ite_true,
    ite_false, ↓reduceIte]
  linear_combination (3 * (v 0 * y 0 + v 1 * y 1) * ιr y ^ 3) * hrel

/-! ### Components and the vector Laplacian of a lift -/

theorem fderiv_coord_eq {f : Space → Space} (hf : ContDiffOn ℝ 2 f axisᶜ) {x : Space}
    (hx : x ∉ axis) (j : Fin 3) (w : Space) :
    fderiv ℝ (fun x => f x j) x w = fderiv ℝ f x w j := by
  have h : HasFDerivAt (fun x => f x j)
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ f x)) x :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
      (differentiableAt_of_contDiffOn hf two_ne_zero hx).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- Components of the vector Laplacian are scalar Laplacians of the components. -/
theorem vecLap_apply {f : Space → Space} (hf : ContDiffOn ℝ 2 f axisᶜ) {y : Space}
    (hy : y ∉ axis) (j : Fin 3) : vecLap f y j = lap (fun x => f x j) y := by
  have key : ∀ i : Fin 3,
      fderiv ℝ (fun x => fderiv ℝ (fun x => f x j) x (coordinateVector i)) y (coordinateVector i) =
        fderiv ℝ (fun x => fderiv ℝ f x (coordinateVector i)) y (coordinateVector i) j := by
    intro i
    have hev : (fun x => fderiv ℝ (fun x => f x j) x (coordinateVector i)) =ᶠ[𝓝 y]
        (fun x => fderiv ℝ f x (coordinateVector i) j) := by
      filter_upwards [mem_nhds_compl_axis hy] with x hx
      exact fderiv_coord_eq hf hx j _
    have hd := differentiableAt_fderiv_apply hf hy (coordinateVector i)
    have h : HasFDerivAt (fun x => fderiv ℝ f x (coordinateVector i) j)
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp
          (fderiv ℝ (fun x => fderiv ℝ f x (coordinateVector i)) y)) y :=
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp y hd.hasFDerivAt
    rw [hev.fderiv_eq, h.fderiv]
    rfl
  simp only [vecLap, lap, Fin.sum_univ_three, PiLp.add_apply, key]

/-- The gradient cross term of `Δ(b_r(ϱ, y₃) · x_j/ϱ)` vanishes. -/
theorem grad_cross_eq_zero {h : ℝ × ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Ioi 0 ×ˢ univ)) {y : Space}
    (hy : y ∉ axis) (v : Space) :
    ∑ i : Fin 3, fderiv ℝ (fun x => h (mer x)) y (coordinateVector i) *
      fderiv ℝ (fun x => linH v x * ιr x) y (coordinateVector i) = 0 := by
  have hrel := ιr_rel hy
  simp only [Fin.sum_univ_three, fderiv_comp_mer_eq hh hy, fderiv_gv_eq hy]
  simp only [linH_apply, coordinateVector_apply, Fin.isValue, Fin.reduceEq, ite_true,
    ite_false, ↓reduceIte]
  linear_combination (-(dρ h (mer y)) * (v 0 * y 0 + v 1 * y 1) * ιr y ^ 2) * hrel

/-- The horizontal components of a lift: `(liftMer b x)_j = b_r(ϱ, x₃) · x_j/ϱ`. -/
theorem liftMer_apply_horizontal (b : ℝ × ℝ → Merid) (x : Space) (j : Fin 3) (hj : j ≠ 2) :
    liftMer b x j = b (mer x) 0 * (linH (coordinateVector j) x * ιr x) := by
  fin_cases j
  · simp only [liftMer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, eR_apply_zero, e3_apply,
      linH_apply, coordinateVector_apply, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
      ↓reduceIte, ιr, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring
  · simp only [liftMer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, eR_apply_one, e3_apply,
      linH_apply, coordinateVector_apply, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
      ↓reduceIte, ιr, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring
  · exact absurd rfl hj

theorem liftMer_apply_two (b : ℝ × ℝ → Merid) (x : Space) : liftMer b x 2 = b (mer x) 1 := by
  simp only [liftMer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, eR_apply_two, e3_apply,
    ↓reduceIte] <;> ring

/-- **AX01 `vecLaplacian_liftMer`** (B0222, tex 3337–3339; B0483). Off the axis, for a profile
of class `C²` on `{ρ > 0}`, `Δ(b_r e_r + b_z e_z) = (Δ_mer b_r − b_r/ρ²) e_r + (Δ_mer b_z) e_z`,
with the Cartesian Laplacian `∑ᵢ ∂ᵢ∂ᵢ` and `Δ_mer = ∂_ρ² + ρ⁻¹∂_ρ + ∂_z²`. -/
theorem vecLap_liftMer {b : ℝ × ℝ → Merid} (hb : ContDiffOn ℝ 2 b (Ioi 0 ×ˢ univ)) {y : Space}
    (hy : y ∉ axis) : vecLap (liftMer b) y = liftMer (vecLapMer b) y := by
  have hB0 : ContDiffOn ℝ 2 (fun p => b p 0) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hb
  have hB1 : ContDiffOn ℝ 2 (fun p => b p 1) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hb
  have hB0m : ContDiffOn ℝ 2 (fun x => b (mer x) 0) axisᶜ :=
    hB0.comp contDiffOn_mer mapsTo_mer
  have hrel : (ϱ y)⁻¹ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) = 1 := ιr_rel hy
  ext j
  rw [vecLap_apply (contDiffOn_liftMer hb) hy j]
  fin_cases j
  · have e0 : (fun x => liftMer b x 0) =
        fun x => b (mer x) 0 * (linH (coordinateVector 0) x * ιr x) :=
      funext fun x => liftMer_apply_horizontal b x 0 (by decide)
    try simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
    rw [e0, lap_mul hB0m (contDiffOn_gv _) hy, lap_gv hy, lap_comp_mer hB0 hy,
      grad_cross_eq_zero hB0 hy (coordinateVector 0)]
    simp only [liftMer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vecLapMer_apply_zero,
      vecLapMer_apply_one, eR_apply_zero, e3_apply, linH_apply, coordinateVector_apply,
      Fin.isValue, Fin.reduceEq, ite_true, ite_false, ↓reduceIte, ιr, mer, div_eq_mul_inv]
    ring
  · have e1 : (fun x => liftMer b x 1) =
        fun x => b (mer x) 0 * (linH (coordinateVector 1) x * ιr x) :=
      funext fun x => liftMer_apply_horizontal b x 1 (by decide)
    try simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
    rw [e1, lap_mul hB0m (contDiffOn_gv _) hy, lap_gv hy, lap_comp_mer hB0 hy,
      grad_cross_eq_zero hB0 hy (coordinateVector 1)]
    simp only [liftMer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vecLapMer_apply_zero,
      vecLapMer_apply_one, eR_apply_one, e3_apply, linH_apply, coordinateVector_apply,
      Fin.isValue, Fin.reduceEq, ite_true, ite_false, ↓reduceIte, ιr, mer, div_eq_mul_inv]
    ring
  · have e2 : (fun x => liftMer b x 2) = fun x => b (mer x) 1 :=
      funext fun x => liftMer_apply_two b x
    try simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
    rw [e2, lap_comp_mer hB1 hy]
    simp only [liftMer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vecLapMer_apply_zero,
      vecLapMer_apply_one, eR_apply_two, e3_apply, ↓reduceIte]
    ring

/-! ### Agreement with the conventions of `Statement` -/

/-- `divergence` is `Statement.spatialDivergence` at a fixed time. -/
theorem spatialDivergence_eq_divergence (φ : SpaceTime → Space) (t : ℝ) (x : Space) :
    spatialDivergence φ t x = divergence (fun y => φ (t, y)) x := rfl

/-- `vecLap` is `Statement.spatialLaplacian` at a fixed time. -/
theorem spatialLaplacian_eq_vecLap (φ : SpaceTime → Space) (t : ℝ) (x : Space) :
    spatialLaplacian φ t x = vecLap (fun y => φ (t, y)) x := rfl

end UnforcedLeray.Axi
