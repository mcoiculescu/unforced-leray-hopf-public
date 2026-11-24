import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2

/-!
# `PartII-b:T10/7/1/1/2/10` (`GLGradToEquivar`): equivariance of `radComb g` and `g 2`

Source of record: `the November 2 reference manuscript` lines 1912-1921.

Pointwise algebra.  For `T ∈ 𝒪` we have `T e₂ = e₂` (`glg_e2`), and `T` is an inner-product
isometry, so `∑_j (T y)_j (T e_k)_j = y_k` (`glg_ortho`).  Consequently `(T e_k)_2 = δ_{k2}`, and
`(T y)_2 = y_2`, `(T y)_0² + (T y)_1² = y_0² + y_1²`.  Substituting the transformation law of
`g` into `radComb g (τ, T y)` gives the coefficient of `cApp T (g_k x)` equal to `y_k/ϱ` for
`k < 2` and `0` for `k = 2`, i.e. `radComb g (τ, T y) = cApp T (radComb g x)`; and
`g 2 (τ, T y) = cApp T (g 2 x)`.  Finally `reS`, `imS` intertwine `cApp T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- An isometry `T` gives `∑_j (T y)_j (T e_k)_j = y_k`. -/
theorem glg_ortho (T : Space ≃ₗᵢ[ℝ] Space) (y : Space) (k : Fin 3) :
    ∑ j : Fin 3, T y j * T (UnforcedLeray.coordinateVector k) j = y k := by
  have h2 : ∑ j : Fin 3, T y j * T (UnforcedLeray.coordinateVector k) j =
      inner ℝ (T y) (T (UnforcedLeray.coordinateVector k)) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [h2, LinearIsometryEquiv.inner_map_map]
  simp [UnforcedLeray.coordinateVector, EuclideanSpace.inner_single_right]

/-- `T e₂ = e₂` for `T ∈ 𝒪`. -/
theorem glg_e2 {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) :
    T (UnforcedLeray.coordinateVector 2) = UnforcedLeray.coordinateVector 2 := by
  rcases hT with rfl | ⟨θ, rfl⟩
  · ext i
    fin_cases i <;> simp [UnforcedLeray.coordinateVector, UnforcedLeray.Axi.reflY_apply]
  · ext i
    fin_cases i <;> simp [UnforcedLeray.coordinateVector, UnforcedLeray.Axi.rotZ_apply]

theorem glg_fix2 {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) (y : Space) : T y 2 = y 2 := by
  have h := glg_ortho T y 2
  rw [glg_e2 hT] at h
  simpa [Fin.sum_univ_three, UnforcedLeray.coordinateVector, EuclideanSpace.single_apply] using h

theorem glg_horiz {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) (y : Space) :
    T y 0 ^ 2 + T y 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  have hn : ‖T y‖ ^ 2 = ‖y‖ ^ 2 := by rw [T.norm_map]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    Fin.sum_univ_three, glg_fix2 hT] at hn
  linarith

theorem glg_Te0_two {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) :
    T (UnforcedLeray.coordinateVector 0) 2 = 0 := by
  have h := glg_ortho T (UnforcedLeray.coordinateVector 2) 0
  rw [glg_e2 hT, Fin.sum_univ_three] at h
  simpa [UnforcedLeray.coordinateVector, EuclideanSpace.single_apply] using h

theorem glg_Te1_two {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) :
    T (UnforcedLeray.coordinateVector 1) 2 = 0 := by
  have h := glg_ortho T (UnforcedLeray.coordinateVector 2) 1
  rw [glg_e2 hT, Fin.sum_univ_three] at h
  simpa [UnforcedLeray.coordinateVector, EuclideanSpace.single_apply] using h

theorem glg_Te2_two {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) :
    T (UnforcedLeray.coordinateVector 2) 2 = 1 := by
  rw [glg_e2 hT]
  simp [UnforcedLeray.coordinateVector, EuclideanSpace.single_apply]

theorem glg_Te2_zero {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) :
    T (UnforcedLeray.coordinateVector 2) 0 = 0 := by
  rw [glg_e2 hT]
  simp [UnforcedLeray.coordinateVector, EuclideanSpace.single_apply]

theorem glg_Te2_one {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) :
    T (UnforcedLeray.coordinateVector 2) 1 = 0 := by
  rw [glg_e2 hT]
  simp [UnforcedLeray.coordinateVector, EuclideanSpace.single_apply]

/-- Coefficient identity for `k = 0`. -/
theorem glg_c0 {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) (y : Space) :
    (T y 0 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) * T (UnforcedLeray.coordinateVector 0) 0 +
      (T y 1 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) * T (UnforcedLeray.coordinateVector 0) 1 =
      y 0 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by
  have h := glg_ortho T y 0
  rw [Fin.sum_univ_three, glg_Te0_two hT, mul_zero, add_zero] at h
  calc _ = (T y 0 * T (UnforcedLeray.coordinateVector 0) 0 +
        T y 1 * T (UnforcedLeray.coordinateVector 0) 1) / Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by ring
    _ = y 0 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by rw [h]

/-- Coefficient identity for `k = 1`. -/
theorem glg_c1 {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) (y : Space) :
    (T y 0 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) * T (UnforcedLeray.coordinateVector 1) 0 +
      (T y 1 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) * T (UnforcedLeray.coordinateVector 1) 1 =
      y 1 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by
  have h := glg_ortho T y 1
  rw [Fin.sum_univ_three, glg_Te1_two hT, mul_zero, add_zero] at h
  calc _ = (T y 0 * T (UnforcedLeray.coordinateVector 1) 0 +
        T y 1 * T (UnforcedLeray.coordinateVector 1) 1) / Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by ring
    _ = y 1 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by rw [h]

/-- Coefficient identity for `k = 2`. -/
theorem glg_c2 {T : Space ≃ₗᵢ[ℝ] Space} (hT : GLIsO T) (y : Space) :
    (T y 0 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) * T (UnforcedLeray.coordinateVector 2) 0 +
      (T y 1 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) * T (UnforcedLeray.coordinateVector 2) 1 = 0 := by
  simp [glg_Te2_zero hT, glg_Te2_one hT]

/-! ### Complexification and `reS`, `imS` -/

theorem glg_realC_add (a b : Space) :
    B0412.realC (a + b) = B0412.realC a + B0412.realC b := by
  ext i
  simp [B0412.realC_apply]

theorem glg_realC_smul (r : ℝ) (w : Space) :
    B0412.realC (r • w) = ((r : ℝ) : ℂ) • B0412.realC w := by
  ext i
  simp [B0412.realC_apply]

theorem glg_reS_add (u v : CVec3) : reS (u + v) = reS u + reS v := by
  ext i
  simp [reS]

theorem glg_imS_add (u v : CVec3) : imS (u + v) = imS u + imS v := by
  ext i
  simp [imS]

theorem glg_reS_realC (w : Space) : reS (B0412.realC w) = w := by
  ext i
  simp [reS, B0412.realC_apply]

theorem glg_imS_realC (w : Space) : imS (B0412.realC w) = 0 := by
  ext i
  simp [imS, B0412.realC_apply]

theorem glg_reS_I_realC (w : Space) : reS (Complex.I • B0412.realC w) = 0 := by
  ext i
  simp [reS, B0412.realC_apply]

theorem glg_imS_I_realC (w : Space) : imS (Complex.I • B0412.realC w) = w := by
  ext i
  simp [imS, B0412.realC_apply]

theorem glg_reS_smul (r : ℝ) (v : CVec3) : reS (((r : ℝ) : ℂ) • v) = r • reS v := by
  ext i
  simp [reS]

theorem glg_imS_smul (r : ℝ) (v : CVec3) : imS (((r : ℝ) : ℂ) • v) = r • imS v := by
  ext i
  simp [imS]

theorem glg_reS_cApp (T : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : reS (cApp T v) = T (reS v) := by
  unfold cApp
  rw [glg_reS_add, glg_reS_realC, glg_reS_I_realC, add_zero]

theorem glg_imS_cApp (T : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : imS (cApp T v) = T (imS v) := by
  unfold cApp
  rw [glg_imS_add, glg_imS_realC, glg_imS_I_realC, zero_add]

theorem glg_cApp_add (T : Space ≃ₗᵢ[ℝ] Space) (u v : CVec3) :
    cApp T (u + v) = cApp T u + cApp T v := by
  unfold cApp
  simp only [glg_reS_add, glg_imS_add, map_add, glg_realC_add, smul_add]
  abel

theorem glg_cApp_smul (T : Space ≃ₗᵢ[ℝ] Space) (r : ℝ) (v : CVec3) :
    cApp T (((r : ℝ) : ℂ) • v) = ((r : ℝ) : ℂ) • cApp T v := by
  unfold cApp
  simp only [glg_reS_smul, glg_imS_smul, map_smul, glg_realC_smul]
  module

/-! ### The radial combination and `g 2` -/

theorem glg_radComb (T : Space ≃ₗᵢ[ℝ] Space) (hT : GLIsO T) (g : Fin 3 → ℝ × Space → CVec3)
    (x : ℝ × Space)
    (hx : ∀ j : Fin 3, g j (x.1, T x.2) =
      ∑ k : Fin 3, (((T (UnforcedLeray.coordinateVector k) j : ℝ) : ℂ)) • cApp T (g k x)) :
    radComb g (x.1, T x.2) = cApp T (radComb g x) := by
  have hϱ : Real.sqrt (T x.2 0 ^ 2 + T x.2 1 ^ 2) = Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) := by
    rw [glg_horiz hT]
  simp only [radComb]
  rw [hϱ, hx 0, hx 1, glg_cApp_add, glg_cApp_smul, glg_cApp_smul]
  simp only [Fin.sum_univ_three]
  have hc0 : ((T x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ) *
        ((T (UnforcedLeray.coordinateVector 0) 0 : ℝ) : ℂ) +
      ((T x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ) *
        ((T (UnforcedLeray.coordinateVector 0) 1 : ℝ) : ℂ) =
      ((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ) := by
    exact_mod_cast glg_c0 hT x.2
  have hc1 : ((T x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ) *
        ((T (UnforcedLeray.coordinateVector 1) 0 : ℝ) : ℂ) +
      ((T x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ) *
        ((T (UnforcedLeray.coordinateVector 1) 1 : ℝ) : ℂ) =
      ((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ) := by
    exact_mod_cast glg_c1 hT x.2
  have hc2 : ((T x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ) *
        ((T (UnforcedLeray.coordinateVector 2) 0 : ℝ) : ℂ) +
      ((T x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ) *
        ((T (UnforcedLeray.coordinateVector 2) 1 : ℝ) : ℂ) = 0 := by
    simp [glg_Te2_zero hT, glg_Te2_one hT]
  linear_combination (norm := module) hc0 • cApp T (g 0 x) + hc1 • cApp T (g 1 x) +
    hc2 • cApp T (g 2 x)

theorem glg_g2 (T : Space ≃ₗᵢ[ℝ] Space) (hT : GLIsO T) (g : Fin 3 → ℝ × Space → CVec3)
    (x : ℝ × Space)
    (hx : ∀ j : Fin 3, g j (x.1, T x.2) =
      ∑ k : Fin 3, (((T (UnforcedLeray.coordinateVector k) j : ℝ) : ℂ)) • cApp T (g k x)) :
    g 2 (x.1, T x.2) = cApp T (g 2 x) := by
  rw [hx 2, Fin.sum_univ_three, glg_Te2_two hT, glg_Te0_two hT, glg_Te1_two hT]
  simp

/-- **Equivariance of the radial combination and `g 2`** (SP 1912-1921, `GLGradToEquivar`). -/
theorem gl_gradToEquivar : UnforcedLeray.Short.IIb.GLGradToEquivar := by
  intro g T hT h P hP
  rcases hP with rfl | rfl
  · exact ⟨by
      filter_upwards [h] with x hx
      rw [glg_radComb T hT g x hx, glg_reS_cApp],
      by
      filter_upwards [h] with x hx
      rw [glg_g2 T hT g x hx, glg_reS_cApp]⟩
  · exact ⟨by
      filter_upwards [h] with x hx
      rw [glg_radComb T hT g x hx, glg_imS_cApp],
      by
      filter_upwards [h] with x hx
      rw [glg_g2 T hT g x hx, glg_imS_cApp]⟩

end UnforcedLeray.Short.IIb
