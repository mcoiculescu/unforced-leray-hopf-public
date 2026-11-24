import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLiftDefs
import UnforcedLeray.Lib.AxisymmetricB.Average

/-!
# The Cartesian lift of the chart tensor `U ⊗ w + w ⊗ U` (source 4147, 2683)

For an axisymmetric field `U` without swirl, `P`-periodic in `τ` (`P = 2c/R`), the physical lift
`cartLift` of the chart tensor `ten3Of (symOuter (chartCoeff R U p) (w p))` is `symProd U (𝒩_v w)`
at every `(τ, z)`. On the axis both sides vanish. Off the axis, `U(z)` is the rotation of
`U(ϱ, 0, z₃)` (`rotZ`), its swirl component vanishes by the reflection `reflY`, and the chart
coefficient reads `U` at the periodic phase `τ` (`chartOf_eq_ring`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hRad_eq_ϱ (z : Space) : NearInst.hRad z = ϱ z := rfl

theorem cl_nsSym_symOuter (a b : Merid) :
    NearInst.nsSym (NearInst.ten3Of (IIIa.symOuter a b)) = IIIa.symOuter a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NearInst.nsSym, NearInst.ten3Of, NearInst.symRZ, IIIa.symOuter, IIIa.embedMerid] <;>
    ring

theorem cartLiftSymOuter_proved (R c : ℝ) (U : ℝ → SpatialField) : CartLiftSymOuter R c U := by
  intro hR hc hax hper w τ z
  by_cases h0 : ϱ z = 0
  · -- the axis: both sides vanish
    have hage : age R z = 0 := by
      unfold age
      rw [h0]
      simp
    have hs : (NearInst.chartOf R c z τ).1 = 0 := by
      show R ^ 2 / NearInst.hRad z ^ 2 = 0
      have hh : NearInst.hRad z = ϱ z := rfl
      rw [hh, h0]
      simp
    have hN : Nv R (perExt c w) τ z = 0 := by
      unfold Nv
      rw [hage, Real.sqrt_zero, zero_smul]
    unfold NearInst.cartLift
    rw [hs, hN, zero_smul, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    simp [symProd]
  · -- off the axis
    have hpos : 0 < ϱ z := lt_of_le_of_ne (ϱ_nonneg z) (Ne.symm h0)
    have hϱne : ϱ z ≠ 0 := hpos.ne'
    have hRne : R ≠ 0 := hR.ne'
    have hchart := NearInst.chartOf_eq_ring R c hR hc z τ
    have hsq : Real.sqrt (age R z) = R / ϱ z := by
      have hA : age R z = (R / ϱ z) ^ 2 := by
        unfold age
        rw [div_pow]
      rw [hA]
      exact Real.sqrt_sq (div_nonneg hR.le hpos.le)
    have hfst : (NearInst.chartOf R c z τ).1 = age R z := by
      rw [hchart]
    -- the periodic phase
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊(phase R τ z + c / 2) / c⌋ := ⟨_, rfl⟩
    have hct : 2 * cellRep c (phase R τ z) / R + Real.log (age R z) =
        τ + ((-k : ℤ) : ℝ) * (2 * c / R) := by
      rw [cellRep, ← hk]
      unfold phase
      push_cast
      field_simp
      ring
    have hct' : 2 * (NearInst.chartOf R c z τ).2.1 / R + Real.log (NearInst.chartOf R c z τ).1 =
        τ + ((-k : ℤ) : ℝ) * (2 * c / R) := by
      rw [hchart]
      exact hct
    have hper_k : ∀ y : Space, U (τ + ((-k : ℤ) : ℝ) * (2 * c / R)) y = U τ y := by
      intro y
      have hp : Function.Periodic (fun t => U t y) (2 * c / R) := fun t => hper t y
      exact hp.int_mul (-k) τ
    -- the similarity point of the chart point is the axis point `(ϱ, 0, z₃)`
    have hY0 : (!₂[R / Real.sqrt (NearInst.chartOf R c z τ).1, 0,
        (NearInst.chartOf R c z τ).2.2 / Real.sqrt (NearInst.chartOf R c z τ).1] : Space) =
        !₂[ϱ z, 0, z 2] := by
      rw [hchart]
      dsimp only
      rw [hsq]
      ext i
      fin_cases i <;> simp [Axi.trans] <;> field_simp
    -- the chart coefficient
    have hcc : IIIa.chartCoeff R U (NearInst.chartOf R c z τ) =
        (R / ϱ z)⁻¹ • !₂[U τ !₂[ϱ z, 0, z 2] 0, U τ !₂[ϱ z, 0, z 2] 2] := by
      unfold IIIa.chartCoeff
      rw [hct', hY0, hper_k, hfst, hsq]
    -- the chart point of `Nv`
    have hp : perExt c w (UnforcedLeray.Axi.chart R τ z) = w (NearInst.chartOf R c z τ) := by
      rw [hchart]
      rfl
    have hNv : Nv R (perExt c w) τ z = (R / ϱ z) • frameL z (w (NearInst.chartOf R c z τ)) := by
      unfold Nv
      rw [hsq, hp]
    -- the axis reflection kills the swirl component at `(ϱ, 0, z₃)`
    have hV1 : U τ !₂[ϱ z, 0, z 2] 1 = 0 := by
      have h := hax τ reflY fixesAxis_reflY !₂[ϱ z, 0, z 2]
      have hsymm : reflY.symm !₂[ϱ z, 0, z 2] = !₂[ϱ z, 0, z 2] := by
        rw [LinearIsometryEquiv.symm_apply_eq]
        ext i
        fin_cases i <;> simp [reflY_apply, reflFun]
      rw [hsymm] at h
      have h1 := congrArg (fun v : Space => v 1) h
      simp [reflY_apply, reflFun] at h1
      linarith
    -- the rotation about the axis carrying `(ϱ, 0, z₃)` to `z`
    obtain ⟨w2, hw2⟩ : ∃ w2 : ℂ, w2 = ⟨z 0, z 1⟩ := ⟨_, rfl⟩
    have hre : w2.re = z 0 := by rw [hw2]
    have him : w2.im = z 1 := by rw [hw2]
    have hnorm : ‖w2‖ = ϱ z := by
      have h1 := Complex.norm_mul_cos_arg w2
      have h2 := Complex.norm_mul_sin_arg w2
      have e : (‖w2‖ * Real.cos (Complex.arg w2)) ^ 2 +
          (‖w2‖ * Real.sin (Complex.arg w2)) ^ 2 = ‖w2‖ ^ 2 := by
        linear_combination ‖w2‖ ^ 2 * Real.cos_sq_add_sin_sq (Complex.arg w2)
      rw [h1, h2, hre, him] at e
      have key : ‖w2‖ ^ 2 = ϱ z ^ 2 := by
        rw [ϱ_sq]
        linarith [e]
      exact (sq_eq_sq₀ (norm_nonneg _) (ϱ_nonneg z)).1 key
    have hcos : ϱ z * Real.cos (Complex.arg w2) = z 0 := by
      rw [← hnorm, Complex.norm_mul_cos_arg, hre]
    have hsin : ϱ z * Real.sin (Complex.arg w2) = z 1 := by
      rw [← hnorm, Complex.norm_mul_sin_arg, him]
    generalize Complex.arg w2 = θ at hcos hsin
    have hg : rotZ θ !₂[ϱ z, 0, z 2] = z := by
      ext i
      fin_cases i
      · simp [rotZ_apply, rotFun]
        linear_combination hcos
      · simp [rotZ_apply, rotFun]
        linear_combination hsin
      · simp [rotZ_apply, rotFun]
    have hinv : (rotZ θ).symm z = !₂[ϱ z, 0, z 2] := by
      conv_lhs => rw [← hg]
      exact (rotZ θ).symm_apply_apply _
    have hUz : U τ z = rotZ θ (U τ !₂[ϱ z, 0, z 2]) := by
      have h := hax τ (rotZ θ) (fixesAxis_rotZ θ) z
      rw [hinv] at h
      exact h.symm
    have hc' : Real.cos θ = z 0 / ϱ z := by
      field_simp
      linear_combination hcos
    have hs' : Real.sin θ = z 1 / ϱ z := by
      field_simp
      linear_combination hsin
    have hUz0 : U τ z 0 = z 0 / ϱ z * U τ !₂[ϱ z, 0, z 2] 0 := by
      rw [hUz]
      simp only [rotZ_apply, rotFun_apply_zero, hV1, hc']
      ring
    have hUz1 : U τ z 1 = z 1 / ϱ z * U τ !₂[ϱ z, 0, z 2] 0 := by
      rw [hUz]
      simp only [rotZ_apply, rotFun_apply_one, hV1, hs']
      ring
    have hUz2 : U τ z 2 = U τ !₂[ϱ z, 0, z 2] 2 := by
      rw [hUz]
      simp only [rotZ_apply, rotFun_apply_two]
    -- the Cartesian identity
    unfold NearInst.cartLift
    simp only [cl_nsSym_symOuter]
    rw [hfst, hcc, hNv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.add_apply, smul_eq_mul, Fin.isValue] <;>
      simp [NearInst.cylFrame, IIIa.symOuter, IIIa.embedMerid, symProd, frameL_apply, eR, hor,
        e3, hUz0, hUz1, hUz2, hRad_eq_ϱ, age] <;>
      field_simp <;> ring

end UnforcedLeray.Short.PartIIIb.Concrete
