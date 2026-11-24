import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_22_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near.Q3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Split
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K2

/-!
# `PartIII-b:C/near/masked/22/2/4`: axisymmetry of `nearM` (source 4000-4003, 4171-4178)

Source of record: `the November 2 reference manuscript`, lines 4000-4003.

Route. Let `hRad z = hRad z'` and `z 2 = z' 2`. The truncation in `nearM` depends only on `hRad`, so
it suffices to compare `|sepW(z)|₂` and `|sepW(z')|₂` when `R/√r < hRad z`. A real rotation
`M = rotM co si` with `actM M z = z'` exists (`nearAx_exists_rot`). The integrand of `sepW` at `z`
is integrable (`sp_integrable`, since `rr = R/√(e^δ l) < R/√r < hRad z`), and the Cartesian lift is
covariant (`cartLiftRotCov_holds`), so `sepWEquivariance` gives `sepW(z') = M sepW(z)`. Finally a
real orthogonal `M` preserves the Euclidean norm on `ℂ³` (`nearAx_norm_rot`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- Two points with the same `hRad` and the same height differ by a vertical-axis rotation. -/
theorem nearAx_exists_rot (y y' : UnforcedLeray.Space) (hr : hRad y = hRad y') (hz : y 2 = y' 2) :
    ∃ co si : ℝ, co ^ 2 + si ^ 2 = 1 ∧ actM (rotM co si) y = y' := by
  have hsq : ∀ w : UnforcedLeray.Space, hRad w ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
    intro w
    unfold hRad
    exact Real.sq_sqrt (by positivity)
  have hE : y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [← hsq y', ← hsq y, hr]
  by_cases h0 : y 0 ^ 2 + y 1 ^ 2 = 0
  · have hy0 : y 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]) (sq_nonneg _))
    have hy1 : y 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]) (sq_nonneg _))
    have hy0' : y' 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm (by nlinarith [sq_nonneg (y' 0), sq_nonneg (y' 1)]) (sq_nonneg _))
    have hy1' : y' 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm (by nlinarith [sq_nonneg (y' 0), sq_nonneg (y' 1)]) (sq_nonneg _))
    refine ⟨1, 0, by norm_num, ?_⟩
    ext i
    fin_cases i <;> simp [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      hy0, hy1, hy0', hy1', hz]
  · obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (y 0 * y' 0 + y 1 * y' 1) / (y 0 ^ 2 + y 1 ^ 2) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (y 0 * y' 1 - y 1 * y' 0) / (y 0 ^ 2 + y 1 ^ 2) := ⟨_, rfl⟩
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      have hid : (y 0 * y' 0 + y 1 * y' 1) ^ 2 + (y 0 * y' 1 - y 1 * y' 0) ^ 2 =
          (y 0 ^ 2 + y 1 ^ 2) * (y' 0 ^ 2 + y' 1 ^ 2) := by ring
      rw [hc, hs, div_pow, div_pow, ← add_div, hid, hE]
      rw [div_eq_one_iff_eq (pow_ne_zero 2 h0)]
      ring
    have e0 : c * y 0 - s * y 1 = y' 0 := by
      rw [hc, hs]
      field_simp
      ring
    have e1 : s * y 0 + c * y 1 = y' 1 := by
      rw [hc, hs]
      field_simp
      ring
    refine ⟨c, s, hcs, ?_⟩
    ext i
    fin_cases i <;> simp [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hz] <;>
      linarith

/-- A real orthogonal rotation `rotM co si` preserves the Euclidean norm of `ℂ³`. -/
theorem nearAx_norm_rot (co si : ℝ) (hcs : co ^ 2 + si ^ 2 = 1) (w : Fin 3 → ℂ) :
    ‖(WithLp.toLp 2 (fun i : Fin 3 => ∑ a : Fin 3, ((rotM co si i a : ℝ) : ℂ) * w a) :
        EuclideanSpace ℂ (Fin 3))‖ = ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, rotM, Complex.sq_norm, Complex.normSq_apply, Complex.re_sum,
    Complex.mul_re, Complex.mul_im]
  linear_combination ((w 0).re * (w 0).re + (w 0).im * (w 0).im +
    ((w 1).re * (w 1).re + (w 1).im * (w 1).im)) * hcs

/-- **Leaf Q4** (`NearAxisym`, source 4000-4003, 4171-4178): `nearM` is axisymmetric. -/
theorem nearAxisym_holds : NearAxisym := by
  intro R c ν μ δ l r g hR hc hν hμ hδ hl hlr hrl hg hsupp τ z z' hr hz2
  have hr0 : 0 < r := hl.trans hlr
  have hlam0 : 0 < Real.exp δ * l := by positivity
  have hexp : Real.exp (δ / 2) < Real.exp δ := Real.exp_lt_exp.2 (by linarith)
  have hlt : r < Real.exp δ * l := by
    have : Real.exp (δ / 2) * l < Real.exp δ * l := mul_lt_mul_of_pos_right hexp hl
    linarith
  have hrr0 : 0 < R / Real.sqrt (Real.exp δ * l) := by positivity
  have hrrlt : R / Real.sqrt (Real.exp δ * l) < R / Real.sqrt r :=
    div_lt_div_of_pos_left hR (Real.sqrt_pos.2 hr0) (Real.sqrt_lt_sqrt hr0.le hlt)
  have hrel : R ^ 2 = (Real.exp δ * l) * (R / Real.sqrt (Real.exp δ * l)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hlam0.le]
    field_simp
  have hP : 0 < 2 * c / R := by positivity
  have hS : IIIa.IsSepSource (2 * c / R) (R / Real.sqrt (Real.exp δ * l))
      (NearInst.cartLift R c g) :=
    sp_isSepSource_cartLift R c hR hc (Real.exp δ * l) (R / Real.sqrt (Real.exp δ * l))
      hlam0 hrr0 hrel g hg hsupp
  have hMA : SepMoment (2 * c / R) (NearInst.cartLift R c g) := by
    obtain ⟨s1, s2, L, hs1, hband⟩ := hg.band
    obtain ⟨B, hB⟩ := hg.bounded
    exact sp_sepMoment_cart R c hR hc s1 s2 L B hs1 g hB hband
  unfold nearM
  by_cases h : R / Real.sqrt r < hRad z
  · have h' : R / Real.sqrt r < hRad z' := by rw [← hr]; exact h
    rw [if_pos h, if_pos h']
    have hy : R / Real.sqrt (Real.exp δ * l) < UnforcedLeray.Axi.ϱ z := lt_trans hrrlt h
    have hI : SepIntegrableAt ν (μ : ℂ) (NearInst.cartLift R c g) z τ :=
      fun i => sp_integrable ν μ hν hμ (2 * c / R) (R / Real.sqrt (Real.exp δ * l)) hP hrr0.le
        (NearInst.cartLift R c g) hS hMA τ z hy i
    obtain ⟨co, si, hcs, hM'⟩ := nearAx_exists_rot z z' hr hz2
    have hE := Concrete.sepWEquivariance (rotM co si) (rotM_orth hcs) ν (μ : ℂ)
      (NearInst.cartLift R c g) (cartLiftRotCov_holds co si hcs R c g) z τ hI
    rw [hM'] at hE
    unfold nearEN
    congr 1
    rw [hE]
    exact (nearAx_norm_rot co si hcs _).symm
  · have h' : ¬ R / Real.sqrt r < hRad z' := by rw [← hr]; exact h
    rw [if_neg h, if_neg h']

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
