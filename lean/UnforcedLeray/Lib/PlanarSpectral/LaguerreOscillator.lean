import UnforcedLeray.Lib.PlanarSpectral.Laguerre

/-!
# The Laguerre basis is the image of the B0094 oscillator basis


bypass B6 (H1--H2, preparing H3). The compiled draft `Units/B0094` (unit B0094,
`eq:st18-t00068`, tex lines 1503--1515) built the Hilbert basis `oscBasis` of `X_G` as the
Gram--Schmidt orthonormalization of the profiles `r^{2+2k} e^{-r²/4}` and proved that it
diagonalizes `D` with eigenvalues `-ℓ` (`B0094.osc_eigen`, `B0094.Dcore_oscBasis`). Since
`xGToLaguerre` maps these profiles to positive multiples of the monomials `x^k`
(`xGToLaguerre_vmono`), and Gram--Schmidt commutes with isometries and with positive rescaling of
the input vectors, `xGToLaguerre (oscBasis n) = laguerreBasis n` (`xGToLaguerre_oscBasis`).
Thus the Laguerre basis carries the diagonal model `D e_ℓ = -ℓ e_ℓ` of B6.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter Polynomial InnerProductSpace
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate Real
namespace UnforcedLeray.PlanarSpectral

section GramSchmidt
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Gram--Schmidt commutes with a linear isometry and with positive rescaling of the inputs. -/
theorem gramSchmidt_smul_map (U : E →ₗᵢ[ℂ] F) (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (f : ℕ → E) (n : ℕ) :
    gramSchmidt ℂ (fun k => (c k : ℂ) • U (f k)) n = (c n : ℂ) • U (gramSchmidt ℂ f n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [gramSchmidt_def ℂ (fun k => (c k : ℂ) • U (f k)) n, gramSchmidt_def ℂ f n, map_sub,
      smul_sub, map_sum, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [ih i (Finset.mem_Iio.mp hi), Submodule.starProjection_singleton,
      Submodule.starProjection_singleton]
    set g := gramSchmidt ℂ f i
    simp only [inner_smul_left, inner_smul_right, LinearIsometry.inner_map_map, norm_smul,
      LinearIsometry.norm_map, map_smul, smul_smul, Complex.conj_ofReal, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hc i)]
    congr 1
    have h1 : (c i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hc i).ne'
    rcases eq_or_ne ‖g‖ 0 with hg | hg
    · simp [hg]
    · have h2 : (‖g‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
      simp only [RCLike.ofReal_eq_complex_ofReal] at *
      push_cast
      field_simp

/-- Normalized Gram--Schmidt commutes with a linear isometry and with positive rescaling. -/
theorem gramSchmidtNormed_smul_map (U : E →ₗᵢ[ℂ] F) (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (f : ℕ → E) (n : ℕ) :
    gramSchmidtNormed ℂ (fun k => (c k : ℂ) • U (f k)) n = U (gramSchmidtNormed ℂ f n) := by
  simp only [gramSchmidtNormed, gramSchmidt_smul_map U c hc f n, map_smul,
    norm_smul, LinearIsometry.norm_map, smul_smul]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc n)]
  rcases eq_or_ne ‖gramSchmidt ℂ f n‖ 0 with hg | hg
  · simp [hg]
  · have hcn : (c n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hc n).ne'
    have hgn : (‖gramSchmidt ℂ f n‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
    simp only [RCLike.ofReal_eq_complex_ofReal] at *
    push_cast
    field_simp

end GramSchmidt

/-- `xGToLaguerre (B0094.oscBasis n) = laguerreBasis n`: the Laguerre basis is the image of the
oscillator eigenbasis of B0094 (`eq:st18-t00068`, tex lines 1503--1515). -/
theorem xGToLaguerre_oscBasis (n : ℕ) : xGToLaguerre (B0094.oscBasis n) = laguerreBasis n := by
  rw [coe_laguerreBasis, B0094.coe_oscBasis]
  have h : laguerreMono = fun k => (((monoScale k)⁻¹ : ℝ) : ℂ) •
      xGToLaguerre.toLinearIsometry (B0094.vmono k) := by
    funext k
    rw [laguerreMono_eq, Complex.ofReal_inv]
    rfl
  rw [h, gramSchmidtNormed_smul_map xGToLaguerre.toLinearIsometry (fun k => (monoScale k)⁻¹)
    (fun k => inv_pos.mpr (monoScale_pos k)) B0094.vmono n]
  rfl

theorem laguerreBasis_eq_map (n : ℕ) :
    xGToLaguerre.symm (laguerreBasis n) = B0094.oscBasis n := by
  rw [← xGToLaguerre_oscBasis, LinearIsometryEquiv.symm_apply_apply]

/-- The transported basis `xGLaguerreBasis` is the B0094 oscillator basis. -/
theorem xGLaguerreBasis_eq_oscBasis (n : ℕ) : xGLaguerreBasis n = B0094.oscBasis n := by
  rw [xGLaguerreBasis_apply, laguerreBasis_eq_map]

end UnforcedLeray.PlanarSpectral
