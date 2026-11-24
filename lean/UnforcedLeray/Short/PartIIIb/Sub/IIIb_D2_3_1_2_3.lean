import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2

/-!
# Decomposition of `wardX0Axi_all` (`PartIII-b:IIIb-D2/3/1/2/3`)

Source of record: `the November 2 reference manuscript`
lines 4171-4178 (rotation about the vertical axis; `K_t = δG_t + ∂∂∫_t^∞ G` depends only on `|x|`,
3600-3610; `cartLift` through `cylFrame` and `chartOf`, 2666-2683).

`WardX0Axi` follows from four equivariance statements for orthogonal matrices `M` acting on
`Space` by `actM`:

1. `KernelEquivariance`: `K_t(Mx) = M K_t(x) Mᵀ` (`heatLerayK`);
2. `SepWEquivariance`: for a tensor field with `T(Mz) = M T(z) Mᵀ`, `W(My) = M W(y)` (`sepW`);
3. `OldPhysRotEquiv`: `oldPhys` is equivariant for rotations about the vertical axis;
4. `OldPhysReflEquiv`: `oldPhys` is equivariant for the reflection `φ ↦ -φ`.

`wardX0Axi_of` (proved here) assembles them: the rotation carrying `meridPt y` to `y` gives
`wardX0 y = Rot (wardX0 (meridPt y))`, and the reflection fixing `meridPt y` kills the `e_φ`
component of `wardX0 (meridPt y)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The linear action of a real `3×3` matrix on `Space`. -/
def actM (M : Matrix (Fin 3) (Fin 3) ℝ) (x : Space) : Space :=
  WithLp.toLp 2 (M.mulVec (WithLp.ofLp x))

/-- The rotation about the vertical axis with cosine `co` and sine `si`. -/
def rotM (co si : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![co, -si, 0; si, co, 0; 0, 0, 1]

/-- The reflection `φ ↦ -φ` (`y₁ ↦ -y₁`). -/
def reflM : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- **Kernel equivariance** (3600-3610; `heatG`, `heatTail` depend only on `‖x‖`, the delta term
is invariant and `part2` transforms as a Hessian; for `M` orthogonal, `f ∘ M` is differentiable
at `x` iff `f` is at `Mx`, and when neither is, both sides vanish): for `M Mᵀ = 1`, every real
`t` and every `x`,
`K_t(Mx)_{ij} = ∑_{a,b} M_{ia} M_{jb} K_t(x)_{ab}`. -/
def KernelEquivariance : Prop :=
  ∀ (M : Matrix (Fin 3) (Fin 3) ℝ), M * M.transpose = 1 → ∀ (t : ℝ) (i j : Fin 3) (x : Space),
    IIIa.heatLerayK t i j (actM M x) =
      ∑ a : Fin 3, ∑ b : Fin 3, M i a * M j b * IIIa.heatLerayK t a b x

/-- **`sepW` equivariance** (4171-4178): for `M` orthogonal and a tensor field with
`T τ (Mz) = M (T τ z) Mᵀ`, `W_μ(My, τ) = M W_μ(y, τ)` (the complex-linear action of the real
matrix `M`), **provided the integrand of `sepW` at `y` is integrable** (`SepIntegrableAt`,
`Sub/IIIb-D2_3_1_1_2/Int.lean`): `sepW` is a componentwise Bochner integral, and a matrix mixing
components commutes with it only for integrable integrands (the junk value `0` of a non-integrable
component would be mixed with the integrals of the others).  Route: `KernelEquivariance`
(differentiated) gives the pointwise identity `Φ_i(l, Mz; My) = ∑_a M_ia Φ_a(l, z; y)`;
`sepW_eq_integral` writes `sepW` as one vector-valued integral over `sepRho` (Fubini); the
substitution `(l,z) ↦ (l, Mz)` is `sepRho`-measure preserving (`M` orthogonal), and the
`ContinuousLinearEquiv` of `M` on `Fin 3 → ℂ` commutes with the Bochner integral. -/
def SepWEquivariance : Prop :=
  ∀ (M : Matrix (Fin 3) (Fin 3) ℝ), M * M.transpose = 1 →
    ∀ (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
      (∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) →
      ∀ (y : Space) (τ : ℝ), SepIntegrableAt ν μ T y τ → IIIa.sepW ν μ T (actM M y) τ =
        fun i => ∑ a : Fin 3, ((M i a : ℝ) : ℂ) * IIIa.sepW ν μ T y τ a

/-- **Rotation equivariance of `oldPhys`** (2666-2683): `hRad`, `chartOf` are invariant under the
rotation, `cylFrame (Rz) = R cylFrame z` (also on the axis, where `s = 0`), `nsSym` untouched. -/
def OldPhysRotEquiv : Prop :=
  ∀ (co si : ℝ), co ^ 2 + si ^ 2 = 1 → ∀ (R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (z : Space),
    oldPhys R c g τ (actM (rotM co si) z) =
      rotM co si * oldPhys R c g τ z * (rotM co si).transpose

/-- **Reflection equivariance of `oldPhys`** (2666-2683): `cylFrame (Fz) = F cylFrame z F` and
`F nsSym F = nsSym` (the entries with one azimuthal index vanish). -/
def OldPhysReflEquiv : Prop :=
  ∀ (R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (z : Space),
    oldPhys R c g τ (actM reflM z) = reflM * oldPhys R c g τ z * reflM.transpose

theorem wardX0_equivariant (hS : SepWEquivariance) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M * M.transpose = 1) (ν μ R c : ℝ) (g : Chart → Ten3) (τ : ℝ)
    (hT : ∀ τ z, oldPhys R c g τ (actM M z) = M * oldPhys R c g τ z * M.transpose) (y : Space)
    (hI1 : SepIntegrableAt ν (μ : ℂ) (oldPhys R c g) y τ)
    (hI2 : SepIntegrableAt ν ((μ : ℂ) + 1) (oldPhys R c g) y τ) :
    wardX0 ν μ R c g τ (actM M y) = actM M (wardX0 ν μ R c g τ y) := by
  have h1 := hS M hM ν (μ : ℂ) (oldPhys R c g) hT y τ hI1
  have h2 := hS M hM ν ((μ : ℂ) + 1) (oldPhys R c g) hT y τ hI2
  unfold wardX0
  ext i
  simp only [h1, h2]
  simp only [actM, Matrix.mulVec, dotProduct, PiLp.toLp_apply, WithLp.ofLp_toLp]
  rw [← Finset.sum_sub_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_sub]

theorem rotM_orth {co si : ℝ} (h : co ^ 2 + si ^ 2 = 1) :
    rotM co si * (rotM co si).transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [h]

theorem reflM_orth : reflM * reflM.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflM, Matrix.mul_apply, Fin.sum_univ_three]

theorem wardX0Axi_of (hS : SepWEquivariance) (hR : OldPhysRotEquiv) (hF : OldPhysReflEquiv) :
    WardX0Axi := by
  intro ν μ R c g τ y hy hI1 hI2
  have hsq : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    by_contra h
    apply hy
    have h0 : y 0 ^ 2 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 ^ 2 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact ⟨pow_eq_zero_iff (two_ne_zero) |>.1 h0, pow_eq_zero_iff (two_ne_zero) |>.1 h1⟩
  have hρ : 0 < ϱ y := Real.sqrt_pos.2 hsq
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt hsq.le
  have hco : (y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 = 1 := by
    field_simp
    rw [hρ2]
  have hmer : actM (rotM (y 0 / ϱ y) (y 1 / ϱ y)) (meridPt y) = y := by
    ext i
    fin_cases i <;>
      simp [actM, rotM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      field_simp
  have hfix : actM reflM (meridPt y) = meridPt y := by
    ext i
    fin_cases i <;> simp [actM, reflM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have e1 := wardX0_equivariant hS _ (rotM_orth hco) ν μ R c g τ
    (hR _ _ hco R c g) (meridPt y) hI1 hI2
  have e2 := wardX0_equivariant hS _ reflM_orth ν μ R c g τ (hF R c g) (meridPt y) hI1 hI2
  rw [hmer] at e1
  rw [hfix] at e2
  have h1 : wardX0 ν μ R c g τ (meridPt y) 1 = 0 := by
    have := congrArg (fun w : Space => w 1) e2
    simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    linarith
  rw [e1]
  ext i
  fin_cases i <;>
    simp [actM, rotM, frameL_apply, eR, hor, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1] <;>
    field_simp

end UnforcedLeray.Short.PartIIIb.Concrete
