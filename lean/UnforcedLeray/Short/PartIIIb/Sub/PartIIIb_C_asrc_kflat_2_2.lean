import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2

/-!
# `PartIII-b:C/asrc/kflat/2/2` : linearity of `xi_B` in `B`

Source of record: `the November 2 reference manuscript` (lines 4605-4610).
`g_B` is pointwise linear in `B` (`Bd`, `Be`, `Bbeta` are linear and `g_B(t)` is a linear
combination of `H`, `conjX H`, `R` with coefficients linear in `B(t)`), and `𝒰(s,t)` is `ℂ`-linear.
Hence the Duhamel integrands are additive (resp. homogeneous) on `Ioc 0 u`, and the integral and
the outer factor `s^{-μ}` respect this.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

theorem xiDLinear_Bd_add (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.PartIIIb.Bd (X + Y) =
      UnforcedLeray.Short.PartIIIb.Bd X + UnforcedLeray.Short.PartIIIb.Bd Y := by
  simp only [UnforcedLeray.Short.PartIIIb.Bd, Matrix.add_apply]
  ring

theorem xiDLinear_Be_add (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.PartIIIb.Be (X + Y) =
      UnforcedLeray.Short.PartIIIb.Be X + UnforcedLeray.Short.PartIIIb.Be Y := by
  simp only [UnforcedLeray.Short.PartIIIb.Be, Matrix.add_apply]
  ring

theorem xiDLinear_Bbeta_add (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta (X + Y) =
      UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta X +
        UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta Y := by
  simp only [UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta, Matrix.add_apply]
  ring

theorem xiDLinear_Bd_smul (r : ℝ) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.PartIIIb.Bd (r • X) = r * UnforcedLeray.Short.PartIIIb.Bd X := by
  simp only [UnforcedLeray.Short.PartIIIb.Bd, Matrix.smul_apply, smul_eq_mul]
  ring

theorem xiDLinear_Be_smul (r : ℝ) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.PartIIIb.Be (r • X) = r * UnforcedLeray.Short.PartIIIb.Be X := by
  simp only [UnforcedLeray.Short.PartIIIb.Be, Matrix.smul_apply, smul_eq_mul]
  ring

theorem xiDLinear_Bbeta_smul (r : ℝ) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta (r • X) =
      r * UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta X := by
  simp only [UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `g_B` is additive in `B` at a fixed age (source 4605-4608). -/
theorem xiDLinear_gBD_add {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] {tr : UnforcedLeray.B0140.TrainSol ν c}
    {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels}
    (FI : FlatInstData κ ν c m tr) (B B' B'' : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ)
    (h : B'' t = B t + B' t) :
    gBD FI B'' t = gBD FI B t + gBD FI B' t := by
  rw [gBD_apply, gBD_apply, gBD_apply, h, xiDLinear_Bd_add, xiDLinear_Be_add,
    xiDLinear_Bbeta_add]
  push_cast
  module

/-- `g_B` is real-homogeneous in `B` at a fixed age (source 4605-4608). -/
theorem xiDLinear_gBD_smul {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] {tr : UnforcedLeray.B0140.TrainSol ν c}
    {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels}
    (FI : FlatInstData κ ν c m tr) (B B'' : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t r : ℝ)
    (h : B'' t = r • B t) :
    gBD FI B'' t = (r : ℂ) • gBD FI B t := by
  rw [gBD_apply, gBD_apply, h, xiDLinear_Bd_smul, xiDLinear_Be_smul, xiDLinear_Bbeta_smul]
  push_cast
  module

/-- The Duhamel integrand is additive in `B` at ages `t > 0`. -/
theorem xiDLinear_duh_add {ν m : ℝ} [Fact (1 < m)] [Fact (0 < cOf ν)]
    {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels}
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (μ : ℝ) (B B' B'' : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (u t : ℝ) (h : B'' t = B t + B' t) :
    DuhIntegrand FI μ B'' u t = DuhIntegrand FI μ B u t + DuhIntegrand FI μ B' u t := by
  unfold DuhIntegrand
  rw [xiDLinear_gBD_add FI B B' B'' t h, map_add, smul_add]

/-- The Duhamel integrand is real-homogeneous in `B` at ages `t > 0`. -/
theorem xiDLinear_duh_smul {ν m : ℝ} [Fact (1 < m)] [Fact (0 < cOf ν)]
    {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels}
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (μ : ℝ) (B B'' : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (u t r : ℝ) (h : B'' t = r • B t) :
    DuhIntegrand FI μ B'' u t = (r : ℂ) • DuhIntegrand FI μ B u t := by
  unfold DuhIntegrand
  rw [xiDLinear_gBD_smul FI B B'' t r h, map_smul, smul_comm]

/-- **Linearity of `xi_B` in `B` (source 4605-4610).** -/
theorem xiDLinear (m : ℝ) [Fact (1 < m)] : XiDLinearProp m := by
  intro κ ν μ hν tr FI B B' B'' r u
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  intro hI hI'
  have hxi : ∀ X : ℝ → Matrix (Fin 3) (Fin 3) ℝ, xiD FI (μ : ℂ) X u =
      ((u : ℂ) ^ (-(μ : ℂ))) • ∫ t in Ioc 0 u, DuhIntegrand FI μ X u t :=
    fun X => rfl
  constructor
  · intro hB
    have hint : ∫ t in Ioc 0 u, DuhIntegrand FI μ B'' u t =
        (∫ t in Ioc 0 u, DuhIntegrand FI μ B u t) + (∫ t in Ioc 0 u, DuhIntegrand FI μ B' u t) := by
      rw [← integral_add hI hI']
      exact setIntegral_congr_fun measurableSet_Ioc
        (fun t ht => xiDLinear_duh_add FI μ B B' B'' u t (hB t ht.1))
    rw [hxi, hxi, hxi, hint, smul_add]
  · intro hB
    have hint : ∫ t in Ioc 0 u, DuhIntegrand FI μ B'' u t =
        (r : ℂ) • ∫ t in Ioc 0 u, DuhIntegrand FI μ B u t := by
      rw [← integral_smul]
      exact setIntegral_congr_fun measurableSet_Ioc
        (fun t ht => xiDLinear_duh_smul FI μ B B'' u t r (hB t ht.1))
    rw [hxi, hxi, hint, smul_comm]

end UnforcedLeray.Short.PartIIIb.Concrete
