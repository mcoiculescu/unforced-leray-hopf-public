import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Units.B0421.Phase

/-!
# Part II-a, task `PartII-a:F01`: the body resolvent `R_μ` (conditional on the sharp decay)

Source of record: `the November 2 reference manuscript`, lines 1363-1368
(`R_μ f(τ) = ∫₀^∞ e^{-μt} S(t) f(τ - t) dt`, with `‖R_μ‖ ≤ 1/a_r`, `a_r = Re μ + γ_r`; the
integrand has `Y_r`-norm at most `e^{-a_r t} ‖f‖`).

The bound `‖R_μ‖ ≤ (Re μ + γ_r)⁻¹` uses the semigroup bound with constant `1`:
`‖S_ν(t)‖_{L^r(ℝ³;ℂ³)} ≤ e^{-γ_r t}`. The library (`B0421.norm_freeC_le`) only has the constant `2`
for complex fields (complexification of a real operator), and `norm_freeC_two_le` has constant 1
only at `r = 2`. The constant 1 holds for every `1 ≤ p < ∞` because the heat kernel is a positive
kernel: `|S F(y)| ≤ S|F|(y)` pointwise, and `S` is bounded by `e^{-γ_p t}` on the real field
`(|F|, 0, 0)`. This is the Prop `FreeCSharpDecay`, reduced to two leaf Props (`NormLiftExists`, `FreeCPointwiseLe`;
tasks `PartII-a:F01/1`, `F01/2`) by `freeCSharpDecay_of`.

From `FreeCSharpDecay`, the resolvent is assembled here: with `a = Re μ + γ_r > 0`, the integrand
`t ↦ e^{-μ t} 𝒯_ν(t) f` is continuous on `[0, ∞)` (`B0421.continuousOn_phaseT`), bounded in norm by
`e^{-a t} ‖f‖` (`B0421.norm_phaseT_le` and the sharp decay), hence Bochner integrable on `(0, ∞)`
with `‖∫‖ ≤ a⁻¹ ‖f‖`; the integral is linear in `f`, and `LinearMap.mkContinuous` gives the CLM.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Sharp decay of the free similarity semigroup on complex fields** (the constant-1 form of
`eq:free-stress-8`, used at source lines 1363-1368): for every `1 ≤ p < ∞`, `ν ∈ ℝ` and `r ≥ 0`,
`‖S_ν(r)‖_{L^p(ℝ³;ℂ³) → L^p(ℝ³;ℂ³)} ≤ e^{-γ_p r}` with `γ_p = (3/p - 1)/2`. Proof idea: the heat
kernel is positive, so `|S F| ≤ S |F|` pointwise; apply the real bound to `(|F|, 0, 0)`. -/
def FreeCSharpDecay : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (ν r : ℝ), 0 ≤ r →
    ‖B0421.freeC hp ν r‖ ≤ Real.exp (-B0418.gammaExp p * r)

/-- **Norm lift** (task `PartII-a:F01/1`): for `F ∈ L^p(ℝ³; ℂ³)` there is a real field
`G = (‖F‖, 0, 0) ∈ L^p(ℝ³; ℝ³)` with the same `L^p` norm. -/
def NormLiftExists : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ⊤) (F : Lp CVec3 p (volume : Measure Space)),
    ∃ G : Lp Space p (volume : Measure Space),
      (G : Space → Space) =ᵐ[volume] (fun x => EuclideanSpace.single (0 : Fin 3) ‖F x‖) ∧
        ‖G‖ = ‖F‖

/-- **Positivity of the heat kernel** (task `PartII-a:F01/2`): for `F ∈ L^p(ℝ³; ℂ³)` and the real
field `G = (‖F‖, 0, 0)`, `|S_ν(r) F (y)| ≤ |S_ν(r) G (y)|` for a.e. `y`, because `S_ν(r)` is
`e^{r/2}` times a convolution with the positive Gaussian kernel (or the identity when
`ν(e^r - 1) ≤ 0`). -/
def FreeCPointwiseLe : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (ν r : ℝ) (F : Lp CVec3 p (volume : Measure Space))
    (G : Lp Space p (volume : Measure Space)),
    (G : Space → Space) =ᵐ[volume] (fun x => EuclideanSpace.single (0 : Fin 3) ‖F x‖) →
    ∀ᵐ y ∂(volume : Measure Space),
      ‖(B0421.freeC hp ν r F : Space → CVec3) y‖ ≤ ‖(B0418.freeSemigroupLp hp ν r G : Space → Space) y‖

/-- The sharp decay follows from the norm lift and the pointwise domination. -/
theorem freeCSharpDecay_of (h1 : NormLiftExists) (h2 : FreeCPointwiseLe) : FreeCSharpDecay := by
  intro p _ hp ν r _hr
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun F => ?_
  obtain ⟨G, hG, hGn⟩ := h1 p hp F
  have hae := h2 p hp ν r F G hG
  have hle : ‖B0421.freeC hp ν r F‖ ≤ ‖B0418.freeSemigroupLp hp ν r G‖ :=
    Lp.norm_le_norm_of_ae_le hae
  calc ‖B0421.freeC hp ν r F‖ ≤ ‖B0418.freeSemigroupLp hp ν r G‖ := hle
    _ ≤ ‖B0418.freeSemigroupLp hp ν r‖ * ‖G‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.exp (-B0418.gammaExp p * r) * ‖F‖ := by
        rw [hGn]
        exact mul_le_mul_of_nonneg_right (B0418.norm_freeSemigroupLp_le hp ν r) (norm_nonneg _)

/-- **`PartII-a:F01`, conditional on the sharp decay**: existence of the body resolvent
`R_μ : Y_r → Y_r` with `‖R_μ‖ ≤ (Re μ + γ_r)⁻¹` given by the Laplace integral of `𝒯_ν`. -/
theorem bodyResolvent_exists_of (hdec : FreeCSharpDecay)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h3 : r < 3) (P : ℝ) [Fact (0 < P)]
    (nu : ℝ) (hnu : 0 < nu) (mu : ℂ) (hmu : 0 < mu.re + gammaR r) :
    ∃ Rm : Yq P r →L[ℂ] Yq P r, ‖Rm‖ ≤ (mu.re + gammaR r)⁻¹ ∧
      ∀ f, Rm f = ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-(mu * t)) • B0421.phaseT (ne_top_of_lt h3) nu t f := by
  have hq : r ≠ ⊤ := ne_top_of_lt h3
  set a : ℝ := mu.re + gammaR r with ha
  have hnorm : ∀ t : ℝ, 0 ≤ t → ∀ f : Yq P r,
      ‖Complex.exp (-(mu * t)) • B0421.phaseT hq nu t f‖ ≤ Real.exp (-a * t) * ‖f‖ := by
    intro t ht f
    rw [norm_smul, Complex.norm_exp]
    have hre : (-(mu * (t : ℂ))).re = -(mu.re * t) := by simp
    rw [hre]
    have h2 : ‖B0421.phaseT hq nu t f‖ ≤ Real.exp (-B0418.gammaExp r * t) * ‖f‖ :=
      ((B0421.phaseT hq nu t).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right
          ((B0421.norm_phaseT_le hq nu t).trans (hdec r hq nu t ht)) (norm_nonneg _))
    calc Real.exp (-(mu.re * t)) * ‖B0421.phaseT hq nu t f‖
        ≤ Real.exp (-(mu.re * t)) * (Real.exp (-B0418.gammaExp r * t) * ‖f‖) := by gcongr
      _ = Real.exp (-a * t) * ‖f‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        simp only [ha, gammaR, B0418.gammaExp]
        ring
  have hint : ∀ f : Yq P r, IntegrableOn
      (fun t : ℝ => Complex.exp (-(mu * t)) • B0421.phaseT hq nu t f) (Ioi (0 : ℝ)) := by
    intro f
    have hcont : ContinuousOn (fun t : ℝ => Complex.exp (-(mu * t)) • B0421.phaseT hq nu t f)
        (Ioi (0 : ℝ)) := by
      have hc1 : Continuous fun t : ℝ => Complex.exp (-(mu * (t : ℂ))) := by fun_prop
      exact hc1.continuousOn.smul
        ((B0421.continuousOn_phaseT hq hnu.le f).mono Ioi_subset_Ici_self)
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine Integrable.mono' (hexp.mul_const ‖f‖) (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t ht => hnorm t (le_of_lt ht) f)
  let Φ : Yq P r →ₗ[ℂ] Yq P r :=
    { toFun := fun f => ∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-(mu * t)) • B0421.phaseT hq nu t f
      map_add' := fun f g => by
        simp only [map_add, smul_add]
        exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by
        have hcomm : ∀ t : ℝ, Complex.exp (-(mu * (t : ℂ))) • B0421.phaseT hq nu t (c • f) =
            c • (Complex.exp (-(mu * (t : ℂ))) • B0421.phaseT hq nu t f) := fun t => by
          rw [map_smul, smul_comm]
        simp only [RingHom.id_apply]
        simp_rw [hcomm]
        exact integral_smul c _ }
  have hapos : 0 < a := hmu
  have hbound : ∀ f : Yq P r, ‖Φ f‖ ≤ a⁻¹ * ‖f‖ := by
    intro f
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-a * t) * ‖f‖) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).mul_const ‖f‖
    have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun t : ℝ => Complex.exp (-(mu * t)) • B0421.phaseT hq nu t f) hexp
      ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun t ht => hnorm t (le_of_lt ht) f))
    have hI : ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * ‖f‖ = a⁻¹ * ‖f‖ := by
      rw [integral_mul_const, integral_exp_mul_Ioi (by linarith) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp
    exact (hI ▸ h : ‖Φ f‖ ≤ a⁻¹ * ‖f‖)
  refine ⟨LinearMap.mkContinuous Φ a⁻¹ hbound, ?_, fun f => rfl⟩
  exact LinearMap.mkContinuous_norm_le Φ (inv_nonneg.2 hapos.le) hbound

end UnforcedLeray.Short.PartIIa
