import UnforcedLeray.Lib.HeatR3.Anisotropic
import UnforcedLeray.Lib.HeatR3.Smooth

/-!
# The transverse `L¹` bound for the heat flow on `ℝ³ = ℝ × ℝ²` (INF04 T12)


item `norm_iteratedFDeriv_average_le_transverse`. Unit B0300 (tex 5335–5348,
`background:eq:2.29`): if every vertical line carries `∫_ℝ |a(x', z)| dz ≤ A`, then
"heat convolution gives `‖D^jH_a‖_∞ ≤ P_j ν^{-(j+1)/2} A`".

Splitting. `vsplit : ℝ³ ≃ᵐ ℝ × ℝ²`, `y ↦ (y₃, y_h)`, is volume preserving
(`measurePreserving_vsplit`: `ℝ³ ≅ ℝ^{Fin 3}` (`PiLp.volume_preserving`), the last coordinate
split off (`volume_preserving_piFinSuccAbove`), `ℝ^{Fin 2} ≅ ℝ²`). `mkPoint x' z` is the point
with horizontal part `x'` and height `z`.

Proof. `|D^jG_θ(w)| ≤ Cθ^{-(3+j)/2} e^{-|w|²/(8θ)} ≤ Cθ^{-(3+j)/2} e^{-|w_h|²/(8θ)}`, so by
Tonelli in `(z, y_h)`:
`|D^j e^{θΔ}a(x)| ≤ Cθ^{-(3+j)/2} ∫_{ℝ²} e^{-|x_h - y_h|²/(8θ)} (∫_ℝ |a(y_h, z)| dz) dy_h
  ≤ Cθ^{-(3+j)/2} · 8πθ · A`.
All integrals are lower Lebesgue integrals (no integrability side conditions).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Real
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-! ### The splitting `ℝ³ = ℝ × ℝ²` -/

/-- `ℝ³ ≃ᵐ ℝ × ℝ²`, `y ↦ (y₃, y_h)`. -/
def vsplit : Space ≃ᵐ ℝ × Euc 2 :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

theorem measurePreserving_vsplit : MeasurePreserving vsplit volume volume := by
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans ?_
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).trans ?_
  exact (MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))

theorem vsplit_apply (y : Space) : vsplit y = (y 2, horiz y) := by
  refine Prod.ext rfl ?_
  ext j
  fin_cases j <;> rfl

/-- The point of `ℝ³` with horizontal part `x'` and height `z`. -/
def mkPoint (x' : Euc 2) (z : ℝ) : Space := vsplit.symm (z, x')

theorem horiz_mkPoint (x' : Euc 2) (z : ℝ) : horiz (mkPoint x' z) = x' := by
  have h := vsplit.apply_symm_apply (z, x')
  rw [vsplit_apply] at h
  exact (Prod.ext_iff.mp h).2

theorem mkPoint_two (x' : Euc 2) (z : ℝ) : (mkPoint x' z) 2 = z := by
  have h := vsplit.apply_symm_apply (z, x')
  rw [vsplit_apply] at h
  exact (Prod.ext_iff.mp h).1

theorem horiz_sub (x y : Space) : horiz (x - y) = horiz x - horiz y := by
  ext j
  simp [horiz]

theorem norm_horiz_le (x : Space) : ‖horiz x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [norm_sq_eq_horiz]
  nlinarith [sq_nonneg (x 2)]

/-! ### The two-dimensional Gaussian mass -/

theorem lintegral_exp_horiz {θ : ℝ} (hθ : 0 < θ) (v : Euc 2) :
    ∫⁻ x' : Euc 2, ENNReal.ofReal (Real.exp (-‖v - x'‖ ^ 2 / (8 * θ))) =
      ENNReal.ofReal (8 * π * θ) := by
  have hb : 0 < 1 / (8 * θ) := by positivity
  have hfun : (fun x' : Euc 2 => Real.exp (-‖v - x'‖ ^ 2 / (8 * θ))) =
      fun x' => (fun w : Euc 2 => Real.exp (-(1 / (8 * θ)) * ‖w‖ ^ 2)) (v - x') := by
    funext x'; congr 1; ring
  have hint : Integrable (fun w : Euc 2 => Real.exp (-(1 / (8 * θ)) * ‖w‖ ^ 2)) :=
    Gaussian.integrable_exp_neg_mul_sq_norm hb
  rw [← ofReal_integral_eq_lintegral_ofReal (by rw [hfun]; exact hint.comp_sub_left v)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le), hfun,
    integral_sub_left_eq_self (fun w : Euc 2 => Real.exp (-(1 / (8 * θ)) * ‖w‖ ^ 2)) volume v,
    Gaussian.integral_exp_neg_mul_sq_norm hb]
  congr 1
  rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  field_simp

/-! ### The transverse bound -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **INF04 T12 `norm_iteratedFDeriv_average_le_transverse`** (B0300, tex 5335–5348). For every
`j` there is `C` such that for `θ > 0`, admissible `a : ℝ³ → E` whose vertical lines carry
`∫_ℝ |a(x', z)| dz ≤ A` (every horizontal `x'`), and every `x`:
`|D^j e^{θΔ}a(x)| ≤ C θ^{-(j+1)/2} A`. (Admissibility is implied by the transverse bound for
measurable `a`; it is kept as a hypothesis for the heat integral.) -/
theorem norm_iteratedFDeriv_average_le_transverse (j : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {θ : ℝ}, 0 < θ → ∀ {a : Space → E}, HeatAdmissible a → ∀ {A : ℝ}, 0 ≤ A →
      (∀ x' : Euc 2, ∫⁻ z : ℝ, ‖a (mkPoint x' z)‖ₑ ≤ ENNReal.ofReal A) → ∀ x : Space,
        ‖iteratedFDeriv ℝ j (average θ a) x‖ ≤ C * θ ^ (-((j : ℝ) + 1) / 2) * A := by
  obtain ⟨C₀, hC₀, hK⟩ := Gaussian.norm_iteratedFDeriv_gaussKernel_le 3 j
  refine ⟨8 * π * C₀, by positivity, fun {θ} hθ {a} ha {A} hA0 hA x => ?_⟩
  set c := C₀ * θ ^ (-((((3 : ℕ) : ℝ) + j) / 2)) with hc
  have hc0 : 0 ≤ c := by positivity
  -- the kernel bound with the horizontal Gaussian
  have hKh : ∀ y : Space, ‖iteratedFDeriv ℝ j (kernel θ) (x - y)‖ ≤
      c * Real.exp (-‖horiz x - horiz y‖ ^ 2 / (8 * θ)) := by
    intro y
    have h := hK hθ (x - y)
    rw [Gaussian.gaussKernel_three_eq] at h
    have hexp : Real.exp (-‖x - y‖ ^ 2 / (8 * θ)) ≤
        Real.exp (-‖horiz x - horiz y‖ ^ 2 / (8 * θ)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [← horiz_sub]
      exact norm_horiz_le _
    exact h.trans (mul_le_mul_of_nonneg_left hexp hc0)
  -- pass to the lower integral
  have hmeas : AEStronglyMeasurable (fun y : Space =>
      ‖iteratedFDeriv ℝ j (kernel θ) (x - y)‖ * ‖a y‖) volume := by
    have hcK : Continuous (iteratedFDeriv ℝ j (kernel θ)) :=
      (decayKernel_gaussKernel hθ le_rfl).smooth.continuous_iteratedFDeriv (by simp)
    exact ((hcK.comp (continuous_const.sub continuous_id)).norm.aestronglyMeasurable).mul
      ha.1.norm
  refine (norm_iteratedFDeriv_average_le_kernel ha hθ j x).trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => by positivity) hmeas]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  -- the lower integral, bounded through the splitting
  set G : Space → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp (-‖horiz x - horiz y‖ ^ 2 / (8 * θ))) * ‖a y‖ₑ with hG
  have hstep1 : ∫⁻ y : Space, ENNReal.ofReal (‖iteratedFDeriv ℝ j (kernel θ) (x - y)‖ * ‖a y‖) ≤
      ENNReal.ofReal c * ∫⁻ y : Space, G y := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm (a y), hG, ← mul_assoc,
      ← ENNReal.ofReal_mul hc0]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hKh y)) _
  have hGm : AEMeasurable G volume := by
    have h1 : Measurable fun y : Space =>
        ENNReal.ofReal (Real.exp (-‖horiz x - horiz y‖ ^ 2 / (8 * θ))) := by
      have : Continuous fun y : Space => horiz y := by
        unfold horiz; fun_prop
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
    exact h1.aemeasurable.mul ha.1.enorm
  have hsplit : ∫⁻ y : Space, G y = ∫⁻ x' : Euc 2, ∫⁻ z : ℝ, G (mkPoint x' z) := by
    have h1 := (measurePreserving_vsplit.symm).lintegral_comp_emb vsplit.symm.measurableEmbedding G
    rw [← h1]
    have h2 : AEMeasurable (fun p : ℝ × Euc 2 => G (vsplit.symm p)) (volume.prod volume) :=
      hGm.comp_quasiMeasurePreserving measurePreserving_vsplit.symm.quasiMeasurePreserving
    exact lintegral_prod_symm _ h2
  have hstep2 : ∫⁻ x' : Euc 2, ∫⁻ z : ℝ, G (mkPoint x' z) ≤
      ∫⁻ x' : Euc 2, ENNReal.ofReal (Real.exp (-‖horiz x - x'‖ ^ 2 / (8 * θ))) *
        ENNReal.ofReal A := by
    refine lintegral_mono fun x' => ?_
    simp only [hG, horiz_mkPoint]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    exact hA x'
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_exp_horiz hθ] at hstep2
  calc ∫⁻ y : Space, ENNReal.ofReal (‖iteratedFDeriv ℝ j (kernel θ) (x - y)‖ * ‖a y‖)
      ≤ ENNReal.ofReal c * (ENNReal.ofReal (8 * π * θ) * ENNReal.ofReal A) := by
        refine hstep1.trans ?_
        rw [hsplit]
        gcongr
    _ = ENNReal.ofReal (8 * π * C₀ * θ ^ (-((j : ℝ) + 1) / 2) * A) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc0]
        congr 1
        rw [hc]
        have hθe : θ ^ (-((((3 : ℕ) : ℝ) + j) / 2)) * θ = θ ^ (-((j : ℝ) + 1) / 2) := by
          rw [← Real.rpow_add_one hθ.ne']
          congr 1
          push_cast
          ring
        rw [← hθe]
        ring

end UnforcedLeray.Heat
