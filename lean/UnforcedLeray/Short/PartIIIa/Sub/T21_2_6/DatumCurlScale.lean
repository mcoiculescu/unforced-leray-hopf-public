import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity

/-!
# Part III-a, `PartIII-a:T21/2/6/6`: the scaling of the periodized Gaussian vorticity

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2867
(`DatumCurlScale`), with `ψ^p = -2a⁻¹e^{-|x|²/(4a)}` (SP 290-296). With `r = √a > 0`, the
scaling identity `vcReg_Vc_scale` gives `V_c(z) = r⁻³ datum_{c/r}(r⁻¹ z)`, so the curl satisfies
`curl V_c(z) = r⁻⁴ (curl datum_{c/r})(r⁻¹ z)`; the `j`-th derivative of the dilation picks up
`r⁻ʲ`, and at `z = r y` one gets the factor `(a² r^j)⁻¹ = r⁻⁴ r⁻ʲ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Dilation of a real-valued field, sup bound for the `j`-th derivative:
`‖D^j [z ↦ K G(l z)](x)‖ ≤ |K| |l|^j ‖D^j G(l x)‖`. -/
theorem dcs_norm_iteratedFDeriv_scalar_comp_le {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (K l : ℝ) (j : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j (fun z => K * G (l • z)) x‖ ≤
      |K| * |l| ^ j * ‖iteratedFDeriv ℝ j G (l • x)‖ := by
  set L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := l • ContinuousLinearMap.id ℝ (ℝ × ℝ) with hL_def
  have hLx : ∀ y, L y = l • y := fun y => by simp [hL_def]
  have hfun : (fun z => K * G (l • z)) = K • (G ∘ L) := by
    funext z
    simp [hLx]
  have hjn : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hcomp : ContDiffAt ℝ j (G ∘ L) x :=
    ((hG.comp L.contDiff).of_le hjn).contDiffAt
  rw [hfun, iteratedFDeriv_const_smul_apply hcomp, L.iteratedFDeriv_comp_right hG x hjn,
    hLx, norm_smul, Real.norm_eq_abs]
  have hnL : ‖L‖ ≤ |l| :=
    L.opNorm_le_bound (abs_nonneg l) fun y => by
      rw [hLx, norm_smul, Real.norm_eq_abs]
  have hcomp_le := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j G (l • x)) (fun _ : Fin j => L)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp_le
  have hpow : ‖L‖ ^ j ≤ |l| ^ j := pow_le_pow_left₀ (norm_nonneg _) hnL j
  calc |K| * ‖(iteratedFDeriv ℝ j G (l • x)).compContinuousLinearMap fun _ => L‖
      ≤ |K| * (‖iteratedFDeriv ℝ j G (l • x)‖ * |l| ^ j) :=
        mul_le_mul_of_nonneg_left
          (hcomp_le.trans (mul_le_mul_of_nonneg_left hpow (norm_nonneg _))) (abs_nonneg K)
    _ = |K| * |l| ^ j * ‖iteratedFDeriv ℝ j G (l • x)‖ := by ring

/-- Curl of a dilated field: `curl [z ↦ K F(l z)](z) = K l (curl F)(l z)`. -/
theorem dcs_curl_smul_comp (F : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) (K l : ℝ) :
    UnforcedLeray.Cyl.curl (fun w => K • F (l • w)) =
      fun z => K * l * UnforcedLeray.Cyl.curl F (l • z) := by
  have hX := UnforcedLeray.B0147.partialX_scale K l (fun u => F u 1)
  have hY := UnforcedLeray.B0147.partialY_scale K l (fun u => F u 0)
  funext z
  unfold UnforcedLeray.Cyl.curl
  simp only [UnforcedLeray.Cyl.partialQ_eq_partialX, UnforcedLeray.Cyl.partialEta_eq_partialY]
  have hX' : UnforcedLeray.GaussianVortex.partialX (fun w => (K • F (l • w)) 1) =
      fun z => K * l * UnforcedLeray.GaussianVortex.partialX (fun u => F u 1)
        (l * z.1, l * z.2) := hX
  have hY' : UnforcedLeray.GaussianVortex.partialY (fun w => (K • F (l • w)) 0) =
      fun z => K * l * UnforcedLeray.GaussianVortex.partialY (fun u => F u 0)
        (l * z.1, l * z.2) := hY
  rw [hX', hY']
  have hz : l • z = (l * z.1, l * z.2) := rfl
  rw [hz]
  ring

/-- The curl of a `C^(⊤ : ℕ∞)` vector field is `C^(⊤ : ℕ∞)`. -/
theorem dcs_contDiff_curl {F : ℝ × ℝ → UnforcedLeray.Cyl.Vec2} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (UnforcedLeray.Cyl.curl F) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun w => F w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun w => F w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  unfold UnforcedLeray.Cyl.curl
  exact (UnforcedLeray.Cyl.contDiff_partialQ (h1.of_le (by simp))).sub
    (UnforcedLeray.Cyl.contDiff_partialEta (h0.of_le (by simp)))

/-- **Scaling of the periodized Gaussian vorticity** (SP 2866-2867, `V_c^p = a^{-3/2}·datum`,
`Spine.vcReg_Vc_scale`): `‖D^j curl V_c(s)(√a y)‖ ≤ (a² (√a)^j)⁻¹ ‖D^j curl datum_{c/√a}(y)‖`. -/
theorem datumCurlScale : DatumCurlScale := by
  unfold DatumCurlScale
  intro ν c s hν hc hs j y
  have ha_pos : 0 < clockA ν s := by
    have : 0 ≤ ν * s := mul_nonneg hν.le hs
    unfold clockA
    linarith
  have hr : 0 < Real.sqrt (clockA ν s) := Real.sqrt_pos.2 ha_pos
  have hA : clockA ν s = Real.sqrt (clockA ν s) ^ 2 := (Real.sq_sqrt ha_pos.le).symm
  have hr2 : Real.sqrt (clockA ν s) ^ 2 = UnforcedLeray.Train.width ν s := by
    rw [← hA]
    rfl
  have hVc : UnforcedLeray.Train.Vc ν c s =
      fun z => (Real.sqrt (clockA ν s))⁻¹ ^ 3 •
        UnforcedLeray.Train.datum (c / Real.sqrt (clockA ν s)) ((Real.sqrt (clockA ν s))⁻¹ • z) :=
    funext (UnforcedLeray.Short.Spine.vcReg_Vc_scale ν c s (Real.sqrt (clockA ν s)) hr2)
  have hcell : cellLen c (clockA ν s) = c / Real.sqrt (clockA ν s) := rfl
  rw [hcell, hVc, dcs_curl_smul_comp]
  generalize hr_def : Real.sqrt (clockA ν s) = r at *
  have hr0 : r ≠ 0 := hr.ne'
  rw [hA]
  have hG : ContDiff ℝ (⊤ : ℕ∞) (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum (c / r))) :=
    dcs_contDiff_curl (UnforcedLeray.Train.datum_contDiff (div_ne_zero hc.ne' hr0))
  have key := dcs_norm_iteratedFDeriv_scalar_comp_le hG (r⁻¹ ^ 3 * r⁻¹) (r⁻¹) j
    (r * y.1, r * y.2)
  have hlx : r⁻¹ • (r * y.1, r * y.2) = y := by
    ext
    · show r⁻¹ * (r * y.1) = y.1
      field_simp
    · show r⁻¹ * (r * y.2) = y.2
      field_simp
  rw [hlx] at key
  have hconst : |r⁻¹ ^ 3 * r⁻¹| * |r⁻¹| ^ j = ((r ^ 2) ^ 2 * r ^ j)⁻¹ := by
    rw [abs_of_pos (mul_pos (pow_pos (inv_pos.2 hr) 3) (inv_pos.2 hr)),
      abs_of_pos (inv_pos.2 hr)]
    ring
  calc _ ≤ _ := key
    _ = ((r ^ 2) ^ 2 * r ^ j)⁻¹ *
          ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl
            (UnforcedLeray.Train.datum (c / r))) y‖ := by
        rw [hconst]

end UnforcedLeray.Short.IIIa
