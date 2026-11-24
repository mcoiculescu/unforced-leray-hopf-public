import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2

/-!
# Part III-a, task `PartIII-a:T19/2/2`: complex `H¹(cell c)` Biot-Savart reconstruction

Source of record: `the November 2 reference manuscript` (SP), lines 3497-3505
(Step P4: zero-circulation Biot-Savart `H¹` reconstruction on `X_{9,c}`).
Target: `theorem coreBiotSavartH1Uniform : UnforcedLeray.Short.IIIa.CoreBiotSavartH1Uniform`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace BiotSavartH1Aux

/-- Each coordinate of an `L²(cell; ℂ²)` element is measurable on `ℝ × ℝ`. -/
lemma measurable_lp_coord {c : ℝ} (F : Lp B0581.Vel 2 (B0581.cellVol c)) (i : Fin 2) :
    Measurable fun x : B0579.Plane => (F : B0579.Plane → B0581.Vel) x i :=
  (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) i).measurable.comp
    (Lp.stronglyMeasurable F).measurable

/-- Each coordinate of an `L²(cell; ℂ²)` element belongs to `MemLp · 2 (volume.restrict (cell c))`. -/
lemma memLp_lp_coord {c : ℝ} (F : Lp B0581.Vel 2 (B0581.cellVol c)) (i : Fin 2) :
    MemLp (fun x : B0579.Plane => (F : B0579.Plane → B0581.Vel) x i) 2
      (volume.restrict (B0579.cell c)) :=
  ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj i : B0581.Vel →L[ℂ] ℂ) (Lp.memLp F)

/-- `HasWeakVelDeriv c j U G` for real/complex `Lp` fields implies `HasWeakCellDerivC` on each
component `i : Fin 2`. -/
lemma hasWeakCellDerivC_of_velDeriv {c : ℝ} (j : Fin 2)
    (U G : Lp B0581.Vel 2 (B0581.cellVol c)) (h : B0583.HasWeakVelDeriv c j U G) (i : Fin 2) :
    HasWeakCellDerivC c j (fun x => (U : B0579.Plane → B0581.Vel) x i)
      (fun x => (G : B0579.Plane → B0581.Vel) x i) := by
  refine ⟨fun ψ hψ => ⟨CTE.T20_7.integrableOn_comp_test _ (memLp_lp_coord U) i (hψ.pd j),
    CTE.T20_7.integrableOn_comp_test _ (memLp_lp_coord G) i hψ⟩, fun ψ hψ => ?_⟩
  have hid := h ψ hψ i
  change ∫ x in B0579.cell c, (B0579.pd j ψ x : ℂ) * (U : B0579.Plane → B0581.Vel) x i =
      -∫ x in B0579.cell c, (ψ x : ℂ) * (G : B0579.Plane → B0581.Vel) x i at hid
  have hL : ∫ x in B0579.cell c, (U : B0579.Plane → B0581.Vel) x i * (B0579.pd j ψ x : ℂ) =
      ∫ x in B0579.cell c, (B0579.pd j ψ x : ℂ) * (U : B0579.Plane → B0581.Vel) x i :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hR : ∫ x in B0579.cell c, (G : B0579.Plane → B0581.Vel) x i * (ψ x : ℂ) =
      ∫ x in B0579.cell c, (ψ x : ℂ) * (G : B0579.Plane → B0581.Vel) x i :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hL, hR, hid]

/-- Complex linear combination of two `HasWeakCellDerivC` pairs `φ₁ + I * φ₂`, `g₁ + I * g₂`. -/
lemma hasWeakCellDerivC_add_I {c : ℝ} (j : Fin 2) {φ₁ φ₂ g₁ g₂ : ℝ × ℝ → ℂ}
    (h₁ : HasWeakCellDerivC c j φ₁ g₁) (h₂ : HasWeakCellDerivC c j φ₂ g₂) :
    HasWeakCellDerivC c j (fun x => φ₁ x + Complex.I * φ₂ x)
      (fun x => g₁ x + Complex.I * g₂ x) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨hφ₁, hg₁⟩ := h₁.1 ψ hψ
    obtain ⟨hφ₂, hg₂⟩ := h₂.1 ψ hψ
    refine ⟨?_, ?_⟩
    · refine (hφ₁.add (hφ₂.const_mul Complex.I)).congr_fun_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]
      ring
    · refine (hg₁.add (hg₂.const_mul Complex.I)).congr_fun_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]
      ring
  · obtain ⟨hφ₁, hg₁⟩ := h₁.1 ψ hψ
    obtain ⟨hφ₂, hg₂⟩ := h₂.1 ψ hψ
    have hsplit₁ : ∀ x, (φ₁ x + Complex.I * φ₂ x) * (B0579.pd j ψ x : ℂ) =
        φ₁ x * (B0579.pd j ψ x : ℂ) + Complex.I * (φ₂ x * (B0579.pd j ψ x : ℂ)) :=
      fun _ => by ring
    have hsplit₂ : ∀ x, (g₁ x + Complex.I * g₂ x) * (ψ x : ℂ) =
        g₁ x * (ψ x : ℂ) + Complex.I * (g₂ x * (ψ x : ℂ)) :=
      fun _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hsplit₁),
      integral_add hφ₁ (hφ₂.const_mul Complex.I), integral_const_mul,
      integral_congr_ae (Eventually.of_forall hsplit₂),
      integral_add hg₁ (hg₂.const_mul Complex.I), integral_const_mul,
      h₁.2 ψ hψ, h₂.2 ψ hψ]
    ring

/-- For a measurable vector field `v`, the cell integral of `vnorm2 (v x) ^ 2` equals
`velNorm c v ^ 2`. -/
lemma lintegral_vnorm2_sq_eq_velNorm_sq (c : ℝ) (v : ℝ × ℝ → Fin 2 → ℂ)
    (hv : ∀ i, Measurable fun x => v x i) :
    ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (v x) ^ 2) = (velNorm c v) ^ (2 : ℝ) := by
  have hsq : ∀ x, vnorm2 (v x) ^ 2 = ∑ i : Fin 2, ‖v x i‖ ^ 2 := fun x => by
    unfold vnorm2
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hpt : ∀ x, ENNReal.ofReal (vnorm2 (v x) ^ 2) =
      ∑ i : Fin 2, ENNReal.ofReal (‖v x i‖ ^ 2) := fun x => by
    rw [hsq x, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  simp_rw [hpt]
  rw [lintegral_finsetSum _ (fun i _ => ((hv i).norm.pow_const 2).ennreal_ofReal)]
  have hcomp : ∀ i : Fin 2,
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖v x i‖ ^ 2) =
        eLpNorm (fun x => v x i) 2 (volume.restrict (B0579.cell c)) ^ 2 := by
    intro i
    rw [← eLpNorm_two_sq_eq_lintegral_nonneg (volume.restrict (B0579.cell c))
      (fun x => ‖v x i‖) (fun _ => norm_nonneg _)]
    congr 1
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => norm_norm (v x i))
  simp_rw [hcomp]
  unfold velNorm
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

/-- Pointwise decomposition `tnorm2 (G x) ^ 2 = vnorm2 (G x · 0) ^ 2 + vnorm2 (G x · 1) ^ 2`. -/
lemma tnorm2_sq_eq_vnorm2_sq_add (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ^ 2 = vnorm2 (fun i => T i 0) ^ 2 + vnorm2 (fun i => T i 1) ^ 2 := by
  have hT : tnorm2 T ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
    unfold tnorm2
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h0 : vnorm2 (fun i => T i 0) ^ 2 = ∑ i : Fin 2, ‖T i 0‖ ^ 2 := by
    unfold vnorm2
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h1 : vnorm2 (fun i => T i 1) ^ 2 = ∑ i : Fin 2, ‖T i 1‖ ^ 2 := by
    unfold vnorm2
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hT, h0, h1, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two]
  ring

end BiotSavartH1Aux

open BiotSavartH1Aux

/-- **Leaf `PartIII-a:T19/2/2` (`CoreBiotSavartH1Uniform`, SP lines 3497-3505)**:
Complex `H¹(cell c)` Biot-Savart velocity and weak gradient reconstruction on `X_{9,c}` with
zero circulation for `c ≥ 1`, with constant `C_BS` independent of `c`. -/
theorem coreBiotSavartH1Uniform : UnforcedLeray.Short.IIIa.CoreBiotSavartH1Uniform := by
  obtain ⟨C1, hC1nn, hC1⟩ := CTE.nonzeroVelUniform 9 (by norm_num)
  set C0 : ℝ := C1 + 2
  have hC0nn : 0 ≤ C0 := by linarith
  refine ⟨2 * C0 + 6, by linarith, fun c hc1 f hf hz => ?_⟩
  have : Fact (0 < c) := ⟨by linarith⟩
  have hm1 : (1 : ℝ) ≤ 9 := by norm_num
  have hm1' : (1 : ℝ) < 9 := by norm_num
  obtain ⟨hint, hzero⟩ := hz
  have hre : MemLp (fun x => (f x).re) 2 (B0579.cellMeasure c 9) := hf.re
  have him : MemLp (fun x => (f x).im) 2 (B0579.cellMeasure c 9) := hf.im
  set ω₁ : B0579.X c 9 := hre.toLp _
  set ω₂ : B0579.X c 9 := him.toLp _
  have hω₁ : (ω₁ : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c 9] fun x => (f x).re :=
    MemLp.coeFn_toLp hre
  have hω₂ : (ω₂ : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c 9] fun x => (f x).im :=
    MemLp.coeFn_toLp him
  have ae₁ : (ω₁ : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell c)] fun x => (f x).re :=
    (B0579.ac_cellMeasure c 9).ae_le hω₁
  have ae₂ : (ω₂ : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell c)] fun x => (f x).im :=
    (B0579.ac_cellMeasure c 9).ae_le hω₂
  have hcirc₁ : ∫ x in B0579.cell c, ω₁ x = 0 := by
    rw [integral_congr_ae ae₁]
    have h := integral_re hint
    rw [hzero] at h
    simpa using h
  have hcirc₂ : ∫ x in B0579.cell c, ω₂ x = 0 := by
    rw [integral_congr_ae ae₂]
    have h := integral_im hint
    rw [hzero] at h
    simpa using h
  set U₁ := B0583.velocity c hm1 ω₁ hcirc₁
  set U₂ := B0583.velocity c hm1 ω₂ hcirc₂
  set GQ₁ := B0583.velGradQ c hm1 ω₁
  set GQ₂ := B0583.velGradQ c hm1 ω₂
  set GE₁ := B0583.velGradEta c hm1 ω₁ hcirc₁
  set GE₂ := B0583.velGradEta c hm1 ω₂ hcirc₂
  set u₁ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (U₁ : B0579.Plane → B0581.Vel) x i
  set u₂ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (U₂ : B0579.Plane → B0581.Vel) x i
  set gq₁ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (GQ₁ : B0579.Plane → B0581.Vel) x i
  set gq₂ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (GQ₂ : B0579.Plane → B0581.Vel) x i
  set ge₁ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (GE₁ : B0579.Plane → B0581.Vel) x i
  set ge₂ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (GE₂ : B0579.Plane → B0581.Vel) x i
  set u : ℝ × ℝ → Fin 2 → ℂ := fun x i => u₁ x i + Complex.I * u₂ x i
  set gq : ℝ × ℝ → Fin 2 → ℂ := fun x i => gq₁ x i + Complex.I * gq₂ x i
  set ge : ℝ × ℝ → Fin 2 → ℂ := fun x i => ge₁ x i + Complex.I * ge₂ x i
  set G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ := fun x i j => if j = 0 then gq x i else ge x i
  have hmu : ∀ i, Measurable fun x => u x i := fun i =>
    (measurable_lp_coord U₁ i).add ((measurable_lp_coord U₂ i).const_mul Complex.I)
  have hmgq : ∀ i, Measurable fun x => gq x i := fun i =>
    (measurable_lp_coord GQ₁ i).add ((measurable_lp_coord GQ₂ i).const_mul Complex.I)
  have hmge : ∀ i, Measurable fun x => ge x i := fun i =>
    (measurable_lp_coord GE₁ i).add ((measurable_lp_coord GE₂ i).const_mul Complex.I)
  have hmG : ∀ i j, Measurable fun x => G x i j := by
    intro i j
    fin_cases j
    · simpa [G] using hmgq i
    · simpa [G] using hmge i
  have hbs₁ : IsBiotSavart c (fun x => ((ω₁ x : ℝ) : ℂ)) u₁ :=
    CTE.velocityIsBiotSavart c 9 hm1' ω₁ hcirc₁
  have hbs₂ : IsBiotSavart c (fun x => ((ω₂ x : ℝ) : ℂ)) u₂ :=
    CTE.velocityIsBiotSavart c 9 hm1' ω₂ hcirc₂
  obtain ⟨hm₁, hdiv₁, hcurl₁⟩ := hbs₁
  obtain ⟨hm₂, hdiv₂, hcurl₂⟩ := hbs₂
  have hn₁ : ‖ω₁‖ ≤ (xNorm c 9 f).toReal :=
    CTE.T20_7.norm_le_xNorm hf (fun x => by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm (f x)) ω₁ hω₁
  have hn₂ : ‖ω₂‖ ≤ (xNorm c 9 f).toReal :=
    CTE.T20_7.norm_le_xNorm hf (fun x => by
      rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm (f x)) ω₂ hω₂
  have hfin : xNorm c 9 f ≠ ⊤ := hf.2.ne
  have hU_norm : ∀ (ω : B0579.X c 9) (hc : ∫ x in B0579.cell c, ω x = 0),
      ‖B0583.velocity c hm1 ω hc‖ ≤ C0 * ‖ω‖ := by
    intro ω hc
    have hsplit : B0583.velocity c hm1 ω hc =
        B0581.velNe c (B0581.nonzeroPart c (B0581.ofX c 9 (by norm_num) ω)) +
          B0583.zeroVelLp c hm1 ω hc := rfl
    calc ‖B0583.velocity c hm1 ω hc‖
        ≤ ‖B0581.velNe c (B0581.nonzeroPart c (B0581.ofX c 9 (by norm_num) ω))‖ +
            ‖B0583.zeroVelLp c hm1 ω hc‖ := by rw [hsplit]; exact norm_add_le _ _
      _ ≤ C1 * ‖ω‖ + 2 * ‖ω‖ :=
          add_le_add (hC1 c hc1 ω hc) (B0583.norm_zeroVelLp_le c hm1 ω hc)
      _ = C0 * ‖ω‖ := by ring
  refine ⟨u, G, hmu, hmG, ?_, ?_, ?_, ?_⟩
  · -- Clause 3: `IsBiotSavart c f u`
    refine ⟨fun j => (hm₁ j).add ((hm₂ j).const_mul Complex.I), ?_, ?_⟩
    · intro ψ hψ
      have hA : IntegrableOn (fun x => u₁ x 0 * (B0579.pd 0 ψ x : ℂ) +
          u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
        (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 0 (hψ.pd 0)).add
          (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 1 (hψ.pd 1))
      have hB : IntegrableOn (fun x => u₂ x 0 * (B0579.pd 0 ψ x : ℂ) +
          u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
        (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 0 (hψ.pd 0)).add
          (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 1 (hψ.pd 1))
      have hsplit : ∀ x, u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ) =
          (u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) +
            Complex.I * (u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) :=
        fun _ => by dsimp [u]; ring
      rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hA (hB.const_mul _),
        integral_const_mul, hdiv₁ ψ hψ, hdiv₂ ψ hψ]
      ring
    · intro ψ hψ
      have hI1 : IntegrableOn (fun x => u₁ x 0 * (B0579.pd 1 ψ x : ℂ) -
          u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
        (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 0 (hψ.pd 1)).sub
          (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 1 (hψ.pd 0))
      have hI2 : IntegrableOn (fun x => u₂ x 0 * (B0579.pd 1 ψ x : ℂ) -
          u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
        (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 0 (hψ.pd 1)).sub
          (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 1 (hψ.pd 0))
      have hpt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
          f x * (ψ x : ℂ) = ((ω₁ x : ℝ) : ℂ) * (ψ x : ℂ) +
            Complex.I * (((ω₂ x : ℝ) : ℂ) * (ψ x : ℂ)) := by
        filter_upwards [ae₁, ae₂] with x h₁ h₂
        simp only [h₁, h₂]
        conv_lhs => rw [← Complex.re_add_im (f x)]
        ring
      have hsplit : ∀ x, u x 0 * (B0579.pd 1 ψ x : ℂ) - u x 1 * (B0579.pd 0 ψ x : ℂ) =
          (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) +
            Complex.I * (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) :=
        fun _ => by dsimp [u]; ring
      rw [integral_congr_ae hpt,
        integral_add (CTE.T20_7.integrableOn_X_test_complex ω₁ hψ)
          ((CTE.T20_7.integrableOn_X_test_complex ω₂ hψ).const_mul _),
        integral_const_mul, hcurl₁ ψ hψ, hcurl₂ ψ hψ,
        integral_congr_ae (Eventually.of_forall hsplit), integral_add hI1 (hI2.const_mul _),
        integral_const_mul]
  · -- Clause 4: `∀ i j, HasWeakCellDerivC c j (fun x => u x i) (fun x => G x i j)`
    intro i j
    fin_cases j
    · simpa [G, u, gq] using hasWeakCellDerivC_add_I 0
        (hasWeakCellDerivC_of_velDeriv 0 U₁ GQ₁
          (B0583.hasWeakVelDeriv_velocity_q c hm1 ω₁ hcirc₁) i)
        (hasWeakCellDerivC_of_velDeriv 0 U₂ GQ₂
          (B0583.hasWeakVelDeriv_velocity_q c hm1 ω₂ hcirc₂) i)
    · simpa [G, u, ge] using hasWeakCellDerivC_add_I 1
        (hasWeakCellDerivC_of_velDeriv 1 U₁ GE₁
          (B0583.hasWeakVelDeriv_velocity_eta c hm1 ω₁ hcirc₁) i)
        (hasWeakCellDerivC_of_velDeriv 1 U₂ GE₂
          (B0583.hasWeakVelDeriv_velocity_eta c hm1 ω₂ hcirc₂) i)
  · -- Clause 5: velocity `L²(cell c)` bound
    rw [lintegral_vnorm2_sq_eq_velNorm_sq c u hmu]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    have hv₁ : velNorm c u₁ ≤ ENNReal.ofReal (C0 * (xNorm c 9 f).toReal) := by
      rw [CTE.velNorm_eq_lp c U₁]
      exact ENNReal.ofReal_le_ofReal ((hU_norm ω₁ hcirc₁).trans
        (mul_le_mul_of_nonneg_left hn₁ hC0nn))
    have hv₂ : velNorm c u₂ ≤ ENNReal.ofReal (C0 * (xNorm c 9 f).toReal) := by
      rw [CTE.velNorm_eq_lp c U₂]
      exact ENNReal.ofReal_le_ofReal ((hU_norm ω₂ hcirc₂).trans
        (mul_le_mul_of_nonneg_left hn₂ hC0nn))
    have hX : ENNReal.ofReal (C0 * (xNorm c 9 f).toReal) = ENNReal.ofReal C0 * xNorm c 9 f := by
      rw [ENNReal.ofReal_mul hC0nn, ENNReal.ofReal_toReal hfin]
    calc velNorm c u
        ≤ velNorm c u₁ + velNorm c u₂ := CTE.T20_7.velNorm_add_I_le c u₁ u₂ hm₁ hm₂
      _ ≤ ENNReal.ofReal (C0 * (xNorm c 9 f).toReal) +
            ENNReal.ofReal (C0 * (xNorm c 9 f).toReal) := add_le_add hv₁ hv₂
      _ = ENNReal.ofReal (2 * C0) * xNorm c 9 f := by
          rw [hX, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          ring
      _ ≤ ENNReal.ofReal (2 * C0 + 6) * xNorm c 9 f := by
          gcongr
          linarith
  · -- Clause 6: gradient `L²(cell c)` bound
    have hpt : ∀ x, ENNReal.ofReal (tnorm2 (G x) ^ 2) =
        ENNReal.ofReal (vnorm2 (gq x) ^ 2) + ENNReal.ofReal (vnorm2 (ge x) ^ 2) := by
      intro x
      rw [tnorm2_sq_eq_vnorm2_sq_add (G x),
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      rfl
    simp_rw [hpt]
    rw [lintegral_add_left (((causalLin_measurable_vnorm2 hmgq).pow_const 2).ennreal_ofReal),
      lintegral_vnorm2_sq_eq_velNorm_sq c gq hmgq,
      lintegral_vnorm2_sq_eq_velNorm_sq c ge hmge]
    have hgq₁ : velNorm c gq₁ ≤ ENNReal.ofReal (1 * (xNorm c 9 f).toReal) := by
      rw [CTE.velNorm_eq_lp c GQ₁]
      exact ENNReal.ofReal_le_ofReal ((B0583.norm_velGradQ_le c hm1 ω₁).trans (by linarith))
    have hgq₂ : velNorm c gq₂ ≤ ENNReal.ofReal (1 * (xNorm c 9 f).toReal) := by
      rw [CTE.velNorm_eq_lp c GQ₂]
      exact ENNReal.ofReal_le_ofReal ((B0583.norm_velGradQ_le c hm1 ω₂).trans (by linarith))
    have hge₁ : velNorm c ge₁ ≤ ENNReal.ofReal (2 * (xNorm c 9 f).toReal) := by
      rw [CTE.velNorm_eq_lp c GE₁]
      exact ENNReal.ofReal_le_ofReal ((B0583.norm_velGradEta_le c hm1 ω₁ hcirc₁).trans
        (by linarith))
    have hge₂ : velNorm c ge₂ ≤ ENNReal.ofReal (2 * (xNorm c 9 f).toReal) := by
      rw [CTE.velNorm_eq_lp c GE₂]
      exact ENNReal.ofReal_le_ofReal ((B0583.norm_velGradEta_le c hm1 ω₂ hcirc₂).trans
        (by linarith))
    have hgq : velNorm c gq ≤ ENNReal.ofReal 2 * xNorm c 9 f := by
      calc velNorm c gq
          ≤ velNorm c gq₁ + velNorm c gq₂ :=
            CTE.T20_7.velNorm_add_I_le c gq₁ gq₂ (memLp_lp_coord GQ₁) (memLp_lp_coord GQ₂)
        _ ≤ ENNReal.ofReal (1 * (xNorm c 9 f).toReal) +
              ENNReal.ofReal (1 * (xNorm c 9 f).toReal) := add_le_add hgq₁ hgq₂
        _ = ENNReal.ofReal 2 * xNorm c 9 f := by
            rw [one_mul, ENNReal.ofReal_toReal hfin, ENNReal.ofReal_ofNat]
            ring
    have hge : velNorm c ge ≤ ENNReal.ofReal 4 * xNorm c 9 f := by
      calc velNorm c ge
          ≤ velNorm c ge₁ + velNorm c ge₂ :=
            CTE.T20_7.velNorm_add_I_le c ge₁ ge₂ (memLp_lp_coord GE₁) (memLp_lp_coord GE₂)
        _ ≤ ENNReal.ofReal (2 * (xNorm c 9 f).toReal) +
              ENNReal.ofReal (2 * (xNorm c 9 f).toReal) := add_le_add hge₁ hge₂
        _ = ENNReal.ofReal 4 * xNorm c 9 f := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_toReal hfin,
              ENNReal.ofReal_ofNat, ← add_mul, ← ENNReal.ofReal_ofNat]
            norm_num
    calc velNorm c gq ^ (2 : ℝ) + velNorm c ge ^ (2 : ℝ)
        ≤ (ENNReal.ofReal 2 * xNorm c 9 f) ^ (2 : ℝ) +
            (ENNReal.ofReal 4 * xNorm c 9 f) ^ (2 : ℝ) :=
          add_le_add (ENNReal.rpow_le_rpow hgq (by norm_num))
            (ENNReal.rpow_le_rpow hge (by norm_num))
      _ ≤ (ENNReal.ofReal (2 * C0 + 6) * xNorm c 9 f) ^ (2 : ℝ) := by
          simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← add_mul]
          refine mul_le_mul_of_nonneg_right ?_ bot_le
          rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two,
            ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
            ← ENNReal.ofReal_pow (by linarith),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by nlinarith)

end UnforcedLeray.Short.IIIa
