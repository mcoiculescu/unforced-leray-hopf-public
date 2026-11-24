import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8

/-!
# Homogeneity of `X^mt` (`XmtSmulP`, source 4766-4791)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

open UnforcedLeray.Short.PartIIIb.Concrete

theorem phaseMean_smul_aux (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (r u : ℝ) :
    phaseMean c ν χo (r • M) u = r • phaseMean c ν χo M u := by
  funext i j
  unfold phaseMean
  by_cases h : i = 1 ∨ j = 1
  · simp [h]
  · simp only [h, ite_false, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul]
    ring

theorem sigmaM_smul_aux (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (r : ℝ) (x' : ℝ × ℝ) :
    sigmaM c ν χo (r • M) x' = r • sigmaM c ν χo M x' := by
  funext a b
  unfold sigmaM
  simp only [phaseMean_smul_aux, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem int_mul_const_aux (s : Set ℝ) (p r : ℝ) (f : ℝ → ℝ) :
    ∫ t in s, t ^ p * (r * f t) = r * ∫ t in s, t ^ p * f t := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  ring

theorem newtonV_smul_aux (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (r : ℝ) (x : Vec3) :
    newtonV c ν μ χo (r • M) x = r • newtonV c ν μ χo M x := by
  funext i
  have hpt : ∀ (y : Vec3) (x' : ℝ × ℝ),
      ∑ j, ∑ k, newtonD3 y i j k * sigmaM c ν χo (r • M) x' j k =
        r * ∑ j, ∑ k, newtonD3 y i j k * sigmaM c ν χo M x' j k := by
    intro y x'
    rw [sigmaM_smul_aux, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have key : ∀ t : ℝ,
      ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo (r • M) x' j k
        = r * ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo M x' j k := by
    intro t
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x' => hpt _ x')
  unfold newtonV
  simp only [key, Pi.smul_apply, smul_eq_mul, int_mul_const_aux]
  ring

/-- Unconditional homogeneity `X^mt_{r M} = r X^mt_M` (source 4766-4791). -/
theorem xmtSmul : UnforcedLeray.Short.PartIIIb.Concrete.XmtSmulP := by
  intro c ν ε μ χo χy M r
  have hY : ∀ μ' y, youngW c ν ε μ' χo (r • M) y = r • youngW c ν ε μ' χo M y := by
    intro μ' y
    unfold youngW
    rw [newtonV_smul_aux]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hZ : ∀ y, (youngW c ν ε μ χo (r • M) - youngW c ν ε (μ + 1) χo (r • M)) y =
      r • (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) y := by
    intro y
    simp only [Pi.sub_apply, hY, smul_sub]
  have hpsi : ∀ (Z : Vec3 → Vec3) (y : Vec3), streamPsi (r • Z) y = r * streamPsi Z y := by
    intro Z y
    unfold streamPsi
    have : ∫ ρ in Ioi (cylR y), ρ * (r • Z) (rayPt y ρ) 2 =
        r * ∫ ρ in Ioi (cylR y), ρ * Z (rayPt y ρ) 2 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    ring
  have hZf : youngW c ν ε μ χo (r • M) - youngW c ν ε (μ + 1) χo (r • M) =
      r • (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) := by
    funext y
    exact hZ y
  unfold Xmt
  rw [hZf]
  funext y
  ext i
  simp only [streamCut, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpsi]
  ring
