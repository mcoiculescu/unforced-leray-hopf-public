import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth.Zero.IBP.Cut

/-!


Source: `the November 2 reference manuscript`, line 346.
Statement: `Sub/PartI_T08_6_2.lean`, `EtaCutIBP`. Helpers: `IBP/Cut.lean`.

Route. With `χ = etaCut R (·.2)` (a function of `η` only):
* `q`-part: `∫ ∂_q f₀ · (χP) = -∫ f₀ · ∂_q(χP)` (`Cyl.integral_cell_partialQ_mul`, periodicity);
* `η`-part: `∫ χ' · (P f₁) = -∫ χ · ∂_η(P f₁)` (`Cyl.integral_cell_partialEta_mul`);
* `div f = 0` gives `∂_q f₀ + ∂_η f₁ = 0`, so `∫ (χP) ∂_η f₁ = -∫ ∂_q f₀ (χP)`.
Adding: `∫ χ (f₀ ∂_q P + f₁ ∂_η P) = -∫ χ' P f₁`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem etaCutIBP_proof : UnforcedLeray.Short.PartI.EtaCutIBP := by
  intro c f P hyp R hR
  obtain ⟨hc, ⟨hfc, hfper, hL2⟩, hdiv, hP, hper, ⟨M, hM⟩, hL2P⟩ := hyp
  have hc0 : 0 ≤ c := hc.le
  have hR0 : 0 ≤ R := hR.le
  obtain ⟨K, hK⟩ := etaBump_deriv_bound
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  -- smoothness
  have hPd : Differentiable ℝ P := hP.differentiable (by simp)
  have hPc : Continuous P := hP.continuous
  have hf0C : ContDiff ℝ ∞ (fun z : Plane => f z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Train.Vec →L[ℝ] ℝ).contDiff.comp hfc
  have hf1C : ContDiff ℝ ∞ (fun z : Plane => f z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Train.Vec →L[ℝ] ℝ).contDiff.comp hfc
  have hf0d : Differentiable ℝ (fun z : Plane => f z 0) := hf0C.differentiable (by simp)
  have hf1d : Differentiable ℝ (fun z : Plane => f z 1) := hf1C.differentiable (by simp)
  have hχd : Differentiable ℝ (fun z : Plane => etaCut R z.2) :=
    ((contDiff_etaCut R).differentiable (by simp)).comp differentiable_snd
  -- L² facts (word derivatives, `wordComp [] g k = g · k`)
  have hq0 : MemLp (fun z : Plane => Cyl.partialQ (fun x => f x 0) z) 2 (Cyl.cellμ c) :=
    hL2 [true] 0
  have he1 : MemLp (fun z : Plane => Cyl.partialEta (fun x => f x 1) z) 2 (Cyl.cellμ c) :=
    hL2 [false] 1
  have hf1L : MemLp (fun z : Plane => f z 1) 2 (Cyl.cellμ c) := hL2 [] 1
  have hf0L : MemLp (fun z : Plane => f z 0) 2 (Cyl.cellμ c) := hL2 [] 0
  have hPq : MemLp (fun z : Plane => Cyl.partialQ P z) 2 (Cyl.cellμ c) := hL2P [] 0
  have hPe : MemLp (fun z : Plane => Cyl.partialEta P z) 2 (Cyl.cellμ c) := hL2P [] 1
  have hL1q : IntegrableOn (fun z : Plane => f z 0 * Cyl.partialQ P z) (Cyl.cell c) :=
    hf0L.integrable_mul hPq
  have hL1e : IntegrableOn (fun z : Plane => f z 1 * Cyl.partialEta P z) (Cyl.cell c) :=
    hf1L.integrable_mul hPe
  have hL1P : IntegrableOn (fun z : Plane => Cyl.partialEta P z * f z 1) (Cyl.cell c) :=
    hPe.integrable_mul hf1L
  -- pointwise identities
  have hdivz : ∀ z : Plane,
      Cyl.partialQ (fun x => f x 0) z + Cyl.partialEta (fun x => f x 1) z = 0 :=
    fun z => hdiv z
  have hf0per : Cyl.IsPeriodic c (fun z : Plane => f z 0) := fun z =>
    congrArg (fun v => v 0) (hfper z)
  have hgper : Cyl.IsPeriodic c (fun z : Plane => etaCut R z.2 * P z) := fun z => by
    show etaCut R z.2 * P (z.1 + c, z.2) = etaCut R z.2 * P z
    rw [hper z]
  have hχm : Measurable (fun z : Plane => etaCut R z.2) :=
    (continuous_etaCut R).measurable.comp measurable_snd
  have hχb : ∀ z : Plane, |etaCut R z.2| ≤ 1 := fun z => by
    rw [abs_of_nonneg (etaCut_nonneg _ _)]
    exact etaCut_le_one _ _
  have hχP_m : Measurable (fun z : Plane => etaCut R z.2 * P z) := hχm.mul hPc.measurable
  have hχP_b : ∀ z : Plane, |etaCut R z.2 * P z| ≤ M := fun z => by
    rw [abs_mul, abs_of_nonneg (etaCut_nonneg _ _)]
    calc etaCut R z.2 * |P z| ≤ 1 * M :=
          mul_le_mul (etaCut_le_one _ _) (hM z) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have hχP_s : ∀ z : Plane, 2 * R < |z.2| → etaCut R z.2 * P z = 0 := fun z h => by
    rw [etaCut_eq_zero hR (le_of_lt h), zero_mul]
  have hdP_m : Measurable (fun z : Plane => deriv (etaCut R) z.2 * P z) :=
    (measurable_deriv_etaCut R).mul hPc.measurable
  have hdP_b : ∀ z : Plane, |deriv (etaCut R) z.2 * P z| ≤ K * R⁻¹ * M := fun z => by
    rw [abs_mul]
    exact mul_le_mul (etaCut_deriv_abs_le hR hK z.2) (hM z) (abs_nonneg _)
      (mul_nonneg hK0 (inv_nonneg.2 hR0))
  have hdP_s : ∀ z : Plane, 2 * R < |z.2| → deriv (etaCut R) z.2 * P z = 0 := fun z h => by
    rw [etaCut_deriv_eq_zero hR h, zero_mul]
  -- derivatives of products
  have hpQ : ∀ z : Plane, Cyl.partialQ (fun w : Plane => etaCut R w.2 * P w) z
      = etaCut R z.2 * Cyl.partialQ P z := fun z => by
    have h := (Cyl.hasDerivAt_sliceQ hPd z.1 z.2).const_mul (etaCut R z.2)
    exact h.deriv
  have hgE : ∀ z : Plane, Cyl.partialEta (fun w : Plane => P w * f w 1) z
      = Cyl.partialEta P z * f z 1 + P z * Cyl.partialEta (fun x => f x 1) z := fun z => by
    have h := (Cyl.hasDerivAt_sliceEta hPd z.1 z.2).mul (Cyl.hasDerivAt_sliceEta hf1d z.1 z.2)
    exact h.deriv
  have hχE : ∀ z : Plane, Cyl.partialEta (fun w : Plane => etaCut R w.2) z
      = deriv (etaCut R) z.2 := fun z => rfl
  -- Step A: the `q`-part
  have hA1 : IntegrableOn (fun z : Plane => Cyl.partialQ (fun x => f x 0) z * (etaCut R z.2 * P z))
      (Cyl.cell c) :=
    integrableOn_congr_pt (integrableOn_cell_mul_of_slab hc0 hR0 hχP_m hχP_b hχP_s hq0)
      (fun z => mul_comm _ _)
  have hA2 : IntegrableOn (fun z : Plane => f z 0 * Cyl.partialQ
      (fun w : Plane => etaCut R w.2 * P w) z) (Cyl.cell c) :=
    integrableOn_congr_pt (integrableOn_cell_mul_of_bdd hL1q hχm hχb)
      (fun z => by rw [hpQ z]; ring)
  have hA : ∫ z in Cyl.cell c, Cyl.partialQ (fun x => f x 0) z * (etaCut R z.2 * P z)
      = -∫ z in Cyl.cell c, f z 0 * (etaCut R z.2 * Cyl.partialQ P z) := by
    refine (UnforcedLeray.Cyl.integral_cell_partialQ_mul hc hf0d (hχd.mul hPd) hf0per hgper
      hA1 hA2).trans ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact congrArg (fun t => f z 0 * t) (hpQ z)
  -- Step B: the `η`-part
  have hB0 : IntegrableOn (fun z : Plane => etaCut R z.2 * (P z * f z 1)) (Cyl.cell c) :=
    integrableOn_congr_pt (integrableOn_cell_mul_of_slab hc0 hR0 hχP_m hχP_b hχP_s hf1L)
      (fun z => mul_assoc _ _ _)
  have hB1 : IntegrableOn (fun z : Plane => deriv (etaCut R) z.2 * (P z * f z 1)) (Cyl.cell c) :=
    integrableOn_congr_pt (integrableOn_cell_mul_of_slab hc0 hR0 hdP_m hdP_b hdP_s hf1L)
      (fun z => mul_assoc _ _ _)
  have hT1 : IntegrableOn (fun z : Plane => etaCut R z.2 * (Cyl.partialEta P z * f z 1))
      (Cyl.cell c) :=
    integrableOn_cell_mul_of_bdd hL1P hχm hχb
  have hT2 : IntegrableOn (fun z : Plane => etaCut R z.2 * P z * Cyl.partialEta
      (fun x => f x 1) z) (Cyl.cell c) :=
    integrableOn_cell_mul_of_slab hc0 hR0 hχP_m hχP_b hχP_s he1
  have hB2 : IntegrableOn (fun z : Plane => etaCut R z.2 * Cyl.partialEta
      (fun w : Plane => P w * f w 1) z) (Cyl.cell c) :=
    (hT1.add hT2).congr_fun (fun z _ => by
      simp only [Pi.add_apply]
      rw [hgE z]
      ring) (Cyl.measurableSet_cell c)
  have hB : ∫ z in Cyl.cell c, deriv (etaCut R) z.2 * (P z * f z 1)
      = -∫ z in Cyl.cell c, etaCut R z.2 * Cyl.partialEta (fun w : Plane => P w * f w 1) z := by
    have h := UnforcedLeray.Cyl.integral_cell_partialEta_mul
      (f := fun z : Plane => etaCut R z.2) (g := fun z : Plane => P z * f z 1)
      hχd (hPd.mul hf1d) hB0 hB1 hB2
    simpa only [hχE] using h
  have hBsplit : ∫ z in Cyl.cell c, etaCut R z.2 * Cyl.partialEta (fun w : Plane => P w * f w 1) z
      = (∫ z in Cyl.cell c, etaCut R z.2 * (Cyl.partialEta P z * f z 1))
        + ∫ z in Cyl.cell c, etaCut R z.2 * P z * Cyl.partialEta (fun x => f x 1) z := by
    rw [← integral_add hT1 hT2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hgE z]
    ring
  -- Step C: divergence
  have hC : (∫ z in Cyl.cell c, Cyl.partialQ (fun x => f x 0) z * (etaCut R z.2 * P z))
      + (∫ z in Cyl.cell c, etaCut R z.2 * P z * Cyl.partialEta (fun x => f x 1) z) = 0 := by
    rw [← integral_add hA1 hT2]
    have hz : ∀ z : Plane, Cyl.partialQ (fun x => f x 0) z * (etaCut R z.2 * P z)
        + etaCut R z.2 * P z * Cyl.partialEta (fun x => f x 1) z = 0 := fun z => by
      linear_combination (etaCut R z.2 * P z) * hdivz z
    simp only [hz, integral_zero]
  -- splitting the main integrand
  have hU1 : IntegrableOn (fun z : Plane => f z 0 * (etaCut R z.2 * Cyl.partialQ P z))
      (Cyl.cell c) :=
    integrableOn_congr_pt (integrableOn_cell_mul_of_bdd hL1q hχm hχb) (fun z => by ring)
  have hU2 : IntegrableOn (fun z : Plane => f z 1 * (etaCut R z.2 * Cyl.partialEta P z))
      (Cyl.cell c) :=
    integrableOn_congr_pt (integrableOn_cell_mul_of_bdd hL1e hχm hχb) (fun z => by ring)
  have hsplit : ∫ z in Cyl.cell c, etaCut R z.2 * (f z 0 * Cyl.partialQ P z
      + f z 1 * Cyl.partialEta P z)
      = (∫ z in Cyl.cell c, f z 0 * (etaCut R z.2 * Cyl.partialQ P z))
        + ∫ z in Cyl.cell c, f z 1 * (etaCut R z.2 * Cyl.partialEta P z) := by
    rw [← integral_add hU1 hU2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  have hV2U2 : ∫ z in Cyl.cell c, etaCut R z.2 * (Cyl.partialEta P z * f z 1)
      = ∫ z in Cyl.cell c, f z 1 * (etaCut R z.2 * Cyl.partialEta P z) :=
    integral_congr_ae (Eventually.of_forall fun z => by ring)
  rw [hsplit]
  rw [hBsplit] at hB
  linarith [hA, hB, hC, hV2U2]

end UnforcedLeray.Short.PartI
