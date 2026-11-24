import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.AdvInt

/-!
# Part I, task `PartI:T08/7/2/2`: helpers for `JTBoundA`

Source: `the November 2 reference manuscript` lines 352-358.
* `ba_top_zero`: the top term `∫ G (V·∇G) = 0` for `div V = 0` periodic (integration by parts);
* `ba_term_bound`: Cauchy-Schwarz bound of one Leibniz term `∫ ∂_w f_k (∂_a V_m ∂_b f_k)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem ba_partialQ_mul {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun x => f x * g x) z = Cyl.partialQ f z * g z + f z * Cyl.partialQ g z :=
  ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).mul (Cyl.hasDerivAt_sliceQ hg z.1 z.2)).deriv

theorem ba_partialEta_mul {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun x => f x * g x) z =
      Cyl.partialEta f z * g z + f z * Cyl.partialEta g z :=
  ((Cyl.hasDerivAt_sliceEta hf z.1 z.2).mul (Cyl.hasDerivAt_sliceEta hg z.1 z.2)).deriv

/-- Integrability of `B · (x · y)` with `B` bounded continuous, `x, y ∈ L²`. -/
theorem ba_int3 {μ : Measure Plane} {x y B : Plane → ℝ} (hx : MemLp x 2 μ) (hy : MemLp y 2 μ)
    (hB : AEStronglyMeasurable B μ) (M : ℝ) (hM : ∀ z, |B z| ≤ M) :
    Integrable (fun z => B z * (x z * y z)) μ := by
  have h1 : Integrable (x * y) μ := hx.integrable_mul hy
  have h2 : Integrable (fun z => (x * y) z * B z) μ :=
    h1.mul_bdd (c := M) hB (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hM z)
  refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.mul_apply]
  ring

theorem ba_top_zero {c : ℝ} (hc : 0 < c) {V : Plane → Vec} {G : Plane → ℝ}
    (hV : ContDiff ℝ ∞ V) (hVp : Cyl.IsPeriodic c V) (hVd : ∀ z, Cyl.divergence V z = 0)
    (hVb : ∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w V k z| ≤ M)
    (hG : ContDiff ℝ ∞ G) (hGp : Cyl.IsPeriodic c G)
    (hG0 : MemLp G 2 (Cyl.cellμ c)) (hGq : MemLp (Cyl.partialQ G) 2 (Cyl.cellμ c))
    (hGe : MemLp (Cyl.partialEta G) 2 (Cyl.cellμ c)) :
    ∫ z in Cyl.cell c, G z * (V z 0 * Cyl.partialQ G z + V z 1 * Cyl.partialEta G z) = 0 := by
  have hV0 : ContDiff ℝ ∞ (fun z => V z 0) := contDiff_comp_coord hV 0
  have hV1 : ContDiff ℝ ∞ (fun z => V z 1) := contDiff_comp_coord hV 1
  have dV0 : Differentiable ℝ (fun z => V z 0) := hV0.differentiable (by simp)
  have dV1 : Differentiable ℝ (fun z => V z 1) := hV1.differentiable (by simp)
  have dG : Differentiable ℝ G := hG.differentiable (by simp)
  have dGG : Differentiable ℝ (fun z => G z * G z) := dG.mul dG
  obtain ⟨M00, h00⟩ := hVb [] 0
  obtain ⟨M01, h01⟩ := hVb [] 1
  obtain ⟨M10, h10⟩ := hVb [true] 0
  obtain ⟨M11, h11⟩ := hVb [false] 1
  have cV0 : AEStronglyMeasurable (fun z => V z 0) (Cyl.cellμ c) := hV0.continuous.aestronglyMeasurable
  have cV1 : AEStronglyMeasurable (fun z => V z 1) (Cyl.cellμ c) := hV1.continuous.aestronglyMeasurable
  have cdV0 : AEStronglyMeasurable (Cyl.partialQ (fun z => V z 0)) (Cyl.cellμ c) :=
    (contDiff_wordComp hV [true] 0).continuous.aestronglyMeasurable
  have cdV1 : AEStronglyMeasurable (Cyl.partialEta (fun z => V z 1)) (Cyl.cellμ c) :=
    (contDiff_wordComp hV [false] 1).continuous.aestronglyMeasurable
  have b00 : ∀ z, |V z 0| ≤ M00 := h00
  have b01 : ∀ z, |V z 1| ≤ M01 := h01
  have b10 : ∀ z, |Cyl.partialQ (fun z => V z 0) z| ≤ M10 := h10
  have b11 : ∀ z, |Cyl.partialEta (fun z => V z 1) z| ≤ M11 := h11
  -- the two products and their derivatives
  have eQ : ∀ z, Cyl.partialQ (fun x => V x 0 * (G x * G x)) z =
      Cyl.partialQ (fun z => V z 0) z * (G z * G z) +
        V z 0 * (Cyl.partialQ G z * G z + G z * Cyl.partialQ G z) := by
    intro z
    rw [ba_partialQ_mul dV0 dGG, ba_partialQ_mul dG dG]
  have eE : ∀ z, Cyl.partialEta (fun x => V x 1 * (G x * G x)) z =
      Cyl.partialEta (fun z => V z 1) z * (G z * G z) +
        V z 1 * (Cyl.partialEta G z * G z + G z * Cyl.partialEta G z) := by
    intro z
    rw [ba_partialEta_mul dV1 dGG, ba_partialEta_mul dG dG]
  have iQ1 := ba_int3 (μ := Cyl.cellμ c) hG0 hG0 cdV0 M10 b10
  have iQ2 := ba_int3 (μ := Cyl.cellμ c) hGq hG0 cV0 M00 b00
  have iQ3 := ba_int3 (μ := Cyl.cellμ c) hG0 hGq cV0 M00 b00
  have iE1 := ba_int3 (μ := Cyl.cellμ c) hG0 hG0 cdV1 M11 b11
  have iE2 := ba_int3 (μ := Cyl.cellμ c) hGe hG0 cV1 M01 b01
  have iE3 := ba_int3 (μ := Cyl.cellμ c) hG0 hGe cV1 M01 b01
  have iP0 := ba_int3 (μ := Cyl.cellμ c) hG0 hG0 cV0 M00 b00
  have iP1 := ba_int3 (μ := Cyl.cellμ c) hG0 hG0 cV1 M01 b01
  have iDQ : Integrable (Cyl.partialQ (fun x => V x 0 * (G x * G x))) (Cyl.cellμ c) := by
    have : Cyl.partialQ (fun x => V x 0 * (G x * G x)) = fun z =>
      Cyl.partialQ (fun z => V z 0) z * (G z * G z) +
        (V z 0 * (Cyl.partialQ G z * G z) + V z 0 * (G z * Cyl.partialQ G z)) := by
      funext z; rw [eQ]; ring
    rw [this]
    exact iQ1.add (iQ2.add iQ3)
  have iDE : Integrable (Cyl.partialEta (fun x => V x 1 * (G x * G x))) (Cyl.cellμ c) := by
    have : Cyl.partialEta (fun x => V x 1 * (G x * G x)) = fun z =>
      Cyl.partialEta (fun z => V z 1) z * (G z * G z) +
        (V z 1 * (Cyl.partialEta G z * G z) + V z 1 * (G z * Cyl.partialEta G z)) := by
      funext z; rw [eE]; ring
    rw [this]
    exact iE1.add (iE2.add iE3)
  have pP0 : Cyl.IsPeriodic c (fun x => V x 0 * (G x * G x)) := fun z => by
    show V _ 0 * (G _ * G _) = V z 0 * (G z * G z)
    rw [hVp z, hGp z]
  have z1 : ∫ z in Cyl.cell c, Cyl.partialQ (fun x => V x 0 * (G x * G x)) z = 0 :=
    Cyl.integral_cell_deriv_q_of_periodic hc pP0
      (Cyl.hasDerivAt_sliceQ (dV0.mul dGG)) iDQ
  have z2 : ∫ z in Cyl.cell c, Cyl.partialEta (fun x => V x 1 * (G x * G x)) z = 0 :=
    Cyl.integral_cell_deriv_eta (Cyl.hasDerivAt_sliceEta (dV1.mul dGG)) iP1 iDE
  have hsum : ∫ z in Cyl.cell c, (Cyl.partialQ (fun x => V x 0 * (G x * G x)) z +
      Cyl.partialEta (fun x => V x 1 * (G x * G x)) z) = 0 := by
    have e : ∫ z in Cyl.cell c, (Cyl.partialQ (fun x => V x 0 * (G x * G x)) z +
        Cyl.partialEta (fun x => V x 1 * (G x * G x)) z) =
        (∫ z in Cyl.cell c, Cyl.partialQ (fun x => V x 0 * (G x * G x)) z) +
        ∫ z in Cyl.cell c, Cyl.partialEta (fun x => V x 1 * (G x * G x)) z :=
      integral_add iDQ iDE
    rw [e, z1, z2, add_zero]
  have hpt : ∀ z, Cyl.partialQ (fun x => V x 0 * (G x * G x)) z +
      Cyl.partialEta (fun x => V x 1 * (G x * G x)) z =
      2 * (G z * (V z 0 * Cyl.partialQ G z + V z 1 * Cyl.partialEta G z)) := by
    intro z
    have hd := hVd z
    simp only [Cyl.divergence] at hd
    rw [eQ, eE]
    have : Cyl.partialQ (fun z => V z 0) z * (G z * G z) +
        Cyl.partialEta (fun z => V z 1) z * (G z * G z) = 0 := by
      rw [← add_mul, hd, zero_mul]
    linarith [this]
  simp only [hpt] at hsum
  rw [integral_const_mul] at hsum
  linarith

/-- One Leibniz term, by Cauchy-Schwarz: `|∫ ∂_w f_k (∂_a V_m ∂_b f_k)| ≤ M ‖∂_b f_k‖ ‖∂_w f_k‖`. -/
theorem ba_term_bound {c : ℝ} {V f : Plane → Vec} (hV : ContDiff ℝ ∞ V)
    (hf : CellSmoothL2 c f) (M : ℝ) (a w b : List Bool) (m k : Fin 2)
    (hM : ∀ z, |wordComp a V m z| ≤ M) :
    |∫ z in Cyl.cell c, wordComp w f k z * (wordComp a V m z * wordComp b f k z)| ≤
      M * (Real.sqrt (∫ z in Cyl.cell c, wordComp b f k z * wordComp b f k z) *
        Real.sqrt (∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z)) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have cA : AEStronglyMeasurable (wordComp a V m) (Cyl.cellμ c) :=
    (contDiff_wordComp hV a m).continuous.aestronglyMeasurable
  have Lw := hf.2.2 w k
  have Lb := hf.2.2 b k
  have haa : IntegrableOn (fun z => wordComp w f k z * wordComp w f k z) (Cyl.cell c) :=
    Lw.integrable_mul Lw
  have hbb : IntegrableOn (fun z => wordComp b f k z * wordComp b f k z) (Cyl.cell c) :=
    Lb.integrable_mul Lb
  -- the product `V b`
  have hVbb : IntegrableOn (fun z => (wordComp a V m z * wordComp b f k z) *
      (wordComp a V m z * wordComp b f k z)) (Cyl.cell c) := by
    have := ba_int3 (μ := Cyl.cellμ c) Lb Lb
      (B := fun z => wordComp a V m z * wordComp a V m z)
      (cA.mul cA) (M * M) (fun z => by
        rw [abs_mul]; exact mul_le_mul (hM z) (hM z) (abs_nonneg _) hM0)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring
  have habV : IntegrableOn (fun z => wordComp w f k z *
      (wordComp a V m z * wordComp b f k z)) (Cyl.cell c) :=
    ba_int3 (μ := Cyl.cellμ c) (B := fun z => wordComp a V m z) (x := wordComp w f k)
      (y := wordComp b f k) Lw Lb cA M hM |>.congr (Filter.Eventually.of_forall fun z => by
        simp only; ring)
  have h1 := ForcingIBP.abs_int_cs (c := c) (wordComp w f k) (fun z => wordComp a V m z * wordComp b f k z)
    haa hVbb habV
  have h2 : ∫ z in Cyl.cell c, (wordComp a V m z * wordComp b f k z) *
      (wordComp a V m z * wordComp b f k z) ≤
      M ^ 2 * ∫ z in Cyl.cell c, wordComp b f k z * wordComp b f k z := by
    rw [← integral_const_mul]
    refine integral_mono hVbb (hbb.const_mul _) fun z => ?_
    have : (wordComp a V m z * wordComp b f k z) * (wordComp a V m z * wordComp b f k z) =
        (wordComp a V m z) ^ 2 * (wordComp b f k z * wordComp b f k z) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ (mul_self_nonneg _)
    have := abs_le.mp (hM z)
    nlinarith [this.1, this.2]
  have h3 : Real.sqrt (∫ z in Cyl.cell c, (wordComp a V m z * wordComp b f k z) *
      (wordComp a V m z * wordComp b f k z)) ≤
      M * Real.sqrt (∫ z in Cyl.cell c, wordComp b f k z * wordComp b f k z) := by
    refine (Real.sqrt_le_sqrt h2).trans ?_
    rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0]
  calc _ ≤ _ := h1
    _ ≤ Real.sqrt (∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z) *
          (M * Real.sqrt (∫ z in Cyl.cell c, wordComp b f k z * wordComp b f k z)) :=
        mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    _ = _ := by ring

end UnforcedLeray.Short.PartI
