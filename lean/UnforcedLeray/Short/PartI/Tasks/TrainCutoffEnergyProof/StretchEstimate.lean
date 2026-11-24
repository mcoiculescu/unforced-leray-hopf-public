import UnforcedLeray.Short.PartI.Sub.T05b_2
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T05b/2/5`: the stretching estimate (leaf `StretchEstimate`)

Source of record: `the November 2 reference manuscript`, lines 276-288 (the
stretching term of the cutoff energy method).
Target: `stretchEstimate : StretchEstimate` (`Short/PartI/Sub/T05b_2.lean`). The four hypotheses
`EtaCutoffFacts`, `CellIntegrableOfSupport`, `TrainSliceSmooth`, `DiffEnergyBound` are black boxes.

Route. Fix `S ≥ 0`, `R ≥ 1`, `s ∈ [0, S]`, `w = diffV tr tr' s`, `φ = etaCutoff R`, `C₀` from
`EtaCutoffFacts`, and `M ≥ 0` from `TrainBoundedBy` (at age `0`). Write `g = gradNormSq w`.

* Term 1 (`2 ∫ φ' w₁ ⟨w, v'⟩`): `|φ'| ≤ C₀/R` (since `0 ≤ φ ≤ 1`), `|w₁| ≤ |w|`,
  `|⟨w, v'⟩| ≤ M|w|`, so the integrand is at most `(C₀M/R)|w|²`, and `∫|w|² ≤ 4M`.
* Term 2 (`2 ∫ φ ⟨(w·∇)w, v'⟩`): componentwise Cauchy-Schwarz gives `|(w·∇)w|² ≤ |w|² g`, so
  with `a = √g`, `b = M|w|` and Young, `2φ⟨(w·∇)w, v'⟩ ≤ φ((ν/2) g + (2M²/ν)|w|²)`.
  Integrating: `2 ∫ φ⟨(w·∇)w, v'⟩ ≤ (ν/2) D + (2M²/ν) F`.
* Constant `K = 2M²/ν + 8C₀M²`; `F ≥ 0` and `1/R ≤ 1/√R` for `R ≥ 1` close the estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Pointwise algebra -/

/-- `|x|² = x₀² + x₁²` on `Vec`. -/
theorem se_norm_sq (x : Vec) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- Componentwise Cauchy-Schwarz: `|(u·∇)u|² ≤ |u|² |∇u|²`. -/
theorem se_bilin_sq (u : Plane → Vec) (z : Plane) :
    ‖bilinAdv u u z‖ ^ 2 ≤ ‖u z‖ ^ 2 * gradNormSq u z := by
  rw [se_norm_sq (bilinAdv u u z), se_norm_sq (u z)]
  unfold bilinAdv gradNormSq
  simp only [Train.toVec_zero, Train.toVec_one]
  nlinarith [sq_nonneg (u z 0 * Cyl.partialEta (fun w => u w 0) z -
      u z 1 * Cyl.partialQ (fun w => u w 0) z),
    sq_nonneg (u z 0 * Cyl.partialEta (fun w => u w 1) z -
      u z 1 * Cyl.partialQ (fun w => u w 1) z)]

/-- Young's inequality for the stretching term: `X ≤ M n a` gives `2X ≤ (ν/2) a² + (2M²/ν) n²`. -/
theorem se_young (ν M n a X : ℝ) (hν : 0 < ν) (hn : 0 ≤ n) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hX : X ≤ M * n * a) : 2 * X ≤ (ν / 2) * a ^ 2 + (2 * M ^ 2 / ν) * n ^ 2 := by
  have hν' : ν ≠ 0 := hν.ne'
  have key : (ν / 2) * a ^ 2 + (2 * M ^ 2 / ν) * n ^ 2 - 2 * M * n * a
      = (ν * a - 2 * M * n) ^ 2 / (2 * ν) := by
    field_simp
    ring
  have hnn : 0 ≤ (ν * a - 2 * M * n) ^ 2 / (2 * ν) :=
    div_nonneg (sq_nonneg _) (by linarith)
  nlinarith [key, hnn, hX]

/-- Pointwise stretching bound: `2⟨(u·∇)u, v⟩ ≤ (ν/2)|∇u|² + (2M²/ν)|u|²` when `|v| ≤ M`. -/
theorem se_stretch_pt (ν M : ℝ) (hν : 0 < ν) (hM : 0 ≤ M) (u v : Plane → Vec) (z : Plane)
    (hv : ‖v z‖ ≤ M) :
    2 * inner ℝ (bilinAdv u u z) (v z) ≤
      (ν / 2) * gradNormSq u z + (2 * M ^ 2 / ν) * ‖u z‖ ^ 2 := by
  have hg0 : 0 ≤ gradNormSq u z := gradNormSq_nonneg u z
  have ha0 : 0 ≤ Real.sqrt (gradNormSq u z) := Real.sqrt_nonneg _
  have ha2 : Real.sqrt (gradNormSq u z) ^ 2 = gradNormSq u z := Real.sq_sqrt hg0
  have hB2 := se_bilin_sq u z
  have hB : ‖bilinAdv u u z‖ ≤ ‖u z‖ * Real.sqrt (gradNormSq u z) := by
    have h1 : ‖bilinAdv u u z‖ ^ 2 ≤ (‖u z‖ * Real.sqrt (gradNormSq u z)) ^ 2 := by
      rw [mul_pow, ha2]
      exact hB2
    nlinarith [norm_nonneg (bilinAdv u u z), mul_nonneg (norm_nonneg (u z)) ha0]
  have hX : inner ℝ (bilinAdv u u z) (v z) ≤ M * ‖u z‖ * Real.sqrt (gradNormSq u z) := by
    calc inner ℝ (bilinAdv u u z) (v z) ≤ ‖bilinAdv u u z‖ * ‖v z‖ :=
          real_inner_le_norm _ _
      _ ≤ ‖bilinAdv u u z‖ * M := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ ≤ (‖u z‖ * Real.sqrt (gradNormSq u z)) * M := mul_le_mul_of_nonneg_right hB hM
      _ = M * ‖u z‖ * Real.sqrt (gradNormSq u z) := by ring
  have hY := se_young ν M ‖u z‖ (Real.sqrt (gradNormSq u z)) (inner ℝ (bilinAdv u u z) (v z))
    hν (norm_nonneg _) hM ha0 hX
  rw [ha2] at hY
  exact hY

/-- Pointwise transport bound for term 1: `|d w₁ ⟨w, v⟩| ≤ (C₀M/R)|w|²` when `|d| ≤ C₀/R`, `|v| ≤ M`. -/
theorem se_term1_pt (C₀ M R : ℝ) (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M) (hR : 0 < R) (d : ℝ)
    (hd : |d| ≤ C₀ / R) (w v : Vec) (hv : ‖v‖ ≤ M) :
    |d * w 1 * inner ℝ w v| ≤ (C₀ * M / R) * ‖w‖ ^ 2 := by
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  have hw1 : |w 1| ≤ ‖w‖ := by
    have h := PiLp.norm_apply_le w 1
    rwa [Real.norm_eq_abs] at h
  have hinner : |inner ℝ w v| ≤ ‖w‖ * M :=
    (abs_real_inner_le_norm w v).trans (mul_le_mul_of_nonneg_left hv hn)
  rw [abs_mul, abs_mul]
  calc |d| * |w 1| * |inner ℝ w v|
      ≤ (C₀ / R) * ‖w‖ * (‖w‖ * M) :=
        mul_le_mul (mul_le_mul hd hw1 (abs_nonneg _) (div_nonneg hC₀ hR.le)) hinner
          (abs_nonneg _) (mul_nonneg (div_nonneg hC₀ hR.le) hn)
    _ = (C₀ * M / R) * ‖w‖ ^ 2 := by ring

/-! ### Continuity -/

/-- Component of a `Vec`-valued function is `C^∞` when the function is. -/
theorem se_comp (u : Plane → Vec) (i : Fin 2) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun z => u z i) :=
  (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hu

/-- The `q`-derivative of a `C^∞` real function is `C¹`. -/
theorem se_pQ_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 (Cyl.partialQ f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]
    exact hf.of_le (by norm_num)
  exact Cyl.contDiff_partialQ (n := 1) h2

/-- The `η`-derivative of a `C^∞` real function is `C¹`. -/
theorem se_pE_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 (Cyl.partialEta f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]
    exact hf.of_le (by norm_num)
  exact Cyl.contDiff_partialEta (n := 1) h2

/-- The transport `(u·∇)v` of `C^∞` fields is continuous. -/
theorem se_bilin_cont {a b : Plane → Vec} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Continuous (fun z => bilinAdv a b z) := by
  have a0 : Continuous (fun z => a z 0) := (se_comp a 0 ha).continuous
  have a1 : Continuous (fun z => a z 1) := (se_comp a 1 ha).continuous
  have q0 : Continuous (fun z => Cyl.partialQ (fun w => b w 0) z) :=
    (se_pQ_cd (se_comp b 0 hb)).continuous
  have e0 : Continuous (fun z => Cyl.partialEta (fun w => b w 0) z) :=
    (se_pE_cd (se_comp b 0 hb)).continuous
  have q1 : Continuous (fun z => Cyl.partialQ (fun w => b w 1) z) :=
    (se_pQ_cd (se_comp b 1 hb)).continuous
  have e1 : Continuous (fun z => Cyl.partialEta (fun w => b w 1) z) :=
    (se_pE_cd (se_comp b 1 hb)).continuous
  unfold bilinAdv
  exact Train.toVecL.continuous.comp (((a0.mul q0).add (a1.mul e0)).prodMk
    ((a0.mul q1).add (a1.mul e1)))

/-- The gradient energy density `|∇u|²` of a `C^∞` field is continuous. -/
theorem se_grad_cont {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    Continuous (fun z => gradNormSq u z) := by
  have q0 : Continuous (fun z => Cyl.partialQ (fun w => u w 0) z) :=
    (se_pQ_cd (se_comp u 0 hu)).continuous
  have e0 : Continuous (fun z => Cyl.partialEta (fun w => u w 0) z) :=
    (se_pE_cd (se_comp u 0 hu)).continuous
  have q1 : Continuous (fun z => Cyl.partialQ (fun w => u w 1) z) :=
    (se_pQ_cd (se_comp u 1 hu)).continuous
  have e1 : Continuous (fun z => Cyl.partialEta (fun w => u w 1) z) :=
    (se_pE_cd (se_comp u 1 hu)).continuous
  unfold gradNormSq
  exact (((q0.pow 2).add (e0.pow 2)).add (q1.pow 2)).add (e1.pow 2)

/-! ### The target -/

/-- **`PartI:T05b/2/5`, target `StretchEstimate`.** -/
theorem stretchEstimate (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport)
    (hS : TrainSliceSmooth) (hE : DiffEnergyBound) : StretchEstimate := by
  unfold EtaCutoffFacts at hη
  obtain ⟨C₀, hC₀, hφ⟩ := hη
  unfold StretchEstimate
  intro ν c hν hc tr tr' S M hS0 hb hb'
  -- `M ≥ 0`, from `‖v(0, z)‖ ≤ M`
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) ((hb 0 ⟨le_rfl, hS0⟩).1 0)
  have hK0 : 0 ≤ 2 * M ^ 2 / ν + 8 * C₀ * M ^ 2 :=
    add_nonneg (div_nonneg (by positivity) hν.le)
      (mul_nonneg (mul_nonneg (by norm_num) hC₀) (sq_nonneg M))
  refine ⟨2 * M ^ 2 / ν + 8 * C₀ * M ^ 2, hK0, ?_⟩
  intro R hR s hs
  have hRpos : 0 < R := by linarith
  have hs0 : 0 ≤ s := hs.1
  obtain ⟨hφS, hφ01, -, hφ0, hφd⟩ := hφ R hR
  have hφC : Continuous (etaCutoff R) := hφS.continuous
  have hφz : Continuous fun z : Plane => etaCutoff R z.2 := hφC.comp continuous_snd
  -- `|φ'| ≤ C₀/R`, from `|φ'| ≤ (C₀/R)√φ` and `0 ≤ φ ≤ 1`
  have hd1 : ∀ z : Plane, |deriv (etaCutoff R) z.2| ≤ C₀ / R := by
    intro z
    have hs1 : Real.sqrt (etaCutoff R z.2) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (hφ01 z.2).2
      rwa [Real.sqrt_one] at h
    exact (hφd z.2).trans (mul_le_of_le_one_right (div_nonneg hC₀ hRpos.le) hs1)
  -- smoothness of the slices and of the difference `w = v - v'`
  have hvS : ContDiff ℝ ∞ (tr.v s) := (hS ν c tr s hs0).1
  have hv'S : ContDiff ℝ ∞ (tr'.v s) := (hS ν c tr' s hs0).1
  have hwS : ContDiff ℝ ∞ (diffV tr tr' s) := by
    unfold diffV
    exact hvS.sub hv'S
  have hwC : Continuous (diffV tr tr' s) := hwS.continuous
  have hv'C : Continuous (tr'.v s) := hv'S.continuous
  have hW1 : Continuous fun z : Plane => diffV tr tr' s z 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp hwC
  have hD : Continuous fun z : Plane => deriv (etaCutoff R) z.2 :=
    (hφS.continuous_deriv (by simp)).comp continuous_snd
  -- term 1: `2 ∫ φ' w₁ ⟨w, v'⟩`
  have hf1c : Continuous fun z : Plane =>
      deriv (etaCutoff R) z.2 * diffV tr tr' s z 1 * inner ℝ (diffV tr tr' s z) (tr'.v s z) :=
    (hD.mul hW1).mul (hwC.inner hv'C)
  have hf1zero : ∀ z : Plane, 2 * R ≤ |z.2| →
      deriv (etaCutoff R) z.2 * diffV tr tr' s z 1 * inner ℝ (diffV tr tr' s z) (tr'.v s z) = 0 := by
    intro z hz
    have h0 : deriv (etaCutoff R) z.2 = 0 := by
      have h := hφd z.2
      rw [hφ0 z.2 hz, Real.sqrt_zero, mul_zero] at h
      exact abs_nonpos_iff.mp h
    rw [h0]
    simp
  have hf1I : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * diffV tr tr' s z 1 * inner ℝ (diffV tr tr' s z) (tr'.v s z))
      (Cyl.cell c) :=
    hI c R hc hRpos _ hf1c hf1zero
  have hpt1 : ∀ z : Plane,
      deriv (etaCutoff R) z.2 * diffV tr tr' s z 1 * inner ℝ (diffV tr tr' s z) (tr'.v s z) ≤
        (C₀ * M / R) * ‖diffV tr tr' s z‖ ^ 2 := fun z =>
    (le_abs_self _).trans
      (se_term1_pt C₀ M R hC₀ hM0 hRpos (deriv (etaCutoff R) z.2) (hd1 z)
        (diffV tr tr' s z) (tr'.v s z) ((hb' s hs).1 z))
  have hmaj1 : IntegrableOn (fun z : Plane => (C₀ * M / R) * ‖diffV tr tr' s z‖ ^ 2)
      (Cyl.cell c) :=
    Integrable.const_mul (hE ν c hc tr tr' S M hb hb' s hs).1 _
  have hmono1 := integral_mono hf1I hmaj1 (fun z => hpt1 z)
  have hconst1 : ∫ z in Cyl.cell c, (C₀ * M / R) * ‖diffV tr tr' s z‖ ^ 2 =
      (C₀ * M / R) * ∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2 :=
    integral_const_mul (C₀ * M / R) (fun z : Plane => ‖diffV tr tr' s z‖ ^ 2)
  have hC1 : 0 ≤ C₀ * M / R := div_nonneg (mul_nonneg hC₀ hM0) hRpos.le
  have hI1 : (C₀ * M / R) * ∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2 ≤
      (C₀ * M / R) * (4 * M) :=
    mul_le_mul_of_nonneg_left (hE ν c hc tr tr' S M hb hb' s hs).2 hC1
  have h1 : ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * diffV tr tr' s z 1 *
      inner ℝ (diffV tr tr' s z) (tr'.v s z) ≤ (C₀ * M / R) * (4 * M) := by
    linarith [hmono1, hconst1, hI1]
  -- term 2: `2 ∫ φ ⟨(w·∇)w, v'⟩`
  have hBc : Continuous fun z : Plane => bilinAdv (diffV tr tr' s) (diffV tr tr' s) z :=
    se_bilin_cont hwS hwS
  have hf2c : Continuous fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z) :=
    hφz.mul (hBc.inner hv'C)
  have hf2zero : ∀ z : Plane, 2 * R ≤ |z.2| →
      etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z) = 0 := by
    intro z hz
    rw [hφ0 z.2 hz, zero_mul]
  have hf2I : IntegrableOn (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z))
      (Cyl.cell c) :=
    hI c R hc hRpos _ hf2c hf2zero
  have hgc : Continuous fun z : Plane => etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z :=
    hφz.mul (se_grad_cont hwS)
  have hgI : IntegrableOn (fun z : Plane => etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z)
      (Cyl.cell c) :=
    hI c R hc hRpos _ hgc (fun z hz => by simp [hφ0 z.2 hz])
  have hnc : Continuous fun z : Plane => etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2 :=
    hφz.mul (hwC.norm.pow 2)
  have hnI : IntegrableOn (fun z : Plane => etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2)
      (Cyl.cell c) :=
    hI c R hc hRpos _ hnc (fun z hz => by simp [hφ0 z.2 hz])
  have hpt2 : ∀ z : Plane,
      2 * (etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z)) ≤
        (ν / 2) * (etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z) +
          (2 * M ^ 2 / ν) * (etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2) := by
    intro z
    have hY := se_stretch_pt ν M hν hM0 (diffV tr tr' s) (tr'.v s) z ((hb' s hs).1 z)
    have h0 : 0 ≤ etaCutoff R z.2 := (hφ01 z.2).1
    calc 2 * (etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z))
        = etaCutoff R z.2 *
            (2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z)) := by ring
      _ ≤ etaCutoff R z.2 * ((ν / 2) * gradNormSq (diffV tr tr' s) z +
            (2 * M ^ 2 / ν) * ‖diffV tr tr' s z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hY h0
      _ = (ν / 2) * (etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z) +
            (2 * M ^ 2 / ν) * (etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2) := by ring
  have hLI : IntegrableOn (fun z : Plane =>
      2 * (etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z)))
      (Cyl.cell c) :=
    Integrable.const_mul hf2I 2
  have hRI : IntegrableOn (fun z : Plane =>
      (ν / 2) * (etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z) +
        (2 * M ^ 2 / ν) * (etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2)) (Cyl.cell c) :=
    Integrable.add (Integrable.const_mul hgI (ν / 2)) (Integrable.const_mul hnI (2 * M ^ 2 / ν))
  have hmono2 := integral_mono hLI hRI (fun z => hpt2 z)
  have eL : ∫ z in Cyl.cell c,
      2 * (etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z)) =
      2 * ∫ z in Cyl.cell c,
        etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z) :=
    integral_const_mul 2 (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z))
  have eR : ∫ z in Cyl.cell c,
      ((ν / 2) * (etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z) +
        (2 * M ^ 2 / ν) * (etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2)) =
      (ν / 2) * (∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z) +
        (2 * M ^ 2 / ν) * (∫ z in Cyl.cell c, etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2) := by
    rw [integral_add (Integrable.const_mul hgI (ν / 2)) (Integrable.const_mul hnI (2 * M ^ 2 / ν)),
      integral_const_mul, integral_const_mul]
  rw [eL, eR] at hmono2
  -- the unfolded quantities
  have hSR : stretchRhs tr tr' R s =
      2 * (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * diffV tr tr' s z 1 *
        inner ℝ (diffV tr tr' s z) (tr'.v s z)) +
      2 * (∫ z in Cyl.cell c,
        etaCutoff R z.2 * inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z)) :=
    rfl
  have hDd : cutoffDissipation tr tr' R s =
      ∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z :=
    rfl
  have hFe : cutoffEnergy tr tr' R s =
      ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2 :=
    rfl
  have hF0 : 0 ≤ ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2 := by
    rw [← hFe]
    exact cutoffEnergy_nonneg tr tr' R s
  rw [hSR, hDd, hFe]
  -- the constants
  have hsqR : Real.sqrt R ≤ R := by
    have h1' : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
    have h2' : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hRpos.le
    nlinarith [Real.sqrt_nonneg R]
  have hsqpos : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
  have hA : 2 * ((C₀ * M / R) * (4 * M)) ≤ (8 * C₀ * M ^ 2) / Real.sqrt R := by
    have e : 2 * ((C₀ * M / R) * (4 * M)) = (8 * C₀ * M ^ 2) / R := by ring
    rw [e]
    exact div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by norm_num) hC₀) (sq_nonneg M)) hsqpos hsqR
  have hKs : (2 * M ^ 2 / ν + 8 * C₀ * M ^ 2) / Real.sqrt R =
      (2 * M ^ 2 / ν) / Real.sqrt R + (8 * C₀ * M ^ 2) / Real.sqrt R := add_div _ _ _
  have hKF : (2 * M ^ 2 / ν + 8 * C₀ * M ^ 2) *
      (∫ z in Cyl.cell c, etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2) =
      (2 * M ^ 2 / ν) * (∫ z in Cyl.cell c, etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2) +
      (8 * C₀ * M ^ 2) * (∫ z in Cyl.cell c, etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2) :=
    add_mul _ _ _
  have hQs : 0 ≤ (2 * M ^ 2 / ν) / Real.sqrt R :=
    div_nonneg (div_nonneg (by positivity) hν.le) hsqpos.le
  have hTF : 0 ≤ (8 * C₀ * M ^ 2) *
      (∫ z in Cyl.cell c, etaCutoff R z.2 * ‖diffV tr tr' s z‖ ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀) (sq_nonneg M)) hF0
  linarith [hmono2, h1, hA, hKs, hKF, hQs, hTF]

end UnforcedLeray.Short.PartI
