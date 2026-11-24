import UnforcedLeray.Short.PartI.Sub.T02_3_10
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, leaf `EbPressureIdentity`: `ebPressureIdentity`

Source of record: `the November 2 reference manuscript`, lines 276-282 (the
finite-energy solution and the velocity energy identities used by the cutoff energy method).

Target (`Short/PartI/Sub/T02_3_10.lean`, `EbPressureIdentity`): for a classical solution `(v, p)`
on `[0, T]` with `0 < c`, every `R ≥ 1` and every `s ∈ [0, T]`,
`ebPres c v p R s = ebPresRhs c v p R s`, that is
`-2 ∫_cell φ ⟨v, ∇p⟩ = 2 ∫_cell φ' p v_η`, where `φ = etaCutoff R`.

## Mathematics

Put `G_q = φ p v_0` and `G_η = φ p v_η`. The product rule gives, at every point,

    ∂_q G_q + ∂_η G_η = φ ⟨v, ∇p⟩ + φ' p v_η + φ p (∂_q v_0 + ∂_η v_η).

The last bracket is `div v = 0`, so `∂_q G_q + ∂_η G_η = φ ⟨v, ∇p⟩ + φ' p v_η`.
Both fluxes are `c`-periodic in `q` (by `periodic_p`, `periodic_v`), are `C^∞` (by `EbSliceSmooth`),
and vanish for `2R ≤ |η|` (where `φ = φ' = 0`). `CellDerivZero` gives zero integral for each
partial derivative, and `CellIntegrableOfSupport` gives integrability of all four integrands.
Hence `∫ φ ⟨v, ∇p⟩ = -∫ φ' p v_η`, which is the claim after multiplying by `-2`.

## Layout

The `ebPr_*` helpers give the calculus facts (components, partials of lines, continuity of the
gradient, the inner product with a gradient). `ebPrGq`, `ebPrGe` are the two fluxes. The main
theorem combines them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Calculus helpers -/

theorem ebPr_cd2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Plane → E}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  hf.of_le (by norm_num)

theorem ebPr_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Plane → E}
    (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  (ebPr_cd2 hf).differentiable (by norm_num)

/-- The `i`-th coordinate of a `C^n` vector field is `C^n`. -/
theorem ebPr_comp {u : Plane → Vec} (i : Fin 2) {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun x => u x i) :=
  (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) i)).comp hu

/-- `∂_q f` of a `C^∞` function is `C^1`. -/
theorem ebPr_pQ_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 (Cyl.partialQ f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact ebPr_cd2 hf
  exact Cyl.contDiff_partialQ (n := 1) h2

/-- `∂_η f` of a `C^∞` function is `C^1`. -/
theorem ebPr_pE_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 (Cyl.partialEta f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact ebPr_cd2 hf
  exact Cyl.contDiff_partialEta (n := 1) h2

/-- The `q`-line derivative of a differentiable function, at the point `z`. -/
theorem ebPr_line_q {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : Plane) :
    HasDerivAt (fun q : ℝ => f (q, z.2)) (Cyl.partialQ f z) z.1 :=
  ((hf (z.1, z.2)).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))).hasDerivAt

/-- The `η`-line derivative of a differentiable function, at the point `z`. -/
theorem ebPr_line_e {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : Plane) :
    HasDerivAt (fun η : ℝ => f (z.1, η)) (Cyl.partialEta f z) z.2 :=
  ((hf (z.1, z.2)).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)).hasDerivAt

/-- Continuity of the gradient of a `C^∞` function. -/
theorem ebPr_gradS_cont {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun z => Train.gradS f z) := by
  unfold Train.gradS
  exact Train.toVecL.continuous.comp
    ((ebPr_pQ_cd hf).continuous.prodMk (ebPr_pE_cd hf).continuous)

/-- The inner product with a gradient, in coordinates. -/
theorem ebPr_inner_gradS (u : Vec) (f : Plane → ℝ) (z : Plane) :
    inner ℝ u (Train.gradS f z) = u 0 * Cyl.partialQ f z + u 1 * Cyl.partialEta f z := by
  unfold Train.gradS
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Train.toVec_zero, Train.toVec_one,
    RCLike.inner_apply, conj_trivial]
  try ring

/-! ### The fluxes `G_q = φ p v_0` and `G_η = φ p v_η` -/

/-- The `q`-flux of the pressure term: `G_q(z) = φ_R(z_η) p(z) v_0(z)`. -/
def ebPrGq (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * p s z * v s z 0

/-- The `η`-flux of the pressure term: `G_η(z) = φ_R(z_η) p(z) v_1(z)`. -/
def ebPrGe (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * p s z * v s z 1

/-- `∂_q G_q` by the product rule (`φ` is independent of `q`). -/
theorem ebPr_pQ_Gq (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (R s : ℝ)
    (hP : Differentiable ℝ (p s)) (hW : Differentiable ℝ (fun x => v s x 0)) (z : Plane) :
    Cyl.partialQ (ebPrGq v p R s) z =
      etaCutoff R z.2 * Cyl.partialQ (p s) z * v s z 0 +
        etaCutoff R z.2 * p s z * Cyl.partialQ (fun x => v s x 0) z := by
  have hd : HasDerivAt (fun q : ℝ => ebPrGq v p R s (q, z.2))
      (etaCutoff R z.2 * Cyl.partialQ (p s) z * v s z 0 +
        etaCutoff R z.2 * p s z * Cyl.partialQ (fun x => v s x 0) z) z.1 :=
    ((ebPr_line_q hP z).const_mul (etaCutoff R z.2)).mul (ebPr_line_q hW z)
  exact hd.deriv

/-- `∂_η G_η` by the product rule (`φ` depends on `η`). -/
theorem ebPr_pE_Ge (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (R s : ℝ)
    (hφ : Differentiable ℝ (etaCutoff R)) (hP : Differentiable ℝ (p s))
    (hW : Differentiable ℝ (fun x => v s x 1)) (z : Plane) :
    Cyl.partialEta (ebPrGe v p R s) z =
      (deriv (etaCutoff R) z.2 * p s z + etaCutoff R z.2 * Cyl.partialEta (p s) z) * v s z 1 +
        etaCutoff R z.2 * p s z * Cyl.partialEta (fun x => v s x 1) z := by
  have hd : HasDerivAt (fun η : ℝ => ebPrGe v p R s (z.1, η))
      ((deriv (etaCutoff R) z.2 * p s z + etaCutoff R z.2 * Cyl.partialEta (p s) z) * v s z 1 +
        etaCutoff R z.2 * p s z * Cyl.partialEta (fun x => v s x 1) z) z.2 :=
    (((hφ z.2).hasDerivAt).mul (ebPr_line_e hP z)).mul (ebPr_line_e hW z)
  exact hd.deriv

/-! ### The theorem -/

/-- **Leaf `EbPressureIdentity`** (`Short/PartI/Sub/T02_3_10.lean`): `T_pres = 2 ∫ φ' p v_η`,
from the cell integration by parts of the fluxes `φ p v_0` and `φ p v_η` (source lines 276-282). -/
theorem ebPressureIdentity : EtaCutoffFacts → CellIntegrableOfSupport → CellDerivZero →
    EbSliceSmooth → EbPressureIdentity := by
  intro hη hI hZ hS ν c T v p hc hcl R hR s hs
  unfold EtaCutoffFacts at hη
  obtain ⟨_C₀, -, hcut⟩ := hη
  obtain ⟨hφS, -, -, hφ0, hφd⟩ := hcut R hR
  have hRpos : 0 < R := by linarith
  -- the derivative of the cutoff vanishes where the cutoff does
  have hsuppD : ∀ z : Plane, 2 * R ≤ |z.2| → deriv (etaCutoff R) z.2 = 0 := by
    intro z hz
    have h := hφd z.2
    rw [hφ0 z.2 hz, Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  -- smoothness of the slices at age `s`
  obtain ⟨hv, hp⟩ := hS ν c T v p hcl s hs
  have hsnd : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2) := hφS.comp contDiff_snd
  -- periodicity of the fluxes
  have hperQ : Cyl.IsPeriodic c (ebPrGq v p R s) := by
    intro z
    show etaCutoff R z.2 * p s (z.1 + c, z.2) * v s (z.1 + c, z.2) 0 =
      etaCutoff R z.2 * p s z * v s z 0
    rw [hcl.periodic_p s hs z, hcl.periodic_v s hs z]
  have hperE : Cyl.IsPeriodic c (ebPrGe v p R s) := by
    intro z
    show etaCutoff R z.2 * p s (z.1 + c, z.2) * v s (z.1 + c, z.2) 1 =
      etaCutoff R z.2 * p s z * v s z 1
    rw [hcl.periodic_p s hs z, hcl.periodic_v s hs z]
  -- the fluxes vanish for `2R ≤ |η|`
  have hsuppQ : ∀ z : Plane, 2 * R ≤ |z.2| → ebPrGq v p R s z = 0 := by
    intro z hz
    simp [ebPrGq, hφ0 z.2 hz]
  have hsuppE : ∀ z : Plane, 2 * R ≤ |z.2| → ebPrGe v p R s z = 0 := by
    intro z hz
    simp [ebPrGe, hφ0 z.2 hz]
  -- smoothness of the fluxes
  have hGqS : ContDiff ℝ ∞ (ebPrGq v p R s) := (hsnd.mul hp).mul (ebPr_comp 0 hv)
  have hGeS : ContDiff ℝ ∞ (ebPrGe v p R s) := (hsnd.mul hp).mul (ebPr_comp 1 hv)
  have hGq1 : ContDiff ℝ 1 (ebPrGq v p R s) := hGqS.of_le (by norm_num)
  have hGe1 : ContDiff ℝ 1 (ebPrGe v p R s) := hGeS.of_le (by norm_num)
  -- differentiability and continuity of the basic factors
  have hPdiff : Differentiable ℝ (p s) := ebPr_diff hp
  have hW0diff : Differentiable ℝ (fun x => v s x 0) := ebPr_diff (ebPr_comp 0 hv)
  have hW1diff : Differentiable ℝ (fun x => v s x 1) := ebPr_diff (ebPr_comp 1 hv)
  have hφdiff : Differentiable ℝ (etaCutoff R) := hφS.differentiable (by norm_num)
  have hφC : Continuous (fun z : Plane => etaCutoff R z.2) := hφS.continuous.comp continuous_snd
  have hDφC : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    (hφS.continuous_deriv (by simp)).comp continuous_snd
  have hPC : Continuous (p s) := hp.continuous
  have hW1C : Continuous (fun z : Plane => v s z 1) := (ebPr_comp 1 hv).continuous
  have hWC : Continuous (v s) := hv.continuous
  -- the solenoidal condition
  have hdiv : ∀ z : Plane, Cyl.partialQ (fun x => v s x 0) z +
      Cyl.partialEta (fun x => v s x 1) z = 0 := by
    intro z
    have h := hcl.solenoidal s hs z
    unfold Cyl.divergence at h
    exact h
  -- the pointwise identity `∂_q G_q + ∂_η G_η = φ ⟨v, ∇p⟩ + φ' p v_η`
  have hpt : ∀ z : Plane, Cyl.partialQ (ebPrGq v p R s) z + Cyl.partialEta (ebPrGe v p R s) z =
      etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z) +
        deriv (etaCutoff R) z.2 * p s z * v s z 1 := by
    intro z
    rw [ebPr_pQ_Gq v p R s hPdiff hW0diff z, ebPr_pE_Ge v p R s hφdiff hPdiff hW1diff z,
      ebPr_inner_gradS]
    linear_combination (etaCutoff R z.2 * p s z) * hdiv z
  -- the partial derivatives vanish for `2R ≤ |η|`
  have hQzero : ∀ z : Plane, 2 * R ≤ |z.2| → Cyl.partialQ (ebPrGq v p R s) z = 0 := by
    intro z hz
    rw [ebPr_pQ_Gq v p R s hPdiff hW0diff z, hφ0 z.2 hz]
    ring
  have hEzero : ∀ z : Plane, 2 * R ≤ |z.2| → Cyl.partialEta (ebPrGe v p R s) z = 0 := by
    intro z hz
    rw [ebPr_pE_Ge v p R s hφdiff hPdiff hW1diff z, hφ0 z.2 hz, hsuppD z hz]
    ring
  -- integrability on the cell
  have iQ : IntegrableOn (fun z : Plane => Cyl.partialQ (ebPrGq v p R s) z) (Cyl.cell c) :=
    hI c R hc hRpos _ (ebPr_pQ_cd hGqS).continuous (fun z hz => hQzero z hz)
  have iE : IntegrableOn (fun z : Plane => Cyl.partialEta (ebPrGe v p R s) z) (Cyl.cell c) :=
    hI c R hc hRpos _ (ebPr_pE_cd hGeS).continuous (fun z hz => hEzero z hz)
  have iF1 : IntegrableOn (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)) (Cyl.cell c) :=
    hI c R hc hRpos _ (hφC.mul (hWC.inner (ebPr_gradS_cont hp)))
      (fun z hz => by simp [hφ0 z.2 hz])
  have iF2 : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * p s z * v s z 1) (Cyl.cell c) :=
    hI c R hc hRpos _ ((hDφC.mul hPC).mul hW1C) (fun z hz => by simp [hsuppD z hz])
  -- cell integration by parts
  have hZq := hZ c R hc hRpos (ebPrGq v p R s) hGq1 hperQ hsuppQ
  have hZe := hZ c R hc hRpos (ebPrGe v p R s) hGe1 hperE hsuppE
  have hsplit1 : ∫ z in Cyl.cell c, (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z) +
      deriv (etaCutoff R) z.2 * p s z * v s z 1) =
      (∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)) +
        ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * p s z * v s z 1 :=
    integral_add iF1 iF2
  have hsplit2 : ∫ z in Cyl.cell c, (Cyl.partialQ (ebPrGq v p R s) z +
      Cyl.partialEta (ebPrGe v p R s) z) =
      (∫ z in Cyl.cell c, Cyl.partialQ (ebPrGq v p R s) z) +
        ∫ z in Cyl.cell c, Cyl.partialEta (ebPrGe v p R s) z :=
    integral_add iQ iE
  have hcongr : ∫ z in Cyl.cell c, (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z) +
      deriv (etaCutoff R) z.2 * p s z * v s z 1) =
      ∫ z in Cyl.cell c, (Cyl.partialQ (ebPrGq v p R s) z +
        Cyl.partialEta (ebPrGe v p R s) z) := by
    congr 1
    funext z
    exact (hpt z).symm
  have htot : (∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)) +
      (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * p s z * v s z 1) = 0 := by
    rw [← hsplit1, hcongr, hsplit2, hZq.1, hZe.2, add_zero]
  unfold ebPres ebPresRhs
  linarith

end UnforcedLeray.Short.PartI
