import UnforcedLeray.Short.PartI.Sub.T02_3_11
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T02/3/11`, leaf `CcPressureIdentity` (classical solutions)

Source of record: `the November 2 reference manuscript`, lines 276-288.

Target: `ccPressureIdentity (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport)
(hZ : CellDerivZero) (hS : CcSliceSmooth) : CcPressureIdentity` (`Short/PartI/Sub/T02_3_11.lean`).

Mathematics. Fix `R ≥ 1`, `s ∈ [0, T]`, put `w = v - v'`, `π = p - p'`, `φ = etaCutoff R`.
Both solutions are solenoidal, so `∂_q w_0 + ∂_η w_1 = 0`. With `G_q = φ π w_0` and
`G_η = φ π w_1`, at every point `∂_q G_q + ∂_η G_η = φ ⟨w, ∇π⟩ + φ' π w_1`. Cell integration
by parts (`CellDerivZero`) kills both integrals of partial derivatives, so
`∫ φ ⟨w, ∇π⟩ = -∫ φ' π w_1`, which is `ccPressure = ccPressureRhs`.

Each integrand is continuous and vanishes for `2R ≤ |η|`, hence is integrable on the cell by
`CellIntegrableOfSupport`. The `ccPI_*` helpers are the generic calculus facts of the proved
train analogue `Tasks/TrainCutoffEnergyProof/PressureIdentity.lean`, renamed; the flux helpers
`ccPIGq`, `ccPIGe` are defined from `ccDiffV`, `ccDiffP` instead of train fields.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Calculus helpers -/

section CcPICalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ccPI_cd2 {f : Plane → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  hf.of_le (by norm_num)

theorem ccPI_diff {f : Plane → E} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  (ccPI_cd2 hf).differentiable (by norm_num)

theorem ccPI_comp {u : Plane → Vec} (i : Fin 2) {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun x => u x i) :=
  (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) i)).comp hu

/-- Linearity of `∂_q` on a difference, pointwise. -/
theorem ccPI_pQ_sub {f g : Plane → E} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun x => f x - g x) z = Cyl.partialQ f z - Cyl.partialQ g z := by
  unfold Cyl.partialQ
  have h1 : DifferentiableAt ℝ (fun q : ℝ => f (q, z.2)) z.1 :=
    (hf (z.1, z.2)).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))
  have h2 : DifferentiableAt ℝ (fun q : ℝ => g (q, z.2)) z.1 :=
    (hg (z.1, z.2)).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))
  exact deriv_sub h1 h2

/-- Linearity of `∂_η` on a difference, pointwise. -/
theorem ccPI_pE_sub {f g : Plane → E} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun x => f x - g x) z = Cyl.partialEta f z - Cyl.partialEta g z := by
  unfold Cyl.partialEta
  have h1 : DifferentiableAt ℝ (fun η : ℝ => f (z.1, η)) z.2 :=
    (hf (z.1, z.2)).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)
  have h2 : DifferentiableAt ℝ (fun η : ℝ => g (z.1, η)) z.2 :=
    (hg (z.1, z.2)).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)
  exact deriv_sub h1 h2

end CcPICalculus

/-- `∂_q f` of a `C^∞` function is `C^1`. -/
theorem ccPI_pQ_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 (Cyl.partialQ f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact ccPI_cd2 hf
  exact Cyl.contDiff_partialQ (n := 1) h2

/-- `∂_η f` of a `C^∞` function is `C^1`. -/
theorem ccPI_pE_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 (Cyl.partialEta f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact ccPI_cd2 hf
  exact Cyl.contDiff_partialEta (n := 1) h2

/-- The `q`-line derivative of a differentiable function, at the point `z`. -/
theorem ccPI_line_q {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : Plane) :
    HasDerivAt (fun q : ℝ => f (q, z.2)) (Cyl.partialQ f z) z.1 :=
  ((hf (z.1, z.2)).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))).hasDerivAt

/-- The `η`-line derivative of a differentiable function, at the point `z`. -/
theorem ccPI_line_e {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : Plane) :
    HasDerivAt (fun η : ℝ => f (z.1, η)) (Cyl.partialEta f z) z.2 :=
  ((hf (z.1, z.2)).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)).hasDerivAt

/-- Continuity of the gradient of a `C^∞` function. -/
theorem ccPI_gradS_cont {π : Plane → ℝ} (hπ : ContDiff ℝ ∞ π) :
    Continuous (fun z => Train.gradS π z) := by
  unfold Train.gradS
  exact Train.toVecL.continuous.comp
    ((ccPI_pQ_cd hπ).continuous.prodMk (ccPI_pE_cd hπ).continuous)

/-- The inner product with a gradient, in coordinates. -/
theorem ccPI_inner_gradS (u : Vec) (p : Plane → ℝ) (z : Plane) :
    inner ℝ u (Train.gradS p z) = u 0 * Cyl.partialQ p z + u 1 * Cyl.partialEta p z := by
  unfold Train.gradS
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Train.toVec_zero, Train.toVec_one,
    RCLike.inner_apply, conj_trivial]
  try ring

/-! ### The fluxes `G_q = φ π w_0` and `G_η = φ π w_1` -/

/-- The `q`-flux of the pressure term: `G_q(z) = φ_R(z_η) π(z) w_0(z)`. -/
def ccPIGq (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * ccDiffP p p' s z * ccDiffV v v' s z 0

/-- The `η`-flux of the pressure term: `G_η(z) = φ_R(z_η) π(z) w_1(z)`. -/
def ccPIGe (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1

/-- `∂_q G_q` by the product rule (`φ` is independent of `q`). -/
theorem ccPIGq_partialQ (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ) (R s : ℝ)
    (hP : Differentiable ℝ (ccDiffP p p' s)) (hW : Differentiable ℝ (fun x => ccDiffV v v' s x 0))
    (z : Plane) :
    Cyl.partialQ (ccPIGq v v' p p' R s) z =
      etaCutoff R z.2 * Cyl.partialQ (ccDiffP p p' s) z * ccDiffV v v' s z 0 +
        etaCutoff R z.2 * ccDiffP p p' s z * Cyl.partialQ (fun x => ccDiffV v v' s x 0) z := by
  have hd : HasDerivAt (fun q : ℝ => ccPIGq v v' p p' R s (q, z.2))
      (etaCutoff R z.2 * Cyl.partialQ (ccDiffP p p' s) z * ccDiffV v v' s z 0 +
        etaCutoff R z.2 * ccDiffP p p' s z * Cyl.partialQ (fun x => ccDiffV v v' s x 0) z) z.1 :=
    ((ccPI_line_q hP z).const_mul (etaCutoff R z.2)).mul (ccPI_line_q hW z)
  exact hd.deriv

/-- `∂_η G_η` by the product rule (`φ` depends on `η`). -/
theorem ccPIGe_partialEta (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ) (R s : ℝ)
    (hφ : Differentiable ℝ (etaCutoff R)) (hP : Differentiable ℝ (ccDiffP p p' s))
    (hW : Differentiable ℝ (fun x => ccDiffV v v' s x 1)) (z : Plane) :
    Cyl.partialEta (ccPIGe v v' p p' R s) z =
      (deriv (etaCutoff R) z.2 * ccDiffP p p' s z +
          etaCutoff R z.2 * Cyl.partialEta (ccDiffP p p' s) z) * ccDiffV v v' s z 1 +
        etaCutoff R z.2 * ccDiffP p p' s z * Cyl.partialEta (fun x => ccDiffV v v' s x 1) z := by
  have hd : HasDerivAt (fun η : ℝ => ccPIGe v v' p p' R s (z.1, η))
      ((deriv (etaCutoff R) z.2 * ccDiffP p p' s z +
          etaCutoff R z.2 * Cyl.partialEta (ccDiffP p p' s) z) * ccDiffV v v' s z 1 +
        etaCutoff R z.2 * ccDiffP p p' s z * Cyl.partialEta (fun x => ccDiffV v v' s x 1) z) z.2 :=
    (((hφ z.2).hasDerivAt).mul (ccPI_line_e hP z)).mul (ccPI_line_e hW z)
  exact hd.deriv

/-! ### The theorem -/

/-- **`PartI:T02/3/11`, leaf `CcPressureIdentity`.** Under the cutoff facts, the cell toolkit and
the smoothness of the classical slices, `T_pres = 2 ∫ φ' π w_η`
(`Short/PartI/Sub/T02_3_11.lean`, leaf `CcPressureIdentity`, source lines 276-288). -/
theorem ccPressureIdentity (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport)
    (hZ : CellDerivZero) (hS : CcSliceSmooth) : CcPressureIdentity := by
  intro ν c T M v v' p p' h R hR s hs
  have hc : 0 < c := by linarith [h.c_ge]
  have hRpos : 0 < R := by linarith
  unfold EtaCutoffFacts at hη
  obtain ⟨C₀, -, hcut⟩ := hη
  obtain ⟨hφS, -, -, hφ0, hφd⟩ := hcut R hR
  -- the derivative of the cutoff vanishes where the cutoff does
  have hsuppD : ∀ z : Plane, 2 * R ≤ |z.2| → deriv (etaCutoff R) z.2 = 0 := by
    intro z hz
    have hd' := hφd z.2
    rw [hφ0 z.2 hz, Real.sqrt_zero, mul_zero] at hd'
    exact abs_nonpos_iff.mp hd'
  -- smoothness of both solutions at time `s`
  obtain ⟨hv, hp⟩ := hS ν c T v p h.cl s hs
  obtain ⟨hv', hp'⟩ := hS ν c T v' p' h.cl' s hs
  have hwd : ContDiff ℝ ∞ (ccDiffV v v' s) := hv.sub hv'
  have hPd : ContDiff ℝ ∞ (ccDiffP p p' s) := hp.sub hp'
  -- periodicity of the differences
  have hpP : ∀ z : Plane, ccDiffP p p' s (z.1 + c, z.2) = ccDiffP p p' s z := by
    intro z
    simp only [ccDiffP, h.cl.periodic_p s hs z, h.cl'.periodic_p s hs z]
  have hpV : ∀ z : Plane, ccDiffV v v' s (z.1 + c, z.2) = ccDiffV v v' s z := by
    intro z
    simp only [ccDiffV, h.cl.periodic_v s hs z, h.cl'.periodic_v s hs z]
  have hperQ : Cyl.IsPeriodic c (ccPIGq v v' p p' R s) := by
    intro z
    show etaCutoff R z.2 * ccDiffP p p' s (z.1 + c, z.2) * ccDiffV v v' s (z.1 + c, z.2) 0 =
      etaCutoff R z.2 * ccDiffP p p' s z * ccDiffV v v' s z 0
    rw [hpP z, hpV z]
  have hperE : Cyl.IsPeriodic c (ccPIGe v v' p p' R s) := by
    intro z
    show etaCutoff R z.2 * ccDiffP p p' s (z.1 + c, z.2) * ccDiffV v v' s (z.1 + c, z.2) 1 =
      etaCutoff R z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1
    rw [hpP z, hpV z]
  -- the fluxes vanish for `2R ≤ |η|`
  have hsuppQ : ∀ z : Plane, 2 * R ≤ |z.2| → ccPIGq v v' p p' R s z = 0 := by
    intro z hz
    simp [ccPIGq, hφ0 z.2 hz]
  have hsuppE : ∀ z : Plane, 2 * R ≤ |z.2| → ccPIGe v v' p p' R s z = 0 := by
    intro z hz
    simp [ccPIGe, hφ0 z.2 hz]
  -- smoothness of the fluxes
  have hsnd : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2) := hφS.comp contDiff_snd
  have hGqS : ContDiff ℝ ∞ (ccPIGq v v' p p' R s) := (hsnd.mul hPd).mul (ccPI_comp 0 hwd)
  have hGeS : ContDiff ℝ ∞ (ccPIGe v v' p p' R s) := (hsnd.mul hPd).mul (ccPI_comp 1 hwd)
  have hGq1 : ContDiff ℝ 1 (ccPIGq v v' p p' R s) := hGqS.of_le (by norm_num)
  have hGe1 : ContDiff ℝ 1 (ccPIGe v v' p p' R s) := hGeS.of_le (by norm_num)
  -- differentiability
  have hPdiff : Differentiable ℝ (ccDiffP p p' s) := ccPI_diff hPd
  have hW0diff : Differentiable ℝ (fun x => ccDiffV v v' s x 0) := ccPI_diff (ccPI_comp 0 hwd)
  have hW1diff : Differentiable ℝ (fun x => ccDiffV v v' s x 1) := ccPI_diff (ccPI_comp 1 hwd)
  have hφdiff : Differentiable ℝ (etaCutoff R) := hφS.differentiable (by norm_num)
  -- continuity of the basic factors
  have hφC : Continuous (fun z : Plane => etaCutoff R z.2) := hφS.continuous.comp continuous_snd
  have hDφC : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    (hφS.continuous_deriv (by simp)).comp continuous_snd
  have hPC : Continuous (ccDiffP p p' s) := hPd.continuous
  have hW1C : Continuous (fun z : Plane => ccDiffV v v' s z 1) := (ccPI_comp 1 hwd).continuous
  have hWC : Continuous (ccDiffV v v' s) := hwd.continuous
  -- the solenoidal condition for the difference `w`
  have hdiv : ∀ z : Plane, Cyl.partialQ (fun x => ccDiffV v v' s x 0) z +
      Cyl.partialEta (fun x => ccDiffV v v' s x 1) z = 0 := by
    intro z
    have e0 : (fun x => ccDiffV v v' s x 0) = fun x => v s x 0 - v' s x 0 := by
      funext x; simp [ccDiffV]
    have e1 : (fun x => ccDiffV v v' s x 1) = fun x => v s x 1 - v' s x 1 := by
      funext x; simp [ccDiffV]
    rw [e0, e1, ccPI_pQ_sub (ccPI_diff (ccPI_comp 0 hv)) (ccPI_diff (ccPI_comp 0 hv')) z,
      ccPI_pE_sub (ccPI_diff (ccPI_comp 1 hv)) (ccPI_diff (ccPI_comp 1 hv')) z]
    have s1 := h.cl.solenoidal s hs z
    have s2 := h.cl'.solenoidal s hs z
    unfold Cyl.divergence at s1 s2
    linarith
  -- the pointwise identity `∂_q G_q + ∂_η G_η = φ ⟨w, ∇π⟩ + φ' π w_η`
  have hpt : ∀ z : Plane, Cyl.partialQ (ccPIGq v v' p p' R s) z +
      Cyl.partialEta (ccPIGe v v' p p' R s) z =
        etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (Train.gradS (ccDiffP p p' s) z) +
          deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1 := by
    intro z
    rw [ccPIGq_partialQ v v' p p' R s hPdiff hW0diff z,
      ccPIGe_partialEta v v' p p' R s hφdiff hPdiff hW1diff z, ccPI_inner_gradS]
    linear_combination (etaCutoff R z.2 * ccDiffP p p' s z) * hdiv z
  -- the partial derivatives vanish for `2R ≤ |η|`
  have hQzero : ∀ z : Plane, 2 * R ≤ |z.2| → Cyl.partialQ (ccPIGq v v' p p' R s) z = 0 := by
    intro z hz
    rw [ccPIGq_partialQ v v' p p' R s hPdiff hW0diff z, hφ0 z.2 hz]
    ring
  have hEzero : ∀ z : Plane, 2 * R ≤ |z.2| → Cyl.partialEta (ccPIGe v v' p p' R s) z = 0 := by
    intro z hz
    rw [ccPIGe_partialEta v v' p p' R s hφdiff hPdiff hW1diff z, hφ0 z.2 hz, hsuppD z hz]
    ring
  -- integrability
  have iQ : IntegrableOn (fun z : Plane => Cyl.partialQ (ccPIGq v v' p p' R s) z) (Cyl.cell c) :=
    hI c R hc hRpos _ (ccPI_pQ_cd hGqS).continuous (fun z hz => hQzero z hz)
  have iE : IntegrableOn (fun z : Plane => Cyl.partialEta (ccPIGe v v' p p' R s) z) (Cyl.cell c) :=
    hI c R hc hRpos _ (ccPI_pE_cd hGeS).continuous (fun z hz => hEzero z hz)
  have iF1 : IntegrableOn (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (Train.gradS (ccDiffP p p' s) z)) (Cyl.cell c) :=
    hI c R hc hRpos _ (hφC.mul (hWC.inner (ccPI_gradS_cont hPd)))
      (fun z hz => by simp [hφ0 z.2 hz])
  have iF2 : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1) (Cyl.cell c) :=
    hI c R hc hRpos _ ((hDφC.mul hPC).mul hW1C) (fun z hz => by simp [hsuppD z hz])
  -- cell integration by parts
  have hZq := hZ c R hc hRpos (ccPIGq v v' p p' R s) hGq1 hperQ hsuppQ
  have hZe := hZ c R hc hRpos (ccPIGe v v' p p' R s) hGe1 hperE hsuppE
  have hsplit1 : ∫ z in Cyl.cell c, (etaCutoff R z.2 *
        inner ℝ (ccDiffV v v' s z) (Train.gradS (ccDiffP p p' s) z) +
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1) =
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        inner ℝ (ccDiffV v v' s z) (Train.gradS (ccDiffP p p' s) z)) +
      ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1 :=
    integral_add iF1 iF2
  have hsplit2 : ∫ z in Cyl.cell c, (Cyl.partialQ (ccPIGq v v' p p' R s) z +
        Cyl.partialEta (ccPIGe v v' p p' R s) z) =
      (∫ z in Cyl.cell c, Cyl.partialQ (ccPIGq v v' p p' R s) z) +
        ∫ z in Cyl.cell c, Cyl.partialEta (ccPIGe v v' p p' R s) z :=
    integral_add iQ iE
  have hcongr : ∫ z in Cyl.cell c, (etaCutoff R z.2 *
        inner ℝ (ccDiffV v v' s z) (Train.gradS (ccDiffP p p' s) z) +
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1) =
      ∫ z in Cyl.cell c, (Cyl.partialQ (ccPIGq v v' p p' R s) z +
        Cyl.partialEta (ccPIGe v v' p p' R s) z) := by
    congr 1
    funext z
    exact (hpt z).symm
  have htot : (∫ z in Cyl.cell c, etaCutoff R z.2 *
        inner ℝ (ccDiffV v v' s z) (Train.gradS (ccDiffP p p' s) z)) +
      (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1) = 0 := by
    rw [← hsplit1, hcongr, hsplit2, hZq.1, hZe.2, add_zero]
  unfold ccPressure ccPressureRhs
  linarith

end UnforcedLeray.Short.PartI
