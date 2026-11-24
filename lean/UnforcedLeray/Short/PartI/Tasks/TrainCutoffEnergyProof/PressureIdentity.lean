import UnforcedLeray.Short.PartI.Sub.T05b_2
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T05b/2`: the pressure identity `PressureIdentity`

Source of record: `the November 2 reference manuscript`, lines 276-288.

Target: `pressureIdentity (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport)
(hZ : CellDerivZero) (hS : TrainSliceSmooth) : PressureIdentity` (`Short/PartI/Sub/T05b_2.lean`,
leaf `PressureIdentity`).

Mathematics. Fix `s ≥ 0`, `R ≥ 1`, put `w = v - v'`, `π = p - p'`, `φ = etaCutoff R`. Both trains are
solenoidal, so `∂_q w_0 + ∂_η w_1 = 0`. With `G_q = φ π w_0` and `G_η = φ π w_1`, at every point
`∂_q G_q + ∂_η G_η = φ ⟨w, ∇π⟩ + φ' π w_1`. Cell integration by parts (`CellDerivZero`) kills the
two integrals of partial derivatives, so `∫ φ ⟨w, ∇π⟩ = -∫ φ' π w_1` and
`cutoffPressure = 2 ∫ φ' π w_1 = pressureRhs`.

Each integrand is continuous and vanishes for `2R ≤ |η|` (there `φ = φ' = 0`), so it is
integrable on the cell by `CellIntegrableOfSupport`.

Proof layout. `prId_*` helpers give the calculus facts (partials of products, linearity,
continuity, the inner product with a gradient). The fluxes `prIdGq`, `prIdGe` have explicit
partial-derivative formulas. The main theorem combines them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Calculus helpers -/

section PrIdCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem prId_cd2 {f : Plane → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  hf.of_le (by norm_num)

theorem prId_diff {f : Plane → E} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  (prId_cd2 hf).differentiable (by norm_num)

theorem prId_comp {u : Plane → Vec} (i : Fin 2) {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun x => u x i) :=
  (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) i)).comp hu

/-- Linearity of `∂_q` on a difference, pointwise. -/
theorem prId_pQ_sub {f g : Plane → E} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun x => f x - g x) z = Cyl.partialQ f z - Cyl.partialQ g z := by
  unfold Cyl.partialQ
  have h1 : DifferentiableAt ℝ (fun q : ℝ => f (q, z.2)) z.1 :=
    (hf (z.1, z.2)).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))
  have h2 : DifferentiableAt ℝ (fun q : ℝ => g (q, z.2)) z.1 :=
    (hg (z.1, z.2)).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))
  exact deriv_sub h1 h2

/-- Linearity of `∂_η` on a difference, pointwise. -/
theorem prId_pE_sub {f g : Plane → E} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun x => f x - g x) z = Cyl.partialEta f z - Cyl.partialEta g z := by
  unfold Cyl.partialEta
  have h1 : DifferentiableAt ℝ (fun η : ℝ => f (z.1, η)) z.2 :=
    (hf (z.1, z.2)).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)
  have h2 : DifferentiableAt ℝ (fun η : ℝ => g (z.1, η)) z.2 :=
    (hg (z.1, z.2)).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)
  exact deriv_sub h1 h2

end PrIdCalculus

/-- `∂_q f` of a `C^∞` function is `C^1`. -/
theorem prId_pQ_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 (Cyl.partialQ f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact prId_cd2 hf
  exact Cyl.contDiff_partialQ (n := 1) h2

/-- `∂_η f` of a `C^∞` function is `C^1`. -/
theorem prId_pE_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 (Cyl.partialEta f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact prId_cd2 hf
  exact Cyl.contDiff_partialEta (n := 1) h2

/-- The `q`-line derivative of a differentiable function, at the point `z`. -/
theorem prId_line_q {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : Plane) :
    HasDerivAt (fun q : ℝ => f (q, z.2)) (Cyl.partialQ f z) z.1 :=
  ((hf (z.1, z.2)).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))).hasDerivAt

/-- The `η`-line derivative of a differentiable function, at the point `z`. -/
theorem prId_line_e {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : Plane) :
    HasDerivAt (fun η : ℝ => f (z.1, η)) (Cyl.partialEta f z) z.2 :=
  ((hf (z.1, z.2)).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)).hasDerivAt

/-- Continuity of the gradient of a `C^∞` function. -/
theorem prId_gradS_cont {π : Plane → ℝ} (hπ : ContDiff ℝ ∞ π) :
    Continuous (fun z => Train.gradS π z) := by
  unfold Train.gradS
  exact Train.toVecL.continuous.comp
    ((prId_pQ_cd hπ).continuous.prodMk (prId_pE_cd hπ).continuous)

/-- The inner product with a gradient, in coordinates. -/
theorem prId_inner_gradS (u : Vec) (p : Plane → ℝ) (z : Plane) :
    inner ℝ u (Train.gradS p z) = u 0 * Cyl.partialQ p z + u 1 * Cyl.partialEta p z := by
  unfold Train.gradS
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Train.toVec_zero, Train.toVec_one,
    RCLike.inner_apply, conj_trivial]
  try ring

/-! ### The fluxes `G_q = φ π w_0` and `G_η = φ π w_1` -/

/-- The `q`-flux of the pressure term: `G_q(z) = φ_R(z_η) π(z) w_0(z)`. -/
def prIdGq {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * diffP tr tr' s z * diffV tr tr' s z 0

/-- The `η`-flux of the pressure term: `G_η(z) = φ_R(z_η) π(z) w_1(z)`. -/
def prIdGe {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * diffP tr tr' s z * diffV tr tr' s z 1

/-- `∂_q G_q` by the product rule (`φ` is independent of `q`). -/
theorem prIdGq_partialQ {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ)
    (hP : Differentiable ℝ (diffP tr tr' s)) (hW : Differentiable ℝ (fun x => diffV tr tr' s x 0))
    (z : Plane) :
    Cyl.partialQ (prIdGq tr tr' R s) z =
      etaCutoff R z.2 * Cyl.partialQ (diffP tr tr' s) z * diffV tr tr' s z 0 +
        etaCutoff R z.2 * diffP tr tr' s z * Cyl.partialQ (fun x => diffV tr tr' s x 0) z := by
  have hd : HasDerivAt (fun q : ℝ => prIdGq tr tr' R s (q, z.2))
      (etaCutoff R z.2 * Cyl.partialQ (diffP tr tr' s) z * diffV tr tr' s z 0 +
        etaCutoff R z.2 * diffP tr tr' s z * Cyl.partialQ (fun x => diffV tr tr' s x 0) z) z.1 :=
    ((prId_line_q hP z).const_mul (etaCutoff R z.2)).mul (prId_line_q hW z)
  exact hd.deriv

/-- `∂_η G_η` by the product rule (`φ` depends on `η`). -/
theorem prIdGe_partialEta {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ)
    (hφ : Differentiable ℝ (etaCutoff R)) (hP : Differentiable ℝ (diffP tr tr' s))
    (hW : Differentiable ℝ (fun x => diffV tr tr' s x 1)) (z : Plane) :
    Cyl.partialEta (prIdGe tr tr' R s) z =
      (deriv (etaCutoff R) z.2 * diffP tr tr' s z +
          etaCutoff R z.2 * Cyl.partialEta (diffP tr tr' s) z) * diffV tr tr' s z 1 +
        etaCutoff R z.2 * diffP tr tr' s z * Cyl.partialEta (fun x => diffV tr tr' s x 1) z := by
  have hd : HasDerivAt (fun η : ℝ => prIdGe tr tr' R s (z.1, η))
      ((deriv (etaCutoff R) z.2 * diffP tr tr' s z +
          etaCutoff R z.2 * Cyl.partialEta (diffP tr tr' s) z) * diffV tr tr' s z 1 +
        etaCutoff R z.2 * diffP tr tr' s z * Cyl.partialEta (fun x => diffV tr tr' s x 1) z) z.2 :=
    (((hφ z.2).hasDerivAt).mul (prId_line_e hP z)).mul (prId_line_e hW z)
  exact hd.deriv

/-! ### The theorem -/

/-- **`PartI:T05b/2`, `PressureIdentity`.** Under the cutoff facts, the toolkit leaves and the
smoothness of trains, `T_pres = 2 ∫ φ' π w_η` (`Short/PartI/Sub/T05b_2.lean`, leaf
`PressureIdentity`, source lines 276-288). -/
theorem pressureIdentity (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport)
    (hZ : CellDerivZero) (hS : TrainSliceSmooth) : PressureIdentity := by
  intro ν c hν hc tr tr' R hR s hs0
  unfold EtaCutoffFacts at hη
  obtain ⟨C₀, -, hcut⟩ := hη
  obtain ⟨hφS, -, -, hφ0, hφd⟩ := hcut R hR
  have hRpos : 0 < R := by linarith
  -- the derivative of the cutoff vanishes where the cutoff does
  have hsuppD : ∀ z : Plane, 2 * R ≤ |z.2| → deriv (etaCutoff R) z.2 = 0 := by
    intro z hz
    have h := hφd z.2
    rw [hφ0 z.2 hz, Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  -- smoothness of both trains at age `s`
  obtain ⟨hv, hp⟩ := hS ν c tr s hs0
  obtain ⟨hv', hp'⟩ := hS ν c tr' s hs0
  have hwd : ContDiff ℝ ∞ (diffV tr tr' s) := hv.sub hv'
  have hPd : ContDiff ℝ ∞ (diffP tr tr' s) := hp.sub hp'
  -- periodicity of the differences
  have hpP : ∀ z : Plane, diffP tr tr' s (z.1 + c, z.2) = diffP tr tr' s z := by
    intro z
    simp only [diffP, tr.isTrain.periodic_p s hs0 z, tr'.isTrain.periodic_p s hs0 z]
  have hpV : ∀ z : Plane, diffV tr tr' s (z.1 + c, z.2) = diffV tr tr' s z := by
    intro z
    simp only [diffV, tr.isTrain.periodic_v s hs0 z, tr'.isTrain.periodic_v s hs0 z]
  have hperQ : Cyl.IsPeriodic c (prIdGq tr tr' R s) := by
    intro z
    show etaCutoff R z.2 * diffP tr tr' s (z.1 + c, z.2) * diffV tr tr' s (z.1 + c, z.2) 0 =
      etaCutoff R z.2 * diffP tr tr' s z * diffV tr tr' s z 0
    rw [hpP z, hpV z]
  have hperE : Cyl.IsPeriodic c (prIdGe tr tr' R s) := by
    intro z
    show etaCutoff R z.2 * diffP tr tr' s (z.1 + c, z.2) * diffV tr tr' s (z.1 + c, z.2) 1 =
      etaCutoff R z.2 * diffP tr tr' s z * diffV tr tr' s z 1
    rw [hpP z, hpV z]
  -- the fluxes vanish for `2R ≤ |η|`
  have hsuppQ : ∀ z : Plane, 2 * R ≤ |z.2| → prIdGq tr tr' R s z = 0 := by
    intro z hz
    simp [prIdGq, hφ0 z.2 hz]
  have hsuppE : ∀ z : Plane, 2 * R ≤ |z.2| → prIdGe tr tr' R s z = 0 := by
    intro z hz
    simp [prIdGe, hφ0 z.2 hz]
  -- smoothness of the fluxes
  have hsnd : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2) := hφS.comp contDiff_snd
  have hGqS : ContDiff ℝ ∞ (prIdGq tr tr' R s) := (hsnd.mul hPd).mul (prId_comp 0 hwd)
  have hGeS : ContDiff ℝ ∞ (prIdGe tr tr' R s) := (hsnd.mul hPd).mul (prId_comp 1 hwd)
  have hGq1 : ContDiff ℝ 1 (prIdGq tr tr' R s) := hGqS.of_le (by norm_num)
  have hGe1 : ContDiff ℝ 1 (prIdGe tr tr' R s) := hGeS.of_le (by norm_num)
  -- differentiability
  have hPdiff : Differentiable ℝ (diffP tr tr' s) := prId_diff hPd
  have hW0diff : Differentiable ℝ (fun x => diffV tr tr' s x 0) := prId_diff (prId_comp 0 hwd)
  have hW1diff : Differentiable ℝ (fun x => diffV tr tr' s x 1) := prId_diff (prId_comp 1 hwd)
  have hφdiff : Differentiable ℝ (etaCutoff R) := hφS.differentiable (by norm_num)
  -- continuity of the basic factors
  have hφC : Continuous (fun z : Plane => etaCutoff R z.2) := hφS.continuous.comp continuous_snd
  have hDφC : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    (hφS.continuous_deriv (by simp)).comp continuous_snd
  have hPC : Continuous (diffP tr tr' s) := hPd.continuous
  have hW1C : Continuous (fun z : Plane => diffV tr tr' s z 1) := (prId_comp 1 hwd).continuous
  have hWC : Continuous (diffV tr tr' s) := hwd.continuous
  -- the solenoidal condition for the difference `w`
  have hdiv : ∀ z : Plane, Cyl.partialQ (fun x => diffV tr tr' s x 0) z +
      Cyl.partialEta (fun x => diffV tr tr' s x 1) z = 0 := by
    intro z
    have e0 : (fun x => diffV tr tr' s x 0) = fun x => tr.v s x 0 - tr'.v s x 0 := by
      funext x; simp [diffV]
    have e1 : (fun x => diffV tr tr' s x 1) = fun x => tr.v s x 1 - tr'.v s x 1 := by
      funext x; simp [diffV]
    rw [e0, e1, prId_pQ_sub (prId_diff (prId_comp 0 hv)) (prId_diff (prId_comp 0 hv')) z,
      prId_pE_sub (prId_diff (prId_comp 1 hv)) (prId_diff (prId_comp 1 hv')) z]
    have s1 := tr.isTrain.solenoidal s hs0 z
    have s2 := tr'.isTrain.solenoidal s hs0 z
    unfold Cyl.divergence at s1 s2
    linarith
  -- the pointwise identity `∂_q G_q + ∂_η G_η = φ ⟨w, ∇π⟩ + φ' π w_η`
  have hpt : ∀ z : Plane, Cyl.partialQ (prIdGq tr tr' R s) z +
      Cyl.partialEta (prIdGe tr tr' R s) z =
        etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (Train.gradS (diffP tr tr' s) z) +
          deriv (etaCutoff R) z.2 * diffP tr tr' s z * diffV tr tr' s z 1 := by
    intro z
    rw [prIdGq_partialQ tr tr' R s hPdiff hW0diff z,
      prIdGe_partialEta tr tr' R s hφdiff hPdiff hW1diff z, prId_inner_gradS]
    linear_combination (etaCutoff R z.2 * diffP tr tr' s z) * hdiv z
  -- the partial derivatives vanish for `2R ≤ |η|`
  have hQzero : ∀ z : Plane, 2 * R ≤ |z.2| → Cyl.partialQ (prIdGq tr tr' R s) z = 0 := by
    intro z hz
    rw [prIdGq_partialQ tr tr' R s hPdiff hW0diff z, hφ0 z.2 hz]
    ring
  have hEzero : ∀ z : Plane, 2 * R ≤ |z.2| → Cyl.partialEta (prIdGe tr tr' R s) z = 0 := by
    intro z hz
    rw [prIdGe_partialEta tr tr' R s hφdiff hPdiff hW1diff z, hφ0 z.2 hz, hsuppD z hz]
    ring
  -- integrability
  have iQ : IntegrableOn (fun z : Plane => Cyl.partialQ (prIdGq tr tr' R s) z) (Cyl.cell c) :=
    hI c R hc hRpos _ (prId_pQ_cd hGqS).continuous (fun z hz => hQzero z hz)
  have iE : IntegrableOn (fun z : Plane => Cyl.partialEta (prIdGe tr tr' R s) z) (Cyl.cell c) :=
    hI c R hc hRpos _ (prId_pE_cd hGeS).continuous (fun z hz => hEzero z hz)
  have iF1 : IntegrableOn (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (Train.gradS (diffP tr tr' s) z)) (Cyl.cell c) :=
    hI c R hc hRpos _ (hφC.mul (hWC.inner (prId_gradS_cont hPd)))
      (fun z hz => by simp [hφ0 z.2 hz])
  have iF2 : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * diffP tr tr' s z * diffV tr tr' s z 1) (Cyl.cell c) :=
    hI c R hc hRpos _ ((hDφC.mul hPC).mul hW1C) (fun z hz => by simp [hsuppD z hz])
  -- cell integration by parts
  have hZq := hZ c R hc hRpos (prIdGq tr tr' R s) hGq1 hperQ hsuppQ
  have hZe := hZ c R hc hRpos (prIdGe tr tr' R s) hGe1 hperE hsuppE
  have hsplit1 : ∫ z in Cyl.cell c, (etaCutoff R z.2 *
        inner ℝ (diffV tr tr' s z) (Train.gradS (diffP tr tr' s) z) +
      deriv (etaCutoff R) z.2 * diffP tr tr' s z * diffV tr tr' s z 1) =
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        inner ℝ (diffV tr tr' s z) (Train.gradS (diffP tr tr' s) z)) +
      ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * diffP tr tr' s z * diffV tr tr' s z 1 :=
    integral_add iF1 iF2
  have hsplit2 : ∫ z in Cyl.cell c, (Cyl.partialQ (prIdGq tr tr' R s) z +
        Cyl.partialEta (prIdGe tr tr' R s) z) =
      (∫ z in Cyl.cell c, Cyl.partialQ (prIdGq tr tr' R s) z) +
        ∫ z in Cyl.cell c, Cyl.partialEta (prIdGe tr tr' R s) z :=
    integral_add iQ iE
  have hcongr : ∫ z in Cyl.cell c, (etaCutoff R z.2 *
        inner ℝ (diffV tr tr' s z) (Train.gradS (diffP tr tr' s) z) +
      deriv (etaCutoff R) z.2 * diffP tr tr' s z * diffV tr tr' s z 1) =
      ∫ z in Cyl.cell c, (Cyl.partialQ (prIdGq tr tr' R s) z +
        Cyl.partialEta (prIdGe tr tr' R s) z) := by
    congr 1
    funext z
    exact (hpt z).symm
  have htot : (∫ z in Cyl.cell c, etaCutoff R z.2 *
        inner ℝ (diffV tr tr' s z) (Train.gradS (diffP tr tr' s) z)) +
      (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * diffP tr tr' s z * diffV tr tr' s z 1) = 0 := by
    rw [← hsplit1, hcongr, hsplit2, hZq.1, hZe.2, add_zero]
  unfold cutoffPressure pressureRhs
  linarith

end UnforcedLeray.Short.PartI
