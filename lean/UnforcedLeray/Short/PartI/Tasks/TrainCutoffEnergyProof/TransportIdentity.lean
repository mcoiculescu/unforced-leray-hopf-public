import UnforcedLeray.Short.PartI.Sub.T05b_2
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T05b/2/3`: the transport identity (leaf `TransportIdentity`)

Source of record: `the November 2 reference manuscript`, lines 276-288.
Target: `transportIdentity : TransportIdentity` (`Short/PartI/Sub/T05b_2.lean`).

Route. Fix `s ≥ 0`, `R ≥ 1`, `v = tr.v s`, `w = diffV tr tr' s`, `φ = etaCutoff R`.
Put `S = |w|² = w₀² + w₁²`, `G_q = φ S v₀`, `G_η = φ S v₁`.  Then pointwise

`2 φ ⟨w, (v·∇)w⟩ + φ' S v₁ = ∂_q G_q + ∂_η G_η - φ S (∂_q v₀ + ∂_η v₁)`,

and `div v = 0` kills the last term.  The cell integrals of `∂_q G_q` and `∂_η G_η` vanish by
`CellDerivZero`, so `-2 ∫ φ ⟨w, (v·∇)w⟩ = ∫ S v₁ φ'`, which is `transportRhs`.  Integrability of
each piece comes from `CellIntegrableOfSupport` (the `η`-derivative of `G_η` vanishes on
`2R < |η|`, so it is handled with the radius `2R`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Slice-derivative calculus -/

/-- Leibniz rule for `∂_q`. -/
theorem tp_partialQ_mul (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun y => f y * g y) z = Cyl.partialQ f z * g z + f z * Cyl.partialQ g z :=
  ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).mul (Cyl.hasDerivAt_sliceQ hg z.1 z.2)).deriv

/-- Leibniz rule for `∂_η`. -/
theorem tp_partialEta_mul (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun y => f y * g y) z = Cyl.partialEta f z * g z + f z * Cyl.partialEta g z :=
  ((Cyl.hasDerivAt_sliceEta hf z.1 z.2).mul (Cyl.hasDerivAt_sliceEta hg z.1 z.2)).deriv

/-- Additivity of `∂_q`. -/
theorem tp_partialQ_add (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun y => f y + g y) z = Cyl.partialQ f z + Cyl.partialQ g z :=
  ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).add (Cyl.hasDerivAt_sliceQ hg z.1 z.2)).deriv

/-- Additivity of `∂_η`. -/
theorem tp_partialEta_add (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun y => f y + g y) z = Cyl.partialEta f z + Cyl.partialEta g z :=
  ((Cyl.hasDerivAt_sliceEta hf z.1 z.2).add (Cyl.hasDerivAt_sliceEta hg z.1 z.2)).deriv

/-- A function of `η` alone has zero `∂_q`. -/
theorem tp_partialQ_snd (φ : ℝ → ℝ) (z : Plane) :
    Cyl.partialQ (fun y : Plane => φ y.2) z = 0 := by
  show deriv (fun _ : ℝ => φ z.2) z.1 = 0
  exact deriv_const _ _

/-- A function of `η` alone has `∂_η` equal to its ordinary derivative. -/
theorem tp_partialEta_snd (φ : ℝ → ℝ) (z : Plane) :
    Cyl.partialEta (fun y : Plane => φ y.2) z = deriv φ z.2 := rfl

/-- A `C^1` function that vanishes on `2R ≤ |η|` has zero `∂_η` on the open set `2R < |η|`. -/
theorem tp_partialEta_zero (G : Plane → ℝ) (R : ℝ)
    (hG : ∀ z : Plane, 2 * R ≤ |z.2| → G z = 0) (z : Plane) (hz : 2 * R < |z.2|) :
    Cyl.partialEta G z = 0 := by
  have hopen : IsOpen {η : ℝ | 2 * R < |η|} := isOpen_lt continuous_const continuous_abs
  have hev : (fun η : ℝ => G (z.1, η)) =ᶠ[nhds z.2] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds (show z.2 ∈ {η : ℝ | 2 * R < |η|} from hz)] with η hη
    have hη' : 2 * R < |η| := hη
    exact hG (z.1, η) hη'.le
  show deriv (fun η : ℝ => G (z.1, η)) z.2 = 0
  rw [hev.deriv_eq, deriv_const]

/-! ### Algebra of the coordinates -/

/-- The real inner product on `Vec` in coordinates. -/
theorem tp_inner (x y : Vec) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

/-- `|x|² = x₀² + x₁²` on `Vec`. -/
theorem tp_norm_sq (x : Vec) : ‖x‖ ^ 2 = x 0 * x 0 + x 1 * x 1 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  ring

/-- Component of a `Vec`-valued function is `C^∞` when the function is. -/
theorem tp_comp_contDiff (u : Plane → Vec) (i : Fin 2) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun z => u z i) :=
  (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hu

/-! ### The transport identity, for arbitrary smooth periodic fields -/

/-- The core computation: for a smooth, `c`-periodic, divergence-free `v` and a smooth periodic `w`,
with a cutoff `φ` vanishing (with its derivative) on `2R ≤ |η|`,
`-2 ∫_cell φ ⟨w, (v·∇)w⟩ = ∫_cell |w|² v₁ φ'`. -/
theorem tp_core (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφ0 : ∀ η : ℝ, 2 * R ≤ |η| → φ η = 0)
    (hφ1 : ∀ η : ℝ, 2 * R ≤ |η| → deriv φ η = 0)
    (v w : Plane → Vec) (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w)
    (hvp : Cyl.IsPeriodic c v) (hwp : Cyl.IsPeriodic c w)
    (hdiv : ∀ z : Plane, Cyl.divergence v z = 0)
    (hI : CellIntegrableOfSupport) (hZ : CellDerivZero) :
    -2 * ∫ z in Cyl.cell c, φ z.2 * inner ℝ (w z) (bilinAdv v w z) =
      ∫ z in Cyl.cell c, ‖w z‖ ^ 2 * v z 1 * deriv φ z.2 := by
  -- smoothness of the pieces
  have hw0 : ContDiff ℝ ∞ (fun z => w z 0) := tp_comp_contDiff w 0 hw
  have hw1 : ContDiff ℝ ∞ (fun z => w z 1) := tp_comp_contDiff w 1 hw
  have hv0 : ContDiff ℝ ∞ (fun z => v z 0) := tp_comp_contDiff v 0 hv
  have hv1 : ContDiff ℝ ∞ (fun z => v z 1) := tp_comp_contDiff v 1 hv
  have hφs : ContDiff ℝ ∞ (fun z : Plane => φ z.2) := hφ.comp contDiff_snd
  have hS : ContDiff ℝ ∞ (fun z : Plane => w z 0 * w z 0 + w z 1 * w z 1) :=
    (hw0.mul hw0).add (hw1.mul hw1)
  have hGQs : ContDiff ℝ ∞ (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0) :=
    (hφs.mul hS).mul hv0
  have hGEs : ContDiff ℝ ∞ (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1) :=
    (hφs.mul hS).mul hv1
  have hGQ1 : ContDiff ℝ 1 (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0) :=
    hGQs.of_le (by simp)
  have hGE1 : ContDiff ℝ 1 (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1) :=
    hGEs.of_le (by simp)
  have hGQc : Continuous (Cyl.partialQ (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0)) :=
    (Cyl.C1_partial_of_contDiff hGQ1).1
  have hGEc : Continuous (Cyl.partialEta (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1)) :=
    (Cyl.C1_partial_of_contDiff hGE1).2
  -- the fluxes vanish for `2R ≤ |η|`
  have hGQ0 : ∀ z : Plane, 2 * R ≤ |z.2| →
      φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0 = 0 := by
    intro z hz
    simp [hφ0 z.2 hz]
  have hGE0 : ∀ z : Plane, 2 * R ≤ |z.2| →
      φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1 = 0 := by
    intro z hz
    simp [hφ0 z.2 hz]
  have hPQ0 : ∀ z : Plane, 2 * R ≤ |z.2| →
      Cyl.partialQ (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0) z = 0 := by
    intro z hz
    have hfun : (fun q : ℝ => φ (q, z.2).2 * (w (q, z.2) 0 * w (q, z.2) 0 + w (q, z.2) 1 * w (q, z.2) 1) * v (q, z.2) 0) = fun _ => (0 : ℝ) :=
      funext fun q => hGQ0 (q, z.2) hz
    show deriv (fun q : ℝ => φ (q, z.2).2 * (w (q, z.2) 0 * w (q, z.2) 0 + w (q, z.2) 1 * w (q, z.2) 1) * v (q, z.2) 0) z.1 = 0
    rw [hfun, deriv_const]
  have hPE0 : ∀ z : Plane, 2 * (2 * R) ≤ |z.2| →
      Cyl.partialEta (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1) z = 0 :=
    fun z hz => tp_partialEta_zero _ R hGE0 z (by linarith)
  -- integrability of the three pieces
  have hPQi : IntegrableOn
      (Cyl.partialQ (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0)) (Cyl.cell c) :=
    hI c R hc hR _ hGQc hPQ0
  have hPEi : IntegrableOn
      (Cyl.partialEta (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1)) (Cyl.cell c) :=
    hI c (2 * R) hc (by linarith) _ hGEc hPE0
  have hdφ : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hBc : Continuous (fun z : Plane => ‖w z‖ ^ 2 * v z 1 * deriv φ z.2) := by
    have h1 : Continuous (fun z : Plane => ‖w z‖ ^ 2) := (hw.continuous.norm).pow 2
    have h2 : Continuous (fun z : Plane => v z 1) := hv1.continuous
    have h3 : Continuous (fun z : Plane => deriv φ z.2) := hdφ.comp continuous_snd
    exact (h1.mul h2).mul h3
  have hB0 : ∀ z : Plane, 2 * R ≤ |z.2| → ‖w z‖ ^ 2 * v z 1 * deriv φ z.2 = 0 := by
    intro z hz
    simp [hφ1 z.2 hz]
  have hBi : IntegrableOn (fun z : Plane => ‖w z‖ ^ 2 * v z 1 * deriv φ z.2) (Cyl.cell c) :=
    hI c R hc hR _ hBc hB0
  -- differentiability of the factors
  have hw0d : Differentiable ℝ (fun z => w z 0) := hw0.differentiable (by simp)
  have hw1d : Differentiable ℝ (fun z => w z 1) := hw1.differentiable (by simp)
  have hv0d : Differentiable ℝ (fun z => v z 0) := hv0.differentiable (by simp)
  have hv1d : Differentiable ℝ (fun z => v z 1) := hv1.differentiable (by simp)
  have hφsd : Differentiable ℝ (fun z : Plane => φ z.2) := hφs.differentiable (by simp)
  have hSd : Differentiable ℝ (fun z : Plane => w z 0 * w z 0 + w z 1 * w z 1) :=
    hS.differentiable (by simp)
  have hφS : Differentiable ℝ (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1)) :=
    hφsd.mul hSd
  have hWW0 : Differentiable ℝ (fun z : Plane => w z 0 * w z 0) := hw0d.mul hw0d
  have hWW1 : Differentiable ℝ (fun z : Plane => w z 1 * w z 1) := hw1d.mul hw1d
  -- the pointwise identity
  have hkey : ∀ z : Plane,
      2 * (φ z.2 * inner ℝ (w z) (bilinAdv v w z)) =
        Cyl.partialQ (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0) z +
          Cyl.partialEta (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1) z -
          ‖w z‖ ^ 2 * v z 1 * deriv φ z.2 := by
    intro z
    have hdiv' : Cyl.partialQ (fun y => v y 0) z + Cyl.partialEta (fun y => v y 1) z = 0 :=
      hdiv z
    have hQ : Cyl.partialQ (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0) z =
        φ z.2 * Cyl.partialQ (fun y => w y 0 * w y 0 + w y 1 * w y 1) z * v z 0 +
          φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * Cyl.partialQ (fun y => v y 0) z := by
      rw [tp_partialQ_mul _ _ hφS hv0d z, tp_partialQ_mul _ _ hφsd hSd z,
        tp_partialQ_snd φ z]
      ring
    have hE : Cyl.partialEta (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1) z =
        (deriv φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) +
            φ z.2 * Cyl.partialEta (fun y => w y 0 * w y 0 + w y 1 * w y 1) z) * v z 1 +
          φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * Cyl.partialEta (fun y => v y 1) z := by
      rw [tp_partialEta_mul _ _ hφS hv1d z, tp_partialEta_mul _ _ hφsd hSd z,
        tp_partialEta_snd φ z]
    have hSq : Cyl.partialQ (fun y => w y 0 * w y 0 + w y 1 * w y 1) z =
        2 * (w z 0 * Cyl.partialQ (fun y => w y 0) z + w z 1 * Cyl.partialQ (fun y => w y 1) z) := by
      rw [tp_partialQ_add _ _ hWW0 hWW1 z,
        tp_partialQ_mul _ _ hw0d hw0d z, tp_partialQ_mul _ _ hw1d hw1d z]
      ring
    have hSe : Cyl.partialEta (fun y => w y 0 * w y 0 + w y 1 * w y 1) z =
        2 * (w z 0 * Cyl.partialEta (fun y => w y 0) z + w z 1 * Cyl.partialEta (fun y => w y 1) z) := by
      rw [tp_partialEta_add _ _ hWW0 hWW1 z,
        tp_partialEta_mul _ _ hw0d hw0d z, tp_partialEta_mul _ _ hw1d hw1d z]
      ring
    have hb0 : bilinAdv v w z 0 = v z 0 * Cyl.partialQ (fun y => w y 0) z +
        v z 1 * Cyl.partialEta (fun y => w y 0) z := rfl
    have hb1 : bilinAdv v w z 1 = v z 0 * Cyl.partialQ (fun y => w y 1) z +
        v z 1 * Cyl.partialEta (fun y => w y 1) z := rfl
    rw [hQ, hE, hSq, hSe, tp_inner, hb0, hb1, tp_norm_sq]
    linear_combination (-(φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1))) * hdiv'
  -- periodicity of the fluxes
  have hperQ : Cyl.IsPeriodic c (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0) := by
    intro z
    show φ z.2 * (w (z.1 + c, z.2) 0 * w (z.1 + c, z.2) 0 + w (z.1 + c, z.2) 1 * w (z.1 + c, z.2) 1) *
        v (z.1 + c, z.2) 0 = φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0
    rw [hwp z, hvp z]
  have hperE : Cyl.IsPeriodic c (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1) := by
    intro z
    show φ z.2 * (w (z.1 + c, z.2) 0 * w (z.1 + c, z.2) 0 + w (z.1 + c, z.2) 1 * w (z.1 + c, z.2) 1) *
        v (z.1 + c, z.2) 1 = φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1
    rw [hwp z, hvp z]
  -- cell integration by parts for both fluxes
  have hZQ := hZ c R hc hR _ hGQ1 hperQ hGQ0
  have hZE := hZ c R hc hR _ hGE1 hperE hGE0
  -- integrate the pointwise identity
  have h2 : ∫ z in Cyl.cell c, 2 * (φ z.2 * inner ℝ (w z) (bilinAdv v w z)) =
      ∫ z in Cyl.cell c, (Cyl.partialQ (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 0) z +
        Cyl.partialEta (fun z : Plane => φ z.2 * (w z 0 * w z 0 + w z 1 * w z 1) * v z 1) z -
        ‖w z‖ ^ 2 * v z 1 * deriv φ z.2) :=
    integral_congr_ae (ae_of_all _ hkey)
  rw [integral_const_mul] at h2
  have h3 := integral_sub (hPQi.add hPEi) hBi
  simp only [Pi.add_apply] at h3
  have h4 := integral_add hPQi hPEi
  linarith [h2, h3, h4, hZQ.1, hZE.2]

/-! ### The target -/

/-- **`PartI:T05b/2/3`, target `TransportIdentity`.** Uses the cutoff facts (`EtaCutoffFacts`),
the two toolkit integration leaves (`CellIntegrableOfSupport`, `CellDerivZero`) and the smoothness
of the slices (`TrainSliceSmooth`), as black boxes. -/
theorem transportIdentity (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport) (hZ : CellDerivZero)
    (hS : TrainSliceSmooth) : TransportIdentity := by
  obtain ⟨C₀, _hC₀, hcut⟩ := hη
  intro ν c _hν hc tr tr' R hR1 s hs
  have hR : 0 < R := by linarith
  obtain ⟨hφ, _, _, hφ0, hφ'⟩ := hcut R hR1
  have hφ1 : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    have h1 := hφ' η
    rw [hφ0 η hη, Real.sqrt_zero, mul_zero, abs_nonpos_iff] at h1
    exact h1
  have hvS : ContDiff ℝ ∞ (tr.v s) := (hS ν c tr s hs).1
  have hv'S : ContDiff ℝ ∞ (tr'.v s) := (hS ν c tr' s hs).1
  have hwS : ContDiff ℝ ∞ (diffV tr tr' s) := hvS.sub hv'S
  have hvp : Cyl.IsPeriodic c (tr.v s) := tr.isTrain.periodic_v s hs
  have hwp : Cyl.IsPeriodic c (diffV tr tr' s) := by
    intro z
    show tr.v s (z.1 + c, z.2) - tr'.v s (z.1 + c, z.2) = tr.v s z - tr'.v s z
    rw [tr.isTrain.periodic_v s hs z, tr'.isTrain.periodic_v s hs z]
  have hdiv : ∀ z : Plane, Cyl.divergence (tr.v s) z = 0 := fun z => tr.isTrain.solenoidal s hs z
  have hcore := tp_core c R hc hR (etaCutoff R) hφ hφ0 hφ1 (tr.v s) (diffV tr tr' s) hvS hwS
    hvp hwp hdiv hI hZ
  unfold cutoffTransport transportRhs
  exact hcore

end UnforcedLeray.Short.PartI
