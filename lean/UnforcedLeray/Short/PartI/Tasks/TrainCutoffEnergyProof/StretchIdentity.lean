import UnforcedLeray.Short.PartI.Sub.T05b_2
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task: the stretch identity (leaf `StretchIdentity`)

Source of record: `the November 2 reference manuscript`, lines 276-288.
Target: `stretchIdentity : StretchIdentity` (`Short/PartI/Sub/T05b_2.lean`).

Route. Fix `s ≥ 0`, `R ≥ 1`, `w = diffV tr tr' s`, `v = tr'.v s`, `φ = etaCutoff R`. Put
`F = w₀ v₀ + w₁ v₁`, `G₀ = φ w₀ F`, `G₁ = φ w₁ F`. Then pointwise

`φ ⟨w, (w·∇)v⟩ = ∂_q G₀ + ∂_η G₁ - φ' w₁ F - φ ⟨(w·∇)w, v⟩ - φ F (∂_q w₀ + ∂_η w₁)`,

and `div w = 0` kills the last term. The cell integrals of `∂_q G₀` and `∂_η G₁` vanish by
`CellDerivZero`, which gives `-2 ∫ φ ⟨w, (w·∇)v⟩ = 2 ∫ φ' w₁ ⟨w, v⟩ + 2 ∫ φ ⟨(w·∇)w, v⟩`,
that is `cutoffStretch = stretchRhs`.
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
theorem sr_partialQ_mul (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun y => f y * g y) z = Cyl.partialQ f z * g z + f z * Cyl.partialQ g z :=
  ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).mul (Cyl.hasDerivAt_sliceQ hg z.1 z.2)).deriv

/-- Leibniz rule for `∂_η`. -/
theorem sr_partialEta_mul (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun y => f y * g y) z = Cyl.partialEta f z * g z + f z * Cyl.partialEta g z :=
  ((Cyl.hasDerivAt_sliceEta hf z.1 z.2).mul (Cyl.hasDerivAt_sliceEta hg z.1 z.2)).deriv

/-- Additivity of `∂_q`. -/
theorem sr_partialQ_add (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun y => f y + g y) z = Cyl.partialQ f z + Cyl.partialQ g z :=
  ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).add (Cyl.hasDerivAt_sliceQ hg z.1 z.2)).deriv

/-- Additivity of `∂_η`. -/
theorem sr_partialEta_add (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun y => f y + g y) z = Cyl.partialEta f z + Cyl.partialEta g z :=
  ((Cyl.hasDerivAt_sliceEta hf z.1 z.2).add (Cyl.hasDerivAt_sliceEta hg z.1 z.2)).deriv

/-- Subtractivity of `∂_q`. -/
theorem sr_partialQ_sub (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun y => f y - g y) z = Cyl.partialQ f z - Cyl.partialQ g z :=
  ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).sub (Cyl.hasDerivAt_sliceQ hg z.1 z.2)).deriv

/-- Subtractivity of `∂_η`. -/
theorem sr_partialEta_sub (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun y => f y - g y) z = Cyl.partialEta f z - Cyl.partialEta g z :=
  ((Cyl.hasDerivAt_sliceEta hf z.1 z.2).sub (Cyl.hasDerivAt_sliceEta hg z.1 z.2)).deriv

/-- A function of `η` alone has zero `∂_q`. -/
theorem sr_partialQ_snd (φ : ℝ → ℝ) (z : Plane) :
    Cyl.partialQ (fun y : Plane => φ y.2) z = 0 := by
  show deriv (fun _ : ℝ => φ z.2) z.1 = 0
  exact deriv_const _ _

/-- A function of `η` alone has `∂_η` equal to its ordinary derivative. -/
theorem sr_partialEta_snd (φ : ℝ → ℝ) (z : Plane) :
    Cyl.partialEta (fun y : Plane => φ y.2) z = deriv φ z.2 := rfl

/-- A function vanishing on `2R ≤ |η|` has zero `∂_q` on that set. -/
theorem sr_partialQ_zero_of (G : Plane → ℝ) (R : ℝ)
    (hG : ∀ z : Plane, 2 * R ≤ |z.2| → G z = 0) (z : Plane) (hz : 2 * R ≤ |z.2|) :
    Cyl.partialQ G z = 0 := by
  have hfun : (fun q : ℝ => G (q, z.2)) = fun _ => (0 : ℝ) :=
    funext fun q => hG (q, z.2) hz
  show deriv (fun q : ℝ => G (q, z.2)) z.1 = 0
  rw [hfun, deriv_const]

/-- A `C^1` function that vanishes on `2R ≤ |η|` has zero `∂_η` on the open set `2R < |η|`. -/
theorem sr_partialEta_zero (G : Plane → ℝ) (R : ℝ)
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
theorem sr_inner (x y : Vec) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

/-- The first component of the transport `(a·∇) b`. -/
theorem sr_bilin0 (a b : Plane → Vec) (z : Plane) :
    bilinAdv a b z 0 = a z 0 * Cyl.partialQ (fun y => b y 0) z +
      a z 1 * Cyl.partialEta (fun y => b y 0) z := rfl

/-- The second component of the transport `(a·∇) b`. -/
theorem sr_bilin1 (a b : Plane → Vec) (z : Plane) :
    bilinAdv a b z 1 = a z 0 * Cyl.partialQ (fun y => b y 1) z +
      a z 1 * Cyl.partialEta (fun y => b y 1) z := rfl

/-- Component of a `Vec`-valued function is `C^∞` when the function is. -/
theorem sr_comp_contDiff (u : Plane → Vec) (i : Fin 2) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun z => u z i) :=
  (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hu

/-- The transport `(a·∇) b` is continuous when `a` and `b` are `C^∞`. -/
theorem sr_bilin_continuous (a b : Plane → Vec) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Continuous (bilinAdv a b) := by
  have ha0 : Continuous (fun z : Plane => a z 0) := (sr_comp_contDiff a 0 ha).continuous
  have ha1 : Continuous (fun z : Plane => a z 1) := (sr_comp_contDiff a 1 ha).continuous
  have hb0 : ContDiff ℝ 1 (fun z : Plane => b z 0) :=
    (sr_comp_contDiff b 0 hb).of_le (by simp)
  have hb1 : ContDiff ℝ 1 (fun z : Plane => b z 1) :=
    (sr_comp_contDiff b 1 hb).of_le (by simp)
  have hq0 : Continuous (Cyl.partialQ (fun z : Plane => b z 0)) :=
    (Cyl.C1_partial_of_contDiff hb0).1
  have he0 : Continuous (Cyl.partialEta (fun z : Plane => b z 0)) :=
    (Cyl.C1_partial_of_contDiff hb0).2
  have hq1 : Continuous (Cyl.partialQ (fun z : Plane => b z 1)) :=
    (Cyl.C1_partial_of_contDiff hb1).1
  have he1 : Continuous (Cyl.partialEta (fun z : Plane => b z 1)) :=
    (Cyl.C1_partial_of_contDiff hb1).2
  have hx : Continuous (fun z : Plane =>
      a z 0 * Cyl.partialQ (fun y => b y 0) z + a z 1 * Cyl.partialEta (fun y => b y 0) z) :=
    (ha0.mul hq0).add (ha1.mul he0)
  have hy : Continuous (fun z : Plane =>
      a z 0 * Cyl.partialQ (fun y => b y 1) z + a z 1 * Cyl.partialEta (fun y => b y 1) z) :=
    (ha0.mul hq1).add (ha1.mul he1)
  have htv : Continuous (fun p : ℝ × ℝ => (Train.toVec p : Vec)) := Train.toVecL.continuous
  exact htv.comp (hx.prodMk hy)

/-! ### Integral bookkeeping -/

/-- Abstract form of the cell integration: if `A = ∂_q G₀ + ∂_η G₁ - C - B` pointwise and the two
derivative integrals vanish, then `∫ A = -∫ C - ∫ B`. -/
theorem sr_integral_split (s : Set Plane) (A PQ PE C B : Plane → ℝ)
    (hkey : ∀ z, A z = PQ z + PE z - C z - B z)
    (hPQi : IntegrableOn PQ s) (hPEi : IntegrableOn PE s)
    (hCi : IntegrableOn C s) (hBi : IntegrableOn B s)
    (hPQ0 : ∫ z in s, PQ z = 0) (hPE0 : ∫ z in s, PE z = 0) :
    ∫ z in s, A z = -(∫ z in s, C z) - ∫ z in s, B z := by
  have h2 : ∫ z in s, A z = ∫ z in s, (PQ z + PE z - C z - B z) :=
    integral_congr_ae (ae_of_all _ hkey)
  have i1 : IntegrableOn (fun z => PQ z + PE z) s := hPQi.add hPEi
  have i2 : IntegrableOn (fun z => PQ z + PE z - C z) s := i1.sub hCi
  have e1 : ∫ z in s, (PQ z + PE z - C z - B z) =
      (∫ z in s, (PQ z + PE z - C z)) - ∫ z in s, B z :=
    integral_sub i2 hBi
  have e2 : ∫ z in s, (PQ z + PE z - C z) = (∫ z in s, (PQ z + PE z)) - ∫ z in s, C z :=
    integral_sub i1 hCi
  have e3 : ∫ z in s, (PQ z + PE z) = (∫ z in s, PQ z) + ∫ z in s, PE z :=
    integral_add hPQi hPEi
  linarith [h2, e1, e2, e3, hPQ0, hPE0]

/-! ### The core computation -/

/-- The core computation for smooth periodic `w`, `v` with `div w = 0` and a cutoff `φ` vanishing
(with its derivative) on `2R ≤ |η|`:
`-2 ∫_cell φ ⟨w, (w·∇)v⟩ = 2 ∫_cell φ' w₁ ⟨w, v⟩ + 2 ∫_cell φ ⟨(w·∇)w, v⟩`. -/
theorem sr_core (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφ0 : ∀ η : ℝ, 2 * R ≤ |η| → φ η = 0)
    (hφ1 : ∀ η : ℝ, 2 * R ≤ |η| → deriv φ η = 0)
    (w v : Plane → Vec) (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    (hwp : Cyl.IsPeriodic c w) (hvp : Cyl.IsPeriodic c v)
    (hdiv : ∀ z : Plane, Cyl.divergence w z = 0)
    (hI : CellIntegrableOfSupport) (hZ : CellDerivZero) :
    -2 * ∫ z in Cyl.cell c, φ z.2 * inner ℝ (w z) (bilinAdv w v z) =
      2 * (∫ z in Cyl.cell c, deriv φ z.2 * w z 1 * inner ℝ (w z) (v z)) +
        2 * ∫ z in Cyl.cell c, φ z.2 * inner ℝ (bilinAdv w w z) (v z) := by
  -- smoothness and differentiability of the factors
  have hw0 : ContDiff ℝ ∞ (fun z : Plane => w z 0) := sr_comp_contDiff w 0 hw
  have hw1 : ContDiff ℝ ∞ (fun z : Plane => w z 1) := sr_comp_contDiff w 1 hw
  have hv0 : ContDiff ℝ ∞ (fun z : Plane => v z 0) := sr_comp_contDiff v 0 hv
  have hv1 : ContDiff ℝ ∞ (fun z : Plane => v z 1) := sr_comp_contDiff v 1 hv
  have hφs : ContDiff ℝ ∞ (fun z : Plane => φ z.2) := hφ.comp contDiff_snd
  have hw0d : Differentiable ℝ (fun z : Plane => w z 0) := hw0.differentiable (by simp)
  have hw1d : Differentiable ℝ (fun z : Plane => w z 1) := hw1.differentiable (by simp)
  have hv0d : Differentiable ℝ (fun z : Plane => v z 0) := hv0.differentiable (by simp)
  have hv1d : Differentiable ℝ (fun z : Plane => v z 1) := hv1.differentiable (by simp)
  have hφsd : Differentiable ℝ (fun z : Plane => φ z.2) := hφs.differentiable (by simp)
  have hFs : ContDiff ℝ ∞ (fun z : Plane => w z 0 * v z 0 + w z 1 * v z 1) :=
    (hw0.mul hv0).add (hw1.mul hv1)
  have hFd : Differentiable ℝ (fun z : Plane => w z 0 * v z 0 + w z 1 * v z 1) :=
    hFs.differentiable (by simp)
  have hf0d : Differentiable ℝ (fun z : Plane => φ z.2 * w z 0) := hφsd.mul hw0d
  have hf1d : Differentiable ℝ (fun z : Plane => φ z.2 * w z 1) := hφsd.mul hw1d
  -- the two fluxes `G₀ = φ w₀ F`, `G₁ = φ w₁ F`
  have hG0s : ContDiff ℝ ∞
      (fun z : Plane => φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1)) :=
    (hφs.mul hw0).mul hFs
  have hG1s : ContDiff ℝ ∞
      (fun z : Plane => φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1)) :=
    (hφs.mul hw1).mul hFs
  have hG0_1 : ContDiff ℝ 1
      (fun z : Plane => φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1)) :=
    hG0s.of_le (by simp)
  have hG1_1 : ContDiff ℝ 1
      (fun z : Plane => φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1)) :=
    hG1s.of_le (by simp)
  have hG0c : Continuous
      (Cyl.partialQ (fun z : Plane => φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1))) :=
    (Cyl.C1_partial_of_contDiff hG0_1).1
  have hG1c : Continuous
      (Cyl.partialEta (fun z : Plane => φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1))) :=
    (Cyl.C1_partial_of_contDiff hG1_1).2
  -- the fluxes vanish for `2R ≤ |η|`
  have hG0_0 : ∀ z : Plane, 2 * R ≤ |z.2| →
      φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1) = 0 := by
    intro z hz
    simp [hφ0 z.2 hz]
  have hG1_0 : ∀ z : Plane, 2 * R ≤ |z.2| →
      φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1) = 0 := by
    intro z hz
    simp [hφ0 z.2 hz]
  -- periodicity of the fluxes
  have hperG0 : Cyl.IsPeriodic c
      (fun z : Plane => φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1)) := by
    intro z
    show φ z.2 * w (z.1 + c, z.2) 0 *
        (w (z.1 + c, z.2) 0 * v (z.1 + c, z.2) 0 + w (z.1 + c, z.2) 1 * v (z.1 + c, z.2) 1) =
      φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1)
    rw [hwp z, hvp z]
  have hperG1 : Cyl.IsPeriodic c
      (fun z : Plane => φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1)) := by
    intro z
    show φ z.2 * w (z.1 + c, z.2) 1 *
        (w (z.1 + c, z.2) 0 * v (z.1 + c, z.2) 0 + w (z.1 + c, z.2) 1 * v (z.1 + c, z.2) 1) =
      φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1)
    rw [hwp z, hvp z]
  -- derivative integrals: the vanishing conditions
  have hPQ0 : ∀ z : Plane, 2 * R ≤ |z.2| →
      Cyl.partialQ (fun z : Plane => φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1)) z = 0 :=
    fun z hz => sr_partialQ_zero_of
      (fun z : Plane => φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1)) R hG0_0 z hz
  have hPE0 : ∀ z : Plane, 2 * (2 * R) ≤ |z.2| →
      Cyl.partialEta (fun z : Plane => φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1)) z = 0 :=
    fun z hz => sr_partialEta_zero
      (fun z : Plane => φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1)) R hG1_0 z (by linarith)
  -- integrability of the derivative terms
  have hPQi : IntegrableOn
      (Cyl.partialQ (fun z : Plane => φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1)))
      (Cyl.cell c) :=
    hI c R hc hR _ hG0c hPQ0
  have hPEi : IntegrableOn
      (Cyl.partialEta (fun z : Plane => φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1)))
      (Cyl.cell c) :=
    hI c (2 * R) hc (by linarith) _ hG1c hPE0
  -- integrability of the stretching term and of the `φ'` term
  have hdφ : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hwc : Continuous w := hw.continuous
  have hvc : Continuous v := hv.continuous
  have hφc : Continuous (fun z : Plane => φ z.2) := hφs.continuous
  have hCc : Continuous (fun z : Plane => deriv φ z.2 * w z 1 * inner ℝ (w z) (v z)) :=
    ((hdφ.comp continuous_snd).mul (sr_comp_contDiff w 1 hw).continuous).mul (hwc.inner hvc)
  have hC0 : ∀ z : Plane, 2 * R ≤ |z.2| → deriv φ z.2 * w z 1 * inner ℝ (w z) (v z) = 0 := by
    intro z hz
    simp [hφ1 z.2 hz]
  have hCi : IntegrableOn (fun z : Plane => deriv φ z.2 * w z 1 * inner ℝ (w z) (v z))
      (Cyl.cell c) :=
    hI c R hc hR _ hCc hC0
  have hBc : Continuous (fun z : Plane => φ z.2 * inner ℝ (bilinAdv w w z) (v z)) :=
    hφc.mul ((sr_bilin_continuous w w hw hw).inner hvc)
  have hB0 : ∀ z : Plane, 2 * R ≤ |z.2| → φ z.2 * inner ℝ (bilinAdv w w z) (v z) = 0 := by
    intro z hz
    simp [hφ0 z.2 hz]
  have hBi : IntegrableOn (fun z : Plane => φ z.2 * inner ℝ (bilinAdv w w z) (v z))
      (Cyl.cell c) :=
    hI c R hc hR _ hBc hB0
  -- the pointwise identity
  have hkey : ∀ z : Plane,
      φ z.2 * inner ℝ (w z) (bilinAdv w v z) =
        Cyl.partialQ (fun z : Plane => φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1)) z +
          Cyl.partialEta (fun z : Plane => φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1)) z -
          deriv φ z.2 * w z 1 * inner ℝ (w z) (v z) -
          φ z.2 * inner ℝ (bilinAdv w w z) (v z) := by
    intro z
    have hdz : Cyl.partialQ (fun y : Plane => w y 0) z +
        Cyl.partialEta (fun y : Plane => w y 1) z = 0 := hdiv z
    have hQ : Cyl.partialQ (fun z : Plane => φ z.2 * w z 0 * (w z 0 * v z 0 + w z 1 * v z 1)) z =
        Cyl.partialQ (fun y : Plane => φ y.2 * w y 0) z * (w z 0 * v z 0 + w z 1 * v z 1) +
          (φ z.2 * w z 0) * Cyl.partialQ (fun y : Plane => w y 0 * v y 0 + w y 1 * v y 1) z :=
      sr_partialQ_mul (fun y : Plane => φ y.2 * w y 0)
        (fun y : Plane => w y 0 * v y 0 + w y 1 * v y 1) hf0d hFd z
    have hE : Cyl.partialEta (fun z : Plane => φ z.2 * w z 1 * (w z 0 * v z 0 + w z 1 * v z 1)) z =
        Cyl.partialEta (fun y : Plane => φ y.2 * w y 1) z * (w z 0 * v z 0 + w z 1 * v z 1) +
          (φ z.2 * w z 1) * Cyl.partialEta (fun y : Plane => w y 0 * v y 0 + w y 1 * v y 1) z :=
      sr_partialEta_mul (fun y : Plane => φ y.2 * w y 1)
        (fun y : Plane => w y 0 * v y 0 + w y 1 * v y 1) hf1d hFd z
    have hPQφ : Cyl.partialQ (fun y : Plane => φ y.2 * w y 0) z =
        φ z.2 * Cyl.partialQ (fun y : Plane => w y 0) z := by
      rw [sr_partialQ_mul (fun y : Plane => φ y.2) (fun y : Plane => w y 0) hφsd hw0d z,
        sr_partialQ_snd]
      ring
    have hPEφ : Cyl.partialEta (fun y : Plane => φ y.2 * w y 1) z =
        deriv φ z.2 * w z 1 + φ z.2 * Cyl.partialEta (fun y : Plane => w y 1) z := by
      rw [sr_partialEta_mul (fun y : Plane => φ y.2) (fun y : Plane => w y 1) hφsd hw1d z,
        sr_partialEta_snd]
    have hFq : Cyl.partialQ (fun y : Plane => w y 0 * v y 0 + w y 1 * v y 1) z =
        Cyl.partialQ (fun y : Plane => w y 0) z * v z 0 +
          w z 0 * Cyl.partialQ (fun y : Plane => v y 0) z +
        (Cyl.partialQ (fun y : Plane => w y 1) z * v z 1 +
          w z 1 * Cyl.partialQ (fun y : Plane => v y 1) z) := by
      rw [sr_partialQ_add (fun y : Plane => w y 0 * v y 0) (fun y : Plane => w y 1 * v y 1)
          (hw0d.mul hv0d) (hw1d.mul hv1d) z,
        sr_partialQ_mul (fun y : Plane => w y 0) (fun y : Plane => v y 0) hw0d hv0d z,
        sr_partialQ_mul (fun y : Plane => w y 1) (fun y : Plane => v y 1) hw1d hv1d z]
    have hFe : Cyl.partialEta (fun y : Plane => w y 0 * v y 0 + w y 1 * v y 1) z =
        Cyl.partialEta (fun y : Plane => w y 0) z * v z 0 +
          w z 0 * Cyl.partialEta (fun y : Plane => v y 0) z +
        (Cyl.partialEta (fun y : Plane => w y 1) z * v z 1 +
          w z 1 * Cyl.partialEta (fun y : Plane => v y 1) z) := by
      rw [sr_partialEta_add (fun y : Plane => w y 0 * v y 0) (fun y : Plane => w y 1 * v y 1)
          (hw0d.mul hv0d) (hw1d.mul hv1d) z,
        sr_partialEta_mul (fun y : Plane => w y 0) (fun y : Plane => v y 0) hw0d hv0d z,
        sr_partialEta_mul (fun y : Plane => w y 1) (fun y : Plane => v y 1) hw1d hv1d z]
    rw [hQ, hE, hPQφ, hPEφ, hFq, hFe]
    simp only [sr_inner, sr_bilin0, sr_bilin1]
    linear_combination (-(φ z.2 * (w z 0 * v z 0 + w z 1 * v z 1))) * hdz
  -- cell integration by parts for both fluxes
  have hZG0 := hZ c R hc hR _ hG0_1 hperG0 hG0_0
  have hZG1 := hZ c R hc hR _ hG1_1 hperG1 hG1_0
  have hint := sr_integral_split (Cyl.cell c) _ _ _ _ _ hkey hPQi hPEi hCi hBi hZG0.1 hZG1.2
  linarith [hint]

/-! ### The target -/

/-- **`PartI:T05b/2/4`, target `StretchIdentity`.** Uses the cutoff facts (`EtaCutoffFacts`),
the two toolkit integration leaves (`CellIntegrableOfSupport`, `CellDerivZero`) and the smoothness
of the slices (`TrainSliceSmooth`), as black boxes. -/
theorem stretchIdentity (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport) (hZ : CellDerivZero)
    (hS : TrainSliceSmooth) : StretchIdentity := by
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
  have hv'p : Cyl.IsPeriodic c (tr'.v s) := tr'.isTrain.periodic_v s hs
  have hwp : Cyl.IsPeriodic c (diffV tr tr' s) := by
    intro z
    show tr.v s (z.1 + c, z.2) - tr'.v s (z.1 + c, z.2) = tr.v s z - tr'.v s z
    rw [tr.isTrain.periodic_v s hs z, tr'.isTrain.periodic_v s hs z]
  have hdiv : ∀ z : Plane, Cyl.divergence (diffV tr tr' s) z = 0 := by
    intro z
    have h1 : Cyl.partialQ (fun y : Plane => tr.v s y 0) z +
        Cyl.partialEta (fun y : Plane => tr.v s y 1) z = 0 :=
      tr.isTrain.solenoidal s hs z
    have h2 : Cyl.partialQ (fun y : Plane => tr'.v s y 0) z +
        Cyl.partialEta (fun y : Plane => tr'.v s y 1) z = 0 :=
      tr'.isTrain.solenoidal s hs z
    have hd0 : Differentiable ℝ (fun y : Plane => tr.v s y 0) :=
      (sr_comp_contDiff (tr.v s) 0 hvS).differentiable (by simp)
    have hd1 : Differentiable ℝ (fun y : Plane => tr.v s y 1) :=
      (sr_comp_contDiff (tr.v s) 1 hvS).differentiable (by simp)
    have hd0' : Differentiable ℝ (fun y : Plane => tr'.v s y 0) :=
      (sr_comp_contDiff (tr'.v s) 0 hv'S).differentiable (by simp)
    have hd1' : Differentiable ℝ (fun y : Plane => tr'.v s y 1) :=
      (sr_comp_contDiff (tr'.v s) 1 hv'S).differentiable (by simp)
    show Cyl.partialQ (fun y : Plane => tr.v s y 0 - tr'.v s y 0) z +
        Cyl.partialEta (fun y : Plane => tr.v s y 1 - tr'.v s y 1) z = 0
    rw [sr_partialQ_sub _ _ hd0 hd0' z, sr_partialEta_sub _ _ hd1 hd1' z]
    linarith
  have hcore := sr_core c R hc hR (etaCutoff R) hφ hφ0 hφ1 (diffV tr tr' s) (tr'.v s) hwS hv'S
    hwp hv'p hdiv hI hZ
  unfold cutoffStretch stretchRhs
  exact hcore

end UnforcedLeray.Short.PartI
