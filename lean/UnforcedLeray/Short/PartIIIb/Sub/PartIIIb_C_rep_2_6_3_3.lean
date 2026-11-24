import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2

/-!
# Decomposition of `sepX0YGrad` and `sepX0Lap` (`PartIII-b:C/rep/2/6/3/3`, `.../3/4`)

Source `the November 2 reference manuscript`
lines 3603-3626, 3800-3807, 4171-4200, 5223.  `X₀ = Re kerInt Kd` off the old disk (`SepX0KerInt`);
the `y`-derivatives of `X₀` are then the real parts of the `y`-derivatives of `kerInt Kd`, and these
are computed under the integral (kernel smooth in `y` off the source disk, uniform majorant from
`IIIa.SepKernelBounds`, as in `sepWSmoothOn_of`).  The analytic content is the two Props
`KerIntD1`, `KerIntD2` (differentiation under `kerInt`); the real-part and `EuclideanSpace`
assembly is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(D1)** first `y`-derivative of `kerInt Kd` under the integral, off the old disk (source
3603-3626, 5223): the kernel `Kd(h,·,z)` is `C²` for `h > 0`, `D_y^n Kd` (`n ≤ 2`) is dominated near
`y` by an integrable majorant in `(h,z)` against `T(τ-h,z)` (`IIIa.SepKernelBounds`,
`|y - e^{-h/2}z| ≥ c(1+e^{-h/2}|z|)` on `supp T`, `SepMoment`, `Re μ > -1/4`). -/
def KerIntD1 : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ i : Fin 3,
      DifferentiableAt ℝ (fun y' => kerInt T (Kd ν μ) τ y' i) y ∧
      ∀ v : Space, fderiv ℝ (fun y' => kerInt T (Kd ν μ) τ y' i) y v =
        kerInt T (fun h y z i j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y v) τ y i

/-- **(D2)** second `y`-derivative: differentiate `kerInt` of `∂_l Kd` once more under the integral
(same domination, order `n ≤ 2`). -/
def KerIntD2 : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ (l : Fin 3) (i : Fin 3),
      DifferentiableAt ℝ (fun y' => kerInt T
        (fun h y z i j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y
          (UnforcedLeray.coordinateVector l)) τ y' i) y ∧
      ∀ v : Space, fderiv ℝ (fun y' => kerInt T
        (fun h y z i j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y
          (UnforcedLeray.coordinateVector l)) τ y' i) y v =
        kerInt T (fun h y z i j k => fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y'
          (UnforcedLeray.coordinateVector l)) y v) τ y i

lemma piLp_fderiv_apply {Ξ : Space → Space} {y : Space} (hΞ : DifferentiableAt ℝ Ξ y) (i : Fin 3)
    (v : Space) : (fderiv ℝ Ξ y v) i = fderiv ℝ (fun x => Ξ x i) y v := by
  have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (Ξ y) i).comp y hΞ.hasFDerivAt
  have h2 : fderiv ℝ (fun x => Ξ x i) y = PiLp.proj 2 (fun _ : Fin 3 => ℝ) i ∘L fderiv ℝ Ξ y :=
    h.fderiv
  rw [h2]; rfl

lemma fderiv_re_apply {f : Space → ℂ} {y : Space} (hf : DifferentiableAt ℝ f y) (v : Space) :
    fderiv ℝ (fun x => (f x).re) y v = (fderiv ℝ f y v).re := by
  have h := Complex.reCLM.hasFDerivAt.comp y hf.hasFDerivAt
  have h2 : fderiv ℝ (fun x => (f x).re) y = Complex.reCLM.comp (fderiv ℝ f y) := h.fderiv
  rw [h2]; rfl

lemma isOpen_gap (rOut : ℝ) : IsOpen {y : Space | rOut < ϱ y} :=
  isOpen_lt continuous_const (by unfold ϱ; fun_prop)

/-- Generic-direction first derivative of `sepX0`. -/
lemma sepX0_fderiv_gen (h1 : SepX0KerInt) (hD : KerIntD1) (ν μ rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hd : SepData ν μ rOut P T) (τ : ℝ) (y : Space)
    (hy : rOut < ϱ y) (v : Space) :
    fderiv ℝ (sepX0 ν μ T τ) y v = WithLp.toLp 2 fun i => (kerInt T
      (fun h y z i j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y v) τ y i).re := by
  have hev : sepX0 ν μ T τ =ᶠ[nhds y]
      fun y' => (WithLp.toLp 2 fun i => (kerInt T (Kd ν μ) τ y' i).re : Space) := by
    filter_upwards [(isOpen_gap rOut).mem_nhds hy] with y' hy'
    exact h1 ν μ rOut P T hd τ y' hy'
  rw [hev.fderiv_eq]
  have hdiff : DifferentiableAt ℝ
      (fun y' => (WithLp.toLp 2 fun i => (kerInt T (Kd ν μ) τ y' i).re : Space)) y := by
    refine (differentiableAt_piLp 2).2 fun i => ?_
    exact Complex.reCLM.differentiableAt.comp y (hD ν μ rOut P T hd τ y hy i).1
  ext i
  rw [piLp_fderiv_apply hdiff]
  show fderiv ℝ (fun x => (kerInt T (Kd ν μ) τ x i).re) y v = _
  rw [fderiv_re_apply (hD ν μ rOut P T hd τ y hy i).1, (hD ν μ rOut P T hd τ y hy i).2 v]

theorem sepX0YGrad_of (h1 : SepX0KerInt) (hD1 : KerIntD1) : SepX0YGrad := by
  intro ν μ rOut P T hd τ y hy
  rw [sepX0_fderiv_gen h1 hD1 ν μ rOut P T hd τ y hy y]
  rfl

theorem sepX0Lap_of (h1 : SepX0KerInt) (hD1 : KerIntD1) (hD2 : KerIntD2) : SepX0Lap := by
  intro ν μ rOut P T hd τ y hy l
  have hev : (fun y' => fderiv ℝ (sepX0 ν μ T τ) y' (UnforcedLeray.coordinateVector l))
      =ᶠ[nhds y] fun y' => (WithLp.toLp 2 fun i => (kerInt T
        (fun h y z i j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y
          (UnforcedLeray.coordinateVector l)) τ y' i).re : Space) := by
    filter_upwards [(isOpen_gap rOut).mem_nhds hy] with y' hy'
    exact sepX0_fderiv_gen h1 hD1 ν μ rOut P T hd τ y' hy' _
  rw [hev.fderiv_eq]
  have hdiff : DifferentiableAt ℝ (fun y' => (WithLp.toLp 2 fun i => (kerInt T
        (fun h y z i j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y
          (UnforcedLeray.coordinateVector l)) τ y' i).re : Space)) y := by
    refine (differentiableAt_piLp 2).2 fun i => ?_
    exact Complex.reCLM.differentiableAt.comp y (hD2 ν μ rOut P T hd τ y hy l i).1
  ext i
  rw [piLp_fderiv_apply hdiff]
  show fderiv ℝ (fun x => (kerInt T
        (fun h y z i j k => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y
          (UnforcedLeray.coordinateVector l)) τ x i).re) y _ = _
  rw [fderiv_re_apply (hD2 ν μ rOut P T hd τ y hy l i).1, (hD2 ν μ rOut P T hd τ y hy l i).2]
  rfl

/-! ### Leaf Props for `KerIntD1`, `KerIntD2` (domination in `(h,z)`, differentiation under `∫`) -/

/-- `dh ⊗ dz` on `(0,∞) × ℝ³`, the measure of `kerInt` (`l = e^{-h/2}`, `dl = (l/2) dh`). -/
def mHZ : Measure (ℝ × Space) := (volume.restrict (Ioi (0 : ℝ))).prod volume

/-- The scalar integrand of `kerInt` at `p = (h,z)`: `∑_{j,k} Φ(h,y,z)_{ijk} T(τ-h,z)_{jk}`. -/
def kerF (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (i : Fin 3) (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ)
    (p : ℝ × Space) (y : Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, Φ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)

/-- The `h`-majorant: `(l/2)(sepMajorant μ + sepMajorant (μ+1))(l,z)` with `l = e^{-h/2}`
(`dl = (l/2)dh`; `sepMajorant` is the `l`-variable majorant of `sepWSmoothOn_of`). -/
def gMaj (μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (n : ℕ)
    (p : ℝ × Space) : ℝ :=
  Real.exp (-p.1 / 2) / 2 * (sepMajorant (μ : ℂ) T τ n (Real.exp (-p.1 / 2), p.2) +
    sepMajorant ((μ : ℂ) + 1) T τ n (Real.exp (-p.1 / 2), p.2))

/-- **(L1)** `h`-form of the `sepPhi` integrand (source 3611-3621, `l = e^{-h/2}`,
`l^{2m+2}·l = e^{-(m+3/2)h}`, `2 log l = -h`): `kerF (Gker ν m) (h,z) y = -(l/2)·sepPhi ν m (l,z) y`
for every `h` (no sign condition). -/
def KerFGker : Prop :=
  ∀ (ν : ℝ) (m : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (p : ℝ × Space) (y : Space),
    kerF T τ i (Gker ν m) p y =
      -((Real.exp (-p.1 / 2) / 2 : ℝ) : ℂ) * sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2) y

/-- **(L2)** Fubini: the iterated integral `kerInt` is `-∫ kerF` over `mHZ` when integrable. -/
def KerIntProd : Prop :=
  ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (y : Space),
    Integrable (fun p => kerF T τ i Φ p y) mHZ →
      kerInt T Φ τ y i = -∫ p, kerF T τ i Φ p y ∂mHZ

/-- **(L3)** `fderiv` of `kerF` in `y` is `kerF` of the `fderiv` of the kernel (`T` is constant in
`y`, finite sums and products with constants). -/
def KerFFderiv : Prop :=
  ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (p : ℝ × Space) (y v : Space),
    (∀ j k : Fin 3, DifferentiableAt ℝ (fun y' => Φ p.1 y' p.2 i j k) y) →
      fderiv ℝ (kerF T τ i Φ p) y v =
        kerF T τ i (fun h y z i j k => fderiv ℝ (fun y'' => Φ h y'' z i j k) y v) p y

/-- **(L4)** smoothness of `y ↦ kerF (Kd) (h,z) y` for `h > 0` (`gker_contDiff`, `C²`). -/
def KdGapSmooth : Prop :=
  ∀ (ν μ : ℝ), 0 < ν → ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (p : ℝ × Space), 0 < p.1 → ContDiff ℝ 2 (kerF T τ i (Kd ν μ) p)

/-- **(L5)** pointwise gap bound in `(h,z)` (source 3604-3621 `sep:kernel`; from `sepGapPointwise`
and `IIIa.sepKernelBounds` via `KerFGker`; `ε` is the minimum of the `ε` for `μ` and `μ+1`). -/
def KdGapPt : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y₀ : Space), rOut < ϱ y₀ → ∀ i : Fin 3,
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball y₀ ε ⊆ {y : Space | rOut < ϱ y} ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℕ, n ≤ 2 → ∀ p : ℝ × Space, 0 < p.1 → ∀ y ∈ Metric.ball y₀ ε,
          ‖iteratedFDeriv ℝ n (kerF T τ i (Kd ν μ) p) y‖ ≤ C * gMaj μ T τ n p

/-- **(L6)** integrability of the `h`-majorant against `mHZ` (change of variables `l = e^{-h/2}`
from `sepGapMajorantIntegrable`, i.e. `integrable` transfer through `dl = (l/2)dh`). -/
def KdGapInt : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (n : ℕ), n ≤ 2 → Integrable (gMaj μ T τ n) mHZ

/-- **(L7)** measurability of the `y`-derivatives in `(h,z)` (`sepPhiMeasurable` composed with the
measurable `(h,z) ↦ (e^{-h/2}, z)`, via `KerFGker`). -/
def KdGapMeas : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (i : Fin 3) (n : ℕ), n ≤ 2 → ∀ y : Space,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (kerF T τ i (Kd ν μ) p) y) mHZ

/-- **(L8)** differentiation under the integral sign, first order (the first half of
`paramContDiff`, `hasFDerivAt_integral_of_dominated_of_fderiv_le`). -/
def ParamHasFDeriv1 : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (m : Measure α) (F : α → Space → ℂ) (U : Set Space)
    (g : ℕ → α → ℝ), IsOpen U → (∀ᵐ a ∂m, ContDiffOn ℝ 1 (F a) U) →
    (∀ n, n ≤ 1 → Integrable (g n) m) →
    (∀ n, n ≤ 1 → ∀ᵐ a ∂m, ∀ y ∈ U, ‖iteratedFDeriv ℝ n (F a) y‖ ≤ g n a) →
    (∀ n, n ≤ 1 → ∀ y ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) y) m) →
    ∀ y ∈ U, HasFDerivAt (fun y' => ∫ a, F a y' ∂m) (∫ a, fderiv ℝ (F a) y ∂m) y

end UnforcedLeray.Short.PartIIIb.Concrete
