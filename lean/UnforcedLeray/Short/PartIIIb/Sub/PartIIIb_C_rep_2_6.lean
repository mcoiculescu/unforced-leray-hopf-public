import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs

/-!
# Decomposition of `SepX0FreeEq` (`ward:shifted-resolvent`, source 4199-4200)

Source of record: `the November 2 reference manuscript`,
lines 4199-4200 (`D_{μ+1}X₀ = W_μ`), 3800-3807, 3603-3626, 5223.

With `l = e^{-h/2}` (`dl = -(l/2) dh`) the separated response is
`W_m(y,τ) = -∫_0^∞ G_m(h,y,·) * T(τ-h) dh`, `G_m(h,y,z) = e^{-(m+3/2)h} ∇K_{ν(1-e^{-h})}(y - e^{-h/2} z)`.
`X₀ = W_μ - W_{μ+1}` has kernel `Kd = G_μ - G_{μ+1}`, `Kd(0) = 0`.  With
`L = ½ y·∇_y + νΔ_y`, the kernel identity `(∂_h - L + m - ½)G_m = 0` (heat equation and
homogeneity `K_{s²t}(sx) = s^{-3}K_t(x)`) gives `(∂_h - L + μ + ½)Kd = G_μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `G_m(h,y,z)_{i;jk} = e^{-(m+3/2)h} ∂_k (K_{ν(1-e^{-h})})_{ij}(y - e^{-h/2} z)`. -/
def Gker (ν : ℝ) (m : ℂ) (h : ℝ) (y z : Space) (i j k : Fin 3) : ℂ :=
  Complex.exp (-(m + 3 / 2) * (h : ℂ)) *
    ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x)
      (y - Real.exp (-h / 2) • z) (UnforcedLeray.coordinateVector k) : ℝ) : ℂ)

/-- `Kd = G_μ - G_{μ+1}`, the kernel of `X₀ = W_μ - W_{μ+1}`. -/
def Kd (ν μ : ℝ) (h : ℝ) (y z : Space) (i j k : Fin 3) : ℂ :=
  Gker ν (μ : ℂ) h y z i j k - Gker ν ((μ : ℂ) + 1) h y z i j k

/-- The kernel integral `-∫_0^∞ ∫ Φ(h,y,z) : T(τ-h,z) dz dh` (component `i`). -/
def kerInt (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (τ : ℝ) (y : Space) (i : Fin 3) : ℂ :=
  -∫ h in Ioi (0 : ℝ), ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
    Φ h y z i j k * ((T (τ - h) z j k : ℝ) : ℂ)

/-- `L Φ = ½ y·∇_yΦ + νΔ_yΦ` for a complex-valued kernel. -/
def Lker (ν : ℝ) (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ)
    (h : ℝ) (y z : Space) (i j k : Fin 3) : ℂ :=
  (1 / 2 : ℂ) * fderiv ℝ (fun y' => Φ h y' z i j k) y y +
    (ν : ℂ) * ∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Φ h y'' z i j k) y'
      (UnforcedLeray.coordinateVector l)) y (UnforcedLeray.coordinateVector l)

/-- `(∂_h - L + μ + ½) Kd`. -/
def KdOp (ν μ : ℝ) (h : ℝ) (y z : Space) (i j k : Fin 3) : ℂ :=
  deriv (fun h' => Kd ν μ h' y z i j k) h - Lker ν (Kd ν μ) h y z i j k +
    ((μ : ℂ) + 1 / 2) * Kd ν μ h y z i j k

/-- **(R) h-representation** (source 3611-3621, substitution `l = e^{-h/2}` in `sepW`). -/
def SepWHRep : Prop :=
  ∀ (ν : ℝ) (m : ℂ) (rOut P : ℝ), 0 < ν → -(1 / 4) < m.re → 0 ≤ rOut → 0 < P →
    ∀ T, IIIa.IsSepSource P rOut T → SepMoment P T →
      ∀ (τ : ℝ) (y : Space) (i : Fin 3), IIIa.sepW ν m T y τ i = kerInt T (Gker ν m) τ y i

/-- **(K) kernel identity** (source 3603-3610: heat equation `∂_tK = ΔK`, homogeneity
`x·∇∇K_t + 2t∂_t∇K_t = -4∇K_t`, `t(h) = ν(1-e^{-h})`): for `h > 0`,
`(∂_h - L + μ + ½)(G_μ - G_{μ+1}) = G_μ` (the `G_m` satisfy `(∂_h - L + m - ½)G_m = 0`). -/
def SepKerPDE : Prop :=
  ∀ (ν μ : ℝ), 0 < ν → ∀ h : ℝ, 0 < h → ∀ (y z : Space) (i j k : Fin 3),
    KdOp ν μ h y z i j k = Gker ν (μ : ℂ) h y z i j k

/-- **(C) τ- and y-differentiation under the integral** (source 4199-4200, 5223; `Kd(0) = 0` so no
instantaneous term and no phase derivative of `T`; dominated convergence with `SepMoment`;
`y`-derivatives as in `sepWSmoothOn_of`, `Sub/IIIb-D2_3_1_1/L2.lean`):
`D_{μ+1}X₀ = Re(-∫_0^∞∫ (∂_h - L + μ + ½)Kd : T(τ-h) dz dh)` off the old disk. -/
def SepX0Comb : Prop :=
  ∀ (ν μ rOut P : ℝ), 0 < ν → -(1 / 4) < μ → 0 ≤ rOut → 0 < P →
    ∀ T, IIIa.IsSepSource P rOut T → SepMoment P T →
      ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ i : Fin 3,
        physDmu ν (μ + 1) (sepX0 ν μ T) τ y i = (kerInt T (KdOp ν μ) τ y i).re

theorem sepX0FreeEq_of (hR : SepWHRep) (hK : SepKerPDE) (hC : SepX0Comb) : SepX0FreeEq := by
  intro ν μ rOut P hν hμ hr hP T hT hM τ y hy
  ext i
  have h1 := hC ν μ rOut P hν hμ hr hP T hT hM τ y hy i
  have h2 : kerInt T (KdOp ν μ) τ y i = kerInt T (Gker ν (μ : ℂ)) τ y i := by
    unfold kerInt
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
    simp only [hK ν μ hν h hh y]
  have h3 := hR ν (μ : ℂ) rOut P hν (by simpa using hμ) hr hP T hT hM τ y i
  simp only [sepWre]
  rw [h1, h2, ← h3]

end UnforcedLeray.Short.PartIIIb.Concrete
