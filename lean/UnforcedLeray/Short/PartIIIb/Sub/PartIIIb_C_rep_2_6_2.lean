import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6

/-!
# Decomposition of `SepKerPDE` (`sep:kernel`, source 3603-3610, 3800-3807)

Source `the November 2 reference manuscript`.
With `t(h) = ν(1-e^{-h})`, `G_m(h,y,z) = e^{-(m+3/2)h} ∇K_{t(h)}(y - e^{-h/2}z)`:
the per-`m` identity `(∂_h - L + m - 1/2) G_m = 0` (heat equation `∂_tK = ΔK`, Euler form of
`K_{s²t}(sx) = s^{-3}K_t(x)`) gives `(∂_h - L + μ + 1/2)(G_μ - G_{μ+1}) = G_μ` by algebra.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

/-- (a) joint regularity of `(t,x) ↦ K_t(x)` for `t > 0` (source 3603-3607, `K_t = δG_t + ∂∂∫_t^∞G`). -/
def HeatLerayKJointC3 : Prop :=
  ∀ i j : Fin 3, ContDiffOn ℝ 3 (fun p : ℝ × Space => IIIa.heatLerayK p.1 i j p.2)
    {p : ℝ × Space | 0 < p.1}

/-- (a') heat equation `∂_tK_t = ΔK_t` for `t > 0` (source 3603-3607, 3800). -/
def HeatLerayKHeat : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ (i j : Fin 3) (x : Space),
    HasDerivAt (fun s => IIIa.heatLerayK s i j x)
      (∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') y
        (UnforcedLeray.coordinateVector l)) x (UnforcedLeray.coordinateVector l)) t

/-- (b) Euler form of the homogeneity `K_{s²t}(sx) = s^{-3}K_t(x)` (source 3800-3807):
`x·∇(∂_kK_t) + 2t ∂_t ∂_kK_t = -4 ∂_kK_t`. -/
def HeatLerayKEuler : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ (i j k : Fin 3) (x : Space),
    fderiv ℝ (fun x' => fderiv ℝ (fun x'' => IIIa.heatLerayK t i j x'')
      x' (UnforcedLeray.coordinateVector k)) x x +
    2 * t * deriv (fun s => fderiv ℝ (fun x' => IIIa.heatLerayK s i j x') x
      (UnforcedLeray.coordinateVector k)) t =
    -4 * fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') x (UnforcedLeray.coordinateVector k)

/-- (c) per-`m` `h`-identity (chain rule with `t'(h) = νe^{-h}`, `d/dh(y - e^{-h/2}z) = ½(y-(y-e^{-h/2}z))`,
(a'), (a), (b), and `νe^{-h} + t(h) = ν`): `∂_hG_m = L G_m - (m - ½)G_m` for `h > 0`. -/
def GkerHasDerivH : Prop :=
  ∀ (ν : ℝ) (m : ℂ), 0 < ν → ∀ (h : ℝ), 0 < h → ∀ (y z : Space) (i j k : Fin 3),
    HasDerivAt (fun h' => Gker ν m h' y z i j k)
      (Lker ν (Gker ν m) h y z i j k - (m - 1 / 2) * Gker ν m h y z i j k) h

/-- (d) `L` is linear on the two kernels `G_μ, G_{μ+1}` (both are `C²` in `y` for `h > 0` by
`HeatLerayKSmooth`, `Sub/IIIb-D2_3_1_1_2.lean`). -/
def LkerKdSplit : Prop :=
  ∀ (ν μ : ℝ), 0 < ν → ∀ (h : ℝ), 0 < h → ∀ (y z : Space) (i j k : Fin 3),
    Lker ν (Kd ν μ) h y z i j k =
      Lker ν (Gker ν (μ : ℂ)) h y z i j k - Lker ν (Gker ν ((μ : ℂ) + 1)) h y z i j k

theorem sepKerPDE_of (hG : GkerHasDerivH) (hL : LkerKdSplit) : SepKerPDE := by
  intro ν μ hν h hh y z i j k
  have h1 := hG ν (μ : ℂ) hν h hh y z i j k
  have h2 := hG ν ((μ : ℂ) + 1) hν h hh y z i j k
  have hd : deriv (fun h' => Kd ν μ h' y z i j k) h =
      (Lker ν (Gker ν (μ : ℂ)) h y z i j k - ((μ : ℂ) - 1 / 2) * Gker ν (μ : ℂ) h y z i j k) -
      (Lker ν (Gker ν ((μ : ℂ) + 1)) h y z i j k
        - (((μ : ℂ) + 1) - 1 / 2) * Gker ν ((μ : ℂ) + 1) h y z i j k) :=
    (h1.sub h2).deriv
  unfold KdOp
  rw [hd, hL ν μ hν h hh y z i j k]
  unfold Kd
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
