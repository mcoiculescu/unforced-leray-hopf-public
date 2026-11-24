import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2

/-!
# Part I, `PartI:T04/9/1/2/2/2`: `APL2IBP` from four leaves (source lines 285-288)

`the November 2 reference manuscript` lines 285-288.  With `ω = curl v(s)`,
`P = ∂_qω`, `Q = ∂_ηω` and the vorticity right-hand side `F = -(v·∇ω) + νΔω`, the local vorticity
equation gives `∂_s P = ∂_q F`, `∂_s Q = ∂_η F` (leaf `APL2TimeDerivQE`).  The remaining identity is
a statement about one frozen smooth, periodic, divergence-free field `w = v(s)`:
`∫χ 2(P ∂_qF + Q ∂_ηF) = -2ν G² - 2X + E`, split into a pointwise-algebra leaf (`APL2FrozenAlg`),
the transport integration by parts (`APL2FrozenTransport`) and the viscous integration by parts
(`APL2FrozenViscous`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The vorticity right-hand side `F = -(w·∇ω) + νΔω` for a frozen field `w` and `ω = curl w`
(`ω_s = F`, line 285). -/
def apL2F (ν : ℝ) (w : Plane → Vec) (z : Plane) : ℝ :=
  -(w z 0 * Cyl.partialQ (Cyl.curl w) z + w z 1 * Cyl.partialEta (Cyl.curl w) z)
    + ν * Train.lapS (Cyl.curl w) z

/-- The enstrophy-gradient density `g = (∂_qω)² + (∂_ηω)²` of a frozen field. -/
def apL2G (w : Plane → Vec) (z : Plane) : ℝ :=
  Cyl.partialQ (Cyl.curl w) z ^ 2 + Cyl.partialEta (Cyl.curl w) z ^ 2

/-- **Leaf A (time derivative of the vorticity gradient)** (lines 285-288): for `s ∈ (0,T)`,
`∂_s ∂_qω = ∂_q F` and `∂_s ∂_ηω = ∂_η F` pointwise.  Route: `localVorticityEquation`
(`Sub/T02_4.lean:71`, `ω_s = F` on `(0,T) × Plane`), smoothness of `v` on `(0,T) × Plane`
(`IsClassicalOn.smooth_v`), commuting `∂_s` with `∂_q`, `∂_η` (symmetry of mixed partials for the
`C^∞` function `(s,z) ↦ ω`; `CurlRegularity`), and `partialQ` of the identity `ω_t = F_t` on the
open set `Ioo 0 T`. -/
def APL2TimeDerivQE : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ s ∈ Ioo (0 : ℝ) T, ∀ z : Plane,
      deriv (fun t => Cyl.partialQ (Cyl.curl (v t)) z) s = Cyl.partialQ (apL2F ν (v s)) z ∧
      deriv (fun t => Cyl.partialEta (Cyl.curl (v t)) z) s = Cyl.partialEta (apL2F ν (v s)) z

/-- **Leaf B1 (frozen field: pointwise algebra, integrated)** (lines 285-288): for a `C^∞`,
`c`-periodic, divergence-free `w`, `R ≥ 1`, `φ = χ_R`:
`∫χ 2(P ∂_qF + Q ∂_ηF) = -2 X_R + ∫χ(-(w_0 ∂_q g + w_1 ∂_η g)) + 2ν ∫χ (P ΔP + Q ΔQ)` with
`P = ∂_qω`, `Q = ∂_ηω`, `g = P² + Q²`, `ΔP = lapS P`.  Pointwise: Leibniz on `∂_qF`, `∂_ηF`,
`∂_q∂_ηω = ∂_η∂_qω` and `∂_qΔω = Δ∂_qω`, `∂_ηΔω = Δ∂_ηω` (Schwarz, `C^∞`); then integrate
(continuous, compact `η`-support, `apHD_integ`) and split the integral. -/
def APL2FrozenAlg : Prop :=
  ∀ (ν c R : ℝ) (w : Plane → Vec), 0 < ν → 1 ≤ c → 1 ≤ R → ContDiff ℝ ∞ w →
    Cyl.IsPeriodic c w → (∀ z, Cyl.divergence w z = 0) →
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
          (2 * (Cyl.partialQ (Cyl.curl w) z * Cyl.partialQ (apL2F ν w) z
            + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta (apL2F ν w) z)))
        = -2 * apL2X c (fun _ => w) R 0
          + (∫ z in Cyl.cell c, etaCutoff R z.2 *
              (-(w z 0 * Cyl.partialQ (apL2G w) z + w z 1 * Cyl.partialEta (apL2G w) z)))
          + 2 * ν * ∫ z in Cyl.cell c, etaCutoff R z.2 *
              (Cyl.partialQ (Cyl.curl w) z * Train.lapS (Cyl.partialQ (Cyl.curl w)) z
                + Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z)

/-- **Leaf B2 (transport integration by parts)** (lines 285-288): same hypotheses,
`∫χ(-(w_0 ∂_q g + w_1 ∂_η g)) = ∫χ' w_1 g` (`q`-periodicity with `div w = 0`, `η`-integration by
parts, compact support of `χ_R`; `Cyl.integral_cell_partialQ_mul`, `Cyl.integral_cell_partialEta_mul`,
as `q1`, `e1` in `apHD_core`). -/
def APL2FrozenTransport : Prop :=
  ∀ (c R : ℝ) (w : Plane → Vec), 1 ≤ c → 1 ≤ R → ContDiff ℝ ∞ w →
    Cyl.IsPeriodic c w → (∀ z, Cyl.divergence w z = 0) →
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
          (-(w z 0 * Cyl.partialQ (apL2G w) z + w z 1 * Cyl.partialEta (apL2G w) z)))
        = ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * w z 1 * apL2G w z

/-- **Leaf B3 (viscous integration by parts)** (lines 285-288): same hypotheses (no divergence),
`∫χ(P ΔP + Q ΔQ) = -∫χ eucJet2 ω - ∫χ'(P ∂_ηP + Q ∂_ηQ)`: for `h ∈ {P,Q}`,
`∫χ h (∂_q∂_q h + ∂_η∂_η h) = -∫χ((∂_qh)² + (∂_ηh)²) - ∫χ' h ∂_ηh` (as `q2`, `e2` in `apHD_core`),
and `Σ_{h∈{P,Q}} ((∂_qh)² + (∂_ηh)²) = eucJet2 ω` by definition. -/
def APL2FrozenViscous : Prop :=
  ∀ (c R : ℝ) (w : Plane → Vec), 1 ≤ c → 1 ≤ R → ContDiff ℝ ∞ w → Cyl.IsPeriodic c w →
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
          (Cyl.partialQ (Cyl.curl w) z * Train.lapS (Cyl.partialQ (Cyl.curl w)) z
            + Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z))
        = -(∫ z in Cyl.cell c, etaCutoff R z.2 * eucJet2 (Cyl.curl w) z)
          - ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 *
              (Cyl.partialQ (Cyl.curl w) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z
                + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z)

/-- Each time slice of a classical solution is `C^∞`. -/
theorem apL2_slice_smooth {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (h : IsClassicalOn ν c T v p) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) : ContDiff ℝ ∞ (v s) := by
  have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  have hO : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    h.smooth_v.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
  have h2 : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    contDiff_const.prodMk contDiff_id
  have := h1.comp_contDiff h2 (fun z => ⟨hs, mem_univ _⟩)
  exact this

theorem aPL2IBP_of (hA : APL2TimeDerivQE) (hB1 : APL2FrozenAlg) (hB2 : APL2FrozenTransport)
    (hB3 : APL2FrozenViscous) : APL2IBP := by
  intro ν c T v p hν hc hcls R hR s hs
  have hcl := hcls.classical
  have hsm := apL2_slice_smooth hcl hs
  have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  have hper := hcl.periodic_v s hs'
  have hdiv := hcl.solenoidal s hs'
  have hW : apL2W c v R s = ∫ z in Cyl.cell c, etaCutoff R z.2 *
      (2 * (Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (apL2F ν (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (apL2F ν (v s)) z)) := by
    unfold apL2W
    congr 1
    funext z
    rw [(hA ν c T v p hν hc hcls s hs z).1, (hA ν c T v p hν hc hcls s hs z).2]
  have e1 := hB1 ν c R (v s) hν hc hR hsm hper hdiv
  have e2 := hB2 c R (v s) hc hR hsm hper hdiv
  have e3 := hB3 c R (v s) hc hR hsm hper
  rw [e2, e3] at e1
  rw [hW, e1]
  have hX : apL2X c (fun _ => v s) R 0 = apL2X c v R s := rfl
  have hG : apCutG c 2 v R s = ∫ z in Cyl.cell c, etaCutoff R z.2 * eucJet2 (Cyl.curl (v s)) z := by
    simp [apCutG, eucJetN]
  have hE : apL2E ν c v R s =
      (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * v s z 1 * apL2G (v s) z)
        - 2 * ν * (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 *
          (Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
            + Cyl.partialEta (Cyl.curl (v s)) z *
              Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z)) := rfl
  rw [apL2Rhs, hX, hG.symm, hE]
  ring
