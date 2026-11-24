import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Norm

/-!
# Decomposition of `PartII-b:P1/1/1` (`BLRange`)

Source: `the November 2 reference manuscript` 1902-1906 (every real solenoidal
`𝒪`-invariant `f ∈ Y_{q₀}` is `N_v b` a.e. for a `c`-periodic profile `b ∈ H_p`; inverse chart
`(τ,ϱ,z) ↔ (s,q,η)` mod the period).

Steps: (1) `rep f` is real a.e.; (2) a.e. phase slice of `Re rep f` is axisymmetric without swirl
(from `Osym`); (3) the inverse-chart profile `B` of a measurable `P`-periodic field with
axisymmetric slices reproduces it (this is the body of `Lib/AxisymmetricB/Unitary.lean`
`mem_range_Jv` without `L²`); (4) `B ∈ L^{q₀}(ageμ)` from the finite `Y_{q₀}` norm
(`eLpNorm_Nv`); (5) the periodic profile of an `H_p` class agrees a.e. with the lift of any
a.e.-representative (chart null pullback).  `blRange_of` assembles them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- (1) A real element `f` of `Y_{q₀}` has real joint representative a.e. (`realSub`; SP 1902). -/
def BLRReal : Prop :=
  ∀ (p : Params) (f : p.Y), ∀ᵐ x : ℝ × Space,
    rep (f : Yq p.period q0E) x.1 x.2 =
      realC (reP (rep (f : Yq p.period q0E) x.1 x.2))

/-- (2) An `𝒪`-invariant `f` has, for a.e. phase `τ`, the slice `Re rep f (τ, ·)` axisymmetric
without swirl (`Osym`, `rep_slice`; SP 1902-1903). -/
def BLRAxi : Prop :=
  ∀ (p : Params) (f : p.Y), ∀ᵐ τ : ℝ,
    IsAxisymmetricNoSwirl (fun y => reP (rep (f : Yq p.period q0E) τ y))

/-- (3) Inverse chart (SP 1902-1906; `invLift`, `avgMer`, `liftFun_invLift`, `ae_eq_avgLift`,
`mem_range_Jv` of `Lib/AxisymmetricB/Unitary.lean` without the `L²` hypothesis): a measurable
`P`-periodic field whose phase slices are axisymmetric without swirl equals, a.e. on `ℝ × ℝ³`,
the ring lift `N_v` of a `c`-periodic extension of a measurable profile. -/
def BLRLift : Prop :=
  ∀ (R c P : ℝ), 0 < R → 0 < c → P = 2 * c / R →
    ∀ W : ℝ × Space → Space, Measurable W → (∀ τ y, W (τ + P, y) = W (τ, y)) →
      (∀ᵐ τ : ℝ, IsAxisymmetricNoSwirl (fun y => W (τ, y))) →
      ∃ B : ℝ × (ℝ × ℝ) → Axi.Merid, Measurable B ∧
        ∀ᵐ x : ℝ × Space, W x = Axi.Nv R (Axi.perExt c B) x.1 x.2

/-- (4) Finite `H_p` norm of the profile (`Axi.eLpNorm_Nv`, `Axi.perExt_ae_eq`). -/
def BLRNorm : Prop :=
  ∀ (R c P : ℝ), 0 < R → 0 < c → P = 2 * c / R →
    ∀ B : ℝ × (ℝ × ℝ) → Axi.Merid, Measurable B →
      phaseLpNorm P bgp (fun x => realC (Axi.Nv R (Axi.perExt c B) x.1 x.2)) < ⊤ →
      eLpNorm B (ENNReal.ofReal bgp) (hMeas c bgp) < ⊤

/-- (5) The `c`-periodic profile of an `H_p` class lifts, a.e., like any measurable
representative (`ChartNullPullback`, `toProf_ae_eq`, `Axi.perExt_ae_eq`, `NvC` is the lift of real
and imaginary parts). -/
def BLRCongr : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c →
    ∀ (g : HpR c) (B : ℝ × (ℝ × ℝ) → Axi.Merid), Measurable B →
      (g : ℝ × (ℝ × ℝ) → Axi.Merid) =ᵐ[hMeas c bgp] B →
      ∀ᵐ x : ℝ × Space, NvC R (toProf c g) x = realC (Axi.Nv R (Axi.perExt c B) x.1 x.2)

theorem blRange_of (h1 : BLRReal) (h2 : BLRAxi) (h3 : BLRLift) (h4 : BLRNorm)
    (h5 : BLRCongr) : BLRange := by
  intro dm dp hdm p d hreg f
  have hR : 0 < p.R := by unfold Params.R; exact inv_pos.2 p.ε_pos
  have hc : 0 < p.c := p.c_pos
  have hP : p.period = 2 * p.c / p.R := by
    unfold Params.period Params.R
    field_simp
  haveI : Fact (0 < p.period) := inferInstance
  set W : ℝ × Space → Space := fun x => reP (rep (f : Yq p.period q0E) x.1 x.2) with hW
  have hWm : Measurable W := by
    have hs := stronglyMeasurable_rep (f : Yq p.period q0E)
    have hm : Measurable fun x : ℝ × Space => rep (f : Yq p.period q0E) x.1 x.2 :=
      hs.measurable
    have hcont : Continuous reP := by
      unfold reP
      fun_prop
    exact hcont.measurable.comp hm
  have hWper : ∀ τ y, W (τ + p.period, y) = W (τ, y) := by
    intro τ y
    simp only [hW, rep_add_period]
  obtain ⟨B, hBm, hB⟩ := h3 p.R p.c p.period hR hc hP W hWm hWper (h2 p f)
  have hrepB : ∀ᵐ x : ℝ × Space, rep (f : Yq p.period q0E) x.1 x.2 =
      realC (Axi.Nv p.R (Axi.perExt p.c B) x.1 x.2) := by
    filter_upwards [h1 p f, hB] with x a b
    rw [a, ← b]
  have hnorm : phaseLpNorm p.period bgp
      (fun x => realC (Axi.Nv p.R (Axi.perExt p.c B) x.1 x.2)) < ⊤ := by
    rw [← phaseLpNorm_congr_ae' hrepB]
    have h := enorm_eq_phaseLpNorm_rep (P := p.period) (q := q0E) q0E_ne_top'
      (f : Yq p.period q0E)
    rw [q0E_toReal] at h
    rw [← h]
    exact enorm_lt_top
  have hfin := h4 p.R p.c p.period hR hc hP B hBm hnorm
  have hmem : MemLp B (ENNReal.ofReal bgp) (hMeas p.c bgp) :=
    ⟨hBm.aestronglyMeasurable, hfin⟩
  refine ⟨hmem.toLp B, ?_⟩
  have h5' := h5 p.R p.c hR hc (hmem.toLp B) B hBm hmem.coeFn_toLp
  filter_upwards [hrepB, h5'] with x a b
  rw [a, b]

end UnforcedLeray.Short.IIb
