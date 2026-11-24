import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3

/-!
# Decomposition of `VtvTimeFubini` (source 4610, last clause of `VtvHyps`)

Source of record: `the November 2 reference manuscript`
(line 4610: the integrated Duhamel identity `Y(s,φ) = ∫₀^s R(r,φ) dr`; 3511-3514 for the pairing).

With `φ_s = ∂_sη(s)` (a cylinder test, `VtvDerivCyl`) and
`F(s,r) = 1_{r ≤ s} R(r,φ_s)`:
`∫ Y(s,φ_s) ds = ∫_s ∫_r F(s,r) dr ds` (Duhamel slice, proved here as `vtvDuhamelSlice`)
`= ∫_r ∫_s F(s,r) ds dr` (Fubini; `VtvFubiniJoint` gives `F ∈ L¹`)
`= -∫_r R(r,η(r)) dr` (`VtvFubiniInner`: `∫_r^∞ R(r,∂_sη(s)) ds = -R(r,η(r))`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **`∂_sη(s)` is a cylinder test** (for every `s`): `η` is jointly smooth, so
`x ↦ ∂_sη(s,x)` is smooth (derivative of a jointly smooth function in one variable), `c`-periodic
(differentiate the periodicity of each `η(s')`), and vanishes for `|x.2| > R` (the band clause of
`IsStreamTest`). -/
def VtvDerivCyl : Prop :=
  ∀ (c : ℝ) (η : ℝ → ℝ × ℝ → ℝ), IsStreamTest c η → ∀ s : ℝ,
    B0579.IsCylTest c (fun x => deriv (fun s' => η s' x) s)

/-- **Joint integrability of the Duhamel triangle** (source 4610): with
`F(s,r) = 1_{r ≤ s} R(r,∂_sη(s))`, `F` is integrable on `(0,∞)²`.  It vanishes for `s ∉ [s₁,s₂]`.
For `r` bounded below (`r ≥ r₀`) the pairing bounds of the `Y`/`R` leaves of `VtvTimeIntegrable`
apply uniformly in `s` (`ω` is paired through `b`, `energyLoc`, `f` in `L²` on bands); near `r = 0`
only the entrance control is available (`zeroEntrance` of `IsEnergyField`, and the integrability of
`r ↦ R(r,φ)` on `(0,s]` from the last clause of `VtvHyps`), with the constant depending on `φ_s`
through its `C²` norm, which is uniformly bounded in `s`; also joint measurability of
`(s,r) ↦ R(r,φ_s)` (parametric integrals of jointly measurable integrands). -/
def VtvFubiniJoint : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η →
      Integrable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then
          vtvR μ tr ω g b p.2 (fun x => deriv (fun s' => η s' x) p.1) else 0)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))

/-- **The inner `s`-integral** (source 4610): for almost every `r > 0` (clause 6 of `VtvHyps` gives
`f(r,·) ∈ L²` of the cell only for a.e. `r`, which is what makes `φ ↦ ∫ g(r) φ` linear),
`∫_{s ≥ r} R(r,∂_sη(s)) ds = -R(r,η(r))`.  Route: `R(r,·)` is linear and continuous on the
cylinder tests supported in the common band `|η| ≤ R₀` (`ω(r)·1_{|η|≤R₀+1}` is integrable by the
last clause of `VtvHyps` applied to a cutoff cylinder test equal to `1` on the band; `g(r)` through
the curl clause; the flow terms are `ω`-pairings with `νΔφ+v·∇φ` and `b`-pairings with
`φ ∇E`); a second Fubini in `(s,x)` over the compact `s`-range `[r,s₂]` exchanges `∫ds` with the
cell integral, and `∫_r^∞ ∂_sη(s,x) ds = -η(r,x)` (fundamental theorem of calculus, `η(s)=0` for
`s ≥ s₂`). -/
def VtvFubiniInner : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η →
      ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ s in Ioi (0 : ℝ), (if r ≤ s then
          vtvR μ tr ω g b r (fun x => deriv (fun s' => η s' x) s) else 0) =
        - vtvR μ tr ω g b r (η r)

/-- **Duhamel on a slice**: for a cylinder test `φ` (time independent) and `s > 0`,
`Y(s,φ) = ∫_{(0,s]} R(r,φ) dr` (last clause of `VtvHyps`). -/
theorem vtvDuhamelSlice {ν c μ : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {ω g : ℝ → ℝ × ℝ → ℂ} {b : Chart → Fin 2 → ℂ} {G : Chart → Fin 2 → Fin 2 → ℂ}
    {f : Chart → Fin 2 → ℂ} (H : VtvHyps ν c μ tr ω g b G f) {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) {s : ℝ} (hs : 0 < s) :
    vtvY μ c ω s φ = ∫ r in Ioc 0 s, vtvR μ tr ω g b r φ := by
  obtain ⟨h1, h2, h3⟩ := H.2.2.2.2.2.2.2.1 φ hφ s hs
  unfold vtvY vtvR
  rw [h3]
  simp_rw [mul_add]
  rw [integral_add h1 h2]

/-- Reduction of `VtvTimeFubini` to the leaves. -/
theorem vtvTimeFubini_of (hD : VtvDerivCyl) (hJ : VtvFubiniJoint) (hI : VtvFubiniInner) :
    VtvTimeFubini := by
  intro ν c μ tr ω g b G f H η hη
  have hY : ∀ s ∈ Ioi (0 : ℝ), vtvY μ c ω s (fun x => deriv (fun s' => η s' x) s) =
      ∫ r in Ioi (0 : ℝ), (if r ≤ s then
          vtvR μ tr ω g b r (fun x => deriv (fun s' => η s' x) s) else 0) := by
    intro s hs
    rw [vtvDuhamelSlice H (hD c η hη s) hs]
    have : (fun r : ℝ => if r ≤ s then
        vtvR μ tr ω g b r (fun x => deriv (fun s' => η s' x) s) else 0) =
        (Iic s).indicator (fun r => vtvR μ tr ω g b r (fun x => deriv (fun s' => η s' x) s)) := by
      funext r
      simp [Set.indicator_apply]
    rw [this, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]
  rw [setIntegral_congr_fun measurableSet_Ioi hY]
  have hsw := integral_integral_swap (f := fun s r : ℝ => if r ≤ s then
      vtvR μ tr ω g b r (fun x => deriv (fun s' => η s' x) s) else 0) (hJ ν c μ tr ω g b G f H η hη)
  rw [hsw]
  have hr : ∫ r in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), (if r ≤ s then
      vtvR μ tr ω g b r (fun x => deriv (fun s' => η s' x) s) else 0) =
      ∫ r in Ioi (0 : ℝ), - vtvR μ tr ω g b r (η r) :=
    setIntegral_congr_ae measurableSet_Ioi
      ((ae_restrict_iff' measurableSet_Ioi).1 (hI ν c μ tr ω g b G f H η hη)
        |>.mono fun r hr hm => hr hm)
  rw [hr, integral_neg]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
