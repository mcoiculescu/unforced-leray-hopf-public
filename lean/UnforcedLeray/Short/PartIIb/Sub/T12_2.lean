import UnforcedLeray.Short.PartIIb.Sub.T12

/-!
# Part II-b, task `PartII-b:T12/2` (`FlatLerayLiftOfSlice`): Sub-lemma Props and conditional assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1926 (`P_0` applied at
each age). Target: `FlatLerayLiftOfSlice : CylinderHelmholtzLr → FlatLerayHr` (`Sub/T12.lean`).

Status: the unconditional target is NOT proved here. This file contains

* six named Prop-level sub-lemmas `SlicePeriodicRep`, `SliceCylLpAe`, `SliceJointHelmholtz`,
  `SliceNormBound`, `SliceWeakSolenoidal`, `SlicePerpPlanar` (each a true statement, see the
  notes at its definition), and
* the conditional assembly `flatLerayLiftOfSlice_of` : (six sub-lemmas) → `FlatLerayLiftOfSlice`,
  proved in full from them (no placeholder proofs, no added hypotheses on the target).

The sub-lemmas carry the measure-theoretic work: exact `q`-periodic strongly measurable representative
of an `H_r` profile, the a.e.-slice `L^r` property, the jointly measurable slice operator (via
`Infra/JointMeasurableRep.lean`), the Tonelli norm bound, and the periodization of compact planar tests
to cell tests (`Lib/CylinderB/Periodize.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

/-- The bound clause of `CylinderHelmholtzLr` at fixed `c, r, C` for an operator `P`. -/
def HelmBoundP (c r C : ℝ) (P : (ℝ × ℝ → CMerid) → (ℝ × ℝ → CMerid)) : Prop :=
  ∀ F : ℝ × ℝ → CMerid, CylLp c r F →
    IsCylHelmholtz c r F (P F) ∧
      eLpNorm (P F) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- The a.e. linearity clause of `CylinderHelmholtzLr` at `c, r` for an operator `P`. -/
def HelmLinP (c r : ℝ) (P : (ℝ × ℝ → CMerid) → (ℝ × ℝ → CMerid)) : Prop :=
  ∀ (F₁ F₂ : ℝ × ℝ → CMerid) (a : ℂ), CylLp c r F₁ → CylLp c r F₂ →
    P (F₁ + a • F₂) =ᵐ[UnforcedLeray.Cyl.avgμ c] P F₁ + a • P F₂

/-- **Sub-lemma `LerayLift/1`** (periodic representative; SP 1923-1926 "periodize"). For `F ∈ H_r`
there is a strongly measurable `F'` that is exactly `q`-periodic and agrees with `F` both `H_r`-a.e. and
Lebesgue-a.e. on `{s > 0}`. Source: `exists_periodic_rep` (`Tasks/FlatCausal/DuhamelMeasurable/Periodic.lean`)
with the reduction `q ↦ redQ c q` (exact periodicity), plus `ageμ_eq_withDensity`
(`Tasks/HilbertEnergy/SPeriodic.lean`) for the `H_r`-a.e. half. -/
def SlicePeriodicRep : Prop :=
  ∀ (c r : ℝ), 0 < c → ∀ F : CProf, InHr c r F →
    ∃ F' : CProf, StronglyMeasurable F' ∧
      (∀ (s : ℝ) (z : ℝ × ℝ), F' (s, (z.1 + c, z.2)) = F' (s, z)) ∧
      (∀ᵐ x ∂(hMeas c r), F x = F' x) ∧
      (∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → F x = F' x)

/-- **Sub-lemma `LerayLift/2`** (a.e. slice in `L^r`; Tonelli). For strongly measurable, exactly periodic
`F'` with finite `H_r` norm, for `a.e.` `s > 0` the slice `F'(s, ·)` is `CylLp c r`. Proof: `Axi.lintegral_ageμ`
writes `hNorm` as an integral over `(0,∞) × qCell` with weight `c⁻¹ s^a > 0`, so the slice integrals
`∫_cell |F'(s,·)|^r` are finite for a.e. `s > 0`. -/
def SliceCylLpAe : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ F' : CProf, StronglyMeasurable F' →
    (∀ (s : ℝ) (z : ℝ × ℝ), F' (s, (z.1 + c, z.2)) = F' (s, z)) →
    hNorm c r F' < ⊤ →
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), CylLp c r (fun z => F' (s, z))

/-- **Sub-lemma `LerayLift/3`** (jointly measurable slice operator; SP 1923-1926, `P_0` at each age).
Given an operator `P` with the two clauses of `CylinderHelmholtzLr` at `c, r, C`, and a strongly measurable
exactly periodic `F'` of finite `H_r` norm, there is a strongly measurable exactly periodic `G` whose
slices are a.e. (on the cell) equal to `P` applied to the slices of `F'`, for a.e. `s > 0`.
Proof plan: `u s := [P (F'(s,·))]` in `Lp` (for a.e. `s` the slice is `CylLp` by `LerayLift/2`) is a
bounded linear image of the strongly measurable path `s ↦ [F'(s,·)]`, so it is strongly measurable;
`Infra/JointMeasurableRep.lean` `exists_stronglyMeasurable_rep` gives a jointly strongly measurable
`G₀` with `G₀(s,·) =ᵐ u s`; then `G z := G₀ (s, redQ c z)` is exactly periodic and still represents the
slices on the cell (`Tasks/FlatCausal/DuhamelMeasurable/Periodic.lean` `measurable_redCoord`). -/
def SliceJointHelmholtz : Prop :=
  ∀ (c r C : ℝ) (P : (ℝ × ℝ → CMerid) → (ℝ × ℝ → CMerid)), 0 < c → 1 < r → 0 < C →
    HelmBoundP c r C P → HelmLinP c r P →
    ∀ F' : CProf, StronglyMeasurable F' →
      (∀ (s : ℝ) (z : ℝ × ℝ), F' (s, (z.1 + c, z.2)) = F' (s, z)) →
      hNorm c r F' < ⊤ →
      ∃ G : CProf, StronglyMeasurable G ∧
        (∀ (s : ℝ) (z : ℝ × ℝ), G (s, (z.1 + c, z.2)) = G (s, z)) ∧
        ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
          (fun z => G (s, z)) =ᵐ[UnforcedLeray.Cyl.avgμ c] P (fun z => F' (s, z))

/-- **Sub-lemma `LerayLift/4`** (norm bound; Tonelli). If for a.e. `s > 0` the cell `L^r` norms of the
slices satisfy `‖G(s,·)‖ ≤ C ‖F'(s,·)‖`, then `‖G‖_{H_r} ≤ C ‖F'‖_{H_r}`. Proof: `Axi.lintegral_ageμ`
(`Lib/AxisymmetricB/Lift.lean`) and `lintegral_prod`/Tonelli for `(s, z)`, then raise to the power `r`. -/
def SliceNormBound : Prop :=
  ∀ (c r C : ℝ) (G F' : CProf), 0 < c → 0 < r → 0 ≤ C →
    StronglyMeasurable G → StronglyMeasurable F' →
    (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        eLpNorm (fun z => G (s, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
          ENNReal.ofReal C *
            eLpNorm (fun z => F' (s, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) →
    hNorm c r G ≤ ENNReal.ofReal C * hNorm c r F'

/-- **Sub-lemma `LerayLift/5`** (weak solenoidality from cell identities; SP 1923-1926). For strongly
measurable, exactly periodic `G ∈ H_r`, if for a.e. `s > 0` every cell test `Φ` (`CylTest c`) satisfies the
cell identity `∫_cell G(s,·)·∇Φ = 0` (integrable), then `G` is weakly solenoidal in `(q, η)`
(`WeakSolenoidal`). Proof: a compact planar test `φ` (supported in `s > 0`) is periodized in `q`
(`periodize`, a finite sum on compact support), `integral_cell_periodize_mul` (`Lib/CylinderB/Periodize.lean`)
turns the planar slice integral into a cell integral, `∂_q, ∂_η` commute with the periodization, and
Fubini in `s` gives the `Coord` identity. Integrability on `supp φ` uses `G ∈ L^r` (`InHr`) with `1 < r`
(local integrability, Hölder on a compact window) plus periodicity. The hypothesis `1 < r` is needed: for
`r ≤ 1` an `H_r` profile need not be locally integrable in `(s, q, η)` (e.g. `r = 1/2`,
`G = (f(s) k(η), 0)` with `f = |s - s₀|⁻¹ 1_{s ≥ s₀/2}`), and the planar pairing is then undefined. -/
def SliceWeakSolenoidal : Prop :=
  ∀ (c r : ℝ) (G : CProf), 0 < c → 1 < r → StronglyMeasurable G →
    (∀ (s : ℝ) (z : ℝ × ℝ), G (s, (z.1 + c, z.2)) = G (s, z)) →
    InHr c r G →
    (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ Φ : ℝ × ℝ → ℝ, CylTest c Φ →
        Integrable (fun z => G (s, z) 0 * (fderiv ℝ Φ z (1, 0) : ℂ) +
            G (s, z) 1 * (fderiv ℝ Φ z (0, 1) : ℂ)) (UnforcedLeray.Cyl.avgμ c) ∧
          ∫ z, (G (s, z) 0 * (fderiv ℝ Φ z (1, 0) : ℂ) + G (s, z) 1 * (fderiv ℝ Φ z (0, 1) : ℂ))
            ∂(UnforcedLeray.Cyl.avgμ c) = 0) →
    WeakSolenoidal G

/-- **Sub-lemma `LerayLift/6`** (orthogonality to planar solenoidal tests; SP 1923-1926). For
`F ∈ H_r` with exactly periodic strongly measurable representative `F'` (`F = F'` a.e. on `s > 0`) and
`G ∈ H_r` exactly periodic and strongly measurable, if for a.e. `s > 0` every cell solenoidal test `Ψ`
(`CylSolTest c`) satisfies `∫_cell (F'(s,·) - G(s,·))·Ψ = 0` (integrable), then `F - G` is orthogonal to
every planar solenoidal test (`PerpPlanarSol`). Proof: periodize the planar test `Ψ` in `q` (divergence
free, still compact), `integral_cell_periodize_mul` with the periodic factor `F' - G`, and Fubini in `s`.
As for `SliceWeakSolenoidal`, `1 < r` gives the local integrability of `(F - G)·Ψ` on `Coord`. -/
def SlicePerpPlanar : Prop :=
  ∀ (c r : ℝ) (F F' G : CProf), 0 < c → 1 < r → InHr c r F →
    StronglyMeasurable F' → (∀ (s : ℝ) (z : ℝ × ℝ), F' (s, (z.1 + c, z.2)) = F' (s, z)) →
    (∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → F x = F' x) →
    InHr c r G → StronglyMeasurable G →
    (∀ (s : ℝ) (z : ℝ × ℝ), G (s, (z.1 + c, z.2)) = G (s, z)) →
    (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, CylSolTest c Ψ →
        Integrable (fun z => ∑ i : Fin 2, (F' (s, z) i - G (s, z) i) * (Ψ z i : ℂ))
            (UnforcedLeray.Cyl.avgμ c) ∧
          ∫ z, ∑ i : Fin 2, (F' (s, z) i - G (s, z) i) * (Ψ z i : ℂ)
            ∂(UnforcedLeray.Cyl.avgμ c) = 0) →
    PerpPlanarSol (F - G)

/-- **Conditional assembly** of `FlatLerayLiftOfSlice` from the six sub-lemmas above. No placeholder
proofs; the target statement is not changed and no hypothesis is added to it. -/
theorem flatLerayLiftOfSlice_of (h1 : SlicePeriodicRep) (h2 : SliceCylLpAe)
    (h3 : SliceJointHelmholtz) (h4 : SliceNormBound) (h5 : SliceWeakSolenoidal)
    (h6 : SlicePerpPlanar) : FlatLerayLiftOfSlice := by
  intro hL r hr1 hr3
  obtain ⟨C, hC, hCL⟩ := hL r hr1
  refine ⟨C, hC, fun c hc F hF => ?_⟩
  obtain ⟨P, hPb, hPl⟩ := hCL c hc
  obtain ⟨F', hF's, hF'p, hFa, hFa'⟩ := h1 c r hc F hF
  have hF'eq : hNorm c r F' = hNorm c r F :=
    eLpNorm_congr_ae (hFa.mono fun x hx => hx.symm)
  have hF'fin : hNorm c r F' < ⊤ := by
    rw [hF'eq]
    exact hF.finite
  obtain ⟨G, hGs, hGper, hGjoint⟩ := h3 c r C P hc hr1 hC hPb hPl F' hF's hF'p hF'fin
  have hCyl := h2 c r hc hr1 F' hF's hF'p hF'fin
  have hbound : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      eLpNorm (fun z => G (s, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => F' (s, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
    filter_upwards [hGjoint, hCyl] with s hs hcs
    exact (eLpNorm_congr_ae hs).trans_le (hPb _ hcs).2
  have hGnorm : hNorm c r G ≤ ENNReal.ofReal C * hNorm c r F' :=
    h4 c r C G F' hc (by linarith) hC.le hGs hF's hbound
  have hGfin : hNorm c r G < ⊤ :=
    lt_of_le_of_lt hGnorm (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF'fin)
  have hGH : InHr c r G :=
    { periodic := Filter.Eventually.of_forall fun x => hGper x.1 x.2
      meas := hGs.aestronglyMeasurable
      finite := hGfin }
  have hGw : WeakSolenoidal G := by
    apply h5 c r G hc hr1 hGs hGper hGH
    filter_upwards [hGjoint, hCyl] with s hs hcs
    intro Φ hΦ
    have hcyl := (hPb _ hcs).1.2.1 Φ hΦ
    have hae : (fun z => G (s, z) 0 * (fderiv ℝ Φ z (1, 0) : ℂ) +
          G (s, z) 1 * (fderiv ℝ Φ z (0, 1) : ℂ)) =ᵐ[UnforcedLeray.Cyl.avgμ c]
        (fun z => P (fun w => F' (s, w)) z 0 * (fderiv ℝ Φ z (1, 0) : ℂ) +
          P (fun w => F' (s, w)) z 1 * (fderiv ℝ Φ z (0, 1) : ℂ)) :=
      hs.mono fun z hz => by
        have hz' : G (s, z) = P (fun w => F' (s, w)) z := hz
        dsimp only
        rw [hz']
    exact ⟨hcyl.1.congr hae.symm, by rw [integral_congr_ae hae]; exact hcyl.2⟩
  have hPp : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, CylSolTest c Ψ →
      Integrable (fun z => ∑ i : Fin 2, (F' (s, z) i - G (s, z) i) * (Ψ z i : ℂ))
          (UnforcedLeray.Cyl.avgμ c) ∧
        ∫ z, ∑ i : Fin 2, (F' (s, z) i - G (s, z) i) * (Ψ z i : ℂ)
          ∂(UnforcedLeray.Cyl.avgμ c) = 0 := by
    filter_upwards [hGjoint, hCyl] with s hs hcs
    intro Ψ hΨ
    have hcyl := (hPb _ hcs).1.2.2 Ψ hΨ
    have hae : (fun z => ∑ i : Fin 2, (F' (s, z) i - G (s, z) i) * (Ψ z i : ℂ)) =ᵐ[UnforcedLeray.Cyl.avgμ c]
        (fun z => ∑ i : Fin 2, (F' (s, z) i - P (fun w => F' (s, w)) z i) * (Ψ z i : ℂ)) :=
      hs.mono fun z hz => by
        have hz' : G (s, z) = P (fun w => F' (s, w)) z := hz
        dsimp only
        rw [hz']
    exact ⟨hcyl.1.congr hae.symm, by rw [integral_congr_ae hae]; exact hcyl.2⟩
  have hGp : PerpPlanarSol (F - G) :=
    h6 c r F F' G hc hr1 hF hF's hF'p hFa' hGH hGs hGper hPp
  refine ⟨G, hGH, ?_, hGw, hGp⟩
  rw [← hF'eq]
  exact hGnorm

end UnforcedLeray.Short.IIb.LerayLiftSub
