import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2

/-!
# Decomposition of `KerIntKdDeriv` (`PartIII-b:C/rep/2/6/3/2/1`)

Source `the November 2 reference manuscript`
lines 3603-3626, 3800-3807, 4171-4200.  Substituting `s = t - h` writes
`kerInt T Φ t y i` as `-∫_{ℝ×Space} extInt T Φ t y i`, where `extInt` extends the kernel by `0`
to `s ≥ t` (continuity of `Kd` at `h = 0` by `kd_zero`).  The derivative under the integral is
`hasDerivAt_integral_of_dominated_loc_of_lip` on `volume.prod volume`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The shifted, zero-extended integrand (`s = t - h`; zero for `s ≥ t`), a function of
`p = (s, z)`. -/
def extInt (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (t : ℝ) (y : Space) (i : Fin 3)
    (p : ℝ × Space) : ℂ :=
  (Iio t).indicator (fun s : ℝ => ∑ j : Fin 3, ∑ k : Fin 3,
    Φ (t - s) y p.2 i j k * ((T s p.2 j k : ℝ) : ℂ)) p.1

/-- (E) Shift identity (change of variables `s = t - h`, then Fubini): when the shifted
integrand is integrable on `ℝ × Space`, `kerInt T Φ t y i = -∫ extInt`. -/
def KerIntShift : Prop :=
  ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (t : ℝ) (y : Space) (i : Fin 3),
    Integrable (extInt T Φ t y i) (volume.prod volume) →
      kerInt T Φ t y i = -∫ p, extInt T Φ t y i p ∂(volume.prod volume)

/-- (D) Pointwise `t`-derivative of the shifted integrand away from the null set `s = t`
(`Kd` is `C¹` in `h` for `h > 0` by the heat equation; `Kd` is extended by `0` for `h ≤ 0`). -/
def ExtIntPointDeriv : Prop :=
  ∀ (ν μ : ℝ), 0 < ν → ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space)
    (i : Fin 3) (p : ℝ × Space), p.1 ≠ τ →
      HasDerivAt (fun t => extInt T (Kd ν μ) t y i p) (extInt T (kdDh ν μ) τ y i p) τ

/-- (C) Measurability of the shifted integrands on `ℝ × Space` (joint measurability of `Kd`,
`kdDh` in `(h, z)` and of `T`). -/
def ExtIntMeasurable : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (y : Space) (i : Fin 3),
      (∀ t : ℝ, AEStronglyMeasurable (extInt T (Kd ν μ) t y i) (volume.prod volume)) ∧
      (∀ t : ℝ, AEStronglyMeasurable (extInt T (kdDh ν μ) t y i) (volume.prod volume))

/-- (B) Integrability of the shifted `Kd` integrand off the old disk (`SepKernelBounds`,
`|y - e^{-h/2}z| ≥ ϱ y - rOut` on the support, `SepMoment`, periodicity; cf. `GkerIntegrable`). -/
def ExtIntKdIntegrable : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (y : Space), rOut < ϱ y → ∀ (i : Fin 3) (t : ℝ),
      Integrable (extInt T (Kd ν μ) t y i) (volume.prod volume)

/-- (A) Local Lipschitz envelope in `t` (source 3603-3626, 3800-3807): `dh G_m = L G_m -
(m-1/2) G_m`; with the kernel bounds `SepKernelBounds` for `D²∇K`, the gap, and `T ∈ Y₂`, the
map `t ↦ extInt T (Kd) t y i p` is Lipschitz on a ball around `τ` with an integrable constant. -/
def ExtIntKdLipschitz : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ i : Fin 3, ∃ ε : ℝ, 0 < ε ∧
      ∃ g : ℝ × Space → ℝ, Integrable g (volume.prod volume) ∧
        ∀ᵐ p ∂(volume.prod volume),
          LipschitzOnWith (Real.nnabs (g p)) (fun t => extInt T (Kd ν μ) t y i p)
            (Metric.ball τ ε)

theorem kerIntKdDeriv_of (hE : KerIntShift) (hD : ExtIntPointDeriv) (hC : ExtIntMeasurable)
    (hB : ExtIntKdIntegrable) (hA : ExtIntKdLipschitz) : KerIntKdDeriv := by
  intro ν μ rOut P T hS τ y hy i
  obtain ⟨ε, hε, g, hg, hlip⟩ := hA ν μ rOut P T hS τ y hy i
  have hν : 0 < ν := hS.1
  have hae : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × Space)), p.1 ≠ τ := by
    have h1 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ τ := by
      simpa [ae_iff] using (measure_singleton (μ := (volume : Measure ℝ)) τ)
    exact Measure.quasiMeasurePreserving_fst.ae h1
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume.prod volume) (F := fun t p => extInt T (Kd ν μ) t y i p)
    (F' := extInt T (kdDh ν μ) τ y i) (bound := g) (s := Metric.ball τ ε)
    (Metric.ball_mem_nhds τ hε)
    (Filter.Eventually.of_forall fun t => (hC ν μ rOut P T hS y i).1 t) (hB ν μ rOut P T hS y hy i τ)
    ((hC ν μ rOut P T hS y i).2 τ) hlip hg
    (hae.mono fun p hp => hD ν μ hν T τ y i p hp)
  have hfun : (fun t => kerInt T (Kd ν μ) t y i) =
      fun t => -∫ p, extInt T (Kd ν μ) t y i p ∂(volume.prod volume) := by
    funext t; exact hE T (Kd ν μ) t y i (hB ν μ rOut P T hS y hy i t)
  rw [hfun, hE T (kdDh ν μ) τ y i key.1]
  exact key.2.neg

end UnforcedLeray.Short.PartIIIb.Concrete
