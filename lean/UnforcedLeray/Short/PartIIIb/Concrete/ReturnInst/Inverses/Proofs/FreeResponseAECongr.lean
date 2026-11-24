import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Leaves

/-!
# Free responses are a.e. classes (source 1341-1347, 1351-1362)

Proof of `FreeResponseAECongr`.  Every clause of `IIb.IsFreeResponse` sees the field `w` only
through the iterated integrals of `pairF` and `phaseLpNorm` over the phase cell, and the phase
translation `(τ, y) ↦ (τ + P, y)` preserves Lebesgue measure.  So an a.e. modification `w'` of
`w` keeps every clause, with the same auxiliary fields `a`, `b`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The period integral `phaseInt` only sees its integrand up to a.e. equality. -/
theorem frc_phaseInt_congr {P : ℝ} {f g : ℝ × Space → ℂ} (h : f =ᵐ[volume] g) :
    phaseInt P f = phaseInt P g := by
  have h' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), f x = g x := by
    rw [← Measure.volume_eq_prod]
    exact h
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure Space), f (t, y) = g (t, y) :=
    Measure.ae_ae_of_ae_prod h'
  unfold phaseInt
  congr 1
  refine integral_congr_ae ?_
  refine ae_restrict_of_ae ?_
  filter_upwards [hae] with t ht
  exact integral_congr_ae ht

/-- The phase translation `(τ, y) ↦ (τ + P, y)` preserves Lebesgue measure on `ℝ × ℝ³`. -/
theorem frc_measurePreserving_shift (P : ℝ) :
    MeasurePreserving (fun x : ℝ × Space => (x.1 + P, x.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right (volume : Measure ℝ) P).prod
    (MeasurePreserving.id (volume : Measure Space))

theorem freeResponseAECongr : FreeResponseAECongr := by
  intro ν μ r P f w w' h hae
  -- pairings with any test are unchanged by an a.e. modification
  have hpair : ∀ G : ℝ × Space → CVec3, pairF P G w' = pairF P G w := by
    intro G
    unfold pairF
    apply frc_phaseInt_congr
    filter_upwards [hae] with x hx
    simp only [hx]
  -- the phase-normalized norm is unchanged
  have hl : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y, ‖w' (t, y)‖ₑ ^ r
      = ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y, ‖w (t, y)‖ₑ ^ r := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    have h' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), w' x = w x := by
      rw [← Measure.volume_eq_prod]
      exact hae
    have hae2 : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure Space),
        w' (t, y) = w (t, y) := Measure.ae_ae_of_ae_prod h'
    filter_upwards [hae2] with t ht
    exact lintegral_congr_ae (ht.mono fun y hy => by simp only [hy])
  have hnorm : UnforcedLeray.Short.IIb.phaseLpNorm P r w'
      = UnforcedLeray.Short.IIb.phaseLpNorm P r w := by
    unfold UnforcedLeray.Short.IIb.phaseLpNorm
    rw [hl]
  -- the periodicity of `w` transported by the shift
  have hae_T : ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      w' (x.1 + P, x.2) = w (x.1 + P, x.2) :=
    (frc_measurePreserving_shift P).quasiMeasurePreserving.ae
      (p := fun y => w' y = w y) hae
  refine ⟨⟨?_, h.mem_w.meas.congr hae.symm, ?_⟩, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hae_T, h.mem_w.periodic, hae] with x h1 h2 h3
    rw [h1, h2, h3]
  · rw [hnorm]
    exact h.mem_w.finite
  · obtain ⟨a, ha, hPt⟩ := h.lapl
    refine ⟨a, ha, ?_⟩
    unfold UnforcedLeray.Short.IIb.HasPtwOp at hPt ⊢
    intro Φ hΦ
    rw [hpair]
    exact hPt Φ hΦ
  · obtain ⟨b, hb, hPt⟩ := h.drift
    refine ⟨b, hb, ?_⟩
    unfold UnforcedLeray.Short.IIb.HasPtwOp at hPt ⊢
    intro Φ hΦ
    rw [hpair]
    exact hPt Φ hΦ
  · intro φ hφ
    rw [hpair]
    exact h.solenoidal φ hφ
  · intro Φ hΦ
    rw [hpair]
    exact h.equation Φ hΦ

end UnforcedLeray.Short.PartIIIb.Concrete
