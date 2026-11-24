import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4.HalfPlane

/-!
# `SpacePolar` (`PartIII-b:C/near/masked/14/2/3/1/4`; source 3996-4011)

Polar coordinates in the first two coordinates of `ℝ³` for axisymmetric integrands.
Splitting of `Space` into the plane and the axis, Tonelli, then `lintegral_comp_polarCoord_symm`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- Measurability of the vector `(a x, b x, c x) ∈ ℝ³` as a point of `Space`. -/
lemma measurable_toLp3 {α : Type*} [MeasurableSpace α] (a b c : α → ℝ) (ha : Measurable a)
    (hb : Measurable b) (hc : Measurable c) :
    Measurable (fun x => (WithLp.toLp 2 ![a x, b x, c x] : UnforcedLeray.Space)) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  exacts [ha, hb, hc]

/-- Splitting `Space = ℝ³` into the plane `(y₀,y₁)` and the axis `y₂`, with the axis outside. -/
lemma spacePolar_split (H : UnforcedLeray.Space → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ y : UnforcedLeray.Space, H y =
      ∫⁻ t : ℝ, ∫⁻ p : ℝ × ℝ, H (WithLp.toLp 2 ![p.1, p.2, t]) := by
  have hA : MeasurePreserving (fun z : UnforcedLeray.Space => (z 2, (z 0, z 1))) volume volume := by
    have h : (fun z : UnforcedLeray.Space => (z 2, (z 0, z 1)))
        = (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
          ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2) ∘ WithLp.ofLp := by
      funext z
      rfl
    rw [h]
    have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
    have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
    have h3 := PiLp.volume_preserving_ofLp (Fin 3)
    exact (h1.comp h2).comp h3
  have hψmp : MeasurePreserving (fun z : UnforcedLeray.Space => ((z 0, z 1), z 2)) volume volume :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))).comp hA
  have hφψ : ∀ z : UnforcedLeray.Space,
      H z = H (WithLp.toLp 2 ![((z 0, z 1), z 2).1.1, ((z 0, z 1), z 2).1.2, ((z 0, z 1), z 2).2]) := by
    intro z
    congr 1
    ext i
    fin_cases i <;> simp
  have hφm : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      H (WithLp.toLp 2 ![q.1.1, q.1.2, q.2])) :=
    hH.comp (measurable_toLp3 (fun q : (ℝ × ℝ) × ℝ => q.1.1) (fun q => q.1.2) (fun q => q.2)
      (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd)
  calc ∫⁻ y : UnforcedLeray.Space, H y
      = ∫⁻ z : UnforcedLeray.Space,
          H (WithLp.toLp 2 ![((z 0, z 1), z 2).1.1, ((z 0, z 1), z 2).1.2, ((z 0, z 1), z 2).2]) :=
        lintegral_congr fun z => hφψ z
    _ = ∫⁻ q : (ℝ × ℝ) × ℝ, H (WithLp.toLp 2 ![q.1.1, q.1.2, q.2]) :=
        hψmp.lintegral_comp hφm
    _ = ∫⁻ t : ℝ, ∫⁻ p : ℝ × ℝ, H (WithLp.toLp 2 ![p.1, p.2, t]) := by
        rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ]
        exact lintegral_prod_symm _ hφm.aemeasurable

/-- The planar polar formula at fixed height `t`. -/
lemma spacePolar_plane (H : UnforcedLeray.Space → ℝ≥0∞) (hH : Measurable H)
    (hax : ∀ y y' : UnforcedLeray.Space, y 0 ^ 2 + y 1 ^ 2 = y' 0 ^ 2 + y' 1 ^ 2 → y 2 = y' 2 →
      H y = H y') (t : ℝ) :
    ∫⁻ p : ℝ × ℝ, H (WithLp.toLp 2 ![p.1, p.2, t]) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * H (WithLp.toLp 2 ![ρ, 0, t]) := by
  have hKm : Measurable (fun p : ℝ × ℝ => H (WithLp.toLp 2 ![p.1, p.2, t])) :=
    hH.comp (measurable_toLp3 (fun p : ℝ × ℝ => p.1) (fun p => p.2) (fun _ : ℝ × ℝ => t)
      measurable_fst measurable_snd measurable_const)
  have hsymm : Measurable (polarCoord.symm) := continuous_polarCoord_symm.measurable
  have hm : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 *
      H (WithLp.toLp 2 ![(polarCoord.symm q).1, (polarCoord.symm q).2, t])) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (hKm.comp hsymm)
  have hs : ∀ ρ θ : ℝ, polarCoord.symm (ρ, θ) = (ρ * Real.cos θ, ρ * Real.sin θ) :=
    fun _ _ => rfl
  have e := lintegral_comp_polarCoord_symm
    (fun p : ℝ × ℝ => H (WithLp.toLp 2 ![p.1, p.2, t]))
  simp only [smul_eq_mul] at e
  rw [← e]
  rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl]
  rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hm.aemeasurable]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ρ => ?_
  have hθ : ∀ θ : ℝ, H (WithLp.toLp 2 ![ρ * Real.cos θ, ρ * Real.sin θ, t]) =
      H (WithLp.toLp 2 ![ρ, 0, t]) := by
    intro θ
    apply hax
    · simp
      linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq θ
    · simp
  simp only [hs]
  simp only [hθ]
  rw [setLIntegral_const, Real.volume_Ioo, mul_comm, show Real.pi - -Real.pi = 2 * Real.pi by ring]

/-- **Polar coordinates in the first two coordinates of `ℝ³`** (source 3996-4011). -/
theorem spacePolar : SpacePolar := by
  intro H hH hax
  rw [spacePolar_split H hH]
  simp_rw [spacePolar_plane H hH hax]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_lintegral_swap]
  exact (ENNReal.measurable_ofReal.comp measurable_snd |>.mul
    (hH.comp (measurable_toLp3 (fun q : ℝ × ℝ => q.2) (fun _ => (0 : ℝ)) (fun q => q.1)
      measurable_snd measurable_const measurable_fst))).aemeasurable

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
