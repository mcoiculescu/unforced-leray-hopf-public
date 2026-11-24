import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf7

/-!
# Lifts of body forces: `Y_2` membership and nondegeneracy of the phase pairings

Source of record: `the November 2 reference manuscript` (73 pages), lines
2666-2689 (the cylinder chart `(s, q, η) = (R²/ρ², R log(ρ/R) + Rτ/2, Rz/ρ)`, the space
`H = L²(s^{-3/2} dς)` and the lift identity `‖𝒩_v b‖²_{Y_2} = πR²‖b‖²_H`) and 5001-5008
(Lemma `ret:physical-affine`: the physical identity, read against all phase tests, determines
the body force `𝔯_A`).

With `R = ε⁻¹` and `P = 2εc = 2c/R`:

* `sp_isInYr` : the lift `velPhys R c f = 𝒩_v f` of `f ∈ SrcG c` lies in `Y_2`.  It is
  `P`-periodic (`Axi.Nv_dss`: `τ ↦ τ + P` shifts `q` by a full cell `c`, and `𝒩_v` uses the
  `q`-periodic extension `Axi.perExt`), and `P⁻¹∫₀ᴾ∫|𝒩_v f|² dy dτ = πR² ∫|f|² s^{-3/2} dς`
  (`sp_lintegral_velPhys`, from `Axi.lintegral_Nv_rpow`; source 2683-2689) is finite because
  `SrcG c = L²(π s^{-3/2} dς)`.
* `sp_nondeg` : phase tests separate points of `Y_2` (`IIb.phaseFundamental`, the fundamental
  lemma on the phase circle times `ℝ³`), so equal pairings give `𝒩_v f = 𝒩_v g` a.e.; the norm
  identity for `f - g` (`Axi.eLpNorm_liftFun`, `R⁻¹‖𝒩_v b‖_{Y_2} = √π‖b‖_H`) then gives `f = g`
  a.e. for `s^{-3/2} dς`, hence `f = g` in `SrcG c`.  This is the body of
  `ReturnInst.SrcPairingNondeg` (proved in `Concrete/ReturnInst/SrcPairing.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (pairF)

namespace SrcPairing

/-- The complexification `realC : ℝ³ → ℂ³` is isometric (enorm form). -/
theorem sp_enorm_realC (x : Space) : ‖B0412.realC x‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  congr 1
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [B0412.realC_apply, Complex.norm_real]

/-- The complexification `realC : ℝ³ → ℂ³` is injective. -/
theorem sp_realC_injective : Function.Injective B0412.realC := by
  intro x y h
  ext i
  have hi := congrArg (fun v : CVec3 => v i) h
  simp only [B0412.realC_apply] at hi
  exact_mod_cast hi

theorem sp_realC_continuous : Continuous (B0412.realC : Space → CVec3) := by
  unfold B0412.realC
  fun_prop

theorem sp_measurable_velPhys (R c : ℝ) {b : Chart → Merid} (hb : Measurable b) :
    Measurable (velPhys R c b) :=
  sp_realC_continuous.measurable.comp (measurable_Nv R (measurable_perExt c hb))

/-- `SrcG c ⊆ H = L²(s^{-3/2} dς)`: `srcMeasure c = π · s^{-3/2} dς` (source 2676-2678,
2683-2689). -/
theorem sp_memLp_ageμ {c : ℝ} (f : SrcG c) : MemLp (f : Chart → Merid) 2 (ageμ c (-3 / 2)) := by
  have hπ : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.2 Real.pi_pos).ne'
  have e : (ENNReal.ofReal Real.pi)⁻¹ • srcMeasure c = ageμ c (-3 / 2) := by
    rw [srcMeasure, smul_smul, ENNReal.inv_mul_cancel hπ ENNReal.ofReal_ne_top, one_smul]
  exact MemLp.of_measure_le_smul (ENNReal.inv_ne_top.2 hπ) e.ge (Lp.memLp f)

theorem sp_lintegral_lt_top {c : ℝ} (f : SrcG c) :
    ∫⁻ p, ‖(f : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) < ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero
    ENNReal.ofNat_ne_top (sp_memLp_ageμ f).eLpNorm_lt_top
  have e : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rwa [e] at h

/-- **The lift identity** (source 2683-2689, `Axi.lintegral_Nv_rpow`): at `R = ε⁻¹`, `P = 2εc`,
`P⁻¹∫₀ᴾ∫|𝒩_v b|² dy dτ = πR² ∫|b|² s^{-3/2} dς`. -/
theorem sp_lintegral_velPhys {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {b : Chart → Merid}
    (hb : Measurable b) :
    ENNReal.ofReal (2 * ε * c)⁻¹ *
        ∫⁻ t in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y : Space, ‖velPhys ε⁻¹ c b (t, y)‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * ∫⁻ p, ‖b p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) := by
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hP0 : 0 < 2 * ε * c := by positivity
  have h := lintegral_Nv_rpow hR hc hP (by norm_num : (0 : ℝ) < 2) (measurable_perExt c hb)
    (perExt_periodic hc.ne' b)
  have e1 : ∀ (t : ℝ) (y : Space),
      ‖velPhys ε⁻¹ c b (t, y)‖ₑ = ‖Nv ε⁻¹ (perExt c b) t y‖ₑ := fun t y =>
    sp_enorm_realC _
  simp_rw [e1]
  rw [ENNReal.ofReal_inv_of_pos hP0, h, show (2 : ℝ) / 2 - 5 / 2 = -3 / 2 by norm_num]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [perExt_ae_eq hc (-3 / 2) b] with p hp
  rw [hp]

/-- The phase `L²` norm of the lift of a body force is finite. -/
theorem sp_phaseLpNorm_lt_top {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (f : SrcG c) :
    UnforcedLeray.Short.IIb.phaseLpNorm (2 * ε * c) 2 (velPhys ε⁻¹ c (f : Chart → Merid)) < ⊤ := by
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  rw [sp_lintegral_velPhys hc hε (Lp.stronglyMeasurable f).measurable]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (sp_lintegral_lt_top f).ne)

/-- Lifts of body forces lie in `Y_2` (period `P = 2εc`; source 2666-2689). -/
theorem sp_isInYr {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (f : SrcG c) :
    UnforcedLeray.Short.IIb.IsInYr (2 * ε * c) 2 (velPhys ε⁻¹ c (f : Chart → Merid)) := by
  have hR0 : ε⁻¹ ≠ 0 := (inv_pos.2 hε).ne'
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  refine ⟨Filter.Eventually.of_forall fun x => ?_,
    (sp_measurable_velPhys _ _ (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable,
    sp_phaseLpNorm_lt_top hc hε f⟩
  have hper := congrFun (Nv_dss hR0 hP (perExt_periodic hc.ne' (f : Chart → Merid)) x.1) x.2
  show B0412.realC (Nv ε⁻¹ (perExt c (f : Chart → Merid)) (x.1 + 2 * ε * c) x.2) =
    B0412.realC (Nv ε⁻¹ (perExt c (f : Chart → Merid)) x.1 x.2)
  rw [hper]

/-- The period-averaged measure `P⁻¹ dτ|_{(0,P]} ⊗ dy` is absolutely continuous for Lebesgue
measure on `ℝ × ℝ³`. -/
theorem sp_phaseμ_ac (P : ℝ) : phaseμ P ≪ (volume : Measure (ℝ × Space)) := by
  have h1 : (ENNReal.ofReal P)⁻¹ • (volume : Measure ℝ).restrict (Ioc (0 : ℝ) P) ≪
      (volume : Measure ℝ) :=
    Measure.smul_absolutelyContinuous.trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have h2 := h1.prod (Measure.AbsolutelyContinuous.refl (volume : Measure Space))
  rw [Measure.volume_eq_prod]
  exact h2

/-- **Nondegeneracy of the phase pairings on body forces** (source 2666-2689, 5001-5008): body
forces `f, g ∈ SrcG c` whose lifts `𝒩_v f, 𝒩_v g` have the same pairing with every phase test
are equal.  The lifts lie in `Y_2` (`sp_isInYr`), phase tests separate points of `Y_2`
(`IIb.phaseFundamental`), and the lift identity for `f - g` gives `‖f - g‖_H = 0`. -/
theorem sp_nondeg (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (f g : SrcG c)
    (hpair : ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (f : Chart → Merid)) =
        pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (g : Chart → Merid))) : f = g := by
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hP0 : 0 < 2 * ε * c := by positivity
  have hfm : Measurable (f : Chart → Merid) := (Lp.stronglyMeasurable f).measurable
  have hgm : Measurable (g : Chart → Merid) := (Lp.stronglyMeasurable g).measurable
  -- (1) phase tests separate points of `Y_2`: the lifts agree a.e. on `ℝ × ℝ³`
  have hae : velPhys ε⁻¹ c (f : Chart → Merid) =ᵐ[volume] velPhys ε⁻¹ c (g : Chart → Merid) :=
    UnforcedLeray.Short.IIb.phaseFundamental (2 * ε * c) 2 _ _ hP0 (by norm_num)
      (sp_isInYr hc hε f) (sp_isInYr hc hε g) hpair
  -- (2) the normalized lifts `(√π R)⁻¹ 𝒩_v` agree a.e. for the phase measure
  have hlift : liftFun ε⁻¹ c (f : Chart → Merid) - liftFun ε⁻¹ c (g : Chart → Merid)
      =ᵐ[phaseμ (2 * ε * c)] 0 := by
    filter_upwards [(sp_phaseμ_ac (2 * ε * c)).ae_le hae] with x hx
    have h1 : Nv ε⁻¹ (perExt c (f : Chart → Merid)) x.1 x.2 =
        Nv ε⁻¹ (perExt c (g : Chart → Merid)) x.1 x.2 :=
      sp_realC_injective hx
    simp only [Pi.sub_apply, Pi.zero_apply, liftFun, h1, sub_self]
  -- (3) the lift identity for `f - g` (2683-2689): `‖f - g‖_H = 0`
  have hnorm : eLpNorm ((f : Chart → Merid) - (g : Chart → Merid)) 2 (ageμ c (-3 / 2)) = 0 := by
    rw [← eLpNorm_liftFun hR hc hP (hfm.sub hgm), liftFun_sub, eLpNorm_congr_ae hlift,
      eLpNorm_zero]
  have hz := (eLpNorm_eq_zero_iff (hfm.sub hgm).aestronglyMeasurable two_ne_zero).1 hnorm
  -- (4) hence `f = g` in `SrcG c = L²(π s^{-3/2} dς)`
  have hπ : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.2 Real.pi_pos).ne'
  refine Lp.ext ?_
  change ∀ᵐ p ∂(ENNReal.ofReal Real.pi • ageμ c (-3 / 2)),
    (f : Chart → Merid) p = (g : Chart → Merid) p
  rw [Measure.ae_ennreal_smul_measure_iff hπ]
  filter_upwards [hz] with p hp
  simp only [Pi.sub_apply, Pi.zero_apply] at hp
  exact sub_eq_zero.1 hp

end SrcPairing

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.SrcPairing.sp_nondeg
