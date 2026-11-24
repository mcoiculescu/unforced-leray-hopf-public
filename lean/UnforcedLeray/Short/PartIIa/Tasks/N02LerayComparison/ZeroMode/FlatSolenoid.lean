import UnforcedLeray.Short.PartIIa.Sub.N02_3
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CellFubiniEta
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IntegralMeasureHCell
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IntegralDerivPeriodic
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.PartialDerivSlice
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.InnerCgradStream

/-!
# Part II-a, task `PartII-a:N02/3`, target `zeroFlatSolenoid` (`ZeroFlatSolenoid`)

Source of record: `the November 2 reference manuscript`, lines 1728-1729 ("the radial
component is solenoidal"). Specification: `ZeroFlatSolenoid` in `Short/PartII-a/Sub/N02_3.lean`.

Proof outline. For a `q`-independent smooth meridional test `f`, the field `(f_r, 0)` is continuous and
supported in the band, hence in `L²(measureH c)` (`NearGradMemberAux.memLp_of_band`). Its class is
orthogonal to every generator `toLp (cgrad 0 Φ)` of `solenoidalHC 0 c`. The pairing becomes the cell
integral `∫_cell s^{-3/2} (∂_q Φ) f_r`, which vanishes by `q`-integration by parts
(`ZeroFlatSolenoidAux.ibpQ_cell`: Fubini on the cell, periodicity in `q`, and `f_r` independent of `q`).

The `IbpQCell` leaf is not yet present as a compiled file, so its proof is included here as a helper.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace ZeroFlatSolenoidAux

/-- The weighted `q`-derivative integrand `s^{-3/2} ∂_q F` on the cell. -/
def gZ (F : Profile → ℂ) (p : Profile) : ℂ :=
  ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ F p

/-- `q`-integration by parts with the weight on the cell (the content of `IbpQCell`). -/
theorem ibpQ_cell (c : ℝ) (F : Profile → ℂ) (hF : IsCTest c F) :
    ∫ p in cell c, gZ F p = 0 := by
  by_cases hG : IntegrableOn (gZ F) (cell c)
  · have hvol : (volume : Measure Profile) =
        (volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
    have hcell : cell c = Ioi (0 : ℝ) ×ˢ (Ioc (0 : ℝ) c ×ˢ (univ : Set ℝ)) := rfl
    have hG2 : Integrable (gZ F)
        (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
          (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
            (Ioc (0 : ℝ) c ×ˢ (univ : Set ℝ)))) := by
      rw [Measure.prod_restrict]
      rw [hvol, hcell] at hG
      exact hG
    -- for fixed `(s, η)`, the `q`-integral of `s^{-3/2} ∂_q F` vanishes by periodicity
    have hline : ∀ s η : ℝ, ∫ q in Ioc (0 : ℝ) c, gZ F (s, q, η) = 0 := by
      intro s η
      have hline_map : ContDiff ℝ ∞ (fun t : ℝ => ((s, t, η) : Profile)) :=
        contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
      have hsm : ContDiff ℝ ∞ (fun t : ℝ => F (s, t, η)) := hF.smooth.comp hline_map
      have hper : ∀ t : ℝ, (fun t : ℝ => F (s, t, η)) (t + c) = (fun t : ℝ => F (s, t, η)) t :=
        fun t => hF.periodic (s, t, η)
      have hd : ∀ q : ℝ, gZ F (s, q, η) =
          ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * deriv (fun t : ℝ => F (s, t, η)) q := by
        intro q
        unfold gZ
        rw [(partialDerivSlice F hF.smooth s q η).2.1]
      have hint : ∫ q in Ioc (0 : ℝ) c, gZ F (s, q, η) =
          ∫ q in Ioc (0 : ℝ) c, ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
            deriv (fun t : ℝ => F (s, t, η)) q :=
        integral_congr_ae (Filter.Eventually.of_forall hd)
      rw [hint, integral_const_mul, integralDerivPeriodic c _ hsm hper, mul_zero]
    have hae : (fun s : ℝ => ∫ q in Ioc (0 : ℝ) c, ∫ η : ℝ, gZ F (s, q, η)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun _ => (0 : ℂ) := by
      filter_upwards [hG2.prod_right_ae] with s hs
      show (∫ q in Ioc (0 : ℝ) c, ∫ η : ℝ, gZ F (s, q, η)) = 0
      have hs2 : Integrable (fun y : ℝ × ℝ => gZ F (s, y))
          ((volume.restrict (Ioc (0 : ℝ) c)).prod (volume.restrict (univ : Set ℝ))) := by
        rw [Measure.prod_restrict]
        exact hs
      have hswap := integral_integral_swap (μ := volume.restrict (Ioc (0 : ℝ) c))
        (ν := volume.restrict (univ : Set ℝ)) (f := fun (q η : ℝ) => gZ F (s, (q, η))) hs2
      rw [Measure.restrict_univ] at hswap
      rw [hswap]
      simp only [hline, integral_zero]
    rw [cellFubiniEta c (gZ F) hG, integral_congr_ae hae, integral_zero]
  · exact integral_undef hG

/-- The scalar component `p ↦ f p 0` of a meridional test is a complex band test. -/
theorem zeroComp_isCTest {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) :
    IsCTest c (fun p => f p 0) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
  refine ⟨?_, ?_, s0, s1, L, hs0, ?_⟩
  · exact ((EuclideanSpace.proj (0 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp
      hf.smooth
  · intro p
    exact congrArg (fun v : MeridC => v 0) (hf.periodic p)
  · intro p hp
    exact hb p (fun h => hp (by simp [h]))

/-- The product `Φ · f_r` of a real profile test and the scalar component is a complex band test. -/
theorem psi_isCTest {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) (Φ : ProfileTest c) :
    IsCTest c (fun p => ((Φ.1 p : ℝ) : ℂ) * f p 0) := by
  have hF0 := zeroComp_isCTest hf
  have hΦC : ContDiff ℝ ∞ (fun x => (Φ.1 x : ℂ)) := Complex.ofRealCLM.contDiff.comp Φ.2.smooth
  refine ⟨hΦC.mul hF0.smooth, ?_, ?_⟩
  · intro p
    show ((Φ.1 (p.1, p.2.1 + c, p.2.2) : ℝ) : ℂ) * f (p.1, p.2.1 + c, p.2.2) 0
      = ((Φ.1 p : ℝ) : ℂ) * f p 0
    rw [Φ.2.periodic p, congrArg (fun v : MeridC => v 0) (hf.periodic p)]
  · obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
    refine ⟨s0, s1, L, hs0, fun p hp => hb p (fun h => hp ?_)⟩
    simp [h]

/-- The `q`-derivative of `Φ · f_r` is `(∂_q Φ) · f_r`, since `f_r` does not depend on `q`. -/
theorem pdQ_psi {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) (hQ : QInvariant c f)
    (Φ : ProfileTest c) (p : Profile) :
    pdQ (fun p => ((Φ.1 p : ℝ) : ℂ) * f p 0) p = ((Axi.dQ Φ.1 p : ℝ) : ℂ) * f p 0 := by
  obtain ⟨s, q, η⟩ := p
  have hΦC : ContDiff ℝ ∞ (fun x => (Φ.1 x : ℂ)) := Complex.ofRealCLM.contDiff.comp Φ.2.smooth
  have hΨs : ContDiff ℝ ∞ (fun p => ((Φ.1 p : ℝ) : ℂ) * f p 0) :=
    hΦC.mul (zeroComp_isCTest hf).smooth
  have hq : pdQ (fun x => (Φ.1 x : ℂ)) (s, q, η) = ((Axi.dQ Φ.1 (s, q, η) : ℝ) : ℂ) :=
    icsFderivOfReal Φ.2.smooth _ _
  have hsl := (partialDerivSlice (fun p => ((Φ.1 p : ℝ) : ℂ) * f p 0) hΨs s q η).2.1
  have hΦsl := (partialDerivSlice (fun x => (Φ.1 x : ℂ)) hΦC s q η).2.1
  have hfun : (fun t : ℝ => ((Φ.1 (s, t, η) : ℝ) : ℂ) * f (s, t, η) 0) =
      fun t : ℝ => ((Φ.1 (s, t, η) : ℝ) : ℂ) * f (s, q, η) 0 := by
    funext t
    rw [hQ s t q η]
  rw [hsl, hfun, deriv_mul_const_field, ← hΦsl, hq]

/-- The pairing of `toLp (cgrad 0 Φ)` with `toLp (f_r, 0)` vanishes. -/
theorem pairing_zero {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) (hQ : QInvariant c f)
    (hm : MemLp (fun p : Profile => (!₂[f p 0, 0] : MeridC)) 2 (measureH c))
    (Φ : ProfileTest c) (hΦ : MemLp (cgrad 0 Φ.1) 2 (measureH c)) :
    ⟪hΦ.toLp (cgrad 0 Φ.1), hm.toLp _⟫_ℂ = 0 := by
  have hpt : ∀ p : Profile, ⟪cgrad 0 Φ.1 p, (!₂[f p 0, 0] : MeridC)⟫_ℂ =
      ((Axi.dQ Φ.1 p : ℝ) : ℂ) * f p 0 := by
    intro p
    simp [cgrad, Deps, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hint : ∫ a, ⟪hΦ.toLp (cgrad 0 Φ.1) a, hm.toLp _ a⟫_ℂ ∂(measureH c) =
      ∫ a, ((Axi.dQ Φ.1 a : ℝ) : ℂ) * f a 0 ∂(measureH c) := by
    apply integral_congr_ae
    filter_upwards [hΦ.coeFn_toLp, hm.coeFn_toLp] with a h1 h2
    simp only [h1, h2, hpt]
  rw [L2.inner_def, hint,
    integralMeasureHCell c (fun a => ((Axi.dQ Φ.1 a : ℝ) : ℂ) * f a 0)]
  have hz := ibpQ_cell c _ (psi_isCTest hf Φ)
  simp only [gZ, pdQ_psi hf hQ Φ] at hz
  exact hz

end ZeroFlatSolenoidAux

/-- **L3a (the radial component is flat-solenoidal)**, target `zeroFlatSolenoid` for the Prop
`ZeroFlatSolenoid` (`Sub/N02_3.lean`, tex lines 1728-1729). -/
theorem zeroFlatSolenoid : UnforcedLeray.Short.PartIIa.ZeroFlatSolenoid := by
  intro c f _hc hf hQ
  obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
  have hF0 : IsCTest c (fun p : Profile => f p 0) := ZeroFlatSolenoidAux.zeroComp_isCTest hf
  have hcont : Continuous (fun p : Profile => (!₂[f p 0, 0] : MeridC)) :=
    NearGradMemberAux.continuous_mk hF0.smooth.continuous continuous_const
  have hz : ∀ p : Profile, ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
      (fun p : Profile => (!₂[f p 0, 0] : MeridC)) p = 0 := by
    intro p hp
    have h0 : f p 0 = 0 := by
      by_contra h
      exact hp (hb p (fun h' => h (by simp [h'])))
    ext i
    fin_cases i <;> simp [h0]
  have hm : MemLp (fun p : Profile => (!₂[f p 0, 0] : MeridC)) 2 (measureH c) :=
    NearGradMemberAux.memLp_of_band hcont hs0 hz
  refine ⟨hm, ?_⟩
  unfold solenoidalHC
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Φ, hΦmem, rfl⟩ := hx
    exact ZeroFlatSolenoidAux.pairing_zero hf hQ hm Φ hΦmem
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

end UnforcedLeray.Short.PartIIa
