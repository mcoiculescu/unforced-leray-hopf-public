import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5
import UnforcedLeray.Short.PartIIa.Sub.F03Rep
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

/-!
# `PartIII-b:C/ward/12/3/1/2/5/2` : `inletRepYq`

Source `the November 2 reference manuscript`
lines 2548-2551 (`Fn` in `L^{q0E}` of the product) and 2563-2569.

Proof. Let `g` be a strongly measurable version of `Fn` on the product measure
`μ = (volume.restrict (Ioc 0 P)).prod volume`. Put `Λ(τ,y) = g(ρ(τ), y)` with `ρ` the
representative of `τ mod P` in `(0,P]`; `Λ` is strongly measurable, exactly `P`-periodic in
the phase, and equal to `Fn` `μ`-a.e. Tonelli and the `L^{q0E}` bound give the finite period
integral, so `periodicFieldToYq_proof` yields `a : Yq P q0E` with `IsRep a Λ`. The slices of
`rep a` agree with those of `a`, hence with `Λ`, hence with `Fn` for a.e. `t ∈ (0,P]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIa
open UnforcedLeray.Cons.C03.Concrete (rep rep_slice)

theorem inletRepYq (P : ℝ) [Fact (0 < P)] : InletRepYq P := by
  intro Fn hFn
  have hP : (0 : ℝ) < P := Fact.out
  -- a strongly measurable version of `Fn` on the product
  set μ : Measure (ℝ × UnforcedLeray.Space) :=
    (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space) with hμ
  set g : ℝ × UnforcedLeray.Space → CVec3 := hFn.aestronglyMeasurable.mk Fn with hgdef
  have hg : StronglyMeasurable g := hFn.aestronglyMeasurable.stronglyMeasurable_mk
  have hGae : Fn =ᵐ[μ] g := hFn.aestronglyMeasurable.ae_eq_mk
  -- the periodic extension
  obtain ⟨Λ, hΛeq⟩ : ∃ Λ : ℝ × UnforcedLeray.Space → CVec3,
      Λ = fun p => g (pfyRho P ((p.1 : ℝ) : AddCircle P), p.2) := ⟨_, rfl⟩
  have hΛ : StronglyMeasurable Λ := by
    rw [hΛeq]
    exact hg.comp_measurable
      (((pfyRho_measurable P).comp ((AddCircle.continuous_mk' P).measurable.comp measurable_fst)).prodMk
        measurable_snd)
  have hT : ∀ τ ∈ Ioc (0 : ℝ) P, pfyRho P ((τ : ℝ) : AddCircle P) = τ := by
    intro τ hτ
    unfold pfyRho
    have h0 : τ ∈ Ioc (0 : ℝ) (0 + P) := by rw [zero_add]; exact hτ
    have := AddCircle.equivIoc_coe_of_mem (p := P) (a := 0) h0
    rw [this]
  have hper : ∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y) :=
    Filter.Eventually.of_forall fun τ => Filter.Eventually.of_forall fun y => by
      simp only [hΛeq, AddCircle.coe_add_period]
  -- `Λ = Fn` almost everywhere on the product
  have hfst : ∀ᵐ z ∂μ, z ∈ (Prod.fst ⁻¹' Ioc (0 : ℝ) P : Set (ℝ × UnforcedLeray.Space)) := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioc.preimage measurable_fst)).2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Filter.Eventually.of_forall fun y => hx
  have hLam_ae : ∀ᵐ z ∂μ, Λ z = Fn z := by
    filter_upwards [hfst, hGae] with z hz hzg
    have hz' : z.1 ∈ Ioc (0 : ℝ) P := hz
    rw [hzg, hΛeq]
    simp only [hT z.1 hz']
  -- finiteness of the period integral
  have hq0ne : UnforcedLeray.B0412.q0E ≠ 0 :=
    (zero_lt_one.trans UnforcedLeray.B0412.one_lt_q0E).ne'
  have hN : ∫⁻ z, ‖Fn z‖ₑ ^ UnforcedLeray.B0412.q0E.toReal ∂μ < ⊤ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0ne UnforcedLeray.B0412.q0E_ne_top
      hFn.eLpNorm_lt_top
  have hmeas : Measurable (fun z : ℝ × UnforcedLeray.Space => ‖Λ z‖ₑ ^ UnforcedLeray.B0412.q0E.toReal) :=
    hΛ.measurable.enorm.pow_const _
  have hTon : ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ UnforcedLeray.B0412.q0E.toReal
      = ∫⁻ z, ‖Λ z‖ₑ ^ UnforcedLeray.B0412.q0E.toReal ∂μ := by
    rw [hμ, lintegral_prod _ hmeas.aemeasurable]
  have hLamLE : ∫⁻ z, ‖Λ z‖ₑ ^ UnforcedLeray.B0412.q0E.toReal ∂μ
      = ∫⁻ z, ‖Fn z‖ₑ ^ UnforcedLeray.B0412.q0E.toReal ∂μ :=
    lintegral_congr_ae (hLam_ae.mono fun z hz => by simp only [hz])
  have hfin : ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ UnforcedLeray.B0412.q0E.toReal < ⊤ := by
    rw [hTon, hLamLE]
    exact hN
  -- the element of `Y_{q0E}`
  obtain ⟨a, ha⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof
    UnforcedLeray.B0412.q0E UnforcedLeray.B0412.q0E_ne_top P Λ hΛ hper hfin
  refine ⟨a, ?_⟩
  have hA : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
      rep a t y = Λ (t, y) := by
    filter_upwards [ha.slice] with t ht
    filter_upwards [ht, rep_slice a t] with y h1 h2
    exact h2.trans h1.symm
  have hB : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)),
      ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space), Λ (t, y) = Fn (t, y) :=
    Measure.ae_ae_of_ae_prod hLam_ae
  filter_upwards [ae_restrict_of_ae hA, hB] with t h1 h2
  filter_upwards [h1, h2] with y e1 e2
  exact e1.trans e2

end UnforcedLeray.Short.PartIIIb.Concrete
