import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1478-1480.

Proof. Let `Λ` be strongly measurable, a.e. `P`-periodic in slices, with finite period integral
`∫_{(0,P]} ∫ ‖Λ(τ,y)‖^r dy dτ < ∞`. Put `ρ(θ) ∈ (0,P]` for the representative of `θ ∈ ℝ/Pℤ`.
The field `G(θ,y) = Λ(ρ θ, y)` is strongly measurable on `ℝ/Pℤ × ℝ³` with finite `L^r` norm for the
product of the Haar measure and Lebesgue measure. Its Fubini image `a = prodLpEquiv G` lies in `Y_r`.
Slices: `a(θ) = G(θ, ·)` a.e. in `θ` (`prodLpEquiv_ae`), `G(τ mod P, ·) = Λ(τ + nP, ·)` by
definition of `ρ`, and `Λ(τ + nP, ·) = Λ(τ, ·)` a.e. in `τ` for every `n ∈ ℤ`, by periodicity and
translation invariance of Lebesgue measure. Hence `IsRep a Λ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Short.PartIIa.Rep

/-- The representative of `θ ∈ ℝ/Pℤ` in `(0, P]`. -/
def pfyRho (P : ℝ) [Fact (0 < P)] (θ : AddCircle P) : ℝ :=
  ((AddCircle.equivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ)

lemma pfyRho_measurable (P : ℝ) [Fact (0 < P)] : Measurable (pfyRho P) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc P 0).measurable

lemma pfyRho_coe (P : ℝ) [Fact (0 < P)] (t : ℝ) :
    ∃ n : ℤ, pfyRho P (t : AddCircle P) = t + (n : ℝ) * P := by
  have h1 : ((pfyRho P (t : AddCircle P) - t : ℝ) : AddCircle P) = 0 := by
    unfold pfyRho
    rw [QuotientAddGroup.mk_sub, AddCircle.coe_equivIoc, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff P).mp h1
  refine ⟨n, ?_⟩
  rw [zsmul_eq_mul] at hn
  linarith

lemma pfy_ae_shift {P : ℝ} {Λ : ℝ × Space → CVec3}
    (hper : ∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) (c : ℝ) :
    ∀ᵐ τ : ℝ, (fun y => Λ (τ + c + P, y)) =ᵐ[volume] fun y => Λ (τ + c, y) :=
  (measurePreserving_add_right (volume : Measure ℝ) c).quasiMeasurePreserving.ae hper

lemma pfy_ae_int {P : ℝ} {Λ : ℝ × Space → CVec3}
    (hper : ∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) (n : ℤ) :
    ∀ᵐ τ : ℝ, (fun y => Λ (τ + (n : ℝ) * P, y)) =ᵐ[volume] fun y => Λ (τ, y) := by
  induction n using Int.induction_on with
  | zero =>
    refine ae_of_all _ (fun τ => ?_)
    simp only [Int.cast_zero, zero_mul, add_zero]
    exact EventuallyEq.rfl
  | succ i ih =>
    filter_upwards [ih, pfy_ae_shift hper ((i : ℝ) * P)] with τ h1 h2
    have e : τ + (i : ℝ) * P + P = τ + ((i + 1 : ℤ) : ℝ) * P := by push_cast; ring
    rw [e] at h2
    exact h2.trans h1
  | pred i ih =>
    filter_upwards [ih, pfy_ae_shift hper ((-(i : ℝ) - 1) * P)] with τ h1 h2
    have e : τ + (-(i : ℝ) - 1) * P + P = τ + ((-(i : ℤ) : ℤ) : ℝ) * P := by push_cast; ring
    rw [e] at h2
    have e2 : τ + ((-(i : ℤ) - 1 : ℤ) : ℝ) * P = τ + (-(i : ℝ) - 1) * P := by push_cast; ring
    rw [e2]
    exact h2.symm.trans h1

lemma pfy_ae_rep {P : ℝ} [Fact (0 < P)] {Λ : ℝ × Space → CVec3}
    (hper : ∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) :
    ∀ᵐ t : ℝ, (fun y => Λ (pfyRho P (t : AddCircle P), y)) =ᵐ[volume] fun y => Λ (t, y) := by
  have hall : ∀ᵐ t : ℝ, ∀ n : ℤ, (fun y => Λ (t + (n : ℝ) * P, y)) =ᵐ[volume] fun y => Λ (t, y) :=
    ae_all_iff.2 (fun n => pfy_ae_int hper n)
  filter_upwards [hall] with t ht
  obtain ⟨n, hn⟩ := pfyRho_coe P t
  rw [hn]
  exact ht n

theorem periodicFieldToYq_proof : UnforcedLeray.Short.PartIIa.PeriodicFieldToYq := by
  intro r hr hrT P hP Λ hΛm hper hfin
  have : Fact (r ≠ ⊤) := ⟨hrT⟩
  set G : AddCircle P × Space → CVec3 := fun p => Λ (pfyRho P p.1, p.2) with hGdef
  have hGm : StronglyMeasurable G :=
    hΛm.comp_measurable (((pfyRho_measurable P).comp measurable_fst).prodMk measurable_snd)
  set F : ℝ → ℝ≥0∞ := fun τ => ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal with hFdef
  have hFm : Measurable F :=
    (hΛm.measurable.enorm.pow_const _).lintegral_prod_right'
  have hmp := AddCircle.measurePreserving_equivIoc P (a := 0)
  have h1 : ∫⁻ θ, F (pfyRho P θ) ∂(volume : Measure (AddCircle P)) =
      ∫⁻ x : Ioc (0 : ℝ) (0 + P), F (x : ℝ) ∂(Measure.comap Subtype.val (volume : Measure ℝ)) :=
    hmp.lintegral_comp (hFm.comp measurable_subtype_coe)
  have hvolfin : ∫⁻ θ, F (pfyRho P θ) ∂(volume : Measure (AddCircle P)) < ⊤ := by
    rw [h1, lintegral_subtype_comap measurableSet_Ioc F, zero_add]
    exact hfin
  have hhaar : ∫⁻ θ, F (pfyRho P θ) ∂(AddCircle.haarAddCircle (T := P)) < ⊤ := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure, smul_eq_mul] at hvolfin
    refine lt_top_iff_ne_top.2 (fun hb => ?_)
    rw [hb, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hP.out).ne'] at hvolfin
    exact lt_irrefl _ hvolfin
  have hprod_fin : ∫⁻ z, ‖G z‖ₑ ^ r.toReal ∂((AddCircle.haarAddCircle (T := P)).prod
      (volume : Measure Space)) < ⊤ := by
    rw [lintegral_prod _ (hGm.measurable.enorm.pow_const r.toReal).aemeasurable]
    exact hhaar
  have hmemG : MemLp G r ((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)) := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (one_pos.trans_le hr.out).ne' hrT]
    exact hprod_fin
  have hGL : ⇑(hmemG.toLp G) =ᵐ[(AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)] G :=
    hmemG.coeFn_toLp
  have h2 : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)), ∀ᵐ y ∂(volume : Measure Space),
      (hmemG.toLp G) (θ, y) = G (θ, y) := Measure.ae_ae_of_ae_prod hGL
  have h3 : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ((FreeStress.prodLpEquiv (hmemG.toLp G) θ : Lp CVec3 r (volume : Measure Space)) :
        Space → CVec3) =ᵐ[volume] fun y => G (θ, y) := by
    filter_upwards [FreeStress.prodLpEquiv_ae (hmemG.toLp G), h2] with θ hθ1 hθ2
    exact hθ1.trans hθ2
  have h4 := ae_comp_mk (P := P) h3
  refine ⟨FreeStress.prodLpEquiv (hmemG.toLp G), ⟨hΛm, ?_⟩⟩
  filter_upwards [h4, pfy_ae_rep hper] with t h5 h6
  exact h6.symm.trans h5.symm

end UnforcedLeray.Short.PartIIa
