import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLiftDefs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_9
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Bridge
import UnforcedLeray.Lib.AxisymmetricB.DSS

/-!
# `WardVelPhysYH` (source 4161-4174): the physical velocity of `Yf T + hf T`

The pins give the chart coefficients of `Yf T` and `hf T` a.e. on the body measure; their sum is
the coefficient of `wardY + wardH` (pointwise additivity of `coefOf`). `velPhys_pin_ae` then
identifies the physical velocity with `realC (wardY + wardH)` a.e. on the phase cell
`(0, 2εc] × ℝ³`. Both sides are `2εc`-periodic in the phase variable (`Nv_dss` for the left,
`periodicY`/`periodicH` for the right), so the a.e. identity extends to all of `ℝ × ℝ³`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

/-- The translation of the time variable by `-kP`, as a shift of `ℝ × ℝ³`. -/
def ppShift (P : ℝ) (k : ℤ) : ℝ × Space := (-((k : ℝ) * P), (0 : Space))

/-- An a.e. identity on the phase cell of two `P`-periodic functions holds a.e. on `ℝ × ℝ³`. -/
theorem wvp_ae_eq_volume_of_periodic {E : Type*} {P : ℝ} (hP : 0 < P) {f g : ℝ × Space → E}
    (hf : ∀ τ z, f (τ + P, z) = f (τ, z)) (hg : ∀ τ z, g (τ + P, z) = g (τ, z))
    (h : f =ᵐ[(volume : Measure (ℝ × Space)).restrict (phaseCell P)] g) :
    f =ᵐ[(volume : Measure (ℝ × Space))] g := by
  have : (volume : Measure (ℝ × Space)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hS : MeasurableSet (phaseCell P) := measurableSet_Ioc.prod MeasurableSet.univ
  have hN : ∀ᵐ y ∂(volume : Measure (ℝ × Space)), y ∈ phaseCell P → f y = g y :=
    (ae_restrict_iff' hS).1 h
  have hk : ∀ (k : ℤ) (y : ℝ × Space), f (y.1 + -((k : ℝ) * P), y.2) = f y ∧
      g (y.1 + -((k : ℝ) * P), y.2) = g y := by
    intro k y
    have hf' : Function.Periodic (fun t => f (t, y.2)) P := fun t => hf t y.2
    have hg' : Function.Periodic (fun t => g (t, y.2)) P := fun t => hg t y.2
    have h1 := hf'.int_mul (-k) y.1
    have h2 := hg'.int_mul (-k) y.1
    simp only [Int.cast_neg, neg_mul] at h1 h2
    exact ⟨h1, h2⟩
  have hQ : ∀ k : ℤ, ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      x + ppShift P k ∈ phaseCell P → f (x + ppShift P k) = g (x + ppShift P k) :=
    fun k => (measurePreserving_add_right (volume : Measure (ℝ × Space))
      (ppShift P k)).quasiMeasurePreserving.ae hN
  have hall := ae_all_iff.2 hQ
  filter_upwards [hall] with x hx
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, (k : ℝ) * P < x.1 ∧ x.1 ≤ (k : ℝ) * P + P := by
    refine ⟨⌈x.1 / P⌉ - 1, ?_, ?_⟩
    · push_cast
      have h1 : (⌈x.1 / P⌉ : ℝ) - 1 < x.1 / P := by linarith [Int.ceil_lt_add_one (x.1 / P)]
      have h2 := mul_lt_mul_of_pos_right h1 hP
      rwa [div_mul_cancel₀ _ hP.ne'] at h2
    · push_cast
      have h2 : x.1 / P ≤ (⌈x.1 / P⌉ : ℝ) := Int.le_ceil _
      have h3 := mul_le_mul_of_nonneg_right h2 hP.le
      rw [div_mul_cancel₀ _ hP.ne'] at h3
      have e : ((⌈x.1 / P⌉ : ℝ) - 1) * P + P = (⌈x.1 / P⌉ : ℝ) * P := by ring
      linarith
  have hmem : x + ppShift P k ∈ phaseCell P := by
    simp only [phaseCell, ppShift, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true,
      Prod.fst_add, Prod.snd_add, add_zero]
    constructor <;> linarith
  have h := hx k hmem
  have e2 : x + ppShift P k = (x.1 + -((k : ℝ) * P), x.2) := by
    ext <;> simp [ppShift]
  rw [e2, (hk k x).1, (hk k x).2] at h
  exact h

/-- `coefOf` is additive in the field, pointwise. -/
theorem coefOf_add_pt (R : ℝ) (F G : ℝ → Space → Space) (p : Chart) :
    coefOf R (fun τ y => F τ y + G τ y) p = coefOf R F p + coefOf R G p := by
  unfold coefOf
  rw [← smul_add]
  congr 1
  ext i
  fin_cases i <;> simp

/-- The physical velocity of a chart coefficient is `2εc`-periodic in the phase. -/
theorem velPhys_periodic_of {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (b : Chart → Merid)
    (τ : ℝ) (z : Space) :
    velPhys ε⁻¹ c b (τ + 2 * ε * c, z) = velPhys ε⁻¹ c b (τ, z) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hpd : ∀ s ξ η, perExt c b (s, (ξ + c, η)) = perExt c b (s, (ξ, η)) :=
    fun s ξ η => perExt_periodic hc.ne' b s ξ η
  have hN := Nv_dss (R := ε⁻¹) (c := c) (P := 2 * c / ε⁻¹) (b := perExt c b) hR.ne' rfl hpd τ
  rw [hP]
  show B0412.realC (Nv ε⁻¹ (perExt c b) (τ + 2 * c / ε⁻¹) z) =
    B0412.realC (Nv ε⁻¹ (perExt c b) τ z)
  rw [congrFun hN z]

theorem wardVelPhysYH_proved {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) (hν : 0 < ν) {μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) :
    WardVelPhysYH B hc ε hε hν μ hχo χy U p := by
  intro hW T g₁ g₂ hg1 hg2 hin
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hPpos : 0 < 2 * ε * c := by positivity
  obtain ⟨hY, hH, -⟩ := wardPinned_reg B hε.ne' hW T g₁ g₂ hg1 hg2
  have hsum_ae : ((B.Yf T : Chart → Merid) + (B.hf T : Chart → Merid)) =ᵐ[ageμ c (-3 / 2)]
      coefOf ε⁻¹ (fun τ y => wardYr ν μ ε⁻¹ c χy (g₁ + g₂) τ y +
        wardHr ν μ ε⁻¹ c χy U (g₁ + g₂) τ y) := by
    rw [← NearInst.ae_bodyMeasure c γ ν]
    filter_upwards [hY, hH] with q h1 h2
    rw [Pi.add_apply, h1, h2, coefOf_add_pt]
  have hbm : Measurable ((B.Yf T : Chart → Merid) + (B.hf T : Chart → Merid)) :=
    (Lp.stronglyMeasurable (B.Yf T)).measurable.add (Lp.stronglyMeasurable (B.hf T)).measurable
  have hcont : Continuous (fun x : ℝ × Space =>
      wardYr ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 + wardHr ν μ ε⁻¹ c χy U (g₁ + g₂) x.1 x.2) :=
    hin.smoothY.continuous.add hin.smoothH.continuous
  have hloc := velPhys_pin_ae (c := c) (ε := ε) hc hε hbm
    (F := fun τ y => wardYr ν μ ε⁻¹ c χy (g₁ + g₂) τ y + wardHr ν μ ε⁻¹ c χy U (g₁ + g₂) τ y)
    hcont hin.liftYH hsum_ae
  have hper_R : ∀ τ z,
      B0412.realC (wardYr ν μ ε⁻¹ c χy (g₁ + g₂) (τ + 2 * ε * c) z +
        wardHr ν μ ε⁻¹ c χy U (g₁ + g₂) (τ + 2 * ε * c) z) =
      B0412.realC (wardYr ν μ ε⁻¹ c χy (g₁ + g₂) τ z + wardHr ν μ ε⁻¹ c χy U (g₁ + g₂) τ z) := by
    intro τ z
    rw [hP, hin.periodicY τ z, hin.periodicH τ z]
  have hreg := wvp_ae_eq_volume_of_periodic (f := velPhys ε⁻¹ c
      ((B.Yf T : Chart → Merid) + (B.hf T : Chart → Merid)))
    (g := fun x : ℝ × Space => B0412.realC (wardYr ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 +
      wardHr ν μ ε⁻¹ c χy U (g₁ + g₂) x.1 x.2))
    hPpos (fun τ z => velPhys_periodic_of hc hε _ τ z) hper_R hloc
  exact hreg.trans (realC_wardYHr_ae ν μ ε⁻¹ c χy U (g₁ + g₂))

end UnforcedLeray.Short.PartIIIb.Concrete
