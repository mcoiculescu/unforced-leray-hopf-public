import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.Defs

/-!
# `TwoPeriodLtau`: normalized phase norms over two periods agree

Source `the November 2 reference manuscript` 5946-5950 (one phase period
`P_n = 2ε_nc_n`), 2666-2668 (`τ = 2q/R + log s`), 3611-3621 (normalized phase norms on `(0,P]`).

Proof: for a `P`-periodic `g` and a `p₀`-periodic `G` with `g = G` a.e., the double integral
`J = ∫_0^{p₀}∫_0^P g(u+x)² du dx` equals `p₀ ∫_0^P g²` (window shift) and `P ∫_0^{p₀} G²`
(window shift again, after translating the a.e. equality). Tonelli swaps the order.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace AnnulusTwoPeriod

/-- Window shift invariance of a periodic lintegral over `[a, a+P)` (the argument of
`NearInst.Masked.periodShift_holds`, copied here). -/
private theorem shiftIco {P : ℝ} (hP : 0 < P) (g : ℝ → ℝ≥0∞)
    (hper : ∀ τ, g (τ + P) = g τ) (a σ : ℝ) :
    ∫⁻ τ in Ico a (a + P), g (τ + σ) = ∫⁻ τ in Ico a (a + P), g τ := by
  have : Fact (0 < P) := ⟨hP⟩
  have hp : Function.Periodic g P := hper
  have hk : Function.Periodic (fun τ => g (τ + σ)) P := fun τ => by
    show g (τ + P + σ) = g (τ + σ)
    rw [add_right_comm]
    exact hp (τ + σ)
  have window : ∀ (f : ℝ → ℝ≥0∞) (hf : Function.Periodic f P),
      ∫⁻ τ in Ico a (a + P), f τ = ∫⁻ x : AddCircle P, hf.lift x := by
    intro f hf
    rw [← AddCircle.lintegral_preimage P a hf.lift]
    rw [setLIntegral_congr (Ico_ae_eq_Ioc : Ico a (a + P) =ᵐ[volume] Ioc a (a + P))]
    rfl
  have e1 : ∫⁻ τ in Ico a (a + P), g (τ + σ) = ∫⁻ x : AddCircle P, hk.lift x :=
    window (fun τ => g (τ + σ)) hk
  have e2 : ∫⁻ τ in Ico a (a + P), g τ = ∫⁻ x : AddCircle P, hp.lift x :=
    window g hp
  rw [e1, e2]
  have hl : ∀ x : AddCircle P, hk.lift x = hp.lift (x + (σ : AddCircle P)) := by
    intro x
    obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← AddCircle.coe_add]
    rfl
  refine (lintegral_congr hl).trans ?_
  exact lintegral_add_right_eq_self (fun x : AddCircle P => hp.lift x) (σ : AddCircle P)

/-- Window shift on `(0, P]`: `∫_{(0,P]} g(u + x) du = ∫_{(0,P]} g` for every `x`. -/
private theorem shiftIoc {P : ℝ} (hP : 0 < P) (g : ℝ → ℝ≥0∞)
    (hper : ∀ τ, g (τ + P) = g τ) (x : ℝ) :
    ∫⁻ u in Ioc 0 P, g (u + x) = ∫⁻ t in Ioc 0 P, g t := by
  have h1 : ∫⁻ u in Ioc 0 P, g (u + x) = ∫⁻ u in Ico 0 P, g (u + x) :=
    setLIntegral_congr (Ico_ae_eq_Ioc.symm : Ioc 0 P =ᵐ[volume] Ico 0 P)
  have h2 : ∫⁻ t in Ioc 0 P, g t = ∫⁻ t in Ico 0 P, g t :=
    setLIntegral_congr (Ico_ae_eq_Ioc.symm : Ioc 0 P =ᵐ[volume] Ico 0 P)
  rw [h1, h2]
  have h3 := shiftIco hP g hper 0 x
  rw [zero_add] at h3
  exact h3

/-- The two-period identity for the squared integrals: `I_g · p₀ = I_G · P`. -/
private theorem key_eq (P p₀ : ℝ) (hP : 0 < P) (hp₀ : 0 < p₀) (g G : ℝ → ℝ≥0∞)
    (hgm : Measurable g) (_hGm : Measurable G)
    (hgP : ∀ τ, g (τ + P) = g τ) (hGp : ∀ τ, G (τ + p₀) = G τ) (hgG : g =ᵐ[volume] G) :
    (∫⁻ τ in Ioc 0 P, g τ) * ENNReal.ofReal p₀ = (∫⁻ τ in Ioc 0 p₀, G τ) * ENNReal.ofReal P := by
  have hA : ∫⁻ x in Ioc 0 p₀, ∫⁻ u in Ioc 0 P, g (u + x)
      = (∫⁻ τ in Ioc 0 P, g τ) * ENNReal.ofReal p₀ := by
    simp only [shiftIoc hP g hgP, setLIntegral_const, Real.volume_Ioc, sub_zero]
  have hT : ∫⁻ x in Ioc 0 p₀, ∫⁻ u in Ioc 0 P, g (u + x)
      = ∫⁻ u in Ioc 0 P, ∫⁻ x in Ioc 0 p₀, g (u + x) :=
    lintegral_lintegral_swap (f := fun x u => g (u + x))
      (hgm.comp (measurable_snd.add measurable_fst)).aemeasurable
  have h1 : ∀ u : ℝ, ∫⁻ x in Ioc 0 p₀, g (u + x) = ∫⁻ x in Ioc 0 p₀, G (u + x) := by
    intro u
    apply lintegral_congr_ae
    apply ae_restrict_of_ae
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), g (u + x) = G (u + x) :=
      (measurePreserving_add_left volume u).quasiMeasurePreserving.ae
        (p := fun y => g y = G y) hgG
    exact hae
  have h2 : ∀ u : ℝ, ∫⁻ x in Ioc 0 p₀, G (u + x) = ∫⁻ t in Ioc 0 p₀, G t :=
    fun u => by simp only [add_comm u]; exact shiftIoc hp₀ G hGp u
  have hB : ∫⁻ u in Ioc 0 P, ∫⁻ x in Ioc 0 p₀, g (u + x)
      = (∫⁻ τ in Ioc 0 p₀, G τ) * ENNReal.ofReal P := by
    simp only [h1, h2, setLIntegral_const, Real.volume_Ioc, sub_zero]
  exact hA.symm.trans (hT.trans hB)

/-- Cancelling two finite nonzero factors. -/
private theorem inv_mul_eq_of (a b x y : ℝ≥0∞) (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (hb : b ≠ 0) (hb' : b ≠ ⊤) (h : x * b = y * a) : a⁻¹ * x = b⁻¹ * y := by
  calc a⁻¹ * x = a⁻¹ * x * (b * b⁻¹) := by rw [ENNReal.mul_inv_cancel hb hb', mul_one]
    _ = a⁻¹ * (x * b) * b⁻¹ := by ring
    _ = a⁻¹ * (y * a) * b⁻¹ := by rw [h]
    _ = y * (a⁻¹ * a) * b⁻¹ := by ring
    _ = y * b⁻¹ := by rw [ENNReal.inv_mul_cancel ha ha', mul_one]
    _ = b⁻¹ * y := by ring

end AnnulusTwoPeriod

open AnnulusTwoPeriod in
/-- **Normalized phase norm over two periods** (source 5946-5950, 2666-2668, 3611-3621). -/
theorem twoPeriodLtau : TwoPeriodLtau := by
  intro P p₀ hP hp₀ h k hh hk hhP hkp hae
  have hkey := key_eq P p₀ hP hp₀ (fun τ => h τ ^ (2:ℝ)) (fun τ => k τ ^ (2:ℝ))
    (hh.pow_const (2:ℝ))
    (hk.pow_const (2:ℝ))
    (fun τ => by show h (τ + P) ^ (2:ℝ) = h τ ^ (2:ℝ); rw [hhP τ])
    (fun τ => by show k (τ + p₀) ^ (2:ℝ) = k τ ^ (2:ℝ); rw [hkp τ])
    (hae.mono fun τ hτ => by show h τ ^ (2:ℝ) = k τ ^ (2:ℝ); rw [hτ])
  beta_reduce at hkey
  unfold UnforcedLeray.Short.IIIa.ltauAt
  congr 1
  have ha : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.mpr hP).ne'
  have hb : ENNReal.ofReal p₀ ≠ 0 := (ENNReal.ofReal_pos.mpr hp₀).ne'
  exact inv_mul_eq_of _ _ _ _ ha ENNReal.ofReal_ne_top hb ENNReal.ofReal_ne_top hkey

end UnforcedLeray.Short.PartIIIb.Concrete
