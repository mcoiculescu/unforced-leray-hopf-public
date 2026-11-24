import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_2_props
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont

/-!
# `cSliceAe`: a.e. slices of a `Y_2` field are `L²` (source 1334-1337)

Finite phase-`L²` norm on `(0,P]` gives finite slice norms for a.e. `τ ∈ (0,P]`; a.e. periodicity
(Fubini on `ℝ × ℝ³`) transports this to every integer translate of `(0,P]`, hence to a.e. `τ ∈ ℝ`.
Measurability of the slices a.e. comes from an a.e. strongly measurable representative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Slice `L²`-energy `∫ ‖f(τ, ·)‖²` (as an extended real). -/
def sNorm2 (f : ℝ × Space → CVec3) (τ : ℝ) : ENNReal :=
  ∫⁻ y : Space, ‖f (τ, y)‖ₑ ^ (2 : ℝ)

theorem memLp_slice_of_lint {g : Space → CVec3} (hm : AEStronglyMeasurable g volume)
    (h : ∫⁻ y : Space, ‖g y‖ₑ ^ (2 : ℝ) < ⊤) : MemLp g 2 volume := by
  refine ⟨hm, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

theorem sNorm2_periodic {P : ℝ} {f : ℝ × Space → CVec3}
    (hper : ∀ᵐ x : ℝ × Space, f (x.1 + P, x.2) = f x) :
    ∀ᵐ τ : ℝ, sNorm2 f (τ + P) = sNorm2 f τ := by
  rw [Measure.volume_eq_prod] at hper
  have hae := Measure.ae_ae_of_ae_prod hper
  filter_upwards [hae] with τ hτ
  unfold sNorm2
  refine lintegral_congr_ae ?_
  filter_upwards [hτ] with y hy
  simp only [hy]

theorem sNorm2_shift_all {P : ℝ} {f : ℝ × Space → CVec3}
    (hP1 : ∀ᵐ τ : ℝ, sNorm2 f (τ + P) = sNorm2 f τ) :
    ∀ k : ℤ, ∀ᵐ τ : ℝ, sNorm2 f (τ + (k : ℝ) * P) = sNorm2 f τ := by
  intro k
  induction k using Int.induction_on with
  | zero => exact Filter.Eventually.of_forall fun τ => by simp
  | succ n ih =>
    have h2 := (measurePreserving_add_right volume ((n : ℝ) * P)).quasiMeasurePreserving.ae hP1
    filter_upwards [h2, ih] with τ h2τ hτ
    simp only [Int.cast_natCast] at hτ
    have e : τ + ((n + 1 : ℤ) : ℝ) * P = (τ + (n : ℝ) * P) + P := by push_cast; ring
    rw [e, h2τ, hτ]
  | pred n ih =>
    have h2 := (measurePreserving_add_right volume (((-(n : ℤ) - 1 : ℤ) : ℝ) * P)).quasiMeasurePreserving.ae hP1
    filter_upwards [h2, ih] with τ h2τ hτ
    have e : τ + ((-(n : ℤ) - 1 : ℤ) : ℝ) * P + P = τ + ((-(n : ℤ) : ℤ) : ℝ) * P := by push_cast; ring
    rw [e] at h2τ
    rw [← h2τ, hτ]

theorem cSliceAe : CSliceAe := by
  unfold CSliceAe
  intro P hP f hf
  have hlint : ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(muP P) < ⊤ := lint_lt_top_of_phaseLpNorm hP hf.meas hf.finite
  have hm : AEMeasurable (fun z : ℝ × Space => ‖f z‖ₑ ^ (2 : ℝ)) (muP P) :=
    AEMeasurable.pow_const (AEStronglyMeasurable.enorm (aesm_muP hf.meas)) 2
  rw [lintegral_prod _ hm] at hlint
  have hm' : AEMeasurable (sNorm2 f) (volume.restrict (Ioc 0 P)) := hm.lintegral_prod_right'
  have hA0 : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)), sNorm2 f τ < ⊤ := ae_lt_top' hm' hlint.ne
  have hA1 : ∀ᵐ τ : ℝ, τ ∈ Ioc 0 P → sNorm2 f τ < ⊤ := (ae_restrict_iff' measurableSet_Ioc).1 hA0
  have hP1 : ∀ᵐ τ : ℝ, sNorm2 f (τ + P) = sNorm2 f τ := sNorm2_periodic hf.periodic
  have hG := sNorm2_shift_all (f := f) hP1
  have hk : ∀ k : ℤ, ∀ᵐ τ : ℝ, sNorm2 f τ = sNorm2 f (τ - (k : ℝ) * P)
      ∧ (τ - (k : ℝ) * P ∈ Ioc 0 P → sNorm2 f (τ - (k : ℝ) * P) < ⊤) := by
    intro k
    have hE : ∀ᵐ τ : ℝ, sNorm2 f (τ - (k : ℝ) * P + (k : ℝ) * P) = sNorm2 f (τ - (k : ℝ) * P) :=
      (measurePreserving_sub_right volume ((k : ℝ) * P)).quasiMeasurePreserving.ae (hG k)
    have hL : ∀ᵐ τ : ℝ, τ - (k : ℝ) * P ∈ Ioc 0 P → sNorm2 f (τ - (k : ℝ) * P) < ⊤ :=
      (measurePreserving_sub_right volume ((k : ℝ) * P)).quasiMeasurePreserving.ae hA1
    filter_upwards [hE, hL] with τ h1 h2
    rw [sub_add_cancel] at h1
    exact ⟨h1, h2⟩
  have hall : ∀ᵐ τ : ℝ, ∀ k : ℤ, sNorm2 f τ = sNorm2 f (τ - (k : ℝ) * P)
      ∧ (τ - (k : ℝ) * P ∈ Ioc 0 P → sNorm2 f (τ - (k : ℝ) * P) < ⊤) := ae_all_iff.2 hk
  have hF : ∀ᵐ τ : ℝ, sNorm2 f τ < ⊤ := by
    filter_upwards [hall] with τ hτ
    obtain ⟨he, hl⟩ := hτ (⌈τ / P⌉ - 1)
    rw [he]
    apply hl
    have h1 : ((⌈τ / P⌉ : ℤ) : ℝ) - 1 < τ / P := by
      have := Int.ceil_lt_add_one (τ / P)
      linarith
    have hA' : ((⌈τ / P⌉ : ℤ) : ℝ) * P - P < τ := by
      have h := mul_lt_mul_of_pos_right h1 hP
      rw [div_mul_cancel₀ τ hP.ne', sub_mul, one_mul] at h
      exact h
    have hB' : τ ≤ ((⌈τ / P⌉ : ℤ) : ℝ) * P := (div_le_iff₀ hP).1 (Int.le_ceil (τ / P))
    have e : ((⌈τ / P⌉ - 1 : ℤ) : ℝ) = ((⌈τ / P⌉ : ℤ) : ℝ) - 1 := by push_cast; ring
    have e2 : τ - ((⌈τ / P⌉ : ℤ) - 1 : ℝ) * P = τ - ((⌈τ / P⌉ : ℤ) : ℝ) * P + P := by ring
    rw [Set.mem_Ioc, e, e2]
    constructor <;> linarith
  have hpt : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, f (τ, y) = hf.meas.mk f (τ, y) := by
    have hfg : f =ᵐ[(volume : Measure ℝ).prod (volume : Measure Space)] hf.meas.mk f :=
      hf.meas.ae_eq_mk
    exact Measure.ae_ae_of_ae_prod hfg
  have hslice : ∀ᵐ τ : ℝ, AEStronglyMeasurable (fun y : Space => f (τ, y)) volume := by
    filter_upwards [hpt] with τ hτ
    have hτ' : (fun y : Space => hf.meas.mk f (τ, y)) =ᵐ[volume] (fun y : Space => f (τ, y)) :=
      hτ.mono fun y hy => hy.symm
    exact (((hf.meas.stronglyMeasurable_mk).comp_measurable
      (measurable_prodMk_left (x := τ))).aestronglyMeasurable).congr hτ'
  filter_upwards [hslice, hF] with τ h1 h2
  exact memLp_slice_of_lint h1 h2

end UnforcedLeray.Short.PartIIIb.Concrete
