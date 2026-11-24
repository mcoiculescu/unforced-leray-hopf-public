import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10_2

/-!
# `weakCurlLin`: linearity of the weak curl relation

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Sums and real multiples of weak-curl pairs are weak-curl pairs. The sum uses additivity of
`pairF` in its second slot, with integrability from `wcm_integrable_dotL` (the phase test
`curlT Ψ` is continuous with bounded `y`-support). The scalar part needs no integrability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest pairF_add_right_of_integrable)

/-- A phase integral is `ℂ`-linear under a constant factor on the integrand. -/
theorem wcl_phaseInt_const_mul (P : ℝ) (c : ℂ) (f : ℝ × Space → ℂ) :
    phaseInt P (fun x => c * f x) = c * phaseInt P f := by
  unfold phaseInt
  simp only [integral_const_mul, Complex.real_smul]
  ring

/-- Real scalar in the second slot of `pairF`. -/
theorem wcl_pairF_smul_right (P : ℝ) (Φ u : ℝ × Space → CVec3) (s : ℝ) :
    pairF P Φ (fun x => s • u x) = (s : ℂ) * pairF P Φ u := by
  show phaseInt P (fun x => dotL (Φ x) (s • u x)) = (s : ℂ) * phaseInt P (fun x => dotL (Φ x) (u x))
  have e : (fun x => dotL (Φ x) (s • u x)) = fun x => (s : ℂ) * dotL (Φ x) (u x) :=
    funext fun x => wcm_dotL_realsmul_right s _ _
  rw [e]
  exact wcl_phaseInt_const_mul P _ _

/-- **WeakCurlLin** (source 1334-1337, 1351-1362, 1470-1480): the weak curl relation is closed
under sums and real multiples of locally `L²` pairs. -/
theorem weakCurlLin : WeakCurlLin := by
  intro P hP u1 u2 v1 v2 hu1 hu2 hv1 hv2 h1 h2
  have : Fact (0 < P) := ⟨hP⟩
  constructor
  · intro Ψ hΨ
    have I1 := wcm_integrable_dotL hP (wcm_curlT_continuous hΨ) (wcm_curlT_support hΨ) hu1
    have I2 := wcm_integrable_dotL hP (wcm_curlT_continuous hΨ) (wcm_curlT_support hΨ) hu2
    have J1 := wcm_integrable_dotL hP hΨ.continuous hΨ.bounded_support hv1
    have J2 := wcm_integrable_dotL hP hΨ.continuous hΨ.bounded_support hv2
    have hsum_l : pairF P (curlT Ψ) (fun x => u1 x + u2 x) =
        pairF P (curlT Ψ) u1 + pairF P (curlT Ψ) u2 :=
      pairF_add_right_of_integrable I1 I2
        (Integrable.congr (Integrable.add I1 I2) (ae_of_all _ fun x => by
          show dotL (curlT Ψ x) (u1 x) + dotL (curlT Ψ x) (u2 x)
            = dotL (curlT Ψ x) (u1 x + u2 x)
          rw [map_add]))
    have hsum_r : pairF P Ψ (fun x => v1 x + v2 x) = pairF P Ψ v1 + pairF P Ψ v2 :=
      pairF_add_right_of_integrable J1 J2
        (Integrable.congr (Integrable.add J1 J2) (ae_of_all _ fun x => by
          show dotL (Ψ x) (v1 x) + dotL (Ψ x) (v2 x) = dotL (Ψ x) (v1 x + v2 x)
          rw [map_add]))
    show pairF P (curlT Ψ) (fun x => u1 x + u2 x) = pairF P Ψ (fun x => v1 x + v2 x)
    rw [hsum_l, hsum_r, h1 Ψ hΨ, h2 Ψ hΨ]
  · intro s Ψ hΨ
    show pairF P (curlT Ψ) (fun x => s • u1 x) = pairF P Ψ (fun x => s • v1 x)
    rw [wcl_pairF_smul_right, wcl_pairF_smul_right, h1 Ψ hΨ]

end UnforcedLeray.Short.PartIIIb.Concrete
