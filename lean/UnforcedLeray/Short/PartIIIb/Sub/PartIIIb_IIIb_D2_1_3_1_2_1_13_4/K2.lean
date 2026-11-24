import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13_4

/-!
# `curlOfGrad`: `curl ∂ₖψ = ∂ₖΦ` weakly

Source `the November 2 reference manuscript`
lines 1351-1362: `spΦ.grad` on the phase test `curl Θ`, `∂ₖ curl Θ = curl ∂ₖ Θ`, `spΦ.curl` on
`∂ₖ Θ`, then `dΦ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

theorem dy_curlT_comm {Θ : ℝ × Space → CVec3} (hΘ : ContDiff ℝ ∞ Θ) (k : Fin 3) :
    dy k (curlT Θ) = curlT (dy k Θ) := by
  funext x
  rw [dy_curl_apply hΘ k x, curlT_apply]
  simp only [dy_dy_comm hΘ]

theorem curlOfGrad : CurlOfGrad := by
  intro P ν μ D hD k Θ hΘ
  have hZ := isPhaseTest_curlT hΘ
  have hg : pairF P (-dy k (curlT Θ)) D.ψ = pairF P (curlT Θ) (D.Dψ k) :=
    (hD.spΦ.grad k).2 (curlT Θ) hZ
  have hc : pairF P (curlT (dy k Θ)) D.ψ = pairF P (dy k Θ) D.Φ :=
    hD.spΦ.curl (dy k Θ) (hΘ.dy k)
  have h3 : pairF P (-dy k Θ) D.Φ = pairF P Θ (D.DΦ k) := (hD.dΦ k).2 Θ hΘ
  have h4 : pairF P (-dy k Θ) D.Φ = -pairF P (dy k Θ) D.Φ := pairF_neg_left P _ _
  have h5 : pairF P (-curlT (dy k Θ)) D.ψ = -pairF P (curlT (dy k Θ)) D.ψ :=
    pairF_neg_left P _ _
  rw [dy_curlT_comm hΘ.smooth k] at hg
  rw [← hg, h5, hc, ← h4, h3]

end UnforcedLeray.Short.PartIIIb.Concrete
