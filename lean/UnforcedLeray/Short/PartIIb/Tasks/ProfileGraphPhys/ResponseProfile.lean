import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ResponseProfile.Equivar
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileOfNoSwirl
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileRegularize
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.FreeResponseCongr
import UnforcedLeray.Short.PartIIb.Bridge.Consequences
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.ComposeFree
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.LerayPairSol
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.SolSeparation

/-!
# Part II-b, task `PartII-b:T10/5` (`ResponseProfile`)

Source of record: `the November 2 reference manuscript`, lines 1912-1938, 1356-1420,
1634-1672.

Proof. The free response `w` to the axisymmetric no-swirl datum `N_v F` is unique
(`isFreeResponse_iff` and injectivity of `μ + L` on `D_r`), and `gAct g w` is a free response to
`gAct g (N_v F) = N_v F` a.e. for every `g` fixing the axis (`isFreeResponse_gAct`); hence `w` is
no-swirl, `w = N_v p` a.e. (`profileOfNoSwirl_proof`), and `p` is replaced by a profile of `H_r`
(`profileRegularize_proof`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

namespace RespProf

/-- Uniqueness of the free response. -/
theorem freeResponse_unique {ν : ℝ} {μ : ℂ} {r P : ℝ} {f w₁ w₂ : ℝ × Space → CVec3}
    (hP : 0 < P) (hP1 : P ≤ 1) (hν : 0 < ν) (h1 : 1 < r) (h3 : r < 3)
    (hμ : 0 < μ.re + (3 / r - 1) / 2) (hf : IsInYr P r f)
    (hw₁ : IsFreeResponse ν μ r P f w₁) (hw₂ : IsFreeResponse ν μ r P f w₂) :
    w₁ =ᵐ[volume] w₂ := by
  have : Fact (0 < P) := ⟨hP⟩
  have hr : 0 < r := by linarith
  have h1' : 1 < ENNReal.ofReal r := ENNReal.one_lt_ofReal.2 h1
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨h1'.le⟩
  have hμ' : 0 < μ.re + gammaR (ENNReal.ofReal r) := by rw [gammaR_ofReal hr.le]; exact hμ
  obtain ⟨Ff, hF, -⟩ := exists_hasRepY P r hr f hf
  obtain ⟨W₁, hW₁, -⟩ := exists_hasRepY P r hr w₁ hw₁.mem_w
  obtain ⟨W₂, hW₂, -⟩ := exists_hasRepY P r hr w₂ hw₂.mem_w
  obtain ⟨-, D₁, -, b₁⟩ := (isFreeResponse_iff hr lerayPairSol solSeparation h1 hF hW₁).1 hw₁
  obtain ⟨-, D₂, -, b₂⟩ := (isFreeResponse_iff hr lerayPairSol solSeparation h1 hF hW₂).1 hw₂
  have hinj := bodyOp_injective_of_bound commonBodyGraphBound (ENNReal.ofReal r) h1'
    (ofReal_lt_three h3) P hP1 ν hν μ hμ'
  have hE : (⟨W₁, D₁⟩ : D P ν (ENNReal.ofReal r)) = ⟨W₂, D₂⟩ := hinj (b₁.trans b₂.symm)
  have hW : W₁ = W₂ := congrArg Subtype.val hE
  subst hW
  exact PhaseFundHelp.hasRepY_ae_eq hW₁ hW₂

end RespProf

theorem responseProfile_proof : UnforcedLeray.Short.IIb.ResponseProfile := by
  intro c ε r ν μ F w hc hε hν hP1 hr1 hr3 hμ hF hw
  have hr0 : 0 < r := by linarith
  have hP : 0 < 2 * ε * c := by positivity
  have hf : IsInYr (2 * ε * c) r (NvC ε⁻¹ F) := nvCInYr_proof c ε r F hc hε hr0 hF
  have hNS : PhaseNoSwirl w := by
    intro g hg
    have h1 := RespProf.isFreeResponse_gAct hP hw g
    have h2 : gAct g (NvC ε⁻¹ F) =ᵐ[volume] NvC ε⁻¹ F := nvCInvariant ε⁻¹ F g hg
    have h3 := freeResponseCongr_proof ν μ r _ _ _ _ _ hP h2 (Filter.EventuallyEq.refl _ _) h1
    exact RespProf.freeResponse_unique hP hP1 hν hr1 hr3 hμ hf h3 hw
  obtain ⟨p, -, -, hpw⟩ := profileOfNoSwirl_proof c ε r w hc hε hr1 hw.mem_w hNS
  have hNp : IsInYr (2 * ε * c) r (NvC ε⁻¹ p) :=
    FreeRespCongrHelp.isInYr_congr hpw.symm hw.mem_w
  obtain ⟨b', -, -, hb', hb'e⟩ := profileRegularize_proof c ε r p hc hε hr0 hNp
  exact ⟨b', hb', hb'e.trans hpw⟩

end UnforcedLeray.Short.IIb

end
