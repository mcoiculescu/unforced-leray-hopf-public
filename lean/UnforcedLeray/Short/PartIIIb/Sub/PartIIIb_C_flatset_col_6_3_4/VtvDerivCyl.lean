import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvDerivCyl : VtvDerivCyl := by
  unfold VtvDerivCyl
  intro c η hη s
  unfold IsStreamTest at hη
  obtain ⟨hsm, hcyl, s₁, s₂, R, _hs₁, hband⟩ := hη
  have hGd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) := hsm
  have hDG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) p) :=
    (contDiff_infty_iff_fderiv.1 hGd).2
  have hGdiff : Differentiable ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) :=
    hGd.differentiable (by simp)
  have hkey : ∀ x : ℝ × ℝ, deriv (fun s' => η s' x) s =
      fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) (s, x) ((1 : ℝ), (0 : ℝ × ℝ)) := by
    intro x
    have hG : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)
        (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) (s, x)) (s, x) :=
      (hGdiff (s, x)).hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
    have hcomp := hG.comp_hasDerivAt s hline
    have hfun : (fun s' => η s' x) =
        ((fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) ∘ fun t : ℝ => ((t, x) : ℝ × (ℝ × ℝ))) := rfl
    rw [hfun]
    exact hcomp.deriv
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => ((s, x) : ℝ × (ℝ × ℝ))) :=
    contDiff_const.prodMk contDiff_id
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ => fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) (s, x)) :=
    hDG.comp hpair
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ => fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) (s, x) ((1 : ℝ), (0 : ℝ × ℝ))) :=
    hfd.clm_apply contDiff_const
  have hfun : (fun x : ℝ × ℝ => deriv (fun s' => η s' x) s) =
      (fun x : ℝ × ℝ => fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) (s, x) ((1 : ℝ), (0 : ℝ × ℝ))) :=
    funext hkey
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hsmooth
  · intro x
    show deriv (fun s' => η s' (x.1 + c, x.2)) s = deriv (fun s' => η s' x) s
    have hf : (fun s' => η s' (x.1 + c, x.2)) = (fun s' => η s' x) :=
      funext fun s' => (hcyl s').periodic x
    rw [hf]
  · refine ⟨R, fun x hx => ?_⟩
    show deriv (fun s' => η s' x) s = 0
    have hz : (fun s' => η s' x) = fun _ => (0 : ℝ) :=
      funext fun s' => hband s' x (Or.inr (Or.inr hx))
    rw [hz, deriv_const]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
