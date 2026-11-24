import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.Defs

/-!
# `PartIII-b:C/asrc/ra/9/4/org/2` : continuity of `gradRem` on `s > 0`

Source of record: `the November 2 reference manuscript`, lines 5024, 5040-5043, 4978.
`AffPsiC1` says `sΨ_A` is `C¹` on the open set `Ioi 0 ×ˢ univ`, so its partial derivatives
`dS`, `dEta` are continuous there, and so is `gradRem = !₂[-ε(2s dS F + η dEta F), 0]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradRemCont (as : ℝ) (χf : ℝ → ℝ) : GradRemCont as χf := by
  intro h hχ p μ A hA
  have hSo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hF : ContDiffOn ℝ 1 (sPsiChart p χf A) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    h hχ p.ν p.ν_pos A hA
  have hD : ContinuousOn (fderiv ℝ (sPsiChart p χf A)) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hF.continuousOn_fderiv_of_isOpen hSo le_rfl
  have hdS : ContinuousOn (fun q : Chart => UnforcedLeray.Axi.dS (sPsiChart p χf A) q)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hD.clm_apply continuousOn_const
  have hdE : ContinuousOn (fun q : Chart => UnforcedLeray.Axi.dEta (sPsiChart p χf A) q)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hD.clm_apply continuousOn_const
  have hnum : ContinuousOn (fun q : Chart => -(p.ε * (2 * q.1 *
      UnforcedLeray.Axi.dS (sPsiChart p χf A) q + q.2.2 *
        UnforcedLeray.Axi.dEta (sPsiChart p χf A) q)))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    have h1 : ContinuousOn (fun q : Chart => q.1) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
      continuous_fst.continuousOn
    have h2 : ContinuousOn (fun q : Chart => q.2.2) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
      (continuous_snd.comp continuous_snd).continuousOn
    fun_prop
  have hvec : ContinuousOn (fun q : Chart => (![-(p.ε * (2 * q.1 *
      UnforcedLeray.Axi.dS (sPsiChart p χf A) q + q.2.2 *
        UnforcedLeray.Axi.dEta (sPsiChart p χf A) q)), (0 : ℝ)] : Fin 2 → ℝ))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    refine continuousOn_pi.2 fun i => ?_
    fin_cases i
    · simpa using hnum
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact continuousOn_const
  have hT : Continuous (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) :=
    PiLp.continuous_toLp 2 _
  unfold gradRem
  exact hT.comp_continuousOn hvec

end UnforcedLeray.Short.PartIIIb.Concrete
