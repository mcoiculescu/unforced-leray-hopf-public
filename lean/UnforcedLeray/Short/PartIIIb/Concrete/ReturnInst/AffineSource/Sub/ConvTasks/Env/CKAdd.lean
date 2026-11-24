import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvEnvSub

/-!
# `CKAdd`: additivity of `𝒦 = η∂_η + 2s∂_s` on profiles (source 5034-5044)

`Kop ψ s x = x.2 · D_xψ(s)(e_1) + 2s ∂_sψ(s,x)`; both pieces are linear in `ψ` at a point where
`ψ` is differentiable in `x` (at `s`) and in `s` (at `x`). Applied componentwise to
`F + ε E`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- Linearity of `Kop` for a scalar combination `a + c·b` of two real profiles. -/
theorem ckAdd_kop_lin (a b : ℝ → ℝ × ℝ → ℝ) (c s : ℝ) (x : ℝ × ℝ)
    (ha : DifferentiableAt ℝ (a s) x) (hb : DifferentiableAt ℝ (b s) x)
    (ha' : DifferentiableAt ℝ (fun s' => a s' x) s)
    (hb' : DifferentiableAt ℝ (fun s' => b s' x) s) :
    Kop (fun s' y => a s' y + c * b s' y) s x = Kop a s x + c * Kop b s x := by
  have hd : fderiv ℝ (fun y => a s y + c * b s y) x =
      fderiv ℝ (a s) x + c • fderiv ℝ (b s) x :=
    (ha.hasFDerivAt.add (hb.hasFDerivAt.const_mul c)).fderiv
  have hs : deriv (fun s' => a s' x + c * b s' x) s =
      deriv (fun s' => a s' x) s + c * deriv (fun s' => b s' x) s :=
    (ha'.hasDerivAt.add (hb'.hasDerivAt.const_mul c)).deriv
  unfold Kop
  dsimp only
  rw [hd, hs]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem ckAdd : CKAdd := by
  intro F E ε s x hFx hEx hFs hEs
  have c1 : Kop (fun s' y => (F s' y + ε • E s' y).1) s x =
      Kop (fun s' y => (F s' y).1) s x + ε * Kop (fun s' y => (E s' y).1) s x := by
    have := ckAdd_kop_lin (fun s' y => (F s' y).1) (fun s' y => (E s' y).1) ε s x
      hFx.fst hEx.fst hFs.fst hEs.fst
    simpa only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] using this
  have c2 : Kop (fun s' y => (F s' y + ε • E s' y).2) s x =
      Kop (fun s' y => (F s' y).2) s x + ε * Kop (fun s' y => (E s' y).2) s x := by
    have := ckAdd_kop_lin (fun s' y => (F s' y).2) (fun s' y => (E s' y).2) ε s x
      hFx.snd hEx.snd hFs.snd hEs.snd
    simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using this
  unfold cK
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    exact c1
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    exact c2

end UnforcedLeray.Short.PartIIIb.Concrete
