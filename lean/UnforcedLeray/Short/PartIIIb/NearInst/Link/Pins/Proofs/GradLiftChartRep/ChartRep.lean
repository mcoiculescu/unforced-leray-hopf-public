import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3_2

/-!
# `gradLiftChartRep` (task `PartIII-b:C/near/pins/3/3/2/1`)

Source `the November 2 reference manuscript` 1666, 1675-1677, 2666-2668, 2683.

The real chart form of the gradient lift `cgrad ε Ψ` is `f x = (D_εΨ, ∂_ηΨ)(x)` (real), since
`Ψ` is `c`-periodic in `q`, so `D_εΨ` and `∂_ηΨ` are too, and `cellPt` only shifts `q` by `c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The shift by `c` in the `q`-coordinate of a profile point. -/
private def qShift (c : ℝ) : Profile := (0, (c, 0))

/-- A `q`-periodic profile function has `q`-periodic first derivatives. -/
private theorem fderiv_qShift {c : ℝ} {Φ : Profile → ℝ} (hΦ : UnforcedLeray.B0220.QPeriodic c Φ) (p : Profile) :
    fderiv ℝ Φ (p + qShift c) = fderiv ℝ Φ p := by
  have hf : (fun x : Profile => Φ (x + qShift c)) = Φ := by
    funext x
    have hq' : x + qShift c = (x.1, x.2.1 + c, x.2.2) := by simp [qShift, Prod.ext_iff]
    rw [hq']
    exact hΦ x
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Φ) (qShift c) (x := p)
  rw [hf] at h
  exact h.symm

/-- `cgrad` is `q`-periodic. -/
private theorem cgrad_qPeriodic {c ε : ℝ} {Φ : Profile → ℝ} (hΦ : UnforcedLeray.B0220.QPeriodic c Φ) (p : Profile) :
    UnforcedLeray.Short.PartIIa.cgrad ε Φ (p.1, p.2.1 + c, p.2.2) =
      UnforcedLeray.Short.PartIIa.cgrad ε Φ p := by
  have hp : fderiv ℝ Φ (p + qShift c) = fderiv ℝ Φ p := fderiv_qShift hΦ p
  have hq : (p.1, p.2.1 + c, p.2.2) = p + qShift c := by
    simp [qShift, Prod.ext_iff]
  rw [hq]
  unfold UnforcedLeray.Short.PartIIa.cgrad UnforcedLeray.B0226.Deps UnforcedLeray.B0226.Kop
    Axi.dQ Axi.dS Axi.dEta
  simp only [hp]
  congr 2
  simp [qShift]

theorem gradLiftChartRep : GradLiftChartRep := by
  intro c ε hc hε Ψ hm
  refine ⟨fun x => !₂[UnforcedLeray.B0226.Deps ε Ψ.1 x, Axi.dEta Ψ.1 x], ?_, ?_⟩
  · unfold ChartRep
    filter_upwards [hm.coeFn_toLp] with q hq
    rw [hq]
    have hmC : ∀ x : Chart, merC (!₂[UnforcedLeray.B0226.Deps ε Ψ.1 x, Axi.dEta Ψ.1 x]) =
        UnforcedLeray.Short.PartIIa.cgrad ε Ψ.1 x := by
      intro x
      ext i
      fin_cases i <;> simp [merC, UnforcedLeray.Short.PartIIa.cgrad]
    rw [hmC]
    unfold cellPt
    split_ifs with h
    · rfl
    · have := cgrad_qPeriodic (ε := ε) Ψ.2.periodic (q.1, q.2.1 - c, q.2.2)
      simpa using this
  · intro x
    ext i
    fin_cases i <;> simp [merC, UnforcedLeray.Short.PartIIa.cgrad]

end UnforcedLeray.Short.PartIIIb.NearInst
