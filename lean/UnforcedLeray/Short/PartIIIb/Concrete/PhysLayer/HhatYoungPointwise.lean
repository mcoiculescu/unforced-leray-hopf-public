import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

/-!
# `hhatYoungPointwise`: `ĥ_A` has young support (source 4953-4956, 4996)

`A^y = χ_f A` vanishes for `s ≥ 1.1/ν`, so every lattice term of `h^p_A`, `ψ^p_A` vanishes at
those ages, and so does `ĥ_A`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hhatY_Ay_zero {ν : ℝ} {χf : ℝ → ℝ} (hχf : IsSourceCutoffC χf) (A : ℝ → Mat3)
    (t : ℝ) (ht : 11 / 10 < ν * t) : Ay ν χf A t = 0 := by
  unfold Ay
  rw [hχf.zero (ν * t) ht.le, zero_smul]

theorem hhatY_psipA_zero {ν : ℝ} {χf : ℝ → ℝ} (hχf : IsSourceCutoffC χf) (A : ℝ → Mat3)
    (t : ℝ) (ht : 11 / 10 < ν * t) (y : ℝ × ℝ) : psipA ν χf A t y = 0 := by
  unfold psipA
  rw [hhatY_Ay_zero hχf A t ht]
  simp [merTrace, merApply, Prod.mk_zero_zero, map_zero]

theorem hhatY_hpA_zero {ν : ℝ} {χf : ℝ → ℝ} (hχf : IsSourceCutoffC χf) (A : ℝ → Mat3)
    (t : ℝ) (ht : 11 / 10 < ν * t) (y : ℝ × ℝ) : hpA ν χf A t y = 0 := by
  unfold hpA
  rw [hhatY_Ay_zero hχf A t ht]
  simp [merApply, Prod.mk_zero_zero, map_zero]

theorem hhatYoungPointwise {ν ε : ℝ} {χf : ℝ → ℝ} (hχf : IsSourceCutoffC χf) :
    HhatYoungPointwise ν ε χf := by
  intro A s x hs
  have hopen : {t : ℝ | 11 / 10 < ν * t} ∈ 𝓝 s :=
    (isOpen_lt continuous_const (continuous_const.mul continuous_id)).mem_nhds hs
  have hd : deriv (fun s' => psipA ν χf A s' x) s = 0 := by
    have hev : (fun s' => psipA ν χf A s' x) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [hopen] with t ht
      exact hhatY_psipA_zero hχf A t ht x
    rw [hev.deriv_eq, deriv_const]
  have hf : fderiv ℝ (fun y => psipA ν χf A s y) x = 0 := by
    have hfun : (fun y => psipA ν χf A s y) = fun _ => (0 : ℝ) :=
      funext fun y => hhatY_psipA_zero hχf A s hs y
    rw [hfun, fderiv_const_apply]
  have hKop : Kop (fun s' y => psipA ν χf A s' y) s x = 0 := by
    unfold Kop
    simp only
    rw [hf, hd]
    simp
  have he : emb ((0 : ℝ), (0 : ℝ)) = 0 := by
    ext i
    fin_cases i <;> simp [emb]
  unfold hhatA
  rw [hKop, hhatY_psipA_zero hχf A s hs x, hhatY_hpA_zero hχf A s hs x]
  simp [he]

end UnforcedLeray.Short.PartIIIb.Concrete
