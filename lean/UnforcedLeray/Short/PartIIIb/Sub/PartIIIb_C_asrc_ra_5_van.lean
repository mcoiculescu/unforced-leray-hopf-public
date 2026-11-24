import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem emb_zero' : emb (0 : ℝ × ℝ) = 0 := by
  ext i; fin_cases i <;> simp [emb]

theorem eventually_far {ν s : ℝ} (h : 11 / 10 < ν * s) : ∀ᶠ s' in 𝓝 s, 11 / 10 < ν * s' := by
  have hc : Continuous fun s' : ℝ => ν * s' := by fun_prop
  exact continuousAt_const.eventually_lt hc.continuousAt h

theorem mv_zero' (v : Vec3) : mv 0 v = 0 := by
  ext i; simp [mv]

theorem mv_zero'' (v : Vec3) : mv (fun _ _ => (0 : ℝ)) v = 0 := by
  ext i; simp [mv]

theorem Ay_eq_zero {ν : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {s : ℝ}
    (h : 11 / 10 ≤ ν * s) : Ay ν χf A s = 0 := by
  simp [Ay, hχ.zero _ h]

theorem Ay_eventually_zero {ν : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {s : ℝ}
    (h : 11 / 10 < ν * s) : Ay ν χf A =ᶠ[𝓝 s] fun _ => 0 := by
  have h1 : ∀ᶠ s' in 𝓝 s, 11 / 10 < ν * s' := eventually_far h
  filter_upwards [h1] with s' h'
  exact Ay_eq_zero hχ A h'.le

theorem Bmat_eq_zero {ν μ : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {s : ℝ}
    (h : 11 / 10 < ν * s) : Bmat ν μ χf A s = 0 := by
  unfold Bmat
  rw [(Ay_eventually_zero hχ A h).deriv_eq, Ay_eq_zero hχ A h.le]
  simp

theorem hpA_eq_zero {ν : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {s : ℝ}
    (h : 11 / 10 ≤ ν * s) (x : ℝ × ℝ) : hpA ν χf A s x = 0 := by
  simp [hpA, Ay_eq_zero hχ A h, merApply, Prod.mk_zero_zero]

theorem psipA_eq_zero {ν : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {s : ℝ}
    (h : 11 / 10 ≤ ν * s) (x : ℝ × ℝ) : psipA ν χf A s x = 0 := by
  simp [psipA, Ay_eq_zero hχ A h, merApply, merTrace, Prod.mk_zero_zero]

theorem PsiA_eq_zero {ν : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {s : ℝ}
    (h : 11 / 10 ≤ ν * s) (x : ℝ × ℝ) : PsiA ν χf A s x = 0 := by
  simp [PsiA, Ay_eq_zero hχ A h, merApply]

theorem hhatA_eq_zero {ν ε : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {s : ℝ}
    (h : 11 / 10 < ν * s) (x : ℝ × ℝ) : hhatA ν ε χf A s x = 0 := by
  have hp : psipA ν χf A s = fun _ => 0 := funext fun y => psipA_eq_zero hχ A h.le y
  have h1 : ∀ᶠ s' in 𝓝 s, 11 / 10 < ν * s' := eventually_far h
  have h2 : (fun s' => psipA ν χf A s' x) =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [h1] with s' h'
    exact psipA_eq_zero hχ A h'.le x
  have hK : Kop (fun s' y => psipA ν χf A s' y) s x = 0 := by
    show x.2 * fderiv ℝ (psipA ν χf A s) x (ei 1) +
      2 * s * deriv (fun s' => psipA ν χf A s' x) s = 0
    rw [hp, h2.deriv_eq]
    simp
  simp [hhatA, hK, hpA_eq_zero hχ A h.le, psipA_eq_zero hχ A h.le, emb_zero', Prod.mk_zero_zero]

theorem fA_eq_zero {ν μ : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {s : ℝ}
    (h : 11 / 10 < ν * s) (x : ℝ × ℝ) : fA ν μ χf A s x = 0 := by
  simp [fA, Bmat_eq_zero hχ A h, merApply, mv_zero', emb_zero', Prod.mk_zero_zero]

theorem eA_eq_zero {ν μ : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {s : ℝ}
    (h : 11 / 10 < ν * s) (x : ℝ × ℝ) : eA ν μ χf A s x = 0 := by
  simp [eA, Bmat_eq_zero hχ A h, Ay_eq_zero hχ A h.le, mv_zero', mv_zero'', hessContr, emb_zero']

theorem merOf_zero'' : merOf (0 : Vec3) = 0 := by
  ext i; fin_cases i <;> simp [merOf]

theorem hAcoef_eq_zero {ν ε : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {p : Chart}
    (h : 11 / 10 < ν * p.1) : hAcoef ν ε χf A p = 0 := by
  simp [hAcoef, hhatA_eq_zero hχ A h, merOf_zero'']

theorem FEcoef_eq_zero {ν μ : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3) {p : Chart}
    (h : 11 / 10 < ν * p.1) : (FAcoef ν μ χf A + EAcoef ν μ χf A) p = 0 := by
  simp [FAcoef, EAcoef, FA, EA, fA_eq_zero hχ A h, eA_eq_zero hχ A h, merOf_zero'']

end UnforcedLeray.Short.PartIIIb.Concrete
