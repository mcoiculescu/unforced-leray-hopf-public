import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3

/-!
# `PartIII-b:C/grad/3/1`: support of `∇ĥ_A` above the cutoff (source 4953-4963, 5063-5079)

For `s > 1.1/ν`, `χ_f(νt) = 0` for all `t ≥ s`, so `A^y = 0` on the open set `(1.1/ν, ∞)`;
hence `h^p_A = ψ^p_A = 0` there, `ĥ_A = 0` on that set, and `∇ĥ_A(s, ·) = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradAy_zero {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) {ν : ℝ} (hν : 0 < ν)
    (A : ℝ → Mat3) {t : ℝ} (ht : (11 / 10) / ν < t) : Ay ν χf A t = 0 := by
  have h1 : 11 / 10 ≤ ν * t := by
    have := (div_lt_iff₀ hν).1 ht
    linarith [mul_comm ν t]
  show χf (ν * t) • A t = 0
  rw [hχ.zero _ h1, zero_smul]

theorem gradHp_zero {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) {ν : ℝ} (hν : 0 < ν)
    (A : ℝ → Mat3) {t : ℝ} (ht : (11 / 10) / ν < t) (y : ℝ × ℝ) :
    hpA ν χf A t y = 0 ∧ psipA ν χf A t y = 0 := by
  have hA := gradAy_zero hχ hν A ht
  constructor
  · simp [hpA, hA, merApply, Prod.mk_zero_zero, map_zero, tsum_zero]
  · simp [psipA, hA, merApply, merTrace, Prod.mk_zero_zero, map_zero, neg_zero, tsum_zero]

theorem gradKop_zero {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) {ν : ℝ} (hν : 0 < ν)
    (A : ℝ → Mat3) {t : ℝ} (ht : (11 / 10) / ν < t) (y : ℝ × ℝ) :
    Kop (fun s' y' => psipA ν χf A s' y') t y = 0 := by
  have hfun : (fun y' => psipA ν χf A t y') = fun _ => 0 :=
    funext fun y' => (gradHp_zero hχ hν A ht y').2
  have hev : (fun s' => psipA ν χf A s' y) =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds ht] with u hu using (gradHp_zero hχ hν A hu y).2
  have hd : deriv (fun s' => psipA ν χf A s' y) t = 0 := by
    rw [hev.deriv_eq]; simp
  simp [Kop, hfun, hd]

theorem gradHhat_zero {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf) {ν : ℝ} (hν : 0 < ν) (ε : ℝ)
    (A : ℝ → Mat3) {t : ℝ} (ht : (11 / 10) / ν < t) (y : ℝ × ℝ) :
    hhatA ν ε χf A t y = 0 := by
  have h := gradHp_zero hχ hν A ht y
  have hK := gradKop_zero hχ hν A ht y
  simp [hhatA, emb, h.1, h.2, hK]

theorem cylGrad_zero_of {u : ℝ → ℝ × ℝ → Vec3} {T : ℝ} (hu : ∀ t, T < t → ∀ y, u t y = 0)
    {s : ℝ} (hs : T < s) (ε : ℝ) (x : ℝ × ℝ) : cylGrad ε u s x = 0 := by
  have hc : ∀ i : Fin 3, chartComp u i s = fun _ => 0 := by
    intro i; funext y; simp [chartComp, hu s hs y]
  have hev : ∀ i : Fin 3, (fun t => chartComp u i t x) =ᶠ[𝓝 s] fun _ => 0 := by
    intro i
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp [chartComp, hu t ht x]
  have hd : ∀ i : Fin 3, deriv (fun t => chartComp u i t x) s = 0 := by
    intro i; rw [(hev i).deriv_eq]; simp
  have hu0 : u s x = 0 := hu s hs x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cylGrad, physDr, physDz, dQ, dEta, Kop, hc, hd, hu0]

/-- Support (source 4953-4963, 5063-5079): `∇ĥ_A(s, ·) = 0` for `s > 1.1/ν`. -/
theorem gradSupport (χf : ℝ → ℝ) : GradSupport χf := by
  intro hχ ν ε hν A s hs x
  have hcyl : physGradA ν ε χf A s x = 0 :=
    cylGrad_zero_of (T := (11 / 10) / ν) (fun t ht y => gradHhat_zero hχ hν ε A ht y) hs ε x
  simp [gradAcoef, hcyl, matTen]
  right
  rfl
