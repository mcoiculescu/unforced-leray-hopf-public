import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1.Integrability

/-!
# `PartIII-a:T19/2/3/2/1` helpers: the vorticity form of the tested velocity equation

At a fixed age `r > 0` whose slices are in `L²(cell)`, the integrand of `CoreVortWeakEqAt`
(`flowIntegrand` of `Ω = r^μ g ω`, `U = r^μ g u₁`, plus the source `r^μ g ⟨-curl a, φ⟩`) equals
`r^μ ∫ jInt`, the velocity-form pairing `ν ⟨w, ΔΨ⟩ + ⟨v⊗b + b⊗v, ∇Ψ⟩` with `Ψ = (∂_η φ, -∂_q φ)`
(SP 3426-3440, 3462-3466). The difference is a combination of weak-gradient identities and
divergence-free identities, each integrating to zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.V1

open UnforcedLeray.Short.IIIa

/-! ## Bands -/

/-- `m` vanishes for `|η| > R`. -/
def Band (R : ℝ) (m : ℝ × ℝ → ℝ) : Prop := ∀ x : ℝ × ℝ, R < |x.2| → m x = 0

theorem Band.pd {R : ℝ} {m : ℝ × ℝ → ℝ} (h : Band R m) (j : Fin 2) : Band R (B0579.pd j m) := by
  intro x hx
  have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : m =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hx] with y hy using h y hy
  simp only [B0579.pd]
  rw [hev.fderiv_eq]
  simp

theorem Band.mul_left {R : ℝ} {m : ℝ × ℝ → ℝ} (h : Band R m) (k : ℝ × ℝ → ℝ) :
    Band R (fun x => k x * m x) := fun x hx => by simp only [h x hx, mul_zero]

theorem Band.add {R : ℝ} {m n : ℝ × ℝ → ℝ} (h : Band R m) (h' : Band R n) :
    Band R (fun x => m x + n x) := fun x hx => by simp only [h x hx, h' x hx, add_zero]

theorem Band.sub {R : ℝ} {m n : ℝ × ℝ → ℝ} (h : Band R m) (h' : Band R n) :
    Band R (fun x => m x - n x) := fun x hx => by simp only [h x hx, h' x hx, sub_zero]

theorem Band.lapP {R : ℝ} {m : ℝ × ℝ → ℝ} (h : Band R m) : Band R (lapP m) :=
  ((h.pd 0).pd 0).add ((h.pd 1).pd 1)

/-- `L² × (continuous, banded)` is integrable on the cell. -/
theorem intL2 {c : ℝ} {u : ℝ × ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (B0579.cell c)))
    {m : ℝ × ℝ → ℝ} (hm : Continuous m) {R : ℝ} (hb : Band R m) :
    IntegrableOn (fun x => u x * (m x : ℂ)) (B0579.cell c) := by
  have hm2 : MemLp m 2 (volume.restrict (B0579.cell c)) := by
    refine B0579.memLp_cell_of_continuous hm (B0579.isCompact_box c R) fun x hx hxK => hb x ?_
    by_contra h
    exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 h))
  exact hu.integrable_mul hm2.ofReal

/-! ## Integrable with zero integral -/

/-- `f` is integrable on the cell with vanishing integral. -/
def IZ (c : ℝ) (f : ℝ × ℝ → ℂ) : Prop :=
  IntegrableOn f (B0579.cell c) ∧ ∫ x in B0579.cell c, f x = 0

theorem IZ.add {c : ℝ} {f g : ℝ × ℝ → ℂ} (hf : IZ c f) (hg : IZ c g) :
    IZ c (fun x => f x + g x) :=
  ⟨hf.1.add hg.1, by rw [integral_add hf.1 hg.1, hf.2, hg.2, add_zero]⟩

theorem IZ.sub {c : ℝ} {f g : ℝ × ℝ → ℂ} (hf : IZ c f) (hg : IZ c g) :
    IZ c (fun x => f x - g x) :=
  ⟨hf.1.sub hg.1, by rw [integral_sub hf.1 hg.1, hf.2, hg.2, sub_zero]⟩

theorem IZ.const_mul {c : ℝ} {f : ℝ × ℝ → ℂ} (hf : IZ c f) (a : ℂ) :
    IZ c (fun x => a * f x) :=
  ⟨hf.1.const_mul a, by rw [integral_const_mul, hf.2, mul_zero]⟩

/-- Weak-gradient identity `∫ G_ij χ + b_i ∂_j χ = 0`. -/
def Wk (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (r : ℝ)
    (i j : Fin 2) (χ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  G (r, x) i j * (χ x : ℂ) + b (r, x) i * (B0579.pd j χ x : ℂ)

/-- Divergence-free identity `∫ b · ∇χ = 0`. -/
def Dv (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (r : ℝ) (χ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  b (r, x) 0 * (B0579.pd 0 χ x : ℂ) + b (r, x) 1 * (B0579.pd 1 χ x : ℂ)

theorem Wk_IZ {c ν' : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hb : IsCausalEnergySolution c ν' μ vel F b G)
    {r : ℝ} (hr : 0 < r) (i j : Fin 2) {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    IZ c (Wk G b r i j χ) := by
  have hw := hb.weakGrad r hr i j
  obtain ⟨h1, h2⟩ := hw.1 χ hχ
  refine ⟨h2.add h1, ?_⟩
  simp only [Wk]
  rw [integral_add h2 h1, hw.2 χ hχ]
  ring

theorem Dv_IZ {c ν' : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hb : IsCausalEnergySolution c ν' μ vel F b G)
    {r : ℝ} (hr : 0 < r) {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    IZ c (Dv b r χ) := by
  have h0 := ((hb.weakGrad r hr 0 0).1 χ hχ).1
  have h1 := ((hb.weakGrad r hr 1 1).1 χ hχ).1
  exact ⟨h0.add h1, hb.divFree r hr χ hχ⟩

/-! ## Composite test functions -/

variable {ν c : ℝ}

/-- `ψ = νΔφ + v·∇φ` (the tested right side of the vorticity equation). -/
def psiF (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => ν * lapP φ y + (vC tr r 0 y * B0579.pd 0 φ y + vC tr r 1 y * B0579.pd 1 φ y)

/-- `v_a ∂_k φ`. -/
def vfF (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (a k : Fin 2) (φ : ℝ × ℝ → ℝ) :
    ℝ × ℝ → ℝ :=
  fun y => vC tr r a y * B0579.pd k φ y

/-- `χ₀ = v · Ψ = v_q ∂_η φ - v_η ∂_q φ`. -/
def chi0F (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => vC tr r 0 y * B0579.pd 1 φ y - vC tr r 1 y * B0579.pd 0 φ y

/-- `χ_w = v · Ψ + E φ`. -/
def chiwF (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => chi0F tr r φ y + UnforcedLeray.B0238.Ec tr r y * φ y

section Tests

variable (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) {φ : ℝ × ℝ → ℝ}
  (hφ : B0579.IsCylTest c φ)
include hr hφ

theorem vfF_test (a k : Fin 2) : B0579.IsCylTest c (vfF tr r a k φ) :=
  cylTest_mul_left (vC_contDiff tr hr a) (vC_periodic tr hr a) (hφ.pd k)

theorem psiF_test : B0579.IsCylTest c (psiF tr r φ) :=
  cylTest_add (cylTest_const_mul ν (cylTest_lapP hφ))
    (cylTest_add (vfF_test tr hr hφ 0 0) (vfF_test tr hr hφ 1 1))

theorem chi0F_test : B0579.IsCylTest c (chi0F tr r φ) :=
  cylTest_sub (vfF_test tr hr hφ 0 1) (vfF_test tr hr hφ 1 0)

theorem chiwF_test : B0579.IsCylTest c (chiwF tr r φ) :=
  cylTest_add (chi0F_test tr hr hφ) (cylTest_mul_left (Ec_contDiff tr hr) (Ec_periodic tr hr) hφ)

theorem pd_vfF (a k j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j (vfF tr r a k φ) x =
      B0579.pd j (vC tr r a) x * B0579.pd k φ x + vC tr r a x * B0579.pd j (B0579.pd k φ) x :=
  pd_mul' (vC_diff tr hr a) (hφ.pd k).differentiable j x

theorem pd_psiF (j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j (psiF tr r φ) x =
      ν * lapP (B0579.pd j φ) x +
        ((B0579.pd j (vC tr r 0) x * B0579.pd 0 φ x +
            vC tr r 0 x * B0579.pd j (B0579.pd 0 φ) x) +
          (B0579.pd j (vC tr r 1) x * B0579.pd 1 φ x +
            vC tr r 1 x * B0579.pd j (B0579.pd 1 φ) x)) := by
  have hL : Differentiable ℝ (fun y => ν * lapP φ y) :=
    (cylTest_lapP hφ).differentiable.const_mul ν
  have hS : Differentiable ℝ (fun y => vfF tr r 0 0 φ y + vfF tr r 1 1 φ y) :=
    (vfF_test tr hr hφ 0 0).differentiable.add (vfF_test tr hr hφ 1 1).differentiable
  show B0579.pd j (fun y => ν * lapP φ y + (vfF tr r 0 0 φ y + vfF tr r 1 1 φ y)) x = _
  rw [pd_add (hL x) (hS x), pd_const_mul (cylTest_lapP hφ).differentiable,
    pd_add ((vfF_test tr hr hφ 0 0).differentiable x) ((vfF_test tr hr hφ 1 1).differentiable x),
    pd_vfF tr hr hφ, pd_vfF tr hr hφ, congrFun (pd_lapP hφ j) x]

theorem pd_chi0F (j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j (chi0F tr r φ) x =
      (B0579.pd j (vC tr r 0) x * B0579.pd 1 φ x + vC tr r 0 x * B0579.pd j (B0579.pd 1 φ) x) -
        (B0579.pd j (vC tr r 1) x * B0579.pd 0 φ x + vC tr r 1 x * B0579.pd j (B0579.pd 0 φ) x) := by
  show B0579.pd j (fun y => vfF tr r 0 1 φ y - vfF tr r 1 0 φ y) x = _
  rw [pd_sub ((vfF_test tr hr hφ 0 1).differentiable x) ((vfF_test tr hr hφ 1 0).differentiable x),
    pd_vfF tr hr hφ, pd_vfF tr hr hφ]

theorem pd_chiwF (j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j (chiwF tr r φ) x =
      B0579.pd j (chi0F tr r φ) x +
        (B0579.pd j (UnforcedLeray.B0238.Ec tr r) x * φ x +
          UnforcedLeray.B0238.Ec tr r x * B0579.pd j φ x) := by
  have hE : Differentiable ℝ (UnforcedLeray.B0238.Ec tr r) :=
    (Ec_contDiff tr hr).differentiable (by simp)
  show B0579.pd j (fun y => chi0F tr r φ y + UnforcedLeray.B0238.Ec tr r y * φ y) x = _
  rw [pd_add (f := chi0F tr r φ) (g := fun y => UnforcedLeray.B0238.Ec tr r y * φ y)
    ((chi0F_test tr hr hφ).differentiable x) ((hE.mul hφ.differentiable) x),
    pd_mul' hE hφ.differentiable]

end Tests

/-! ## The perturbation and the two pairings -/

/-- `w = b_sol - b₀`. -/
def wF (b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : ℝ × (ℝ × ℝ) → Fin 2 → ℂ :=
  fun p i => b_sol p i - b₀ p i

/-- `w · Ψ`. -/
def hInt (w : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (φ : ℝ × ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ∑ i : Fin 2, w p i * (perpF φ p.2 i : ℂ)

/-- `ν w · ΔΨ + (v⊗b + b⊗v) : ∇Ψ`. -/
def jInt (tr : UnforcedLeray.B0140.TrainSol ν c) (b_sol w : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (φ : ℝ × ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ∑ i : Fin 2, ((ν : ℂ) * w p i * (lapP (fun y => perpF φ y i) p.2 : ℂ) +
    ∑ j : Fin 2, ((trainVel tr p.1 p.2 i : ℂ) * b_sol p j + b_sol p i * (trainVel tr p.1 p.2 j : ℂ)) *
      (B0579.pd j (fun y => perpF φ y i) p.2 : ℂ))

/-- `H(r) = r^μ ⟨w(r), Ψ⟩`. -/
def Hf (c : ℝ) (μ : ℂ) (w : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (φ : ℝ × ℝ → ℝ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ μ * ∫ x in B0579.cell c, hInt w φ (r, x)

/-- `J(r) = r^μ ∫ jInt`. -/
def Jf (c : ℝ) (μ : ℂ) (tr : UnforcedLeray.B0140.TrainSol ν c) (b_sol w : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (φ : ℝ × ℝ → ℝ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ μ * ∫ x in B0579.cell c, jInt tr b_sol w φ (r, x)

/-! ## The left side -/

theorem gain_ne (γ ν' r : ℝ) : (gainG γ ν' r : ℂ) ≠ 0 := by
  have : 0 < gainG γ ν' r := Real.exp_pos _
  exact_mod_cast this.ne'

theorem lhs_eq {ν' γ : ℝ} {μ : ℂ} {vel₀ vel₁ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F₀ F₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hfree : IsCausalEnergySolution c ν' μ vel₀ F₀ b₀ G₀)
    (hsol : IsCausalEnergySolution c ν' μ vel₁ F₁ b_sol G_sol) {s : ℝ} (hs : 0 < s)
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∫ x in B0579.cell c, ((s : ℂ) ^ μ * (gainG γ ν' s : ℂ)) * corePerturbVort γ ν' G₀ G_sol s x *
        (φ x : ℂ) = Hf c μ (wF b₀ b_sol) φ s := by
  have hg := gain_ne γ ν' s
  have hZ : IZ c (fun x => (s : ℂ) ^ μ * (((Wk G_sol b_sol s 1 0 φ x - Wk G₀ b₀ s 1 0 φ x) -
      Wk G_sol b_sol s 0 1 φ x) + Wk G₀ b₀ s 0 1 φ x)) :=
    ((((Wk_IZ hsol hs 1 0 hφ).sub (Wk_IZ hfree hs 1 0 hφ)).sub
      (Wk_IZ hsol hs 0 1 hφ)).add (Wk_IZ hfree hs 0 1 hφ)).const_mul _
  have hH : IntegrableOn (fun x => (s : ℂ) ^ μ * hInt (wF b₀ b_sol) φ (s, x)) (B0579.cell c) := by
    have h0s := ((hsol.weakGrad s hs 0 1).1 φ hφ).1
    have h0f := ((hfree.weakGrad s hs 0 1).1 φ hφ).1
    have h1s := ((hsol.weakGrad s hs 1 0).1 φ hφ).1
    have h1f := ((hfree.weakGrad s hs 1 0).1 φ hφ).1
    refine IntegrableOn.congr_fun ((((h0s.sub h0f).sub (h1s.sub h1f))).const_mul ((s : ℂ) ^ μ))
      (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [hInt, wF, Fin.sum_univ_two, perpF_zero, perpF_one, Pi.sub_apply]
    push_cast; ring
  have hpt : ∀ x, ((s : ℂ) ^ μ * (gainG γ ν' s : ℂ)) * corePerturbVort γ ν' G₀ G_sol s x * (φ x : ℂ) =
      (s : ℂ) ^ μ * hInt (wF b₀ b_sol) φ (s, x) +
        (s : ℂ) ^ μ * (((Wk G_sol b_sol s 1 0 φ x - Wk G₀ b₀ s 1 0 φ x) -
          Wk G_sol b_sol s 0 1 φ x) + Wk G₀ b₀ s 0 1 φ x) := by
    intro x
    simp only [corePerturbVort, corePerturbGrad, gainConj, hInt, wF, Wk, Fin.sum_univ_two,
      perpF_zero, perpF_one, Pi.smul_apply, Complex.real_smul]
    push_cast
    field_simp
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hH hZ.1, hZ.2, add_zero,
    integral_const_mul]
  rfl

/-! ## The integrand of the time equation -/

theorem trainVel_of_nonneg (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (x : ℝ × ℝ) (k : Fin 2) : trainVel tr r x k = vC tr r k x := by
  simp [trainVel, vC, hr]

@[simp] theorem vC_apply (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (k : Fin 2) (x : ℝ × ℝ) :
    vC tr r k x = tr.v r x k := rfl

theorem trainVel_fun (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (k : Fin 2) :
    (fun y => trainVel tr r y k) = vC tr r k :=
  funext fun y => trainVel_of_nonneg tr hr y k

/-- The pointwise identity behind the vorticity form (SP 3462-3466). -/
theorem pointwise_TI (tr : UnforcedLeray.B0140.TrainSol ν c) {γ : ℝ} {μ : ℂ}
    {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {r : ℝ} (hr : 0 < r) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (x : ℝ × ℝ) :
    flowIntegrand tr
        (fun y => ((r : ℂ) ^ μ * (gainG γ ν r : ℂ)) * corePerturbVort γ ν G₀ G_sol r y)
        (fun y => ((r : ℂ) ^ μ * (gainG γ ν r : ℂ)) • corePerturbVel γ ν b₀ b_sol (r, y)) r φ x +
      ((r : ℂ) ^ μ * (gainG γ ν r : ℂ)) *
        (coreAdvSlice γ tr b₀ G₀ r x 1 * (B0579.pd 0 φ x : ℂ) -
          coreAdvSlice γ tr b₀ G₀ r x 0 * (B0579.pd 1 φ x : ℂ)) =
    (r : ℂ) ^ μ * jInt tr b_sol (wF b₀ b_sol) φ (r, x) +
      (r : ℂ) ^ μ * ((((((((((Wk G_sol b_sol r 1 0 (psiF tr r φ) x -
        Wk G₀ b₀ r 1 0 (psiF tr r φ) x) - Wk G_sol b_sol r 0 1 (psiF tr r φ) x) +
        Wk G₀ b₀ r 0 1 (psiF tr r φ) x) + Wk G₀ b₀ r 1 0 (vfF tr r 0 0 φ) x) +
        Wk G₀ b₀ r 1 1 (vfF tr r 1 0 φ) x) - Wk G₀ b₀ r 0 0 (vfF tr r 0 1 φ) x) -
        Wk G₀ b₀ r 0 1 (vfF tr r 1 1 φ) x) - Dv b_sol r (chiwF tr r φ) x) +
        Dv b₀ r (chiwF tr r φ) x) - Dv b₀ r (chi0F tr r φ) x) := by
  have hg := gain_ne γ ν r
  have hsym : B0579.pd 1 (B0579.pd 0 φ) x = B0579.pd 0 (B0579.pd 1 φ) x :=
    congrFun (pd_comm (cylTest_c2 hφ) 1 0) x
  have hdiv : B0579.pd 1 (vC tr r 1) x = -B0579.pd 0 (vC tr r 0) x := by
    have := vC_div tr hr.le x; linarith
  have hE : UnforcedLeray.B0238.Ec tr r x =
      B0579.pd 0 (vC tr r 1) x - B0579.pd 1 (vC tr r 0) x := congrFun (Ec_eq tr hr.le) x
  have hL1 : lapP (fun y => -B0579.pd 0 φ y) x = -lapP (B0579.pd 0 φ) x := lapP_neg (hφ.pd 0) x
  have hperp1 : (fun y => perpF φ y 1) = fun y => -B0579.pd 0 φ y := rfl
  have hperp0 : (fun y => perpF φ y 0) = B0579.pd 1 φ := rfl
  simp only [flowIntegrand, corePerturbVort, corePerturbGrad, corePerturbVel, gainConj,
    coreAdvSlice, advStretch, jInt, wF, Wk, Dv, Fin.sum_univ_two, hperp0, hperp1,
    Pi.smul_apply, smul_eq_mul, Complex.real_smul, trainVel_fun tr hr.le]
  simp only [trainVel_of_nonneg tr hr.le]
  rw [pd_psiF tr hr.le hφ 0, pd_psiF tr hr.le hφ 1, pd_vfF tr hr.le hφ, pd_vfF tr hr.le hφ,
    pd_vfF tr hr.le hφ, pd_vfF tr hr.le hφ, pd_chiwF tr hr.le hφ, pd_chiwF tr hr.le hφ,
    pd_chi0F tr hr.le hφ, pd_chi0F tr hr.le hφ, pd_neg, pd_neg, hL1]
  simp only [psiF, vfF]
  rw [hsym, hdiv, hE]
  simp only [vC_apply]
  push_cast
  field_simp
  ring

end UnforcedLeray.Short.IIIa.V1

end
